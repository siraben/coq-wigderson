(** * wigderson.v - Wigderson's graph coloring algorithm and correctness proof *)
Require Import graph.
Require Import subgraph.
Require Import coloring.
Require Import List.
Require Import Setoid.
Require Import FSets.
Require Import FMaps.
Require Import PArith.
Require Import FunInd.
Require Import restrict.
Require Import munion.
Require Import Psatz.
Require Import forcing.
Require Import bipartite.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
Import Arith.
Import ListNotations.
Import Nat.


(** [high_deg K n adj] holds when vertex [n] with adjacency set [adj]
    has degree strictly greater than [K]. *)
Definition high_deg (K: nat) (n: node) (adj: nodeset) : bool := K <? S.cardinal adj.

Local Open Scope positive_scope.

(** Wigderson's algorithm on a graph [G] with [|V(G)| = k]. A vertex is
    high-degree when its degree exceeds [sqrt k].

    - Phase 1 selects the high-degree vertices and 2-colors their
      neighborhoods.
    - Phase 2 colors the remaining (low-degree) graph with at most
      [sqrt k] colors.

    The two phases use disjoint color palettes, so their union is a
    valid coloring using [O(sqrt k)] colors. *)

(** * Phase 1: color the neighborhoods of high-degree vertices

    While a high-degree vertex [v] (degree > [k]) exists, 2-color its
    neighborhood [N(v)] with two fresh colors, color [v] with a third,
    remove [v] and [N(v)] from the graph, and recurse. Each step uses
    three new colors and removes at least [k+2] vertices. *)

Require Import Program.

(** 2-coloring of the neighborhood of [v] using colors [c1], [c2],
    computed by BFS-based forcing. *)
Definition two_color_nbd (g : graph) (v : node) (c1 c2 : positive) : coloring :=
  force_all (neighborhood g v) c1 c2.

(** The recursive body of phase 1: at each step it picks a high-degree
    vertex, 2-colors its neighborhood, colors the vertex itself, and
    recurses on the residual graph. Returns the coloring and the
    residual graph of untouched vertices. *)
Function phase1
  (k : nat) (c : positive) (g : graph) {measure M.cardinal g} : coloring * graph :=
  match S.choose (subset_nodes (high_deg k) g) with
  | Some v =>
      let nbhd := neighborhood g v in
      let m' := two_color_nbd g v (c+1) (c+2) in
      let g' := remove_nodes g (S.add v (nodes nbhd)) in
      let '(c2, g2) := phase1 k (c+3) g' in
      (Munion (M.add v c m') c2, g2)
  | None => (@M.empty _, g)
  end.
Proof.
  intros k c g v Hchoose.
  set (s := S.add v (nodes (neighborhood g v))).
  assert (Sv : S.In v s) by (unfold s; apply S.add_spec; left; reflexivity).
  assert (Vin : M.In v g).
  { apply in_nodes_iff. apply S.choose_1 in Hchoose.
    apply subset_nodes_sub in Hchoose. auto. }
  rewrite !m_cardinal_domain. rewrite nodes_remove_nodes_eq.
  eapply SP.subset_cardinal_lt with (x := v).
  - apply SP.diff_subset.
  - now rewrite in_nodes_iff.
  - unfold s. hauto l: on use: S.diff_spec, S.add_spec.
Defined.

(** A vertex chosen by [S.choose] on the high-degree subset is a
    vertex of the graph. Used throughout the phase-1 induction. *)
Lemma chosen_high_deg_in : forall k g v,
    S.choose (subset_nodes (high_deg k) g) = Some v -> M.In v g.
Proof.
  intros k g v Echoose.
  apply in_nodes_iff. apply S.choose_1 in Echoose.
  apply subset_nodes_sub in Echoose. auto.
Qed.

(** ** Colors used by phase1 are bounded below by c *)
Lemma phase1_color_lower_bound :
  forall k c g i ci,
    M.find i (fst (phase1 k c g)) = Some ci -> (c <= ci)%positive.
Proof.
  intros k c g.
  remember (M.cardinal g) as n eqn:Hn.
  revert k c g Hn.
  induction n as [n IH] using lt_wf_ind.
  intros k c g Hn i ci Hfi.
  rewrite phase1_equation in Hfi.
  destruct (S.choose (subset_nodes (high_deg k) g)) as [v|] eqn:Echoose.
  - set (nbhd := neighborhood g v) in *.
    set (m' := two_color_nbd g v (c+1) (c+2)) in *.
    set (g' := remove_nodes g (S.add v (nodes nbhd))) in *.
    destruct (phase1 k (c+3) g') as [f2 g2] eqn:Eph. simpl in Hfi.
    munion_cases Hfi.
    + destruct (E.eq_dec i v) as [->|Hne].
      * rewrite M.gss in Hfi. injection Hfi as <-. lia.
      * rewrite M.gso in Hfi by auto.
        apply force_all_palette in Hfi. destruct Hfi; subst; lia.
    + assert (Hlt : (M.cardinal g' < n)%nat).
      { subst n. unfold g'.
        eapply remove_nodes_lt with (i := v).
        - apply S.add_spec. left. reflexivity.
        - eapply chosen_high_deg_in; eauto. }
      assert (Hge : (c + 3 <= ci)%positive).
      { eapply (IH _ Hlt k (c+3) g' (Logic.eq_refl _)).
        rewrite Eph. simpl. exact Hfi. }
      lia.
  - simpl in Hfi. rewrite WF.empty_o in Hfi. discriminate.
Qed.

(** ** Phase1 domain is contained in g's vertices *)
Lemma phase1_domain :
  forall k c g i ci,
    undirected g ->
    M.find i (fst (phase1 k c g)) = Some ci -> M.In i g.
Proof.
  intros k c g.
  remember (M.cardinal g) as n eqn:Hn.
  revert k c g Hn.
  induction n as [n IH] using lt_wf_ind.
  intros k c g Hn i ci Ug Hfi.
  rewrite phase1_equation in Hfi.
  destruct (S.choose (subset_nodes (high_deg k) g)) as [v|] eqn:Echoose.
  - set (nbhd := neighborhood g v) in *.
    set (m' := two_color_nbd g v (c+1) (c+2)) in *.
    set (g' := remove_nodes g (S.add v (nodes nbhd))) in *.
    destruct (phase1 k (c+3) g') as [f2 g2] eqn:Eph. simpl in Hfi.
    munion_cases Hfi.
    + destruct (E.eq_dec i v) as [->|Hne].
      * eapply chosen_high_deg_in; eauto.
      * rewrite M.gso in Hfi by auto.
        unfold m', two_color_nbd in Hfi.
        eapply subgraph_vert_m; [apply nbd_subgraph |].
        eapply force_all_domain; eauto.
        apply neighborhood_undirected. auto.
    + assert (Hlt : (M.cardinal g' < n)%nat).
      { subst n. unfold g'. eapply remove_nodes_lt with (i := v).
        - apply S.add_spec. left. reflexivity.
        - eapply chosen_high_deg_in; eauto. }
      eapply subgraph_vert_m; [apply remove_nodes_subgraph |].
      eapply (IH _ Hlt k (c+3) g' (Logic.eq_refl _) i ci); auto.
      * apply remove_nodes_undirected. auto.
      * rewrite Eph. simpl. auto.
  - simpl in Hfi. rewrite WF.empty_o in Hfi. discriminate.
Qed.

(** ** Phase1 produces a valid coloring on the original graph *)
Lemma phase1_coloring_ok :
  forall k c g f p,
    undirected g -> no_selfloop g ->
    coloring_complete p g f -> three_coloring f p ->
    forall i j ci cj,
      S.In j (adj g i) ->
      M.find i (fst (phase1 k c g)) = Some ci ->
      M.find j (fst (phase1 k c g)) = Some cj -> ci <> cj.
Proof.
  intros k c g f p Ug Hloop Hcol H3.
  remember (M.cardinal g) as n eqn:Hn.
  revert k c g f p Ug Hloop Hcol H3 Hn.
  induction n as [n IH] using lt_wf_ind.
  intros k c g f p Ug Hloop Hcol H3 Hn i j ci cj Hadj Hfi Hfj.
  rewrite phase1_equation in Hfi, Hfj.
  destruct (S.choose (subset_nodes (high_deg k) g)) as [v|] eqn:Echoose.
  - (* Step case: v is a high-degree vertex *)
    set (nbhd := neighborhood g v) in *.
    set (m' := two_color_nbd g v (c+1) (c+2)) in *.
    set (g' := remove_nodes g (S.add v (nodes nbhd))) in *.
    destruct (phase1 k (c+3) g') as [f2 g2] eqn:Eph.
    simpl in Hfi, Hfj.
    (* Both colored by Munion (M.add v c m') f2 *)
    munion_cases2 Hfi Hfj.
    + (* Both in current step: M.add v c m' *)
      destruct (E.eq_dec i v) as [->|Hine]; destruct (E.eq_dec j v) as [->|Hjne].
      * (* i = v, j = v: self-loop, contradiction *)
        exfalso. apply (Hloop v). auto.
      * (* i = v, j ≠ v: v gets c, j gets c+1 or c+2 *)
        rewrite M.gss in Hfi. injection Hfi as <-.
        rewrite M.gso in Hfj by auto.
        apply force_all_palette in Hfj. destruct Hfj; subst; lia.
      * (* i ≠ v, j = v: symmetric *)
        rewrite M.gso in Hfi by auto. rewrite M.gss in Hfj. injection Hfj as <-.
        apply force_all_palette in Hfi. destruct Hfi; subst; lia.
      * (* both ≠ v: both in m' = force_all(neighborhood g v, c+1, c+2) *)
        rewrite M.gso in Hfi, Hfj by auto.
        (* Need: (i,j) is an edge in neighborhood g v *)
        assert (Hbip : bipartite nbhd).
        { unfold nbhd. eapply neighborhood_bipartite_of_three_coloring; eauto. }
        assert (Hnbd_und : undirected nbhd).
        { unfold nbhd. apply neighborhood_undirected. auto. }
        pose proof (force_all_ok nbhd (c+1) (c+2) Hnbd_und Hbip ltac:(lia)) as Hok.
        unfold m', two_color_nbd in Hfi, Hfj.
        (* i and j are in dom(force_all nbhd ...) hence in nodes nbhd ⊆ adj g v *)
        assert (HiN : S.In i (adj g v)).
        { apply nbd_adj. apply in_nodes_iff.
          eapply force_all_domain; eauto. }
        assert (HjN : S.In j (adj g v)).
        { apply nbd_adj. apply in_nodes_iff.
          eapply force_all_domain; eauto. }
        (* The edge (i,j) is in neighborhood g v *)
        assert (Hadj' : S.In j (adj nbhd i)).
        { unfold nbhd. apply adj_neighborhood_spec; auto. }
        (* Apply coloring_ok *)
        destruct (Hok i j Hadj') as [_ Hneq].
        exact (Hneq ci cj Hfi Hfj).
    + (* i in current step, j in recursive *)
      assert (Hci_bound : (ci <= c + 2)%positive).
      { destruct (E.eq_dec i v) as [->|Hne].
        - rewrite M.gss in Hfi. injection Hfi as <-. lia.
        - rewrite M.gso in Hfi by auto.
          apply force_all_palette in Hfi. destruct Hfi; subst; lia. }
      assert (Hcj_bound : (c + 3 <= cj)%positive).
      { eapply phase1_color_lower_bound. rewrite Eph. simpl. exact Hfj. }
      lia.
    + (* i in recursive, j in current step *)
      assert (Hci_bound : (c + 3 <= ci)%positive).
      { eapply phase1_color_lower_bound. rewrite Eph. simpl. exact Hfi. }
      assert (Hcj_bound : (cj <= c + 2)%positive).
      { destruct (E.eq_dec j v) as [->|Hne].
        - rewrite M.gss in Hfj. injection Hfj as <-. lia.
        - rewrite M.gso in Hfj by auto.
          apply force_all_palette in Hfj. destruct Hfj; subst; lia. }
      lia.
    + (* Both in recursive step *)
      assert (Hlt : (M.cardinal g' < n)%nat).
      { subst n. unfold g'.
        eapply remove_nodes_lt with (i := v).
        - apply S.add_spec. left. reflexivity.
        - eapply chosen_high_deg_in; eauto. }
      (* The edge (i,j) must exist in g' *)
      (* Both i,j are colored by phase1 on g', so they're in nodes g' *)
      (* Since i,j ∉ {v} ∪ nodes(nbhd) and (i,j) is edge in g, it's edge in g' *)
      assert (Ug' : undirected g') by (unfold g'; apply remove_nodes_undirected; auto).
      assert (Hloop' : no_selfloop g') by
        (unfold g'; eapply subgraph_no_selfloop; [apply remove_nodes_subgraph | auto]).
      (* three-colorability carries to subgraph *)
      assert (Hcol' : coloring_complete p g' f).
      { eapply subgraph_coloring_complete; eauto. apply remove_nodes_subgraph. }
      assert (Hfi' : M.find i (fst (phase1 k (c+3) g')) = Some ci) by (rewrite Eph; auto).
      assert (Hfj' : M.find j (fst (phase1 k (c+3) g')) = Some cj) by (rewrite Eph; auto).
      assert (Hi_g' : M.In i g') by (eapply phase1_domain; eauto).
      assert (Hj_g' : M.In j g') by (eapply phase1_domain; eauto).
      assert (Hadj' : S.In j (adj g' i)).
      { unfold g'. apply adj_remove_nodes_spec. split; [|split]; auto.
        - apply (proj1 (in_remove_nodes_iff _ _ _) Hj_g').
        - apply (proj1 (in_remove_nodes_iff _ _ _) Hi_g'). }
      eapply (IH _ Hlt k (c+3) g' f p Ug' Hloop' Hcol' H3 (Logic.eq_refl _)); eauto.
  - (* Base case: empty coloring *)
    simpl in Hfi. rewrite WF.empty_o in Hfi. discriminate.
Qed.

(** ** Phase1 residual graph is a subgraph of the original *)
Lemma phase1_subgraph :
  forall k c g,
    is_subgraph (snd (phase1 k c g)) g.
Proof.
  intros k c g.
  remember (M.cardinal g) as n eqn:Hn.
  revert k c g Hn.
  induction n as [n IH] using lt_wf_ind.
  intros k c g Hn.
  rewrite phase1_equation.
  destruct (S.choose (subset_nodes (high_deg k) g)) as [v|] eqn:Echoose.
  - set (nbhd := neighborhood g v) in *.
    set (m' := two_color_nbd g v (c+1) (c+2)) in *.
    set (g' := remove_nodes g (S.add v (nodes nbhd))) in *.
    destruct (phase1 k (c+3) g') as [f2 g2] eqn:Eph. simpl.
    assert (Hlt : (M.cardinal g' < n)%nat).
    { subst n. unfold g'. eapply remove_nodes_lt with (i := v).
      - apply S.add_spec. left. reflexivity.
      - eapply chosen_high_deg_in; eauto. }
    specialize (IH _ Hlt k (c+3) g' (Logic.eq_refl _)). rewrite Eph in IH. simpl in IH.
    eapply subgraph_trans; eauto. apply remove_nodes_subgraph.
  - simpl. apply subgraph_refl.
Qed.

(** ** Phase1 residual graph is undirected *)
Lemma phase1_undirected :
  forall k c g,
    undirected g -> undirected (snd (phase1 k c g)).
Proof.
  intros k c g Ug.
  remember (M.cardinal g) as n eqn:Hn.
  revert k c g Ug Hn.
  induction n as [n IH] using lt_wf_ind.
  intros k c g Ug Hn.
  rewrite phase1_equation.
  destruct (S.choose (subset_nodes (high_deg k) g)) as [v|] eqn:Echoose.
  - set (nbhd := neighborhood g v) in *.
    set (g' := remove_nodes g (S.add v (nodes nbhd))) in *.
    destruct (phase1 k (c+3) g') as [f2 g2] eqn:Eph. simpl.
    assert (Hlt : (M.cardinal g' < n)%nat).
    { subst n. unfold g'. eapply remove_nodes_lt with (i := v).
      - apply S.add_spec. left. reflexivity.
      - eapply chosen_high_deg_in; eauto. }
    assert (Ug' : undirected g') by (unfold g'; apply remove_nodes_undirected; auto).
    specialize (IH _ Hlt k (c+3) g' Ug' (Logic.eq_refl _)).
    rewrite Eph in IH. simpl in IH. exact IH.
  - simpl. auto.
Qed.

(** ** Phase1 residual graph has no self-loops *)
Lemma phase1_no_selfloop :
  forall k c g,
    no_selfloop g -> no_selfloop (snd (phase1 k c g)).
Proof.
  intros k c g Hloop.
  remember (M.cardinal g) as n eqn:Hn.
  revert k c g Hloop Hn.
  induction n as [n IH] using lt_wf_ind.
  intros k c g Hloop Hn.
  rewrite phase1_equation.
  destruct (S.choose (subset_nodes (high_deg k) g)) as [v|] eqn:Echoose.
  - set (nbhd := neighborhood g v) in *.
    set (g' := remove_nodes g (S.add v (nodes nbhd))) in *.
    destruct (phase1 k (c+3) g') as [f2 g2] eqn:Eph. simpl.
    assert (Hlt : (M.cardinal g' < n)%nat).
    { subst n. unfold g'. eapply remove_nodes_lt with (i := v).
      - apply S.add_spec. left. reflexivity.
      - eapply chosen_high_deg_in; eauto. }
    assert (Hloop' : no_selfloop g') by
      (unfold g'; eapply subgraph_no_selfloop; [apply remove_nodes_subgraph | auto]).
    specialize (IH _ Hlt k (c+3) g' Hloop' (Logic.eq_refl _)).
    rewrite Eph in IH. simpl in IH. exact IH.
  - simpl. auto.
Qed.

(** ** Phase1 eliminates all high-degree vertices *)
Lemma phase1_no_high_deg :
  forall k c g,
    undirected g ->
    S.Empty (subset_nodes (high_deg k) (snd (phase1 k c g))).
Proof.
  intros k c g Ug.
  remember (M.cardinal g) as n eqn:Hn.
  revert k c g Ug Hn.
  induction n as [n IH] using lt_wf_ind.
  intros k c g Ug Hn.
  rewrite phase1_equation.
  destruct (S.choose (subset_nodes (high_deg k) g)) as [v|] eqn:Echoose.
  - set (nbhd := neighborhood g v) in *.
    set (g' := remove_nodes g (S.add v (nodes nbhd))) in *.
    destruct (phase1 k (c+3) g') as [f2 g2] eqn:Eph. simpl.
    assert (Hlt : (M.cardinal g' < n)%nat).
    { subst n. unfold g'. eapply remove_nodes_lt with (i := v).
      - apply S.add_spec. left. reflexivity.
      - eapply chosen_high_deg_in; eauto. }
    assert (Ug' : undirected g') by (unfold g'; apply remove_nodes_undirected; auto).
    specialize (IH _ Hlt k (c+3) g' Ug' (Logic.eq_refl _)).
    rewrite Eph in IH. simpl in IH. exact IH.
  - simpl. apply S.choose_2 in Echoose. auto.
Qed.

(** ** Phase1 preserves adjacency among remaining vertices *)
Lemma phase1_adj_preserved :
  forall k c g i j,
    undirected g ->
    S.In j (adj g i) ->
    M.In i (snd (phase1 k c g)) ->
    M.In j (snd (phase1 k c g)) ->
    S.In j (adj (snd (phase1 k c g)) i).
Proof.
  intros k c g.
  remember (M.cardinal g) as n eqn:Hn.
  revert k c g Hn.
  induction n as [n IH] using lt_wf_ind.
  intros k c g Hn i j Ug Hadj Hi Hj.
  rewrite phase1_equation in Hi, Hj |- *.
  destruct (S.choose (subset_nodes (high_deg k) g)) as [v|] eqn:Echoose.
  - set (nbhd := neighborhood g v) in *.
    set (g' := remove_nodes g (S.add v (nodes nbhd))) in *.
    destruct (phase1 k (c+3) g') as [f2 g2] eqn:Eph. simpl in *.
    assert (Hlt : (M.cardinal g' < n)%nat).
    { subst n. unfold g'. eapply remove_nodes_lt with (i := v).
      - apply S.add_spec. left. reflexivity.
      - eapply chosen_high_deg_in; eauto. }
    assert (Ug' : undirected g') by (unfold g'; apply remove_nodes_undirected; auto).
    (* g2 is a subgraph of g' *)
    assert (Hsub : is_subgraph g2 g').
    { pose proof (phase1_subgraph k (c+3) g'). rewrite Eph in H. simpl in H. exact H. }
    (* i,j are in g' since g2 ⊆ g' *)
    assert (Hi' : M.In i g') by (eapply subgraph_vert_m; eauto).
    assert (Hj' : M.In j g') by (eapply subgraph_vert_m; eauto).
    (* i,j not in the removed set *)
    assert (Hni : ~ S.In i (S.add v (nodes nbhd)))
      by (apply (proj1 (in_remove_nodes_iff _ _ _) Hi')).
    assert (Hnj : ~ S.In j (S.add v (nodes nbhd)))
      by (apply (proj1 (in_remove_nodes_iff _ _ _) Hj')).
    (* edge persists in g' *)
    assert (Hadj' : S.In j (adj g' i)).
    { apply adj_preserved_if_not_removed; auto. }
    (* apply IH *)
    assert (IHres := IH _ Hlt k (c+3) g' (Logic.eq_refl _) i j Ug' Hadj').
    rewrite Eph in IHres. simpl in IHres. auto.
  - simpl in *. auto.
Qed.

(** ** Maximum color in a coloring *)
Definition max_color (f : coloring) : positive :=
  M.fold (fun _ v acc => Pos.max v acc) f 1.

(** [Pos.max] is monotone in its right argument. *)
Lemma Pos_max_le_compat_r : forall v a b,
  (a <= b)%positive -> (Pos.max v a <= Pos.max v b)%positive.
Proof.
  intros v a b H.
  unfold Pos.max.
  destruct (Pos.compare_spec v a); destruct (Pos.compare_spec v b); lia.
Qed.

(** The accumulator is a lower bound of the [Pos.max] fold. *)
Lemma fold_left_max_le_acc : forall l (acc : positive),
  (acc <= fold_left (fun (a : positive) (p : M.key * positive) => Pos.max (snd p) a) l acc)%positive.
Proof.
  induction l as [|[k v] l IH]; intros acc; simpl.
  - lia.
  - etransitivity; [apply Pos.le_max_r | apply IH].
Qed.

(** Every value in the list bounds the [Pos.max] fold from below. *)
Lemma fold_left_max_in : forall l i ci acc,
  In (i, ci) l ->
  (ci <= fold_left (fun (a : positive) (p : M.key * positive) => Pos.max (snd p) a) l acc)%positive.
Proof.
  induction l as [|[k v] l IH]; intros i ci acc H.
  - inversion H.
  - simpl in H. destruct H as [H|H].
    + injection H as <- <-. simpl.
      etransitivity; [apply Pos.le_max_l|].
      apply fold_left_max_le_acc.
    + simpl. eapply IH. exact H.
Qed.

(** [max_color] is an upper bound on every color in the coloring. *)
Lemma max_color_spec : forall f i ci,
  M.find i f = Some ci -> (ci <= max_color f)%positive.
Proof.
  intros f i ci Hfi.
  unfold max_color. rewrite M.fold_1.
  apply fold_left_max_in with (i := i).
  apply M.elements_correct. auto.
Qed.

(** * Phase 2: color the low-degree residual graph

    After phase 1 the residual graph has maximum degree at most [k].
    Phase 2 repeatedly extracts a maximal independent set of the
    current-maximum-degree vertices, colors them all with a fresh
    color, and recurses on the rest. A graph of maximum degree [d] is
    colored with at most [d + 1] colors. *)

(** The recursive body of phase 2: colors each independent layer of
    maximum-degree vertices with a fresh color. Returns the coloring
    and the (empty) residual graph. *)
Function phase2 (g : graph) {measure M.cardinal g} : coloring * graph :=
  match (max_deg g)%nat with
  | 0%nat => (constant_color (nodes g) 1, (@M.empty _))
  | S n => let (ns, g') := extract_vertices_degs g (S n) in
          let (f', g'') := phase2 g' in
          (Munion (constant_color ns (Pos.of_nat (S (S n)))) f', g'')
  end.
Proof.
  intros g n teq.
  intros ns g' teq0.
  replace g' with (snd (ns, g')) by auto.
  rewrite <- teq0.
  rewrite teq0.
  simpl.
  assert (~ S.Empty ns).
  {
    intros contra.
    rewrite extract_vertices_degs_equation in teq0.
    destruct (extract_deg_vert_dec g (S n)) eqn:EE.
    - destruct s as [v Hv].
      simpl in *.
      destruct (extract_vertices_degs (remove_node v g) (S n)) as [s g''].
      inversion teq0.
      subst.
      assert (S.In v (S.add v s)).
      {
        sfirstorder use: SP.Dec.F.add_iff unfold: node, PositiveOrderedTypeBits.t, PositiveSet.elt, nodeset.
      }
      scongruence.
    - inversion teq0.
      subst.
      clear teq0.
      pose proof (max_degree_vert g' (S n) ltac:(hauto use: max_deg_gt_not_empty, nlt_0_r unfold: Peano.lt inv: sumbool) teq).
      contradiction.
  }
  assert (exists v, S.In v ns).
  {
    clear -H.
    destruct (PositiveSet.choose ns) eqn:EE.
    - exists e.
      strivial use: PositiveSet.choose_1 unfold: nodeset.
    - sfirstorder use: PositiveSet.choose_2.
  }
  clear H.
  destruct H0 as [v Hv].
  assert (is_subgraph g' g) by hauto l: on use: extract_vertices_degs_subgraph.
  pose proof (extract_vertices_remove g g' ns (S n) ltac:(auto) v Hv).
  unfold is_subgraph in H.
  assert (~ S.In v (nodes g') /\ S.In v (nodes g)).
  {
    sfirstorder use: in_nodes_iff.
  }
  enough (S.cardinal (nodes g') < S.cardinal (nodes g))%nat.
  {
    scongruence use: m_cardinal_domain unfold: snd, extract_vertices_degs, PositiveMap.t, nodes, fst inv: R_extract_vertices_degs.
  }
  apply SP.subset_cardinal_lt with (x := v); sauto lq: on rew: off.
Defined.

Functional Scheme phase2_ind := Induction for phase2 Sort Prop.

(** The palette [{1, ..., p+1}] as a node set, used to bound the colors
    produced by phase 2. *)
Definition siota p := SP.of_list (map Pos.of_nat (seq 1 (p + 1))).
(** The palette used by phase 2: colors [1 .. max_deg g + 1]. *)
Definition phase2_colors g := siota (max_deg g).

(** ** Specification of siota construction *)
Lemma siota_spec : forall (n : nat), (forall i, (0 <= i <= n + 1)%nat <-> S.In (Pos.of_nat i) (siota n)).
Proof.
  intros n i.
  split; intros H.
  - unfold siota.
    apply SP.of_list_1.
    apply inA_iff.
    apply in_map_iff.
    destruct i; [exists 1%nat|exists (S i)%nat]; hauto l: on use: in_seq.
  - destruct i eqn:He; [sfirstorder|].
    apply SP.of_list_1 in H.
    rewrite inA_iff in H.
    rewrite in_map_iff in H.
    hauto l: on use: in_seq.
Qed.

(** ** Surjectivity of of_nat *)
Lemma of_nat_surj : forall p, exists n, Pos.of_nat n = p.
Proof.
  sfirstorder use: Pos2Nat.id.
Qed.

(** ** Siota subset relation *)
Lemma siota_subset p q : (p <= q)%nat -> S.Subset (siota p) (siota q).
Proof.
  intros H a Ha.
  destruct (of_nat_surj a) as [x <-].
  hfcrush use: siota_spec.
Qed.

(** ** Siota non-membership *)
Lemma siota_miss : forall p q,
    (q + 1 < S p)%nat -> ~ S.In (Pos.of_nat (S p)) (siota q).
Proof.
  intros p q H contra.
  apply siota_spec in contra.
  lia.
Qed.

(** ** Augmenting a coloring with an independent set *)
Lemma indep_set_union : forall (g : graph) (f : coloring) (s : nodeset) (p : colors) c,
    undirected g ->
    independent_set g s ->
    ~ S.In c p ->
    coloring_ok p g f ->
    coloring_ok (S.add c p) g (Munion (constant_color s c) f).
Proof.
  intros g f s p c H H0 H1 H2.
  split.
  - intros ci H5.
    apply S.add_spec.
    munion_cases H5.
    + left.
      apply constant_color_inv2 in H5.
      assumption.
    + right.
      sfirstorder.
  - intros ci cj H5 H6.
    munion_cases2 H5 H6.
    + intros contra.
      apply constant_color_inv in H5, H6.
      sfirstorder.
    + assert (cj <> c).
      {
        hauto lq: on rew: off unfold: coloring_ok, undirected.
      }
      apply constant_color_inv2 in H5.
      scongruence.
    + assert (ci <> c) by sfirstorder.
      apply constant_color_inv2 in H6.
      scongruence.
    + strivial unfold: coloring_ok.
Qed.

(** ** Phase2 colors are bounded by max_deg g + 1 *)
Lemma phase2_color_bound :
  forall (g : graph) (f : coloring) (g' : graph) (i : node) n,
    phase2 g = (f, g') ->
    M.find i f = Some (Pos.of_nat n) ->
    (n <= max_deg g + 1)%nat.
Proof.
  intros g f g' i n H H0.
  generalize dependent g'.
  generalize dependent f.
  functional induction (phase2 g) using phase2_ind.
  - intros f Hf g' Hg'.
    rewrite e in *.
    simpl.
    inversion Hg'.
    subst.
    clear Hg'.
    apply constant_color_inv2 in Hf.
    destruct n as [|[|n']]; sfirstorder.
  - intros f H0 g'0 H.
    inversion H.
    subst g''.
    rewrite <- H2 in H0.
    munion_cases H0.
    + apply constant_color_inv2 in H0.
      hauto l: on.
    + pose proof (IHp _ H0 g'0 e1).
      apply extract_vertices_degs_subgraph in e0.
      apply max_deg_subgraph in e0.
      hauto l: on.
Qed.

(** ** Phase2 only colors vertices of the input graph *)
Lemma phase2_domain_subset :
  forall g f g',
    phase2 g = (f, g') ->
    S.Subset (Mdomain f) (nodes g).
Proof.
  intros g f g' Hph.
  revert f Hph.
  functional induction (phase2 g) using phase2_ind.
  - (* base: max_deg g = 0 *)
    intros f Hf.
    inversion Hf; subst; clear Hf.
    intros H Hv.
    sauto lq: on rew: off use: constant_color_inv, in_domain.
  - (* step: max_deg g = S n *)
    intros f Hf.
    inversion Hf; subst; clear Hf.
    intros x Hx.
    (* membership in domain of Munion => membership in one branch *)
    rewrite in_domain in Hx.
    apply munion_in in Hx as [Hx|Hx].
    + (* x came from the fresh constant coloring on ns *)
      apply in_domain.
      remember (Pos.succ match n with
                  | 0%nat => 1
                  | S _ => Pos.succ (Pos.of_nat n)
                  end) as d.
      (* x ∈ ns by inversion on constant_color *)
      destruct Hx as [v Hv].
      apply constant_color_inv in Hv.
      (* vertices extracted lie in g and not in g' *)
      symmetry in e0.
      pose proof (extract_vertices_remove g g'0 ns (S n) e0).
      hauto l: on.
    + (* x came from the recursive coloring f' over g' *)
      hauto lq: on use: in_nodes_iff, in_domain, subgraph_vert_m, extract_vertices_degs_subgraph unfold: PositiveSet.Subset, coloring, PositiveMap.key, PositiveSet.elt.
Qed.

(** Any vertex colored by phase 2 is a vertex of the input graph. *)
Lemma phase2_find_in : forall g f g' i c,
    phase2 g = (f, g') -> M.find i f = Some c -> M.In i g.
Proof.
  intros g f g' i c Hph Hfi.
  apply in_nodes_iff. eapply phase2_domain_subset; eauto.
  apply in_domain. exists c. auto.
Qed.

(** ** Phase2 assigns distinct colors to adjacent vertices *)
Lemma phase2_colors_distinct :
  forall (g g' : graph) (i j ci cj : node) (f : coloring),
    undirected g ->
    no_selfloop g ->
    phase2 g = (f, g') ->
    S.In j (adj g i) ->
    M.find i f = Some ci ->
    M.find j f = Some cj ->
    ci <> cj.
Proof.
  intros g g' i j ci cj f Hund Hloop Hph Hadj Hfi Hfj.
  generalize dependent g'.
  generalize dependent f.
  revert Hadj ci cj.
  functional induction (phase2 g) using phase2_ind.
  - (* base: max_deg g = 0 *)
    intros Hadj ci cj f' Hfi' Hfj' g'' Hph'.
    sauto lq: on rew: off use: max_deg_0_adj.
  - (* step: max_deg g = S n *)
    intros Hadj ci cj f0 Hfi0 Hfj0 g''' Hph''.
    assert (Hund' : undirected g') by hauto l: on use: extract_vertices_degs_undirected.
    assert (Hloop' : no_selfloop g') by
      hauto l: on use: extract_vertices_degs_subgraph, subgraph_no_selfloop.
    specialize (IHp Hund' Hloop').
    inversion Hph''; subst.
    clear Hph''.
    replace (Pos.succ _) with (Pos.of_nat (S (S n))) in * by auto.
    (* Decompose the two lookups through Munion *)
    apply munion_case in Hfi0; apply munion_case in Hfj0.
    destruct Hfi0 as [Hi_now|Hi_later];
    destruct Hfj0 as [Hj_now|Hj_later].
    + (* both colored now → contradiction with independence of ns *)
      apply constant_color_inv in Hi_now.
      apply constant_color_inv in Hj_now.
      pose proof (max_degree_extraction_independent_set g (S n) Hund Hloop (eq_sym e)) as [Hind _].
      hauto l: on unfold: independent_set.
    + (* i now, j later → colors differ: j's color is in siota(max_deg g') but fresh color n' is not *)
      apply constant_color_inv2 in Hi_now. subst ci.
      destruct (of_nat_surj cj) as [x <-].
      pose proof (phase2_color_bound g' _ _ _ _ e1 Hj_later) as B.
      (* cj ∈ siota (max_deg g') and n' ∉ that set *)
      assert (S.In (Pos.of_nat x) (siota (max_deg g'))) by (apply siota_spec; lia).
      assert (~ S.In (Pos.of_nat (S (S n))) (siota (max_deg g'))) as Fresh.
      { (* max_deg g' < max_deg g *)
        pose proof (extract_vertices_max_degs g g' ns ltac:(hauto) ltac:(scongruence)).
        rewrite e in *.
        apply siota_miss; lia.
      }
      congruence.
    + (* j now, i later — symmetric to previous case *)
      apply constant_color_inv2 in Hj_now. subst cj.
      destruct (of_nat_surj ci) as [x <-].
      pose proof (phase2_color_bound g' _ _ _ _ e1 Hi_later) as B.
      assert (S.In (Pos.of_nat x) (siota (max_deg g'))) by (apply siota_spec; lia).
      assert (~ S.In (Pos.of_nat (S (S n))) (siota (max_deg g'))) as Fresh.
      { pose proof (extract_vertices_max_degs g g' ns ltac:(hauto) ltac:(scongruence)).
        rewrite e in *; apply siota_miss; lia. }
      congruence.
    + (* both later → use IH; first show the edge persists in g' *)
      (* If both are colored by f', they are in dom f' hence nodes g' *)
      assert (Di : M.In i g') by (eapply phase2_find_in; eauto).
      assert (Dj : M.In j g') by (eapply phase2_find_in; eauto).
      (* adjacency is preserved among surviving vertices *)
      assert (Hadj' : S.In j (adj g' i)).
      { rewrite adj_preserved_after_extract with (g := g).
        - scongruence.
        - hauto l: on.
        - assumption.
        - assumption.
      }
      hauto l: on.
Qed.

(** ** Correctness of phase2 coloring *)
Lemma phase2_ok : forall (g : graph),
    undirected g ->
    no_selfloop g ->
    coloring_ok (phase2_colors g) g (fst (phase2 g)).
Proof.
  intros g Hund Hloop.
  functional induction (phase2 g) using phase2_ind.
  - (* base: max_deg g = 0 *)
    (* all adjacency sets empty => constant_color is vacuously OK *)
    sfirstorder use: max_deg_0_adj unfold: coloring_ok.
  - (* step: max_deg g = S n *)
    remember (Pos.of_nat (S (S n))) as n'.
    rewrite e1 in *; simpl in IHp.
    assert (Hund' : undirected g') by strivial use: extract_vertices_degs_undirected.
    assert (Hloop' : no_selfloop g') by hauto l: on use: extract_vertices_degs_subgraph, subgraph_no_selfloop.
    specialize (IHp Hund' Hloop'). simpl in IHp.
    (* ns is independent, and all are max-degree vertices *)
    pose proof (max_degree_extraction_independent_set g (S n) Hund Hloop (eq_sym e)) as [Hind Hdeg].
    (* First: show the recursive coloring f' is OK on g with palette siota(max_deg g') *)
    assert (Hok_rec_on_g : coloring_ok (siota (max_deg g')) g f').
    { (* prove the two conjuncts explicitly to avoid dependence on edges in g' only *)
      split.
      - (* palette membership for any colored i *)
        intros ci Hfi.
        destruct (of_nat_surj ci) as [x <-].
        apply siota_spec.
        hauto l: on use: phase2_color_bound.
      - (* adjacent vertices get different colors *)
        intros ci cj H0 H1.
        pose proof (phase2_domain_subset g' f' g'' e1) as DomSub.
        assert (Hi_dom : S.In i (Mdomain f')).
        {
          qauto use: in_domain, WF.in_find_iff unfold: coloring, node, PositiveSet.elt, PositiveOrderedTypeBits.t, PositiveMap.key.
        }
        assert (Hj_dom : S.In j (Mdomain f')).
        {
          qauto use: WF.in_find_iff, in_domain unfold: coloring, PositiveMap.key, PositiveSet.elt.
        }
        pose proof (DomSub _ Hi_dom) as Hi_nodes'.
        pose proof (DomSub _ Hj_dom) as Hj_nodes'.
        assert (Hadj' : S.In j (adj g' i)).
        {
          assert (M.In i g') by hauto l: on use: in_domain.
          assert (M.In j g') by hauto l: on use: in_domain.
          pose proof (adj_preserved_after_extract _ _ _ _ i j e0 H2 H3).
          sauto lq: on.
        }
        strivial unfold: coloring_ok.
    }
    (* Combine the independent-set constant coloring with f' *)
    assert (Hok_union :
      coloring_ok (S.add n' (siota (max_deg g'))) g (Munion (constant_color ns n') f')).
    { eapply indep_set_union; eauto.
      hauto lq: on unfold: fst.
      (* Freshness: n' ∉ siota (max_deg g') *)
      assert (Fresh : ~ S.In n' (siota (max_deg g'))).
      { (* max_deg g' < max_deg g *)
        pose proof (extract_vertices_max_degs g g' ns ltac:(hauto) ltac:(scongruence)).
        rewrite e in *.
        hauto l: on use: siota_miss.
      }
      exact Fresh.
    }
    (* Finally, enlarge the palette from {n'}∪siota(max_deg g') to siota(max_deg g) *)
    assert (S.Subset (S.add n' (siota (max_deg g'))) (siota (max_deg g))) as Pal_incl.
    { intros a Ha.
      apply S.add_spec in Ha as [->|Ha]; subst.
      - apply siota_spec.
        lia.
      - (* show n' ∈ siota(max_deg g) *)
        assert (is_subgraph g' g).
        { hauto l: on use: extract_vertices_degs_subgraph. }
        pose proof (max_deg_subgraph g g' H).
        clear -Ha H0.
        sauto lq: on use: siota_subset unfold: PositiveSet.Subset.
    }
    (* palette grows monotonically *)
    eapply ok_coloring_subset; eauto.
Qed.

(** ** Definition of the full Wigderson algorithm *)
Definition wigderson (k : nat) (g : graph) : coloring :=
  let '(f1, g') := phase1 k 1 g in
  let offset := max_color f1 in
  Munion f1 (M.map (Pos.add offset) (fst (phase2 g'))).

(** ** Correctness of Wigderson's algorithm *)
Theorem wigderson_ok k g f p :
  undirected g -> no_selfloop g ->
  coloring_complete p g f -> three_coloring f p ->
  forall i j ci cj,
    S.In j (adj g i) ->
    M.find i (wigderson k g) = Some ci ->
    M.find j (wigderson k g) = Some cj -> ci <> cj.
Proof.
  intros Ug Hloop Hcol H3 i j ci cj Hadj Hfi Hfj.
  unfold wigderson in Hfi, Hfj.
  destruct (phase1 k 1 g) as [f1 g'] eqn:Eph.
  set (offset := max_color f1) in *.
  set (f2 := fst (phase2 g')) in *.
  set (f2' := M.map (Pos.add offset) f2) in *.
  assert (Ug' : undirected g').
  { assert (H := phase1_undirected k 1 g Ug). rewrite Eph in H. simpl in H. exact H. }
  assert (Hloop' : no_selfloop g').
  { assert (H := phase1_no_selfloop k 1 g Hloop). rewrite Eph in H. simpl in H. exact H. }
  munion_cases2 Hfi Hfj.
  - (* Both from f1: use phase1_coloring_ok *)
    assert (Hfi' : M.find i (fst (phase1 k 1 g)) = Some ci) by (rewrite Eph; simpl; auto).
    assert (Hfj' : M.find j (fst (phase1 k 1 g)) = Some cj) by (rewrite Eph; simpl; auto).
    exact (phase1_coloring_ok k 1 g f p Ug Hloop Hcol H3 i j ci cj Hadj Hfi' Hfj').
  - (* i from f1, j from f2': color bounds separate *)
    assert (Hci : (ci <= offset)%positive) by (apply max_color_spec with (i := i); auto).
    unfold f2' in Hfj. rewrite map_o in Hfj.
    destruct (M.find j f2) as [cj_orig|] eqn:Ecj; [|simpl in Hfj; discriminate].
    simpl in Hfj. injection Hfj as <-.
    (* cj = offset + cj_orig > offset >= ci *)
    intro Heq. lia.
  - (* i from f2', j from f1: symmetric *)
    assert (Hcj : (cj <= offset)%positive) by (apply max_color_spec with (i := j); auto).
    unfold f2' in Hfi. rewrite map_o in Hfi.
    destruct (M.find i f2) as [ci_orig|] eqn:Eci; [|simpl in Hfi; discriminate].
    simpl in Hfi. injection Hfi as <-.
    intro Heq. lia.
  - (* Both from f2': use phase2_colors_distinct *)
    unfold f2', f2 in Hfi, Hfj.
    rewrite map_o in Hfi, Hfj.
    destruct (phase2 g') as [f2_res g''] eqn:Ep2.
    simpl in Hfi, Hfj.
    destruct (M.find i f2_res) as [ci_orig|] eqn:Eci; [|simpl in Hfi; discriminate].
    destruct (M.find j f2_res) as [cj_orig|] eqn:Ecj; [|simpl in Hfj; discriminate].
    simpl in Hfi, Hfj.
    injection Hfi as Hci_eq. injection Hfj as Hcj_eq.
    (* Show ci_orig ≠ cj_orig via phase2_colors_distinct *)
    assert (Hi_g' : M.In i g') by (eapply phase2_find_in; eauto).
    assert (Hj_g' : M.In j g') by (eapply phase2_find_in; eauto).
    assert (Hg'_eq : g' = snd (phase1 k 1 g)) by (rewrite Eph; auto).
    assert (Hadj' : S.In j (adj g' i)).
    { rewrite Hg'_eq.
      apply phase1_adj_preserved; auto.
      - rewrite Hg'_eq in Hi_g'. auto.
      - rewrite Hg'_eq in Hj_g'. auto. }
    assert (Hneq_orig : ci_orig <> cj_orig).
    { eapply phase2_colors_distinct; eauto. }
    subst ci cj. intro Heq. lia.
Qed.

(** ** Color bound for Wigderson's algorithm *)

(** fold_left with Pos.max is bounded when all list values are bounded *)
Lemma fold_left_max_bounded_nat : forall l acc (B : nat),
  (Pos.to_nat acc <= B)%nat ->
  (forall i ci, In (i, ci) l -> (Pos.to_nat ci <= B)%nat) ->
  (Pos.to_nat (fold_left (fun (a : positive) (p : M.key * positive) => Pos.max (snd p) a) l acc) <= B)%nat.
Proof.
  induction l as [|[k v] l IH]; intros acc B Hacc Hall; simpl.
  - auto.
  - apply IH.
    + assert (Hv : (Pos.to_nat v <= B)%nat).
      { apply Hall with (i := k). left. auto. }
      unfold Pos.max. destruct (Pos.compare_spec v acc); subst; lia.
    + intros j cj Hj. apply Hall with (i := j). right. auto.
Qed.

(** max_color is bounded if all values in the coloring are bounded *)
Lemma max_color_bound_nat : forall f (B : nat),
  (1 <= B)%nat ->
  (forall i ci, M.find i f = Some ci -> (Pos.to_nat ci <= B)%nat) ->
  (Pos.to_nat (max_color f) <= B)%nat.
Proof.
  intros f B HB Hall.
  unfold max_color. rewrite M.fold_1.
  apply fold_left_max_bounded_nat; auto.
  intros i ci Hi.
  apply Hall with (i := i).
  apply M.elements_complete. auto.
Qed.

(** If there are no high-degree vertices, then max_deg g <= k *)
Lemma no_high_deg_max_deg_le : forall k g,
  S.Empty (subset_nodes (high_deg k) g) ->
  (max_deg g <= k)%nat.
Proof.
  intros k g Hempty.
  destruct (Nat.le_gt_cases (max_deg g) k) as [|Hgt]; auto.
  exfalso.
  destruct (M.elements g) eqn:Hel.
  - (* empty graph: max_deg = 0 *)
    unfold max_deg in Hgt. rewrite Hel in Hgt. simpl in Hgt. lia.
  - assert (Hne : ~ M.Empty g).
    { intro He. apply WP.elements_Empty in He. rewrite Hel in He. discriminate. }
    destruct (max_degree_vert g (max_deg g) Hne (Logic.eq_refl _)) as [v Hv].
    apply degree_spec in Hv. destruct Hv as [Hvin Hdeg].
    apply Hempty with (a := v).
    unfold subset_nodes. apply in_domain.
    assert (HIn : M.In v g) by (apply in_nodes_iff; auto).
    destruct HIn as [e He].
    exists e. apply WP.filter_iff;
      [intros x y Heq a b Hab; subst; auto |].
    split; auto.
    unfold high_deg. apply Nat.ltb_lt.
    unfold adj in Hdeg. rewrite He in *. lia.
Qed.

(** Phase1 residual graph has max_deg <= k *)
Lemma phase1_residual_max_deg : forall k c g,
  undirected g -> (max_deg (snd (phase1 k c g)) <= k)%nat.
Proof.
  intros k c g Ug.
  apply no_high_deg_max_deg_le. apply phase1_no_high_deg. auto.
Qed.

(** Cardinal of set difference when B is a subset of A *)
Lemma cardinal_diff_subset : forall A B,
  S.Subset B A ->
  (S.cardinal (S.diff A B) + S.cardinal B = S.cardinal A)%nat.
Proof.
  intros A B Hsub.
  assert (Heq : S.Equal A (S.union (S.diff A B) B)).
  { intros x. rewrite S.union_spec, S.diff_spec. split.
    - intros Hx. destruct (SP.In_dec x B); [right|left]; auto.
    - intros [[]|]; auto. }
  assert (Hdisj : S.Empty (S.inter (S.diff A B) B)).
  { intros x Hx. apply S.inter_spec in Hx as [Hd Hb].
    apply S.diff_spec in Hd as [_ Hnb]. auto. }
  rewrite (SP.Equal_cardinal Heq).
  assert (Hinter0 : S.cardinal (S.inter (S.diff A B) B) = 0%nat).
  { apply SP.cardinal_Empty. auto. }
  pose proof (SP.union_inter_cardinal (S.diff A B) B). lia.
Qed.

(** Each phase1 step removes at least k+2 vertices *)
Lemma phase1_removes_many : forall k g v,
  undirected g -> no_selfloop g ->
  S.In v (subset_nodes (high_deg k) g) ->
  (M.cardinal (remove_nodes g (S.add v (nodes (neighborhood g v)))) + k + 2
   <= M.cardinal g)%nat.
Proof.
  intros k g v Ug Hloop Hv.
  (* v is high-degree: S.cardinal (adj g v) > k *)
  assert (HvIn : S.In v (nodes g)) by (eapply subset_nodes_sub; eauto).
  unfold subset_nodes in Hv. apply in_domain in Hv. destruct Hv as [e Hfe].
  apply WP.filter_iff in Hfe; [| intros x y Heq a b Hab; subst; auto].
  destruct Hfe as [Hfind Hhigh].
  unfold high_deg in Hhigh. apply Nat.ltb_lt in Hhigh.
  (* nodes(neighborhood g v) = adj g v *)
  assert (Hneq : S.Equal (nodes (neighborhood g v)) (adj g v)).
  { apply neighborhood_nodes_equal_adj; auto. }
  (* v ∉ adj g v *)
  assert (Hvna : ~ S.In v (adj g v)) by (apply Hloop).
  (* S.cardinal (S.add v (adj g v)) >= k + 2 *)
  assert (Hadj_eq : adj g v = e).
  { unfold adj. unfold M.MapsTo in Hfind. rewrite Hfind. auto. }
  assert (Hcard_add : (S.cardinal (S.add v (nodes (neighborhood g v))) >= k + 2)%nat).
  { assert (Hvna' : ~ S.In v (nodes (neighborhood g v))) by (rewrite Hneq; auto).
    rewrite SP.add_cardinal_2 by auto.
    assert (S.cardinal (nodes (neighborhood g v)) = S.cardinal (adj g v)).
    { apply SP.Equal_cardinal. auto. }
    rewrite Hadj_eq in *. lia. }
  (* S.add v (nodes nbhd) ⊆ nodes g *)
  assert (Hsub : S.Subset (S.add v (nodes (neighborhood g v))) (nodes g)).
  { intros x Hx. apply S.add_spec in Hx as [->|Hx]; auto.
    rewrite Hneq in Hx. eapply in_adj_neighbor_in_nodes; eauto. }
  (* M.cardinal (remove_nodes ...) = S.cardinal(nodes g) - S.cardinal(S.add v ...) *)
  rewrite !m_cardinal_domain.
  change (Mdomain g) with (nodes g).
  change (Mdomain (remove_nodes g (S.add v (nodes (neighborhood g v))))) with
    (nodes (remove_nodes g (S.add v (nodes (neighborhood g v))))).
  rewrite nodes_remove_nodes_eq.
  pose proof (cardinal_diff_subset _ _ Hsub). lia.
Qed.

(** Arithmetic helper: b + m <= a implies b/m + 1 <= a/m *)
Lemma nat_div_step : forall a m b,
  (m > 0)%nat -> (b + m <= a)%nat -> (b / m + 1 <= a / m)%nat.
Proof.
  intros a m b Hm Hle.
  replace (b / m + 1)%nat with ((b + 1 * m) / m)%nat by
    (rewrite Nat.div_add; lia).
  apply Nat.div_le_mono; lia.
Qed.

(** Main inductive bound: phase1 colors are bounded *)
Lemma phase1_color_upper_bound : forall k c g i ci,
  undirected g -> no_selfloop g ->
  M.find i (fst (phase1 k c g)) = Some ci ->
  (Pos.to_nat ci + 1 <= Pos.to_nat c + 3 * (M.cardinal g / (k + 2)))%nat.
Proof.
  intros k c g.
  remember (M.cardinal g) as n eqn:Hn.
  revert k c g Hn.
  induction n as [n IH] using lt_wf_ind.
  intros k c g Hn i ci Ug Hloop Hfi.
  rewrite phase1_equation in Hfi.
  destruct (S.choose (subset_nodes (high_deg k) g)) as [v|] eqn:Echoose.
  - set (nbhd := neighborhood g v) in *.
    set (m' := two_color_nbd g v (c+1) (c+2)) in *.
    set (g' := remove_nodes g (S.add v (nodes nbhd))) in *.
    destruct (phase1 k (c+3) g') as [f2 g2] eqn:Eph. simpl in Hfi.
    assert (Hlt : (M.cardinal g' < n)%nat).
    { subst n. unfold g'. eapply remove_nodes_lt with (i := v).
      - apply S.add_spec. left. reflexivity.
      - eapply chosen_high_deg_in; eauto. }
    assert (Ug' : undirected g') by (unfold g'; apply remove_nodes_undirected; auto).
    assert (Hloop' : no_selfloop g') by
      (unfold g'; eapply subgraph_no_selfloop; [apply remove_nodes_subgraph | auto]).
    assert (Hvin : S.In v (subset_nodes (high_deg k) g)).
    { apply S.choose_1 in Echoose. auto. }
    assert (Hremoves : (M.cardinal g' + k + 2 <= n)%nat).
    { subst n. unfold g'. apply phase1_removes_many; auto. }
    munion_cases Hfi.
    + (* Current step: ci is c, c+1, or c+2 *)
      destruct (E.eq_dec i v) as [->|Hne].
      * rewrite M.gss in Hfi. injection Hfi as <-.
        assert (Hge : (k + 2 <= n)%nat) by lia.
        assert (Hdiv1 : (1 <= n / (k + 2))%nat).
        { apply Nat.div_le_lower_bound; lia. }
        lia.
      * rewrite M.gso in Hfi by auto.
        apply force_all_palette in Hfi. destruct Hfi as [Hci|Hci]; subst ci.
        -- assert (Hge : (k + 2 <= n)%nat) by lia.
           assert (Hdiv1 : (1 <= n / (k + 2))%nat).
           { apply Nat.div_le_lower_bound; lia. }
           rewrite Pos2Nat.inj_add. lia.
        -- assert (Hge : (k + 2 <= n)%nat) by lia.
           assert (Hdiv1 : (1 <= n / (k + 2))%nat).
           { apply Nat.div_le_lower_bound; lia. }
           rewrite Pos2Nat.inj_add. lia.
    + (* Recursive step *)
      assert (IHres : (Pos.to_nat ci + 1 <= Pos.to_nat (c+3) + 3 * (M.cardinal g' / (k + 2)))%nat).
      { eapply (IH _ Hlt k (c+3) g' (Logic.eq_refl _) i ci Ug' Hloop').
        rewrite Eph. simpl. exact Hfi. }
      rewrite Pos2Nat.inj_add in IHres.
      assert (Hdiv_step : (M.cardinal g' / (k + 2) + 1 <= n / (k + 2))%nat).
      { apply nat_div_step; lia. }
      lia.
  - simpl in Hfi. rewrite WF.empty_o in Hfi. discriminate.
Qed.

(** Final theorem: every color assigned by wigderson is bounded *)
Theorem wigderson_color_bound : forall k g i ci,
  undirected g -> no_selfloop g ->
  M.find i (wigderson k g) = Some ci ->
  (Pos.to_nat ci <= 3 * (M.cardinal g / (k + 2)) + k + 2)%nat.
Proof.
  intros k g i ci Ug Hloop Hfi.
  unfold wigderson in Hfi.
  destruct (phase1 k 1 g) as [f1 g'] eqn:Eph.
  set (offset := max_color f1) in *.
  set (f2 := fst (phase2 g')) in *.
  set (f2' := M.map (Pos.add offset) f2) in *.
  munion_cases Hfi.
  - (* Phase1 color *)
    assert (Hfi' : M.find i (fst (phase1 k 1 g)) = Some ci) by (rewrite Eph; simpl; auto).
    assert (Hbound := phase1_color_upper_bound k 1 g i ci Ug Hloop Hfi').
    simpl in Hbound. lia.
  - (* Phase2 color: ci = offset + c2_orig *)
    unfold f2' in Hfi. rewrite map_o in Hfi.
    destruct (M.find i f2) as [ci_orig|] eqn:Eci; [|simpl in Hfi; discriminate].
    simpl in Hfi. injection Hfi as <-.
    (* Bound offset *)
    assert (Hoffset_bound : (Pos.to_nat offset <= 3 * (M.cardinal g / (k + 2)) + 1)%nat).
    { apply max_color_bound_nat; [lia |].
      intros j cj Hfj.
      assert (Hfj' : M.find j (fst (phase1 k 1 g)) = Some cj) by (rewrite Eph; simpl; auto).
      pose proof (phase1_color_upper_bound k 1 g j cj Ug Hloop Hfj') as Hb.
      simpl in Hb. lia. }
    (* Bound ci_orig: by phase2_color_bound + phase1_residual_max_deg *)
    assert (Hci_bound : (Pos.to_nat ci_orig <= k + 1)%nat).
    { unfold f2 in Eci.
      destruct (phase2 g') as [f2_res g''] eqn:Ep2. simpl in Eci.
      assert (Hmd : (max_deg g' <= k)%nat).
      { assert (Hmd := phase1_residual_max_deg k 1 g Ug). rewrite Eph in Hmd. simpl in Hmd. auto. }
      (* ci_orig is a color of phase2, so Pos.of_nat (Pos.to_nat ci_orig) = ci_orig *)
      pose proof (phase2_color_bound g' f2_res g'' i (Pos.to_nat ci_orig) Ep2) as Hpcb.
      rewrite Pos2Nat.id in Hpcb.
      specialize (Hpcb Eci). lia. }
    (* Total *)
    rewrite Pos2Nat.inj_add. lia.
Qed.

(** ** Asymptotic O(sqrt n) color bound *)

Lemma sqrt_div_le : forall n,
  (n / (Nat.sqrt n + 2) <= Nat.sqrt n)%nat.
Proof.
  intros n.
  apply Nat.div_le_upper_bound; [lia |].
  destruct n as [|n'].
  - simpl. lia.
  - pose proof (Nat.sqrt_spec (S n') ltac:(lia)) as [_ Hhi]. nia.
Qed.

(** With [k = sqrt |V|], wigderson colors [g] with [O(sqrt |V|)] colors. *)
Theorem wigderson_sqrt_bound : forall g i ci,
  undirected g -> no_selfloop g ->
  M.find i (wigderson (Nat.sqrt (M.cardinal g)) g) = Some ci ->
  (Pos.to_nat ci <= 4 * Nat.sqrt (M.cardinal g) + 2)%nat.
Proof.
  intros g i ci Ug Hloop Hfi.
  pose proof (wigderson_color_bound (Nat.sqrt (M.cardinal g)) g i ci Ug Hloop Hfi) as H.
  pose proof (sqrt_div_le (M.cardinal g)). lia.
Qed.
