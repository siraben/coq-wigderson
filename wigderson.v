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


(* Predicate that takes a vertex with high degree (> K) *)
Definition high_deg (K: nat) (n: node) (adj: nodeset) : bool := K <? S.cardinal adj.

Definition injective {A B} (f : A -> B) := forall x y, f x = f y -> x = y.

Local Open Scope positive_scope.


(** Wigderson's algorithm definition

    Let G be a graph, |G.v| = k.
    A vertex v is high-degree if deg(v) > sqrt(k).
    Phase 1 is selecting the high-degree vertices and coloring their neighborhoods.
    Phase 2 is coloring the remaining nodes with at most sqrt(k) colors.
 *)

(** ** Termination of selectW *)
Lemma selectW_terminates:
  forall (K: nat) (g : graph) (n : S.elt),
   S.choose (subset_nodes (high_deg K) g) = Some n ->
   (M.cardinal (remove_node n g) < M.cardinal g)%nat.
Proof.
  intros K g n H.
  unfold remove_node.
  assert (~ M.In n (remove_node n g)) by strivial use: in_remove_node_iff.
  assert (M.In n g).
  {
    assert (S.In n (subset_nodes (high_deg K) g))
      by hauto l: on use: S.choose_1.
    pose proof (subset_nodes_sub (high_deg K) g n H1).
    unfold nodes, Mdomain in H2.
    now apply in_domain in H2.
  }
  rewrite cardinal_map.
  now apply m_remove_cardinal_less.
Qed.

Function selectW (K: nat) (g: graph) {measure M.cardinal g} : list node :=
  match S.choose (subset_nodes (high_deg K) g) with
  | Some n => n :: selectW K (remove_node n g)
  | None => nil
  end.
Proof. apply selectW_terminates.
Defined.

(** ** Property of subset_nodes *)
Lemma subset_nodes_prop : forall (P: node -> nodeset -> bool) (g: graph) v,
    S.In v (subset_nodes P g) -> P v (adj g v) = true.
Proof.
  intros P g v H.
  unfold subset_nodes in H.
  apply in_domain in H.
  destruct H as [e He].
  epose proof (@WP.filter_iff _ P _ g v e).
  rewrite H in He.
  unfold adj.
  sauto.
Qed.

(* If a node m is removed from the graph then the cardinality of the
  adj set of a vertex v is decreasing. *)
(** ** Cardinality of adjacency set after removing a node *)
Lemma cardinal_remove : forall g v m,
    (S.cardinal (adj (remove_node m g) v) <= S.cardinal (adj g v))%nat.
Proof.
  intros g v m.
  unfold adj.
  destruct (WF.In_dec g v).
  - ssimpl.
    subst.
    unfold nodeset, node, remove_node in *.
    assert (n0 = x) by scongruence.
    subst.
    (* Note: why is this not more automatic *)
    destruct (E.eq_dec v m).
    + ecrush use: map_o, M.grs.
    + unfold nodeset in *.
      rewrite map_o, M.gro in Heqo by auto.
      qauto use: SP.subset_cardinal, PositiveSet.remove_3 unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, option_map, PositiveSet.Subset.
  - hauto lq: on use: remove_node_subgraph, SP.subset_cardinal unfold: PositiveMap.In, PositiveSet.t, is_subgraph, nodeset, PositiveMap.MapsTo, PositiveSet.Subset, adj inv: option.
Qed.

(* If v is in the list returned by selectW then the cardinality of v is indeed high. *)
(** ** Vertices selected by selectW have high degree *)
Lemma select_hi_deg : forall n g v, In v (selectW n g) -> (S.cardinal (adj g v) > n)%nat.
Proof.
  intros n g v.
  functional induction (selectW n g) using selectW_ind.
  - intros H.
    destruct H.
    + subst.
      clear IHl.
      assert (S.In v (subset_nodes (high_deg n) g)).
      {
        hauto q: on use: PositiveSet.choose_1 inv: option.
      }
      hauto lqb: on drew: off use: subset_nodes_prop unfold: high_deg.
    + specialize (IHl H).
      hfcrush use: cardinal_remove unfold: PositiveOrderedTypeBits.t, PositiveSet.elt, PositiveSet.t, adj, node, nodeset, PositiveSet.empty.
  - sfirstorder.
Qed.

(* Phase 1 of Wigderson *)
(* Let:
- k: bound for degree of vertices
- c: color currently used
- g: graph
- f: coloring
- H: proof that g is 3-colorable
- H1: proof that f is a complete coloring of g
- Hf: proof that f is a 3-coloring

phase1(g,c):
  if a high degree vertex in g exists:
    v := select a high-degree vertex in g
    nbhd := neighborhood of v in g
    coloring_of_nbhd := 2-coloring of nbhd using c+1 and c+2
    g' := remove nbhd from g
    return union(coloring_of_nbhd, phase1(g',c+2))
  else:
    return empty coloring

 *)
Require Import Program.

(* Two-coloring of a neighborhood using BFS-based forcing *)
Definition two_color_nbd (g : graph) (v : node) (c1 c2 : positive) : coloring :=
  force_all (neighborhood g v) c1 c2.

(* Two coloring of a neighborhood of a 3-colorable graph is complete *)

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
    apply munion_case in Hfi as [Hfi|Hfi].
    + destruct (E.eq_dec i v) as [->|Hne].
      * rewrite M.gss in Hfi. injection Hfi as <-. lia.
      * rewrite M.gso in Hfi by auto.
        apply force_all_palette in Hfi. destruct Hfi; subst; lia.
    + assert (Hlt : (M.cardinal g' < n)%nat).
      { subst n. unfold g'.
        eapply remove_nodes_lt with (i := v).
        - apply S.add_spec. left. reflexivity.
        - apply in_nodes_iff. apply S.choose_1 in Echoose.
          apply subset_nodes_sub in Echoose. auto. }
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
    apply munion_case in Hfi as [Hfi|Hfi].
    + destruct (E.eq_dec i v) as [->|Hne].
      * apply in_nodes_iff. apply S.choose_1 in Echoose. apply subset_nodes_sub in Echoose. auto.
      * rewrite M.gso in Hfi by auto.
        unfold m', two_color_nbd in Hfi.
        eapply subgraph_vert_m; [apply nbd_subgraph |].
        eapply force_all_domain; eauto.
        apply neighborhood_undirected. auto.
    + assert (Hlt : (M.cardinal g' < n)%nat).
      { subst n. unfold g'. eapply remove_nodes_lt with (i := v).
        - apply S.add_spec. left. reflexivity.
        - apply in_nodes_iff. apply S.choose_1 in Echoose. apply subset_nodes_sub in Echoose. auto. }
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
    apply munion_case in Hfi as [Hfi|Hfi];
    apply munion_case in Hfj as [Hfj|Hfj].
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
        - apply in_nodes_iff. apply S.choose_1 in Echoose.
          apply subset_nodes_sub in Echoose. auto. }
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
        - intro contra. apply in_nodes_iff in Hj_g'. unfold g' in Hj_g'.
          rewrite nodes_remove_nodes_eq in Hj_g'.
          apply S.diff_spec in Hj_g'. tauto.
        - intro contra. apply in_nodes_iff in Hi_g'. unfold g' in Hi_g'.
          rewrite nodes_remove_nodes_eq in Hi_g'.
          apply S.diff_spec in Hi_g'. tauto. }
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
      - apply in_nodes_iff. apply S.choose_1 in Echoose.
        apply subset_nodes_sub in Echoose. auto. }
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
      - apply in_nodes_iff. apply S.choose_1 in Echoose.
        apply subset_nodes_sub in Echoose. auto. }
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
      - apply in_nodes_iff. apply S.choose_1 in Echoose.
        apply subset_nodes_sub in Echoose. auto. }
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
      - apply in_nodes_iff. apply S.choose_1 in Echoose.
        apply subset_nodes_sub in Echoose. auto. }
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
      - apply in_nodes_iff. apply S.choose_1 in Echoose.
        apply subset_nodes_sub in Echoose. auto. }
    assert (Ug' : undirected g') by (unfold g'; apply remove_nodes_undirected; auto).
    (* g2 is a subgraph of g' *)
    assert (Hsub : is_subgraph g2 g').
    { pose proof (phase1_subgraph k (c+3) g'). rewrite Eph in H. simpl in H. exact H. }
    (* i,j are in g' since g2 ⊆ g' *)
    assert (Hi' : M.In i g') by (eapply subgraph_vert_m; eauto).
    assert (Hj' : M.In j g') by (eapply subgraph_vert_m; eauto).
    (* i,j not in the removed set *)
    assert (Hni : ~ S.In i (S.add v (nodes nbhd))).
    { intro contra. apply in_nodes_iff in Hi'. unfold g' in Hi'.
      rewrite nodes_remove_nodes_eq in Hi'. apply S.diff_spec in Hi'. tauto. }
    assert (Hnj : ~ S.In j (S.add v (nodes nbhd))).
    { intro contra. apply in_nodes_iff in Hj'. unfold g' in Hj'.
      rewrite nodes_remove_nodes_eq in Hj'. apply S.diff_spec in Hj'. tauto. }
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

Lemma Pos_max_le_compat_r : forall v a b,
  (a <= b)%positive -> (Pos.max v a <= Pos.max v b)%positive.
Proof.
  intros v a b H.
  unfold Pos.max.
  destruct (Pos.compare_spec v a); destruct (Pos.compare_spec v b); lia.
Qed.

Lemma fold_left_max_mono : forall l (acc1 acc2 : positive),
  (acc1 <= acc2)%positive ->
  (fold_left (fun (a : positive) (p : M.key * positive) => Pos.max (snd p) a) l acc1 <=
   fold_left (fun (a : positive) (p : M.key * positive) => Pos.max (snd p) a) l acc2)%positive.
Proof.
  induction l as [|[k v] l IH]; intros acc1 acc2 H; simpl.
  - auto.
  - apply IH. apply Pos_max_le_compat_r. auto.
Qed.

Lemma fold_left_max_le_acc : forall l (acc : positive),
  (acc <= fold_left (fun (a : positive) (p : M.key * positive) => Pos.max (snd p) a) l acc)%positive.
Proof.
  induction l as [|[k v] l IH]; intros acc; simpl.
  - lia.
  - etransitivity; [apply Pos.le_max_r | apply IH].
Qed.

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

Lemma max_color_spec : forall f i ci,
  M.find i f = Some ci -> (ci <= max_color f)%positive.
Proof.
  intros f i ci Hfi.
  unfold max_color. rewrite M.fold_1.
  apply fold_left_max_in with (i := i).
  apply M.elements_correct. auto.
Qed.

(* things we want to prove:
 - let d be the number of iterations
 - prove that the resulting color uses 2d+1 colors
   - induction on size of graph
   - two new colors each time
   - base case: no more high degree vertices, color with phase2
 - there are no more high-degree nodes (this is the hypothesis for phase2)
 - need to identify the terminal properties for phase1 to supply to phase2
 *)
(* induction on M.cardinal g *)
Check phase1.
(* Lemmas:
- you can color any graph with max degree + 1 colors
- can prove 3*(sqrt n) + 1
 *)


(** * Phase 2 of Wigderson *)
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

(** ** Phase 2 on max degree 0 graphs *)
Lemma phase2_0 (g : graph) : max_deg g = 0%nat -> phase2 g = (constant_color (nodes g) 1, @M.empty _).
Proof.
  intros H.
  hauto lq: on use: phase2_equation.
Qed.

Lemma no_selfloop_dec (g : graph) : {no_selfloop g} + {~ no_selfloop g}.
Proof.
  unfold no_selfloop.
  remember (M.elements g) as l.
  refine (_ (Exists_dec (fun (p : M.key * nodeset) => let (a,b) := p in S.In a b) l _)).
  - intros H.
    destruct H.
    + right.
      intros contra.
      apply Exists_exists in e.
      destruct e as [[k n] [Hx Hx']].
      unfold adj in contra.
      rewrite Heql in Hx.
      pose proof (contra k).
      apply H.
      apply M.elements_complete in Hx.
      hauto lq: on.
    + left.
      intros i contra.
      apply n.
      apply Exists_exists.
      unfold adj in contra.
      destruct (M.find i g) eqn:E; [|sauto].
      exists (i, n0).
      sfirstorder use: M.elements_correct.
  - hauto lq: on use: SP.In_dec.
Defined.

Example phase_2_example : coloring_ok (SP.of_list [1;2;4]) ex_graph (fst (phase2 ex_graph)).
Proof.
  split.
  - intros ci Hci.
    apply M.elements_correct in Hci.
    compute in Hci.
    hauto l: on.
  - intros ci cj Hci Hcj.
    apply M.elements_correct in Hci, Hcj.
    compute in Hci.
    compute in Hcj.
    hauto l: on.
Qed.

(* Next steps:
 - how can we know a-priori what colors are used in phase2?
 - prove that the coloring returned by phase2 is ok
 - actually we're trying to prove that phase2 uses _at most_ max_deg + 1 colors
 - the coloring_ok predicate can overapproximate
*)

Definition siota p := SP.of_list (map Pos.of_nat (seq 1 (p + 1))).
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

(* if we have an independent set, we can augment any valid coloring
   with it to obtain another valid coloring *)
(** ** Augmenting a coloring with an independent set  *)
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
    apply munion_case in H5.
    destruct H5.
    + left.
      apply constant_color_inv2 in H4.
      assumption.
    + right.
      sfirstorder.
  - intros ci cj H5 H6.
    apply munion_case in H5, H6.
    destruct H5, H6.
    + intros contra.
      apply constant_color_inv in H4, H5.
      sfirstorder.
    + assert (cj <> c).
      {
        hauto lq: on rew: off unfold: coloring_ok, undirected.
      }
      apply constant_color_inv2 in H4.
      scongruence.
    + assert (ci <> c) by sfirstorder.
      apply constant_color_inv2 in H5.
      scongruence.
    + strivial unfold: coloring_ok.
Qed.

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
    apply munion_case in H0.
    destruct H0.
    + apply constant_color_inv2 in H0.
      hauto l: on.
    + pose proof (IHp _ H0 g'0 e1).
      apply extract_vertices_degs_subgraph in e0.
      apply max_deg_subgraph in e0.
      hauto l: on.
Qed.

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
      assert (Di : M.In i g').
      { apply phase2_domain_subset with (g' := g''') in e1.
        clear -e1 Hi_later.
        hecrush use: in_domain.
      }
      assert (Dj : M.In j g').
      { apply phase2_domain_subset with (g' := g''') in e1.
        clear -e1 Hj_later.
        hecrush use: in_domain.
      }      
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
  apply munion_case in Hfi as [Hfi|Hfi];
  apply munion_case in Hfj as [Hfj|Hfj].
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
    assert (Hi_g' : M.In i g').
    { apply in_nodes_iff. eapply phase2_domain_subset; eauto.
      apply in_domain. exists ci_orig. auto. }
    assert (Hj_g' : M.In j g').
    { apply in_nodes_iff. eapply phase2_domain_subset; eauto.
      apply in_domain. exists cj_orig. auto. }
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

(** Adjacency set is a subset of nodes for undirected graphs *)
Lemma adj_subset_nodes : forall g v,
  undirected g -> S.Subset (adj g v) (nodes g).
Proof.
  intros g v Ug x Hx. eapply in_adj_neighbor_in_nodes; eauto.
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
      - apply in_nodes_iff. apply S.choose_1 in Echoose.
        apply subset_nodes_sub in Echoose. auto. }
    assert (Ug' : undirected g') by (unfold g'; apply remove_nodes_undirected; auto).
    assert (Hloop' : no_selfloop g') by
      (unfold g'; eapply subgraph_no_selfloop; [apply remove_nodes_subgraph | auto]).
    assert (Hvin : S.In v (subset_nodes (high_deg k) g)).
    { apply S.choose_1 in Echoose. auto. }
    assert (Hremoves : (M.cardinal g' + k + 2 <= n)%nat).
    { subst n. unfold g'. apply phase1_removes_many; auto. }
    apply munion_case in Hfi as [Hfi|Hfi].
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
  apply munion_case in Hfi as [Hfi|Hfi].
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

(* Some notes about how the algorithm will be written:

- we will not pass proofs that the graph is 3-colorable all the time,
  since later we want to talk about robustness

- we want to break down algorithm enough to reason about the graph and
  the coloring at each step while still making the overall algorithm
  clear

- an important lemma we will use repeatedly is that we can combine OK
  disjoint colorings into larger colorings, and that the number of
  colors used is the size of the palette

- to show that the coloring is complete, we show that a vertex must be
  one of the following:

1) a high-degree vertex, in which case it's colored by phase 1
2) a neighbor of a high-degree vertex, in which case it's colored by phase 1
3) a low-degree vertex, in which case it's colored by phase 2
 *)

(*
We define phase 1 of the algorithm in several pieces:

two_color_step takes:
  - a graph g
  - a high-degree vertex v
  - the current color number c
two_color_step outputs:
  - a complete coloring of N(v) using colors c+1, c+2
note:
  - phase 1 will color v with c
  - the expectation is that two_color_step will be called with another
    vertex and c+2

so phase 1 will fold over the list of high-degree vertices Lv and do:
- the state of the fold will be (c,m), where c is a number and m is the coloring
- call two_color_step on each vertex to produce the coloring and update m
- update c to c+2

we will have to show that:

- the resulting tuple will be (d,m), where d is the number of high-degree
  vertices and m is the coloring of all the neighborhoods of high-degree vertices
- d*d <= k
- the number of colors used is 2*d

random lemmas that we have to show:
- it's decidable to check whether a node is colored or not (WF.In_Dec)
- the number of high-degree vertices cannot exceed sqrt(k)
 *)

(* Lifting two color maps with any injective function *)
(** ** Lifting a 2-coloring by an injective function *)
Lemma two_color_up_inj f g (inj : S.elt -> S.elt) :
  injective inj ->
  undirected g ->
  coloring_ok two_colors g f ->
  {h | coloring_ok (fold_right S.add S.empty [inj 1;inj 2]) g h}.
Proof.
  intros Hm Ug Hf.
  exists (M.map inj f).
  intros v.
  split.
  - intros ci Hv.
    assert (M.In v f) by hauto l: on use: M.map_2.
    destruct H0 as [cj Hcj].
    unfold M.MapsTo in Hcj.
    assert (ci = inj 1 \/ ci = inj 2).
    {
      unfold coloring_ok in Hf.
      pose proof (map_o f v inj).
      assert (Some ci = option_map inj (M.find v f)) by qauto l: on.
      sauto q: on.
    }
    destruct H0; hauto use: PositiveSet.add_2, PositiveSet.add_1 unfold: PositiveSet.elt.
  - intros ci cj Hci Hcj.
    assert (M.In v f) by hauto l: on use: M.map_2.
    assert (M.In j f) by hauto l: on use: M.map_2.
    destruct H0 as [ci' Hci'].
    destruct H1 as [cj' Hcj'].
    unfold M.MapsTo in *.
    assert (Some ci = option_map inj (M.find v f)) by sauto lq: on use: map_o.
    assert (Some cj = option_map inj (M.find j f)) by sauto lq: on use: map_o.
    pose proof (proj2 (Hf v j H) ci' cj' Hci' Hcj').
    assert (ci' = 1 \/ ci' = 2).
    {
      pose proof (proj1 (Hf _ _ H) _ Hci').
      sauto.
    }
    (* Here we use the fact that the graph is undirected so we can
       go from j being adjacent to v to v being adjacent to j. *)
    assert (cj' = 1 \/ cj' = 2).
    {
      pose proof (proj1 (Hf _ _ (Ug _ _ H)) _ Hcj').
      sauto.
    }
    sauto.
Qed.

(* Lifting three color maps *)
(** ** Lifting a 3-coloring by an injective function *)
Lemma three_color_up_inj f g (inj : S.elt -> S.elt) :
  injective inj ->
  undirected g ->
  coloring_ok three_colors g f ->
  {h | coloring_ok (fold_right S.add S.empty [inj 1;inj 2;inj 3]) g h}.
Proof.
  intros Hm Ug Hf.
  exists (M.map inj f).
  intros v.
  split.
  - intros ci Hv.
    assert (M.In v f) by hauto l: on use: M.map_2.
    destruct H0 as [cj Hcj].
    unfold M.MapsTo in Hcj.
    assert (ci = inj 1 \/ ci = inj 2 \/ ci = inj 3).
    {
      unfold coloring_ok in Hf.
      pose proof (map_o f v inj).
      assert (Some ci = option_map inj (M.find v f)) by qauto l: on.
      sauto q: on.
    }
    destruct H0; hauto use: PositiveSet.add_2, PositiveSet.add_1 unfold: PositiveSet.elt.
  - intros ci cj Hci Hcj.
    assert (M.In v f) by hauto l: on use: M.map_2.
    assert (M.In j f) by hauto l: on use: M.map_2.
    destruct H0 as [ci' Hci'].
    destruct H1 as [cj' Hcj'].
    unfold M.MapsTo in *.
    assert (Some ci = option_map inj (M.find v f)) by sauto lq: on use: map_o.
    assert (Some cj = option_map inj (M.find j f)) by sauto lq: on use: map_o.
    pose proof (proj2 (Hf v j H) ci' cj' Hci' Hcj').
    assert (ci' = 1 \/ ci' = 2 \/ ci' = 3).
    {
      pose proof (proj1 (Hf _ _ H) _ Hci').
      sauto.
    }
    (* Here we use the fact that the graph is undirected so we can
       go from j being adjacent to v to v being adjacent to j. *)
    assert (cj' = 1 \/ cj' = 2 \/ cj' = 3).
    {
      pose proof (proj1 (Hf _ _ (Ug _ _ H)) _ Hcj').
      sauto.
    }
    sauto.
Qed.


(* To make "without loss of generality" type arguments, we'll need to
turn any 2-coloring into ones that involve just the colors 1,2 then
use appropriate lemmas to turn them into c, c+1.
*)

(* Idea: use reflection for coloring_ok *)

(* Remove whole neighborhood from a graph *)

(* Try to abstract the details about the criterion about how the
   high-degree vertex is chosen *)

(*
Try to 2-color a 2-colorable graph

- choose a vertex, color it 1
- color all of its neighbors 2
- when you color a vertex 2, color all of its neighbors 1
- keep going

 *)

(*
Induction principle for graphs?

*)
