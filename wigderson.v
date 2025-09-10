Require Import graph.
Require Import subgraph.
Require Import coloring.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
Require Import FunInd.
Require Import restrict.
Require Import munion.
Require Import Psatz.
Require Import FExt.
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
    now apply Sin_domain in H2.
  }
  rewrite cardinal_map.
  now apply Mremove_cardinal_less.
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
  apply Sin_domain in H.
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

(* Two-coloring of a neighborhood *)
Definition two_color_nbd (g : graph) (v : node) (c1 c2 : positive) : option coloring.
Admitted.

(* Two coloring of a neighborhood of a 3-colorable graph is complete *)

Program Fixpoint phase1
  (* The criterion for high-degree vertices *)
  (k : nat)
  (* Current color count *)
  (c : positive)
  (g : graph) {measure (M.cardinal g)} : option (coloring * graph) :=
  (* Choose a high-degree vertex *)
  match S.choose (subset_nodes (high_deg k) g) with
  | Some v =>
      let nbhd := neighborhood g v in
      let coloring_of_nbhd := two_color_nbd g v (c+1) (c+2) in
      let g' := remove_nodes g (S.add v (nodes nbhd)) in
      (* color the high-degree vertex with c each time *)
      match coloring_of_nbhd with
      | None => None
      | Some m' => option_map (fun (p : coloring * graph) => let (c2,g2) := p in (Munion (M.add v c m') c2, g2)) (phase1 k (c+2) g')
      end
  | None => Some (@M.empty _, g)
  end.
Next Obligation.
  (* decrease: |g'| < |g| *)
  simpl.
  set (s := S.add v (nodes (neighborhood g v))).
  (* v ∈ s *)
  assert (Sv : S.In v s) by (unfold s; apply S.add_spec; left; reflexivity).
  (* v ∈ nodes g, because choose picked v from subset_nodes ... *)
  assert (Vin : M.In v g).
  { apply in_nodes_iff.
    (* v ∈ subset_nodes (..) ⊆ nodes g *)
    symmetry in Heq_anonymous.
    pose proof (S.choose_1 _ Heq_anonymous).
    apply subset_nodes_sub in H.
    assumption.
  }

  (* Now just use the canned strict-decrease lemma for remove_nodes *)
  rewrite !Mcardinal_domain.
  rewrite nodes_remove_nodes_eq.
  eapply SP.subset_cardinal_lt with (x := v).
  - apply SP.diff_subset.
  - now rewrite in_nodes_iff.
  - unfold s.
    hauto l: on use: S.diff_spec, S.add_spec.
Qed.

Functional Scheme phase1_ind := Induction for phase1 Sort Prop.

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
    sfirstorder use: FExt.in_nodes_iff.
  }
  enough (S.cardinal (nodes g') < S.cardinal (nodes g))%nat.
  {
    scongruence use: Mcardinal_domain unfold: snd, extract_vertices_degs, PositiveMap.t, nodes, fst inv: R_extract_vertices_degs.
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

(** ** InA to In conversion *)
Lemma InA_iff {A} : forall p (l : list A), (InA Logic.eq p l) <-> In p l.
Proof. induction l; sauto q: on. Qed.

(** ** Specification of siota construction *)
Lemma siota_spec : forall (n : nat), (forall i, (0 <= i <= n + 1)%nat <-> S.In (Pos.of_nat i) (siota n)).
Proof.
  intros n i.
  split; intros H.
  - unfold siota.
    apply SP.of_list_1.
    apply InA_iff.
    apply in_map_iff.
    destruct i; [exists 1%nat|exists (S i)%nat]; hauto l: on use: in_seq.
  - destruct i eqn:He; [sfirstorder|].
    apply SP.of_list_1 in H.
    rewrite InA_iff in H.
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
    apply Munion_case in H5.
    destruct H5.
    + left.
      apply constant_color_inv2 in H4.
      assumption.
    + right.
      sfirstorder.
  - intros ci cj H5 H6.
    apply Munion_case in H5, H6.
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
    apply Munion_case in H0.
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
    sauto lq: on rew: off use: constant_color_inv, Sin_domain.
  - (* step: max_deg g = S n *)
    intros f Hf.
    inversion Hf; subst; clear Hf.
    intros x Hx.
    (* membership in domain of Munion => membership in one branch *)
    rewrite Sin_domain in Hx.
    apply Munion_in in Hx as [Hx|Hx].
    + (* x came from the fresh constant coloring on ns *)
      apply Sin_domain.
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
      hauto lq: on use: FExt.in_nodes_iff, Sin_domain, subgraph_vert_m, extract_vertices_degs_subgraph unfold: PositiveSet.Subset, coloring, PositiveMap.key, PositiveSet.elt.
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
    apply Munion_case in Hfi0; apply Munion_case in Hfj0.
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
        hecrush use: Sin_domain.
      }
      assert (Dj : M.In j g').
      { apply phase2_domain_subset with (g' := g''') in e1.
        clear -e1 Hj_later.
        hecrush use: Sin_domain.
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
          qauto use: Sin_domain, WF.in_find_iff unfold: coloring, node, PositiveSet.elt, PositiveOrderedTypeBits.t, PositiveMap.key.
        }
        assert (Hj_dom : S.In j (Mdomain f')).
        {
          qauto use: WF.in_find_iff, Sin_domain unfold: coloring, PositiveMap.key, PositiveSet.elt.
        }
        pose proof (DomSub _ Hi_dom) as Hi_nodes'.
        pose proof (DomSub _ Hj_dom) as Hj_nodes'.
        assert (Hadj' : S.In j (adj g' i)).
        {
          assert (M.In i g') by hauto l: on use: Sin_domain.
          assert (M.In j g') by hauto l: on use: Sin_domain.
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
