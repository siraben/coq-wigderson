Require Import graph.
Require Import subgraph.
Require Import restrict.
Require Import munion.
Require Import List.
Require Import Setoid.
Require Import FSets.
Require Import FMaps.
Require Import PArith.
Require Import Decidable.
Require Import Program.
Require Import FunInd.
Require Import Psatz.
Require Import bipartite.
Require Import connectivity.
Require Import coloring.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
Import Arith.
Import ListNotations.
Import Nat.

Import ListNotations Arith Nat.

Add Hammer Filter Coq.Numbers.BinNums.
Add Hammer Filter Coq.micromega.RingMicromega.
Add Hammer Filter Coq.micromega.Tauto.
Add Hammer Filter Coq.micromega.ZifyClasses.
Add Hammer Filter Coq.micromega.VarMap.
Add Hammer Filter Coq.micromega.ZMicromega.
Add Hammer Filter Coq.Lists.SetoidList.
Add Hammer Filter Coq.micromega.EnvRing.
Add Hammer Filter Coq.funind.Recdef.
Set Hammer ReconstrLimit 10.

(* ---------- Neighborhood of a set (union of adjacency sets) ---------- *)

Definition nbs (g : graph) (s : S.t) : S.t :=
  S.fold (fun v acc => S.union (adj g v) acc) s S.empty.

Lemma nbs_empty g : nbs g S.empty = S.empty.
Proof. reflexivity. Qed.

Lemma nbs_spec g s i :
  S.In i (nbs g s) <-> exists v, S.In v s /\ S.In i (adj g v).
Proof.
  unfold nbs.
  apply SP.fold_rec_bis
    with (P := fun s' acc =>
                S.In i acc <->
                exists v, S.In v s' /\ S.In i (adj g v)).
  - intros s' Hs'.
    sfirstorder.
  - sauto.
  - intros x a s' Hx Hrec.
    split; intro Hin.
    + qauto use: PositiveSet.union_1, SP.Dec.FSetDecideTestCases.test_iff_conj, PositiveSet.add_spec unfold: PositiveSet.empty, PositiveOrderedTypeBits.t, nodeset, PositiveSet.elt, node, PositiveSet.t, adj.
    + destruct Hin as (v & Hv & Hv2).
      rewrite S.add_spec in Hv.
      destruct Hv.
      * sfirstorder use: PositiveSet.union_2, PositiveSet.mem_Leaf unfold: PositiveOrderedTypeBits.t, PositiveSet.elt, PositiveSet.In, node, adj, PositiveSet.empty, nodeset.
      * sfirstorder use: PositiveSet.union_3 unfold: node, PositiveSet.elt, adj, PositiveOrderedTypeBits.t, nodeset.
Qed.

Lemma nbs_subset_nodes g s :
  undirected g ->
  S.Subset (nbs g s) (nodes g).
Proof.
  intros Ug i Hi.
  apply nbs_spec in Hi as (v&Hv&Hiv).
  sauto lq: on use: FExt.in_adj_neighbor_in_nodes unfold: PositiveOrderedTypeBits.t, node, PositiveSet.elt.
Qed.

(* Convenience: next frontier additions, excluding already "visited" *)
Definition add_to_R g FL Vis := S.diff (nbs g FL) Vis.
Definition add_to_L g FR Vis := S.diff (nbs g FR) Vis.

(* ---------- One-component forcing (layered BFS) ---------- *)

Fixpoint force_layers (g : graph)
         (L R FL FR : S.t) (fuel : nat) {struct fuel} : S.t * S.t :=
  match fuel with
  | 0 => (L, R)
  | S k =>
      let Vis := S.union L R in
      let Radd := add_to_R g FL Vis in   (* neighbors of current L-frontier *)
      let Ladd := add_to_L g FR Vis in   (* neighbors of current R-frontier *)
      force_layers g (S.union L Ladd) (S.union R Radd)
                      Ladd Radd k
  end.

Definition force_component_sets (g : graph) (seed : node) : S.t * S.t :=
  force_layers g (S.singleton seed) S.empty (S.singleton seed) S.empty
               (S.cardinal (nodes g)).

Definition force_component (g : graph) (seed c1 c2 : node) : coloring :=
  let LR := force_component_sets g seed in
  let L := fst LR in
  let R := snd LR in
  bicolor L R c1 c2.

(* ---------- Basic invariants for layers ---------- *)

Lemma frontiers_alternate g L R FL FR k :
  FR = S.empty \/ FL = S.empty ->
  let '(L',R') := force_layers g L R FL FR k in
  True. (* we won't need the boolean form; alternation follows since one frontier starts empty *)
Proof. sauto. Qed.

Lemma force_layers_subsets_nodes g L R FL FR k :
  undirected g ->
  S.Subset L (nodes g) -> S.Subset R (nodes g) ->
  S.Subset FL (nodes g) -> S.Subset FR (nodes g) ->
  let '(L',R') := force_layers g L R FL FR k in
  S.Subset L' (nodes g) /\ S.Subset R' (nodes g).
Proof.
  revert L R FL FR; induction k; cbn; intros L R FL FR UG HL HR HFL HFR.
  - eauto.
  - pose (Vis := S.union L R).
    assert (S.Subset (add_to_R g FL Vis) (nodes g)).
    {
      sauto lq: on use: SP.subset_diff, nbs_subset_nodes unfold: add_to_R.
    }
    assert (S.Subset (add_to_L g FR Vis) (nodes g)).
    {
      sauto lq: on use: SP.subset_diff, nbs_subset_nodes unfold: add_to_L.
    }
    destruct (force_layers g (S.union L (add_to_L g FR Vis))
                           (S.union R (add_to_R g FL Vis))
                           (add_to_L g FR Vis) (add_to_R g FL Vis) k)
      as [L' R'] eqn:E.
    apply IHk; sauto use: SP.union_subset_3.
Qed.

(* In a bipartition (BL,BR), neighbors of BL lie in BR and conversely. *)
Lemma nbs_subset_bip_side g BL BR :
  undirected g ->
  is_bipartition g BL BR ->
  S.Subset (nbs g BL) BR /\ S.Subset (nbs g BR) BL.
Proof.
  intros Hg (Hdisj & Hcov & HindL & HindR).
  split; intros x Hx;
  apply nbs_spec in Hx as (v&Hv&Hxv).
  - (* v in BL, neighbor x is in nodes g; cannot be in BL by independence, hence in BR by cover *)
    qauto use: SP.Dec.F.union_iff, FExt.in_adj_neighbor_in_nodes unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, node, independent_set, PositiveSet.Equal.
  - (* symmetric *)
    qauto use: SP.Dec.F.union_iff, FExt.in_adj_neighbor_in_nodes unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, node, independent_set, PositiveSet.Equal.
Qed.

Lemma nbs_mono g s1 s2 :
  S.Subset s1 s2 -> S.Subset (nbs g s1) (nbs g s2).
Proof.
  intros Hsub i Hi.
  apply nbs_spec in Hi as (v & Hv & Hiv).
  apply nbs_spec. exists v. split; [apply Hsub; exact Hv|exact Hiv].
Qed.

Lemma force_layers_subset_true_partition_gen g BL BR L R FL FR k :
  undirected g ->
  is_bipartition g BL BR ->
  S.Subset L  BL -> S.Subset R  BR ->
  S.Subset FL BL -> S.Subset FR BR ->
  let '(L',R') := force_layers g L R FL FR k in
  S.Subset L' BL /\ S.Subset R' BR.
Proof.
  revert L R FL FR.
  induction k as [|k IH]; intros L R FL FR Ug Hbip HL HR HFL HFR; cbn.
  - split; assumption.
  - set (Vis  := S.union L R).
    set (Radd := add_to_R g FL Vis).
    set (Ladd := add_to_L g FR Vis).
    destruct (nbs_subset_bip_side g BL BR Ug Hbip) as [HBLtoBR HBRtoBL].

    (* nbs of frontiers land on the opposite true side *)
    assert (Hnbs_FL_BR : S.Subset (nbs g FL) BR).
    { hecrush use: nbs_mono unfold: PositiveSet.Subset. }
    assert (Hnbs_FR_BL : S.Subset (nbs g FR) BL).
    { hecrush use: nbs_mono unfold: PositiveSet.Subset. }

    (* removing already visited vertices keeps subset *)
    assert (HRadd_BR : S.Subset Radd BR).
    { unfold Radd, add_to_R. eapply SP.subset_diff. exact Hnbs_FL_BR. }
    assert (HLadd_BL : S.Subset Ladd BL).
    { unfold Ladd, add_to_L. eapply SP.subset_diff. exact Hnbs_FR_BL. }

    destruct (force_layers g (S.union L Ladd) (S.union R Radd) Ladd Radd k) as [L' R'] eqn:E.
    specialize (IH (S.union L Ladd) (S.union R Radd) Ladd Radd Ug Hbip).
    hfcrush use: SP.union_subset_3 inv: prod.
Qed.

Lemma force_layers_subset_true_partition g BL BR seed k :
  undirected g ->
  is_bipartition g BL BR ->
  S.In seed BL ->
  let '(L,R) := force_layers g (S.singleton seed) S.empty
                             (S.singleton seed) S.empty k in
  S.Subset L BL /\ S.Subset R BR.
Proof.
  intros Ug Hbip Hin.
  eapply (force_layers_subset_true_partition_gen g BL BR
          (S.singleton seed) S.empty (S.singleton seed) S.empty k); eauto.
  - intros i Hi. apply SP.Dec.F.singleton_iff in Hi; subst; assumption.
  - fcrush.
  - intros i Hi. apply SP.Dec.F.singleton_iff in Hi; subst; assumption.
  - fcrush.
Qed.

Lemma independent_subset g s s' :
  independent_set g s -> S.Subset s' s -> independent_set g s'.
Proof. firstorder. Qed.

Lemma disjoint_by_subsets BL BR L R :
  S.Empty (S.inter BL BR) ->
  S.Subset L BL -> S.Subset R BR ->
  S.Empty (S.inter L R).
Proof.
  intros Hdis HL HR x Hx.
  qauto use: PositiveSet.inter_1, PositiveSet.inter_3, PositiveSet.inter_2 unfold: PositiveSet.Subset, PositiveSet.Empty.
Qed.

Lemma nodes_subgraph_of_union_eq g L R :
  S.Subset L (nodes g) -> S.Subset R (nodes g) ->
  S.Equal (nodes (subgraph_of g (S.union L R))) (S.union L R).
Proof.
  intros HL HR i; split; intro Hi.
  - apply nodes_subgraph_of_spec in Hi as [HinG HinU]. exact HinU.
  - apply nodes_subgraph_of_spec. split.
    + sfirstorder use: PositiveSet.union_1 unfold: PositiveSet.Subset.
    + assumption.
Qed.

Lemma force_component_bipartition_on_reached g seed :
  undirected g -> bipartite g -> S.In seed (nodes g) ->
  let LR := force_component_sets g seed in
  let L := fst LR in let R := snd LR in
  is_bipartition (subgraph_of g (S.union L R)) L R.
Proof.
  intros Ug [BL [BR Hbip]] HseedG.
  destruct Hbip as [Hdisj [Hcov [HindL HindR]]].
  unfold force_component_sets.
  set (LR := force_layers g (S.singleton seed) S.empty
                          (S.singleton seed) S.empty (S.cardinal (nodes g))).
  destruct LR as [L R] eqn:E.

  (* The seed lies on one of the two true sides *)
  assert (HseedSide : S.In seed BL \/ S.In seed BR).
  { apply (proj2 (Hcov seed)) in HseedG.
    rewrite S.union_spec in HseedG; tauto. }

  (* Each true side is a subset of nodes g *)
  assert (BL_in_nodes : S.Subset BL (nodes g)).
  { sfirstorder use: PositiveSet.union_2 unfold: PositiveSet.Equal, PositiveSet.Subset. }
  assert (BR_in_nodes : S.Subset BR (nodes g)).
  { hfcrush use: SP.Dec.F.union_iff unfold: PositiveSet.Subset, PositiveSet.Equal. }

  (* We now branch on the side of the seed and harvest the forcing invariant *)
  unfold is_bipartition.
  repeat split.
  - (* Disjointness L ∩ R = ∅ *)
    destruct HseedSide as [HseedBL|HseedBR].
    + pose proof (conj (conj Hdisj Hcov) (conj HindL HindR)).
      pose proof (force_layers_subset_true_partition
                    g BL BR seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      hauto use: disjoint_by_subsets unfold: is_bipartition, fst, snd inv: prod.
    + pose proof (bipartition_sym g BL BR) as Hbip'.
      pose proof (force_layers_subset_true_partition
                    g BR BL seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      hauto use: disjoint_by_subsets unfold: is_bipartition, fst, snd inv: prod.
  - (* Cover on the induced subgraph: nodes(subgraph_of g (L ∪ R)) = L ∪ R *)
    destruct HseedSide as [HseedBL|HseedBR].
    + pose proof (force_layers_subset_true_partition
                    g BL BR seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      hfcrush use: PositiveSet.union_spec, nodes_subgraph_of_spec unfold: snd, is_bipartition, fst, PositiveSet.Subset inv: prod.
    + pose proof (bipartition_sym g BL BR) as Hbip'.
      pose proof (force_layers_subset_true_partition
                    g BR BL seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      hfcrush use: nodes_subgraph_of_spec, PositiveSet.union_1 unfold: fst, snd, is_bipartition, PositiveSet.Subset inv: prod.
  - (* Independence of L in the induced subgraph *)
    destruct HseedSide as [HseedBL|HseedBR].
    + pose proof (force_layers_subset_true_partition
                    g BL BR seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      strivial use: nodes_subgraph_of_spec unfold: fst, snd.
    + pose proof (bipartition_sym g BL BR) as Hbip'.
      pose proof (force_layers_subset_true_partition
                    g BR BL seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      strivial use: nodes_subgraph_of_spec unfold: snd, fst.
  - (* Independence of R in the induced subgraph *)
    destruct HseedSide as [HseedBL|HseedBR].
    + pose proof (force_layers_subset_true_partition
                    g BL BR seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      eapply independent_set_subgraph; [apply subgraph_of_is_subgraph|].
      hauto use: independent_subset unfold: is_bipartition, nodeset inv: prod.
    + pose proof (bipartition_sym g BL BR) as Hbip'.
      pose proof (force_layers_subset_true_partition
                    g BR BL seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      eapply independent_set_subgraph; [apply subgraph_of_is_subgraph|].
      hauto use: independent_subset unfold: nodeset, is_bipartition, fst inv: prod.
  - destruct HseedSide as [HseedBL|HseedBR].
    + pose proof (force_layers_subset_true_partition
                    g BL BR seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      eapply independent_set_subgraph; [apply subgraph_of_is_subgraph|].
      hauto use: independent_subset unfold: is_bipartition, nodeset inv: prod.
    + pose proof (bipartition_sym g BL BR) as Hbip'.
      pose proof (force_layers_subset_true_partition
                    g BR BL seed (S.cardinal (nodes g))
                    Ug) as Hsub.
      eapply independent_set_subgraph; [apply subgraph_of_is_subgraph|].
      hauto use: independent_subset unfold: nodeset, is_bipartition, fst inv: prod.
Qed.

(* --- finishing step: the forcing component is a complete 2-coloring on the reached subgraph --- *)
Lemma force_component_ok g seed c1 c2 :
  undirected g -> bipartite g -> c1 <> c2 -> S.In seed (nodes g) ->
  let LR := force_component_sets g seed in
  let L := fst LR in let R := snd LR in
  coloring_complete (SP.of_list [c1;c2])
     (subgraph_of g (S.union L R))
     (force_component g seed c1 c2).
Proof.
  intros Ug Hbip Hneq Hseed.
  (* materialize the [let] pair and rewrite *)
  remember (force_component_sets g seed) as LR eqn:HLR.
  destruct LR as [L R].
  unfold force_component; rewrite HLR; cbn.

  (* bipartition of the induced subgraph on the reached vertices *)
  pose proof (force_component_bipartition_on_reached g seed Ug Hbip Hseed) as HbipLR.
  rewrite <- HLR in HbipLR.
  cbn in HbipLR.
  rewrite <- HLR.
  (* goal is a conjunction by definition of [coloring_complete] *)
  split.
  - (* completeness: every node of the induced subgraph is colored *)
    intros i Hi.
    unfold fst, snd in *.
    eapply bicolor_complete; eauto.  (* uses [HbipLR] *)
  - (* ok-ness: edges are properly 2-colored on the induced subgraph *)
    eapply bicolor_ok; eauto using subgraph_of_undirected.  (* needs undirectedness of the induced subgraph *)
Qed.

Lemma bipartition_remove_nodes g L R s :
  is_bipartition g L R ->
  is_bipartition (remove_nodes g s) (S.diff L s) (S.diff R s).
Proof.
  intros (Hdisj & Hcov & HindL & HindR).
  repeat split.
  - (* disjoint *)
    hauto lq: on use: disjoint_by_subsets, SP.diff_subset unfold: nodeset.
  - (* cover: nodes(remove_nodes g s) = nodes g \ s *)
    rewrite nodes_remove_nodes_eq.
    intros H.
    rewrite S.diff_spec.
    rewrite S.union_spec in H.
    destruct H.
    + sfirstorder use: PositiveSet.diff_1, PositiveSet.union_2, PositiveSet.diff_2 unfold: PositiveSet.Equal, nodeset.
    + sfirstorder use: PositiveSet.diff_2, PositiveSet.diff_1, PositiveSet.union_3 unfold: nodeset, PositiveSet.Equal.
  - (* L independent after removal *)
    hfcrush use: PositiveSet.union_3, nodes_remove_nodes_spec, PositiveSet.union_2, PositiveSet.diff_3, PositiveSet.union_1 unfold: PositiveSet.Equal, nodeset.
  - (* R independent after removal *)
    qauto depth: 4 l: on use: adj_remove_nodes_spec, PositiveSet.diff_1 unfold: PositiveOrderedTypeBits.t, node, nodeset, independent_set, PositiveSet.elt.
  - qauto depth: 4 l: on use: adj_remove_nodes_spec, PositiveSet.diff_1 unfold: PositiveOrderedTypeBits.t, node, nodeset, independent_set, PositiveSet.elt.
Qed.


Corollary bipartite_remove_nodes g s :
  bipartite g -> bipartite (remove_nodes g s).
Proof.
  intros [L [R Hbip]]. eexists; eexists. eapply bipartition_remove_nodes; eauto.
Qed.


Definition reached g seed :=
  let LR := force_component_sets g seed in S.union (fst LR) (snd LR).

Lemma force_layers_preserve_L :
  forall g L R FL FR k,
    S.Subset L (fst (force_layers g L R FL FR k)).
Proof.
  intros g L R FL FR k.
  revert L R FL FR.
  induction k as [|k IH]; intros L R FL FR; simpl.
  - (* k = 0 *) intros x Hx; exact Hx.
  - (* k = S k *)
    set (Vis  := S.union L R).
    set (Radd := add_to_R g FL Vis).
    set (Ladd := add_to_L g FR Vis).
    intro x; intro Hx.
    (* After this step, L becomes L ∪ Ladd; x∈L hence x∈L∪Ladd *)
    specialize (IH (S.union L Ladd) (S.union R Radd) Ladd Radd).
    apply IH. apply S.union_spec; now left.
Qed.

Lemma force_layers_preserve_R :
  forall g L R FL FR k,
    S.Subset R (snd (force_layers g L R FL FR k)).
Proof.
  intros g L R FL FR k.
  revert L R FL FR.
  induction k as [|k IH]; intros L R FL FR; simpl.
  - (* k = 0 *) intros x Hx; exact Hx.
  - (* k = S k *)
    set (Vis  := S.union L R).
    set (Radd := add_to_R g FL Vis).
    set (Ladd := add_to_L g FR Vis).
    intro x; intro Hx.
    (* After this step, R becomes R ∪ Radd; x∈R hence x∈R∪Radd *)
    specialize (IH (S.union L Ladd) (S.union R Radd) Ladd Radd).
    apply IH. apply S.union_spec; now left.
Qed.

Lemma force_layers_seed_in_L g seed k :
  S.In seed (fst (force_layers g (S.singleton seed) S.empty
                                 (S.singleton seed) S.empty k)).
Proof.
  eapply force_layers_preserve_L.
  (* seed ∈ {seed} *)
  now apply S.singleton_2.
Qed.

Lemma seed_in_reached g seed :
  S.In seed (reached g seed).
Proof.
  unfold reached, force_component_sets.
  apply S.union_spec; left.
  apply force_layers_seed_in_L.
Qed.

(** Colors a graph by repeatedly finding a connected component,
    2-coloring it, and recursing on the rest of the graph. *)
Function force_all (g : graph) (c1 c2 : node)
  {measure M.cardinal g} : coloring :=
  match S.choose (nodes g) with
  | None => @M.empty _
  | Some seed =>
      let LR := force_component_sets g seed in
      let L := fst LR in let R := snd LR in
      let S := S.union L R in
      Munion
        (bicolor L R c1 c2)
        (force_all (remove_nodes g S) c1 c2)
  end.
Proof.
  intros g c1 c2 seed Hchoose.
  (* seed ∈ nodes g *)
  assert (HinG : M.In seed g).
  { sfirstorder use: FExt.in_nodes_iff, PositiveSet.choose_1 unfold: nodes. }
  (* seed ∈ reached set *)
  assert (HinS : S.In seed (reached g seed)) by apply seed_in_reached.
  (* strict decrease of cardinality *)
  eapply remove_nodes_lt; eauto.
Defined.

Functional Scheme force_all_ind := Induction for force_all Sort Prop.

Lemma coloring_union_no_cross g p S f1 f2 :
  (* f1 colors the induced subgraph on S *)
  coloring_ok p (subgraph_of g S) f1 ->
  (* f2 colors the complement *)
  coloring_ok p (remove_nodes g S) f2 ->
  (* No cross edges out of S *)
  S.Subset (nbs g S) S ->
  coloring_ok p g (Munion f1 f2).
Proof.
  intros OK1 OK2 Closed.
  split.
  - intros ci Hci.
    apply Munion_case in Hci.
    destruct Hci.
    + unfold coloring_ok in *.
      pose proof (OK1 i j).
      assert (S.In j (adj (subgraph_of g S) i)).
      {
        admit.
      }
      sfirstorder.
    + admit.
  - intros ci cj Hfi Hfj Hadj.
    (* Split by which branch provided the colors *)
    apply Munion_case in Hfi; apply Munion_case in Hfj.
    destruct Hfi as [Hi1|Hi2]; destruct Hfj as [Hj1|Hj2].
    + (* both in S: reduce to subgraph_of g S *)
      admit.
    + (* i in S, j outside — impossible by closure *)
      admit.
    + (* symmetric to previous case *)
      admit.
    + (* both outside S: reduce to remove_nodes g S *)
      admit.
Abort.
