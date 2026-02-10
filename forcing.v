(** * forcing.v - BFS-based forced coloring of bipartite graphs *)
Require Import graph.
Require Import subgraph.
Require Import restrict.
Require Import munion.
Require Import List.
Require Import Setoid.
Require Import FSets.
Require Import FMaps.
Require Import PArith.
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

(* Hammer filters shared across coloring/subgraph/connectivity/forcing *)
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
  sauto lq: on use: in_adj_neighbor_in_nodes unfold: PositiveOrderedTypeBits.t, node, PositiveSet.elt.
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
    qauto use: SP.Dec.F.union_iff, in_adj_neighbor_in_nodes unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, node, independent_set, PositiveSet.Equal.
  - (* symmetric *)
    qauto use: SP.Dec.F.union_iff, in_adj_neighbor_in_nodes unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, node, independent_set, PositiveSet.Equal.
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
  { sfirstorder use: in_nodes_iff, PositiveSet.choose_1 unfold: nodes. }
  (* seed ∈ reached set *)
  assert (HinS : S.In seed (reached g seed)) by apply seed_in_reached.
  (* strict decrease of cardinality *)
  eapply remove_nodes_lt; eauto.
Defined.

Functional Scheme force_all_ind := Induction for force_all Sort Prop.

Lemma coloring_union_no_cross g p S f1 f2 :
  undirected g ->
  (* f1 colors the induced subgraph on S *)
  coloring_ok p (subgraph_of g S) f1 ->
  (* f2 colors the complement *)
  coloring_ok p (remove_nodes g S) f2 ->
  (* No cross edges out of S *)
  S.Subset (nbs g S) S ->
  (* f1's domain is exactly S *)
  S.Equal (Mdomain f1) S ->
  coloring_ok p g (Munion f1 f2).
Proof.
  intros Ug OK1 OK2 Closed Hdom i j Hadj.
  (* Determine whether i is in S *)
  destruct (SP.In_dec i S) as [HiS|HiS].
  - (* i ∈ S: neighbor j ∈ S by closure *)
    assert (HjS : S.In j S).
    { apply Closed. apply nbs_spec. exists i. split; assumption. }
    (* i has a color in f1 *)
    assert (HiIn : M.In i f1).
    { rewrite <- in_domain. rewrite Hdom. exact HiS. }
    destruct HiIn as [ci Hci]. unfold M.MapsTo in Hci.
    (* Use munion_find_l to pin colors to f1 *)
    split.
    + intros ci' Hci'.
      rewrite (munion_find_l _ _ _ _ Hci) in Hci'. injection Hci' as <-.
      assert (Hadj' : S.In j (adj (subgraph_of g S) i)).
      { apply adj_subgraph_of_spec. auto. }
      destruct (OK1 i j Hadj') as [Hpal _].
      exact (Hpal ci Hci).
    + intros ci' cj' Hci' Hcj' Heq.
      rewrite (munion_find_l _ _ _ _ Hci) in Hci'. injection Hci' as <-.
      assert (HjIn : M.In j f1).
      { rewrite <- in_domain. rewrite Hdom. exact HjS. }
      destruct HjIn as [cj Hcj]. unfold M.MapsTo in Hcj.
      rewrite (munion_find_l _ _ _ _ Hcj) in Hcj'. injection Hcj' as <-.
      assert (Hadj' : S.In j (adj (subgraph_of g S) i)).
      { apply adj_subgraph_of_spec. auto. }
      destruct (OK1 i j Hadj') as [_ Hneq].
      exact (Hneq ci cj Hci Hcj Heq).
  - (* i ∉ S *)
    (* j ∉ S: if j ∈ S then i ∈ nbs g S ⊆ S, contradiction *)
    assert (HjS : ~ S.In j S).
    { intro HjS. apply HiS. apply Closed.
      apply nbs_spec. exists j. split; [exact HjS|apply Ug; exact Hadj]. }
    (* i has no color in f1, so Munion gives f2's color *)
    assert (Hfi1 : M.find i f1 = None).
    { destruct (M.find i f1) as [vi|] eqn:E; [|reflexivity].
      exfalso. apply HiS. rewrite <- Hdom. apply in_domain.
      exists vi. exact E. }
    split.
    + intros ci Hci.
      apply munion_case in Hci as [Hci|Hci].
      * congruence.
      * assert (Hadj' : S.In j (adj (remove_nodes g S) i)).
        { apply adj_remove_nodes_spec. auto. }
        destruct (OK2 i j Hadj') as [Hpal _].
        exact (Hpal ci Hci).
    + intros ci cj Hci Hcj Heq.
      apply munion_case in Hci as [Hci|Hci]; [congruence|].
      assert (Hfj1 : M.find j f1 = None).
      { destruct (M.find j f1) as [vj|] eqn:E; [|reflexivity].
        exfalso. apply HjS. rewrite <- Hdom. apply in_domain.
        exists vj. exact E. }
      apply munion_case in Hcj as [Hcj|Hcj]; [congruence|].
      assert (Hadj' : S.In j (adj (remove_nodes g S) i)).
      { apply adj_remove_nodes_spec. auto. }
      destruct (OK2 i j Hadj') as [_ Hneq].
      exact (Hneq ci cj Hci Hcj Heq).
Qed.

(* ---------- Helper lemmas for BFS closure ---------- *)

Lemma nbs_union g A B :
  S.Subset (nbs g (S.union A B)) (S.union (nbs g A) (nbs g B)).
Proof.
  intros i Hi.
  apply nbs_spec in Hi as (v & Hv & Hiv).
  apply S.union_spec in Hv as [Hv|Hv];
  apply S.union_spec; [left|right]; apply nbs_spec; eauto.
Qed.

Lemma nbs_union_eq g A B :
  S.Equal (nbs g (S.union A B)) (S.union (nbs g A) (nbs g B)).
Proof.
  intro i; split; intro Hi.
  - now apply nbs_union.
  - apply S.union_spec in Hi as [Hi|Hi];
    apply nbs_spec in Hi as (v & Hv & Hiv);
    apply nbs_spec; exists v; split; auto;
    apply S.union_spec; [left|right]; auto.
Qed.

Lemma union_empty_r (s : S.t) : S.union s S.empty = s.
Proof. destruct s; reflexivity. Qed.

Lemma diff_empty_l (s : S.t) : S.diff S.empty s = S.empty.
Proof. reflexivity. Qed.

Lemma force_layers_empty_frontiers g L R k :
  force_layers g L R S.empty S.empty k = (L, R).
Proof.
  induction k; simpl; auto.
  unfold add_to_R, add_to_L.
  rewrite nbs_empty, !diff_empty_l, !union_empty_r.
  exact IHk.
Qed.

Lemma nbs_empty_set g s : S.Empty s -> S.Empty (nbs g s).
Proof.
  intros Hs x Hx. apply nbs_spec in Hx as (v & Hv & _). exact (Hs _ Hv).
Qed.

Lemma diff_empty_set s t : S.Empty s -> S.Empty (S.diff s t).
Proof.
  intros Hs x Hx. apply S.diff_spec in Hx as [Hx _]. exact (Hs _ Hx).
Qed.

Lemma union_empty_equal_l s t : S.Empty t -> S.Equal (S.union s t) s.
Proof.
  intros Ht x. rewrite S.union_spec. split.
  - intros [H|H]; auto. exfalso; exact (Ht _ H).
  - left; auto.
Qed.

Lemma force_layers_noop g L R FL FR k :
  S.Empty FL -> S.Empty FR ->
  let '(L', R') := force_layers g L R FL FR k in
  S.Equal L' L /\ S.Equal R' R.
Proof.
  revert L R FL FR.
  induction k as [|k IH]; intros L R FL FR HFL HFR; simpl.
  - split; reflexivity.
  - set (Vis := S.union L R).
    assert (HnFL : S.Empty (nbs g FL)) by (apply nbs_empty_set; auto).
    assert (HRadd : S.Empty (add_to_R g FL Vis)) by (apply diff_empty_set; auto).
    assert (HLadd : S.Empty (add_to_L g FR Vis)).
    { apply diff_empty_set. apply nbs_empty_set; auto. }
    specialize (IH (S.union L (add_to_L g FR Vis))
                   (S.union R (add_to_R g FL Vis))
                   (add_to_L g FR Vis) (add_to_R g FL Vis) HLadd HRadd).
    destruct (force_layers _ _ _ _ _ k) as [L' R'].
    destruct IH as [IHL IHR].
    split; intro x.
    + rewrite IHL, (union_empty_equal_l L _ HLadd). reflexivity.
    + rewrite IHR, (union_empty_equal_l R _ HRadd). reflexivity.
Qed.

(* Helper: nbs of a set split into frontier + rest *)
Lemma nbs_split_frontier g L FL :
  S.Subset FL L ->
  S.Subset (nbs g L) (S.union (nbs g FL) (nbs g (S.diff L FL))).
Proof.
  intros HFL i Hi. apply nbs_spec in Hi as (v & Hv & Hiv).
  destruct (SP.In_dec v FL).
  - apply S.union_spec; left. apply nbs_spec; eauto.
  - apply S.union_spec; right. apply nbs_spec. exists v. split; auto.
    apply S.diff_spec; auto.
Qed.

Lemma nbs_FL_subset_vis_radd g FL Vis :
  S.Subset (nbs g FL) (S.union Vis (add_to_R g FL Vis)).
Proof.
  intros x Hx.
  destruct (SP.In_dec x Vis).
  - apply S.union_spec; left; auto.
  - apply S.union_spec; right. unfold add_to_R. apply S.diff_spec; auto.
Qed.

Lemma nbs_FR_subset_vis_ladd g FR Vis :
  S.Subset (nbs g FR) (S.union Vis (add_to_L g FR Vis)).
Proof.
  intros x Hx.
  destruct (SP.In_dec x Vis).
  - apply S.union_spec; left; auto.
  - apply S.union_spec; right. unfold add_to_L. apply S.diff_spec; auto.
Qed.

Lemma force_layers_closure g L R FL FR k :
  undirected g ->
  S.Subset FL L -> S.Subset FR R ->
  S.Subset L (nodes g) -> S.Subset R (nodes g) ->
  S.Subset (nbs g (S.diff L FL)) (S.union L R) ->
  S.Subset (nbs g (S.diff R FR)) (S.union L R) ->
  (S.cardinal (S.diff (nodes g) (S.union L R)) <= k)%nat ->
  let '(L', R') := force_layers g L R FL FR k in
  S.Subset (nbs g (S.union L' R')) (S.union L' R').
Proof.
  revert L R FL FR.
  induction k as [|k IH]; intros L R FL FR Ug HFL HFR HL HR HdL HdR Hcard; simpl.
  - (* k = 0: all nodes visited *)
    assert (Hcover : S.Subset (nodes g) (S.union L R)).
    { intros x Hx. destruct (SP.In_dec x (S.union L R)); auto.
      exfalso. assert (S.In x (S.diff (nodes g) (S.union L R))) by (apply S.diff_spec; auto).
      destruct (S.cardinal (S.diff (nodes g) (S.union L R))) eqn:Hc; [|lia].
      apply SP.cardinal_inv_1 in Hc. apply (Hc x). auto. }
    intros i Hi. apply nbs_spec in Hi as (v & Hv & Hiv).
    apply Hcover. eapply nbs_subset_nodes; eauto. apply nbs_spec. eauto.
  - (* k = S k *)
    set (Vis := S.union L R).
    set (Radd := add_to_R g FL Vis).
    set (Ladd := add_to_L g FR Vis).
    destruct (S.choose (S.union Ladd Radd)) as [fresh|] eqn:Echoose.
    + (* Non-empty: new vertices added, use IH *)
      assert (Hfresh : S.In fresh (S.union Ladd Radd)) by (apply S.choose_1; auto).
      set (L' := S.union L Ladd). set (R' := S.union R Radd).
      assert (HL' : S.Subset L' (nodes g)).
      { unfold L'. intros x Hx. apply S.union_spec in Hx as [|Hx]; auto.
        unfold Ladd, add_to_L in Hx. apply S.diff_spec in Hx as [Hx _].
        eapply nbs_subset_nodes; eauto. }
      assert (HR' : S.Subset R' (nodes g)).
      { unfold R'. intros x Hx. apply S.union_spec in Hx as [|Hx]; auto.
        unfold Radd, add_to_R in Hx. apply S.diff_spec in Hx as [Hx _].
        eapply nbs_subset_nodes; eauto. }
      assert (HdL' : S.Subset (nbs g (S.diff L' Ladd)) (S.union L' R')).
      { assert (Hdiff_sub : S.Subset (S.diff L' Ladd) L).
        { unfold L'. intros x Hx. apply S.diff_spec in Hx as [Hx Hx'].
          apply S.union_spec in Hx as [|]; auto. contradiction. }
        intros i Hi. apply (nbs_mono _ _ _ Hdiff_sub) in Hi.
        apply (nbs_split_frontier _ _ FL HFL) in Hi.
        apply S.union_spec in Hi as [Hi|Hi].
        - apply (nbs_FL_subset_vis_radd g FL Vis) in Hi.
          apply S.union_spec in Hi as [Hi|Hi].
          * unfold Vis in Hi. apply S.union_spec in Hi as [Hi|Hi];
            apply S.union_spec; [left; unfold L'|right; unfold R'];
            apply S.union_spec; left; auto.
          * apply S.union_spec; right; unfold R'; apply S.union_spec; right; auto.
        - apply HdL in Hi. unfold Vis in Hi.
          apply S.union_spec in Hi as [Hi|Hi];
          apply S.union_spec; [left; unfold L'|right; unfold R'];
          apply S.union_spec; left; auto. }
      assert (HdR' : S.Subset (nbs g (S.diff R' Radd)) (S.union L' R')).
      { assert (Hdiff_sub : S.Subset (S.diff R' Radd) R).
        { unfold R'. intros x Hx. apply S.diff_spec in Hx as [Hx Hx'].
          apply S.union_spec in Hx as [|]; auto. contradiction. }
        intros i Hi. apply (nbs_mono _ _ _ Hdiff_sub) in Hi.
        apply (nbs_split_frontier _ _ FR HFR) in Hi.
        apply S.union_spec in Hi as [Hi|Hi].
        - apply (nbs_FR_subset_vis_ladd g FR Vis) in Hi.
          apply S.union_spec in Hi as [Hi|Hi].
          * unfold Vis in Hi. apply S.union_spec in Hi as [Hi|Hi];
            apply S.union_spec; [left; unfold L'|right; unfold R'];
            apply S.union_spec; left; auto.
          * apply S.union_spec; left; unfold L'; apply S.union_spec; right; auto.
        - apply HdR in Hi. unfold Vis in Hi.
          apply S.union_spec in Hi as [Hi|Hi];
          apply S.union_spec; [left; unfold L'|right; unfold R'];
          apply S.union_spec; left; auto. }
      assert (Hcard' : (S.cardinal (S.diff (nodes g) (S.union L' R')) <= k)%nat).
      { assert (Hfresh_diff : S.In fresh (S.diff (nodes g) Vis)).
        { apply S.union_spec in Hfresh as [Hf|Hf].
          - apply S.diff_spec; split; [apply HL'; apply S.union_spec; right; auto|].
            unfold Ladd, add_to_L in Hf; apply S.diff_spec in Hf; tauto.
          - apply S.diff_spec; split; [apply HR'; apply S.union_spec; right; auto|].
            unfold Radd, add_to_R in Hf; apply S.diff_spec in Hf; tauto. }
        assert (Hfresh_not : ~ S.In fresh (S.diff (nodes g) (S.union L' R'))).
        { intro contra. apply S.diff_spec in contra as [_ contra].
          apply contra. apply S.union_spec in Hfresh as [Hf|Hf];
          apply S.union_spec; [left; unfold L'|right; unfold R'];
          apply S.union_spec; right; auto. }
        assert (Hsub : S.Subset (S.diff (nodes g) (S.union L' R')) (S.diff (nodes g) Vis)).
        { unfold L', R', Vis. intros x Hx. apply S.diff_spec in Hx as [Hx1 Hx2].
          apply S.diff_spec; split; auto. intro contra.
          apply Hx2. apply S.union_spec in contra as [Hc|Hc];
          apply S.union_spec; [left|right]; apply S.union_spec; left; auto. }
        pose proof (SP.subset_cardinal_lt Hsub Hfresh_diff Hfresh_not). unfold Vis in *. lia. }
      apply IH; auto.
      * unfold Ladd. intros x Hx. unfold L'. apply S.union_spec; right; auto.
      * unfold Radd. intros x Hx. unfold R'. apply S.union_spec; right; auto.
    + (* Empty frontiers: closure holds now *)
      assert (HLadd_empty : S.Empty Ladd).
      { apply S.choose_2 in Echoose. intros x Hx. apply (Echoose x).
        apply S.union_spec; left; auto. }
      assert (HRadd_empty : S.Empty Radd).
      { apply S.choose_2 in Echoose. intros x Hx. apply (Echoose x).
        apply S.union_spec; right; auto. }
      assert (HnFL : S.Subset (nbs g FL) Vis).
      { intros x Hx. destruct (SP.In_dec x Vis); auto.
        exfalso. apply (HRadd_empty x). unfold Radd, add_to_R.
        apply S.diff_spec; auto. }
      assert (HnFR : S.Subset (nbs g FR) Vis).
      { intros x Hx. destruct (SP.In_dec x Vis); auto.
        exfalso. apply (HLadd_empty x). unfold Ladd, add_to_L.
        apply S.diff_spec; auto. }
      (* nbs g (L∪R) ⊆ L∪R *)
      assert (Hclosed : S.Subset (nbs g Vis) Vis).
      { intros i Hi. apply nbs_union in Hi.
        apply S.union_spec in Hi as [Hi|Hi].
        - apply (nbs_split_frontier _ _ FL HFL) in Hi.
          apply S.union_spec in Hi as [Hi|Hi]; auto.
        - apply (nbs_split_frontier _ _ FR HFR) in Hi.
          apply S.union_spec in Hi as [Hi|Hi]; auto. }
      (* force_layers with empty frontiers doesn't change L∪R *)
      pose proof (force_layers_noop g (S.union L Ladd) (S.union R Radd) Ladd Radd k
                    HLadd_empty HRadd_empty) as Hnoop.
      destruct (force_layers g (S.union L Ladd) (S.union R Radd) Ladd Radd k) as [Lf Rf].
      destruct Hnoop as [HLf HRf].
      (* Lf ≡ S.union L Ladd ≡ L, Rf ≡ S.union R Radd ≡ R *)
      assert (HLf_eq : forall x, S.In x Lf <-> S.In x L).
      { intro x. rewrite HLf. apply union_empty_equal_l; auto. }
      assert (HRf_eq : forall x, S.In x Rf <-> S.In x R).
      { intro x. rewrite HRf. apply union_empty_equal_l; auto. }
      intros i Hi. apply nbs_spec in Hi as (v & Hv & Hiv).
      apply S.union_spec in Hv as [Hv|Hv].
      * rewrite HLf_eq in Hv. assert (S.In i Vis).
        { apply Hclosed. apply nbs_spec. exists v. split; [apply S.union_spec; left|]; auto. }
        unfold Vis in H. apply S.union_spec in H as [H|H];
        apply S.union_spec; [left; apply HLf_eq|right; apply HRf_eq]; auto.
      * rewrite HRf_eq in Hv. assert (S.In i Vis).
        { apply Hclosed. apply nbs_spec. exists v. split; [apply S.union_spec; right|]; auto. }
        unfold Vis in H. apply S.union_spec in H as [H|H];
        apply S.union_spec; [left; apply HLf_eq|right; apply HRf_eq]; auto.
Qed.

Lemma reached_adj_closed g seed :
  undirected g -> S.In seed (nodes g) ->
  S.Subset (nbs g (reached g seed)) (reached g seed).
Proof.
  intros Ug Hseed.
  unfold reached, force_component_sets.
  pose proof (force_layers_closure g
    (S.singleton seed) S.empty (S.singleton seed) S.empty
    (S.cardinal (nodes g)) Ug) as H.
  destruct (force_layers g (S.singleton seed) S.empty
    (S.singleton seed) S.empty (S.cardinal (nodes g))) as [L' R'] eqn:E.
  simpl in *.
  apply H; clear H.
  - intros x Hx; auto.
  - intros x Hx; auto.
  - intros x Hx. apply S.singleton_1 in Hx. subst; auto.
  - intros x Hx. exfalso. exact (not_in_empty _ Hx).
  - intros i Hi. apply nbs_spec in Hi as (v & Hv & _).
    apply S.diff_spec in Hv as [Hv1 Hv2]. contradiction.
  - intros i Hi. apply nbs_spec in Hi as (v & Hv & _).
    exfalso. exact (not_in_empty _ Hv).
  - apply SP.subset_cardinal. intros x Hx. apply S.diff_spec in Hx as [Hx _]. auto.
Qed.

Lemma domain_bicolor L R c1 c2 :
  S.Equal (Mdomain (bicolor L R c1 c2)) (S.union L R).
Proof.
  unfold bicolor. intro i. rewrite in_domain. rewrite munion_in.
  split.
  - intros [Hi|Hi]; apply S.union_spec;
    [left; rewrite <- domain_constant_color | right; rewrite <- domain_constant_color];
    apply in_domain; exact Hi.
  - intro Hi. apply S.union_spec in Hi as [Hi|Hi];
    [left | right]; apply in_domain;
    rewrite domain_constant_color; exact Hi.
Qed.

Lemma force_all_ok g c1 c2 :
  undirected g -> bipartite g -> c1 <> c2 ->
  coloring_ok (SP.of_list [c1;c2]) g (force_all g c1 c2).
Proof.
  remember (M.cardinal g) as n eqn:Hn.
  revert g Hn.
  induction n as [n IH] using lt_wf_ind.
  intros g Hn Ug Hbip Hneq.
  rewrite force_all_equation.
  destruct (S.choose (nodes g)) as [seed|] eqn:Echoose.
  - (* Some seed *)
    set (LR := force_component_sets g seed).
    set (L := fst LR). set (R := snd LR).
    set (Sreach := S.union L R).
    assert (Hseed : S.In seed (nodes g)) by (apply S.choose_1; auto).
    (* reached set is closed under adjacency *)
    assert (Hclosed : S.Subset (nbs g Sreach) Sreach).
    { unfold Sreach, L, R, LR. apply reached_adj_closed; auto. }
    (* force_component_ok gives coloring_ok on subgraph *)
    pose proof (force_component_ok g seed c1 c2 Ug Hbip Hneq Hseed) as Hcomp.
    unfold force_component, force_component_sets in Hcomp.
    fold LR in Hcomp. fold L R in Hcomp.
    destruct Hcomp as [Hcomp_complete Hcomp_ok].
    (* IH for remove_nodes *)
    assert (Hlt : (M.cardinal (remove_nodes g Sreach) < n)%nat).
    { subst n.
      eapply remove_nodes_lt with (i := seed).
      - unfold Sreach, L, R, LR. apply seed_in_reached.
      - apply in_nodes_iff. auto. }
    assert (Hok_rem : coloring_ok (SP.of_list [c1;c2]) (remove_nodes g Sreach) (force_all (remove_nodes g Sreach) c1 c2)).
    { apply (IH _ Hlt _ (Logic.eq_refl _)); auto.
      - apply remove_nodes_undirected; auto.
      - apply bipartite_remove_nodes; auto. }
    (* domain of bicolor *)
    assert (Hdom : S.Equal (Mdomain (bicolor L R c1 c2)) Sreach).
    { unfold Sreach. apply domain_bicolor. }
    (* combine using coloring_union_no_cross *)
    apply (coloring_union_no_cross g _ Sreach); auto.
  - (* None: empty graph *)
    intros i j Hadj. exfalso.
    apply S.choose_2 in Echoose.
    assert (HiG : S.In i (nodes g)).
    { eapply in_adj_center_in_nodes. eauto. }
    exact (Echoose _ HiG).
Qed.

Lemma force_all_palette g c1 c2 i ci :
  M.find i (force_all g c1 c2) = Some ci -> ci = c1 \/ ci = c2.
Proof.
  remember (M.cardinal g) as n eqn:Hn.
  revert g Hn.
  induction n as [n IH] using lt_wf_ind.
  intros g Hn Hfi.
  rewrite force_all_equation in Hfi.
  destruct (S.choose (nodes g)) as [seed|] eqn:Echoose.
  - set (LR := force_component_sets g seed) in *.
    set (L := fst LR) in *. set (R := snd LR) in *.
    set (Sreach := S.union L R) in *.
    apply munion_case in Hfi as [Hfi|Hfi].
    + (* ci from bicolor L R c1 c2 *)
      unfold bicolor in Hfi. apply munion_case in Hfi as [Hfi|Hfi].
      * left. symmetry. eapply constant_color_inv2. eauto.
      * right. symmetry. eapply constant_color_inv2. eauto.
    + (* ci from force_all (remove_nodes g Sreach) c1 c2 *)
      assert (Hlt : (M.cardinal (remove_nodes g Sreach) < n)%nat).
      { subst n. eapply remove_nodes_lt with (i := seed).
        - unfold Sreach, L, R, LR. apply seed_in_reached.
        - apply in_nodes_iff. apply S.choose_1 in Echoose. auto. }
      eapply IH; eauto.
  - rewrite WF.empty_o in Hfi. discriminate.
Qed.

Lemma reached_subset_nodes g seed :
  undirected g -> S.In seed (nodes g) ->
  S.Subset (reached g seed) (nodes g).
Proof.
  intros Ug Hseed.
  unfold reached, force_component_sets.
  pose proof (force_layers_subsets_nodes g
    (S.singleton seed) S.empty (S.singleton seed) S.empty
    (S.cardinal (nodes g)) Ug) as H.
  destruct (force_layers g (S.singleton seed) S.empty
    (S.singleton seed) S.empty (S.cardinal (nodes g))) as [L' R'].
  simpl. destruct H as [HL HR].
  - intros x Hx. apply S.singleton_1 in Hx. subst. auto.
  - intros x Hx. exfalso. exact (not_in_empty _ Hx).
  - intros x Hx. apply S.singleton_1 in Hx. subst. auto.
  - intros x Hx. exfalso. exact (not_in_empty _ Hx).
  - intros x Hx. apply S.union_spec in Hx as [Hx|Hx]; auto.
Qed.

Lemma force_all_domain g c1 c2 i ci :
  undirected g ->
  M.find i (force_all g c1 c2) = Some ci -> M.In i g.
Proof.
  remember (M.cardinal g) as n eqn:Hn.
  revert g Hn.
  induction n as [n IH] using lt_wf_ind.
  intros g Hn Ug Hfi.
  rewrite force_all_equation in Hfi.
  destruct (S.choose (nodes g)) as [seed|] eqn:Echoose.
  - set (LR := force_component_sets g seed) in *.
    set (L := fst LR) in *. set (R := snd LR) in *.
    set (Sreach := S.union L R) in *.
    assert (Hseed : S.In seed (nodes g)) by (apply S.choose_1; auto).
    apply munion_case in Hfi as [Hfi|Hfi].
    + (* i from bicolor L R c1 c2 — in reached g seed ⊆ nodes g *)
      apply in_nodes_iff.
      apply (reached_subset_nodes g seed Ug Hseed).
      unfold reached, force_component_sets.
      fold LR L R.
      unfold bicolor in Hfi. apply munion_case in Hfi as [Hfi|Hfi];
      apply constant_color_inv in Hfi;
      apply S.union_spec; [left | right]; auto.
    + (* i from recursive call *)
      assert (Hlt : (M.cardinal (remove_nodes g Sreach) < n)%nat).
      { subst n. eapply remove_nodes_lt with (i := seed).
        - unfold Sreach, L, R, LR. apply seed_in_reached.
        - apply in_nodes_iff. auto. }
      assert (Ug' : undirected (remove_nodes g Sreach)).
      { apply remove_nodes_undirected. auto. }
      assert (M.In i (remove_nodes g Sreach)).
      { eapply IH; eauto. }
      eapply subgraph_vert_m; [apply remove_nodes_subgraph | exact H].
  - rewrite WF.empty_o in Hfi. discriminate.
Qed.

(** * Decision procedure for 2-colorability *)

(** ** force_all covers every vertex in g *)
Lemma force_all_covers g c1 c2 :
  undirected g ->
  forall i, M.In i g -> M.In i (force_all g c1 c2).
Proof.
  remember (M.cardinal g) as n eqn:Hn.
  revert g Hn.
  induction n as [n IH] using lt_wf_ind.
  intros g Hn Ug i Hi.
  rewrite force_all_equation.
  destruct (S.choose (nodes g)) as [seed|] eqn:Echoose.
  - set (LR := force_component_sets g seed) in *.
    set (L := fst LR) in *. set (R := snd LR) in *.
    set (Sreach := S.union L R) in *.
    assert (Hseed : S.In seed (nodes g)) by (apply S.choose_1; auto).
    destruct (SP.In_dec i Sreach) as [HiS|HiS].
    + (* i ∈ reached set → colored by bicolor *)
      apply munion_in. left.
      apply in_domain. rewrite domain_bicolor.
      exact HiS.
    + (* i ∉ reached set → colored by recursive call *)
      apply munion_in. right.
      assert (Hlt : (M.cardinal (remove_nodes g Sreach) < n)%nat).
      { subst n. eapply remove_nodes_lt with (i := seed).
        - unfold Sreach, L, R, LR. apply seed_in_reached.
        - apply in_nodes_iff. auto. }
      apply (IH _ Hlt _ (Logic.eq_refl _)).
      * apply remove_nodes_undirected; auto.
      * apply in_nodes_iff. rewrite nodes_remove_nodes_spec.
        split; [apply in_nodes_iff; auto | auto].
  - exfalso. apply S.choose_2 in Echoose.
    apply in_nodes_iff in Hi. exact (Echoose _ Hi).
Qed.

(** ** Boolean checker for coloring properness *)

Definition check_edge (f : coloring) (i j : node) : bool :=
  match M.find i f, M.find j f with
  | Some ci, Some cj => negb (Pos.eqb ci cj)
  | _, _ => true
  end.

Definition coloring_proper_b (g : graph) (f : coloring) : bool :=
  forallb (fun p =>
    let '(i, nbrs) := p in
    forallb (fun j => check_edge f i j) (S.elements nbrs)
  ) (M.elements g).

(** ** Reflection lemma for check_edge *)
Lemma check_edge_true_iff f i j :
  check_edge f i j = true <->
  (forall ci cj, M.find i f = Some ci -> M.find j f = Some cj -> ci <> cj).
Proof.
  unfold check_edge.
  destruct (M.find i f) as [ci|] eqn:Ei, (M.find j f) as [cj|] eqn:Ej;
    try (split; [intros _ ci0 cj0 H1 H2; discriminate | auto]).
  rewrite Bool.negb_true_iff, Pos.eqb_neq.
  split.
  - intros Hneq ci0 cj0 H1 H2. congruence.
  - intros H. apply H; auto.
Qed.

(** ** Reflection lemma for coloring_proper_b *)
Lemma coloring_proper_b_true_iff g f :
  coloring_proper_b g f = true <->
  (forall i j, S.In j (adj g i) ->
    forall ci cj, M.find i f = Some ci -> M.find j f = Some cj -> ci <> cj).
Proof.
  unfold coloring_proper_b.
  rewrite forallb_forall.
  split.
  - (* true → prop *)
    intros Hall i j Hadj ci cj Hci Hcj.
    rewrite adj_in_iff_find in Hadj.
    destruct Hadj as [nbrs [Hfind Hin]].
    assert (HIn : In (i, nbrs) (M.elements g)).
    { apply inA_in_iff. apply M.elements_1. exact Hfind. }
    specialize (Hall _ HIn). simpl in Hall.
    rewrite forallb_forall in Hall.
    assert (HjIn : In j (S.elements nbrs)).
    { apply inA_iff. apply S.elements_1. exact Hin. }
    specialize (Hall _ HjIn).
    rewrite check_edge_true_iff in Hall. eauto.
  - (* prop → true *)
    intros Hprop p Hp. destruct p as [i nbrs]. simpl.
    rewrite forallb_forall.
    intros j Hj.
    apply check_edge_true_iff.
    intros ci cj Hci Hcj.
    apply (Hprop i j); auto.
    rewrite adj_in_iff_find.
    exists nbrs. split.
    + apply M.elements_2. apply inA_in_iff. exact Hp.
    + apply S.elements_2. apply inA_iff. exact Hj.
Qed.

(** ** Combining palette and properness into coloring_ok *)
Lemma coloring_ok_of_proper_and_palette palette g f :
  (forall i ci, M.find i f = Some ci -> S.In ci palette) ->
  (forall i j, S.In j (adj g i) ->
    forall ci cj, M.find i f = Some ci -> M.find j f = Some cj -> ci <> cj) ->
  coloring_ok palette g f.
Proof.
  intros Hpal Hprop.
  intros i j Hadj. split.
  - intros ci Hci. eapply Hpal. exact Hci.
  - intros ci cj Hci Hcj. eapply Hprop; eauto.
Qed.

(** ** Decision procedure for 2-colorability *)
Definition decide_two_colorable (g : graph) :
  undirected g -> no_selfloop g ->
  { f : coloring | coloring_complete two_colors g f } + { ~ bipartite g }.
Proof.
  intros Ug Hns.
  set (f := force_all g 1%positive 2%positive).
  destruct (coloring_proper_b g f) eqn:Echeck.
  - (* coloring is proper → exhibit it *)
    left. exists f. split.
    + (* completeness: every vertex is colored *)
      intros i Hi. apply force_all_covers; auto.
    + (* coloring_ok *)
      apply coloring_ok_of_proper_and_palette.
      * (* palette *)
        intros i ci Hci.
        apply force_all_palette in Hci.
        destruct Hci as [->| ->];
          apply SP.of_list_1; simpl; auto.
      * (* properness *)
        apply coloring_proper_b_true_iff. exact Echeck.
  - (* coloring is not proper → graph is not bipartite *)
    right. intro Hbip.
    assert (Hok : coloring_ok (SP.of_list [1%positive;2%positive]) g f).
    { apply force_all_ok; auto. lia. }
    assert (Hprop : coloring_proper_b g f = true).
    { apply coloring_proper_b_true_iff.
      intros i j Hadj ci cj Hci Hcj.
      destruct (Hok i j Hadj) as [_ Hdiff]. eauto. }
    congruence.
Defined.