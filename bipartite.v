(** * bipartite.v - Bipartition and 2-coloring equivalence *)
Require Import graph.
Require Import subgraph.
Require Import graph_notations.
Require Import coloring.
Require Import munion.
Require Import List.
Require Import Setoid.
Require Import FSets.
Require Import FMaps.
Require Import PArith.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.

Import Arith.
Import ListNotations.
Import Nat.

Local Open Scope positive_scope.
Local Open Scope graph_scope.

(** * Bipartite graphs *)

(** ** A bipartition of a graph [g] is a pair of vertex sets [L] and [R]
    such that they are disjoint, cover all vertices of [g], and each side
    is an independent set (no internal edges). *)
Definition is_bipartition (g : graph) (L R : S.t) : Prop :=
  S.Empty (S.inter L R)
  /\ S.Equal (S.union L R) (nodes g)
  /\ independent_set g L
  /\ independent_set g R.

(** ** A graph is bipartite if it admits a bipartition. *)
Definition bipartite (g : graph) : Prop :=
  exists L R, is_bipartition g L R.

(** ** Symmetry of bipartition *)
Lemma bipartition_sym g L R :
  is_bipartition g L R -> is_bipartition g R L.
Proof.
  hfcrush use: SP.union_sym, SP.equal_trans, SP.inter_sym unfold: PositiveSet.Equal, is_bipartition, PositiveSet.Empty.
Qed.

(** ** A vertex of a bipartite graph lies in one of the two sides *)
Lemma in_bipartition_or g L R i :
  is_bipartition g L R -> i ∈ V[ g ] -> i ∈ L \/ i ∈ R.
Proof.
  intros (_ & Hcov & _ & _) Hi.
  apply S.union_spec, Hcov, Hi.
Qed.

(** ** A graph with no vertices is bipartite *)
Lemma bipartite_no_nodes g :
  S.Empty (nodes g) -> bipartite g.
Proof.
  intro Hempty.
  exists S.empty, S.empty.
  repeat split; sauto lq: on use: SP.Dec.F.empty_iff unfold: PositiveSet.Empty, PositiveSet.Equal, independent_set.
Qed.

(** ** Basic consequences *)
Lemma bipartite_no_selfloop g :
  bipartite g -> no_selfloop g.
Proof.
  intros [L [R (Hdisj & Hcov & HindL & HindR)]].
  unfold no_selfloop.
  intros v Hv.
  (* v is in nodes -> v is in L or R; both independent → no self-loop *)
  hfcrush use: SP.Dec.F.union_iff, in_adj_center_in_nodes unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, node, independent_set, PositiveSet.Equal.
Qed.

(** * From bipartition to complete 2-coloring *)

Definition bicolor (L R : S.t) (c1 c2 : node) : coloring :=
  Munion (constant_color L c1) (constant_color R c2).

Lemma bicolor_ok g L R c1 c2 :
  c1 <> c2 ->
  is_bipartition g L R ->
  coloring_ok (SP.of_list [c1; c2]) g (bicolor L R c1 c2).
Proof.
  intros Hneq (_ & _ & HindL & HindR) i j Hij.
  unfold bicolor.
  split.
  - intros ci Hci; munion_cases Hci;
      hauto l: on use: constant_color_inv2, SP.of_list_1, inA_iff.
  - intros ci cj Hci Hcj.
    munion_cases2 Hci Hcj.
    all: try solve [hauto lq: on use: constant_color_inv unfold: independent_set].
    all: apply constant_color_inv2 in Hci, Hcj; congruence.
Qed.

Lemma bicolor_complete g L R c1 c2 :
  is_bipartition g L R ->
  (forall i, i ∈ dom g -> i ∈ dom (bicolor L R c1 c2)).
Proof.
  intros Hbip i Hi.
  apply in_nodes_iff in Hi.
  destruct (in_bipartition_or _ _ _ _ Hbip Hi) as [HiL|HiR].
  - apply munion_in. left. apply in_domain.
    strivial use: domain_constant_color unfold: PositiveMap.key, PositiveSet.elt, PositiveSet.Equal.
  - apply munion_in. right. apply in_domain.
    strivial use: domain_constant_color unfold: PositiveSet.Equal, PositiveSet.elt, PositiveMap.key.
Qed.

Lemma bipartition_two_coloring_complete g L R :
  is_bipartition g L R ->
  coloring_complete (SP.of_list [1;2]) g (bicolor L R 1 2).
Proof.
  intros H.
  split.
  - intros i Hi. eapply bicolor_complete; eassumption.
  - now apply bicolor_ok.
Qed.

(** * From complete 2-coloring to bipartition *)

(** We build the sides as the preimage of one color and its complement
    in the vertex set.  We do not need to enumerate the two palette
    elements explicitly. *)

(* one place to define the test we use in L_of/side_of *)
Definition color_is (f : coloring) (c : node) (i : S.elt) : bool :=
  match f !! i with
  | Some d => Pos.eqb d c
  | None   => false
  end.

(* This discharges the compat_bool obligation for filter lemmas *)
Local Lemma color_is_compat f c :
  compat_bool S.E.eq (color_is f c).
Proof. scongruence. Qed.

(* side_of over Mdomain *)
Definition side_of (f : coloring) (c : node) : S.t :=
  S.filter (color_is f c) (Mdomain f).

(* sides over nodes g (what you use) *)
Definition L_of (g : graph) (f : coloring) (c : node) : S.t :=
  S.filter (color_is f c) (nodes g).

Definition R_of (g : graph) (f : coloring) (c : node) : S.t :=
  S.diff (nodes g) (L_of g f c).

Lemma side_of_spec f c i :
  i ∈ side_of f c <-> i ∈ Mdomain f /\ f !! i = Some c.
Proof.
  unfold side_of, color_is.
  split.
  - intro Hi.
    apply (SP.Dec.F.filter_iff) in Hi; [|apply color_is_compat].
    destruct Hi as [Hin Hb].
    destruct (f !! i) as [d|] eqn:Fi; simpl in Hb; [|discriminate].
    apply Pos.eqb_eq in Hb; subst d.
    sfirstorder.
  - intros [Hin Hfind].
    apply SP.Dec.F.filter_iff; [apply color_is_compat|].
    split; [assumption|].
    rewrite Hfind; simpl; now rewrite Pos.eqb_refl.
Qed.

Lemma L_of_spec g f c i :
  i ∈ L_of g f c <-> i ∈ V[ g ] /\ f !! i = Some c.
Proof.
  unfold L_of, color_is.
  split.
  - intro Hi.
    apply SP.Dec.F.filter_iff in Hi; [|apply color_is_compat].
    destruct Hi as [Hg Hb].
    destruct (f !! i) as [d|] eqn:Fi; simpl in Hb; [|discriminate].
    apply Pos.eqb_eq in Hb; subst d. sfirstorder.
  - intros [Hg Hfind].
    apply SP.Dec.F.filter_iff; [apply color_is_compat|].
    split; [assumption|].
    rewrite Hfind; simpl; now rewrite Pos.eqb_refl.
Qed.

Lemma L_of_subset_nodes g f c :
  L_of g f c ⊆ V[ g ].
Proof.
  unfold L_of. intros i Hi.
  strivial use: L_of_spec unfold: L_of.
Qed.

Lemma R_of_spec g f c i :
  i ∈ R_of g f c <-> i ∈ V[ g ] /\ f !! i <> Some c.
Proof.
  qauto use: PositiveSet.diff_3, PositiveSet.diff_spec, L_of_spec unfold: R_of.
Qed.

Lemma L_R_cover g f c :
  S.Equal (S.union (L_of g f c) (R_of g f c)) (nodes g).
Proof.
  intro i; split; intro Hi.
  - apply S.union_spec in Hi. destruct Hi as [Hi|Hi].
    + apply L_of_subset_nodes in Hi; assumption.
    + unfold R_of in Hi. apply S.diff_spec in Hi as [Hg _]; assumption.
  - destruct (S.mem i (L_of g f c)) eqn:Emem.
    + apply S.mem_2 in Emem. apply S.union_spec. now left.
    + apply S.union_spec. right. unfold R_of. apply S.diff_spec.
      split; [assumption|].
      apply SP.Dec.F.not_mem_iff in Emem. exact Emem.
Qed.

Lemma L_R_disjoint g f c :
  S.Empty (S.inter (L_of g f c) (R_of g f c)).
Proof.
  intros i. rewrite S.inter_spec, R_of_spec, L_of_spec. firstorder.
Qed.

Lemma two_coloring_complete_to_bipartition g f p :
  coloring_complete p g f ->
  two_coloring f p ->
  exists c, is_bipartition g (L_of g f c) (R_of g f c).
Proof.
  intros (Hcomp & Hok) [Hp2 Hmem].
  (* pick one color c in the 2-element palette *)
  assert (Hex : exists c, c ∈ p).
  { destruct (S.elements p) eqn:E.
    - hfcrush use: SP.elements_Empty, SP.cardinal_Empty unfold: colors.
    - exists e.
      qauto use: set_elements_fold, PositiveSet.add_spec unfold: PositiveSet.empty, fold_right, colors, SP.of_list, PositiveSet.Equal inv: list.
  }
  destruct Hex as [c Hc].
  exists c.
  (* Disjointness *)
  assert (Hdisj : S.Empty (S.inter (L_of g f c) (R_of g f c))).
  { intros x Hx. apply S.inter_spec in Hx as [HxL HxR].
    apply L_of_spec in HxL. apply R_of_spec in HxR.
    destruct HxL as [HxG Hfi]; destruct HxR as [_ Hneq]. congruence. }
  (* Cover *)
  assert (Hcov : S.Equal (S.union (L_of g f c) (R_of g f c)) (nodes g)).
  { intro i; split; intro Hi.
    - apply S.union_spec in Hi as [Hi|Hi]; [apply L_of_spec in Hi|apply R_of_spec in Hi]; tauto.
    - assert (i ∈ dom f).
      {
        hauto l: on use: in_domain.
      }
      destruct H as [ix Hix]; unfold M.MapsTo in Hix.
      destruct (Pos.eqb ix c) eqn:E.
      + apply Pos.eqb_eq in E.
        subst.
        qauto use: PositiveSet.union_2, L_of_spec unfold: PositiveOrderedTypeBits.t, R_of, node, PositiveSet.elt.
      + apply Pos.eqb_neq in E.
        apply S.union_spec.
        right.
        qauto use: R_of_spec unfold: PositiveSet.elt, node, PositiveOrderedTypeBits.t.
  }
  (* Independence of L: same color c on both endpoints would contradict Hok *)
  assert (HindL : independent_set g (L_of g f c)).
  { intros i j Hi Hj Hadj.
    apply L_of_spec in Hi as [HiG Hfi].
    apply L_of_spec in Hj as [HjG Hfj].
    strivial unfold: node, PositiveSet.elt, coloring_ok, PositiveOrderedTypeBits.t.

  }
  (* Independence of R: all nodes outside L must have the other color (only two colors available) *)
  assert (HindR : independent_set g (R_of g f c)).
  { intros i j Hi Hj Hadj.
    apply R_of_spec in Hi as [HiG Hni].
    apply R_of_spec in Hj as [HjG Hnj].
    (* completeness gives some colors *)
    destruct (Hcomp i) as [ci HInfi]; [ now apply in_domain |].
    destruct (Hcomp j) as [cj HInfj]; [ now apply in_domain |].
    inversion HInfi; subst; clear HInfi.
    inversion HInfj; subst; clear HInfj.
    (* palette has cardinal 2 → both ci and cj are among these two; not equal to c means equal to the other one *)
    (* Now use Hok to forbid same color on an edge *)
    specialize (Hok _ _ Hadj).
    (* If both are different from c, they must be equal (the other color), hence contradiction.  *)
    (* We prove by contradiction: assume adjacency, then Hok demands ci <> cj. *)
    (* But since p has exactly two elements and both ci,cj <> c, they must be equal. *)
    assert (ci <> c) by sfirstorder.
    assert (cj <> c) by sfirstorder.
    (* Since S.cardinal p = 2, any color in p \ {c} is unique; we don't need its name. *)
    assert (ci = cj).
    { (* Both belong to p, and both <> c; in a 2-element set that's enough. *)
      (* Use extensionality with elements list to reason. *)
      pose proof (PositiveSet.cardinal_1 p) as HC.
      assert (S.cardinal p = 2)%nat by exact Hp2.
      clear HC.
      (* A simple counting argument: there is exactly one element different from c. *)
      assert (length (PositiveSet.elements p) = 2)%nat.
      {
        clear - H3.
        scongruence use: PositiveSet.cardinal_1 unfold: colors.
      }
      destruct (PositiveSet.elements p) as [| xx [|yy zz]] eqn:E; try discriminate.
      simpl in H4.
      assert (zz = []) by hauto use: length_zero_iff_nil.
      subst.
      clear - E H0 H1 Hmem H H2 Hc.
      apply Hmem in H0, H1; clear Hmem.
      apply S.elements_1 in Hc, H0, H1.
      rewrite E in Hc, H0, H1.
      sauto.
    }
    sfirstorder.
  }
  sfirstorder.
Qed.

(** ** Equivalence: bipartite <-> exists complete 2-coloring *)
Lemma bipartite_iff_exists_two_coloring g :
  undirected g -> (bipartite g <->
  exists f, coloring_complete (SP.of_list [1;2]) g f).
Proof.
  intros Ug.
  split.
  - intros [L [R H]].
    exists (bicolor L R 1 2).
    now apply bipartition_two_coloring_complete.
  - intros [f [Hdom Hok]].
    exists (L_of g f 1), (R_of g f 1).
    split; [apply L_R_disjoint|].
    split; [apply L_R_cover|].
    split.
    + (* independence of L: both endpoints have color 1, contradicts coloring_ok *)
      intros i j Hi Hj Hadj.
      apply L_of_spec in Hi as [_ Hfi].
      apply L_of_spec in Hj as [_ Hfj].
      destruct (Hok j i Hadj) as [_ Hneq].
      apply (Hneq _ _ Hfj Hfi). reflexivity.
    + (* independence of R: both have color <> 1, so both = 2, contradicts coloring_ok *)
      intros i j Hi Hj Hadj.
      apply R_of_spec in Hi as [HiG Hni].
      apply R_of_spec in Hj as [HjG Hnj].
      assert (HMi : i ∈ dom f) by (apply Hdom; now apply in_domain).
      assert (HMj : j ∈ dom f) by (apply Hdom; now apply in_domain).
      destruct HMi as [ci Hci]. destruct HMj as [cj Hcj].
      unfold M.MapsTo in Hci, Hcj.
      destruct (Hok j i Hadj) as [Hpal_j Hneq].
      assert (Hadj' : i ~[ g ] j) by (apply Ug; exact Hadj).
      destruct (Hok i j Hadj') as [Hpal_i _].
      specialize (Hpal_j _ Hcj). specialize (Hpal_i _ Hci).
      assert (ci <> 1) by congruence.
      assert (cj <> 1) by congruence.
      rewrite SP.of_list_1, inA_iff in Hpal_i, Hpal_j.
      simpl in Hpal_i, Hpal_j.
      assert (ci = 2) by (destruct Hpal_i as [|[|[]]]; congruence).
      assert (cj = 2) by (destruct Hpal_j as [|[|[]]]; congruence).
      subst. apply (Hneq _ _ Hcj Hci). reflexivity.
Qed.

(** * Stability under induced subgraphs *)

(** ** An independent set stays independent (intersected with [t]) in the induced subgraph *)
Lemma independent_set_inter_subgraph_of g s t :
  independent_set g s -> independent_set (g ⇂ t) (S.inter s t).
Proof.
  intros Hind i j Hi Hj.
  rewrite adj_subgraph_of_spec.
  hauto lq: on use: PositiveSet.inter_1 unfold: independent_set.
Qed.

Lemma bipartite_subgraph_of g s :
  bipartite g -> bipartite (g ⇂ s).
Proof.
  intros [L [R (Hdisj & Hcov & HindL & HindR)]].
  exists (S.inter L s), (S.inter R s).
  repeat split.
  - (* disjointness *)
    intros contra.
    hfcrush use: PositiveSet.inter_1, PositiveSet.inter_spec, PositiveSet.inter_2 unfold: PositiveSet.Empty.
  - (* cover nodes of induced subgraph *)
    hcrush use: PositiveSet.union_3, PositiveSet.union_2, nodes_subgraph_of_spec, PositiveSet.union_1, PositiveSet.inter_spec unfold: PositiveSet.Equal.
  - hfcrush use: PositiveSet.union_2, PositiveSet.inter_3, nodes_subgraph_of_spec, PositiveSet.union_1, PositiveSet.union_3 unfold: PositiveSet.Equal.
  - apply independent_set_inter_subgraph_of; assumption.
  - apply independent_set_inter_subgraph_of; assumption.
Qed.

(** * Neighborhood of a 3-colorable graph is bipartite *)

Lemma neighborhood_bipartite_of_three_coloring :
  forall (g : graph) (f : coloring) (p : colors) (v : node),
    undirected g ->
    coloring_complete p g f ->
    three_coloring f p ->
    bipartite N[ g ; v ].
Proof.
  intros g f p v Ug Hc H3.
  (* If [v] is in [g], its neighborhood is 2-colorable. Otherwise the
     neighborhood is empty and therefore bipartite. *)
  destruct (WF.In_dec g v) as [Hv|Hnv].
  - (* v is colored *)
    unfold coloring_complete in Hc.
    destruct (proj1 Hc v Hv) as [cv Hfv].
    unfold M.MapsTo in Hfv.
    destruct (neighborhood_two_colorable_of_three g f p Hc H3 v cv ltac:(assumption)) as [H2col HcompN].
    destruct (two_coloring_complete_to_bipartition _ _ _ HcompN H2col) as [c Hbip].
    sfirstorder.
  - (* v not in g ⇒ neighbors are empty ⇒ neighborhood has no nodes ⇒ bipartite *)
    apply bipartite_no_nodes.
    intros w Hw.
    rewrite nodes_neighborhood_spec in Hw.
    hauto lq: on use: adj_empty_if_notin, SP.Dec.F.empty_iff unfold: neighbors.
Qed.
