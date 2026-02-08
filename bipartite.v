Require Import graph.
Require Import subgraph.
Require Import restrict.
Require Import coloring.
Require Import munion.
Require Import List.
Require Import Setoid.
Require Import FSets.
Require Import FMaps.
Require Import PArith.
Require Import Decidable.
Require Import Program.
Require Import FunInd.
Require Import wigderson.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.

Import Arith.
Import ListNotations.
Import Nat.

Local Open Scope positive_scope.

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

(** ** Basic consequences *)
Lemma bipartite_no_selfloop g :
  bipartite g -> no_selfloop g.
Proof.
  intros [L [R (Hdisj & Hcov & HindL & HindR)]].
  unfold no_selfloop.
  intros v Hv.
  (* v is in nodes -> v is in L or R; both independent → no self-loop *)
  hfcrush use: SP.Dec.F.union_iff, FExt.in_adj_center_in_nodes unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, node, independent_set, PositiveSet.Equal.
Qed.

(** * From bipartition to complete 2-coloring *)

Definition bicolor (L R : S.t) (c1 c2 : node) : coloring :=
  Munion (constant_color L c1) (constant_color R c2).

Lemma bicolor_ok g L R c1 c2 :
  undirected g ->
  c1 <> c2 ->
  is_bipartition g L R ->
  coloring_ok (SP.of_list [c1; c2]) g (bicolor L R c1 c2).
Proof.
  intros Ug Hneq (Hdisj & Hcov & HindL & HindR).
  (* Use our general union-of-colorings lemma with disjoint palettes {c1} and {c2} *)
  assert (HokL : coloring_ok (S.singleton c1) g (constant_color L c1)).
  { split.
    - hauto l: on use: constant_color_inv2, PositiveSet.singleton_2.
    - intros ci cj H0 H1.
      hauto lq: on rew: off use: constant_color_inv unfold: independent_set.
  }
  assert (HokR : coloring_ok (S.singleton c2) g (constant_color R c2)).
  { split.
    - hauto l: on use: constant_color_inv2, PositiveSet.singleton_2.
    - intros ci cj H0 H1.
      hauto lq: on rew: off use: constant_color_inv unfold: independent_set.
  }
  (* Palettes disjoint *)
  assert (S.Empty (S.inter (S.singleton c1) (S.singleton c2))).
  { hfcrush use: PositiveSet.singleton_1, PositiveSet.inter_spec unfold: PositiveSet.Empty. }
  (* Convert (singleton ∪ singleton) to of_list [c1;c2] *)
  assert (SE :
    S.Equal (SP.of_list [c1;c2]) (S.union (S.singleton c1) (S.singleton c2))).
  { hauto l: on use: SP.add_union_singleton, PositiveSet.cardinal_1
          unfold: SP.of_list, fold_right, PositiveSet.singleton, PositiveSet.empty. }
  (* Union of ok colorings with disjoint palettes is ok; then rewrite palette *)
  eapply ok_coloring_set_eq; [symmetry; exact SE|].
  eapply coloring_union; eauto.
Qed.

Lemma bicolor_complete g L R c1 c2 :
  is_bipartition g L R ->
  (forall i, M.In i g -> M.In i (bicolor L R c1 c2)).
Proof.
  intros (Hdisj & Hcov & _ & _) i Hi.
  apply Sin_domain in Hi.
  assert (HiUR : S.In i (S.union L R)) by sfirstorder.
  apply S.union_spec in HiUR as [HiL|HiR].
  - apply Munion_in. left. apply Sin_domain.
    strivial use: domain_constant_color unfold: PositiveMap.key, PositiveSet.elt, PositiveSet.Equal.
  - apply Munion_in. right. apply Sin_domain.
    strivial use: domain_constant_color unfold: PositiveSet.Equal, PositiveSet.elt, PositiveMap.key.
Qed.

Lemma bipartition_two_coloring_complete g L R :
  undirected g ->
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
  match M.find i f with
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
  S.In i (side_of f c) <-> S.In i (Mdomain f) /\ M.find i f = Some c.
Proof.
  unfold side_of, color_is.
  split.
  - intro Hi.
    apply (SP.Dec.F.filter_iff) in Hi; [|apply color_is_compat].
    destruct Hi as [Hin Hb].
    destruct (M.find i f) as [d|] eqn:Fi; simpl in Hb; [|discriminate].
    apply Pos.eqb_eq in Hb; subst d.
    sfirstorder.
  - intros [Hin Hfind].
    apply SP.Dec.F.filter_iff; [apply color_is_compat|].
    split; [assumption|].
    rewrite Hfind; simpl; now rewrite Pos.eqb_refl.
Qed.

Lemma L_of_spec g f c i :
  S.In i (L_of g f c) <-> S.In i (nodes g) /\ M.find i f = Some c.
Proof.
  unfold L_of, color_is.
  split.
  - intro Hi.
    apply SP.Dec.F.filter_iff in Hi; [|apply color_is_compat].
    destruct Hi as [Hg Hb].
    destruct (M.find i f) as [d|] eqn:Fi; simpl in Hb; [|discriminate].
    apply Pos.eqb_eq in Hb; subst d. sfirstorder.
  - intros [Hg Hfind].
    apply SP.Dec.F.filter_iff; [apply color_is_compat|].
    split; [assumption|].
    rewrite Hfind; simpl; now rewrite Pos.eqb_refl.
Qed.

Lemma L_of_subset_nodes g f c :
  S.Subset (L_of g f c) (nodes g).
Proof.
  unfold L_of. intros i Hi.
  strivial use: L_of_spec unfold: L_of.
Qed.

Lemma R_of_spec g f c i :
  S.In i (R_of g f c) <-> S.In i (nodes g) /\ M.find i f <> Some c.
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
  assert (Hex : exists c, S.In c p).
  { destruct (S.elements p) eqn:E.
    - hfcrush use: SP.elements_Empty, SP.cardinal_Empty unfold: colors.
    - exists e.
      qauto use: set_elemeum, PositiveSet.add_spec unfold: PositiveSet.empty, fold_right, colors, SP.of_list, PositiveSet.Equal inv: list.
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
    - assert (M.In i f).
      {
        hauto l: on use: Sin_domain.
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
    destruct (Hcomp i) as [ci HInfi]; [ now apply Sin_domain |].
    destruct (Hcomp j) as [cj HInfj]; [ now apply Sin_domain |].
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
      assert (HMi : M.In i f) by (apply Hdom; now apply Sin_domain).
      assert (HMj : M.In j f) by (apply Hdom; now apply Sin_domain).
      destruct HMi as [ci Hci]. destruct HMj as [cj Hcj].
      unfold M.MapsTo in Hci, Hcj.
      destruct (Hok j i Hadj) as [Hpal_j Hneq].
      assert (Hadj' : S.In j (adj g i)) by (apply Ug; exact Hadj).
      destruct (Hok i j Hadj') as [Hpal_i _].
      specialize (Hpal_j _ Hcj). specialize (Hpal_i _ Hci).
      assert (ci <> 1) by congruence.
      assert (cj <> 1) by congruence.
      rewrite SP.of_list_1, InA_iff in Hpal_i, Hpal_j.
      simpl in Hpal_i, Hpal_j.
      assert (ci = 2) by (destruct Hpal_i as [|[|[]]]; congruence).
      assert (cj = 2) by (destruct Hpal_j as [|[|[]]]; congruence).
      subst. apply (Hneq _ _ Hcj Hci). reflexivity.
Qed.

(** * Stability under induced subgraphs *)
Lemma bipartite_subgraph_of g s :
  bipartite g -> bipartite (subgraph_of g s).
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
  - hauto depth: 2 lq: on exh: on use: adj_subgraph_of_spec, PositiveSet.inter_1 unfold: PositiveOrderedTypeBits.t, node, independent_set, PositiveSet.elt.
  - hauto depth: 2 lq: on exh: on use: adj_subgraph_of_spec, PositiveSet.inter_1 unfold: PositiveOrderedTypeBits.t, node, independent_set, PositiveSet.elt.
Qed.

(** * Neighborhood of a 3-colorable graph is bipartite *)

Lemma neighborhood_bipartite_of_three_coloring :
  forall (g : graph) (f : coloring) (p : colors) (v : node),
    undirected g ->
    coloring_complete p g f ->
    three_coloring f p ->
    bipartite (neighborhood g v).
Proof.
  intros g f p v Ug Hc H3.
  (* If v is in G, we can use our nbd_2_colorable_3.  If not, the neighborhood is empty and bipartite. *)
  destruct (WF.In_dec g v) as [Hv|Hnv].
  - (* v is colored *)
    unfold coloring_complete in Hc.
    destruct (proj1 Hc v Hv) as [cv Hfv].
    unfold M.MapsTo in Hfv.
    destruct (nbd_2_colorable_3 g f p Hc H3 v cv ltac:(assumption)) as [H2col HcompN].
    destruct (two_coloring_complete_to_bipartition _ _ _ HcompN H2col) as [c Hbip].
    sfirstorder.
  - (* v not in g ⇒ neighbors are empty ⇒ neighborhood empty ⇒ bipartite *)
    assert (neighbors g v = S.empty).
    { unfold neighbors. now rewrite adj_empty_if_notin by auto. }
    unfold neighborhood. rewrite H.
    (* subgraph_of g S.empty is empty graph; removing v changes nothing *)
    assert (M.Equal (subgraph_of g S.empty) (@M.empty _)) by hauto use: subgraph_of_empty.
    unfold bipartite.
    exists S.empty, S.empty.
    hauto lq: on drew: off use: SP.Dec.F.empty_iff, nodes_neighborhood_spec, PositiveSet.choose_2 unfold: is_bipartition, PositiveSet.choose, PositiveSet.empty, PositiveSet.union, neighbors, PositiveSet.inter, neighborhood, PositiveSet.Equal, independent_set.
Qed.
