(** * connectivity.v - Walks, reachability, and bipartition parity *)
Require Import graph.
Require Import subgraph.
Require Import List.
Require Import Setoid.
Require Import FSets.
Require Import FMaps.
Require Import PArith.
Require Import Psatz.
Require Import bipartite.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
Import Arith.
Import ListNotations.
Import Nat.

Local Open Scope positive_scope.

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


(** * Walks and reachability *)

(** ** A single step follows an edge [x -> y] *)
Definition step (g : graph) (x y : node) : Prop := S.In y (adj g x).

(** ** A walk is a sequence of steps recording its intermediate vertices *)
Inductive walk (g : graph) : node -> list node -> node -> Prop :=
| walk_nil  : forall x, M.In x g -> walk g x [] x
| walk_cons : forall x y l z, step g x y -> walk g y l z -> walk g x (y :: l) z.

(** ** A simple walk has no repeated vertices *)
Definition simple (g : graph) (x : node) (l : list node) (z : node) :=
  walk g x l z /\ NoDup (x :: l ++ [z]).

(** ** [u] reaches [v] if some walk connects them *)
Definition reachable (g : graph) (u v : node) : Prop :=
  exists l, walk g u l v.

(** ** A cycle is a non-empty walk returning to its start *)
Definition cycle (g : graph) (x : node) (l : list node) :=
  l <> [] /\ walk g x l x.

(** ** A simple cycle forbids repeated internal vertices *)
Definition simple_cycle (g : graph) (x : node) (l : list node) :=
  cycle g x l /\ NoDup (x :: l).

(** ** Walk of even/odd length (counted by number of steps) *)
Definition even_walk {A} (l : list A) := Nat.even (length l) = true.
Definition odd_walk {A} (l : list A) := Nat.odd  (length l) = true.

(** ** Inversion for a walk starting with a step *)
Lemma walk_cons_iff g x y l z : walk g x (y::l) z <-> step g x y /\ walk g y l z.
Proof. sauto lq: on rew: off. Qed.

(** ** A single edge to a vertex in [g] is a walk *)
Lemma walk_singleton g x y :
  step g x y -> M.In y g -> walk g x [y] y.
Proof.
  intros Hstep Hy. econstructor; [exact Hstep|].
  now apply walk_nil.
Qed.


(** ** The start of a walk is a vertex of the graph *)
Lemma walk_start_in : forall g x l z, walk g x l z -> M.In x g.
Proof.
  intros g x l z H.
  induction H.
  - assumption.
  - hauto lq: on use: in_nodes_iff, in_adj_center_in_nodes unfold: node, PositiveSet.elt, PositiveOrderedTypeBits.t, step.
Qed.

(** ** The end of a walk is a vertex of the graph *)
Lemma walk_end_in   : forall g x l z, undirected g -> walk g x l z -> M.In z g.
Proof.
  intros g x l z H H0.
  induction H0; assumption.
Qed.

(** ** Every vertex on a walk is a node of the graph *)
Lemma walk_all_in_nodes :
  forall g x l z, undirected g -> walk g x l z ->
             Forall (fun v => S.In v (nodes g)) (x :: l ++ [z]).
Proof.
  intros g x l z H H0.
  induction H0.
  - cbn.
    rewrite !Forall_cons_iff.
    sauto lq: on rew: off use: in_domain unfold: nodes.
  - cbn.
    apply Forall_cons_iff.
    split.
    + sauto lq: on use: in_adj_center_in_nodes unfold: PositiveSet.elt, PositiveMap.key, step inv: walk, list.
    + assumption.
Qed.

(** ** Walks compose by concatenation *)
Lemma walk_app :
  forall g x l1 y l2 z, walk g x l1 y -> walk g y l2 z -> walk g x (l1 ++ l2) z.
Proof.
  intros g x l1 y l2 z H H0.
  generalize dependent x.
  generalize dependent y.
  generalize dependent l2.
  induction l1.
  - sauto.
  - sauto.
Qed.

(** ** A walk in a subgraph is a walk in the supergraph *)
Lemma walk_subgraph_mono :
  forall g' g x l z, is_subgraph g' g -> walk g' x l z -> walk g x l z.
Proof.
  intros g' g x l z H H0.
  induction H0.
  - hauto l: on use: subgraph_vert_m, walk_nil.
  - sfirstorder use: walk_cons unfold: node, step, is_subgraph, PositiveOrderedTypeBits.t, PositiveSet.elt, PositiveSet.Subset.
Qed.

(** ** Induced subgraph: a walk whose vertices all lie in [s] is preserved *)
Lemma walk_in_subgraph_of_iff :
  forall g s x l z,
    Forall (fun v => S.In v s) (x :: l ++ [z]) ->
    (walk (subgraph_of g s) x l z <-> walk g x l z).
Proof.
  intros g s x l z Hall; split; intro W.
  - apply walk_subgraph_mono with (g' := subgraph_of g s); [apply subgraph_of_is_subgraph|assumption].
  - induction W; simpl in *.
    + apply walk_nil.
      inversion Hall; subst.
      hauto use: subgraph_of_in_iff.
    + apply walk_cons_iff. split.
      * inversion Hall; subst.
        inversion H3; subst.
        unfold step. rewrite adj_subgraph_of_spec. repeat split; try now apply Forall_forall in Hall.
        all: eauto using walk_start_in, walk_end_in, in_domain.
      * apply IHW. eapply Forall_inv_tail. exact Hall.
Qed.

(** ** Removing vertices: a walk touching none of them persists *)
Lemma walk_preserved_remove_nodes g s x l z :
  Forall (fun v => ~ S.In v s) (x :: l ++ [z]) ->
  (walk (remove_nodes g s) x l z <-> walk g x l z).
Proof.
  intro Hall; split; intro W.
  - apply walk_subgraph_mono with (g' := remove_nodes g s); [apply remove_nodes_subgraph|assumption].
  - induction W.
    + apply walk_nil. rewrite in_remove_nodes_iff. split; [assumption|].
      sauto.
    + apply walk_cons_iff. split.
      * unfold step. rewrite adj_remove_nodes_spec. repeat split; try now apply Forall_forall in Hall.
        all: sauto.
      * apply IHW. eapply Forall_inv_tail. exact Hall.
Qed.

(** * Bipartition and walk parity *)

(** ** A step from [L] lands in [R] *)
Lemma step_L_R g L R x y :
  undirected g ->
  is_bipartition g L R ->
  S.In x L -> step g x y -> S.In y R.
Proof.
  intros Ug (Hdisj & Hcov & HindL & HindR) Hx Hxy.
  qauto use: SP.Dec.F.union_iff, in_adj_both_in_nodes unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, step, node, undirected, independent_set, PositiveSet.Equal.
Qed.

(** ** A step from [R] lands in [L] *)
Lemma step_R_L g L R x y :
  undirected g ->
  is_bipartition g L R ->
  S.In x R -> step g x y -> S.In y L.
Proof.
  intros Ug (Hdisj & Hcov & HindL & HindR) Hx Hxy.
  qauto use: SP.Dec.F.union_iff, in_adj_both_in_nodes unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, step, node, undirected, independent_set, PositiveSet.Equal.
Qed.

(** ** Side of a walk's endpoint is determined by its start side and length parity *)
Lemma bipartition_walk_parity_even g L R :
  undirected g ->
  is_bipartition g L R ->
  forall x l z, walk g x l z ->
    (* start in L *)
    (S.In x L ->
       (Nat.even (length l) = true  -> S.In z L) /\
       (Nat.even (length l) = false -> S.In z R))
  /\ (* start in R *)
    (S.In x R ->
       (Nat.even (length l) = true  -> S.In z R) /\
       (Nat.even (length l) = false -> S.In z L)).
Proof.
  intros Ug Hbip x l z W; revert x z W.
  induction l as [|y l IH]; intros x z W; simpl.
  - inversion W; subst; split; intros Hx; split; intro He.
    + now cbn in He; inversion He.
    + sauto.
    + now cbn in He; inversion He.
    + sauto.
  - inversion W as [|x' y' l' z' Hxy Hyz]; subst.
    specialize (IH y z Hyz). destruct IH as [IH_L IH_R].
    split.
    + (* start in L *)
      intros HxL.
      assert (HyR : S.In y R) by (eapply step_L_R; eauto).
      destruct (IH_R HyR) as [EvTrue EvFalse].
      hauto lq: on use: even_1, even_succ, odd_1, even_0 unfold: Init.Nat.odd inv: nat.
    + (* start in R *)
      intros HxR.
      assert (HyL : S.In y L) by (eapply step_R_L; eauto).
      hauto lq: on use: even_1, even_succ, odd_1, even_0 unfold: Init.Nat.odd inv: nat.
Qed.

(** ** Parity of a walk starting in [L]: even ends in [L], odd ends in [R] *)
Lemma bipartition_walk_parity_L g L R x l z :
  undirected g ->
  is_bipartition g L R ->
  S.In x L -> walk g x l z ->
  (Nat.even (length l) = true  -> S.In z L) /\
  (Nat.odd  (length l) = true  -> S.In z R).
Proof.
  intros Ug Hbip HxL W.
  pose proof (bipartition_walk_parity_even g L R Ug Hbip x l z W) as [HL _].
  hauto lq: on drew: off use: even_0, negb_odd, even_succ, even_1 unfold: Init.Nat.odd.
Qed.
