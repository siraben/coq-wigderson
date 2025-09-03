Require Import graph.
Require Import subgraph.
Require Import restrict.
Require Import munion.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
Require Import Decidable.
Require Import Program.
Require Import FunInd.
Require Import Psatz.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
Import Arith.
Import ListNotations.
Import Nat.

Local Open Scope positive_scope.

Create HintDb coloring_spec.

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


Definition step (g : graph) (x y : node) : Prop := S.In y (adj g x).


Inductive walk (g : graph) : node -> list node -> node -> Prop :=
| walk_nil  : forall x, M.In x g -> walk g x [] x
| walk_cons : forall x y l z, step g x y -> walk g y l z -> walk g x (y :: l) z.

Definition simple (g : graph) (x : node) (l : list node) (z : node) :=
  walk g x l z /\ NoDup (x :: l ++ [z]).


Definition reachable (g : graph) (u v : node) : Prop :=
  exists l, walk g u l v.

Definition cycle (g : graph) (x : node) (l : list node) :=
  l <> [] /\ walk g x l x.

Definition simple_cycle (g : graph) (x : node) (l : list node) :=
  cycle g x l /\ NoDup (x :: l).  (* typical: forbid repeated internal vertices *)

Definition even_walk {A} (l : list A) := Nat.even (length l) = true.
Definition odd_walk {A} (l : list A) := Nat.odd  (length l) = true.

Lemma walk_cons_iff g x y l z : walk g x (y::l) z <-> step g x y /\ walk g y l z.
Proof. sauto lq: on rew: off. Qed.

Lemma walk_singleton g x y :
  step g x y -> M.In y g -> walk g x [y] y.
Proof.
  intros Hstep Hy. econstructor; [exact Hstep|].
  now apply walk_nil.
Qed.


Lemma walk_start_in : forall g x l z, walk g x l z -> M.In x g.
Proof.
  intros g x l z H.
  induction H.
  - assumption.
  - hauto lq: on use: FExt.in_nodes_iff, FExt.in_adj_center_in_nodes unfold: node, PositiveSet.elt, PositiveOrderedTypeBits.t, step.
Qed.

Lemma walk_end_in   : forall g x l z, undirected g -> walk g x l z -> M.In z g.
Proof.
  intros g x l z H H0.
  induction H0; assumption.
Qed.
  
Lemma walk_all_in_nodes :
  forall g x l z, undirected g -> walk g x l z ->
             Forall (fun v => S.In v (nodes g)) (x :: l ++ [z]).
Proof.
  intros g x l z H H0.
  induction H0.
  - cbn.
    rewrite !Forall_cons_iff.
    best use: Sin_domain unfold: nodes.
  - cbn.
    apply Forall_cons_iff.
    split.
    + sauto lq: on use: FExt.in_adj_center_in_nodes unfold: PositiveSet.elt, PositiveMap.key, step inv: walk, list.
    + assumption.
Qed.

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

(* Subgraph monotonicity *)
Lemma walk_subgraph_mono :
  forall g' g x l z, is_subgraph g' g -> walk g' x l z -> walk g x l z.
Proof.
  intros g' g x l z H H0.
  induction H0.
  - hauto l: on use: subgraph_vert_m, walk_nil.
  - sfirstorder use: walk_cons unfold: node, step, is_subgraph, PositiveOrderedTypeBits.t, PositiveSet.elt, PositiveSet.Subset.
Qed.

(* Induced subgraph: if all vertices lie in s, walk is preserved *)
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
        all: eauto using walk_start_in, walk_end_in, Sin_domain.
      * apply IHW. eapply Forall_inv_tail. exact Hall.
Qed.

(* Removing vertices: if the walk touches none of them, it persists *)
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
