Require Import graph.
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

(** Map/set/domain conversions *)

Lemma in_nodes_iff g v : S.In v (nodes g) <-> M.In v g.
Proof. unfold nodes; now rewrite Sin_domain. Qed.

Lemma find_iff_in {A} (m : M.t A) k v :
  M.find k m = Some v <-> M.In k m /\ exists e, M.MapsTo k e m /\ v = e.
Proof. sfirstorder. Qed.

Lemma in_dec_nodes g v : {S.In v (nodes g)} + {~ S.In v (nodes g)}.
Proof. destruct (WF.In_dec g v); firstorder using in_nodes_iff. Qed.

Lemma adj_in_iff_find g j i :
  S.In i (adj g j) <-> exists e, M.find j g = Some e /\ S.In i e.
Proof.
  qauto use: PositiveSet.mem_Leaf unfold: negb, PositiveSet.empty, PositiveSet.In, adj.
Qed.

(* Trivial direction: the center j must be a key if it has a non-empty adj. *)
Lemma in_adj_center_in_nodes g i j :
  S.In i (adj g j) -> S.In j (nodes g).
Proof.
  rewrite adj_in_iff_find; firstorder using in_nodes_iff.
Qed.

(* With undirectedness you also get the neighbor is a key. *)
Lemma in_adj_neighbor_in_nodes g i j :
  undirected g -> S.In i (adj g j) -> S.In i (nodes g).
Proof.
  intros U Hij. apply U in Hij. (* symmetry j∈adj(i) *)
  now apply in_adj_center_in_nodes in Hij.
Qed.

(* Consolidated: both endpoints are nodes in an undirected graph. *)
Lemma in_adj_both_in_nodes g i j :
  undirected g -> S.In i (adj g j) -> S.In i (nodes g) /\ S.In j (nodes g).
Proof.
  sfirstorder use: in_adj_center_in_nodes, in_adj_neighbor_in_nodes.
Qed.
