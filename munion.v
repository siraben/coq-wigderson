Require Import graph.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
Import Arith.
Import ListNotations.
Import Nat.

Local Open Scope positive_scope.

(* union of maps (left-heavy) *)
Definition Munion {A} (f g : M.t A) := M.fold (fun k v => M.add k v) f g.
(* Two maps are disjoint if their keys have no intersection. *)
(* Mkeys is just Mdomain *)
Definition Mdisjoint {A} (f g : M.t A) := S.Equal (S.inter (Mdomain f) (Mdomain g)) S.empty.

(* Test case for disjointness *)
Example Mdisjoint_test1 :
  Mdisjoint (fold_right (fun p m => M.add (fst p) (snd p) m) (@M.empty _) [(1,1);(2,2)])
            (fold_right (fun p m => M.add (fst p) (snd p) m) (@M.empty _) [(3,1);(4,2)]).
Proof. hauto l: on. Qed.

(* Note: since we're using equality on finite sets can we get for free
   that map disjointness is decidable *)
Lemma Mdisjoint_dec {A} (f g : M.t A) : {Mdisjoint f g} + {~ Mdisjoint f g}.
Proof. apply S.eq_dec. Qed.

Lemma Munion_case {A} : forall (c d : M.t A) i v,
    M.find i (Munion c d) = Some v -> M.MapsTo i v c \/ M.MapsTo i v d.
Proof.
  intros c d i.
  unfold Munion.
  apply WP.fold_rec_bis.
  - hauto unfold: PositiveMap.MapsTo, PositiveMap.In, PositiveMap.Equal.
  - hauto l: on.
  - intros k e a m' H H0 H1 v H2.
    destruct (E.eq_dec i k).
    + hauto use: PositiveMap.gss unfold: PositiveMap.In, PositiveMap.MapsTo.
    + qauto use: WP.F.add_neq_mapsto_iff, PositiveMap.gss unfold: PositiveMap.In, PositiveMap.MapsTo.
Qed.
