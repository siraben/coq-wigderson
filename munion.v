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
(** ** Decidability of map disjointness *)
Lemma Mdisjoint_dec {A} (f g : M.t A) : {Mdisjoint f g} + {~ Mdisjoint f g}.
Proof. apply S.eq_dec. Qed.

(** ** Membership of a map union *)
Lemma Munion_case {A} : forall (c d : M.t A) i v,
    M.find i (Munion c d) = Some v -> M.find i c = Some v \/ M.find i d = Some v.
Proof.
  intros c d i.
  unfold Munion.
  apply WP.fold_rec_bis.
  - hauto unfold: PositiveMap.MapsTo, PositiveMap.In, PositiveMap.Equal.
  - hauto l: on.
  - intros k e a m' H H0 H1 v H2.
    destruct (E.eq_dec i k).
    + sfirstorder use: PositiveMap.gss.
    + hauto use: PositiveMapAdditionalFacts.gsident, WF.add_neq_o, PositiveMap.gss.
Qed.

(** ** Left-priority lookup in a map union *)
Lemma Munion_find_l {A} : forall (c d : M.t A) i v,
    M.find i c = Some v -> M.find i (Munion c d) = Some v.
Proof.
  intros c d i.
  unfold Munion.
  apply WP.fold_rec_bis.
  - hauto unfold: PositiveMap.Equal.
  - hauto use: WP.F.empty_o.
  - intros k e a m' H H0 H1 v H2.
    destruct (E.eq_dec i k) as [->|Hneq].
    + hauto use: PositiveMap.gss.
    + rewrite PositiveMap.gso by auto. apply H1.
      rewrite PositiveMap.gso in H2 by auto. exact H2.
Qed.

(** ** Membership of a map union (expressed with M.In) *)
Lemma Munion_in {A} : forall i (m1 m2 : M.t A),
    M.In i (Munion m1 m2) <-> M.In i m1 \/ M.In i m2.
Proof.
  intros i m1 m2.
  split.
  - hfcrush use: WP.F.not_find_mapsto_iff, @Munion_case unfold: PositiveMap.MapsTo, PositiveMap.In.
  - intros H.
    unfold Munion.
    destruct H.
    + destruct H as [e He].
      unfold M.MapsTo in He.
      revert He.
      apply WP.fold_rec_bis.
      * qauto l: on.
      * sauto lq: on rew: off.
      * intros k e0 a m' H H0 H1 He.
        destruct (E.eq_dec i k).
        ** hauto lq: on rew: off use: PositiveMap.gss unfold: PositiveMap.In, PositiveMap.MapsTo.
        ** hauto lq: on use: PositiveMap.gso, WF.add_neq_in_iff.
    + destruct H as [e He].
      unfold M.MapsTo in He.
      revert He.
      apply WP.fold_rec_bis.
      * qauto l: on.
      * sauto lq: on rew: off.
      * intros k e0 a m' H H0 H1 He.
        destruct (E.eq_dec i k).
        ** hauto lq: on rew: off use: PositiveMap.gss unfold: PositiveMap.In, PositiveMap.MapsTo.
        ** hauto lq: on use: PositiveMap.gso, WF.add_neq_in_iff.
Qed.
