Require Import graph.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
Require Import Decidable.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
Import Arith.
Import ListNotations.
Import Nat.

(* Restrict a map by a set of keys *)
(* Fold over the set we are restricting with for better induction. *)
Definition restrict {A} (m : M.t A) s :=
  S.fold (fun k m' => match M.find k m with
                   | Some v => M.add k v m'
                   | None => m'
                   end) s (@M.empty _).
  
Lemma restrict_subset_keys {A} : forall (m : M.t A) s, S.Subset (Mdomain (restrict m s)) (Mdomain m).
Proof.
  intros m s.
  unfold restrict.
  apply SP.fold_rec_bis.
  - sauto lq: on.
  - hecrush.
  - intros x a s' H H0 H1.
    destruct (M.find x m) eqn:E.
    + intros i Hi.
      destruct (E.eq_dec x i).
      * subst. qauto use: Sin_domain unfold: PositiveMap.MapsTo, PositiveMap.In.
      * hauto lq: on use: WF.add_neq_in_iff, Sin_domain unfold: PositiveSet.elt, PositiveSet.Subset, PositiveMap.key.
    + assumption.
Qed.

Lemma restrict_incl {A} :
  forall s (f : M.t A) i, M.In i (restrict f s) -> M.In i f.
Proof.
  hauto lq: on use: @restrict_subset_keys, Sin_domain unfold: PositiveSet.Subset, PositiveSet.elt, PositiveMap.key.
Qed.

Lemma restrict_restricts {A} :
  forall s (f : M.t A) i, S.In i s -> M.In i f -> M.In i (restrict f s).
Proof.
  intros s f i Hi Hf.
  generalize dependent Hi.
  unfold restrict.
  apply SP.fold_rec_bis.
  - sfirstorder.
  - sauto q: on.
  - intros x a s' H H0 H1 Hi.
    destruct (E.eq_dec i x).
    + subst. hfcrush use: WF.in_find_iff, WF.add_in_iff unfold: PositiveSet.elt, PositiveMap.key inv: option.
    + qauto use: PositiveSet.add_3, WF.add_in_iff unfold: PositiveSet.elt, PositiveMap.key inv: option.
Qed.

(* extensive use of hammer *)
Lemma restrict_full {A} :
  forall s (f : M.t A) (v i : M.key),
    S.In i s ->
    M.In i f ->
    S.Subset (Mdomain (restrict f s)) (Mdomain f) ->
    S.In i (Mdomain (restrict f s)).
Proof.
  hfcrush use: @restrict_restricts, Sin_domain unfold: PositiveSet.elt, PositiveMap.key.
Qed.  

(* Looking through restriction of a map, the values still agree *)
Lemma restrict_agree {A} : forall (m : M.t A) s k v,
    M.find k (restrict m s) = Some v ->
    M.find k m = Some v.
Proof.
  intros m s k v.
  unfold restrict.
  apply SP.fold_rec_bis.
  - sfirstorder.
  - sauto lq: on.
  - intros x a s' H H0 H1 H2.
    destruct (E.eq_dec k x).
    + subst. hauto use: PositiveMap.gss unfold: PositiveMap.key, PositiveSet.elt inv: option.
    + hauto use: PositiveMap.gso unfold: PositiveSet.elt, PositiveMap.key inv: option.
Qed.

Lemma restrict_agree_2 {A} : forall (m : M.t A) s k,
    S.In k s -> M.find k m = M.find k (restrict m s).
Proof.
  intros m s k H.
  destruct (M.find k m) eqn:E.
  - hfcrush use: @restrict_agree, @restrict_restricts, WF.in_find_iff unfold: PositiveMap.key, PositiveSet.elt inv: option.
  - apply not_not.
    {
      unfold decidable.
      remember (M.find k (restrict m s)) as y.
      destruct y; sfirstorder.
    }
    intros contra.
    destruct (M.find k (restrict m s)) eqn:E2.
    + qauto use: @restrict_agree unfold: PositiveSet.elt, PositiveMap.key.
    + contradiction.
Qed.

(* Being in the restriction is enough evidence to be in the set *)
Lemma restrict_in_set {A} : forall (m : M.t A) s k v,
    M.find k (restrict m s) = Some v ->
    S.In k s.
Proof.
  intros m s k v.
  unfold restrict.
  apply SP.fold_rec_bis.
  - sfirstorder.
  - sauto lq: on rew: off.
  - intros x a s' H H0 H1 H2.
    destruct (E.eq_dec k x).
    + subst. hauto l: on use: PositiveSet.add_1.
    + hauto use: PositiveSet.add_2, PositiveMap.gso unfold: PositiveMap.key, PositiveSet.elt inv: option.
Qed.

Lemma restrict_m {A} : forall s s',
    S.Equal s s' ->
    forall k k' : M.t A, M.Equal k k' -> M.Equal (restrict k s) (restrict k' s').
Proof.
  intros s s' H k k' H0.
  apply WF.Equal_mapsto_iff.
  intros k0 e.
  unfold M.MapsTo.
  hauto lq: on use: @restrict_agree_2, @restrict_in_set unfold: PositiveSet.elt, PositiveMap.key, PositiveMap.Equal, PositiveSet.Equal.
Qed.

Lemma restrict_map_comm {A B} : forall (m : M.t A) (f : A -> B) s,
    M.Equal (M.map f (restrict m s)) (restrict (M.map f m) s).
Proof.
  intros m f s.
  apply WF.Equal_mapsto_iff.
  unfold M.MapsTo.
  intros k e.
  split; intros H.
  - rewrite WF.map_o in H.
    destruct (M.find k (restrict m s)) eqn:E; [|scongruence].
    simpl in H.
    rewrite <- H.
    pose proof (restrict_in_set m s k _ E).
    eapply restrict_agree in E.
    pose proof (restrict_agree_2 m _ _ H0).
    pose proof (restrict_agree_2 (M.map f m) s k H0).
    ssimpl.
    qauto use: WF.map_o unfold: PositiveMap.MapsTo, option_map.
  - hfcrush use: WF.map_o, @restrict_in_set, @restrict_agree_2 unfold: PositiveSet.elt, PositiveMap.key.
Qed.
