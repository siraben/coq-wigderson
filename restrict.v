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
  WP.filter (fun k v => S.mem k s) m.
  
(** ** Domain of restricted map is a subset of the original domain *)
Lemma restrict_subset_keys {A} : forall (m : M.t A) s, S.Subset (Mdomain (restrict m s)) (Mdomain m).
Proof.
  intros m s.
  unfold restrict.
  intros v Hv.
  apply Sin_domain.
  apply Sin_domain in Hv.
  destruct Hv as [e He].
  rewrite WP.filter_iff in He; sfirstorder.
Qed.

(** ** Membership in a restricted map implies membership in the original map *)
Lemma restrict_incl {A} :
  forall s (f : M.t A) i, M.In i (restrict f s) -> M.In i f.
Proof.
  qauto use: Sin_domain, @restrict_subset_keys unfold: PositiveMap.key, PositiveSet.elt, PositiveSet.Subset.
Qed.


(** Restrict/lookup in one step *)
Lemma restrict_find_some_iff {A} (m : M.t A) s k v :
  M.find k (restrict m s) = Some v
  <-> S.In k s /\ M.find k m = Some v.
Proof.
  unfold restrict.
  split; intro H.
  - (* -> *)
    apply M.find_2 in H.
    rewrite WP.filter_iff in H; [| sfirstorder].
    sfirstorder.
  - (* <- *)
    destruct H as [Hin Hf].
    apply M.find_1.
    rewrite WP.filter_iff; [|sfirstorder].
    sfirstorder.
Qed.

Lemma restrict_in_iff {A} (m : M.t A) s k :
  M.In k (restrict m s) <-> S.In k s /\ M.In k m.
Proof.
  strivial use: WF.MapsTo_fun, @restrict_find_some_iff, @restrict_incl unfold: PositiveMap.In, PositiveMap.MapsTo.
Qed.

Lemma nodes_restrict_eq (g : graph) s :
  S.Equal (nodes (restrict g s)) (S.inter (nodes g) s).
Proof.
  intro k; split; intro Hin.
  - apply Sin_domain in Hin as [e Hf].
    apply restrict_find_some_iff in Hf as [Hs Hfind].
    apply S.inter_spec; split; [ apply Sin_domain; eexists; eauto | exact Hs ].
  - apply S.inter_spec in Hin as [Hg Hs].
    apply Sin_domain in Hg as [e Hmt].
    apply Sin_domain. exists e.
    strivial use: @restrict_find_some_iff unfold: PositiveSet.elt, nodemap, PositiveMap.MapsTo, PositiveMap.key, graph.
Qed.


Lemma find_filter {A} (f : M.key -> A -> bool) m k v :
  M.find k (WP.filter f m) = Some v -> M.find k m = Some v.
Proof.
  intros H.
  apply M.find_2 in H.
  rewrite WP.filter_iff in H; [|sfirstorder].
  sfirstorder.
Qed.

(** ** Membership in the original map implies membership in the restricted map *)
Lemma restrict_restricts {A} :
  forall s (f : M.t A) i, S.In i s -> M.In i f -> M.In i (restrict f s).
Proof.
  strivial use: @restrict_find_some_iff unfold: PositiveMap.key, PositiveMap.MapsTo, PositiveMap.In, PositiveSet.elt.
Qed.

Lemma restrict_full {A} (m : M.t A) :
  M.Equal (restrict m (Mdomain m)) m.
Proof.
  apply WF.Equal_mapsto_iff; intros k v; split; intro H.
  - strivial use: @restrict_find_some_iff unfold: PositiveMap.MapsTo.
  - hfcrush use: Sin_domain, WF.not_find_mapsto_iff, @restrict_find_some_iff unfold: PositiveSet.elt, PositiveMap.MapsTo, PositiveMap.key.
Qed.

(* Looking through restriction of a map, the values still agree *)
(** ** Values in restricted maps agree with the original map *)
Lemma restrict_agree {A} : forall (m : M.t A) s k v,
    M.find k (restrict m s) = Some v ->
    M.find k m = Some v.
Proof.
  intros m s k v.
  strivial use: @restrict_find_some_iff.
Qed.

(** ** Values in restricted maps agree with the original map (rephrased) *)
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
  strivial use: @restrict_find_some_iff.
Qed.

(** ** Restriction preserves map equality *)
Lemma restrict_m {A} : forall s s',
    S.Equal s s' ->
    forall k k' : M.t A, M.Equal k k' -> M.Equal (restrict k s) (restrict k' s').
Proof.
  intros s s' H k k' H0.
  apply WF.Equal_mapsto_iff.
  intros k0 e.
  unfold M.MapsTo.
  hfcrush use: @restrict_find_some_iff, @restrict_agree_2 unfold: PositiveSet.elt, PositiveMap.Equal, PositiveMap.key, PositiveSet.Equal.
Qed.


(** ** Specification of restriction *)
Lemma restrict_spec : forall {A} (m : M.t A) s k,
    M.In k (restrict m s) <-> M.In k m /\ S.In k s.
Proof.
  intros A m s k.
  strivial use: @restrict_agree_2, @restrict_in_iff, SP.Dec.FSetDecideTestCases.test_iff_conj unfold: PositiveSet.elt, PositiveMap.key.
Qed.

(** ** Restriction and map commute *)
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
    rewrite restrict_find_some_iff.
    qauto use: @restrict_find_some_iff, @restrict_incl, WF.in_find_iff, WF.map_o unfold: option_map.
  - hfcrush use: WF.map_o, @restrict_agree_2, @restrict_find_some_iff unfold: PositiveSet.elt, PositiveMap.key.
Qed.

(** ** Cardinality of a restricted map *)
Lemma restrict_cardinal {A} : forall (m : M.t A) s,
    M.cardinal (restrict m s) = S.cardinal (S.inter (Mdomain m) s).
Proof.
  intros m s.
  apply Mcardinal_Scardinal.
  intros k.
  hfcrush use: @restrict_in_iff, Sin_domain, PositiveSet.inter_1, PositiveSet.inter_spec, PositiveSet.inter_2 unfold: PositiveMap.key, PositiveSet.elt.
Qed.

(** ** Adjacency in a restricted graph *)
Lemma adj_restrict : forall g s i j,
    S.In i (adj (restrict g s) j) <-> S.In i (adj g j) /\ S.In j s.
Proof.
  intros g s i j.
  split.
  - intros H.
    apply in_adj_exists in H.
    destruct H as [v [F I]].
    hauto use: @restrict_find_some_iff, @restrict_agree, find_in_adj, I unfold: PositiveMap.key, PositiveOrderedTypeBits.t, node.
  - intros [I J].
    apply in_adj_exists in I.
    destruct I as [v [F I]].
    eapply find_in_adj.
    rewrite <- restrict_agree_2 by auto.
    eauto.
    auto.
Qed.

Lemma restrict_find {A} (m : M.t A) s i :
  M.find i (restrict m s) = if S.mem i s then M.find i m else None.
Proof.
  pose proof (@restrict_spec A m s i).
  hauto use: SP.Dec.F.not_mem_iff, @restrict_agree_2, WF.not_find_mapsto_iff unfold: PositiveSet.In, PositiveSet.elt, PositiveMap.key inv: bool.
Qed.

(** Idempotence / intersection law *)
Lemma restrict_idem {A} (m : M.t A) s t :
  M.Equal (restrict (restrict m s) t) (restrict m (S.inter s t)).
Proof.
  apply WF.Equal_mapsto_iff; intros k v; split; intro H.
  - apply M.find_1 in H.
    apply restrict_find_some_iff in H as [Ht Hst].
    apply restrict_find_some_iff in Hst as [Hs Hmt].
    apply M.find_1. apply restrict_find_some_iff.
    split; [apply S.inter_spec; tauto|assumption].
  - apply M.find_1 in H.
    apply restrict_find_some_iff in H as [Hint Hmt].
    apply S.inter_spec in Hint as [Hs Ht].
    apply M.find_1. apply restrict_find_some_iff.
    hauto lq: on use: @restrict_find unfold: PositiveSet.In inv: bool.
Qed.

(** Monotonicity *)
Lemma restrict_mono {A} (m : M.t A) s t :
  S.Subset s t -> M.Equal (restrict m s) (restrict (restrict m t) s).
Proof.
  intro Hsub.
  apply WF.Equal_mapsto_iff; intros k v; split; intro H.
  - apply M.find_1 in H.
    apply restrict_find_some_iff in H as [Hs Hmt].
    apply M.find_1. apply restrict_find_some_iff.
    split; [assumption|].
    apply M.find_1. apply restrict_find_some_iff.
    split; [apply Hsub; assumption|assumption].
  - apply M.find_1 in H.
    apply restrict_find_some_iff in H as [Hs Ht].
    apply restrict_find_some_iff in Ht as [_ Hmt].
    apply M.find_1. apply restrict_find_some_iff. tauto.
Qed.

Lemma restrict_empty {A} (m : M.t A) :
  M.Equal (restrict m S.empty) (@M.empty A).
Proof.
  apply WF.Equal_mapsto_iff; intros k v; split; intro H.
  - apply M.find_2 in H. unfold restrict in H.
    rewrite WP.filter_iff in H by firstorder. destruct H as [_ Hmem].
    apply S.mem_2 in Hmem. inversion Hmem.
  - sauto q: on.
Qed.
