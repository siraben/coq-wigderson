(** * graph.v - Core graph definitions, greedy coloring, and map/set infrastructure *)
Require Import List.
Require Import Setoid.
Require Import FSets.
Require Import FMaps.
Require Import PArith.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
From Hammer Require Import Hints.
Import Arith.
Import ListNotations.

(** Core module definitions for positive-based sets and maps *)

Module E := PositiveOrderedTypeBits.
Module S <: FSetInterface.S := PositiveSet.
Module SP := FSetProperties.Properties S.
Module M <: FMapInterface.S := PositiveMap.
Module WF := WFacts_fun E M.
Module WP := WProperties_fun E M.

(** Core lemmas about E.lt ordering *)
Lemma lt_strict: StrictOrder E.lt.
Proof. exact M.ME.MO.IsTO.lt_strorder. Qed.

Lemma lt_proper: Proper (eq ==> eq ==> iff) E.lt.
Proof. exact M.ME.MO.IsTO.lt_compat. Qed.

(** Domain extraction from maps *)
Definition Mdomain {A} (m: M.t A) : S.t :=
  M.fold (fun n _ s => S.add n s) m S.empty.

(** Useful tactic *)
Ltac inv H := inversion H; clear H; subst.

(** Core lemmas about equality and sorting *)
Lemma eqlistA_Eeq_eq: forall al bl, eqlistA E.eq al bl <-> al=bl.
Proof.
  split; intro.
  * induction H; hauto lq: on rew: off.
  * subst. induction bl; sauto lq: on.
Qed.

Lemma SortE_equivlistE_eqlistE:
  forall al bl, Sorted E.lt al ->
           Sorted E.lt bl ->
           equivlistA E.eq al bl -> eqlistA E.eq al bl.
Proof.
  apply SortA_equivlistA_eqlistA; auto.
  apply lt_strict.
  apply lt_proper.
Qed.

Lemma filter_sortE: forall f l,
    Sorted E.lt l -> Sorted E.lt (List.filter f l).
Proof.
  apply filter_sort with E.eq; intuition.
Qed.

Lemma proper_eq_eq:
  forall f, Proper (E.eq ==> @eq bool) f.
Proof.
  congruence.
Qed.

Lemma s_remove_elements:  forall (i: E.t) (s: S.t),
    S.In i s ->
    S.elements (S.remove i s) =
      List.filter (fun x => if E.eq_dec x i then false else true) (S.elements s).
Proof.
  intros.
  apply eqlistA_Eeq_eq.
  apply SortE_equivlistE_eqlistE.
  * (* To prove this one, [SearchAbout S.elements] *)
    apply PositiveSet.elements_3.
  * (* Use [filter_sortE] to prove this one *)
    apply filter_sortE. apply PositiveSet.elements_3.
  *
    intro j.
    rewrite filter_InA; [ | apply proper_eq_eq].
    pose proof S.remove_1.
    pose proof S.remove_2.
    pose proof S.remove_3.
    pose proof S.elements_1.
    pose proof S.elements_2.
    hauto lq: on rew: off.
Qed.

Lemma inA_map_fst_key:
  forall A j l,
    InA E.eq j (map (@fst M.E.t A) l) <-> exists e, InA (@M.eq_key_elt A) (j,e) l.
Proof.
  split; induction l; intros H; sauto lq: on rew: off.
Qed.

Lemma sorted_lt_key:
  forall A (al: list (positive*A)),
    Sorted (@M.lt_key A) al <->  Sorted E.lt (map (@fst positive A) al).
Proof.
  induction al; sauto.
Qed.

(** Cardinality lemmas *)
Lemma cardinal_map:  forall A B (f: A -> B) g,
    M.cardinal (M.map f g) = M.cardinal g.
Proof.
  (** Hint:  To prove this theorem, I used these lemmas.
     You might find a different way. *)
  pose proof M.elements_1.
  pose proof M.elements_2.
  pose proof M.elements_3.
  pose proof map_length.
  pose proof eqlistA_length.
  pose proof SortE_equivlistE_eqlistE.
  pose proof inA_map_fst_key.
  pose proof WF.map_mapsto_iff.
  pose proof sorted_lt_key.
  intros A B f g.
  rewrite !M.cardinal_1.
  pose proof (SortE_equivlistE_eqlistE (map fst (M.elements g)) (map fst (M.elements (M.map f g))) ltac:(hauto l:on) ltac:(hauto l:on)).
  assert (equivlistA E.eq (map fst (M.elements g)) (map fst (M.elements (M.map f g)))).
  {
    unfold equivlistA.
    intros x.
    split; intros HH.
    - hauto lq: on rew: off.
    - fcrush.
  }
  hauto l: on.
Qed.

Lemma s_remove_cardinal_less: forall i s,
    S.In i s -> S.cardinal (S.remove i s) < S.cardinal s.
Proof.
  sfirstorder use: SP.remove_cardinal_1, le_n unfold: lt.
Qed.

Lemma specialize_SortA_equivlistA_eqlistA:
  forall A al bl,
    Sorted (@M.lt_key A) al ->
    Sorted (@M.lt_key A) bl ->
    equivlistA (@M.eq_key_elt A) al bl ->
    eqlistA (@M.eq_key_elt A) al bl.
Proof.
  intros.
  apply SortA_equivlistA_eqlistA with (@M.lt_key A); auto.
  apply M.eqke_equiv.
  apply M.ltk_strorder.
  clear.
  repeat intro.
  unfold M.lt_key, M.eq_key_elt in *.
  destruct H, H0. rewrite H,H0. split; auto.
Qed.

Lemma proper_eq_key_elt:
  forall A,
    Proper (@M.eq_key_elt A ==> @M.eq_key_elt A ==> iff)
      (fun x y : E.t * A => E.lt (fst x) (fst y)).
Proof.
  repeat intro. destruct H,H0. rewrite H,H0. split; auto.
Qed.

Lemma m_remove_cardinal_less: forall A i (s: M.t A), M.In i s ->
                                               M.cardinal (M.remove i s) < M.cardinal s.
Proof.
  intros A i s H.
  pose proof WP.cardinal_2.
  assert (~ M.In i (M.remove i s)) by strivial use: WF.remove_in_iff, diff_false_true unfold: PositiveMap.key.
  enough (S (M.cardinal (M.remove i s)) = M.cardinal s); [hauto l: on|].
  symmetry.
  destruct H as [e He].
  apply H0 with (x := i) (e := e).
  - assumption.
  - qauto use: PositiveMap.gro, WP.F.add_o unfold: WP.Add, PositiveMap.MapsTo inv: sumbool.
Qed.

Lemma fold_right_rev_left:
  forall (A B: Type) (f: A -> B -> A) (l: list B) (i: A),
    fold_left f l i = fold_right (fun x y => f y x) i (rev l).
Proof.
  intros A B f l i.
  generalize dependent i.
  induction l; hauto lq: on use: fold_right_app.
Qed.

Lemma not_in_empty: forall n, ~ S.In n S.empty.
Proof.
  sfirstorder.
Qed.

Lemma in_domain: forall A n (g: M.t A), S.In n (Mdomain g) <-> M.In n g.
Proof.
  (** To reason about [M.fold], used in the definition of [Mdomain],
    a useful theorem is [WP.fold_rec_bis]. *)
  intros A n g.
  unfold Mdomain.
  split.
  - intros H.
    rewrite M.fold_1 in H.
    rewrite fold_right_rev_left in H.
    assert ((fun (x : M.key * A) (y : S.t) => S.add (fst x) y) = WP.uncurry (fun a b c => S.add a c)) by sfirstorder.
    rewrite H0 in H.
    clear H0.
    rewrite <- WP.fold_spec_right in H.
    generalize dependent n.
    apply WP.fold_rec_bis.
    + hauto lq: on use: WF.In_m unfold: PositiveSet.elt.
    + sauto q: on.
    + intros k e a m' H H0 H1 n H2.
      destruct (E.eq_dec n k).
      * hfcrush use: WF.add_in_iff.
      * qauto use: PositiveSet.add_3, WF.add_neq_in_iff unfold: PositiveSet.elt, PositiveMap.key.
  - intros H.
    generalize dependent n.
    apply WP.fold_rec_bis; intros.
    + hauto lq: on use: WP.F.In_m, WF.Equal_sym unfold: PositiveMap.key, PositiveMap.Equal, PositiveSet.elt.
    + sauto q: on.
    + destruct (E.eq_dec n k).
      * subst. sfirstorder use: PositiveSet.add_spec, diff_false_true unfold: PositiveMap.key, PositiveSet.elt, PositiveSet.t.
      * hauto use: WF.add_neq_in_iff, PositiveSet.add_2 unfold: PositiveMap.key, PositiveSet.elt.
Qed.

Lemma m_cardinal_s_cardinal: forall A (m : M.t A) s,
    (forall k, M.In k m <-> S.In k s) ->
    M.cardinal m = S.cardinal s.
Proof.
  intros A m s H.
  rewrite WP.cardinal_fold.
  revert s H.
  apply WP.fold_rec_bis.
  - intros m0 m' a H H0 s H1.
    apply H0. intros k. rewrite <- H1. apply WF.In_m; auto.
  - intros s H.
    rewrite SP.cardinal_1. auto.
    unfold S.Empty. intros k.
    specialize (H k).
    rewrite <- H.
    rewrite WF.empty_in_iff.
    scongruence.
  - intros k e a m' H H0 H1 s H2.
    rewrite <- SP.add_remove with (x := k) by (apply H2; rewrite WF.add_in_iff; auto).
    rewrite SP.add_cardinal_2 by (rewrite S.remove_spec; sfirstorder).
    f_equal.
    apply H1.
    intros k0.
    specialize (H2 k0).
    rewrite S.remove_spec.
    rewrite <- H2.
    rewrite WF.add_in_iff.
    sfirstorder.
Qed.

Lemma m_cardinal_domain: forall A (m : M.t A),
    M.cardinal m = S.cardinal (Mdomain m).
Proof.
  intros A m.
  apply m_cardinal_s_cardinal.
  intros k.
  rewrite in_domain.
  hauto lq: on.
Qed.

(* ================================================================= *)
(** * Graph Theory Core Definitions *)

Definition node := E.t.
Definition nodeset := S.t.
Definition nodemap: Type -> Type := M.t.
Definition graph := nodemap nodeset.

Definition adj (g: graph) (i: node) : nodeset :=
  match M.find i g with Some a => a | None => S.empty end.

(** Well-formedness means everything that is in an adjacency set
    exists in the graph itself. *)
Definition well_formed (g: graph) :=
  forall i j, S.In j (adj g i) -> M.In j g.

Definition undirected (g: graph) :=
  forall i j, S.In j (adj g i) -> S.In i (adj g j).

Definition no_selfloop (g: graph) := forall i, ~ S.In i (adj g i).

(** Undirected graphs are well-formed *)
Lemma undirected_well_formed : forall g,
  undirected g -> well_formed g.
Proof.
  intros g Hund i j Hij.
  sauto unfold: undirected, adj.
Qed.

Definition nodes (g: graph) := Mdomain g.

Definition subset_nodes
  (P: node -> nodeset -> bool)
  (g: graph) := Mdomain (WP.filter P g).

Definition low_deg (K: nat) (n: node) (adj: nodeset) : bool := S.cardinal adj <? K.

Definition remove_node (n: node) (g: graph) : graph :=
  M.map (S.remove n) (M.remove n g).

(* ================================================================= *)
(** * Termination lemmas *)

Lemma subset_nodes_sub:  forall P g, S.Subset (subset_nodes P g) (nodes g).
Proof.
  intros P g.
  unfold subset_nodes.
  intros i Hi.
  qauto use: WP.filter_iff, in_domain unfold: nodes.
Qed.

Lemma select_terminates:
  forall (K: nat) (g : graph) (n : S.elt),
    S.choose (subset_nodes (low_deg K) g) = Some n ->
    M.cardinal (remove_node n g) < M.cardinal g.
Proof.
  intros K g n H.
  assert (S.Subset (subset_nodes (low_deg K) g) (nodes g)).
  {
    apply subset_nodes_sub.
  }
  unfold remove_node.
  rewrite cardinal_map.
  apply m_remove_cardinal_less.
  hfcrush use: in_domain, PositiveSet.choose_1 unfold: graph, nodemap, PositiveSet.Subset, nodes.
Qed.

(* ================================================================= *)
(** * Graph coloring algorithm *)
Require Import Recdef.

Function select (K: nat) (g: graph) {measure M.cardinal g}: list node :=
  match S.choose (subset_nodes (low_deg K) g) with
  | Some n => n :: select K (remove_node n g)
  | None => nil
  end.
Proof. apply select_terminates.
Defined.

Definition coloring := M.t node.

Definition colors_of (f: coloring) (s: S.t) : S.t :=
  S.fold (fun n s => match M.find n f with Some c => S.add c s | None => s end) s S.empty.

Definition color1 (palette: S.t) (g: graph) (n: node) (f: coloring) : coloring :=
  match S.choose (S.diff palette (colors_of f (adj g n))) with
  | Some c => M.add n c f
  | None => f
  end.

Definition color (palette: S.t) (g: graph) : coloring :=
  fold_right (color1 palette g)  (M.empty _) (select (S.cardinal palette) g).

(* ================================================================= *)
(** * Correctness specification *)

Definition coloring_ok (palette: S.t) (g: graph) (f: coloring) :=
  forall i j, S.In j (adj g i) ->
         (forall ci, M.find i f = Some ci -> S.In ci palette) /\
           (forall ci cj, M.find i f = Some ci -> M.find j f = Some cj -> ci<>cj).

Lemma adj_ext: forall g i j, E.eq i j -> S.eq (adj g i) (adj g j).
Proof.
  sauto.
Qed.

Lemma in_adj_exists : forall g i j,
    S.In i (adj g j) -> exists v, M.find j g = Some v /\ S.In i v.
Proof.
  intros g i j H.
  unfold adj in *.
  destruct M.find eqn:E in *.
  + eauto.
  + rewrite SP.FM.empty_iff in H. contradiction.
Qed.

Lemma find_in_adj : forall g i v j,
    M.find(A := nodeset) j g = Some v ->
    S.In i v ->
    S.In i (adj g j).
Proof.
  intros g i v j F I.
  unfold adj.
  rewrite F.
  auto.
Qed.

Lemma in_adj_in_nodes : forall g i j,
    S.In i (adj g j) ->
    S.In j (nodes g).
Proof.
  intros g i j.
  unfold adj.
  destruct M.find eqn:E; intros H.
  - unfold nodes.
    rewrite in_domain.
    sfirstorder.
  - rewrite SP.FM.empty_iff in H. contradiction.
Qed.

Lemma adj_map : forall (f : nodeset -> nodeset) g i,
    f S.empty = S.empty ->
    adj (M.map f g) i = f (adj g i).
Proof.
  intros f g i H.
  unfold adj.
  rewrite WF.map_o.
  unfold option_map.
  destruct M.find; auto.
Qed.

Lemma in_colors_of_1:
  forall i s f c, S.In i s -> M.find i f = Some c -> S.In c (colors_of f s).
Proof.
  intros i s f c H H0.
  unfold colors_of.
  rewrite S.fold_1.
  set (F := fun (a : S.t) (e : S.elt) =>
              match M.find e f with
              | Some c0 => S.add c0 a
              | None    => a
              end).
  set (l := S.elements s).
  assert (HinA : InA E.eq i l).
  { sfirstorder use: PositiveSet.elements_1. }
  assert (Hstep : forall l a, InA E.eq i l \/ S.In c a -> S.In c (fold_left F l a)).
  {
    intros l0; induction l0 as [|x l0 IH]; intros a Hdisj.
    - sauto.
    - cbn.
      destruct Hdisj as [Hin|Hacc].
      + inversion Hin; subst.
        * hauto lq: on use: PositiveSet.add_spec, SP.Dec.F.singleton_iff, PositiveSet.In_1 unfold: PositiveSet.elt.
        * sfirstorder.
      + hfcrush use: PositiveSet.add_spec unfold: PositiveSet.elt.
  }
  hauto l: on.
Qed.

Lemma coloring_ok_empty :
  forall palette g,
    coloring_ok palette g (M.empty _).
Proof.
  intros palette g i j Hij; sauto use: WP.F.empty_o.
Qed.

Lemma color1_preserves_ok :
  forall palette g n f,
    undirected g ->
    no_selfloop g ->
    coloring_ok palette g f ->
    coloring_ok palette g (color1 palette g n f).
Proof.
  intros palette g n f Hundir Hnoloop Hok.
  unfold color1.
  destruct (S.choose (S.diff palette (colors_of f (adj g n)))) as [c|] eqn:Hch.
  - (* A color was chosen: add [n -> c] *)
    pose proof (S.choose_1 _ Hch) as Hcin.
    apply S.diff_spec in Hcin. destruct Hcin as [Hc_in_palette Hc_notin_colors].
    intros i j Hij. split.
    + (* palette-membership of any colored vertex *)
      intros ci Hfi.
      rewrite WP.F.add_o in Hfi.
      destruct (E.eq_dec i n) as [->|Hi_ne].
      * hauto q: on.
      * (* unchanged entry, use old invariant *)
        pose proof ((Hok i j Hij)).
        hauto q: on.
    + (* distinct colors across any edge *)
      intros ci cj Hfi Hfj.
      rewrite WP.F.add_o in Hfi.
      rewrite WP.F.add_o in Hfj.
      destruct (E.eq_dec i n) as [->|Hi_ne];
        destruct (E.eq_dec j n) as [->|Hj_ne].
      * (* i = n, j = n: impossible by no self-loop *)
        sfirstorder.
      (* More explicitly: Hij : S.In n (adj g n) contradicts no_selfloop *)
      * (* i = n, j <> n *)
        hauto use: in_colors_of_1 unfold: nodeset, coloring, adj inv: sumbool.
      * (* i <> n, j = n *)
        hfcrush use: in_colors_of_1 unfold: undirected, coloring, nodeset, adj inv: sumbool.
      * (* i <> n, j <> n: both entries unchanged; defer to Hok *)
        eapply (proj2 (Hok i j Hij)); eauto; hauto q: on.
  - (* No color chosen: map unchanged *)
    (* color1 returns f; correctness carries over *)
    qauto l: on.
Qed.

Lemma fold_color_preserves_ok :
  forall palette g l,
    undirected g ->
    no_selfloop g ->
    coloring_ok palette g
      (fold_right (color1 palette g) (M.empty _) l).
Proof.
  intros palette g l Hundir Hnoloop.
  induction l as [|x xs IH].
  - (* base *)
    strivial use: coloring_ok_empty unfold: fold_right.
  - (* step *)
    qauto l: on use: color1_preserves_ok unfold: fold_right, coloring.
Qed.

Theorem color_correct:
  forall palette g,
    no_selfloop g ->
    undirected g ->
    coloring_ok palette g (color palette g).
Proof.
  strivial use: fold_color_preserves_ok unfold: color, select.
Qed.

(* ================================================================= *)
(** * Graph construction utilities *)

Local Open Scope positive.

Definition add_edge (e: (E.t*E.t)) (g: graph) : graph :=
  match e with
  | (u,v) => M.add u (S.add v (adj g u))
              (M.add v (S.add u (adj g v)) g)
  end.

Definition mk_graph (el: list (E.t*E.t)) :=
  fold_right add_edge (M.empty _) el.

Definition empty_graph : graph := (@M.empty _).

(** ** InA to In conversion *)
Lemma inA_iff {A} : forall p (l : list A), (InA Logic.eq p l) <-> In p l.
Proof. induction l; sauto q: on. Qed.

(* ================================================================= *)
(** * Extended map/set/domain lemmas *)

Local Open Scope positive_scope.

Lemma in_nodes_iff g v : S.In v (nodes g) <-> M.In v g.
Proof. unfold nodes; now rewrite in_domain. Qed.

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

Lemma in_adj_center_in_nodes g i j :
  S.In i (adj g j) -> S.In j (nodes g).
Proof.
  rewrite adj_in_iff_find; firstorder using in_nodes_iff.
Qed.

Lemma in_adj_neighbor_in_nodes_wf g i j :
  well_formed g -> S.In i (adj g j) -> S.In i (nodes g).
Proof.
  intros Hwf Hi.
  unfold nodes. rewrite in_domain.
  exact (Hwf j i Hi).
Qed.

Lemma in_adj_neighbor_in_nodes g i j :
  undirected g -> S.In i (adj g j) -> S.In i (nodes g).
Proof.
  intros U Hij. apply U in Hij.
  now apply in_adj_center_in_nodes in Hij.
Qed.

Lemma in_adj_both_in_nodes_wf g i j :
  well_formed g -> S.In i (adj g j) -> S.In i (nodes g) /\ S.In j (nodes g).
Proof.
  intros Hwf Hi. split.
  - eapply in_adj_neighbor_in_nodes_wf; eauto.
  - eapply in_adj_center_in_nodes; eauto.
Qed.

Lemma in_adj_both_in_nodes g i j :
  undirected g -> S.In i (adj g j) -> S.In i (nodes g) /\ S.In j (nodes g).
Proof.
  sfirstorder use: in_adj_center_in_nodes, in_adj_neighbor_in_nodes.
Qed.

Lemma nodes_map_eq f m :
  S.Equal (nodes (M.map f m)) (nodes m).
Proof.
  hfcrush use: in_domain, WF.map_in_iff unfold: PositiveMap.key, PositiveSet.Equal, nodes, PositiveSet.elt.
Qed.

Lemma well_formed_adj_in : forall (g : graph) (v : node) i , well_formed g -> S.In i (adj g v) -> M.In i g.
Proof.
  intros g v i Hwf Hi.
  exact (Hwf v i Hi).
Qed.

Lemma undirected_adj_in : forall (g : graph) (v : node) i , undirected g -> S.In i (adj g v) -> M.In i g.
Proof.
  hauto use: SP.Dec.F.empty_iff unfold: undirected, adj.
Qed.
