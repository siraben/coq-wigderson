(** * complete.v - Complete graphs *)

Require Import graph.
Require Import subgraph.
Require Import List.
Require Import FSets.
Require Import FMaps.
Require Import PArith.
Require Import Psatz.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
Import Arith.
Import ListNotations.
Import Nat.

Local Open Scope nat.

(** * Complete graphs *)

(** A complete [n]-graph is a simple graph with [n] vertices such that
    every vertex is adjacent to every other vertex. *)
Definition complete_graph (n : nat) (g : graph) :=
    M.cardinal g = n /\ no_selfloop g /\ undirected g /\
    forall i j, M.In i g -> M.In j g -> i <> j -> S.In j (adj g i).

Lemma complete_graph_find_iff :
  forall g n v e i,
    complete_graph n g ->
    M.find v g = Some e ->
    S.In i e <-> M.In i g /\ i <> v.
Proof.
  intros g n v e i cmp H0'.
  assert (H4: (forall i j : M.key, M.In i g -> M.In j g -> i <> j -> S.In j (adj g i))) by sfirstorder.
  split.
  - intros H0.
    split.
    + clear -H0' H0 cmp.
      assert (M.In v g) by sfirstorder.
      assert (S.In i (adj g v)) by hauto lq: on unfold: node, PositiveMap.key, PositiveSet.In, adj, PositiveOrderedTypeBits.t.
      sauto lq: on rew: off use: SP.Dec.F.empty_iff unfold: adj, undirected.
    + hauto lq: on unfold: adj, no_selfloop.
  - hfcrush unfold: degree, adj.
Qed.

(** ** Complete graphs have maximum degree [n-1] *)

Local Lemma list_max_constant : forall l n,
    l <> [] -> Forall (fun k => k = n) l -> list_max l = n.
Proof.
  intros l; induction l; sauto.
Qed.

Lemma complete_graph_max_deg : forall n g,
    complete_graph n g -> max_deg g = n - 1.
Proof.
  intros [|n] g Hcomplete.
  - destruct Hcomplete as [Hcard _].
    apply WP.cardinal_Empty in Hcard.
    apply WP.elements_Empty in Hcard.
    unfold max_deg. now rewrite Hcard.
  - assert (Hcard : M.cardinal g = S n) by sfirstorder.
    unfold max_deg.
    apply list_max_constant.
    assert (Hne : ~ M.Empty g) by
      (intro Hempty; apply WP.cardinal_1 in Hempty; lia).
    + destruct (M.elements g) as [| [v e] l] eqn:E.
      * cbn. exfalso. now apply WP.elements_Empty in E.
      * scongruence.
    + apply Forall_forall.
      intros x Hx; apply in_map_iff in Hx as [[v e] [<- He]].
      apply M.elements_complete in He.
      cbn.
      assert (Heq : S.Equal e (S.remove v (Mdomain g))).
      { intro i; rewrite S.remove_spec, in_domain.
        pose proof (complete_graph_find_iff g (S n) v e i Hcomplete He).
        sfirstorder. }
      assert (Hvin : S.In v (Mdomain g)) by
        (apply in_domain; now exists e).
      apply SP.remove_cardinal_1 in Hvin.
      rewrite (SP.Equal_cardinal Heq).
      rewrite m_cardinal_domain in Hcard.
      lia.
Qed.

(** Removing a vertex from a complete graph preserves completeness. *)
Lemma complete_graph_remove_node : forall n g v,
    complete_graph n g ->
    M.In v g ->
    complete_graph (n - 1) (remove_node v g).
Proof.
  intros n g v Hcomplete Hvin.
  destruct Hcomplete as [Hcard [Hloop [Hundir Hadj]]].
  split.
  - unfold remove_node.
    rewrite cardinal_map.
    clear -Hvin Hcard.
    destruct n.
    { apply WP.cardinal_Empty in Hcard; destruct Hvin as [e He].
      exfalso; exact (Hcard v e He). }
    cbn.
    destruct Hvin as [e He].
    assert (Hnotin : ~ M.In v (M.remove v g)) by
      hauto lq: on rew: off use: M.remove_1.
    assert (Hadded : WP.Add v e (M.remove v g) g).
    {
      qauto l: on use: E.eq_dec, M.gss, M.gso, M.gro unfold: WP.Add.
    }
    pose proof (@WP.cardinal_2 _ (M.remove v g) g v e Hnotin Hadded) as Hremove.
    rewrite Hcard in Hremove.
    rewrite Nat.sub_0_r.
    now injection Hremove.
  - split.
    + now apply remove_node_no_selfloop.
    + split.
      * now apply remove_node_undirected.
      * intros i j H5 H6 H7.
        qauto l: on use: remove_node_subgraph, adj_remove_node_spec, subgraph_vertex_in, remove_node_neq2 unfold: node, PositiveOrderedTypeBits.t, PositiveMap.key.
Qed.

(** Adding a fresh universal vertex to a complete graph preserves completeness. *)
Lemma complete_graph_add_node : forall n g v,
    complete_graph n g -> ~ M.In v g
    -> complete_graph (n + 1)
                     (M.add v (S.remove v (Mdomain g)) (M.map (fun e => S.add v e) g)).
Proof.
  intros n g v [H [H0 [H1 H2]]] H3.
  split.
  - (* cardinality *)
    assert (~ M.In v (M.map (fun e : S.t => S.add v e) g)).
    {
      now rewrite WP.F.map_in_iff.
    }
    remember  (M.map (fun e : S.t => S.add v e) g) as g'.
    pose proof (@WP.cardinal_2 S.t g' (M.add v (S.remove v (Mdomain g)) g') v (S.remove v (Mdomain g)) H4 ltac:(sfirstorder)).
    unfold nodeset in *.
    rewrite H5.
    rewrite Heqg'. rewrite cardinal_map. lia.
  - split.
    + (* no selfloop *)
      unfold no_selfloop.
      intros i contra.
      unfold adj in contra.
      destruct (M.find _ _) eqn:E.
      * rewrite PositiveMapAdditionalFacts.gsspec in E.
        destruct (WP.F.eq_dec _ _) eqn:E2.
        ** ssimpl.
           hecrush use: PositiveSet.remove_3, SP.Dec.F.remove_b unfold: PositiveSet.In, andb, nodes, SP.Dec.F.eqb, negb, PositiveMap.key, PositiveSet.elt.
        ** rewrite WF.map_o in E.
           hauto lq: on rew: off use: PositiveSet.add_3, WF.map_o unfold: no_selfloop, nodeset, adj.
      * sauto lq: on.
    + (* undirected *)
      split.
      * unfold undirected.
        intros i j Hij.
        unfold adj in *.
        destruct (WP.F.eq_dec i v), (WP.F.eq_dec j v).
        ** sfirstorder.
        ** hauto qb: on use: PositiveSet.add_1, in_domain, WF.map_o, M.gso, S.remove_3, M.gss unfold: nodeset.
        ** unfold nodeset in *.
           subst.
           rewrite M.gss.
           rewrite M.gso in Hij by auto.
           rewrite WF.map_o in Hij.
           destruct (M.find i g) eqn:E.
           *** unfold nodeset in *. rewrite E in Hij. simpl in Hij.
               apply SP.FM.remove_iff.
               hauto l: on use: in_domain.
           *** unfold nodeset in *. rewrite E in Hij. simpl in Hij. inversion Hij.
        ** rewrite M.gso in * by auto.
           rewrite WF.map_o in *.
           destruct (M.find i g) eqn:E2; destruct (M.find j g) eqn:E3; unfold nodeset in *.
           *** rewrite E3. cbn.
               rewrite SP.FM.add_neq_iff by auto.
               destruct (WP.F.eq_dec i j).
               **** subst. qauto use: SP.Dec.F.empty_iff, PositiveSet.add_3 unfold: PositiveSet.elt, PositiveMap.key, option_map, PositiveSet.empty inv: option.
               **** hfcrush.
           *** rewrite E3. simpl.
               rewrite E2 in Hij.
               cbn in Hij.
               rewrite SP.FM.add_neq_iff in Hij by auto.
               exfalso.
               unfold undirected in H1.
               pose proof (H1 i j).
               sauto q: on unfold: adj, nodeset.
           *** ssimpl.
           *** ssimpl.
      * (* every vertex is adjacent to every other vertex *)
        intros i j H4 H5 H6.
        unfold adj.
        destruct H4 as [e He].
        rewrite He.
        destruct (WP.F.eq_dec j v).
        ** subst.
           destruct H5 as [e' He'].
           unfold M.MapsTo in He'.
           rewrite M.gss in He'.
           unfold M.MapsTo in He.
           rewrite M.gso in He by auto.
           rewrite WF.map_o in He.
           unfold option_map in He.
           destruct (@M.find S.t i g) eqn:E; inversion He.
           strivial use: PositiveSet.add_spec unfold: PositiveMap.key, PositiveSet.elt.
        ** destruct H5 as [e' He'].
           unfold M.MapsTo in He'.
           rewrite M.gso in He' by auto.
           rewrite WF.map_o in He'.
           destruct (M.find j g) eqn: E2.
           *** unfold nodeset in *. rewrite E2 in He'. cbn in He'.
               inversion He'.
               subst.
               destruct (WP.F.eq_dec i v).
               **** hauto q: on use: M.gss, SP.FM.remove_neq_iff, in_domain unfold: M.MapsTo.
               **** unfold M.MapsTo in He.
                 rewrite M.gso in He by auto.
                 rewrite WF.map_o in He.
                 destruct (M.find i g) eqn: E3; unfold nodeset in *; [|sauto q: on].
                 rewrite E3 in He. cbn in He.
                 inversion He.
                 rewrite SP.FM.add_neq_iff by auto.
                 hfcrush unfold: adj, nodeset.
           *** hauto q: on unfold: nodeset.
Qed.
