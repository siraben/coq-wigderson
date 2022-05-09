Require Import graph.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
Require Import Psatz.
Require Import restrict.
Require Import Program.
Require Import FunInd.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
Import Arith.
Import ListNotations.
Import Nat.

(* The neighbors of a vertex v in a graph g. *)
Definition neighbors (g : graph) v := adj g v.

(* Subgraph induced by a set of vertices *)
Definition subgraph_of (g : graph) (s : S.t) :=
  M.fold (fun v adj g' => if S.mem v s then M.add v (S.inter s adj) g' else g') g empty_graph.

(* g' is a subgraph of g if:
- the vertex set of g' is a subset of the vertex set of g
- the adjacency set of every v in g' is a subset of adjacency set of every v in g
 *)
Definition is_subgraph (g' g : graph) :=
  S.Subset (nodes g') (nodes g) /\ forall v, S.Subset (adj g' v) (adj g v).

Lemma subgraph_refl : forall g, is_subgraph g g.
Proof. sfirstorder. Qed.

Lemma subgraph_trans : forall g g' g'', is_subgraph g g' -> is_subgraph g' g'' -> is_subgraph g g''.
Proof. sfirstorder. Qed.

(* Subgraph vertices are in the original graph, map version *)
Lemma subgraph_vert_m : forall g' g v, is_subgraph g' g -> M.In v g' -> M.In v g.
Proof. qauto l: on use: Sin_domain. Qed.

(* Some lemmas about induced subgraphs. *)
(* The nodes of a subgraph are a subset of the original graph. *)
Lemma subgraph_vertices : forall g s, S.Subset (nodes (subgraph_of g s)) (nodes g).
Proof.
  intros g s.
  unfold subgraph_of.
  apply WP.fold_rec_bis.
  - intros m m' a H H0.
    sauto unfold: M.In, M.MapsTo, nodes, S.Subset use: Sin_domain.
  - sfirstorder.
  - intros k e a m' H H0 H1.
    intros a' Ha'.
    sdestruct (S.mem k s).
    + destruct (E.eq_dec a' k).
      * subst.
        unfold nodes.
        apply Sin_domain.
        hauto lq: on rew: off use: WF.add_in_iff.
      * hauto l: on use: WP.F.add_neq_in_iff, Sin_domain unfold: nodes, S.Subset.
    + apply H1 in Ha'.
      apply Sin_domain.
      apply Sin_domain in Ha'.
      destruct (E.eq_dec a' k); sauto lq: on rew: off use: WP.F.add_neq_in_iff.
Qed.

(* The edges of a subgraph are a subset of the original graph. *)
(* Note this is defined pointwise: the adjacency set is a subset for every vertex. *)
Lemma subgraph_edges : forall g s v,
    S.Subset (adj (subgraph_of g s) v) (adj g v).
Proof.
  intros g s v.
  unfold subgraph_of.
  apply WP.fold_rec_bis.
  - intros m m' a H1 H2.
    unfold adj, nodeset in *.
    unfold nodeset in *.
    hauto drew: off.
  - sfirstorder.
  - intros k e a m' H1 H2 H3.
    (* k is the node we're considering to add to the new subgraph *)
    sdestruct (S.mem k s).
    + (* suppose it's in the set *)
      unfold adj.
      intros a' Ha'.
      destruct (E.eq_dec v k).
      * subst.
        unfold nodeset in *.
        hauto lq: on use: SP.Dec.F.empty_iff, PositiveSet.inter_2, PositiveMap.gss unfold: PositiveSet.empty inv: option.
      * rewrite PositiveMap.gso in *; auto.
    + (* suppose it's not in the set *)
      ssimpl.
      unfold S.Subset in *.
      intros a' Ha'.
      specialize (H3 a').
      unfold adj in *.
      destruct (E.eq_dec v k).
      * fcrush.
      * apply H3 in Ha'.
        assert (M.find v (M.add k e m') = M.find v m').
        {
          hauto lq: on rew: off use: PositiveMap.gso unfold: PositiveSet.elt, PositiveMap.key.
        }
        unfold nodeset in *.
        hauto lq: on.
Qed.

Lemma subgraph_of_is_subgraph : forall g s, is_subgraph (subgraph_of g s) g.
Proof.
  intros g s.
  unfold is_subgraph.
  split; [apply subgraph_vertices|apply subgraph_edges].
Qed.

Lemma remove_node_neq : forall g i j, i <> j -> M.In i g <-> M.In i (remove_node j g).
Proof.
  intros g i j H.
  split; intros H'.
  - apply WF.map_in_iff.
    sauto lq: on use: WP.F.remove_neq_in_iff.
  - unfold remove_node in H'.
    rewrite WF.map_in_iff in H'.
    rewrite WP.F.remove_neq_in_iff in H' by auto.
    assumption.
Qed.

Lemma remove_node_neq2 : forall g i j, M.In i (remove_node j g) -> i <> j.
Proof.
  intros g i j H.
  unfold remove_node in H.
  apply WF.map_in_iff in H.
  destruct (E.eq_dec i j).
  - subst. apply M.remove_1 in H; sfirstorder.
  - assumption.
Qed.

Lemma remove_node_subgraph : forall g v, is_subgraph (remove_node v g) g.
Proof.
  intros g v.
  split.
  - intros i Hi.
    unfold nodes in *.
    apply Sin_domain in Hi.
    apply Sin_domain.
    destruct (E.eq_dec i v).
    * subst. unfold remove_node in Hi.
      rewrite WF.map_in_iff in Hi.
      apply M.remove_1 in Hi; sfirstorder.
    * now apply remove_node_neq in Hi.
  - intros j i Hi.
    unfold adj in *.
    destruct (M.find j (remove_node _ _)) eqn:E.
    + epose proof (remove_node_neq2 g j v ltac:(sfirstorder)).
      assert (M.In j g).
      {
        rewrite (remove_node_neq _ _ v); sfirstorder.
      }
      destruct H0 as [e He].
      unfold M.MapsTo in He.
      rewrite He.
      assert (S.Subset n e).
      {
        intros z Hz.
        unfold remove_node in E.
        assert (M.find j (M.map (S.remove v) g) = Some (S.remove v e)).
        {
          rewrite WF.map_o in E.
          rewrite WF.map_o.
          unfold nodeset in *.
          rewrite He.
          scongruence.
        }
        unfold nodeset, node in *.
        rewrite WF.map_o in H0, E.
        rewrite M.gro in E by auto.
        assert (n = S.remove v e).
        {
          scongruence.
        }
        subst n.
        hauto l: on use: PositiveSet.remove_3 unfold: PositiveOrderedTypeBits.t, PositiveSet.elt.
      }
      sfirstorder.
    + sauto.
Qed.


(* The (open) neighborhood of a vertex v in a graph consists of the
   subgraph induced by the vertices adjacent to v.  It does not
   include v itself. *)
Definition neighborhood (g : graph) v := remove_node v (subgraph_of g (neighbors g v)).

(* Neighborhoods do not include their vertex *)
Lemma nbd_not_include_vertex g v : M.find v (neighborhood g v) = None.
Proof.
  hecrush use: WF.map_o use: M.grs.
Qed.


(* Neighborhood subgraph is a subgraph *)
Lemma nbd_subgraph : forall g i, is_subgraph (neighborhood g i) g.
Proof.
  hauto l: on use: subgraph_of_is_subgraph, remove_node_subgraph, subgraph_trans.
Qed.

Lemma empty_graph_no_vert : forall v, ~ M.In v empty_graph.
Proof. sauto q: on. Qed.

Lemma empty_subgraph_is_subgraph (g : graph) : is_subgraph empty_graph g.
Proof.
  unfold is_subgraph.
  split.
  - hecrush.
  - intros v i Hi.
    unfold adj in Hi.
    unfold empty_graph in Hi.
    ssimpl.
    scongruence use: PositiveMap.gempty unfold: PositiveOrderedTypeBits.t, node, PositiveMap.key.
Qed.

(* The vertices of an induced subgraph is a subset of s. *)
Lemma subgraph_vertices_set : forall g s, S.Subset (nodes (subgraph_of g s)) s.
Proof.
  intros g s.
  unfold subgraph_of.
  apply WP.fold_rec_bis.
  - sauto lq: on.
  - hfcrush.
  - intros k e a m' H H0 H1.
    sdestruct (S.mem k s).
    + unfold nodes.
      unfold nodeset in *.
      intros i' Hi'.
      rewrite Sin_domain in Hi'.
      destruct (E.eq_dec i' k).
      * subst. sauto lq: on.
      * rewrite WP.F.add_neq_in_iff in Hi' by auto.
        rewrite <- Sin_domain in Hi'.
        sfirstorder.
    + assumption.
Qed.

Lemma subgraph_of_nodes : forall g i s, S.In i (nodes (subgraph_of g s)) -> S.In i s.
Proof.
  hauto l: on use: subgraph_vertices_set, subgraph_of_is_subgraph unfold: PositiveMap.key, is_subgraph, PositiveSet.Subset, PositiveSet.elt.
Qed.

(* The adjacency set of any vertex of in an induced subgraph is a subset of s. *)
Lemma subgraph_vertices_adj : forall g s i, S.Subset (adj (subgraph_of g s) i) s.
Proof.
  intros g s i.
  unfold subgraph_of.
  apply WP.fold_rec_bis.
  - sfirstorder.
  - unfold adj.
    hecrush use: empty_graph_no_vert.
  - intros k e a m' H H0 H1.
    sdestruct (S.mem k s).
    + unfold adj, nodeset in *.
      destruct (E.eq_dec i k).
      * subst.
        hauto use: PositiveMap.gss, SP.Dec.F.empty_iff, SP.Dec.F.inter_iff unfold: PositiveSet.Subset inv: option.
      * hauto use: SP.subset_empty, PositiveMap.gso unfold: PositiveSet.Subset, PositiveSet.empty, node, PositiveOrderedTypeBits.t, PositiveMap.key inv: option.
    + assumption.
Qed.

(* If a vertex j is in the neighborhood of i then j is in i's adjacency set. *)
Lemma nbd_adj : forall g i j, S.In j (nodes (neighborhood g i)) -> S.In j (adj g i).
Proof.
  intros g i j H.
  unfold neighborhood in H.
  unfold neighbors in H.
  remember (adj g i) as s.
  apply subgraph_of_nodes with (g := g).
  destruct (E.eq_dec j i).
  - hauto lq: on use: Sin_domain, remove_node_neq2 unfold: nodes.
  - hauto lq: on use: Sin_domain, remove_node_neq unfold: nodes.
Qed.

(* When is an edge in the induced subgraph?
- if i, j in S and (i,j) in G then (i,j) in G|s
- if (i,j) in G|s then (i,j) in G
- if vertex v in G|s then v in S
- if v in S and v in G then v in G|s
 *)

(* Remove a set of vertices from a graph. *)
(* For proving:
- first restrict the graph by (S.diff (Mdomain g) s)
- then map subtracting s from every adj set
 *)
Definition remove_nodes (g : graph) (s : nodeset) :=
  M.map (fun ve => S.diff ve s) (restrict g (S.diff (nodes g) s)).
(* Removing nodes from the subgraph is a subgraph. *)
Lemma remove_nodes_is_subgraph : forall g s, is_subgraph (remove_nodes g s) g.
Proof.
  intros g s.
  unfold remove_nodes.
  split.
  - unfold nodes.
    intros i Hi.
    rewrite Sin_domain in *.
    assert (M.In i (restrict g (S.diff (Mdomain g) s))).
    {
      rewrite WF.map_in_iff in Hi.
      assumption.
    }
    apply restrict_incl in H.
    assumption.
  - intros v i Hi.
    unfold adj in *.
    destruct (M.find v (M.map _ _)) eqn:E.
    + destruct (M.find v g) eqn:E2.
      * rewrite WF.map_o in E.
        destruct (M.find _ (restrict _ _)) eqn:E3; [|scongruence].
        simpl in E.
        unfold nodeset in *.
        apply restrict_agree in E3.
        hauto use: PositiveSet.diff_1.
      * exfalso.
        rewrite WF.map_o in E.
        destruct (M.find _ (restrict _ _)) eqn:E3; [|scongruence].
        apply restrict_agree in E3.
        unfold nodeset in *.
        hauto l: on.
    + sauto.
Qed.

Lemma remove_nodes_sub : forall g s i, S.In i s -> M.In i g -> ~ M.In i (remove_nodes g s).
Proof.
  intros g s i H H0 contra.
  unfold nodeset in *.
  unfold remove_nodes in contra.
  rewrite WF.map_in_iff in contra.
  unfold nodes.
  destruct contra as [e He].
  unfold M.MapsTo in He.
  apply restrict_in_set in He.
  unfold nodes in He.
  apply Sin_domain in H0.
  hauto l: on use: S.diff_spec.
Qed.

(* Removing a subgraph *)
Lemma remove_nodes_lt : forall g s i, S.In i s -> M.In i g -> (M.cardinal (remove_nodes g s) < M.cardinal g)%nat.
Proof.
  intros g s i H H0.
  pose proof (remove_nodes_sub g s i H H0).
  unfold remove_nodes.
  rewrite cardinal_map.
  admit.
Admitted.
  
(* Removing a subgraph preserves undirectedness *)
Lemma remove_nodes_undirected : forall g s, undirected g -> undirected (remove_nodes g s).
Proof. Admitted.

(* Maximum degree of a graph *)
Definition max_deg' (g : graph) := M.fold (fun _ s n => max (S.cardinal s) n) g 0.
Definition max_deg (g : graph) := list_max (map (fun p => S.cardinal (snd p)) (M.elements g)).

Lemma max_deg_empty : max_deg (@M.empty _) = 0.
Proof. sfirstorder. Qed.

Lemma inl_in i l : S.InL i l <-> In i l.
Proof.
  split; induction l; sauto lq: on.
Qed.

Lemma incl_subset s s' : S.Subset s s' -> incl (S.elements s) (S.elements s').
Proof.
  intros H i Hi.
  unfold S.elt in i.
  pose proof (S.elements_2 s ltac:(hauto l: on use: inl_in)).
  rewrite <- inl_in.
  sfirstorder use: PositiveSet.elements_1 unfold: PositiveSet.elt.
Qed.

(* Maximum degree is maximum *)
Lemma max_deg_max : forall g v e, M.find v g = Some e -> S.cardinal e <= max_deg g.
Proof.
  intros g v e H.
  pose proof (M.elements_correct g v H).
  pose proof list_max_le.
  unfold max_deg.
  assert (In e (map snd (M.elements g))) by (exact (in_map snd _ _ H0)).
  rewrite <- map_map.
  pose proof (proj1 (H1 (map S.cardinal (map snd (M.elements g))) (list_max (map S.cardinal (map snd (M.elements g))))) (@le_refl _)).
  assert (In (S.cardinal e) (map S.cardinal (map snd (M.elements g)))).
  {
    hauto l: on use: in_map.
  }
  rewrite Forall_forall in H3.
  specialize (H3 (S.cardinal e)).
  sfirstorder.
Qed.

Lemma list_max_witness : forall l n, l <> [] -> list_max l = n -> {x | In x l /\ x = n}.
Proof.
  intros l n.
  induction l.
  - scongruence.
  - intros H H0.
    clear H.
    replace (a :: l) with ([a] ++ l) in H0 by reflexivity.
    rewrite list_max_app in H0.
    destruct (max_dec (list_max [a]) (list_max l)); sauto lq: on.
Defined.

(* We can extract a vertex of maximum degree in an non-graph *)
Lemma max_degree_vert : forall g n, ~ M.Empty g -> max_deg g = n -> exists v, M.In v g /\ S.cardinal (adj g v) = n.
Proof.
  intros g n H H1.
  unfold max_deg in H1.
  apply list_max_witness in H1.
  - destruct H1 as [x [Hx]].
    subst.
    apply in_map_iff in Hx.
    destruct Hx as [[v ve] [Hx]].
    exists v.
    split.
    + exists ve.
      hauto lq: on use: M.elements_complete.
    + unfold adj.
      apply M.elements_complete in H0.
      sauto lq: on.
  - sauto lq: on rew: off use: map_eq_nil, WP.elements_Empty inv: list.
Qed.

(* TODO: can be done as a direct proof *)
Lemma max_deg_subgraph : forall (g g' : graph), is_subgraph g' g -> max_deg g' <= max_deg g.
Proof.
  intros g g' H.
  unfold max_deg.
  unfold is_subgraph in H.
  pose proof incl_Forall_in_iff.
  (* use contradiction *)
  apply le_ngt.
  intros HH.
  (* let d be the max degree of the original graph *)
  remember (list_max (map (fun p : M.key * S.t => S.cardinal (snd p)) (M.elements g))) as d.
  (* let d' be the max degree of subgraph *)
  remember (list_max (map (fun p : M.key * S.t => S.cardinal (snd p)) (M.elements g'))) as d'.
  (* there is a vertex v in g' that has degree d' *)
  assert (exists v, M.In v g' /\ S.cardinal (adj g' v) = d').
  {
    (* to do this, we can extract the witness by first showing that g' is non-empty *)
    destruct (M.elements g') eqn:Mg; [sauto lq: on|].
    (* hence the witness is realized *)
    destruct (list_max_witness (map (fun p : M.key * S.t => S.cardinal (snd p)) (p :: l)) d' ltac:(scongruence) (eq_sym Heqd')) as [x [Hx xmax]].
    subst x.
    apply in_map_iff in Hx.
    destruct Hx as [[v ve] [Hv]].
    assert (M.In v g').
    {
      hauto l: on use: M.elements_complete.
    }
    rewrite <- Mg in H1.
    exists v.
    assert (M.In v g') by (sauto lq: on use: M.elements_2).
    ssimpl.
    unfold adj.
    rewrite H6.
    assert (M.In v g') by sfirstorder.
    assert (M.MapsTo v ve g') by (sauto lq: on rew: off use: M.elements_complete).
    scongruence unfold: M.MapsTo, nodeset.
  }
  destruct H1 as [v [Hv Hv']].
  (* hence v must exist in g *)
  assert (M.In v g) by (hauto lq: on rew: off use: subgraph_vert_m).
  (* let ve' be the adjacency set of v in g' *)
  remember (adj g' v) as ve'.
  (* let ve be the adjacency set of v in g *)
  destruct H1 as [ve Hve].
  (* ve' is a subset of ve *)
  assert (S.Subset ve' ve).
  {
    qauto unfold: PositiveMap.MapsTo, node, PositiveMap.key, PositiveSet.Subset, adj, PositiveOrderedTypeBits.t.
  }
  pose proof (proj2 H v).
  pose proof (SP.subset_cardinal H2).
  (* let c be the degree of v in g *)
  remember (S.cardinal (adj g v)) as c.
  (* recall that d is the max degree of g, so c <= d *)
  assert (c <= d).
  {
    pose proof (max_deg_max g v ve ltac:(sfirstorder)).
    unfold max_deg in H4.
    rewrite <- Heqd in H4.
    unfold adj in Heqc.
    ssimpl.
  }
  (* but then d' <= c *)
  assert (d' <= c) by scongruence.
  (* but this is a contradiction since we have d < d' <= c < d *)
  lia.
Qed.

(* Degree of a vertex *)
Definition degree (g : graph) (v : node) := S.cardinal (adj g v).

Lemma degree_gt_0_in (g : graph) (v : node) :
  degree g v > 0 -> M.In v g.
Proof.
  sauto unfold: degree, adj.
Qed.

(* If the max degree of a graph is 0 then every pair of vertices is not adjacent. *)
Lemma max_deg_0_adj (g : graph) i j : max_deg g = 0 -> ~ S.In i (adj g j).
Proof.
  intros H contra.
  assert (M.In j g).
  {
    hfcrush use: SP.remove_cardinal_1, neq_0_lt, degree_gt_0_in, SP.Dec.F.empty_iff unfold: PositiveSet.empty, PositiveSet.In, adj, gt, degree, nodeset.
  }
  destruct H0 as [e He].
  unfold adj in contra.
  unfold M.MapsTo in He.
  rewrite He in contra.
  pose proof (max_deg_max g j e ltac:(sfirstorder)).
  hauto use: SP.cardinal_inv_1 unfold: nodeset, PositiveSet.Empty inv: Peano.le.
Qed.
  
Lemma max_deg_gt_not_empty (g : graph) : max_deg g > 0 -> ~ M.Empty g.
Proof.
  intros H contra.
  pose proof max_deg_empty.
  unfold max_deg in H.
  apply (WP.elements_Empty g) in contra.
  sauto q: on.
Qed.

(* If a graph has a maximum degree of greater than 0 then there is a witness *)
(* Stronger than max_degree_vert *)

(* If a vertex is removed from the graph, all of its neighbors have
   reduced degree. *)
Lemma vertex_removed_nbs_dec : forall (g : graph) (i j : node) n,
    undirected g ->
    no_selfloop g ->
    M.In i g ->
    S.In j (adj g i) ->
    degree g j = S n ->
    degree (remove_node i g) j = n.
Proof.
  intros g i j n H Hl H0 H1 H2.
  assert (S.In i (adj g j)) by sfirstorder.
  unfold degree in *.
  (* the adjacency set of j in the new graph has i removed *)
  assert (S.Equal (adj (remove_node i g) j) (S.remove i (adj g j))).
  {
    unfold remove_node.
    unfold adj in H3.
    unfold adj.
    destruct (M.find j g) eqn:E; [|sauto q:on].
    rewrite WF.map_o.
    destruct (E.eq_dec i j); [scongruence|].
    rewrite M.gro by auto.
    rewrite E.
    reflexivity.
  }
  hauto use: SP.Equal_cardinal, SP.remove_cardinal_1 unfold: degree, adj, PositiveSet.elt, nodeset, PositiveOrderedTypeBits.t, node.
Qed.

Definition extract_deg_vert (g : graph) (d : nat) :=
  find (fun p => Nat.eqb (S.cardinal (snd p)) d) (M.elements g).

Lemma InA_in_iff {A} : forall p (l : list (M.key * A)), (InA (@M.eq_key_elt A) p l) <-> In p l.
Proof. induction l; sauto q: on. Qed.

(* Extract a degree of vertex d in a graph or fail *)
Lemma extract_deg_vert_dec : forall (g : graph) (d : nat),
    {v | M.In v g /\ degree g v = d} + ~ exists v, M.In v g /\ degree g v = d.
Proof.
  intros g d.
  destruct (extract_deg_vert g d) eqn:E.
  - destruct p as [v k].
    left. exists v.
    unfold extract_deg_vert in E.
    pose proof (find_some _ _ E).
    unfold degree.
    unfold adj.
    destruct H.
    assert (InA (@M.eq_key_elt _) (v,k) (M.elements g)).
    {
      now apply InA_in_iff.
    }
    apply WF.elements_mapsto_iff in H1.
    split; [exists k; sfirstorder|].
    destruct (M.find v g) eqn:E2.
    + apply eqb_eq in H0.
      scongruence.
    + sfirstorder.
  - right.
    intros contra.
    destruct contra as [v e].
    unfold degree in e.
    unfold extract_deg_vert in E.
    unfold adj in e.
    destruct (M.find v g) eqn:E2.
    + assert (In (v,n) (M.elements g)).
      {
        apply InA_in_iff.
        apply WF.elements_mapsto_iff.
        sfirstorder.
      }
      pose proof (find_none _ _ E _ H).
      simpl in H0.
      hauto lb: on.
    + sfirstorder.
Defined.

(* Extract vertices of a given degree in a graph, removing it from the
   graph each time. *)
Function extract_vertices_deg (g : graph) (d : nat) {measure M.cardinal g} : list (node * graph) * graph :=
  match extract_deg_vert_dec g d with
  | inl v =>
      let (l, g') := extract_vertices_deg (remove_node (`v) g) d in
      ((`v, g') :: l, g')
  | inr _ => (nil, g)
  end.
Proof.
  intros g d v teq.
  destruct v as [v Hv].
  simpl.
  unfold remove_node.
  rewrite cardinal_map.
  hauto lq: on rew: off use: Mremove_cardinal_less.
Defined.

Functional Scheme extract_vertices_deg_ind := Induction for extract_vertices_deg Sort Prop.

Lemma extract_vertices_deg_exhaust (g : graph) n :
  n > 0 -> ~ exists v, degree (snd (extract_vertices_deg g n)) v = n.
Proof.
  functional induction (extract_vertices_deg g n) using extract_vertices_deg_ind.
  - qauto l: on.
  - intros dgt0 contra.
    destruct d; [sauto q:on|].
    simpl in *.
    destruct contra as [v ve].
    sauto lq: on use: degree_gt_0_in.
Qed.

(* If a vertex occurs in *)
(* Lemma extract_vertices_correct (g : graph) n v : In v (fst (extract_vertices_deg g n)) -> degree g v >= n . *)
(* Proof. *)
(*   split. *)
(*   - intros. *)
(*     admit. *)
(*   - functional induction (extract_vertices_deg g n). *)
(*     + hammer. *)
Lemma extract_vertices_deg_subgraph (g : graph) n :
  is_subgraph (snd (extract_vertices_deg g n)) g. 
Proof.
  functional induction (extract_vertices_deg g n) using extract_vertices_deg_ind.
  - simpl.
    rewrite e0 in IHp.
    simpl in IHp.
    pose proof (remove_node_subgraph g (` v)).
    hauto l: on use: subgraph_trans.
  - apply subgraph_refl.
Qed.

Lemma extract_vertices_max_deg (g : graph) :
   max_deg g > 0 -> max_deg (snd (extract_vertices_deg g (max_deg g))) < max_deg g.
Proof.
  intros H.
  pose proof (extract_vertices_deg_exhaust g _ H).
  pose proof (extract_vertices_deg_subgraph g (max_deg g)).
  remember (extract_vertices_deg g (max_deg g)) as g'.
  pose proof (max_deg_subgraph g (snd g') H1).
  apply le_lt_or_eq in H2.
  destruct H2.
  - assumption.
  - exfalso.    
    (* want to get a contradiction because we ran out of vertices of
       max degree *)
    pose proof (max_deg_gt_not_empty _ H).
    assert (~ M.Empty (snd g')).
    {
      rewrite <- H2 in H.
      apply max_deg_gt_not_empty.
      assumption.
    }
    epose proof (max_degree_vert _ (max_deg g) H4 H2).
    hauto lq: on rew: off.
Qed.

(* If a vertex of max degree is removed from a graph then any vertex
   with max degree in the new graph cannot be adjacent to it. *)
Lemma remove_max_deg_adj : forall (g : graph) (i j : node) (d : nat),
    (d > 0)%nat ->
    undirected g ->
    no_selfloop g ->
    max_deg g = d ->
    M.In i g ->
    M.In j g ->
    degree g j = d ->
    degree (remove_node i g) j = d ->
    ~ (S.In j (adj g i)).
Proof.
  intros g i j d H H0 H1 H2 H3 H4 H5 H6 contra.
  destruct d; [inversion H|clear H].
  assert (degree (remove_node i g) j = d) by (now apply vertex_removed_nbs_dec).
  qauto use: le_ngt, le_refl unfold: Peano.lt.
Qed.


(* If two vertices i, j occur in the list of max degree vertices
   extracted from the graph, then i is not adjacent to j
 *)
Lemma extract_vertices_deg_not_adj (g : graph) (d : nat) i j :
  i <> j ->
  d = max_deg g ->
  undirected g ->
  no_selfloop g ->
  In i (map fst (fst (extract_vertices_deg g d))) ->
  In j (map fst (fst (extract_vertices_deg g d))) ->
  ~ S.In j (adj g i).
Proof.
  intros H H0 H1 H2 H3 H4 contra.
  (* assume they are adjacent *)
  (* but one of them was extracted first *)
  (* *)
Admitted.
