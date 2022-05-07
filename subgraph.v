Require Import graph.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
Require Import Psatz.
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
- for every vertex v in g', the 
 *)
Definition is_subgraph (g' g : graph) :=
  (S.Subset (nodes g') (nodes g)) /\ (forall v, S.Subset (adj g' v) (adj g v)).

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

(* The (open) neighborhood of a vertex v in a graph consists of the
   subgraph induced by the vertices adjacent to v.  It does not
   include v itself. *)
Definition neighborhood (g : graph) v := remove_node v (subgraph_of g (neighbors g v)).

(* Neighborhoods do not include their vertex *)
Lemma nbd_not_include_vertex g v : M.find v (neighborhood g v) = None.
Proof.
  hecrush use: WF.map_o use: M.grs.
Qed.

Lemma empty_graph_no_vert : forall v, ~ M.In v empty_graph.
Proof. sauto q: on. Qed.

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


(* When is an edge in the induced subgraph?
- if i, j in S and (i,j) in G then (i,j) in G|s
- if (i,j) in G|s then (i,j) in G
- if vertex v in G|s then v in S
- if v in S and v in G then v in G|s
 *)


(* An induced subgraph of an undirected graph is undirected. *)
Lemma subgraph_of_undirected : forall g s, undirected g -> undirected (subgraph_of g s).
Proof.
  intros g s H.
  unfold undirected.
  intros i j Hij.
  assert (S.In j (adj g i)).
  {
    strivial use: subgraph_edges unfold: PositiveSet.Subset.
  }
  assert (S.In i (adj g j)) by sfirstorder.
  pose proof (subgraph_edges g s i).
  (* same issue as before, we need to reason about subgraph_of *)  
  unfold adj in *.
  assert (S.In i s).
  {
    
    admit.
  }
  assert (S.In j s).
  {
    admit.
  }
Admitted.  

Definition remove_subgraph (g : graph) s :=
  M.fold (fun v e m' => if S.mem v s then m' else M.add v (S.diff e s) m') (@M.empty _) g.

Lemma remove_subgraph_is_subgraph : forall g s, is_subgraph (remove_subgraph g s) g.
Proof. split; unfold remove_subgraph; apply WP.fold_rec_bis; scrush. Qed.

(* Removing a subgraph preserves undirectedness *)
Lemma remove_subgraph_undirected : forall g s, undirected g -> undirected (remove_subgraph g s).
Proof. hauto q: on. Qed.

(* Maximum degree of a graph *)
Definition max_deg' (g : graph) := M.fold (fun _ s n => max (S.cardinal s) n) g 0.
Definition max_deg (g : graph) := list_max (map (fun p => S.cardinal (snd p)) (M.elements g)).

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
