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
Require Import Decidable.
Require Import FExt.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
Import Arith.
Import ListNotations.
Import Nat.

Local Open Scope nat.

(** * Properties of subgraphs and degrees *)

(** ** Subgraph predicate
 [g'] is a subgraph of [g] if:
- the vertex set of [g'] is a subset of the vertex set of [g]
- the adjacency set of every [v] in [g'] is a subset of adjacency set of every [v] in [g]
 *)
Definition is_subgraph (g' g : graph) :=
  S.Subset (nodes g') (nodes g) /\ forall v, S.Subset (adj g' v) (adj g v).

(** ** Subgraph relation is reflexive *)
Lemma subgraph_refl : forall g, is_subgraph g g.
Proof. sfirstorder. Qed.

(** ** Subgraph relation is transitive *)

Lemma subgraph_trans : forall g g' g'', is_subgraph g g' -> is_subgraph g' g'' -> is_subgraph g g''.
Proof. sfirstorder. Qed.

(** ** Subgraphs preserve irreflexivity *)
Lemma subgraph_no_selfloop : forall g' g, is_subgraph g' g -> no_selfloop g -> no_selfloop g'.
Proof. sfirstorder. Qed.

(** ** Vertices in the subgraph are in original graph *)

Lemma subgraph_vert_m : forall g' g v, is_subgraph g' g -> M.In v g' -> M.In v g.
Proof. qauto l: on use: Sin_domain. Qed.

Lemma is_subgraph_nodes_subset g' g :
  is_subgraph g' g -> S.Subset (nodes g') (nodes g).
Proof. firstorder. Qed.

Lemma is_subgraph_edge_mono g' g :
  is_subgraph g' g -> forall v, S.Subset (adj g' v) (adj g v).
Proof. firstorder. Qed.

(** ** Empty graph is a subgraph *)

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

(** * Induced subgraphs *)

(** ** An induced subgraph of [g] under [s] is the restriction of [g] to [s] and all the outgoing edges only allowed to be pointed to vertices in [s]. *)
Definition subgraph_of (g : graph) (s : S.t) :=
  M.map (fun adj => S.inter s adj) (restrict g s).

(** ** Adjacency in an induced subgraph *)
Lemma adj_subgraph_of_spec :
  forall g s i j,
    S.In i (adj (subgraph_of g s) j)
    <-> S.In i (adj g j) /\ S.In i s /\ S.In j s.
Proof.
  intros g s i j.
  unfold subgraph_of.
  (* Push through the map on values *)
  rewrite adj_map; [|sauto].
  (* Now characterize adjacency after key restriction *)
  rewrite S.inter_spec.
  rewrite adj_restrict.
  hauto l: on.
Qed.


(** ** If [i] is in the induced subgraph then i is in the set of inducing  vertices. *)
Lemma subgraph_of_nodes : forall g i s, S.In i (nodes (subgraph_of g s)) -> S.In i s.
Proof.
  intros g i s H.
  unfold subgraph_of in H.
  rewrite nodes_map_eq, nodes_restrict_eq in H.
  apply S.inter_spec in H; tauto.
Qed.

(** ** Nodes of an induced subgraph are a subset of the original graph *)
Lemma subgraph_vertices : forall g s, S.Subset (nodes (subgraph_of g s)) (nodes g).
Proof.
  intros g i s H.
  unfold subgraph_of in H.
  rewrite nodes_map_eq, nodes_restrict_eq in H.
  apply S.inter_spec in H; tauto.
Qed.


(** ** Edges of an induced subgraph are a subset of the original graph *)
(** Note that this is defined pointwise: the adjacency set is a subset
    for every vertex. *)

Lemma subgraph_edges : forall g s v,
    S.Subset (adj (subgraph_of g s) v) (adj g v).
Proof.
  intros g s v.
  strivial use: adj_subgraph_of_spec unfold: PositiveSet.Subset.
Qed.

(** ** Induced subgraph is subgraph *)

Lemma subgraph_of_is_subgraph : forall g s, is_subgraph (subgraph_of g s) g.
Proof.
  unfold is_subgraph.
  split; [apply subgraph_vertices|apply subgraph_edges].
Qed.

(** * Removal of nodes *)
(** ** Removing a distinct vertex from a graph *)
(** If [i] and [j] are distinct vertices then removing [j] from the
    graph doesn't affect [i]'s membership. *)

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

(** If [i] is in the graph with [j] removed then [i] is not equal to [j]. *)

Lemma remove_node_neq2 : forall g i j, M.In i (remove_node j g) -> i <> j.
Proof.
  intros g i j H.
  unfold remove_node in H.
  apply WF.map_in_iff in H.
  destruct (E.eq_dec i j).
  - subst. apply M.remove_1 in H; sfirstorder.
  - assumption.
Qed.

(** ** Removing a node *)
Lemma remove_node_not_in : forall g g' v,
    is_subgraph g' (remove_node v g) -> ~ M.In v g'.
Proof.
  intros g g' v H.
  hauto lq: on use: remove_node_neq2, subgraph_vert_m unfold: node.
Qed.

(** ** Remove a set of vertices from a graph *)
(** To make it easier to prove things about it,
- first restrict the graph by [S.diff (Mdomain g) s]
- then map subtracting s from every adj set
 *)
Definition remove_nodes (g : graph) (s : nodeset) :=
  M.map (fun ve => S.diff ve s) (restrict g (S.diff (nodes g) s)).

Lemma nodes_remove_nodes_eq g s :
  S.Equal (nodes (remove_nodes g s)) (S.diff (nodes g) s).
Proof.
  unfold remove_nodes.
  rewrite nodes_map_eq, nodes_restrict_eq.
  hfcrush use: PositiveSet.diff_1, PositiveSet.inter_spec, PositiveSet.inter_3 unfold: PositiveSet.Equal, nodeset.
Qed.
  

(** ** Removing a node results in a subgraph *)

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


Lemma in_remove_nodes_iff g s w :
  M.In w (remove_nodes g s) <-> M.In w g /\ ~ S.In w s.
Proof.
  rewrite <- !in_nodes_iff.
  hfcrush use: PositiveSet.diff_1, PositiveSet.diff_3, PositiveSet.diff_2, nodes_remove_nodes_eq unfold: PositiveMap.key, nodeset, PositiveSet.Equal, PositiveSet.elt.
Qed.

Lemma in_remove_node_iff g v w :
  M.In w (remove_node v g) <-> M.In w g /\ w <> v.
Proof.
  hauto lq: on use: in_nodes_iff, remove_node_neq2, remove_node_neq unfold: PositiveOrderedTypeBits.t, graph, node, nodemap, PositiveSet.elt, PositiveMap.key.
Qed.

(** ** Removing nodes results in a subgraph *)
Lemma remove_nodes_subgraph : forall g s, is_subgraph (remove_nodes g s) g.
Proof.
  intros g s.
  unfold remove_nodes.
  split.
  - unfold nodes.
    intros i Hi.
    now rewrite nodes_map_eq, nodes_restrict_eq, S.inter_spec in Hi.
  - intros v i Hi.
    rewrite adj_map in Hi; [|sfirstorder].
    now rewrite S.diff_spec, adj_restrict in Hi.
Qed.

(** ** Every vertex in the removing set is not in the resulting graph *)

Lemma remove_nodes_sub : forall g s i, S.In i s -> M.In i g -> ~ M.In i (remove_nodes g s).
Proof.
  hauto l: on use: in_remove_nodes_iff.
Qed.

(** ** Removing a non-empty set of vertices decreases the size of the graph *)

Lemma remove_nodes_lt : forall g s i, S.In i s -> M.In i g -> (M.cardinal (remove_nodes g s) < M.cardinal g).
Proof.
  intros g s i H H0.
  rewrite !Mcardinal_domain, nodes_remove_nodes_eq.
  apply SP.subset_cardinal_lt with (x := i).
  - apply SP.diff_subset.
  - rewrite in_nodes_iff. assumption.
  - sfirstorder use: S.diff_spec.
Qed.

(** ** Specification of adjacency after removing nodes *)
Lemma adj_remove_nodes_spec : forall g s i j,
    S.In i (adj (remove_nodes g s) j) <-> S.In i (adj g j) /\ ~ S.In i s /\ ~ S.In j s.
Proof.
  intros g s i j.
  unfold remove_nodes.
  rewrite adj_map by hauto lq: on.
  rewrite S.diff_spec.
  rewrite adj_restrict.
  rewrite S.diff_spec.
  firstorder.
  eauto using in_adj_in_nodes.
Qed.

(** ** Equivalence of removing a single node and a singleton set of nodes*)
Lemma remove_nodes_singleton : forall g v, M.Equiv S.Equal (remove_nodes g (S.singleton v)) (remove_node v g).
Proof.
  intros g v.
  split.
  - intros k.
    unfold remove_node, remove_nodes.
    rewrite !WF.map_in_iff.
    unfold nodes.
    rewrite restrict_spec, S.diff_spec.
    split; intros H.
    + assert (k <> v) by sfirstorder use: PositiveSet.singleton_2.
      sauto lq: on use: WF.remove_neq_in_iff.
    + assert (k <> v) by hauto lq: on use: WF.remove_in_iff.
      split.
      * sauto lq: on use: WF.remove_neq_in_iff.
      * split.
        ** hauto l: on use: Sin_domain, WF.remove_neq_in_iff.
        ** sfirstorder use: SP.Dec.F.singleton_iff unfold: PositiveSet.elt, PositiveMap.key.
  - intros k e e' H H0.
    unfold remove_node, remove_nodes, M.MapsTo in *.
    rewrite WF.map_o in *.
    destruct (E.eq_dec k v).
    + subst.
      rewrite M.grs in H0.
      inversion H0.
    + rewrite M.gro in H0 by auto.
      destruct (M.find k g) eqn:E.
      * simpl in H0.
        assert (S.In v (S.singleton v)) by sfirstorder use: PositiveSet.singleton_2.
        destruct (M.find k (restrict g (S.diff (nodes g) (S.singleton v)))) eqn:E2.
        ** unfold nodeset in *.
           rewrite E2 in H.
           simpl in H.
           inversion H.
           clear H.
           rewrite <- restrict_agree_2 in E2.
           *** hauto use: SP.remove_diff_singleton unfold: PositiveSet.Equal.
           *** rewrite S.diff_spec.
               split.
               **** unfold nodes.
                    apply Sin_domain.
                    sfirstorder.
               **** intros contra.
                    sfirstorder use: PositiveSet.singleton_1 unfold: PositiveSet.elt, PositiveMap.key.
        ** unfold nodeset in *.
           hauto q: on.
      * inversion H0.
Qed.

Lemma nodes_remove_node_eq g v :
  S.Equal (nodes (remove_node v g)) (S.diff (nodes g) (S.singleton v)).
Proof.
  unfold remove_node.
  rewrite <- SP.remove_diff_singleton.
  rewrite nodes_map_eq.
  unfold nodes.
  unfold S.Equal.
  intros a.
  rewrite Sin_domain.
  rewrite WF.remove_in_iff.
  rewrite S.remove_spec.
  rewrite Sin_domain.
  tauto.
Qed.

(** ** Adjacency after removing a single node or a singleton set of nodes *)
Lemma remove_node_nodes_adj : forall g i v,
    S.Equal (adj (remove_nodes g (S.singleton v)) i) (adj (remove_node v g) i).
Proof.
  intros g i v.
  pose proof (remove_nodes_singleton g v).
  remember (remove_nodes g (S.singleton v)) as m1.
  remember (remove_node v g) as m2.
  destruct H as [H1 H2].
  unfold adj.
  destruct (M.find i m1) eqn:E1, (M.find i m2) eqn:E2; unfold nodeset in *; sauto.
Qed.

Lemma remove_nodes_monotone g s1 s2 :
  S.Subset s1 s2 -> is_subgraph (remove_nodes g s2) (remove_nodes g s1).
Proof.
  intros H.
  split.
  - unfold remove_nodes.
    intros i Hi.
    apply Sin_domain.
    apply Sin_domain in Hi.
    rewrite WP.F.map_in_iff in *.
    rewrite restrict_spec in *.
    hfcrush use: PositiveSet.diff_1, PositiveSet.diff_2, PositiveSet.diff_3 unfold: PositiveSet.Subset.
  - intros v e He.
    apply adj_remove_nodes_spec.
    apply adj_remove_nodes_spec in He.
    sfirstorder.
Qed.

(** ** Specification of adjacency after removing a single node *)
Lemma adj_remove_node_spec : forall g v i j,
    S.In i (adj (remove_node v g) j) <-> S.In i (adj g j) /\ i <> v /\ j <> v.
Proof.
  intros g s i j.
  rewrite <- remove_node_nodes_adj.
  rewrite adj_remove_nodes_spec.
  sfirstorder use: SP.Dec.F.singleton_iff, PositiveSet.singleton_1 unfold: PositiveOrderedTypeBits.t, PositiveSet.elt, node.
Qed.

(** ** Removing nodes removes it from the  graph*)
Lemma remove_nodes_remove : forall g s i, S.In i s -> ~ M.In i (remove_nodes g s).
Proof.
  strivial use: in_remove_nodes_iff.
Qed.

(** ** Removing a subgraph preserves undirectedness *)

Lemma remove_nodes_undirected : forall g s, undirected g -> undirected (remove_nodes g s).
Proof.
  hauto l: on use: adj_remove_nodes_spec unfold: undirected.
Qed.

(** ** Removing a subgraph preserves irreflexivity *)

Lemma remove_nodes_no_selfloop : forall g s, no_selfloop g -> no_selfloop (remove_nodes g s).
Proof.
  hauto l: on use: adj_remove_nodes_spec unfold: no_selfloop.
Qed.

(** ** Removing a node preserves undirectedness *)

Lemma remove_node_undirected : forall g i, undirected g -> undirected (remove_node i g).
Proof.
  hauto use: adj_remove_node_spec unfold: undirected.
Qed.

(** ** Removing a node preserves irreflexivity *)

Lemma remove_node_no_selfloop : forall g i, no_selfloop g -> no_selfloop (remove_node i g).
Proof.
  hauto l: on use: subgraph_no_selfloop, remove_node_subgraph.
Qed.

(** * Neighborhood of a vertex *)
(** ** Definition of neighbors *)

Definition neighbors (g : graph) v := adj g v.

(** ** Definition of neighborhood*)
(** The (open) neighborhood of a vertex v in a graph consists of the
    subgraph induced by the vertices adjacent to v.  It does not
    include v itself. *)

Definition neighborhood (g : graph) v := remove_node v (subgraph_of g (neighbors g v)).

(** ** Neighborhoods do not include the vertex *)

Lemma nbd_not_include_vertex g v : M.find v (neighborhood g v) = None.
Proof.
  hecrush use: WF.map_o use: M.grs.
Qed.

(** ** Neighborhood is a subgraph *)

Lemma nbd_subgraph : forall g i, is_subgraph (neighborhood g i) g.
Proof.
  hauto l: on use: subgraph_of_is_subgraph, remove_node_subgraph, subgraph_trans.
Qed.

(** ** The adjacency set of any vertex of in an induced subgraph is a subset of the vertex set  *)
Lemma subgraph_vertices_adj : forall g s i, S.Subset (adj (subgraph_of g s) i) s.
Proof.
  strivial use: adj_subgraph_of_spec unfold: PositiveSet.Subset.
Qed.

(** ** In neighborhood implies in adjacency set *)

Lemma nbd_adj : forall g i, S.Subset (nodes (neighborhood g i)) (adj g i).
Proof.
  unfold S.Subset.
  intros g i j H.
  unfold neighborhood in H.
  unfold neighbors in H.
  remember (adj g i) as s.
  apply subgraph_of_nodes with (g := g).
  destruct (E.eq_dec j i).
  - hauto lq: on use: Sin_domain, remove_node_neq2 unfold: nodes.
  - hauto lq: on use: Sin_domain, remove_node_neq unfold: nodes.
Qed.

Lemma subgraph_of_in_iff :
  forall g s v, M.In v (subgraph_of g s) <-> (M.In v g /\ S.In v s).
Proof.
  intros g s v.
  sauto lq: on use: WP.F.map_in_iff, restrict_spec unfold: subgraph_of.
Qed.

Lemma subgraph_of_monotone g s1 s2 :
  S.Subset s1 s2 -> is_subgraph (subgraph_of g s1) (subgraph_of g s2).
Proof.
  intros H.
  split.
  - unfold S.Subset.
    intros v Hv.
    apply Sin_domain.
    apply Sin_domain in Hv.
    rewrite subgraph_of_in_iff in *.
    sfirstorder.
  - hfcrush use: SP.in_subset, adj_subgraph_of_spec unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, node, PositiveSet.Subset.
Qed.

Lemma adj_empty_if_notin :
  forall g w, ~ M.In w g -> adj g w = S.empty.
Proof.
  intros g w Hnot.
  unfold adj.
  destruct (WF.In_dec g w) as [Hin|Hout]; [contradiction|].
  sauto.
Qed.

Lemma neighborhood_nodes_eq_adj :
  forall g v,
    no_selfloop g ->
    undirected g ->
    S.Subset (neighbors g v) (nodes (neighborhood g v)).
Proof.
  intros g v Hg Hund w Hw_in.
  (* 1) Show w is a real vertex of g, using undirectedness *)
  assert (Hin_g : M.In w g).
  { (* If w ∉ g, then adj g w = ∅, but undirectedness gives v ∈ adj g w *)
    specialize (Hund v w Hw_in) as Hv_in_w.
    destruct (WF.In_dec g w) as [Hin|Hnot]; [exact Hin|].
    qauto unfold: nodeset, PositiveSet.elt, PositiveSet.empty, PositiveSet.t, node, PositiveSet.In, PositiveOrderedTypeBits.t, adj, PositiveSet.mem, PositiveMap.In, PositiveMap.MapsTo.
  }
  (* 2) Use filter-iff to show w is kept by the neighborhood filter *)
  unfold neighborhood.
  (* nodes = domain of the filtered map *)
  unfold nodes; apply Sin_domain.
  destruct Hin_g as [adjw Hw_maps]. (* witness adjacency set at w in g *)
  apply remove_node_neq.
  - sfirstorder.
  - unfold neighbors in *.
    unfold subgraph_of.
    rewrite WP.F.map_in_iff.
    apply restrict_spec.
    hauto l: on.
Qed.

Lemma neighborhood_nodes_equal_adj :
  forall g v, no_selfloop g -> undirected g ->
  S.Equal (nodes (neighborhood g v)) (adj g v).
Proof. split; [apply nbd_adj|apply neighborhood_nodes_eq_adj]; auto. Qed.

Lemma adj_neighborhood_spec :
  forall g v i j, no_selfloop g -> undirected g ->
  S.In i (adj (neighborhood g v) j)
  <-> S.In i (adj g j) /\ i <> v /\ j <> v
      /\ S.In i (adj g v) /\ S.In j (adj g v).
Proof.
  intros g v i j _ _. unfold neighborhood.
  rewrite adj_remove_node_spec, adj_subgraph_of_spec; tauto.
Qed.


Lemma no_edge_from_center_after_removal :
  forall g v,
    no_selfloop g ->
    undirected g ->
    forall w,
      M.In w (remove_nodes g (nodes (neighborhood g v))) ->
      ~ S.In w (adj g v).
Proof.
  hauto lq: on use: remove_nodes_remove, neighborhood_nodes_equal_adj unfold: PositiveSet.elt, PositiveMap.key, PositiveSet.Equal.
Qed.

(* Flip between the two target colors *)
Definition flip (c1 c2 c : positive) : positive :=
  if Pos.eqb c c1 then c2 else c1.


(** When is an edge in the induced subgraph?
- if [i], [j] in [S] and [(i,j)] in [G] then [(i,j)] in $G|_S$
- if [(i,j)] in $G|_S$ then [(i,j)] in [G]
- if [v] in $G|_S$ then [v] in [S]
- if [v] in [S] and [v] in [G] then [v] in $G|_S$
 *)

(** * Degrees and maximum degrees *)
(** Note that this is a partial function because if the vertex is not
    in the graph and we return 0, we can't tell whether it's actually
    in the graph or not. *)
(** ** Degree of a vertex *)
Definition degree (v : node) (g : graph) :=
  match M.find v g with
  | None => None
  | Some a => Some (S.cardinal a)
  end.

(** ** Maximum degree of a graph *)
Definition max_deg (g : graph) := list_max (map (fun p => S.cardinal (snd p)) (M.elements g)).


(** ** Inversion lemma for degree *)

Lemma degree_gt_0_in (g : graph) (v : node) n :
  degree v g = Some n -> M.In v g.
Proof.
  sauto unfold: degree, adj.
Qed.

(** ** The maximum degree of an empty graph is 0 *)

Lemma max_deg_empty : max_deg (@M.empty _) = 0.
Proof. sfirstorder. Qed.

(** ** Maximum degree bounds the size of all the adjacency sets *)

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

(** ** Max degree being 0 implies non-adjacency of all vertices **)

Lemma max_deg_0_adj (g : graph) i j : max_deg g = 0 -> ~ S.In i (adj g j).
Proof.
  intros H contra.
  assert (M.In j g).
  {
    hauto use: SP.Dec.F.empty_iff unfold: PositiveMap.In, PositiveMap.MapsTo, adj.
  }
  destruct H0 as [e He].
  unfold adj in contra.
  unfold M.MapsTo in He.
  rewrite He in contra.
  pose proof (max_deg_max g j e ltac:(sfirstorder)).
  hauto use: SP.remove_cardinal_1 unfold: nodeset inv: Peano.le.
Qed.

(** ** Non-zero max degree implies non-empty graph *)

Lemma max_deg_gt_not_empty (g : graph) : max_deg g > 0 -> ~ M.Empty g.
Proof.
  intros H contra.
  pose proof max_deg_empty.
  unfold max_deg in H.
  apply (WP.elements_Empty g) in contra.
  sauto q: on.
Qed.

(** ** Removing a node from a graph removes it from adjaceny sets *)
Lemma remove_node_find :
  forall (g : graph) (i j : node) (e1 : nodeset),
    i <> j ->
    M.find j g = Some e1 ->
    M.find j (remove_node i g) = Some (S.remove i e1).
Proof.
  intros g i j e1 H H0.
  unfold remove_node.
  rewrite WF.map_o, M.gro by auto.
  hauto lq: on.
Qed.

(** ** Removing vertex decreases degree of neighbors *)

Lemma vertex_removed_nbs_dec : forall (g : graph) (i j : node) n,
    i <> j ->
    S.In i (adj g j) ->
    degree j g = Some (S n) ->
    degree j (remove_node i g) = Some n.
Proof.
  intros g i j n Hl H1 H2.
  unfold degree, adj in *.
  hfcrush use: remove_node_find, SP.remove_cardinal_1.
Qed.

(** ** S.InL and In agree *)

Lemma inl_in i l : S.InL i l <-> In i l.
Proof.
  split; induction l; sauto lq: on.
Qed.

(** ** Subset respects list inclusion of elements *)

Lemma incl_subset s s' : S.Subset s s' -> incl (S.elements s) (S.elements s').
Proof.
  intros H i Hi.
  unfold S.elt in i.
  pose proof (S.elements_2 s ltac:(hauto l: on use: inl_in)).
  rewrite <- inl_in.
  sfirstorder use: PositiveSet.elements_1 unfold: PositiveSet.elt.
Qed.

(** ** Extract a maximum element from a non-empty list *)
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

(** ** Extract a vertex of maximum degree in an non-empty graph *)

Lemma max_degree_vert : forall g n, ~ M.Empty g -> max_deg g = n -> exists v, degree v g = Some n.
Proof.
  intros g n H H1.
  unfold max_deg in H1.
  apply list_max_witness in H1.
  - destruct H1 as [x [Hx]].
    subst.
    apply in_map_iff in Hx.
    destruct Hx as [[v ve] [Hx]].
    exists v.
    simpl in Hx.
    apply M.elements_complete in H0.
    unfold degree.
    hauto lq: on.
  - sauto lq: on rew: off use: map_eq_nil, WP.elements_Empty inv: list.
Qed.

(** ** Subgraph relation respects maximum degree *)

Lemma max_deg_subgraph : forall (g g' : graph), is_subgraph g' g -> max_deg g' <= max_deg g.
Proof.
  intros g g' H.
  unfold max_deg.
  unfold is_subgraph in H.
  pose proof incl_Forall_in_iff.
  (* let d be the max degree of the original graph *)
  remember (list_max (map (fun p : M.key * S.t => S.cardinal (snd p)) (M.elements g))) as d.
  (* let d' be the max degree of subgraph *)
  remember (list_max (map (fun p : M.key * S.t => S.cardinal (snd p)) (M.elements g'))) as d'.
  (* when d' = 0 this is immediate, otherwise it's non-zero *)
  destruct d'; [hauto l: on|].
  assert (map (fun p : M.key * S.t => S.cardinal (snd p)) (M.elements g') <> []) by sauto.
  pose proof (list_max_witness _ (S d') H1 (eq_sym Heqd')).
  destruct H2 as [x [Hx Hx2]].
  rewrite in_map_iff in Hx.
  destruct Hx as [x' [Hx' Hx'']].
  destruct x'.
  subst.
  simpl in Hx2.
  apply M.elements_complete in Hx''.
  assert (M.In k g).
  {
    hauto lq: on rew: off use: subgraph_vert_m unfold: PositiveMap.MapsTo, nodeset.
  }
  destruct H2 as [e He].
  pose proof (max_deg_max g k e He).
  (* hfcrush use: SP.subset_cardinal, le_trans unfold: adj. *)
  apply le_trans with (m := S.cardinal e).
  - fcrush use: SP.subset_cardinal unfold: adj.
  - assumption.
Qed.


(** ** Max degree remains unchanged after removal of non-adjacent max degree vertex *)
Lemma max_deg_remove_node :
  forall (n : nat) (g : graph) (v x : node),
    max_deg g = S n ->
    degree v g = Some (S n) ->
    degree x g = Some (S n) ->
    ~ S.In x (adj g v) ->
    x <> v ->
    max_deg (remove_node x g) = S n.
Proof.
  intros n g v x H1 H H0 H2 H3.
  assert (is_subgraph (remove_node x g) g) by apply remove_node_subgraph.
  assert ((max_deg (remove_node x g) <= (S n))%nat) by hauto l: on use: max_deg_subgraph.
  apply le_lteq in H5.
  destruct H5; [|assumption].
  assert (M.In v (remove_node x g)).
  {
    apply remove_node_neq.
    - auto.
    - hauto l: on unfold: degree.
  }
  destruct H6 as [e He].
  assert (M.In v g) by hauto l: on unfold: degree.
  assert (degree v (remove_node x g) = Some (S n)).
  {
    unfold degree.
    unfold adj in H2.
    rewrite He.
    destruct H6 as [e' He'].
    hfcrush use: SP.remove_cardinal_2, remove_node_find unfold: PositiveMap.MapsTo, nodeset, PositiveOrderedTypeBits.t, node, PositiveSet.elt, degree inv: option.
  }
  pose proof (max_deg_max (remove_node x g) _ _ He).
  hauto lq: on use: Znat.Nat2Z.inj_le, Znat.Nat2Z.inj_gt unfold: PositiveMap.MapsTo, nodeset, BinInt.Z.gt, BinInt.Z.le, gt, degree.
Qed.

(** * Vertex extraction *)
(** ** Definition for a given degree *)

Definition extract_deg_vert (g : graph) (d : nat) :=
  find (fun p => Nat.eqb (S.cardinal (snd p)) d) (M.elements g).

(* Annoying lemma *)
(** ** InA to In conversion for pairs *)
Lemma InA_in_iff {A} : forall p (l : list (M.key * A)), (InA (@M.eq_key_elt A) p l) <-> In p l.
Proof. induction l; sauto q: on. Qed.

(** ** Decidability of extracting a vertex of a given degree *)

Lemma extract_deg_vert_dec : forall (g : graph) (d : nat),
    {v | degree v g = Some d} + ~ exists v, degree v g = Some d.
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
    ssimpl.
    hauto lb: on.
  - right.
    intros contra.
    destruct contra as [v e].
    unfold degree in e.
    unfold extract_deg_vert in E.
    unfold adj in e.
    ssimpl.
    destruct (M.find v g) eqn:E2.
    + assert (In (v,n) (M.elements g)).
      {
        apply InA_in_iff.
        apply WF.elements_mapsto_iff.
        hauto lq: on drew: off.
      }
      pose proof (find_none _ _ E _ H).
      simpl in H0.
      hauto lb: on.
    + sfirstorder.
Defined.

(** * Iterated extraction *)
(** This section concerns functions that extract a list of vertices
    satisfying a degree criterion and incremental removal from the
    graph. *)

(** ** Extracting a vertex with a given degree iteratively *)
Function extract_vertices_deg (g : graph) (d : nat) {measure M.cardinal g} : list (node * graph) * graph :=
  match extract_deg_vert_dec g d with
  | inl v =>
      let g' := remove_node (`v) g in
      let (l, g'') := extract_vertices_deg g' d in
      ((`v, g') :: l, g'')
  | inr _ => (nil, g)
  end.
Proof.
  intros g d v teq.
  destruct v as [v Hv].
  simpl.
  unfold remove_node.
  rewrite cardinal_map.
  sauto lq: on rew: off use: Mremove_cardinal_less, degree_gt_0_in.
Defined.

Functional Scheme extract_vertices_deg_ind := Induction for extract_vertices_deg Sort Prop.

Definition remove_deg_n_graph g n := snd (extract_vertices_deg g n).
Definition remove_deg_n_trace g n := fst (extract_vertices_deg g n).

(** ** Iterative extraction exhausts vertices of that (non-zero) degree *)
Lemma extract_vertices_deg_exhaust (g : graph) n :
  n > 0 -> ~ exists v, degree v (remove_deg_n_graph g n) = Some n.
Proof.
  unfold remove_deg_n_graph.
  functional induction (extract_vertices_deg g n) using extract_vertices_deg_ind.
  - qauto l: on.
  - intros dgt0 contra.
    destruct d; [sauto q:on|].
    simpl in *.
    destruct contra as [v ve].
    sauto lq: on use: degree_gt_0_in.
Qed.

(** ** Decidability of map emptiness *)
Lemma mempty_dec {A} (m : M.t A) : {M.Empty m} + {~ M.Empty m}.
Proof.
  destruct (eq_dec (M.cardinal m) 0).
  - strivial use: WP.cardinal_Empty.
  - right.
    assert ((M.cardinal m > 0)) by sfirstorder.
    sfirstorder use: WP.cardinal_1.
Defined.

(** ** Extracted graph is a subgraph*)
Lemma extract_vertices_deg_subgraph1 g g' g'' n v l :
  extract_vertices_deg g n = ((v, g') :: l, g'') -> is_subgraph g' g.
Proof.
  intros H.
  rewrite extract_vertices_deg_equation in H.
  hfcrush drew: off use: remove_node_subgraph inv: sum.
Qed.

(** * Subgraph series *)
(** A subgraph series is a list of subgraphs such that later elements
    are subgraphs of former elements.  *)

Inductive subgraph_series : list graph -> Prop :=
| sg_nil : subgraph_series []
| sg_single : forall g, subgraph_series [g]
| sg_cons : forall g g' l, is_subgraph g' g -> subgraph_series (g' :: l) -> subgraph_series (g :: g' :: l).

(** The subgraphs created by the extraction are a subgraph series *)

Lemma extract_vertices_deg_series g n :
  subgraph_series (map snd (remove_deg_n_trace g n)).
Proof.
  unfold remove_deg_n_trace.
  functional induction (extract_vertices_deg g n) using extract_vertices_deg_ind.
  - destruct l eqn:E.
    + hauto l: on.
    + destruct p.
      simpl.
      apply sg_cons.
      * remember (remove_node (` v) g) as g'.
        hauto l: on use: extract_vertices_deg_subgraph1.
      * rewrite e0 in IHp.
        ssimpl.
  - sauto lq: on rew: off.
Qed.

(** ** The final graph returned by the vertex extraction is a subgraph. *)

Lemma extract_vertices_deg_subgraph (g : graph) n :
  is_subgraph (remove_deg_n_graph g n) g.
Proof.
  unfold remove_deg_n_graph.
  functional induction (extract_vertices_deg g n) using extract_vertices_deg_ind.
  - simpl.
    rewrite e0 in IHp.
    simpl in IHp.
    pose proof (remove_node_subgraph g (` v)).
    hauto l: on use: subgraph_trans.
  - apply subgraph_refl.
Qed.

(** ** Max degree 0 implies all vertices have degree 0 *)

Lemma max_deg_0_all_0 : forall (g : graph) v, max_deg g = 0 -> M.In v g -> degree v g = Some 0.
Proof.
  intros g v H H0.
  destruct H0 as [e He].
  pose proof (max_deg_max _ _ _ He).
  unfold degree.
  sauto.
Qed.

(** ** Extracting degree 0 vertices from a max degree 0 graph empties it *)

Lemma extract_vertices_deg0_empty : forall (g : graph),
  max_deg g = 0 -> M.Empty (remove_deg_n_graph g 0).
Proof.
  unfold remove_deg_n_graph.
  intros g.
  remember 0 as d.
  functional induction (extract_vertices_deg g d) using extract_vertices_deg_ind.
  - intros H.
    assert (max_deg (remove_node (` v) g) = 0).
    {
      enough (max_deg (remove_node (` v) g) <= 0).
      sauto.
      rewrite <- H.
      apply max_deg_subgraph.
      apply remove_node_subgraph.
    }
    specialize (IHp (@eq_refl _) H0).
    simpl.
    rewrite e0 in IHp.
    assumption.
  - intros H v e' contra.
    assert (degree v g = Some 0).
    {
      sauto lq: on rew: off use: max_deg_0_all_0, extract_vertices_deg_equation unfold: PositiveMap.In, snd, extract_vertices_deg, PositiveMap.MapsTo inv: sum.
    }
    sauto.
Qed.

(** ** Extracting all max degree vertices strictly decreases max degree *)

Lemma extract_vertices_max_deg (g : graph) :
   max_deg g > 0 -> max_deg (remove_deg_n_graph g (max_deg g)) < max_deg g.
Proof.
  unfold remove_deg_n_graph.
  intros H.
  pose proof (extract_vertices_deg_exhaust g _ H).
  pose proof (extract_vertices_deg_subgraph g (max_deg g)).
  remember (extract_vertices_deg g (max_deg g)) as g'.
  unfold remove_deg_n_graph in H1.
  rewrite <- Heqg' in H1.
  pose proof (max_deg_subgraph g (snd g') H1).
  apply le_lteq in H2.
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
    unfold degree in *.
    apply H0.
    hauto l: on.
Qed.

(** ** Subgraph respects degree of vertices *)

Lemma degree_subgraph (g g': graph) v n m :
  is_subgraph g g' -> degree v g = Some n -> degree v g' = Some m -> n <= m.
Proof.
  hfcrush use: SP.subset_cardinal unfold: degree, adj, nodeset, is_subgraph.
Qed.

(** ** Degree of a node that is removed is 0 *)
Lemma degree_remove (g : graph) v :
  degree v (remove_node v g) = None.
Proof.
  hauto lq: on use: degree_gt_0_in, remove_node_neq2 unfold: degree.
Qed.

(** ** Maximum degree in a subgraph implies maximum degree in original *)
Lemma max_deg_subgraph_inv : forall (g' g : graph) v,
    is_subgraph g' g ->
    degree v g' = Some (max_deg g) ->
    degree v g = Some (max_deg g).
Proof.
  intros g' g v H H0.
  unfold degree in H0.
  destruct (M.find v g') eqn:E; [|scongruence].
  inversion H0; clear H0.
  unfold degree.
  destruct (M.find v g) eqn:E2.
  - rewrite H2.
    f_equal.
    pose proof (max_deg_max g v n0 E2).
    unfold is_subgraph in H.
    pose proof (proj2 H v).
    rewrite <- H2 in H0.
    unfold adj in H1.
    rewrite E, E2 in H1.
    apply SP.subset_cardinal in H1.
    hauto l: on.
  - exfalso.
    hauto l: on use: subgraph_vert_m.
Qed.

(** ** Non-adjacency of max degree vertices after one step *)
(** If a vertex of max degree is removed from a graph then any vertex
    with max degree in the new graph cannot be adjacent to it. *)

Lemma remove_max_deg_adj : forall (g : graph) (i j : node),
    i <> j ->
    M.In i g ->
    degree j g = Some (max_deg g) ->
    degree j (remove_node i g) = Some (max_deg g) ->
    ~ (S.In i (adj g j)).
Proof.
  intros g i j H0 H1 H2 H3 H4.
  remember (max_deg g) as d.
  assert (degree j (remove_node i g) = Some (max_deg g)) by (scongruence use: vertex_removed_nbs_dec).
  destruct d eqn:E.
  - sfirstorder use: max_deg_0_adj.
  - hauto l: on use: vertex_removed_nbs_dec, n_Sn.
Qed.

(** The same as above, but for non-zero degree graphs *)

Lemma remove_max_deg_adj' : forall (g : graph) (i j : node),
    max_deg g > 0 ->
    M.In i g ->
    degree j g = Some (max_deg g) ->
    degree j (remove_node i g) = Some (max_deg g) ->
    ~ (S.In i (adj g j)).
Proof.
  intros g i j H H0 H1 H2 H3.
  remember (max_deg g) as d.
  destruct d; [inversion H|clear H].
  assert (degree j (remove_node i g) = Some (max_deg g)) by (scongruence use: vertex_removed_nbs_dec).
  hauto use: remove_max_deg_adj, degree_remove.
Qed.

(* If n is not adjacent to p in the graph g-m, then n is not adjacent
   to p in g.  *)
(* Need this to transport the information about non-adjacency back up
   the list.*)
(** ** Non-adjacency is preserved after removing a node *)
Lemma not_adj_remove : forall (g : graph) (n m p : node),
    n <> m -> m <> p ->
    ~ (S.In n (adj (remove_node m g) p)) ->
    ~ (S.In n (adj g p)).
Proof.
  intros g n m p H H0 H1 contra.
  hfcrush use: adj_remove_node_spec unfold: PositiveOrderedTypeBits.t, node, PositiveSet.elt.
Qed.

(** ** Non-adjacency is preserved after removing nodes *)
Lemma not_adj_removes : forall (g : graph) (n p : node) s,
    ~ S.In n s -> ~ S.In p s ->
    ~ (S.In n (adj (remove_nodes g s) p)) ->
    ~ (S.In n (adj g p)).
Proof.
  intros g n p s H H0 H1.
  hfcrush use: adj_remove_nodes_spec unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, node, nodeset.
Qed.

(** * Independent sets *)
(** An independent set is a set of vertices such that no two are adjacent. *)

Definition independent_set (g : graph) (s : nodeset) :=
  forall i j, S.In i s -> S.In j s -> ~ S.In i (adj g j).

(* If we have an independent set and a new vertex that is not adjacent
   to anything in the independent set, then adding it results in a new
   independent set. *)
(** ** Adding a non-adjacent vertex to an independent set *)
Lemma independent_set_add g s i :
  no_selfloop g -> undirected g ->
  (forall j, S.In j s -> ~ S.In i (adj g j)) ->
  independent_set g s -> independent_set g (S.add i s).
Proof.
  intros H H0 H1 H2.
  intros a b Ha Hb contra.
  unfold independent_set in H2.
  destruct (E.eq_dec a i), (E.eq_dec b i); hauto l: on use: PositiveSet.add_3.
Qed.

(* An independent set can be restricted to a subgraph *)
(** ** Independent sets are preserved in subgraphs *)
Lemma independent_set_subgraph : forall (g g' : graph) (s : nodeset),
    is_subgraph g' g -> independent_set g s -> independent_set g' s.
Proof. sfirstorder. Qed.

(* Extracting vertices with a given degree into a set *)
Function extract_vertices_degs (g : graph) (d : nat) {measure M.cardinal g} : nodeset * graph :=
  match extract_deg_vert_dec g d with
  | inl v =>
      let g' := remove_node (`v) g in
      let (s, g'') := extract_vertices_degs g' d in
      (S.add (`v) s , g'')
  | inr _ => (S.empty, g)
  end.
Proof.
  intros g d v teq.
  destruct v as [v Hv].
  simpl.
  unfold remove_node.
  rewrite cardinal_map.
  sauto lq: on rew: off use: Mremove_cardinal_less, degree_gt_0_in.
Defined.

Functional Scheme extract_vertices_degs_ind := Induction for extract_vertices_degs Sort Prop.

(** ** Extracting max degree vertices from a strictly lower max degree subgraph is empty *)
Lemma extract_vertices_degs_empty :
  forall (g g' g'' : graph) (d : nat) (v : node) s,
    is_subgraph g' g ->
    d = max_deg g ->
    extract_vertices_degs g' d = (s, g'') ->
    max_deg g' < max_deg g ->
    degree v g = Some d ->
    S.Empty s.
Proof.
  intros g g' g'' d v s H H0 e0 H2 H3.
  rewrite extract_vertices_degs_equation in e0.
  destruct (extract_deg_vert_dec _ _).
  - exfalso.
    
    destruct s0 as [k Hk].
    pose proof (degree_gt_0_in _ _ _ Hk).
    assert (M.In k g).
    {
      sauto lq: on rew: off use: max_deg_subgraph_inv, degree_gt_0_in.
    }
    destruct H4 as [e' He'].
    unfold M.MapsTo in He'.
    pose proof (max_deg_max _ _ _ He').
    unfold degree in Hk.
    clear e0.
    destruct (M.find _ _) eqn:EE.
    + inversion Hk.
      clear Hk.
      assert (max_deg g' = max_deg g) by sfirstorder use: max_deg_max, EE.
      lia.
    + inversion Hk.
  - fcrush.
Qed.

(* we would like to have if and only if in the conclusion but
   unfortunately it's not true while the function is iterating *)
(** ** Extracting all the max degree vertices results in an independent set. *)
Lemma max_degree_extraction_independent_set0 : forall (g : graph) d,
    no_selfloop g ->
    d = max_deg g ->
    d = 0 ->
    independent_set g (fst (extract_vertices_degs g 0)) /\
      (forall k, S.In k (fst (extract_vertices_degs g d)) -> degree k g = Some d).
Proof.
  intros go.
  apply (extract_vertices_degs_ind (fun g d p =>  no_selfloop g -> d = max_deg g -> d = 0 -> independent_set g (fst (extract_vertices_degs g 0)) /\ (forall k, S.In k (fst (extract_vertices_degs g d)) -> degree k g = Some d))).
  - intros g d v e g' H s g'' e0 H0 H1 ->.
    rewrite extract_vertices_degs_equation.
    rewrite e.
    destruct v as [v' Hv'].
    simpl in *.
    subst g'.
    assert (is_subgraph (remove_node v' g) g) by (apply remove_node_subgraph).
    split.
    + hauto l: on use: max_deg_0_adj unfold: independent_set.
    + intros k H5.
      rewrite e0 in H5.
      simpl in H5.
      apply S.add_spec in H5.
      destruct H5.
      * fcrush.
      * pose proof (max_deg_subgraph _ _ H2).
        pose proof (H ltac:(hauto l: on use: remove_node_no_selfloop)
                      ltac:(sauto)
                      ltac:(auto)).
        pose proof (proj2 H5 k).
        rewrite e0 in H6.
        simpl in H6.
        specialize (H6 ltac:(scongruence)).
        hauto l: on use: max_deg_subgraph_inv.
  - intros g d _x e H H0 ->.
    split.
    + rewrite extract_vertices_degs_equation, e.
      sfirstorder.
    + intros k H3.
      rewrite extract_vertices_degs_equation, e in H3.
      sauto q: on.
Qed.

(** ** Extracting max degree vertices gives an independent set *)
Lemma max_degree_extraction_independent_set : forall (g : graph) (d : nat),
    undirected g ->
    no_selfloop g ->
    d = max_deg g ->
    independent_set g (fst (extract_vertices_degs g d)) /\
      (forall k, S.In k (fst (extract_vertices_degs g d)) -> degree k g = Some d).
Proof.
  intros go d.
  destruct d eqn:Hd; [hauto l: on use: max_degree_extraction_independent_set0|].
  assert (d > 0) by sfirstorder.
  rewrite <- Hd in *.
  clear Hd n.
  generalize dependent d.
  apply (extract_vertices_degs_ind (fun g d p => d > 0 -> undirected g -> no_selfloop g -> d = max_deg g -> independent_set g (fst (extract_vertices_degs g d)) /\ (forall k, S.In k (fst (extract_vertices_degs g d)) -> degree k g = Some d))).
  intros g d v e g' H s g'' e0 H3 H0 H1 H2.
  - rewrite extract_vertices_degs_equation.
    rewrite e.
    destruct v as [v' Hv'].
    simpl in *.
    subst g'.
    assert (is_subgraph (remove_node v' g) g) by (apply remove_node_subgraph).
    pose proof (max_deg_subgraph _ _ H4).
    apply le_lteq in H5.
    destruct H5.
    + rewrite e0.
      simpl.
      assert (S.Empty s) by eauto using extract_vertices_degs_empty.
      split.
      * unfold independent_set.
        intros i j H7 H8.
        apply S.add_spec in H7, H8.
        destruct H7, H8; scongruence.
      * intros k H7.
        apply S.add_spec in H7.
        destruct H7; scongruence.
    + subst d.
      pose proof (H H3
                    ltac:(hauto l: on use: remove_node_undirected)
                    ltac:(hauto l: on use: remove_node_no_selfloop)
                    (eq_sym H5)).
      rewrite e0 in *.
      simpl in *.
      split.
      intros i j Hi Hj.
      apply S.add_spec in Hi, Hj.
      (* now we want to prove the new set is an independent set *)
      destruct Hi, Hj.
      * scongruence.
      * assert (i <> j) by hauto l: on use: degree_remove.
        hcrush use: degree_remove, degree_gt_0_in, remove_max_deg_adj, max_deg_subgraph_inv unfold: PositiveSet.elt, node, PositiveOrderedTypeBits.t.
      * hcrush use: max_deg_subgraph_inv, remove_max_deg_adj', degree_gt_0_in unfold: node, PositiveOrderedTypeBits.t, PositiveSet.elt, undirected.
      * unfold independent_set in H5.
        pose proof (proj1 H2 i j H6 H7).
        pose proof (proj2 H2 _ H6).
        pose proof (proj2 H2 _ H7).
        pose proof (degree_gt_0_in _ _ _ H9).
        destruct (E.eq_dec i j); [scongruence|].
        assert (degree j g = Some (max_deg g)).
        {
          hauto l: on use: max_deg_subgraph_inv.
        }
        assert (degree j (remove_node i g) = Some (max_deg g)).
        {
          unfold remove_node, degree.
          unfold adj, remove_node in H8.
          unfold degree in H12.
          rewrite WF.map_o.
          rewrite M.gro by auto.
          destruct (M.find j g) eqn:EE2.
          - inversion H12.
            simpl.
            f_equal.
            destruct (E.eq_dec j v').
            + subst. rewrite degree_remove in H10.
              inversion H10.
            + rewrite WF.map_o in H8.
              rewrite M.gro in H8 by auto.
              rewrite EE2 in H8.
              simpl in H8.
              rewrite SP.remove_cardinal_2.
              reflexivity.
              destruct (E.eq_dec i v').
              * subst. scongruence use: degree_remove.
              * qauto l: on use: S.remove_spec.
          - inversion H12.
        }
        hauto l: on use: remove_max_deg_adj, subgraph_vert_m.
      * intros k H6.
        apply S.add_spec in H6.
        destruct H6.
        ** subst. assumption.
        ** pose proof (proj2 H2 k H6).
           sauto lq: on rew: off use: max_deg_subgraph_inv.
  - intros g d _x e H H0 H1 H2.
    split.
    + rewrite extract_vertices_degs_equation, e.
      sfirstorder.
    + intros k H3.
      rewrite extract_vertices_degs_equation, e in H3.
      sauto q: on.
Qed.

(** ** Iterative extraction exhausts vertices of that (non-zero) degree *)
Lemma extract_vertices_degs_exhaust (g g' : graph) n ns :
  n > 0 ->
  extract_vertices_degs g n = (ns, g') ->
  ~ exists v, degree v g' = Some n.
Proof.
  intros H H0.
  generalize dependent ns.
  functional induction (extract_vertices_degs g n) using extract_vertices_degs_ind.
  - intros ns H0.
    hauto lq: on.
  - intros ns H0.
    hauto lq: on rew: off.
Qed.

(** ** Iterative extraction results in a subgraph *)
Lemma extract_vertices_degs_subgraph : forall (g g' : graph) n ns,
  extract_vertices_degs g n = (ns, g') ->
  is_subgraph g' g.
Proof.
  intros g g' n ns.
  generalize dependent ns.
  functional induction (extract_vertices_degs g n) using extract_vertices_degs_ind.
  - intros ns H.
    rewrite e0 in IHp.
    inversion H.
    subst.
    pose proof (IHp s ltac:(reflexivity)).
    hauto l: on use: subgraph_trans, remove_node_subgraph.
  - intros ns [=H<-].
    apply subgraph_refl.
Qed.

(** ** Adjacency relations are preserved after extraction. **)
Lemma adj_preserved_after_extract :
  forall g d s g' i j,
    extract_vertices_degs g d = (s, g') ->
    M.In i g' -> M.In j g' ->
    (S.In j (adj g' i) <-> S.In j (adj g i)).
Proof.
  intros g d s g' i j Hext Hi Hj.
  revert s g' Hext i j Hi Hj.
  functional induction (extract_vertices_degs g d)
           using extract_vertices_degs_ind; intros s' g' Hext i j Hi Hj.
  - (* a vertex `v` was deleted, we recursed on remove_node (`v) g *)
    inversion Hext; subst; clear Hext.
    (* g' is a subgraph of remove_node (`v) g *)
    assert (Hsub : is_subgraph g' (remove_node (` v) g)).
    { eapply extract_vertices_degs_subgraph; eauto. }
    (* hence neither i nor j can equal the deleted vertex `v` *)
    assert (Hnv : ~ M.In (` v) g'). { eapply remove_node_not_in; eauto. }
    assert (Hi_neq : i <> ` v). { sauto. }
    assert (Hj_neq : j <> ` v). { sauto. }
    rewrite IHp; try (eauto using subgraph_vert_m).
    now rewrite adj_remove_node_spec.
  - (* nothing was deleted: g' = g *)
    inversion Hext; subst; tauto.
Qed.

Lemma adj_preserved_if_not_removed g s i j :
  ~S.In i s -> ~S.In j s ->
  (S.In j (adj (remove_nodes g s) i) <-> S.In j (adj g i)).
Proof. hauto l:on use: adj_remove_nodes_spec. Qed.

(** ** Iterative extraction preserves undirectedness *)
Lemma extract_vertices_degs_undirected : forall (g g' : graph) n ns,
    undirected g ->
    extract_vertices_degs g n = (ns, g') ->
    undirected g'.
Proof.
  intros g g' n ns Hg.
  generalize dependent ns.
  functional induction (extract_vertices_degs g n) using extract_vertices_degs_ind.
  - intros ns Hns.
    rewrite e0 in IHp.
    simpl in *.
    hauto lq: on rew: off use: remove_node_undirected.
  - intros ns [=H<-].
    assumption.
Qed.

(** ** Iterative max degree extraction strictly decreases the max degree *)
Lemma extract_vertices_max_degs : forall (g g' : graph) ns,
    max_deg g > 0 ->
    extract_vertices_degs g (max_deg g) = (ns, g') ->
    max_deg g' < max_deg g.
Proof.
  intros g g' ns H H0.
  pose proof (extract_vertices_degs_subgraph g _ _ _ H0).
  pose proof (extract_vertices_degs_exhaust g _ _ _ H H0).
  pose proof (max_deg_subgraph _ _ H1).
  apply le_lteq in H3.
  destruct H3; [hauto lq: on|].
  exfalso.
  assert (~ M.Empty g') by hauto lq: on use: max_deg_gt_not_empty.
  pose proof (max_degree_vert g' (max_deg g) H4 H3).
  contradiction.
Qed.

Lemma add_back_diff_singleton :
  forall (A B : S.t) (x : node),
    S.In x A -> ~ S.In x B ->
    S.Equal (S.add x (S.diff (S.diff A (S.singleton x)) B))
            (S.diff A B).
Proof.
  intros A B x HAx HxB y; split; intro Hy.
  - (* -> *)
    apply S.add_spec in Hy as [->|Hy].
    + apply S.diff_spec; split; [assumption|assumption].
    + apply S.diff_spec in Hy as [Hy1 Hy2].            (* y∈A\{x} and y∉B *)
      apply S.diff_spec in Hy1 as [HyA _].              (* y∈A *)
      apply S.diff_spec; split; [assumption|assumption].
  - (* <- *)
    apply S.diff_spec in Hy as [HyA HyB].               (* y∈A and y∉B *)
    destruct (E.eq_dec y x) as [->|Hneq].
    + apply S.add_spec; left; reflexivity.
    + apply S.add_spec; right.
      apply S.diff_spec; split.
      * apply S.diff_spec; split; [assumption|].
        intro HySing.                                   (* y∈{x} *)
        sfirstorder use: PositiveSet.singleton_1 unfold: PositiveOrderedTypeBits.t, node, PositiveSet.elt.
      * exact HyB.
Qed.
Lemma extract_vertices_degs_nodes_eq :
  forall g d s g',
    extract_vertices_degs g d = (s, g') ->
    S.Equal s (S.diff (nodes g) (nodes g')).
Proof.
  intros g d; functional induction (extract_vertices_degs g d)
    using extract_vertices_degs_ind; intros s' g' Hext.
  - inversion Hext; subst.
    specialize (IHp _ _ e0).
    rewrite nodes_remove_node_eq in IHp.
    (* v ∉ nodes g' and v ∈ nodes g *)
    assert (~ S.In (`v) (nodes g')).
    { pose proof (extract_vertices_degs_subgraph _ _ _ _ e0).
      pose proof (remove_node_not_in _ _ _ H).
      sauto lq: on rew: off use: in_nodes_iff.
    }
    assert (S.In (`v) (nodes g)).
    { apply Sin_domain.
      apply (degree_gt_0_in g (` v) d).
      hauto l: on.
    } 
    (* S Equalities: add back the freshly removed v *)
    rewrite IHp.
    rewrite add_back_diff_singleton; eauto.
    reflexivity.
  - inversion Hext; subst. strivial use: SP.diff_subset_equal, subgraph_refl unfold: is_subgraph, PositiveSet.Equal.
Qed.

(** ** Vertices in extraction are not in resulting graph but are in original graph *)
(** Later we can use this to show that the vertices after each round
    of extraction are disjoint. *)

Lemma extract_vertices_remove : forall (g g' : graph) s n,
    (s, g') = extract_vertices_degs g n ->
    (forall v, S.In v s -> ~ M.In v g' /\ M.In v g).
Proof.
  intros g g' s n H v Hv.
  symmetry in H.
  apply extract_vertices_degs_nodes_eq in H.
  rewrite H in Hv; clear H.
  hauto lq: on use: S.diff_spec, in_nodes_iff.
Qed.

(** ** Disjointness of after each round of extraction *)
Lemma max_degree_extraction_disjoint : forall (g g' g'' : graph) (n m : nat) s s',
    (s, g') = extract_vertices_degs g n ->
    (s', g'') = extract_vertices_degs g' m ->
    S.Empty (S.inter s s').
Proof.  
  hauto l: on use: extract_vertices_remove, SP.Dec.F.inter_iff unfold: PositiveSet.Empty.
Qed.

