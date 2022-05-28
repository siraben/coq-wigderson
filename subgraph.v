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

(** * Properties of subgraphs and degrees *)

(** ** Neighbors of a vertex *)

Definition neighbors (g : graph) v := adj g v.

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

(** ** Vertices in the subgraph are in original graph *)

Lemma subgraph_vert_m : forall g' g v, is_subgraph g' g -> M.In v g' -> M.In v g.
Proof. qauto l: on use: Sin_domain. Qed.

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
(** ** Definition *)

Definition subgraph_of (g : graph) (s : S.t) :=
  M.fold (fun v adj g' => if S.mem v s then M.add v (S.inter s adj) g' else g') g empty_graph.

(** ** Nodes of an induced subgraph are a subset of the original graph *)
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

(** ** Edges of an induced subgraph are a subset of the original graph *)
(** Note that this is defined pointwise: the adjacency set is a subset
    for every vertex. *)

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

(** ** Induced subgraph is subgraph *)

Lemma subgraph_of_is_subgraph : forall g s, is_subgraph (subgraph_of g s) g.
Proof.
  intros g s.
  unfold is_subgraph.
  split; [apply subgraph_vertices|apply subgraph_edges].
Qed.

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


(** * Neighborhood of a vertex *)
(** ** Definition *)
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

(** ** Vertices of an induced subgraph are a subset *)

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

(** If i is in the induced subgraph then i is in the set of inducing
    vertices. *)

Lemma subgraph_of_nodes : forall g i s, S.In i (nodes (subgraph_of g s)) -> S.In i s.
Proof.
  hauto l: on use: subgraph_vertices_set, subgraph_of_is_subgraph unfold: PositiveMap.key, is_subgraph, PositiveSet.Subset, PositiveSet.elt.
Qed.

(** ** The adjacency set of any vertex of in an induced subgraph is a subset of the vertex set  *)

Lemma subgraph_vertices_adj : forall g s i, S.Subset (adj (subgraph_of g s) i) s.
Proof.
  intros g s i.
  unfold subgraph_of.
  apply WP.fold_rec_bis.
  - sfirstorder.
  - unfold adj.
    unfold empty_graph.
    now rewrite M.gempty.
  - intros k e a m' H H0 H1.
    sdestruct (S.mem k s).
    + unfold adj, nodeset in *.
      destruct (E.eq_dec i k).
      * subst.
        hauto use: PositiveMap.gss, SP.Dec.F.empty_iff, SP.Dec.F.inter_iff unfold: PositiveSet.Subset inv: option.
      * hauto use: SP.subset_empty, PositiveMap.gso unfold: PositiveSet.Subset, PositiveSet.empty, node, PositiveOrderedTypeBits.t, PositiveMap.key inv: option.
    + assumption.
Qed.

(** ** In neighborhood implies in adjacency set *)

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

(** When is an edge in the induced subgraph?
- if i, j in S and (i,j) in G then (i,j) in G|s
- if (i,j) in G|s then (i,j) in G
- if vertex v in G|s then v in S
- if v in S and v in G then v in G|s
 *)

(** ** Remove a set of vertices from a graph *)
(** To make it easier to prove things about it,
- first restrict the graph by (S.diff (Mdomain g) s)
- then map subtracting s from every adj set
 *)
Definition remove_nodes (g : graph) (s : nodeset) :=
  M.map (fun ve => S.diff ve s) (restrict g (S.diff (nodes g) s)).

(** ** Removing nodes results in a subgraph *)
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

(** ** Every vertex in the removing set is not in the resulting graph *)

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

(** ** Removing a non-empty set of vertices decreases the size of the graph *)

Lemma remove_nodes_lt : forall g s i, S.In i s -> M.In i g -> (M.cardinal (remove_nodes g s) < M.cardinal g)%nat.
Proof.
  intros g s i H H0.
  pose proof (remove_nodes_sub g s i H H0).
  unfold remove_nodes.
  rewrite cardinal_map.
  assert (~ S.Empty s) by (hauto l: on).
  rewrite restrict_cardinal.
  rewrite SP.inter_sym.
  rewrite SP.inter_subset_equal by apply SP.diff_subset.
  rewrite Mcardinal_domain.
  apply SP.subset_cardinal_lt with (x := i).
  - apply SP.diff_subset.
  - unfold nodes. rewrite Sin_domain. auto.
  - rewrite S.diff_spec. sfirstorder.
Qed.

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

(** ** Removing a subgraph preserves undirectedness *)

Lemma remove_nodes_undirected : forall g s, undirected g -> undirected (remove_nodes g s).
Proof.
  unfold undirected.
  intros g s U i j IJ.
  rewrite adj_remove_nodes_spec in *.
  sfirstorder.
Qed.

(** * Maximum degree of a graph *)
(** ** Definition *)
Definition max_deg (g : graph) := list_max (map (fun p => S.cardinal (snd p)) (M.elements g)).

(** ** The maximum degree of an empty graph is 0 *)

Lemma max_deg_empty : max_deg (@M.empty _) = 0.
Proof. sfirstorder. Qed.

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

(** * Degree of a vertex *)
(** Note that this is a partial function because if the vertex is not
    in the graph and we return 0, we can't tell whether it's actually
    in the graph or not. *)

Definition degree (v : node) (g : graph) :=
  match M.find v g with
  | None => None
  | Some a => Some (S.cardinal a)
  end.

(** ** Inversion lemma for degree *)

Lemma degree_gt_0_in (g : graph) (v : node) n :
  degree v g = Some n -> M.In v g.
Proof.
  sauto unfold: degree, adj.
Qed.

(** ** Max degree being 0 implies non-adjacency of all vertices **)

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

(** ** Non-zero max degree implies non-empty graph *)

Lemma max_deg_gt_not_empty (g : graph) : max_deg g > 0 -> ~ M.Empty g.
Proof.
  intros H contra.
  pose proof max_deg_empty.
  unfold max_deg in H.
  apply (WP.elements_Empty g) in contra.
  sauto q: on.
Qed.

(** ** Removing vertex decreases degree of neighbors *)

Lemma vertex_removed_nbs_dec : forall (g : graph) (i j : node) n,
    undirected g ->
    no_selfloop g ->
    M.In i g ->
    S.In j (adj g i) ->
    degree j g = Some (S n) ->
    degree j (remove_node i g) = Some n.
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
  assert (j <> i) by scongruence.
  unfold remove_node.
  rewrite WF.map_o.
  rewrite M.gro by auto.
  ssimpl.
  f_equal.
  assert (S.In i n0).
  {
    hauto unfold: PositiveSet.In, adj.
  }
  sfirstorder use: SP.remove_cardinal_1 unfold: PositiveOrderedTypeBits.t, node, nodeset, PositiveSet.elt.
Qed.

(** * Vertex extraction *)
(** ** Definition for a given degree *)

Definition extract_deg_vert (g : graph) (d : nat) :=
  find (fun p => Nat.eqb (S.cardinal (snd p)) d) (M.elements g).

(* Annoying lemma *)
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

(** ** Iteractive extraction exhausts vertices of that (non-zero) degree *)
Lemma extract_vertices_deg_exhaust (g : graph) n :
  n > 0 -> ~ exists v, degree v (snd (extract_vertices_deg g n)) = Some n.
Proof.
  functional induction (extract_vertices_deg g n) using extract_vertices_deg_ind.
  - qauto l: on.
  - intros dgt0 contra.
    destruct d; [sauto q:on|].
    simpl in *.
    destruct contra as [v ve].
    sauto lq: on use: degree_gt_0_in.
Qed.

Lemma mempty_dec {A} (m : M.t A) : {M.Empty m} + {~ M.Empty m}.
Proof.
  destruct (eq_dec (M.cardinal m) 0).
  - strivial use: WP.cardinal_Empty.
  - right.
    assert ((M.cardinal m > 0)%nat) by sfirstorder.
    sfirstorder use: WP.cardinal_1.
Defined.

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
  
(** The subgraphs created by the extraction are a subgraph series; *)

Lemma extract_vertices_deg_series g n :
  subgraph_series (map snd (fst (extract_vertices_deg g n))).
Proof.
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

(** ** Subgraph respects degree of vertices. *)

Lemma degree_subgraph (g g': graph) v n m :
  is_subgraph g g' -> degree v g = Some n -> degree v g' = Some m -> n <= m.
Proof.
  hfcrush use: SP.subset_cardinal unfold: degree, adj, nodeset, is_subgraph.
Qed.

(** If a vertex is extracted by [extract_vertices_deg] then the degree
    is at least [n] in the original graph. *)
Lemma extract_vertices_inv (g g' : graph) n m v :
  In (v,g') (fst (extract_vertices_deg g n)) -> degree v g = Some m -> n <= m .
Proof.
  (* prove this by knowing that g' is a subgraph of g *)
  intros H H1.
  assert (is_subgraph g' g).
  {
    pose proof (extract_vertices_deg_series g n).
    remember (map snd (fst (extract_vertices_deg g n))) as l.
    induction l eqn:E.
    - exfalso.
      destruct (fst (extract_vertices_deg g n)); scongruence.
    - admit.
  }
  rewrite extract_vertices_deg_equation in H.
  destruct (extract_deg_vert_dec g n) eqn:He.
  - destruct (extract_vertices_deg (remove_node (` s) g) n).
    simpl in H.
    (* ok need to perform induction on the list and have a lemma about
       the degree of the vertex at each point having degree n
       (wrt. the graph at that point) *)
Admitted.

(** ** The final graph returned by the vertex extraction is a subgraph. *)

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
  max_deg g = 0 -> M.Empty (snd (extract_vertices_deg g 0)).
Proof.
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
    unfold degree in *.
    apply H0.
    destruct H5 as [v [[e He] Hv2]].
    exists v.
    rewrite He.
    unfold adj in Hv2.
    rewrite He in Hv2.
    scongruence.
Qed.

(** ** Non-adjacency of max degree vertices after one step *)
(** If a vertex of max degree is removed from a graph then any vertex
    with max degree in the new graph cannot be adjacent to it. *)

Lemma remove_max_deg_adj : forall (g : graph) (i j : node) (d : nat),
    (d > 0)%nat ->
    undirected g ->
    no_selfloop g ->
    max_deg g = d ->
    M.In i g ->
    M.In j g ->
    degree j g = Some d ->
    degree j (remove_node i g) = Some d ->
    ~ (S.In j (adj g i)).
Proof.
  intros g i j d H H0 H1 H2 H3 H4 H5 H6 contra.
  destruct d; [inversion H|clear H].
  assert (degree j (remove_node i g) = Some d) by (now apply vertex_removed_nbs_dec).
  qauto use: le_ngt, le_refl unfold: Peano.lt.
Qed.


(** ** Non-adjacency of max degree vertices after arbitrary steps *)
(** If two vertices [i], [j] occur in the list of max degree vertices
    extracted from the graph, then [i] is not adjacent to [j] *)

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
