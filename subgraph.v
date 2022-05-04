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

(* The neighbors of a vertex v in a graph g. *)
Definition neighbors (g : graph) v := adj g v.

(* Subgraph induced by a set of vertices *)
Definition subgraph_of (g : graph) (s : S.t) :=
  M.fold (fun v adj g' => if S.mem v s then M.add v (S.filter (fun u => S.mem u s) adj) g' else g') g empty_graph.

(* g' is a subgraph of g if:
- the vertex set of g' is a subset of the vertex set of g
- for every vertex v in g', the 
 *)
Definition is_subgraph (g' g : graph) :=
  (S.Subset (nodes g') (nodes g)) /\ (forall v, S.Subset (adj g' v) (adj g v)).



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
      * unfold nodes in *.
        unfold S.Subset in H1.
        assert (S.In a' (Mdomain m')).
        {
          hauto l: on use: WP.F.add_neq_in_iff, Sin_domain.
        }
        hauto lq: on rew: off use: WP.F.add_neq_in_iff, Sin_domain.
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
        rewrite PositiveMap.gss in *.
        strivial use: PositiveSet.xfilter_spec unfold: PositiveSet.elt, PositiveSet.filter.
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

(* An induced subgraph of an undirected graph is undirected. *)
Lemma subgraph_of_undirected : forall g s, undirected g -> undirected (subgraph_of g s).
Proof.
Admitted.
  
(* A subgraph of a graph is colorable under the same coloring *)
Lemma subgraph_colorable : forall (g g' : graph) f p,
    undirected g ->
    is_subgraph g' g ->
    coloring_ok p g f ->
    coloring_ok p g' f.
Proof.
  intros g g' f p H H0 H1.
  hfcrush use: subgraph_of_is_subgraph unfold: is_subgraph, PositiveSet.Subset, coloring_ok, undirected.
Qed.

Definition remove_subgraph (g : graph) s :=
  M.fold (fun v e m' => if S.mem v s then m' else M.add v (S.diff e s) m') (@M.empty _) g.

Lemma remove_subgraph_is_subgraph : forall g s, is_subgraph (remove_subgraph g s) g.
Proof.
  intros g s.
  split.
  - unfold remove_subgraph.
    apply WP.fold_rec_bis.
    + hauto lq: on.
    + scongruence.
    + sauto q: on.
  - unfold remove_subgraph.
    apply WP.fold_rec_bis.
    + hauto lq: on.
    + scongruence.
    + intros k e a m' H H0 H1 v.
      sauto q: on.
Qed.

(* Removing a subgraph preserves undirectedness *)
Lemma remove_subgraph_undirected : forall g s, undirected g -> undirected (remove_subgraph g s).
Proof.
  hauto q: on.
Qed.
