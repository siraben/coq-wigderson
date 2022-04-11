Require Import graph.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
From Hammer Require Import Tactics.
Import Arith.
Import ListNotations.
Import Nat.

(* Predicate that takes a vertex with high degree (> sqrt K) *)
Definition high_deg (K: nat) (n: node) (adj: nodeset) : bool := sqrt K <? S.cardinal adj.

Print coloring.

Definition two_colors: S.t := fold_right S.add S.empty [1; 2]%positive.
Definition three_colors: S.t := fold_right S.add S.empty [1; 2; 3]%positive.

(* A graph is bipartite if it is 2-colorable. *)
Definition two_colorable (g : graph) := exists f, coloring_ok two_colors g f.

Definition empty_graph := mk_graph [].

(* The neighbors of a vertex v in a graph g. *)
Definition neighbors (g : graph) v := S.remove v (adj g v).
Check neighbors.

(* Subgraph induced by a set of vertices *)
Definition subgraph_of (g : graph) (s : nodeset) :=
  M.fold (fun v adj g' => if S.mem v s then M.add v (S.filter (fun u => S.mem u s) adj) g' else g') g empty_graph.

Check subgraph_of.

Definition vertices := nodes.
Lemma subgraph_vertices_subset : forall g s, S.Subset (nodes (subgraph_of g s)) (nodes g).
Proof.
  intros g s.
  induction g.
  - cbn. apply S.subset_2. reflexivity.
  - pose proof S.subset_1.
    pose proof S.subset_2.
    pose proof M.fold_1.
    pose proof fold_right_rev_left.
    pose proof S.subset.
Admitted.

(* The (open) neighborhood of a vertex v in a graph consists of the
   subgraph induced by the vertices adjacent to v.  It does not
   include v itself. *)
Definition neighborhood (g : graph) v := remove_node v (subgraph_of g (neighbors g v)).

(* Neighborhoods do not include their vertex *)
Lemma nbd_not_include_vertex g v : M.find v (neighborhood g v) = None.
Proof.
  hecrush use: WF.map_o use: M.grs.
Qed.

(* Definition of a 3-colorable graph *)
Definition three_colorable (g : graph) := exists f, coloring_ok three_colors g f.

Example ex_graph :=
  mk_graph [ (6,4); (4,5); (4,3); (3,2); (5,2); (1,2); (1,5) ]%positive.

Local Open Scope positive_scope.
Compute (M.fold (fun k u y => (k,S.elements u) :: y) ex_graph []).
Compute (M.fold (fun k u y => (k,S.elements u) :: y) (neighborhood ex_graph 5%positive) []).

(* Example of 3-coloring the example graph and proof with ok_coloring *)
Example ex_coloring :=
  fold_right (fun p m => M.add (fst p) (snd p) m) (@M.empty _) [(6,1);(3,1);(5,1);(4,2);(2,2);(1,3)].

(* Proving that an explicit graph coloring is a valid coloring *)
Example ex_coloring_good : coloring_ok three_colors ex_graph ex_coloring.
Proof.
  split; sblast use: M.elements_correct.
Qed.

(* For a vertex i in a nodeset, the subgraph induced by the nodeset
   contains i if and only if vertex i was in the original graph. *)
Lemma subgraph_induced_find : forall i g s, S.In i s -> M.find i (subgraph_of g s) = M.find i g.
Proof.
  intros i g s Hi.
  destruct (M.find i g) eqn:E.
  - unfold subgraph_of.
Admitted.

(* A subgraph of a graph is colorable *)
Lemma subgraph_colorable : forall (g : graph) p f s, coloring_ok f g p -> coloring_ok f (subgraph_of g s) p.
Proof.
  intros g p f s H.
  unfold coloring_ok in *.
  intros i j H0.
  split.
  - assert (S.In j (adj g i)).
    {
      pose proof (subgraph_vertices_subset g s).
      admit.
    }
    pose proof (H i j H1).
    intros ci H3.
    firstorder.
  - admit.
Admitted.


(* In a 3-colorable graph, the neighborhood of any vertex is 2-colorable. *)
Lemma nbd_2_colorable :
  forall (g : graph) v, three_colorable g -> two_colorable (neighborhood g v).
Proof.
  intros g v.
  unfold three_colorable.
  unfold two_colorable.
  unfold neighborhood.
  intros [f Hf].
  exists f.
  unfold coloring_ok in *.
  intros i j H.
  split.
  - intros ci Hci.
    pose proof (Hf i j).
    admit.
  - admit.
Admitted.
