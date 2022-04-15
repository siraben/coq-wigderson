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
  unfold subgraph_of.
  unfold S.Subset.
  intros a H.
  induction g.
  - sfirstorder.
  - pose proof M.fold_1.
    pose proof fold_right_rev_left.

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

(* A subgraph of a graph is colorable under the same coloring *)
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
  (* Let g be a graph and v a vertex. *)
  intros g v.
  unfold three_colorable.
  unfold two_colorable.
  unfold neighborhood.
  intros [f Hf].
  (* The coloring function we use is the same *)
  exists f.
  unfold coloring_ok in *.
  (* Let i be a vertex and j an adjacent vertex in the neighborhood of i. *)
  intros i j H.
  split.
  - (* Want to show that the *)
    intros ci Hci.
    pose proof (Hf i j).
    admit.
  - admit.
Admitted.

Definition injective {A B} (f : A -> B) := forall x y, f x = f y -> x = y.

Inductive two := N | M.
Inductive three := N' | M' | P'.

Require Import Program.

Program Definition three_to_two : forall {A} (f : A -> three) (p : {y | forall x, f x <> y}),
  {p : (two -> three) * (A -> two) | let (i,c) := p in forall x, i (c x) = f x} :=
  fun A f y =>
    (* y is the value not reached by f *)
    (* want to create an injection that agrees on f *)
    match y with
    | N' => exist _ (fun (x : two) =>
                      match x with
                      | N => P'
                      | M => M'
                      end,
                      (fun (a : A) =>
                         match f a with
                         | N' => _
                         | M' => M
                         | P' => N
                         end)) ltac:(hauto)
    | M' => exist _ (fun (x : two) =>
                      match x with
                      | N => N'
                      | M => P'
                      end,
                      (fun (a : A) =>
                         match f a with
                         | N' => N
                         | M' => _
                         | P' => M
                         end)) ltac:(hauto)
    | P' => exist _ (fun (x : two) =>
                      match x with
                      | N => N'
                      | M => M'
                      end,
                      (fun (a : A) =>
                         match f a with
                         | N' => N
                         | M' => M
                         | P' => _
                         end)) ltac:(hauto)
    end.

Definition example_f (b : bool) : three := if b then N' else M'.

Definition f_restricted_pair :=
  proj1_sig (three_to_two example_f ltac:(exists P'; hauto unfold: example_f q: on)).

Compute (let (i, c) := f_restricted_pair in (c true, c false, i (c true), i (c false))).
     (* = (N, M, N', M') *)
     (* : two * two * three * three *)

