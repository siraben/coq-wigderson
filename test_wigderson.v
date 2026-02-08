Require Import graph.
Require Import coloring.
Require Import wigderson.
Require Import subgraph.
Require Import List.
Require Import FSets.
Require Import FMaps.
Require Import PArith.
Import ListNotations.

Local Open Scope positive_scope.

(* ===== Test Graphs ===== *)

(* Graph 1: Triangle (K3) - simplest 3-colorable graph
   1 -- 2 -- 3 -- 1 *)
Definition g_triangle :=
  mk_graph [(1,2); (2,3); (3,1)].

(* Graph 2: Path P4: 1-2-3-4 (bipartite, 2-colorable) *)
Definition g_path4 :=
  mk_graph [(1,2); (2,3); (3,4)].

(* Graph 3: Cycle C5 (odd cycle, 3-colorable but not 2-colorable)
   1-2-3-4-5-1 *)
Definition g_c5 :=
  mk_graph [(1,2); (2,3); (3,4); (4,5); (5,1)].

(* Graph 4: The existing example graph from coloring.v
   Edges: 6-4, 4-5, 4-3, 3-2, 5-2, 1-2, 1-5 *)
Definition g_example := ex_graph.

(* Graph 5: Complete bipartite K_{2,3}: {1,2} x {3,4,5}
   Edges: 1-3,1-4,1-5,2-3,2-4,2-5 *)
Definition g_k23 :=
  mk_graph [(1,3); (1,4); (1,5); (2,3); (2,4); (2,5)].

(* Graph 6: Petersen-like subgraph (3-colorable)
   A star with center 1 connected to 2,3,4,5
   plus edges 2-3, 4-5 *)
Definition g_star_plus :=
  mk_graph [(1,2); (1,3); (1,4); (1,5); (2,3); (4,5)].

(* ===== Complex Test Graphs ===== *)

(* Graph 7: Cycle C7 (odd cycle, 3-chromatic) *)
Definition g_c7 :=
  mk_graph [(1,2);(2,3);(3,4);(4,5);(5,6);(6,7);(7,1)].

(* Graph 8: Petersen graph (3-chromatic, 10 vertices, 15 edges)
   Outer cycle: 1-2-3-4-5-1
   Inner pentagram: 6-8-10-7-9-6
   Spokes: 1-6, 2-7, 3-8, 4-9, 5-10 *)
Definition g_petersen :=
  mk_graph [
    (1,2);(2,3);(3,4);(4,5);(5,1);
    (6,8);(8,10);(10,7);(7,9);(9,6);
    (1,6);(2,7);(3,8);(4,9);(5,10)
  ].

(* Graph 9: Cube graph Q3 (bipartite, 2-chromatic, 8 vertices, 12 edges) *)
Definition g_cube :=
  mk_graph [
    (1,2);(2,3);(3,4);(4,1);
    (5,6);(6,7);(7,8);(8,5);
    (1,5);(2,6);(3,7);(4,8)
  ].

(* Graph 10: Wheel W7 (center 1, rim 2-3-4-5-6-7-2, 3-chromatic since rim is even) *)
Definition g_wheel7 :=
  mk_graph [
    (2,3);(3,4);(4,5);(5,6);(6,7);(7,2);
    (1,2);(1,3);(1,4);(1,5);(1,6);(1,7)
  ].

(* Graph 11: Grotzsch graph (triangle-free, 4-chromatic, 11 vertices, 20 edges)
   Outer: 1-2-3-4-5-1, Inner: 6-10, Center: 11 *)
Definition g_grotzsch :=
  mk_graph [
    (1,2);(2,3);(3,4);(4,5);(5,1);
    (6,2);(6,3);(7,3);(7,4);(8,4);(8,5);
    (9,5);(9,1);(10,1);(10,2);
    (11,6);(11,7);(11,8);(11,9);(11,10)
  ].

(* Graph 12: Grid 3x3 (bipartite, 2-chromatic, 9 vertices, 12 edges) *)
Definition g_grid3x3 :=
  mk_graph [
    (1,2);(2,3);(4,5);(5,6);(7,8);(8,9);
    (1,4);(4,7);(2,5);(5,8);(3,6);(6,9)
  ].

(* Graph 13: K_{3,3} (complete bipartite, 2-chromatic, 6 vertices, 9 edges) *)
Definition g_k33 :=
  mk_graph [
    (1,4);(1,5);(1,6);(2,4);(2,5);(2,6);(3,4);(3,5);(3,6)
  ].

(* Graph 14: Dodecahedron (3-chromatic, 20 vertices, 30 edges) *)
Definition g_dodecahedron :=
  mk_graph [
    (1,2);(2,3);(3,4);(4,5);(5,1);
    (1,6);(2,7);(3,8);(4,9);(5,10);
    (6,11);(6,15);(7,11);(7,12);(8,12);(8,13);
    (9,13);(9,14);(10,14);(10,15);
    (11,16);(12,17);(13,18);(14,19);(15,20);
    (16,17);(17,18);(18,19);(19,20);(20,16)
  ].

(* Graph 15: Two triangles sharing a vertex (bowtie, 3-chromatic) *)
Definition g_bowtie :=
  mk_graph [(1,2);(2,3);(3,1);(3,4);(4,5);(5,3)].

(* Graph 16: Octahedron = K_{2,2,2} (3-chromatic, 6 vertices, 12 edges) *)
Definition g_octahedron :=
  mk_graph [
    (1,3);(1,4);(1,5);(1,6);
    (2,3);(2,4);(2,5);(2,6);
    (3,5);(3,6);(4,5);(4,6)
  ].

(* Graph 17: Path P10 (bipartite, 2-chromatic, 10 vertices) *)
Definition g_path10 :=
  mk_graph [(1,2);(2,3);(3,4);(4,5);(5,6);(6,7);(7,8);(8,9);(9,10)].

(* ===== Helper: extract coloring as list of (node, color) pairs ===== *)
Definition coloring_to_list (f : coloring) : list (positive * positive) :=
  M.elements f.

(* ===== Compute Wigderson on each graph ===== *)
(* Using k=1 means any vertex with degree > 1 is "high degree" *)

Eval compute in (coloring_to_list (wigderson 1 g_triangle)).
Eval compute in (coloring_to_list (wigderson 1 g_path4)).
Eval compute in (coloring_to_list (wigderson 1 g_c5)).
Eval compute in (coloring_to_list (wigderson 1 g_example)).
Eval compute in (coloring_to_list (wigderson 1 g_k23)).
Eval compute in (coloring_to_list (wigderson 1 g_star_plus)).

(* Also try with k=2 (high degree means degree > 2) *)
Eval compute in (coloring_to_list (wigderson 2 g_triangle)).
Eval compute in (coloring_to_list (wigderson 2 g_c5)).
Eval compute in (coloring_to_list (wigderson 2 g_example)).
Eval compute in (coloring_to_list (wigderson 2 g_star_plus)).

(* ===== Complex graphs with k=1 ===== *)
Eval compute in (coloring_to_list (wigderson 1 g_c7)).
Eval compute in (coloring_to_list (wigderson 1 g_petersen)).
Eval compute in (coloring_to_list (wigderson 1 g_cube)).
Eval compute in (coloring_to_list (wigderson 1 g_wheel7)).
Eval compute in (coloring_to_list (wigderson 1 g_grotzsch)).
Eval compute in (coloring_to_list (wigderson 1 g_grid3x3)).
Eval compute in (coloring_to_list (wigderson 1 g_k33)).
Eval compute in (coloring_to_list (wigderson 1 g_bowtie)).
Eval compute in (coloring_to_list (wigderson 1 g_octahedron)).
Eval compute in (coloring_to_list (wigderson 1 g_path10)).
Eval compute in (coloring_to_list (wigderson 1 g_dodecahedron)).

(* ===== Complex graphs with k=2 ===== *)
Eval compute in (coloring_to_list (wigderson 2 g_c7)).
Eval compute in (coloring_to_list (wigderson 2 g_petersen)).
Eval compute in (coloring_to_list (wigderson 2 g_cube)).
Eval compute in (coloring_to_list (wigderson 2 g_wheel7)).
Eval compute in (coloring_to_list (wigderson 2 g_grotzsch)).
Eval compute in (coloring_to_list (wigderson 2 g_grid3x3)).
Eval compute in (coloring_to_list (wigderson 2 g_k33)).
Eval compute in (coloring_to_list (wigderson 2 g_bowtie)).
Eval compute in (coloring_to_list (wigderson 2 g_octahedron)).
Eval compute in (coloring_to_list (wigderson 2 g_path10)).
Eval compute in (coloring_to_list (wigderson 2 g_dodecahedron)).

(* ===== Verify each coloring is valid by computation ===== *)

(* Helper: check all edges have different colors *)
Definition check_edge (f : coloring) (i j : positive) : bool :=
  match M.find i f, M.find j f with
  | Some ci, Some cj => negb (Pos.eqb ci cj)
  | _, _ => false (* uncolored vertex = failure *)
  end.

Definition check_edges (f : coloring) (edges : list (positive * positive)) : bool :=
  forallb (fun e => check_edge f (fst e) (snd e)) edges.

(* Triangle *)
Eval compute in (check_edges (wigderson 1 g_triangle) [(1,2);(2,3);(3,1)]).
(* Path *)
Eval compute in (check_edges (wigderson 1 g_path4) [(1,2);(2,3);(3,4)]).
(* C5 *)
Eval compute in (check_edges (wigderson 1 g_c5) [(1,2);(2,3);(3,4);(4,5);(5,1)]).
(* Example *)
Eval compute in (check_edges (wigderson 1 g_example) [(6,4);(4,5);(4,3);(3,2);(5,2);(1,2);(1,5)]).
(* K23 *)
Eval compute in (check_edges (wigderson 1 g_k23) [(1,3);(1,4);(1,5);(2,3);(2,4);(2,5)]).
(* Star plus *)
Eval compute in (check_edges (wigderson 1 g_star_plus) [(1,2);(1,3);(1,4);(1,5);(2,3);(4,5)]).

(* ===== Complex graph edge checks (k=1) ===== *)

Definition c7_edges := [(1,2);(2,3);(3,4);(4,5);(5,6);(6,7);(7,1)].
Definition petersen_edges := [(1,2);(2,3);(3,4);(4,5);(5,1);
  (6,8);(8,10);(10,7);(7,9);(9,6);(1,6);(2,7);(3,8);(4,9);(5,10)].
Definition cube_edges := [(1,2);(2,3);(3,4);(4,1);(5,6);(6,7);(7,8);(8,5);
  (1,5);(2,6);(3,7);(4,8)].
Definition wheel7_edges := [(2,3);(3,4);(4,5);(5,6);(6,7);(7,2);
  (1,2);(1,3);(1,4);(1,5);(1,6);(1,7)].
Definition grotzsch_edges := [(1,2);(2,3);(3,4);(4,5);(5,1);
  (6,2);(6,3);(7,3);(7,4);(8,4);(8,5);(9,5);(9,1);(10,1);(10,2);
  (11,6);(11,7);(11,8);(11,9);(11,10)].
Definition grid3x3_edges := [(1,2);(2,3);(4,5);(5,6);(7,8);(8,9);
  (1,4);(4,7);(2,5);(5,8);(3,6);(6,9)].
Definition k33_edges := [(1,4);(1,5);(1,6);(2,4);(2,5);(2,6);(3,4);(3,5);(3,6)].
Definition bowtie_edges := [(1,2);(2,3);(3,1);(3,4);(4,5);(5,3)].
Definition octahedron_edges := [(1,3);(1,4);(1,5);(1,6);(2,3);(2,4);(2,5);(2,6);
  (3,5);(3,6);(4,5);(4,6)].
Definition path10_edges := [(1,2);(2,3);(3,4);(4,5);(5,6);(6,7);(7,8);(8,9);(9,10)].
Definition dodecahedron_edges := [(1,2);(2,3);(3,4);(4,5);(5,1);
  (1,6);(2,7);(3,8);(4,9);(5,10);
  (6,11);(6,15);(7,11);(7,12);(8,12);(8,13);
  (9,13);(9,14);(10,14);(10,15);
  (11,16);(12,17);(13,18);(14,19);(15,20);
  (16,17);(17,18);(18,19);(19,20);(20,16)].

(* k=1 checks *)
Eval compute in (check_edges (wigderson 1 g_c7) c7_edges).
Eval compute in (check_edges (wigderson 1 g_petersen) petersen_edges).
Eval compute in (check_edges (wigderson 1 g_cube) cube_edges).
Eval compute in (check_edges (wigderson 1 g_wheel7) wheel7_edges).
Eval compute in (check_edges (wigderson 1 g_grotzsch) grotzsch_edges).
Eval compute in (check_edges (wigderson 1 g_grid3x3) grid3x3_edges).
Eval compute in (check_edges (wigderson 1 g_k33) k33_edges).
Eval compute in (check_edges (wigderson 1 g_bowtie) bowtie_edges).
Eval compute in (check_edges (wigderson 1 g_octahedron) octahedron_edges).
Eval compute in (check_edges (wigderson 1 g_path10) path10_edges).
Eval compute in (check_edges (wigderson 1 g_dodecahedron) dodecahedron_edges).

(* k=2 checks *)
Eval compute in (check_edges (wigderson 2 g_c7) c7_edges).
Eval compute in (check_edges (wigderson 2 g_petersen) petersen_edges).
Eval compute in (check_edges (wigderson 2 g_cube) cube_edges).
Eval compute in (check_edges (wigderson 2 g_wheel7) wheel7_edges).
Eval compute in (check_edges (wigderson 2 g_grotzsch) grotzsch_edges).
Eval compute in (check_edges (wigderson 2 g_grid3x3) grid3x3_edges).
Eval compute in (check_edges (wigderson 2 g_k33) k33_edges).
Eval compute in (check_edges (wigderson 2 g_bowtie) bowtie_edges).
Eval compute in (check_edges (wigderson 2 g_octahedron) octahedron_edges).
Eval compute in (check_edges (wigderson 2 g_path10) path10_edges).
Eval compute in (check_edges (wigderson 2 g_dodecahedron) dodecahedron_edges).
