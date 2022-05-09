Require Import graph.
Require Import subgraph.
Require Import coloring.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
Require Import FunInd.
Require Import restrict.
Require Import munion.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
Import Arith.
Import ListNotations.
Import Nat.


(* Predicate that takes a vertex with high degree (> K) *)
Definition high_deg (K: nat) (n: node) (adj: nodeset) : bool := K <? S.cardinal adj.

Definition injective {A B} (f : A -> B) := forall x y, f x = f y -> x = y.

Local Open Scope positive_scope.


(* Wigderson's algorithm definition

let G be a graph, |G.v| = k
a vertex v is high-degree if deg(v) > k^2
phase1 is selecting the high-degree vertices and coloring their neighborhoods
phase2 is coloring the remaining nodes with at most sqrt(k) colors
 *)

Lemma selectW_terminates:
  forall (K: nat) (g : graph) (n : S.elt),
   S.choose (subset_nodes (high_deg K) g) = Some n ->
   (M.cardinal (remove_node n g) < M.cardinal g)%nat.
Proof.
  intros K g n H.
  unfold remove_node.
  assert (~ M.In n (remove_node n g)).
  {
    strivial use: remove_node_neq2 unfold: PositiveOrderedTypeBits.t, PositiveMap.key, PositiveSet.elt, node.
  }
  assert (M.In n g).
  {
    assert (S.In n (subset_nodes (high_deg K) g)).
    {
      hauto l: on use: S.choose_1.
    }
    pose proof (subset_nodes_sub (high_deg K) g n H1).
    unfold nodes, Mdomain in H2.
    now apply Sin_domain in H2.
  }
  rewrite cardinal_map.
  now apply Mremove_cardinal_less.
Qed.

Function selectW (K: nat) (g: graph) {measure M.cardinal g} : list node :=
  match S.choose (subset_nodes (high_deg K) g) with
  | Some n => n :: selectW K (remove_node n g)
  | None => nil
  end.
Proof. apply selectW_terminates.
Defined.

Lemma subset_nodes_prop : forall (P: node -> nodeset -> bool) (g: graph) v,
    S.In v (subset_nodes P g) -> P v (adj g v) = true.
Proof.
  intros P g v H.
  unfold subset_nodes in H.
  apply Sin_domain in H.
  destruct H as [e He].
  epose proof (@WP.filter_iff _ P _ g v e).
  rewrite H in He.
  unfold adj.
  sauto.
Qed.

(* If a node m is removed from the graph then the cardinality of the
  adj set of a vertex v is decreasing. *)
Lemma cardinal_remove : forall g v m,
    (S.cardinal (adj (remove_node m g) v) <= S.cardinal (adj g v))%nat.
Proof.
  intros g v m.
  unfold adj.
  destruct (WF.In_dec g v).
  - ssimpl.
    subst.
    unfold nodeset, node, remove_node in *.
    assert (n0 = x) by scongruence.
    subst.
    (* Note: why is this not more automatic *)
    destruct (E.eq_dec v m).
    + ecrush use: map_o, M.grs.
    + unfold nodeset in *.
      rewrite map_o, M.gro in Heqo by auto.
      qauto use: SP.subset_cardinal, PositiveSet.remove_3 unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, option_map, PositiveSet.Subset.
  - hauto lq: on use: remove_node_subgraph, SP.subset_cardinal unfold: PositiveMap.In, PositiveSet.t, is_subgraph, nodeset, PositiveMap.MapsTo, PositiveSet.Subset, adj inv: option.
Qed.

(* If v is in the list returned by selectW then the cardinality of v is indeed high. *)
Lemma select_hi_deg : forall n g v, In v (selectW n g) -> (S.cardinal (adj g v) > n)%nat.
Proof.
  intros n g v.
  functional induction (selectW n g) using selectW_ind.
  - intros H.
    destruct H.
    + subst.
      clear IHl.
      assert (S.In v (subset_nodes (high_deg n) g)).
      {
        hauto q: on use: PositiveSet.choose_1 inv: option.
      }
      hauto lqb: on drew: off use: subset_nodes_prop unfold: high_deg.
    + specialize (IHl H).
      strivial use: le_gt_trans, cardinal_remove unfold: PositiveOrderedTypeBits.t, PositiveSet.elt, PositiveSet.t, adj, node, nodeset, PositiveSet.empty.
  - sfirstorder.
Qed.

(* Phase 1 of Wigderson *)
(* Let:
- k: bound for degree of vertices
- c: color currently used
- g: graph
- f: coloring
- H: proof that g is 3-colorable
- H1: proof that f is a complete coloring of g
- Hf: proof that f is a 3-coloring

phase1(g,c):
  if a high degree vertex in g exists:
    v := select a high-degree vertex in g
    nbhd := neighborhood of v in g
    coloring_of_nbhd := 2-coloring of nbhd using c+1 and c+2
    g' := remove nbhd from g
    return union(coloring_of_nbhd, phase1(g',c+2))
  else:
    return empty coloring

 *)
Require Import Program.

(* Two-coloring of neighborhood *)
Definition two_color_nbd (g : graph) (v : node) (c1 c2 : positive) : option coloring.
Admitted.

(* Two coloring of a neighborhood of a 3-colorable graph is complete *)
(* Let c1, c2, c3 be distinct colors.  Assume the graph can be
   3-colored and that in this 3-coloring the vertex v has color c3,
   and that the coloring is complete. Then two_color_nbd colors the
   neighborhood of v correctly with two colors. *)
Lemma two_color_nbd_complete : forall (g : graph) (v : node) c1 c2 c3 m,
    c1 <> c2 ->
    c1 <> c3 ->
    c2 <> c3 ->
    no_selfloop g ->
    undirected g ->
    M.In v g ->
    (exists m, M.find v m = Some c3 /\ coloring_complete (SP.of_list [c1;c2;c3]) g m) ->
    two_color_nbd g v c1 c2 = Some m ->
    coloring_complete (SP.of_list [c1;c2]) (subgraph_of g (nodes (neighborhood g v))) m.
Proof.
Admitted.

Lemma two_color_nbd_fail_n3_col : forall (g : graph) (v : node) c1 c2 c3,
    c1 <> c2 ->
    c1 <> c3 ->
    c2 <> c3 ->
    no_selfloop g ->
    undirected g ->
    M.In v g ->
    two_color_nbd g v c1 c2 = None ->
    ~ (exists m, M.find v m = Some c3 /\ coloring_complete (SP.of_list [c1;c2;c3]) g m).
Proof.
Admitted.
  
Program Fixpoint phase1
  (* The criterion for high-degree vertices *)
  (k : nat)
  (* Current color count *)
  (c : positive)
  (g : graph) {measure (M.cardinal g)} : coloring :=
  (* Choose a high-degree vertex *)
  match S.choose (subset_nodes (high_deg k) g) with
  | Some v =>
      let nbhd := neighborhood g v in
      (* i is the map that turns the coloring using colors 1,2 into c+1, c+2 *)
      let coloring_of_nbhd := two_color_nbd g c (c+1) v in
      let g' := remove_nodes g (nodes nbhd) in
      (* color the high-degree vertex 1 each time *)
      Munion (M.add v 1 coloring_of_nbhd) (phase1 k (c+2) g')
  | None => (@M.empty _)
  end.
Next Obligation.
Admitted.

Functional Scheme phase1_ind := Induction for phase1 Sort Prop.

(* things we want to prove:
 - let d be the number of iterations
 - prove that the resulting color uses 2d+1 colors
   - induction on size of graph
   - two new colors each time
   - base case: no more high degree vertices, color with phase2
 - there are no more high-degree nodes (this is the hypothesis for phase2)
 - need to identify the terminal properties for phase1 to supply to phase2
 *)
(* induction on M.cardinal g *)
Check phase1.
(* Lemmas:
- you can color any graph with max degree + 1 colors
- can prove 3*(sqrt n) + 1
 *)



(* Some notes about how the algorithm will be written:

- we will not pass proofs that the graph is 3-colorable all the time,
  since later we want to talk about robustness

- we want to break down algorithm enough to reason about the graph and
  the coloring at each step while still making the overall algorithm
  clear

- an important lemma we will use repeatedly is that we can combine OK
  disjoint colorings into larger colorings, and that the number of
  colors used is the size of the palette

- to show that the coloring is complete, we show that a vertex must be
  one of the following:

1) a high-degree vertex, in which case it's colored by phase 1
2) a neighbor of a high-degree vertex, in which case it's colored by phase 1
3) a low-degree vertex, in which case it's colored by phase 2
 *)

(*
We define phase 1 of the algorithm in several pieces:

two_color_step takes:
  - a graph g
  - a high-degree vertex v
  - the current color number c
two_color_step outputs:
  - a complete coloring of N(v) using colors c+1, c+2
note:
  - phase 1 will color v with c
  - the expectation is that two_color_step will be called with another
    vertex and c+2

so phase 1 will fold over the list of high-degree vertices Lv and do:
- the state of the fold will be (c,m), where c is a number and m is the coloring
- call two_color_step on each vertex to produce the coloring and update m
- update c to c+2

we will have to show that:

- the resulting tuple will be (d,m), where d is the number of high-degree
  vertices and m is the coloring of all the neighborhoods of high-degree vertices
- d*d <= k
- the number of colors used is 2*d

random lemmas that we have to show:
- it's decidable to check whether a node is colored or not (WF.In_Dec)
- the number of high-degree vertices cannot exceed sqrt(k)
 *)

(* Lifting two color maps with any injective function *)
Lemma two_color_up_inj f g (inj : S.elt -> S.elt) :
  injective inj ->
  undirected g ->
  coloring_ok two_colors g f ->
  {h | coloring_ok (fold_right S.add S.empty [inj 1;inj 2]) g h}.
Proof.
  intros Hm Ug Hf.
  exists (M.map inj f).
  intros v.
  split.
  - intros ci Hv.
    assert (M.In v f) by hauto l: on use: M.map_2.
    destruct H0 as [cj Hcj].
    unfold M.MapsTo in Hcj.
    assert (ci = inj 1 \/ ci = inj 2).
    {
      unfold coloring_ok in Hf.
      pose proof (map_o f v inj).
      assert (Some ci = option_map inj (M.find v f)) by qauto l: on.
      sauto q: on.
    }
    destruct H0; hauto use: PositiveSet.add_2, PositiveSet.add_1 unfold: PositiveSet.elt.
  - intros ci cj Hci Hcj.
    assert (M.In v f) by hauto l: on use: M.map_2.
    assert (M.In j f) by hauto l: on use: M.map_2.
    destruct H0 as [ci' Hci'].
    destruct H1 as [cj' Hcj'].
    unfold M.MapsTo in *.
    assert (Some ci = option_map inj (M.find v f)) by sauto lq: on use: map_o.
    assert (Some cj = option_map inj (M.find j f)) by sauto lq: on use: map_o.
    pose proof (proj2 (Hf v j H) ci' cj' Hci' Hcj').
    assert (ci' = 1 \/ ci' = 2).
    {
      pose proof (proj1 (Hf _ _ H) _ Hci').
      sauto.
    }
    (* Here we use the fact that the graph is undirected so we can
       go from j being adjacent to v to v being adjacent to j. *)
    assert (cj' = 1 \/ cj' = 2).
    {
      pose proof (proj1 (Hf _ _ (Ug _ _ H)) _ Hcj').
      sauto.
    }
    sauto.
Qed.

(* Lifting three color maps *)
Lemma three_color_up_inj f g (inj : S.elt -> S.elt) :
  injective inj ->
  undirected g ->
  coloring_ok three_colors g f ->
  {h | coloring_ok (fold_right S.add S.empty [inj 1;inj 2;inj 3]) g h}.
Proof.
  intros Hm Ug Hf.
  exists (M.map inj f).
  intros v.
  split.
  - intros ci Hv.
    assert (M.In v f) by hauto l: on use: M.map_2.
    destruct H0 as [cj Hcj].
    unfold M.MapsTo in Hcj.
    assert (ci = inj 1 \/ ci = inj 2 \/ ci = inj 3).
    {
      unfold coloring_ok in Hf.
      pose proof (map_o f v inj).
      assert (Some ci = option_map inj (M.find v f)) by qauto l: on.
      sauto q: on.
    }
    destruct H0; hauto use: PositiveSet.add_2, PositiveSet.add_1 unfold: PositiveSet.elt.
  - intros ci cj Hci Hcj.
    assert (M.In v f) by hauto l: on use: M.map_2.
    assert (M.In j f) by hauto l: on use: M.map_2.
    destruct H0 as [ci' Hci'].
    destruct H1 as [cj' Hcj'].
    unfold M.MapsTo in *.
    assert (Some ci = option_map inj (M.find v f)) by sauto lq: on use: map_o.
    assert (Some cj = option_map inj (M.find j f)) by sauto lq: on use: map_o.
    pose proof (proj2 (Hf v j H) ci' cj' Hci' Hcj').
    assert (ci' = 1 \/ ci' = 2 \/ ci' = 3).
    {
      pose proof (proj1 (Hf _ _ H) _ Hci').
      sauto.
    }
    (* Here we use the fact that the graph is undirected so we can
       go from j being adjacent to v to v being adjacent to j. *)
    assert (cj' = 1 \/ cj' = 2 \/ cj' = 3).
    {
      pose proof (proj1 (Hf _ _ (Ug _ _ H)) _ Hcj').
      sauto.
    }
    sauto.
Qed.


(* To make "without loss of generality" type arguments, we'll need to
turn any 2-coloring into ones that involve just the colors 1,2 then
use appropriate lemmas to turn them into c, c+1.
*)

(* Idea: use reflection for coloring_ok *)

(* Remove whole neighborhood from a graph *)

(* Try to abstract the details about the criterion about how the
   high-degree vertex is chosen *)

(*
Try to 2-color a 2-colorable graph

- choose a vertex, color it 1
- color all of its neighbors 2
- when you color a vertex 2, color all of its neighbors 1
- keep going

 *)

(*
Induction principle for graphs?

*)
