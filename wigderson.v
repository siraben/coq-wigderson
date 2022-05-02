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

(* A coloring is complete if every vertex is colored. *)
Definition coloring_complete (palette: S.t) (g: graph) (f: coloring) :=
 ( forall i, M.In i f) /\ coloring_ok palette g f.

Definition two_colors: S.t := fold_right S.add S.empty [1; 2]%positive.
Definition three_colors: S.t := fold_right S.add S.empty [1; 2; 3]%positive.

(* A graph is bipartite if it is 2-colorable. *)
Definition two_colorable (g : graph) := exists f, coloring_ok two_colors g f.

Definition empty_graph := mk_graph [].

(* The neighbors of a vertex v in a graph g. *)
Definition neighbors (g : graph) v := S.remove v (adj g v).

(* Subgraph induced by a set of vertices *)
Definition subgraph_of (g : graph) (s : nodeset) :=
  M.fold (fun v adj g' => if S.mem v s then M.add v (S.filter (fun u => S.mem u s) adj) g' else g') g empty_graph.

Check subgraph_of.

Definition vertices := nodes.
Lemma subgraph_vertices_subset : forall g s, S.Subset (nodes (subgraph_of g s)) (nodes g).
Proof.
  intros g s.
  unfold subgraph_of.
  (* Obviously true, but I'll come back to it later. *)
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

Print Module M.
Definition two_coloring (f : coloring) : Prop := forall v c, M.find v f = Some c -> c = 1 \/ c = 2.
Definition three_coloring (f : coloring) : Prop := forall v c, M.find v f = Some c -> c = 1 \/ c = 2 \/ c = 3.


Lemma map_o {A} : forall (m : M.t A) (x : M.key) f,
 @M.find A x (M.map f m) = Datatypes.option_map f (M.find x m).
Proof.
  scongruence use: WF.map_o.
Qed.

(* (ignored 1) Restricting a 3-coloring map to a 2-coloring map. *)
Lemma two_coloring_from_three_1 (f : coloring) :
  three_coloring f -> (forall x, M.find x f <> Some 1)
  -> {p : (M.key -> M.key) * coloring | let (i,c) := p in two_coloring c /\ M.Equiv Logic.eq (M.map i c) f}.
Proof.
  intros H H0.
  remember (fun i => match i with
                  | 2 => 1
                  | 3 => 2
                  | _ => i
                  end) as down.
  remember (fun i => match i with
                  | 1 => 2
                  | 2 => 3
                  | _ => i
                  end) as up.
  refine (exist _ (up, M.map down f) _).
  split.
  - unfold two_coloring.
    intros v c HH.
    unfold three_coloring in H.
    pose proof (M.map_2 f down ltac:(hauto l:on)).
    destruct H1 as [e He].
    pose proof (M.map_2 f down ltac:(hauto l:on)).
    assert (e = 2 \/ e = 3) by (hauto lq: on rew: off).
    hecrush use: map_o unfold: M.MapsTo.
  - unfold M.Equiv.
    split.
    + sauto use: M.map_1, M.map_2.
    + intros k e e' H1 H2.
      assert (up (down e') = e') by (hauto lq: on).
      pose proof (M.map_1 down H2).
      pose proof (@M.map_1 M.key M.key _ k (down e') up H4).
      scongruence.
Defined.

(* (ignored 2) Restricting a 3-coloring map to a 2-coloring map. *)
Lemma two_coloring_from_three_2 (f : coloring) :
  three_coloring f -> (forall x, M.find x f <> Some 2)
  -> {p : (M.key -> M.key) * coloring | let (i,c) := p in two_coloring c /\ M.Equiv Logic.eq (M.map i c) f}.
Proof.
  intros H H0.
  remember (fun i => match i with
                  | 1 => 1
                  | 3 => 2
                  | _ => i
                  end) as down.
  remember (fun i => match i with
                  | 1 => 1
                  | 2 => 3
                  | _ => i
                  end) as up.
  refine (exist _ (up, M.map down f) _).
  split.
  - unfold two_coloring.
    intros v c HH.
    unfold three_coloring in H.
    pose proof (M.map_2 f down ltac:(hauto l:on)).
    destruct H1 as [e He].
    pose proof (M.map_2 f down ltac:(hauto l:on)).
    assert (e = 1 \/ e = 3) by (hauto lq: on rew: off).
    hecrush use: map_o unfold: M.MapsTo.
  - unfold M.Equiv.
    split.
    + sauto use: M.map_1, M.map_2.
    + intros k e e' H1 H2.
      assert (up (down e') = e') by (hauto lq: on).
      pose proof (M.map_1 down H2).
      pose proof (@M.map_1 M.key M.key _ k (down e') up H4).
      scongruence.
Defined.

(* (ignored 3) Restricting a 3-coloring map to a 2-coloring map. *)
Lemma two_coloring_from_three_3 (f : coloring) :
  three_coloring f -> (forall x, M.find x f <> Some 3)
  -> {p : (M.key -> M.key) * coloring | let (i,c) := p in two_coloring c /\ M.Equiv Logic.eq (M.map i c) f}.
Proof.
  intros H H0.
  remember (fun i => match i with
                  | 1 => 1
                  | 2 => 2
                  | _ => i
                  end) as down.
  remember (fun i => match i with
                  | 1 => 1
                  | 2 => 2
                  | _ => i
                  end) as up.
  refine (exist _ (up, M.map down f) _).
  split.
  - unfold two_coloring.
    intros v c HH.
    unfold three_coloring in H.
    pose proof (M.map_2 f down ltac:(hauto l:on)).
    destruct H1 as [e He].
    pose proof (M.map_2 f down ltac:(hauto l:on)).
    assert (e = 1 \/ e = 2) by (hauto lq: on rew: off).
    hecrush use: map_o unfold: M.MapsTo.
  - unfold M.Equiv.
    split.
    + sauto use: M.map_1, M.map_2.
    + intros k e e' H1 H2.
      assert (up (down e') = e') by (hauto lq: on).
      pose proof (M.map_1 down H2).
      pose proof (@M.map_1 M.key M.key _ k (down e') up H4).
      scongruence.
Defined.

Lemma two_coloring_from_three (f : coloring) y :
  three_coloring f -> ({y = 1} + {y = 2} + {y = 3}) -> (forall x, M.find x f <> Some y)
  -> {p : (M.key -> M.key) * coloring | let (i,c) := p in two_coloring c /\ M.Equiv Logic.eq (M.map i c) f}.
Proof.
  intros H [[A|B]|C] H1;
    [apply two_coloring_from_three_1
    |apply two_coloring_from_three_2
    |apply two_coloring_from_three_3]; sfirstorder.
Qed.

Definition example_f (b : bool) : three := if b then N' else M'.

Definition f_restricted_pair :=
  ` (three_to_two example_f ltac:(exists P'; hauto unfold: example_f q: on)).

Compute (let (i, c) := f_restricted_pair in (c true, c false, i (c true), i (c false))).
     (* = (N, M, N', M') *)
(* : two * two * three * three *)

(* NOTE:

Coloring should be defined as an equivalence class.  A map is a
2-coloring if it's in some equivalence with the canonical two-coloring
map that sends things to 1 or 2.

 *)

Definition coloring_equiv (f g : coloring) :=
  exists to from,
     M.Equiv Logic.eq (M.map to f) g /\ M.Equiv Logic.eq (M.map from g) f.

Lemma coloring_equiv_refl : forall f, coloring_equiv f f.
Proof.
  intros f.
  exists (fun x => x), (fun x => x).
  unfold M.Equiv.
  ssimpl.
  - hauto l: on use: M.map_2.
  - hauto l: on use: M.map_1.
  - pose proof (M.map_1 (fun x => x) H2).
    unfold M.MapsTo in H.
    scongruence.
  - hauto l: on use: M.map_2.
  - hauto l: on use: M.map_1.
  - pose proof (M.map_1 (fun x => x) H2).
    scongruence.
Qed.

Lemma coloring_equiv_sym : forall f g, coloring_equiv f g -> coloring_equiv g f.
Proof.
  hauto q: on.
Qed.

Lemma coloring_equiv_trans : forall f g h, coloring_equiv f g -> coloring_equiv g h -> coloring_equiv f h.
Proof.
  intros f g h [to1 [from1 H1]] [to2 [from2 H2]].
  unfold coloring_equiv.
  exists (fun x => to2 (to1 x)), (fun x => from1 (from2 x)).
  unfold M.Equiv.
  ssimpl.
  - qauto use: PositiveMap.map_2, PositiveMap.map_1 unfold: PositiveMap.MapsTo, coloring, PositiveMap.In.
  - hfcrush use: PositiveMap.map_2, PositiveMap.map_1 unfold: PositiveMap.MapsTo, coloring, PositiveMap.In.
  - pose proof (M.map_1 from2 H14).
    pose proof (M.map_1 from1 H3).
    assert (M.In k (M.map to2 g)) by sfirstorder.
    admit.
  - qauto use: PositiveMap.map_2, PositiveMap.map_1 unfold: PositiveMap.MapsTo, coloring, PositiveMap.In.
  - hfcrush use: PositiveMap.map_2, PositiveMap.map_1 unfold: PositiveMap.MapsTo, coloring, PositiveMap.In.
  - admit.
Admitted.

(*
  Prove that every two-coloring map is 
 *)

(* In a 3-colorable graph, the neighborhood of any vertex is 2-colorable. *)
(* The statement is more subtle than that, we have:

Let g be a graph, f be a 3-coloring that is complete (every node has a color).
Then for every vertex v there is a coloring c and map (i : 2 -> 3) such that:
- c is a 2-coloring of the neighborhood of v, N(v)
- (M.map i c) and f agree on N(v)
- c is a complete coloring on N(v)
 *)
Lemma nbd_2_colorable_3 :
  forall (g : graph) (f : coloring),
    three_coloring f -> coloring_complete three_colors g f ->
    (forall v,
        {p : (M.key -> M.key) * coloring |
          let (i,c) := p in
          two_coloring c
          /\ M.Equiv Logic.eq (M.map i c) f
          /\ coloring_complete two_colors (neighborhood g v) c
    }).
Proof.
Admitted.

