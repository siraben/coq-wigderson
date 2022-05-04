Require Import graph.
Require Import subgraph.
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


Lemma map_o {A} : forall (m : M.t A) (x : M.key) f,
 @M.find A x (M.map f m) = Datatypes.option_map f (M.find x m).
Proof.
  scongruence use: WF.map_o.
Qed.


(* A coloring is complete if every vertex is colored. *)
Definition coloring_complete (palette: S.t) (g: graph) (f: coloring) :=
 (forall i, M.In i f) /\ coloring_ok palette g f.

Definition two_colors: S.t := fold_right S.add S.empty [1; 2]%positive.
Definition three_colors: S.t := fold_right S.add S.empty [1; 2; 3]%positive.

(* A graph is bipartite if it is 2-colorable. *)
Definition two_colorable (g : graph) := exists f, coloring_ok two_colors g f.


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

(* An empty graph is colorable by any coloring. *)
Lemma empty_graph_colorable : forall p f, coloring_ok f empty_graph p.
Proof.
  intros p f.
  unfold empty_graph.
  cbn.
  split.
  - intros ci H0.
    unfold adj in H.
    ssimpl.
    scongruence use: PositiveMap.gempty unfold: node, PositiveMap.key, PositiveOrderedTypeBits.t.
  - unfold adj in H.
    ssimpl.
    scongruence use: PositiveMap.gempty unfold: PositiveMap.key, node, PositiveOrderedTypeBits.t.
Qed.

Definition two_coloring (f : coloring) : Prop := forall v c, M.find v f = Some c -> c = 1 \/ c = 2.
Definition three_coloring (f : coloring) : Prop := forall v c, M.find v f = Some c -> c = 1 \/ c = 2 \/ c = 3.

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

(* (ignored 1) Restricting a 3-coloring map to a 2-coloring map. *)
Lemma two_coloring_from_three_1 (f : coloring) :
  three_coloring f -> (forall x, M.find x f <> Some 1%positive)
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

(* NOTE:

Coloring should be defined as an equivalence class.  A map is a
2-coloring if it's in some equivalence with the canonical two-coloring
map that sends things to 1 or 2.

Alternatively we can use the proof that a graph is 2-colorable then
produce a novel 2-coloring using a forcing algorithm then show that we
only use two colors i, i+1 in that novel coloring.

Then for the last part of Wigderson's algorithm we have to show that
since there are no more vertices of degree greater than sqrt(K) we
only need at most sqrt(K) new colors.

To prove that we use a lemma that says that if a graph has no vertices
of degree greater than some constant c then we need at c+1 colors to
color it.  To do this, we take the max degree vertex (degree d <= c),
color it c+1 then color its neighbors 1,...d, then continue.

It's not hard to show that we never use a color more than c+1 because
we continually use the fact that the max degree is never more than c,
so we are done.

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
          /\ M.Equal (M.map i c) f
          /\ coloring_complete two_colors (neighborhood g v) c
    }).
Proof.
Admitted.

(* union of maps (left-heavy) *)
Definition Munion {A} (f g : M.t A) := M.fold (fun k v => M.add k v) f g.
(* Two maps are disjoint if their keys have no intersection. *)
(* Mkeys is just Mdomain *)
Definition Mdisjoint {A} (f g : M.t A) := S.inter (Mdomain f) (Mdomain g) = S.empty.

Example Mdisjoint_test1 :
  Mdisjoint (fold_right (fun p m => M.add (fst p) (snd p) m) (@M.empty _) [(1,1);(2,2)])
            (fold_right (fun p m => M.add (fst p) (snd p) m) (@M.empty _) [(3,3);(4,4)]).
Proof. hauto l: on. Qed.

Lemma Munion_case {A} : forall (c d : M.t A) i v,
    M.find i (Munion c d) = Some v -> M.MapsTo i v c \/ M.MapsTo i v d.
Proof.
  intros c d i.
  unfold Munion.
  apply WP.fold_rec_bis.
  - hauto unfold: PositiveMap.MapsTo, PositiveMap.In, PositiveMap.Equal.
  - hauto l: on.
  - intros k e a m' H H0 H1 v H2.
    destruct (E.eq_dec i k).
    + hauto use: PositiveMap.gss unfold: PositiveMap.In, PositiveMap.MapsTo.
    + qauto use: WP.F.add_neq_mapsto_iff, PositiveMap.gss unfold: PositiveMap.In, PositiveMap.MapsTo.
Qed.

(* Proof that the union of two disjoint and OK colorings is an OK coloring. *)
(* The keys have to be disjoint and the palettes have to be disjoint *)
Lemma coloring_union (c d : coloring) p1 p2 g :
  undirected g ->
  S.inter p1 p2 = S.empty ->
  coloring_ok p1 g c ->
  coloring_ok p2 g d ->
  Mdisjoint c d ->
  coloring_ok (S.union p1 p2) g (Munion c d).
Proof.
  intros Ug HI cOK dOK Hdisj.
  unfold Munion.
  unfold coloring_ok.
  split.
  - intros ci H0.
    apply Munion_case in H0.
    destruct H0.
    + sfirstorder use: PositiveSet.union_2 unfold: coloring_ok, PositiveMap.MapsTo, node, PositiveOrderedTypeBits.t, PositiveSet.elt.
    + sfirstorder use: PositiveSet.union_3 unfold: PositiveSet.elt, coloring_ok, PositiveMap.MapsTo, PositiveOrderedTypeBits.t, node.
  - intros ci cj H0 H1.
    apply Munion_case in H0.
    apply Munion_case in H1.
    destruct H0, H1.
    + sfirstorder unfold: coloring_ok, PositiveMap.MapsTo.
    + unfold Mdisjoint in Hdisj.
      assert (S.In ci p1) by sfirstorder.
      assert (S.In cj p2).
      {
        hauto unfold: node, PositiveSet.elt, PositiveOrderedTypeBits.t, undirected, PositiveMap.MapsTo, coloring_ok.
      }
      qauto use: PositiveSet.inter_3, Snot_in_empty unfold: PositiveOrderedTypeBits.t, node, PositiveSet.elt.
    + assert (S.In ci p2) by sfirstorder.
      assert (S.In cj p1).
      {
        hauto unfold: node, PositiveSet.elt, PositiveOrderedTypeBits.t, undirected, PositiveMap.MapsTo, coloring_ok.
      }
      qauto use: PositiveSet.inter_3, Snot_in_empty unfold: PositiveOrderedTypeBits.t, node, PositiveSet.elt.
    + sfirstorder unfold: PositiveMap.MapsTo, coloring_ok.
Qed.
