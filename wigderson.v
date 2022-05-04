Require Import graph.
Require Import subgraph.
Require Import coloring.
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

Definition injective {A B} (f : A -> B) := forall x y, f x = f y -> x = y.

Local Open Scope positive_scope.

(* Elements of a 2-element set can be extracted *)
Require Import Program.
Lemma two_elem_set_enumerable s :
  S.cardinal s = 2%nat ->
  { (a,b) : S.elt * S.elt | S.Equal s (fold_right S.add S.empty [a;b])}.
Proof.
  intros Hs.
  assert (length (S.elements s) = 2%nat) by scongruence use: PositiveSet.cardinal_1.
  remember (S.elements s).
  destruct l as [|a b].
  - scongruence.
  - assert ({y | [y] = b}) by sauto q: on.
    destruct X as [y Hy].
    exists (a,y).
    subst.
    split.
    + intros HH.
      assert (In a0 [a; y]).
      {
        sauto l: on use: S.elements_1.
      }
      assert (a0 = a \/ a0 = y) by sfirstorder.
      destruct H1; subst.
      * sauto use: S.elements_2, PositiveSet.add_1, PositiveSet.elements_1 unfold: PositiveSet.elements, PositiveOrderedTypeBits.eq.
      * cbn.
        assert (a <> y).
        {
          intros contra.
          subst.
          pose proof (S.elements_3w s).
          rewrite <- Heql in H1.
          sauto lq: on rew: off.
        }
        sauto use: PositiveSet.add_2, PositiveSet.add_1.
    + intros HH.
      apply S.elements_2.
      assert (a <> y).
      {
        intros contra.
        subst.
        pose proof (S.elements_3w s).
        rewrite <- Heql in H0.
        sauto lq: on rew: off.
      }
      cbn in HH.
      pose proof PositiveSet.add_3.
      pose proof S.add_spec.
      ecrush.
Defined.

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
Proof. Admitted.

Function selectW (K: nat) (g: graph) {measure M.cardinal g} : list node :=
  match S.choose (subset_nodes (high_deg K) g) with
  | Some n => n :: selectW K (remove_node n g)
  | None => nil
  end.
Proof. apply selectW_terminates.
Defined.


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
  vertices and m is the coloring of all the neighbors of high-degree vertices
- d*d <= k
- the number of colors used is 2*d

random lemmas that we have to show:
- it's decidable to check whether a node is colored or not (WF.In_Dec)

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


(* To make "without loss of generality" type arguments, we'll need to
turn any 2-coloring into ones that involve just the colors 1,2 then
use appropriate lemmas to turn them into c, c+1.
*)
