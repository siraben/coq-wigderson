Require Import graph.
Require Import subgraph.
Require Import restrict.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
Require Import Decidable.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
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
 (forall i, M.In i g -> M.In i f) /\ coloring_ok palette g f.

Definition two_colors: S.t := SP.of_list [1; 2]%positive.
Definition three_colors: S.t := SP.of_list [1; 2; 3]%positive.

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

Lemma set_elemeum s : S.Equal s (fold_right S.add S.empty (S.elements s)).
Proof.
  strivial use: SP.of_list_3 unfold: SP.of_list, SP.to_list, PositiveSet.Equal.
Qed.

  
(* Elements of a 2-element set can be extracted *)
Require Import Program.
Lemma two_elem_set_enumerable s :
  S.cardinal s = 2%nat ->
  { (a,b) : S.elt * S.elt | S.Equal s (SP.of_list [a;b])}.
Proof.
  intros Hs.
  assert (length (S.elements s) = 2%nat) by scongruence use: PositiveSet.cardinal_1.
  remember (S.elements s).
  destruct l as [|a [|b t]].
  - scongruence.
  - scongruence.
  - assert (t = []) by sauto.
    subst.
    exists (a,b).
    hauto lq: on use: set_elemeum unfold: SP.of_list.
Defined.

Lemma three_elem_set_enumerable s :
  S.cardinal s = 3%nat ->
  { x : S.elt * S.elt * S.elt | let (p,c) := x in let (a,b) := p in S.Equal s (SP.of_list [a;b;c])}.
Proof.
  intros Hs.
  assert (length (S.elements s) = 3%nat) by scongruence use: PositiveSet.cardinal_1.
  remember (S.elements s).
  destruct l as [|a [|b [|c d]]].
  - scongruence.
  - scongruence.
  - scongruence.
  - assert (d = []) by sauto.
    exists ((a,b),c).
    hauto lq: on use: set_elemeum.
Defined.

Definition two_coloring (f : coloring) : Prop := forall v c, M.find v f = Some c -> c = 1 \/ c = 2.
Definition three_coloring (f : coloring) : Prop := forall v c, M.find v f = Some c -> c = 1 \/ c = 2 \/ c = 3.

(* A subgraph of a graph is colorable under the same coloring *)
Lemma subgraph_colorable : forall (g g' : graph) f p,
    is_subgraph g' g ->
    coloring_ok p g f ->
    coloring_ok p g' f.
Proof.
  intros g g' f p H H0 H1.
  qauto unfold: PositiveSet.Subset, coloring_ok, is_subgraph.
Qed.

Definition n_coloring (f : coloring) (p : S.t) (n : nat) :=
  S.cardinal p = n /\ forall v c, M.find v f = Some c -> S.In c p.

(* A 3-coloring uses 3 colors *)
Definition three_coloring' (f : coloring) p := n_coloring f p 3.
Definition two_coloring' (f : coloring) p := n_coloring f p 2.

(* Let:
- f: coloring
- p: palette of colors of size n
- c: a color
- n: natural number

Assume that f is a (n+1)-coloring wrt. p, c is in p, and c is unused by f.
Then f is a n-coloring wrt. c\{p}.
*)
Lemma n_coloring_missed (f : coloring) p c n :
  n_coloring f p (S n) ->
  S.In c p ->
  (forall x, M.find x f <> Some c) ->
  n_coloring f (S.remove c p) n.
Proof.
  intros [p3 Hf] Hc Hcm.
  qauto l: on use: SP.remove_cardinal_1, S.remove_spec, three_elem_set_enumerable unfold: two_coloring'.
Qed.

Lemma two_coloring_from_three (f : coloring) p c :
  three_coloring' f p ->
  S.In c p ->
  (forall x, M.find x f <> Some c) ->
  two_coloring' f (S.remove c p).
Proof. apply n_coloring_missed. Qed.

(* A restriction of an OK coloring under a set is OK. *)
Lemma restrict_coloring_ok : forall (g : graph) (f : coloring) p (s : nodeset),
    coloring_ok p g f -> coloring_ok p g (restrict f s).
Proof.
  intros g f p s H.
  unfold coloring_ok.
  intros i j H0.
  split.
  - qauto use: @restrict_agree unfold: node, PositiveMap.key, coloring_ok, coloring, nodeset, PositiveOrderedTypeBits.t.
  - intros ci cj H1 H2.
    qauto use: @restrict_agree unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, PositiveMap.key, nodeset, node, coloring, coloring_ok.
Qed.

Lemma nbd_2_colorable_3' : forall (g : graph) (f : coloring) p,
    three_coloring' f p ->
    coloring_complete p g f ->
    forall v ci, M.find v f = Some ci ->
            two_coloring' (restrict f (nodes (neighborhood g v))) (S.remove ci p) /\ coloring_complete (S.remove ci p) (neighborhood g v) (restrict f (nodes (neighborhood g v))).
Proof.
  intros g f p H H0 v ci H1.
  split.
  - apply two_coloring_from_three.
    + hauto use: @restrict_agree unfold: node, coloring, n_coloring, PositiveOrderedTypeBits.t, PositiveMap.key, three_coloring'.
    + sfirstorder.
    + (* let x be a neighbor of v *)
      intros x contra.
      assert (S.In x (adj g v)).
      {
        sauto lq: on rew: off use: nbd_adj, @restrict_in_set, WF.in_find_iff unfold: node, coloring, PositiveMap.key, PositiveOrderedTypeBits.t, PositiveSet.elt, PositiveMap.In, PositiveMap.MapsTo.
      }
      qauto use: WF.in_find_iff, @restrict_agree unfold: coloring_ok, PositiveOrderedTypeBits.t, PositiveMap.MapsTo, coloring_complete, PositiveSet.elt, PositiveMap.key, coloring, PositiveMap.In, node.
  - split.
    + intros i Hi.
      (* use contradiction *)
      apply not_not.
      {
        qauto l: on use: WF.In_dec.
      }
      intros contra.
      assert (M.In i g).
      {
        strivial use: subgraph_vert_m, nbd_subgraph unfold: PositiveOrderedTypeBits.t, node, PositiveMap.key.
      }
      (* contra states that i doesn't have a color in the restriction *)
      (* but that would mean that f was not complete *)
      assert (~ S.In i (nodes (neighborhood g v))).
      {
        hfcrush use: @restrict_restricts unfold: PositiveMap.key, coloring, node, coloring_complete, PositiveSet.elt, PositiveOrderedTypeBits.t.
      }
      apply H3.
      apply Sin_domain.
      assumption.
    + pose proof (nbd_subgraph g v).
      pose proof (subgraph_colorable _ _ f p H2 ltac:(sauto)).
      split.
      * intros ci0 H6.
        assert (S.In j (adj g i)) by sfirstorder.
        qauto use: nbd_adj, PositiveSet.remove_spec, @restrict_agree, @restrict_in_set unfold: PositiveSet.elt, node, PositiveOrderedTypeBits.t, coloring_ok, coloring, nodes, coloring_complete, PositiveMap.key.
      * intros ci0 cj H5 H6.
        qauto use: @restrict_agree unfold: PositiveOrderedTypeBits.t, node, PositiveMap.key, PositiveSet.elt, coloring, coloring_ok.
Qed.

(* In a 3-colorable graph, the neighborhood of any vertex is 2-colorable. *)
(* The statement is more subtle than that, we have: *)
(* Let g be a graph, f be a 3-coloring that is complete (every node has a color).
Then for every vertex v there is a coloring c and map (i : 2 -> 3) such that:
- c is a 2-coloring of the neighborhood of v, N(v)
- (M.map i c) and f agree on N(v)
- c is a complete coloring on N(v)
 *)

Lemma nbd_2_colorable_3 :
  forall (cnt : positive) (g : graph) (f : coloring),
    three_coloring f -> coloring_complete three_colors g f ->
    (forall v,
        {p : (M.key -> M.key) * coloring |
          (* exists injection i into canonical coloring using colors 1 and 2 *)
          let (i,c) := p in
          two_coloring c
          /\ M.Equal (M.map i c) f (* make it agree on the restriction *)
          /\ coloring_complete (SP.of_list [cnt; cnt + 1]) (neighborhood g v) c
    }).
Proof.
Admitted.


(* union of maps (left-heavy) *)
Definition Munion {A} (f g : M.t A) := M.fold (fun k v => M.add k v) f g.
(* Two maps are disjoint if their keys have no intersection. *)
(* Mkeys is just Mdomain *)
Definition Mdisjoint {A} (f g : M.t A) := S.Equal (S.inter (Mdomain f) (Mdomain g)) S.empty.

(* Test case for disjointness *)
Example Mdisjoint_test1 :
  Mdisjoint (fold_right (fun p m => M.add (fst p) (snd p) m) (@M.empty _) [(1,1);(2,2)])
            (fold_right (fun p m => M.add (fst p) (snd p) m) (@M.empty _) [(3,1);(4,2)]).
Proof. hauto l: on. Qed.

(* Note: since we're using equality on finite sets can we get for free
   that map disjointness is decidable *)
Lemma Mdisjoint_dec {A} (f g : M.t A) : {Mdisjoint f g} + {~ Mdisjoint f g}.
Proof. apply S.eq_dec. Qed.

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
    sfirstorder use: PositiveSet.union_3, PositiveSet.union_2 unfold: PositiveOrderedTypeBits.t, PositiveMap.MapsTo, coloring_ok, node, PositiveSet.elt.
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
