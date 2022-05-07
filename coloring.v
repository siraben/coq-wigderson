Require Import graph.
Require Import subgraph.
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
 (forall i, M.In i f) /\ coloring_ok palette g f.

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
    subst.
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

(* A 3-coloring uses 3 colors *)
Definition three_coloring' (f : coloring) p := S.cardinal p = 3%nat /\ forall v c, M.find v f = Some c -> S.In c p.
Definition two_coloring' (f : coloring) p :=  S.cardinal p = 2%nat /\ forall v c, M.find v f = Some c -> S.In c p.

Lemma nodupa_nodup : forall l, NoDupA S.E.eq l -> NoDup l.
Proof.
  intros l H.
  induction H.
  - sfirstorder.
  - sfirstorder use: NoDup_cons, PositiveMap.ME.MO.ListIn_In unfold: PositiveOrderedTypeBits.eq.
Qed.

Lemma sadd_same : forall x s, S.Equal (S.add x s) (S.add x (S.add x s)).
Proof.
  intros x s.
  sauto lq: on rew: off use: SP.add_equal, PositiveSet.add_1, SP.equal_sym.
Qed.

Lemma scardinal_2 : forall x y, x <> y -> S.cardinal (S.add x (S.add y S.empty)) = 2%nat.
Proof.
  intros x y H.
  hecrush use: SP.add_cardinal_2, PositiveSet.add_3, Snot_in_empty, SP.singleton_cardinal unfold: PositiveSet.singleton.
Qed.

Lemma two_coloring_from_three (f : coloring) p :
  three_coloring' f p -> {c | S.In c p /\ forall x, M.find x f <> Some c}
  -> {l : coloring * S.t | let (c,p) := l in two_coloring' c p /\ M.Equiv Logic.eq c f}.
Proof.
  (* Let p3 be the proof that p has cardinality 3, ... *)
  intros [p3 Hf] [c [Hc Hcm]].
  pose proof (three_elem_set_enumerable p p3).
  (* Let x y z be the colors *)
  destruct X as [[[x y] z] Hp].
  (* assert that c is one of the colors x,y,z *)
  assert (c = x \/ c = y \/ c = z).
  {
    assert (In c [x;y;z]).
    {
      assert (S.In c (fold_right S.add S.empty [x; y; z])) by sfirstorder.
      rewrite SP.of_list_1 in H.
      sauto q: on.
    }
    hauto q: on.
  }
  pose proof (S.elements_3w (SP.of_list [x;y;z])).
  (* this is so ugly, it's obviously true *)
  assert (x <> y /\ y <> z /\ x <> z).
  {
    split.
    - intros contra.
      subst.
      unfold SP.of_list in *.
      simpl in H0, Hp.
      rewrite SP.add_equal in Hp by hauto l: on use: PositiveSet.add_1.
      destruct (E.eq_dec y z).
      + subst.
        rewrite SP.add_equal in Hp by hauto l: on use: PositiveSet.add_1.
        hecrush use: SP.Add_Equal, SP.Dec.F.empty_iff, SP.cardinal_2 unfold: PositiveSet.elt, PositiveSet.cardinal, PositiveSet.empty.
      + assert (~ S.In y (S.add z S.empty)) by (sfirstorder use: PositiveSet.add_3, SP.Dec.F.empty_iff).
        qauto use: SP.add_cardinal_2, SP.Equal_cardinal, SP.Dec.F.empty_iff unfold: PositiveSet.empty, PositiveSet.cardinal.
    - split; intros contra.
      + subst.
        unfold SP.of_list in *.
        simpl in H0, Hp.
        destruct (E.eq_dec x z).
        * subst.
          hauto use: PositiveSet.add_spec, SP.Equal_cardinal, SP.Dec.F.empty_iff, SP.add_cardinal_2, SP.add_equal unfold: PositiveSet.empty, PositiveSet.cardinal.
        * assert (~ S.In x (S.add z (S.add z S.empty))).
          {
            qauto use: SP.Dec.F.empty_iff, SP.add_cardinal_2, SP.Equal_cardinal, SP.add_cardinal_1, PositiveSet.add_1 unfold: PositiveSet.cardinal, PositiveSet.empty.
          }
          rewrite <- sadd_same in Hp.
          hauto use: SP.Equal_cardinal, scardinal_2.
      + subst.
        unfold SP.of_list in *.
        simpl in H0, Hp.
        destruct (E.eq_dec y z).
        * subst.
          hauto use: PositiveSet.add_spec, SP.Equal_cardinal, SP.Dec.F.empty_iff, SP.add_cardinal_2, SP.add_equal unfold: PositiveSet.empty, PositiveSet.cardinal.
        * rewrite SP.add_add in Hp.
          assert (~ S.In y (S.add z (S.add z S.empty))).
          {
            qauto use: SP.Dec.F.empty_iff, SP.add_cardinal_2, SP.Equal_cardinal, SP.add_cardinal_1, PositiveSet.add_1 unfold: PositiveSet.cardinal, PositiveSet.empty.
          }
          hauto use: SP.Equal_cardinal, SP.add_cardinal_2, scardinal_2, sadd_same, PositiveSet.add_spec.
  }
  exists (f, S.remove c p).
  destruct H as [Hx|[Hy|Hz]]; qauto l: on use: SP.remove_cardinal_1, S.remove_spec.
Defined.

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

(* A graph is bipartite if it is 2-colorable. *)
Definition completely_two_colorable (g : graph) :=
  exists f, coloring_complete two_colors g f.

(* Definition of a 3-colorable graph *)
Definition completely_three_colorable (g : graph) :=
  exists f, coloring_complete three_colors g f.

(* Restrict a map by a set of keys*)
Definition restrict_m {A} (m : M.t A) s :=
  M.fold (fun v e m' => if S.mem v s then M.add v e m' else m') m (@M.empty _).

(* Lemma restrict_m_subset_nodes : forall  *)


Lemma compl_two_col_dec : forall (g : graph), decidable (completely_two_colorable g).
Proof.
  (* use forcing algorithm *)
  
Admitted.

Lemma nbd_not_2_col_3_col : forall (g : graph) v,
    completely_three_colorable g ->
    completely_two_colorable (neighborhood g v).
Proof.
  intros g v.
  apply contrapositive.
  - (* prove that completely_two_colorable is decidable *)
    apply compl_two_col_dec.
  - (* N2g says that (neighborhood g v) is not two-colorable *)
    (* assume exists 3-coloring of g called Tg *)
    intros N2g Tg.
    (* want to derive contradiction. *)
    (* Let f be the 3-coloring *)
    destruct Tg as [f Hf].
    assert (three_coloring f).
    {
      unfold coloring_complete in Hf.
      admit.
    }
    (* since the coloring is complete, the vertex v has a color 1, 2 or 3 *)
    (* but that would mean that the neighborhood of v is completely 2-colorable *)
    assert (completely_two_colorable (neighborhood g v)).
    {
      unfold completely_two_colorable.
      unfold coloring_complete in Hf.
      pose proof (proj1 Hf v).
      destruct H0 as [c Hc].
      pose proof (H v c Hc).
      assert (is_subgraph (neighborhood g v) g).
      {
        admit.
      }
      unfold coloring_complete.
      pose proof (subgraph_colorable g (neighborhood g v) f three_colors H1 ltac:(hauto lq: on)).
      (* create the color map on the neighbors *)
      remember (nodes (neighborhood g v)) as nv.
      (* restrict f to the neighbors of v *)
      remember (restrict_m f nv) as fn'.
      assert (three_coloring fn').
      {
        admit.
      }
      destruct H0.
      - (* case v has color 1 *)
        admit.
      - (* case v has color 2 *)
        admit.
    }
    contradiction.
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
