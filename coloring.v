Require Import graph.
Require Import subgraph.
Require Import restrict.
Require Import munion.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
Require Import Decidable.
Require Import Program.
Require Import FunInd.
Require Import Psatz.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
Import Arith.
Import ListNotations.
Import Nat.

Local Open Scope positive_scope.

(** * Properties of coloring maps *)
(** ** Definition of a set of colors *)
Definition colors := S.t.

(** ** Map option *)
Lemma map_o {A} : forall (m : M.t A) (x : M.key) f,
 @M.find A x (M.map f m) = Datatypes.option_map f (M.find x m).
Proof.
  scongruence use: WF.map_o.
Qed.

(** ** A coloring is complete if every vertex is colored *)
Definition coloring_complete (palette: colors) (g: graph) (f: coloring) :=
  (forall i, M.In i g -> M.In i f) /\ coloring_ok palette g f.

(** ** Complete coloring implies graph is irreflexive *)
Lemma complete_col_no_selfloop : forall (g : graph) (c : coloring) p,
    coloring_complete p g c -> no_selfloop g.
Proof.
  intros g c p H.
  unfold no_selfloop.
  unfold coloring_complete, coloring_ok in H.
  intros i contra.
  hauto lq: on use: SP.Dec.F.empty_iff unfold: PositiveSet.In, PositiveOrderedTypeBits.t, node, PositiveMap.key, adj, PositiveMap.MapsTo, PositiveSet.elt, PositiveMap.In.
Qed.

Example ex_graph :=
  mk_graph [ (6,4); (4,5); (4,3); (3,2); (5,2); (1,2); (1,5) ]%positive.

Definition two_colors: colors := SP.of_list [1; 2]%positive.
Definition three_colors: colors := SP.of_list [1; 2; 3]%positive.

Local Open Scope positive_scope.

(* Example of 3-coloring the example graph and proof with ok_coloring *)
Example ex_coloring :=
  fold_right (fun p m => M.add (fst p) (snd p) m) (@M.empty _) [(6,1);(3,1);(5,1);(4,2);(2,2);(1,3)].

(* Proving that an explicit graph coloring is a valid coloring *)
Example ex_coloring_good : coloring_ok three_colors ex_graph ex_coloring.
Proof.
  split; sblast use: M.elements_correct.
Qed.

(** ** Empty graph is colorable by any coloring *)
Lemma empty_graph_colorable : forall p f, coloring_ok f empty_graph p.
Proof.
  intros p f.
  unfold empty_graph.
  cbn.
  split.
  - intros ci H0.
    unfold adj in H.
    hauto use: SP.Dec.F.empty_iff, PositiveMap.gempty unfold: PositiveOrderedTypeBits.t, PositiveSet.In, node, PositiveMap.key inv: option.
  - unfold adj in H.
    ssimpl.
    scongruence use: PositiveMap.gempty unfold: PositiveMap.key, node, PositiveOrderedTypeBits.t.
Qed.

(** ** A set is extensionally equal to folding over its elements *)
Lemma set_elemeum s : S.Equal s (fold_right S.add S.empty (S.elements s)).
Proof.
  strivial use: SP.of_list_3 unfold: SP.of_list, SP.to_list, PositiveSet.Equal.
Qed.

(** ** A three-element set is enumerable *)
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

(** ** Valid coloring carries to subgraphs *)
Lemma subgraph_coloring_ok : forall (g g' : graph) f p,
    is_subgraph g' g ->
    coloring_ok p g f ->
    coloring_ok p g' f.
Proof.
  intros g g' f p H H0 H1.
  qauto unfold: PositiveSet.Subset, coloring_ok, is_subgraph.
Qed.

(** ** Complete coloring carries to subgraphs *)
Lemma subgraph_coloring_complete : forall (g g' : graph) f p,
    is_subgraph g' g ->
    coloring_complete p g f ->
    coloring_complete p g' f.
Proof.
  intros g g' f p H H0.
  hauto lq: on use: subgraph_coloring_ok, subgraph_vert_m.
Qed.

(** ** Definition of $n$-coloring *)
Definition n_coloring (f : coloring) (p : colors) (n : nat) :=
  S.cardinal p = n /\ forall v c, M.find v f = Some c -> S.In c p.

(** ** Definition of 3-coloring *)
Definition three_coloring (f : coloring) p := n_coloring f p 3.

(** ** Definition of 2-coloring *)
Definition two_coloring (f : coloring) p := n_coloring f p 2.

(** ** $(n+1)$-coloring not using a color is $n$-coloring *)
(** Let:
- [f] be a coloring
- [p] be palette of colors of size [n]
- [c] be a color in [p]

Assume that [f] is a $(n+1)$-coloring wrt. [p], [c] is in [p], and [c] is unused by [f].
Then [f] is a $n$-coloring wrt. [c\{p}].
 *)

Lemma n_coloring_missed (f : coloring) p c n :
  n_coloring f p (S n) ->
  S.In c p ->
  (forall x, M.find x f <> Some c) ->
  n_coloring f (S.remove c p) n.
Proof.
  intros [p3 Hf] Hc Hcm.
  unfold n_coloring.
  split.
  - sfirstorder use: SP.remove_cardinal_1 unfold: colors.
  - intros v c0 H.
    qauto l: on use: S.remove_spec.

Qed.

(** ** Restriction to 3-coloring to 2-coloring *)

Lemma two_coloring_from_three (f : coloring) p c :
  three_coloring f p ->
  S.In c p ->
  (forall x, M.find x f <> Some c) ->
  two_coloring f (S.remove c p).
Proof. apply n_coloring_missed. Qed.

(** ** Restricting a valid coloring on fewer nodes is valid *)
Lemma restrict_coloring_ok : forall (g : graph) (f : coloring) p (s : nodeset),
    coloring_ok p g f -> coloring_ok p g (restrict f s).
Proof.
  hauto lq: on rew: off use: @restrict_agree unfold: coloring_ok.
Qed.

(** ** Restricting a coloring on the neighborhood of a node *)

Definition restrict_on_nbd (f : coloring) (g : graph) (v : node) :=
  restrict f (nodes (neighborhood g v)).

(** ** Neighborhood of vertex in $(n+1)$-colorable graph is $n$-colorable *)
Lemma nbd_Sn_colorable_n : forall (g : graph) (f : coloring) (p : colors) (n : nat),
    coloring_complete p g f ->
    n_coloring f p (S n) ->
    forall v ci, M.find v f = Some ci ->
            n_coloring (restrict_on_nbd f g v) (S.remove ci p) n
         /\ coloring_complete (S.remove ci p) (neighborhood g v) (restrict_on_nbd f g v).
Proof.
  intros g f p k H H0 v ci H1.
  split.
  - apply n_coloring_missed.
    + hauto use: @restrict_agree unfold: node, coloring, n_coloring, PositiveOrderedTypeBits.t, PositiveMap.key, three_coloring.
    + sfirstorder.
    + (* let x be a neighbor of v *)
      intros x contra.
      assert (S.In x (adj g v)).
      {
        sauto lq: on rew: off use: nbd_adj, @restrict_in_set, WF.in_find_iff.
      }
      qauto use: WF.in_find_iff, @restrict_agree unfold: coloring_ok.
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
        strivial use: subgraph_vert_m, nbd_subgraph.
      }
      (* contra states that i doesn't have a color in the restriction *)
      (* but that would mean that f was not complete *)
      assert (~ S.In i (nodes (neighborhood g v))).
      {
        qauto l: on use: @restrict_restricts.
      }
      apply H3.
      apply Sin_domain.
      assumption.
    + pose proof (nbd_subgraph g v).
      pose proof (subgraph_coloring_ok _ _ f p H2 ltac:(sauto)).
      split.
      * intros ci0 H6.
        assert (S.In j (adj g i)) by sfirstorder.
        qauto use: nbd_adj, PositiveSet.remove_spec, @restrict_agree, @restrict_in_set unfold: coloring_ok.
      * intros ci0 cj H5 H6.
        qauto use: @restrict_agree unfold: coloring_ok.
Qed.

(** ** Neighborhood of vertex in 3-colorable graph is 2-colorable *)
Lemma nbd_2_colorable_3 : forall (g : graph) (f : coloring) p,
    coloring_complete p g f ->
    three_coloring f p ->
    forall v ci, M.find v f = Some ci ->
            two_coloring (restrict_on_nbd f g v) (S.remove ci p) /\
              coloring_complete (S.remove ci p) (neighborhood g v) (restrict_on_nbd f g v).
Proof.
  hauto l: on use: SP.remove_cardinal_1, nbd_Sn_colorable_n.
Qed.

(** ** If some neighborhood cannot be $n$-colored then the coloring is not $(n+1)$ *)
Lemma nbd_not_n_col_graph_not_Sn_col : forall (g : graph) (f : coloring) (p : colors) n,
    coloring_complete p g f ->
    (exists (v : M.key) (ci : node),
        M.find v f = Some ci /\
          (~ n_coloring (restrict_on_nbd f g v) (S.remove ci p) n)) ->
    ~ n_coloring f p (S n).
Proof.
  qauto l: on use: nbd_Sn_colorable_n.
Qed.

(* if f is a complete coloring of g, then if there is a vertex whose
   neighborhood is not 2-colorable or the coloring is not complete
   then f cannot be a 3-coloring
 *)
Lemma nbd_not_2_col_graph_not_3_col : forall (g : graph) (f : coloring) (p : colors),
    coloring_complete p g f ->
    (exists (v : M.key) (ci : node),
        M.find v f = Some ci /\
          (~ two_coloring (restrict_on_nbd f g v) (S.remove ci p))) ->
    ~ three_coloring f p.
Proof.
  qauto l: on use: nbd_2_colorable_3.
Qed.

(** * Constant coloring of a vertex set [s] with [c] *)
Definition constant_color {A} (s : nodeset) c := S.fold (fun v => M.add v c) s (@M.empty A).

(** ** Constant coloring colors any vertex in the set with [c] *)
Lemma constant_color_colors {A} s c : forall i, S.In i s -> M.find i (@constant_color A s c) = Some c.
Proof.
  intros i Hi.
  unfold constant_color.
  generalize dependent Hi.
  apply SP.fold_rec_bis.
  - sfirstorder.
  - sauto q: on.
  - intros x a s' H H0 H1 Hi.
    qauto use: WF.add_o, PositiveSet.add_3, PositiveMap.gss.
Qed.

(** ** Constant coloring inversion 1 *)
Lemma constant_color_inv {A} s c d : forall i, M.find i (@constant_color A s c) = Some d -> S.In i s.
Proof.
  intros i.
  unfold constant_color.
  apply SP.fold_rec_bis.
  - sfirstorder.
  - sauto q: on.
  - intros x a s' H H0 H1 H2.
    destruct (E.eq_dec i x).
    + subst. hauto l: on use: PositiveSet.add_1.
    + qauto use: SP.Dec.F.add_iff, PositiveMap.gso unfold: PositiveMap.key, PositiveSet.elt.
Qed.

(** ** Constant coloring inversion 2 *)
Lemma constant_color_inv2 {A} s c : forall i d, M.find i (@constant_color A s c) = Some d -> c = d.
Proof.
  intros i d.
  unfold constant_color.
  apply SP.fold_rec_bis.
  - sfirstorder.
  - sauto dep: on.
  - intros x a s' H H0 H1 H2.
    destruct (E.eq_dec i x).
    + scongruence use: PositiveMap.gss.
    + hauto use: PositiveMap.gso.
Qed.

(** * 2-color step *)
(** Let [g] be a graph, [v] be a vertex, $c_1$ and $c_2$ the colors we
have that this function colors [v] with $c_1$ and colors its neighbors
with $c_2$. *)

Definition two_color_step (g : graph) (v : node) c1 c2 (f : coloring) : coloring :=
  M.add v c1 (constant_color (adj g v) c2).

(** ** Vertex is colored $c_1$ *)
Lemma two_color_step_colors_v_c1 : forall g v c1 c2 f, M.find v (two_color_step g v c1 c2 f) = Some c1.
Proof.
  scongruence use: PositiveMap.gss unfold: PositiveOrderedTypeBits.t, node, PositiveMap.key, adj, nodeset, two_color_step.
Qed.

(** ** Neighbors are colored $c_2$ *)
Lemma two_color_step_colors_adj_c2 : forall g v c1 c2 f i,
    no_selfloop g -> S.In i (adj g v) -> M.find i (two_color_step g v c1 c2 f) = Some c2.
Proof.
  hauto use: PositiveMap.gso, @constant_color_colors unfold: two_color_step.
Qed.

(** ** Vertex colored by 2-color step is either [v] or a neighbor *)
Lemma two_color_step_inv : forall g v c1 c2 f ci j,
    M.find j (two_color_step g v c1 c2 f) = Some ci ->
    j = v \/ S.In j (adj g v).
Proof.
  intros g v c1 c2 f ci j H.
  unfold two_color_step in H.
  destruct (E.eq_dec j v).
  - subst. left. reflexivity.
  - right.
    rewrite M.gso in H by auto.
    qauto use: WF.in_find_iff, @constant_color_inv.
Qed.

(** ** Adjacency in undirected graphs *)
Lemma undirected_adj_in : forall (g : graph) (v : node) i , undirected g -> S.In i (adj g v) -> M.In i g.
Proof.
  intros g v i H H0.
  hauto use: SP.Dec.F.empty_iff unfold: undirected, adj.
Qed.

(** ** Membership of a two-element set *)
Lemma in_two_set_inv : forall i a b, S.In i (SP.of_list [a;b]) -> i = a \/ i = b.
Proof.
  intros i a b H.
  qauto use: PositiveSet.singleton_1, PositiveSet.add_spec, PositiveSet.cardinal_1.
Qed.

(** ** Correctness of 2-color step *)
Lemma two_color_step_correct : forall (g : graph) (v : node) c1 c2,
    c1 <> c2 ->
    no_selfloop g ->
    undirected g ->
    M.In v g ->
    (exists m, two_coloring m (SP.of_list [c1;c2]) /\ coloring_complete (SP.of_list [c1;c2]) g m) ->
    coloring_ok (SP.of_list [c1;c2]) g (two_color_step g v c1 c2 (@M.empty _)).
Proof.
  intros g v c1 c2 Hc H Hu magic H0.
  split.
  - intros ci H2.
    unfold two_color_step in H2.
    destruct (E.eq_dec i v).
    + subst. hauto use: PositiveMap.gss, PositiveSet.add_1.
    + rewrite M.gso in H2 by auto.
      hauto q: on use: constant_color_inv, constant_color_colors, PositiveSet.add_2, PositiveSet.add_1.
  - intros ci cj H2 H3.
    remember (two_color_step g v c1 c2 (M.empty node)) as f.
    assert (Hv: M.find v f = Some c1).
    {
      subst.
      apply two_color_step_colors_v_c1.
    }
    assert (Cadj: forall x, S.In x (adj g v) -> M.find x f = Some c2).
    {
      intros x Hx.
      hauto l: on use: two_color_step_colors_adj_c2, two_color_step_colors_v_c1.
    }
    assert (~ M.In v (M.empty node)) by hauto l: on use: WF.empty_in_iff.
    destruct (E.eq_dec i j); [scongruence|].
    subst f.
    pose proof (two_color_step_inv g _ _ _ _ _ _ H3).
    pose proof (two_color_step_inv g _ _ _ _ _ _ H2).
    destruct H5, H6; subst.
    + contradiction.
    + hauto l: on use: two_color_step_colors_adj_c2.
    + hauto l: on use: two_color_step_colors_adj_c2.
    + rewrite two_color_step_colors_adj_c2 in H2, H3 by auto.
      (* Contradiction! We supposed that the graph was 2-colorable to
         begin with, but here we have a configuration of vertices that
         cannot be 2-colored. *)
      destruct H0 as (m & p & Hm & Hm').
      pose proof (Hm i ltac:(sauto use: undirected_adj_in)).
      pose proof (Hm j ltac:(sauto use: undirected_adj_in)).
      pose proof (Hm v ltac:(sauto use: undirected_adj_in)).
      destruct H0 as [ii Hii].
      destruct H7 as [jj Hjj].
      destruct H8 as [vv Hvv].
      unfold M.MapsTo in *.
      assert (ii = c1 \/ ii = c2).
      {
        sauto lq: on use: in_two_set_inv unfold: two_coloring, n_coloring.
      }
      assert (jj = c1 \/ jj = c2).
      {
        sauto lq: on rew: off use: in_two_set_inv unfold: two_coloring, n_coloring.
      }
      assert (vv = c1 \/ vv = c2).
      {
        sauto lq: on rew: off use: in_two_set_inv unfold: two_coloring, n_coloring.
      }
      (* So i and j have colors given by the magic coloring function,
         but no matter what colors we give them something is going to go
         wrong *)
      destruct H0, H7, H8; strivial unfold: coloring_ok.
Qed.

(** ** Completeness of 2-color step *)
Lemma two_color_step_complete : forall (g : graph) (v : node) c1 c2,
    c1 <> c2 ->
    no_selfloop g ->
    undirected g ->
    M.In v g ->
    (exists m, two_coloring m (SP.of_list [c1;c2]) /\ coloring_complete (SP.of_list [c1;c2]) g m) ->
    coloring_complete (SP.of_list [c1;c2]) (subgraph_of g (nodes (neighborhood g v))) (two_color_step g v c1 c2 (@M.empty _)).
Proof.
  intros g v c1 c2 H H0 H1 H2 H3.
  split.
  - intros i H4.
    apply Sin_domain in H4.
    qauto use: two_color_step_colors_adj_c2, nbd_adj, WF.in_find_iff, subgraph_of_nodes.
  - qauto l: on use: two_color_step_correct, subgraph_of_is_subgraph, subgraph_coloring_ok.
Qed.

(** ** Constant coloring is complete on max degree 0 graphs *)
Lemma max_deg_0_constant_col : forall (g : graph) c,
    max_deg g = 0%nat ->
    coloring_complete (S.singleton c) g (constant_color (nodes g) c).
Proof.
  intros g c H.
  split.
  - sauto use: constant_color_colors, Sin_domain.
  - split; sfirstorder use: max_deg_0_adj.
Qed.

(** ** Any coloring function is ok on independent sets *)
Lemma indep_set_ok : forall (g : graph) s (p : colors) (m : coloring),
    independent_set g s ->
    S.Subset (Mdomain m) s ->
    (forall i ci : node, M.find i m = Some ci -> S.In ci p) ->
    coloring_ok p (subgraph_of g s) m.
Proof.
  intros g s p m H H0 H1.
  split.
  - sfirstorder.
  - intros ci cj H3 H4 contra.
    assert (S.In ci p) by hauto l: on.
    assert (S.In cj p) by hauto l: on.
    assert (S.In j (adj g i)).
    {
      hauto q: on use: subgraph_edges.
    }
    assert (S.In i s).
    {
      qauto use: WF.in_find_iff, Sin_domain unfold: PositiveSet.Subset.
    }
    assert (S.In j s).
    {
      qauto use: WF.in_find_iff, Sin_domain unfold: PositiveSet.Subset.
    }
    sfirstorder.
Qed.

(** ** Constant coloring is complete on independent sets *)
Lemma constant_col_indep_set : forall (g : graph) s c,
    independent_set g s ->
    coloring_complete (S.singleton c) (subgraph_of g s) (constant_color s c).
Proof.
  intros g s c H.
  split.
  - intros i Hi.
    rewrite <- Sin_domain in Hi.
    apply subgraph_of_nodes in Hi.
    hecrush use: constant_color_colors, subgraph_of_is_subgraph.
  - apply indep_set_ok.
    + assumption.
    + intros ci H1.
      apply Sin_domain in H1.
      hauto q: on use: constant_color_inv.
    + intros i ci H0.
      apply constant_color_inv2 in H0.
      sfirstorder use: S.singleton_2.
Qed.

(** ** Constant coloring on max degree vertices is complete *)

Lemma coloring_max_deg_complete g d c s :
  no_selfloop g ->
  undirected g ->
  d = max_deg g ->
  (d > 0)%nat ->
  s = fst (extract_vertices_degs g d) ->
  coloring_complete (S.singleton c) (subgraph_of g s) (constant_color s c).
Proof.
  intros H H0 H1 H2 H3.
  sauto lq: on rew: off use: constant_col_indep_set, max_degree_extraction_independent_set.
Qed.

(** ** Union of two valid disjoint colorings is valid *)
(** Proof that the union of two disjoint and OK colorings is an OK
    coloring.  The palettes have to be disjoint *)

Lemma coloring_union (c d : coloring) p1 p2 g :
  undirected g ->
  S.Empty (S.inter p1 p2) ->
  coloring_ok p1 g c ->
  coloring_ok p2 g d ->
  coloring_ok (S.union p1 p2) g (Munion c d).
Proof.
  intros Ug HI cOK dOK.
  unfold Munion.
  unfold coloring_ok.
  split.
  - intros ci H0.
    apply Munion_case in H0.
    sfirstorder use: PositiveSet.union_3, PositiveSet.union_2.
  - intros ci cj H0 H1.
    apply Munion_case in H0.
    apply Munion_case in H1.
    destruct H0, H1.
    + sfirstorder unfold: coloring_ok.
    + assert (S.In ci p1) by sfirstorder.
      assert (S.In cj p2) by hauto unfold: undirected, coloring_ok.
      qauto use: PositiveSet.inter_spec unfold: PositiveOrderedTypeBits.t, PositiveSet.elt, PositiveSet.Empty, node.
    + assert (S.In ci p2) by sfirstorder.
      assert (S.In cj p1) by hauto unfold: undirected, coloring_ok.
      qauto use: PositiveSet.inter_spec unfold: PositiveOrderedTypeBits.t, PositiveSet.elt, PositiveSet.Empty, node.
    + sfirstorder unfold: coloring_ok.
Qed.

(** ** Congruence of valid colorings under set equality *)
Lemma ok_coloring_set_eq : forall (g : graph) s1 s2 m,
    S.Equal s1 s2 ->
    coloring_ok s1 g m ->
    coloring_ok s2 g m.
Proof. sfirstorder. Qed.

(** ** Weakening of valid colorings under subset relation *)
Lemma ok_coloring_subset : forall (g : graph) s1 s2 m,
    S.Subset s1 s2 ->
    coloring_ok s1 g m ->
    coloring_ok s2 g m.
Proof. sfirstorder. Qed.

(** ** Union of distinct coloring of independent sets is complete *)
(** If two independent sets are colored constantly with different
    colors, then the union of their colorings is complete over the union
    of the independent sets. *)
Lemma constant_col_union_indep_set : forall (g : graph) (s1 s2 : nodeset) c1 c2,
    independent_set g s1 ->
    independent_set g s2 ->
    c1 <> c2 ->
    coloring_complete (SP.of_list [c1;c2]) (subgraph_of g (S.union s1 s2)) (Munion (constant_color s1 c1) (constant_color s2 c2)).
Proof.
  intros g s1 s2 c1 c2 H H0 H2.
  split.
  - intros i Hi.
    rewrite <- Sin_domain in Hi.
    apply subgraph_of_nodes in Hi.
    apply S.union_spec in Hi.
    destruct Hi.
    + apply Munion_in.
      left.
      hecrush use: constant_color_colors.
    + apply Munion_in.
      right.
      hecrush use: constant_color_colors.
  - assert (S.Equal (SP.of_list [c1; c2]) (S.union (S.singleton c1) (S.singleton c2))).
    {
      hauto l: on use: PositiveSet.cardinal_1, SP.add_union_singleton unfold: SP.of_list, fold_right, PositiveSet.singleton, PositiveSet.empty, length, PositiveSet.cardinal.
    }
    symmetry in H1.
    apply (ok_coloring_set_eq _ _ _ _ H1).
    split.
    + intros ci H5.
      apply Munion_case in H5.
      enough (ci = c1 \/ ci = c2).
      {
        sfirstorder use: PositiveSet.singleton_2, PositiveSet.union_2, PositiveSet.union_3 unfold: PositiveSet.singleton.
      }
      hauto q: on use: constant_color_inv2.
    + intros ci cj H5 H6.
      apply Munion_case in H5, H6.
      destruct H5, H6.
      * hauto lq: on rew: off use: subgraph_edges, constant_color_inv unfold: independent_set, PositiveSet.Subset.
      * hauto lq: on rew: off use: constant_color_inv2.
      * hauto q: on use: constant_color_inv2.
      * hauto lq: on rew: off use: subgraph_edges, constant_color_inv unfold: independent_set, PositiveSet.Subset.
Qed.

(** * Phase 2 of Wigderson *)
Function phase2 (g : graph) {measure M.cardinal g} : coloring * graph :=
  match (max_deg g)%nat with
  | 0%nat => (constant_color (nodes g) 1, (@M.empty _))
  | S n => let (ns, g') := extract_vertices_degs g (S n) in
          let (f', g'') := phase2 g' in
          (Munion (constant_color ns (Pos.of_nat (S (S n)))) f', g'')
  end.
Proof.
  intros g n teq.
  intros ns g' teq0.
  replace g' with (snd (ns, g')) by auto.
  rewrite <- teq0.
  rewrite teq0.
  simpl.
  assert (~ S.Empty ns).
  {
    intros contra.
    rewrite extract_vertices_degs_equation in teq0.
    destruct (extract_deg_vert_dec g (S n)) eqn:EE.
    - destruct s as [v Hv].
      simpl in *.
      destruct (extract_vertices_degs (remove_node v g) (S n)) as [s g''].
      inversion teq0.
      subst.
      assert (S.In v (S.add v s)).
      {
        sfirstorder use: SP.Dec.F.add_iff unfold: node, PositiveOrderedTypeBits.t, PositiveSet.elt, nodeset.
      }
      scongruence.
    - inversion teq0.
      subst.
      clear teq0.
      pose proof (max_degree_vert g' (S n) ltac:(hauto use: max_deg_gt_not_empty, nlt_0_r unfold: Peano.lt inv: sumbool) teq).
      contradiction.
  }
  assert (exists v, S.In v ns).
  {
    clear -H.
    destruct (PositiveSet.choose ns) eqn:EE.
    - exists e.
      strivial use: PositiveSet.choose_1 unfold: nodeset.
    - sfirstorder use: PositiveSet.choose_2.
  }
  clear H.
  destruct H0 as [v Hv].
  assert (is_subgraph g' g) by hauto l: on use: extract_vertices_degs_subgraph.
  pose proof (extract_vertices_remove g g' ns (S n) ltac:(auto) v Hv).
  unfold is_subgraph in H.
  assert (~ S.In v (nodes g') /\ S.In v (nodes g)).
  {
    split.
    - destruct H0.
      unfold nodes.
      intros contra.
      apply Sin_domain in contra.
      contradiction.
    - unfold nodes.
      apply Sin_domain.
      qauto l: on.
  }
  enough (S.cardinal (nodes g') < S.cardinal (nodes g))%nat.
  {
    scongruence use: Mcardinal_domain unfold: snd, extract_vertices_degs, PositiveMap.t, nodes, fst inv: R_extract_vertices_degs.
  }
  apply SP.subset_cardinal_lt with (x := v); sauto lq: on rew: off.
Defined.

Functional Scheme phase2_ind := Induction for phase2 Sort Prop.

(** ** Phase 2 on max degree 0 graphs *)
Lemma phase2_0 (g : graph) : max_deg g = 0%nat -> phase2 g = (constant_color (nodes g) 1, @M.empty _).
Proof.
  intros H.
  hauto lq: on use: phase2_equation.
Qed.

Lemma no_selfloop_dec (g : graph) : {no_selfloop g} + {~ no_selfloop g}.
Proof.
  unfold no_selfloop.
  remember (M.elements g) as l.
  refine (_ (Exists_dec (fun (p : M.key * nodeset) => let (a,b) := p in S.In a b) l _)).
  - intros H.
    destruct H.
    + right.
      intros contra.
      apply Exists_exists in e.
      destruct e as [[k n] [Hx Hx']].
      unfold adj in contra.
      rewrite Heql in Hx.
      pose proof (contra k).
      apply H.
      apply M.elements_complete in Hx.
      hauto lq: on.
    + left.
      intros i contra.
      apply n.
      apply Exists_exists.
      unfold adj in contra.
      destruct (M.find i g) eqn:E; [|sauto].
      exists (i, n0).
      sfirstorder use: M.elements_correct.
  - hauto lq: on use: SP.In_dec.
Defined.

Example phase_2_example : coloring_ok (SP.of_list [1;2;4]) ex_graph (fst (phase2 ex_graph)).
Proof.
  split.
  - intros ci Hci.
    apply M.elements_correct in Hci.
    compute in Hci.
    hauto l: on.
  - intros ci cj Hci Hcj.
    apply M.elements_correct in Hci, Hcj.
    compute in Hci.
    compute in Hcj.
    hauto l: on.
Qed.

(* Next steps:
 - how can we know a-priori what colors are used in phase2?
 - prove that the coloring returned by phase2 is ok
 - actually we're trying to prove that phase2 uses _at most_ max_deg + 1 colors
 - the coloring_ok predicate can overapproximate
*)

Definition siota p := SP.of_list (map Pos.of_nat (seq 1 (p + 1))).
Definition phase2_colors g := siota (max_deg g).

(** ** InA to In conversion *)
Lemma InA_iff {A} : forall p (l : list A), (InA Logic.eq p l) <-> In p l.
Proof. induction l; sauto q: on. Qed.

(** ** Specification of siota construction *)
Lemma siota_spec : forall (n : nat), (forall i, (0 <= i <= n + 1)%nat <-> S.In (Pos.of_nat i) (siota n)).
Proof.
  intros n i.
  split; intros H.
  - unfold siota.
    apply SP.of_list_1.
    apply InA_iff.
    apply in_map_iff.
    destruct i; [exists 1%nat|exists (S i)%nat]; hauto l: on use: in_seq.
  - destruct i eqn:He; [sfirstorder|].
    apply SP.of_list_1 in H.
    rewrite InA_iff in H.
    rewrite in_map_iff in H.
    hauto l: on use: in_seq.
Qed.

(** ** Surjectivity of of_nat *)
Lemma of_nat_surj : forall p, exists n, Pos.of_nat n = p.
Proof.
  sfirstorder use: Pos2Nat.id.
Qed.

(** ** Siota subset relation *)
Lemma siota_subset p q : (p <= q)%nat -> S.Subset (siota p) (siota q).
Proof.
  intros H a Ha.
  destruct (of_nat_surj a) as [x <-].
  hfcrush use: siota_spec.
Qed.

(** ** Siota non-membership *)
Lemma siota_miss : forall p q,
    (q + 1 < S p)%nat -> ~ S.In (Pos.of_nat (S p)) (siota q).
Proof.
  intros p q H contra.
  apply siota_spec in contra.
  lia.
Qed.

(* if we have an independent set, we can augment any valid coloring
   with it to obtain another valid coloring *)
(** ** Augmenting a coloring with an independent set  *)
Lemma indep_set_union : forall (g : graph) (f : coloring) (s : nodeset) (p : colors) c,
    undirected g ->
    independent_set g s ->
    ~ S.In c p ->
    coloring_ok p g f ->
    coloring_ok (S.add c p) g (Munion (constant_color s c) f).
Proof.
  intros g f s p c H H0 H1 H2.
  split.
  - intros ci H5.
    apply S.add_spec.
    apply Munion_case in H5.
    destruct H5.
    + left.
      apply constant_color_inv2 in H4.
      assumption.
    + right.
      sfirstorder.
  - intros ci cj H5 H6.
    apply Munion_case in H5, H6.
    destruct H5, H6.
    + intros contra.
      apply constant_color_inv in H4, H5.
      sfirstorder.
    + assert (cj <> c).
      {
        hauto lq: on rew: off unfold: coloring_ok, undirected.
      }
      apply constant_color_inv2 in H4.
      scongruence.
    + assert (ci <> c) by sfirstorder.
      apply constant_color_inv2 in H5.
      scongruence.
    + strivial unfold: coloring_ok.
Qed.

Lemma phase2_color_bound :
  forall (g : graph) (f : coloring) (g' : graph) (i : node) n,
    phase2 g = (f, g') ->
    M.find i f = Some (Pos.of_nat n) ->
    (n <= max_deg g + 1)%nat.
Proof.
  intros g f g' i n H H0.
  generalize dependent g'.
  generalize dependent f.
  functional induction (phase2 g) using phase2_ind.
  - intros f Hf g' Hg'.
    rewrite e in *.
    simpl.
    inversion Hg'.
    subst.
    clear Hg'.
    apply constant_color_inv2 in Hf.
    destruct n as [|[|n']]; sfirstorder.
  - intros f H0 g'0 H.
    inversion H.
    subst g''.
    rewrite <- H2 in H0.
    apply Munion_case in H0.
    destruct H0.
    + apply constant_color_inv2 in H0.
      hauto l: on.
    + pose proof (IHp _ H0 g'0 e1).
      apply extract_vertices_degs_subgraph in e0.
      apply max_deg_subgraph in e0.
      hauto l: on.
Qed.

(* Lemma max_degree_extraction_independent_set0 : forall (g : graph) d, *)
(*     no_selfloop g -> *)
(*     d = max_deg g -> *)
(*     d = 0 -> *)
(*     independent_set g (fst (extract_vertices_degs g d)) /\ *)
(*       (forall k, S.In k (fst (extract_vertices_degs g d)) -> degree k g = Some d). *)
(* Proof. *)
(*   intros go. *)
(*   apply (extract_vertices_degs_ind (fun g d p =>  no_selfloop g -> d = max_deg g -> d = 0 -> independent_set g (fst (extract_vertices_degs g d)) /\ (forall k, S.In k (fst (extract_vertices_degs g d)) -> degree k g = Some d))). *)
(** ** Adjacency preservation in extracted subgraph *)
Lemma difficult :
  forall (g g' : graph) (n : nat) (ns : nodeset),
    (* undirected g -> *)
    (* no_selfloop g -> *)
    max_deg g = S n ->
    extract_vertices_degs g (S n) = (ns, g') ->
    forall i j, M.In i g' -> M.In j g' -> (S.In j (adj g' i) <-> S.In j (adj g i)).
Proof.
  intros g g' n ns H H0 i j H1 H2.
  split; intros H3.
  - apply extract_vertices_degs_subgraph in H0.
    sfirstorder.
  - remember (S n) as d.
    generalize dependent g'.
    revert H.
    generalize dependent i.
    generalize dependent j.
    generalize dependent ns.
    functional induction (extract_vertices_degs g d) using extract_vertices_degs_ind.
    + intros ns j i H3 H g' H0 H1 H2.
      inversion H0.
      subst.
      clear H0.
      pose proof (IHp (@eq_refl _) s j i).
      rewrite <- remove_node_nodes_adj in H0.
      rewrite adj_remove_nodes_spec in H0.
      rewrite e0 in H0.
      apply H0.
      * split.
        ** assumption.
        ** split; intros contra.
           *** destruct v as [v Hv].
               simpl_sigma.
               assert (j = x) by hauto use: PositiveSet.singleton_1 unfold: PositiveMap.key, node.
               subst.
               pose proof (extract_vertices_degs_exhaust (remove_node x g) g' (max_deg g) s ltac:(hauto l: on) ltac:(scongruence)).
               apply H4.
               exists x.
               rewrite H.
               assert (is_subgraph g' (remove_node x g)).
               {
                 hauto l: on use: extract_vertices_degs_subgraph.
               }
               hauto lq: on use: remove_node_not_in.
           *** simpl_sigma.
               assert (i = x) by hauto use: PositiveSet.singleton_1 unfold: PositiveMap.key, node.
               subst.
               pose proof (extract_vertices_degs_exhaust (remove_node x g) g' (max_deg g) s ltac:(hauto l: on) ltac:(scongruence)).
               apply H4.
               exists x.
               rewrite H.
               assert (is_subgraph g' (remove_node x g)).
               {
                 hauto l: on use: extract_vertices_degs_subgraph.
               }
               hauto lq: on use: remove_node_not_in.
      * destruct v as [v Hv].
        simpl_sigma.
        admit.
      * reflexivity.
      * assumption.
      * assumption.
    + intros ns j i H3 H g' H0 H1 H2.
      scongruence.
Admitted.

Proof.
(** ** Adjacency preservation in extracted subgraph (again) *)
Lemma asfadsf:
  forall (g g' : graph) (i j : node) (n : nat) (ns : nodeset),
    undirected g ->
    no_selfloop g ->
    max_deg g = S n ->
    extract_vertices_degs g (S n) = (ns, g') ->
    S.In j (adj g i) ->
    S.In j (adj g' i).
Proof.
  (* intros g g' i j ci cj n ns H H0 H1. *)
  intros g g' i j n ns H H0 H1 H2 H3.
  generalize dependent ns.
  generalize dependent i.
  generalize dependent j.
  generalize dependent g'.
  generalize dependent n.  
  functional induction (extract_vertices_degs g) using phase2_ind.
  - scongruence.
  - intros n0 H1 g'0 j i H3 ns0 H2.
    pose proof (extract_vertices_max_degs g0 g' ns ltac:(hauto l: on) ltac:(scongruence)).
    pose proof (max_degree_extraction_independent_set _ _ H H0 (eq_sym e)).
    rewrite e0 in H5.
    simpl in H5.
    rename g'0 into g'''.
    assert (undirected g') by best use: extract_vertices_degs_undirected.
    assert (no_selfloop g').
    {
      admit.
    }
    (* eapply IHp; eauto. *)
    (* + hammer. *)
    
    
    (* pose proof (IHp) *)
    (* best unfold: independent_set. *)
    (* destruct (max_deg g') eqn:EE. *)
    (* + hammer. *)
    (* hammer. *)
  (*   pose proof (IHp ). *)
Admitted.


Lemma max_deg_remove_node :
  forall (n : nat) (g : graph) (v x : node),
    degree v g = Some n ->
    degree x g = Some n ->
    max_deg g = n ->
    ~ S.In x (adj g v) ->
    x <> v ->
    max_deg (remove_node x g) = n.
Proof.
  intros n g v x H H0 H1 H2 H3.
  destruct n.
  {
    ecrush use: Arith.PeanoNat.Nat.nlt_0_r, Wigderson.subgraph.remove_node_subgraph, Wigderson.subgraph.max_deg_subgraph, H1.
  }
  assert (is_subgraph (remove_node x g) g) by apply remove_node_subgraph.
  assert ((max_deg (remove_node x g) <= (S n))%nat) by hauto l: on use: max_deg_subgraph.
  apply le_lt_or_eq in H5.
  destruct H5; [|assumption].
  assert (M.In v (remove_node x g)).
  {
    apply remove_node_neq.
    - auto.
    - hauto l: on unfold: degree.
  }
  destruct H6 as [e He].
  assert (M.In v g) by hauto l: on unfold: degree.
  assert (degree v (remove_node x g) = Some (S n)).
  {
    unfold degree.
    unfold adj in H2.
    rewrite He.
    destruct H6 as [e' He'].
    hfcrush use: SP.remove_cardinal_2, remove_node_find unfold: PositiveMap.MapsTo, nodeset, PositiveOrderedTypeBits.t, node, PositiveSet.elt, degree inv: option.
  }
  pose proof (max_deg_max (remove_node x g) _ _ He).
  hauto lq: on use: Znat.Nat2Z.inj_le, Znat.Nat2Z.inj_gt unfold: PositiveMap.MapsTo, nodeset, BinInt.Z.gt, BinInt.Z.le, gt, degree.
Qed.
    
(** ** Correctness of phase2 coloring *)
Lemma barbar :
  forall (g g' : graph) (i j ci cj : node) (f : coloring),
    undirected g ->
    no_selfloop g ->
    (* extract_vertices_degs g (S n) = (ns, g') -> *)
    phase2 g = (f, g') ->
    S.In j (adj g i) ->
    M.find i f = Some ci ->
    M.find j f = Some cj ->
    ci <> cj.
Proof.
  intros g g' i j ci cj f H H0 H1 H2 H3 H4.
  generalize dependent g'.
  generalize dependent f.
  (* revert H2. *)
  functional induction (phase2 g) using phase2_ind.
  - intros f H3 H4 g' H1.
    inversion H1.
    subst.
    sauto lq: on rew: off use: max_deg_0_adj.
  - intros f H3 H4 g'0 H1.
    assert (undirected g') by hauto l: on use: extract_vertices_degs_undirected.
    assert (no_selfloop g') by hauto l: on use: extract_vertices_degs_subgraph, subgraph_no_selfloop.
    specialize (IHp H5 H6).
    inversion H1.
    clear H1.
    subst g'0.
    replace (Pos.succ _) with (Pos.of_nat (S (S n))) in H8 by auto.
    subst f.
    apply Munion_case in H4, H3.
    (* we have the following cases:
   - i and j are colored now, but that means they cannot be adjacent (contradiction)
   - i is colored now and j is colored later, so their colors are not equal
   - j is colored now and i is colored later, so their colors are not equal
   - i and j are both colored later, but by IH their colors are not equal
     *)
    destruct H4, H3.
    + (* case: they are both colored now, but contradiction since max
         degree are independent sets *)
      apply constant_color_inv in H1, H3.
      assert (independent_set g ns).
      {
        pose proof (max_degree_extraction_independent_set _ _ H H0 (eq_sym e)).
        rewrite e0 in H4.
        simpl in H4.
        hauto lq: on.
      }
      hauto l: on unfold: independent_set.
    + (* case: they are both colored now, but contradiction *)
      destruct (of_nat_surj ci) as [x <-].
      pose proof (phase2_color_bound g' _ _ _ _ e1 H3).
      apply constant_color_inv2 in H1.
      intros contra.
      rewrite <- H1 in contra.
      assert (x <= max_deg g + 1)%nat by lia.
      pose proof (extract_vertices_max_degs g g' ns ltac:(hauto l: on) ltac:(scongruence)).
      lia.
    + (* case: they are both colored now, but contradiction *)
      destruct (of_nat_surj cj) as [x <-].
      pose proof (phase2_color_bound g' _ _ _ _ e1 H1).
      apply constant_color_inv2 in H3.
      intros contra.
      rewrite <- H3 in contra.
      assert (x <= max_deg g + 1)%nat by lia.
      pose proof (extract_vertices_max_degs g g' ns ltac:(hauto l: on) ltac:(scongruence)).
      lia.
    + assert (S.In j (adj g' i)).
      {
        (* need a lemma that since i and j are not in ns, then they
        are both in g' and adjacent, since one step of
        extract_vertices_degs never changes adjacency *)
        strivial use: asfadsf.
      }
      pose proof (IHp H4 f' H3 H1 g'' e1).
      assumption.
Qed.


  (**)
  (* i gets colored now (it's a max degree vertex) and j gets colored
     later, but this means that the colors are not equal *)

  
(** ** Adjacency preservation in extracted subgraph (again) *)
Lemma adfadsf:
  forall (g : graph) (n : nat) (ns : nodeset) (g' : graph) (i j ci cj : node)
    (f : coloring) (g'' : graph),
    max_deg g = S n ->
    extract_vertices_degs g (S n) = (ns, g') ->
    phase2 g' = (f, g'') ->
    S.In j (adj g i) -> M.find i f = Some ci -> M.find j f = Some cj -> S.In j (adj g' i).
Proof.
  intros g n ns g' i j ci cj f g'' H H0 H1 H2 H3 H4.
  destruct (SP.In_dec j (adj g' i)); [assumption|].
  exfalso.
  (* we can get a contradiction here because we know that there are
     the following cases: *)
  (* i gets colored now (it's a max degree vertex) and j gets colored
     later, but this means that the colors are not equal *)
Admitted.
(* Lemma foobar: *)
(*   forall (g' : graph) (f' : coloring) (g'' : graph) (i : node) (j : S.elt) (ci cj : node), *)
(*     phase2 g' = (f', g'') -> M.find i f' = Some ci -> M.find j f' = Some cj -> S.In j (adj g' i). *)
(* Proof. *)
(* Admitted. *)
(* Lemma asdfl: *)
(*   forall (g : graph) (n : nat) (ns : nodeset) (g' : graph) (i j ci cj : node) (f : coloring) (g'' : graph), *)
(*     no_selfloop g -> *)
(*     max_deg g = S n -> *)
(*     extract_vertices_degs g (S n) = (ns, g') -> *)
(*     phase2 g' = (f, g'') -> *)
(*     coloring_ok (siota (max_deg g')) g' f -> *)
(*     S.In j (adj g i) -> *)
(*     M.find i f = Some ci -> *)
(*     M.find j f = Some cj -> *)
(*     ci <> cj. *)
(* Proof. *)
(*   intros g n ns g' i j ci cj f g'' Hl H H0 H1 H2 H3 H4 H5. *)
(*   assert (Sg: is_subgraph g' g). *)
(*   { *)
(*     pose proof (extract_vertices_degs_subgraph g (S n)). *)
(*     rewrite H0 in *. *)
(*     assumption. *)
(*   } *)
(*   unfold coloring_ok in H2. *)
(*   assert (S.In j (adj g' i)). *)
(*   { *)
(*     hauto l: on use: adfadsf. *)
(*   } *)
(*   pose proof (proj2 (H2 i j H6) _ _ H4 H5). *)
(*   assumption. *)
(* Qed. *)

                     Lemma phase2_ok : forall (g : graph),
    undirected g ->
    no_selfloop g ->
    coloring_ok (phase2_colors g) g (fst (phase2 g)).
Proof.
  intros g H H0.
  functional induction (phase2 g) using phase2_ind.
  - sfirstorder use: max_deg_0_adj unfold: coloring_ok.
  - remember (Pos.of_nat (S (S n))) as n'.
    rewrite e1 in *.
    simpl in IHp.
    assert (undirected g') by strivial use: extract_vertices_degs_undirected.
    assert (no_selfloop g') by hauto l: on use: extract_vertices_degs_subgraph, subgraph_no_selfloop.
    pose proof (IHp H1 H2).
    simpl.
    pose proof (max_degree_extraction_independent_set g (S n) H H0 (eq_sym e)).
    rewrite e0 in H4.
    simpl in H4.
    destruct H4.
    unfold phase2_colors in *.
    remember (SP.of_list (map Pos.of_nat (seq 1 (max_deg g' + 1)))) as s'.
    remember (SP.of_list (map Pos.of_nat (seq 1 (max_deg g + 1)))) as s.
    assert (max_deg_graphs: (max_deg g' < max_deg g)%nat).
    {
      hfcrush use: extract_vertices_max_degs, nlt_0_r unfold: Peano.lt inv: sumbool.
    }
    assert (S.Subset s' s).
    {
      subst s'.
      subst s.
      pose proof (siota_subset (max_deg g') (max_deg g) ltac:(hauto l:on)).
      assumption.
    }
    assert (~ S.In n' s').
    {
      subst n' s'.
      rewrite e in *.
      intros contra.
      rewrite <- e in max_deg_graphs.
      rewrite <- e in contra.
      assert (max_deg g' + 1 < S (max_deg g))%nat.
      {
        hauto l: on.
      }
      qauto l: on use: siota_miss.
    }
    pose proof (constant_col_indep_set g ns n' H4).
    assert (S.Empty (S.inter (S.singleton n') s')).
    {
      clear -H7.
      hfcrush use: SP.Dec.F.mem_iff, SP.Dec.F.singleton_iff, PositiveSet.inter_spec unfold: PositiveSet.In, PositiveSet.elt, PositiveSet.Empty.
    }
    assert (coloring_ok (S.singleton n') g (constant_color ns n')).
    {
      split.
      - intros ci H12.
        apply constant_color_inv2 in H12.
        hauto l: on use: PositiveSet.singleton_2.
      - intros ci cj H12 H13.
        assert (S.In i ns) by hauto l: on use: constant_color_inv.
        assert (S.In j ns) by hauto l: on use: constant_color_inv.
        exfalso.
        hauto l: on unfold: independent_set.
    }
    assert (coloring_ok (siota (max_deg g')) g f').
    {
      clear IHp.
      split.
      - intros ci H12.
        destruct (of_nat_surj ci) as [x <-].
        apply siota_spec.
        hauto l: on use: phase2_color_bound.
      - intros ci cj H12 H13.
        hauto lq: on use: adfadsf unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, coloring_ok, node.
    }
    pose proof (indep_set_union g f' ns (siota (max_deg g')) n' H H4 ltac:(hauto l: on)).
    assert (S.Subset (S.add n' (siota (max_deg g'))) (siota (max_deg g))).
    {
      intros a Ha.
      apply S.add_spec in Ha.
      destruct Ha.
      - subst. rewrite e.
        clear -n.
        sauto l: on use: siota_spec.
      - hauto l: on.
    }
    hauto l: on use: ok_coloring_subset.
Qed.
