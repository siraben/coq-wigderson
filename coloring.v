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

Create HintDb coloring_spec.

Add Hammer Filter Coq.Numbers.BinNums.
Add Hammer Filter Coq.micromega.RingMicromega.
Add Hammer Filter Coq.micromega.Tauto.
Add Hammer Filter Coq.micromega.ZifyClasses.
Add Hammer Filter Coq.micromega.VarMap.
Add Hammer Filter Coq.micromega.ZMicromega.
Add Hammer Filter Coq.Vectors.VectorDef.
Add Hammer Filter Coq.Vectors.VectorSpec.
Add Hammer Filter Coq.Lists.SetoidList.
Add Hammer Filter Coq.micromega.EnvRing.
Add Hammer Filter Coq.funind.Recdef.
Set Hammer ReconstrLimit 10.

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
  hauto lq: on use: SP.Dec.F.empty_iff unfold: PositiveSet.In, adj.
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
  sfirstorder use: max_deg_empty, max_deg_0_adj unfold: empty_graph, coloring_ok.
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

(* Core find-spec for the neighborhood restriction *)
Lemma restrict_on_nbd_find_iff f g v i c :
  M.find i (restrict_on_nbd f g v) = Some c
  <-> S.In i (nodes (neighborhood g v)) /\ M.find i f = Some c.
Proof.
  hauto l: on use: @restrict_find_some_iff unfold: coloring, restrict_on_nbd.
Qed.

(* Domain of the restriction *)
Lemma restrict_on_nbd_domain_spec f g v :
  S.Equal (Mdomain (restrict_on_nbd f g v))
          (S.inter (nodes (neighborhood g v)) (Mdomain f)).
Proof.
  hfcrush use: @domain_restrict_eq, SP.inter_sym unfold: PositiveSet.Equal, coloring, restrict_on_nbd.
Qed.

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
    + hauto use: @restrict_agree unfold: coloring, n_coloring, three_coloring.
    + sfirstorder.
    + (* let x be a neighbor of v *)
      intros x contra.
      assert (S.In x (adj g v)).
      {
        hauto q: on use: nbd_adj, @restrict_in_set, WF.in_find_iff.
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
      * intros ci0 H5.
        hauto l: on use: S.remove_spec, restrict_on_nbd_find_iff, nodes_neighborhood_spec unfold: coloring_ok, coloring_complete.

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
    + qauto use: SP.Dec.F.add_iff, PositiveMap.gso.
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


Lemma constant_color_find_iff (s : S.t) (c : node) i :
  M.find i (constant_color s c) = Some c <-> S.In i s.
Proof.
  sauto lq: on use: @constant_color_inv, @constant_color_colors unfold: PositiveSet.elt, nodeset, PositiveMap.key.
Qed.
#[global] Hint Rewrite constant_color_find_iff : coloring_spec.


Lemma constant_color_find_some_iff (s : S.t) (c d : node) i :
  M.find i (constant_color s c) = Some d <-> S.In i s /\ d = c.
Proof.
  hauto use: constant_color_find_iff, @constant_color_inv unfold: nodeset.
Qed.

Lemma domain_constant_color (s : S.t) (c : node) :
  S.Equal (Mdomain (constant_color s c)) s.
Proof.
  intro i; split; intro Hi.
  - (* -> *)
    rewrite Sin_domain in Hi.
    strivial use: constant_color_find_some_iff unfold: PositiveMap.key, PositiveSet.elt, PositiveMap.MapsTo, PositiveMap.In.
  - (* <- *) apply Sin_domain. (* show M.In i (constant_color s c) *)
    exists c. now apply constant_color_colors.
Qed.


(** * 2-color step *)
(** Let [g] be a graph, [v] be a vertex, $c_1$ and $c_2$ the colors we
have that this function colors [v] with $c_1$ and colors its neighbors
with $c_2$. *)

Definition two_color_step (g : graph) (v : node) c1 c2 (f : coloring) : coloring :=
  M.add v c1 (constant_color (adj g v) c2).


(* One-shot lookup characterization *)
Lemma two_color_step_find_iff g v c1 c2 f j ci :
  M.find j (two_color_step g v c1 c2 f) = Some ci
  <-> (j = v /\ ci = c1) \/ (j <> v /\ S.In j (adj g v) /\ ci = c2).
Proof.
  unfold two_color_step.
  destruct (E.eq_dec j v) as [->|Hneq].
  - rewrite PositiveMap.gss. firstorder congruence.
  - rewrite PositiveMap.gso by exact Hneq.
    rewrite constant_color_find_some_iff.
    firstorder congruence.
Qed.


Lemma two_color_step_domain_spec g v c1 c2 f :
  S.Equal (Mdomain (two_color_step g v c1 c2 f)) (S.add v (adj g v)).
Proof.
  intro j; split; intro Hj.
  - hauto use: PositiveSet.add_spec, PositiveSet.add_2, Sin_domain, two_color_step_find_iff unfold: node, coloring, PositiveMap.In, PositiveMap.MapsTo, nodeset, adj, PositiveSet.elt, PositiveMap.key, PositiveOrderedTypeBits.t.
  - apply Sin_domain; destruct (E.eq_dec j v).
    + sfirstorder use: PositiveMap.gss unfold: PositiveMap.MapsTo, adj, PositiveSet.elt, PositiveMap.In, PositiveMap.key, two_color_step, nodeset.
    + hauto lq: on use: PositiveSet.add_3, two_color_step_find_iff unfold: PositiveOrderedTypeBits.t, adj, PositiveSet.elt, nodeset, node, PositiveMap.MapsTo, PositiveMap.In, PositiveMap.key.
Qed.

(** ** Vertex is colored $c_1$ *)
Lemma two_color_step_colors_v_c1 : forall g v c1 c2 f, M.find v (two_color_step g v c1 c2 f) = Some c1.
Proof.
  hfcrush use: two_color_step_find_iff.
Qed.

(** ** Neighbors are colored $c_2$ *)
Lemma two_color_step_colors_adj_c2 : forall g v c1 c2 f i,
    i <> v -> S.In i (adj g v) -> M.find i (two_color_step g v c1 c2 f) = Some c2.
Proof.
  hfcrush use: two_color_step_find_iff.
Qed.



(** ** Vertex colored by 2-color step is either [v] or a neighbor *)
Lemma two_color_step_inv : forall g v c1 c2 f ci j,
    M.find j (two_color_step g v c1 c2 f) = Some ci ->
    j = v \/ S.In j (adj g v).
Proof.
  qauto use: two_color_step_find_iff.
Qed.

(** ** Adjacency in undirected graphs *)
Lemma undirected_adj_in : forall (g : graph) (v : node) i , undirected g -> S.In i (adj g v) -> M.In i g.
Proof.
  hauto use: SP.Dec.F.empty_iff unfold: undirected, adj.
Qed.

(** ** Membership of a two-element set *)
Lemma in_two_set_inv : forall i a b, S.In i (SP.of_list [a;b]) -> i = a \/ i = b.
Proof.
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
    apply two_color_step_find_iff in H2.
    hauto q: on use: PositiveSet.add_spec unfold: fold_right, SP.of_list.
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
    + rewrite two_color_step_colors_adj_c2 in H2, H3; auto; [|sfirstorder|sfirstorder].
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
    rewrite nodes_subgraph_of_spec in H4.
    qauto use: WF.in_find_iff, nodes_neighborhood_spec, two_color_step_colors_adj_c2 unfold: PositiveMap.key, PositiveOrderedTypeBits.t, coloring, PositiveSet.elt, node.
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
  - hfcrush use: adj_subgraph_of_spec unfold: independent_set.
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
    rewrite nodes_subgraph_of_spec in Hi.
    hecrush use: constant_color_colors, subgraph_of_is_subgraph.
  -
    apply indep_set_ok.
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
  hfcrush use: max_degree_extraction_independent_set, constant_col_indep_set.
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
    apply nodes_subgraph_of_spec in Hi.
    destruct Hi.
    rewrite S.union_spec in H3.
    destruct H3.
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
