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
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
Import Arith.
Import ListNotations.
Import Nat.

Definition colors := S.t.

Lemma map_o {A} : forall (m : M.t A) (x : M.key) f,
 @M.find A x (M.map f m) = Datatypes.option_map f (M.find x m).
Proof.
  scongruence use: WF.map_o.
Qed.

(* A coloring is complete if every vertex is colored. *)
Definition coloring_complete (palette: colors) (g: graph) (f: coloring) :=
 (forall i, M.In i g -> M.In i f) /\ coloring_ok palette g f.

Definition two_colors: colors := SP.of_list [1; 2]%positive.
Definition three_colors: colors := SP.of_list [1; 2; 3]%positive.

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
    hauto use: SP.Dec.F.empty_iff, PositiveMap.gempty unfold: PositiveOrderedTypeBits.t, PositiveSet.In, node, PositiveMap.key inv: option.
  - unfold adj in H.
    ssimpl.
    scongruence use: PositiveMap.gempty unfold: PositiveMap.key, node, PositiveOrderedTypeBits.t.
Qed.

Lemma set_elemeum s : S.Equal s (fold_right S.add S.empty (S.elements s)).
Proof.
  strivial use: SP.of_list_3 unfold: SP.of_list, SP.to_list, PositiveSet.Equal.
Qed.

  
(* Elements of a 2-element set can be extracted *)
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
Lemma subgraph_coloring_ok : forall (g g' : graph) f p,
    is_subgraph g' g ->
    coloring_ok p g f ->
    coloring_ok p g' f.
Proof.
  intros g g' f p H H0 H1.
  qauto unfold: PositiveSet.Subset, coloring_ok, is_subgraph.
Qed.

Lemma subgraph_coloring_complete : forall (g g' : graph) f p,
    is_subgraph g' g ->
    coloring_complete p g f ->
    coloring_complete p g' f.
Proof.
  intros g g' f p H H0.
  hauto lq: on use: subgraph_coloring_ok, subgraph_vert_m.
Qed.

Definition n_coloring (f : coloring) (p : colors) (n : nat) :=
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

Definition restrict_on_nbd (f : coloring) (g : graph) (v : node) :=
  restrict f (nodes (neighborhood g v)).

(* The neighborhood of a (n+1)-colorable graph is n-colorable *)
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
      pose proof (subgraph_coloring_ok _ _ f p H2 ltac:(sauto)).
      split.
      * intros ci0 H6.
        assert (S.In j (adj g i)) by sfirstorder.
        qauto use: nbd_adj, PositiveSet.remove_spec, @restrict_agree, @restrict_in_set unfold: PositiveSet.elt, node, PositiveOrderedTypeBits.t, coloring_ok, coloring, nodes, coloring_complete, PositiveMap.key.
      * intros ci0 cj H5 H6.
        qauto use: @restrict_agree unfold: PositiveOrderedTypeBits.t, node, PositiveMap.key, PositiveSet.elt, coloring, coloring_ok.
Qed.
  
Lemma nbd_2_colorable_3 : forall (g : graph) (f : coloring) p,
    coloring_complete p g f ->
    three_coloring' f p ->
    forall v ci, M.find v f = Some ci ->
            two_coloring' (restrict_on_nbd f g v) (S.remove ci p) /\
              coloring_complete (S.remove ci p) (neighborhood g v) (restrict_on_nbd f g v).
Proof.
  hauto l: on use: SP.remove_cardinal_1, nbd_Sn_colorable_n unfold: PositiveOrderedTypeBits.t, three_coloring', node, two_coloring', n_coloring, PositiveSet.elt inv: nat.
Qed.

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
          (~ two_coloring' (restrict_on_nbd f g v) (S.remove ci p))) ->
    ~ three_coloring' f p.
Proof.
  qauto l: on use: nbd_2_colorable_3.
Qed.

Definition constant_color {A} (s : nodeset) c := S.fold (fun v => M.add v c) s (@M.empty A).

Lemma constant_color_colors {A} s c : forall i, S.In i s -> M.find i (@constant_color A s c) = Some c.
Proof.
  intros i Hi.
  unfold constant_color.
  generalize dependent Hi.
  apply SP.fold_rec_bis.
  - sfirstorder.
  - sauto q: on.
  - intros x a s' H H0 H1 Hi.
    qauto use: WF.add_o, PositiveSet.add_3, PositiveMap.gss unfold: PositiveMap.key, PositiveSet.elt inv: sumbool.
Qed.

Lemma constant_color_inv {A} s c : forall i, M.In i (@constant_color A s c) -> S.In i s.
Proof.
  intros i.
  unfold constant_color.
  apply SP.fold_rec_bis.
  - sfirstorder.
  - sauto q: on.
  - intros x a s' H H0 H1 H2.
    destruct (E.eq_dec i x).
    + subst. hauto l: on use: PositiveSet.add_1 unfold: PositiveMap.key, PositiveSet.elt.
    + hauto use: WF.add_neq_in_iff, PositiveSet.add_2 unfold: PositiveSet.elt, PositiveMap.key.
Qed.

Lemma constant_color_inv2 {A} s c : forall i d, M.find i (@constant_color A s c) = Some d -> c = d.
Proof.
  intros i d.
  unfold constant_color.
  apply SP.fold_rec_bis.
  - sfirstorder.
  - sauto dep: on.
  - intros x a s' H H0 H1 H2.
    destruct (E.eq_dec i x).
    + scongruence use: PositiveMap.gss unfold: PositiveSet.elt, PositiveMap.key.
    + hauto use: PositiveMap.gso unfold: PositiveMap.key, PositiveSet.elt.
Qed.

(* two_color_step
 - let g be a graph, v be a vertex, c1 and c2 the colors we have
 - this function colors v with c1 and colors its neighbors with c2
 *)
Definition two_color_step (g : graph) (v : node) c1 c2 (f : coloring) : coloring :=
  M.add v c1 (constant_color (adj g v) c2).

Lemma two_color_step_colors_v_c1 : forall g v c1 c2 f, M.find v (two_color_step g v c1 c2 f) = Some c1.
Proof.
  scongruence use: PositiveMap.gss unfold: PositiveOrderedTypeBits.t, node, PositiveMap.key, adj, nodeset, two_color_step.
Qed.

Lemma two_color_step_colors_adj_c2 : forall g v c1 c2 f i,
    no_selfloop g -> S.In i (adj g v) -> M.find i (two_color_step g v c1 c2 f) = Some c2.
Proof.
  hauto use: PositiveMap.gso, @constant_color_colors unfold: two_color_step, PositiveSet.In, PositiveOrderedTypeBits.t, nodeset, node, PositiveSet.t, PositiveMap.key, PositiveSet.empty, PositiveSet.elt, no_selfloop, adj.
Qed.

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
    qauto use: WF.in_find_iff, @constant_color_inv unfold: nodeset, adj, node, PositiveMap.key, PositiveOrderedTypeBits.t.
Qed.

Lemma undirected_adj_in : forall (g : graph) (v : node) i , undirected g -> S.In i (adj g v) -> M.In i g.
Proof.
  intros g v i H H0.
  hauto use: SP.Dec.F.empty_iff unfold: PositiveOrderedTypeBits.t, PositiveSet.elt, undirected, node, PositiveMap.MapsTo, adj, PositiveMap.In.
Qed.

Lemma in_two_set_inv : forall i a b, S.In i (SP.of_list [a;b]) -> i = a \/ i = b.
Proof.
  intros i a b H.
  qauto use: PositiveSet.singleton_1, PositiveSet.add_spec, PositiveSet.cardinal_1 unfold: fold_right, PositiveSet.empty, length, SP.of_list, PositiveSet.cardinal, PositiveSet.singleton.
Qed.

Lemma two_color_step_correct : forall (g : graph) (v : node) c1 c2,
    c1 <> c2 ->
    no_selfloop g ->
    undirected g ->
    M.In v g ->
    (exists m, two_coloring' m (SP.of_list [c1;c2]) /\ coloring_complete (SP.of_list [c1;c2]) g m) ->
    coloring_ok (SP.of_list [c1;c2]) g (two_color_step g v c1 c2 (@M.empty _)).
Proof.
  intros g v c1 c2 Hc H Hu magic H0.
  split.
  - intros ci H2.
    unfold two_color_step in H2.
    destruct (E.eq_dec i v).
    + subst. hauto use: PositiveMap.gss, PositiveSet.add_1 unfold: PositiveSet.empty, PositiveOrderedTypeBits.t, PositiveMap.key, node, adj, PositiveSet.elt, nodeset, PositiveSet.t, fold_right, SP.of_list.
    + rewrite M.gso in H2 by auto.
      pose proof (constant_color_inv (adj g v) c2 i ltac:(sfirstorder)).
      pose proof (constant_color_colors (adj g v) c2 _ H3).
      qauto use: @constant_color_colors, PositiveSet.add_2, PositiveSet.add_1 unfold: PositiveSet.elt, node, adj, PositiveOrderedTypeBits.t, nodeset, fold_right, SP.of_list.
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
      hauto l: on use: two_color_step_colors_adj_c2, two_color_step_colors_v_c1 unfold: PositiveSet.elt, PositiveOrderedTypeBits.t, node, PositiveMap.key, coloring.
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
      destruct H0 as [m [p [Hm Hm']]].
      pose proof (Hm i ltac:(sauto use: undirected_adj_in)).
      pose proof (Hm j ltac:(sauto use: undirected_adj_in)).
      pose proof (Hm v ltac:(sauto use: undirected_adj_in)) as H8.
      destruct H0 as [ii Hii].
      destruct H7 as [jj Hjj].
      destruct H8 as [vv Hvv].
      unfold M.MapsTo in *.
      assert (ii = c1 \/ ii = c2).
      {
        sauto lq: on rew: off use: in_two_set_inv unfold: two_coloring', n_coloring.
      }
      assert (jj = c1 \/ jj = c2).
      {
        sauto lq: on rew: off use: in_two_set_inv unfold: two_coloring', n_coloring.
      }
      assert (vv = c1 \/ vv = c2).
      {
        sauto lq: on rew: off use: in_two_set_inv unfold: two_coloring', n_coloring.
      }
      (* So i and j have colors given by the magic coloring function,
         but no matter what colors we give them something is going to go
         wrong *)
      destruct H0, H7, H8; strivial unfold: coloring_ok.
Qed.

Lemma two_color_step_complete : forall (g : graph) (v : node) c1 c2,
    c1 <> c2 ->
    no_selfloop g ->
    undirected g ->
    M.In v g ->
    (exists m, two_coloring' m (SP.of_list [c1;c2]) /\ coloring_complete (SP.of_list [c1;c2]) g m) ->
    coloring_complete (SP.of_list [c1;c2]) (subgraph_of g (nodes (neighborhood g v))) (two_color_step g v c1 c2 (@M.empty _)).
Proof.
  intros g v c1 c2 H H0 H1 H2 H3.
  split.
  - intros i H4.
    apply Sin_domain in H4.
    qauto use: two_color_step_colors_adj_c2, nbd_adj, WF.in_find_iff, subgraph_of_nodes.
  - qauto l: on use: two_color_step_correct, subgraph_of_is_subgraph, subgraph_coloring_ok.
Qed.

(* If a coloring is not complete then it misses a vertex (constructively *)
Lemma not_complete_has_uncolored (f : coloring) (g : graph) p :
  ~ coloring_complete p g f ->
  ~ M.Empty g ->
  { v | M.In v g /\ ~ M.In v f }.
Proof.
  intros Hf Hg.
  unfold coloring_complete in Hf.
Admitted.

(* If a graph has max degree 0 then the constant coloring is a complete coloring. *)
Lemma max_deg_0_constant_col : forall (g : graph) c,
    max_deg g = 0%nat ->
    coloring_complete (S.singleton c) g (constant_color (nodes g) c).
Proof.
  intros g c H.
  split.
  - sauto use: constant_color_colors, Sin_domain.
  - split; sfirstorder use: max_deg_0_adj.
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


(* If a graph has a vertex of degree d then color that vertex with c *)





(* maybe we just use a "larger unit of operation" on each function call
   remove all the max degree vertices then color them *)

(* TODO: map over a set to produce new sets *)


Function phase2 (g : graph) {measure max_deg g} : coloring * graph :=
  match (max_deg g)%nat with
  | 0%nat => (constant_color (nodes g) 1, (@M.empty _))
  | S n => let (ns, g') := extract_vertices_deg g (S n) in
          let ns' := SP.of_list (map fst ns) in
          let (f', g'') := phase2 g' in
          (Munion (constant_color ns' (Pos.of_nat (S (S n)))) f', g'')
  end.
Proof.
  intros g n teq.
  intros ns g' teq0.
  replace g' with (snd (ns, g')) by auto.
  rewrite <- teq0.
  hfcrush use: nlt_0_r, max_deg_subgraph, extract_vertices_deg_subgraph, le_lt_or_eq, extract_vertices_max_deg unfold: Peano.lt, snd, extract_vertices_deg inv: sumbool.
Defined.

(* Functional Scheme phase2_ind := Induction for phase2 Sort Prop. *)

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
      split.
      * hauto l: on use: M.elements_correct.
      * assumption.
  - intros x.
    destruct x.
    apply SP.In_dec.
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

(* Need to define an induction principle for graphs on max degree. *)
(* Given a graph g, to prove P holds on g, then
 - if max_deg g = 0, then use H0
 - if max_deg g = Sn, then remove all the vertices of max degree and prove
   if P holds on the subgraph then it holds on the graph with the vertices placed back,
 - then P holds on all g.
 *)
Lemma max_deg_ind (P : graph -> Prop)
    (H0: forall g, max_deg g = 0%nat -> P g)
    (IH: forall g n, (forall g', (max_deg g' <= n)%nat -> P g') -> max_deg g = S n -> P g) :
    (forall g, P g).
Proof.
assert (indnew : forall (n : nat) (g : graph), (max_deg g <= n)%nat -> P g).
{ induction n; sauto lq: on rew: off. }
hauto l: on.
Qed.
  

Lemma phase2_n_adj : forall g i j,
  i <> j ->
  undirected g ->
  no_selfloop g ->
  M.In i (fst (phase2 g)) ->
  M.In j (fst (phase2 g)) ->
  ~ S.In i (adj g j).
Proof.
  (* how to proceed?  without loss of generality i occurs before j,
  then there is a sequence of extractions of max degree vertices between them*)
  intros g.
  pattern g.
  apply max_deg_ind.
  - hauto l: on use: max_deg_0_adj.
  - intros g0 n H H0 i j H1 H2 H3 H4 H5.
    rewrite phase2_equation in H4, H5.
    rewrite H0 in H4, H5.
    simpl in H4, H5.
    remember (extract_vertices_deg g0 (S n)) as k.
    destruct k as [ns g'].
    destruct (phase2 g') as [f' g''] eqn:E.
    assert ((max_deg g' <= n)%nat).
    {
      hauto lq: on use: phase2_tcc, le_ngt unfold: Peano.lt.
    }
    remember (map fst ns) as l.
    remember (constant_color (SP.of_list l)
                  match n with
                  | 0%nat => 1
                  | S _ => Pos.succ (Pos.of_nat n)
                  end) as mns.
    simpl in H4, H5.
    destruct H4 as [ci Hci].
    destruct H5 as [cj Hcj].
    apply Munion_case in Hci, Hcj.
    admit.
Admitted.


  
(* let d be the max degree,
   remove, (using other rec algo) vertices of degree d
   - if you remove a vertex i and some j adj to i then j does not have deg d anymore after removal
   - so
 *)
