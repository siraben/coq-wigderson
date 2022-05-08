Require Import graph.
Require Import subgraph.
Require Import restrict.
Require Import List.
Require Import Setoid.  (* Generalized rewriting *)
Require Import FSets.   (* Efficient functional sets *)
Require Import FMaps.   (* Efficient functional maps *)
Require Import PArith.
Require Import Decidable.
Require Import Program.
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

(* The neighborhood of an (n+1)-colorable graph is n-colorable *)
Lemma nbd_Sn_colorable_n : forall (g : graph) (f : coloring) p n,
    coloring_complete p g f ->
    n_coloring f p (S n) ->
    forall v ci, M.find v f = Some ci ->
            n_coloring (restrict f (nodes (neighborhood g v))) (S.remove ci p) n
            /\ coloring_complete (S.remove ci p) (neighborhood g v) (restrict f (nodes (neighborhood g v))).
Proof.
  intros g f p n H H0 v ci H1.
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
      pose proof (subgraph_colorable _ _ f p H2 ltac:(sauto)).
      split.
      * intros ci0 H6.
        assert (S.In j (adj g i)) by sfirstorder.
        qauto use: nbd_adj, PositiveSet.remove_spec, @restrict_agree, @restrict_in_set unfold: PositiveSet.elt, node, PositiveOrderedTypeBits.t, coloring_ok, coloring, nodes, coloring_complete, PositiveMap.key.
      * intros ci0 cj H5 H6.
        qauto use: @restrict_agree unfold: PositiveOrderedTypeBits.t, node, PositiveMap.key, PositiveSet.elt, coloring, coloring_ok.
Qed.
  
Lemma nbd_2_colorable_3' : forall (g : graph) (f : coloring) p,
    coloring_complete p g f ->
    three_coloring' f p ->
    forall v ci, M.find v f = Some ci ->
            two_coloring' (restrict f (nodes (neighborhood g v))) (S.remove ci p) /\ coloring_complete (S.remove ci p) (neighborhood g v) (restrict f (nodes (neighborhood g v))).
Proof.
  hauto l: on use: SP.remove_cardinal_1, nbd_Sn_colorable_n unfold: PositiveOrderedTypeBits.t, three_coloring', node, two_coloring', n_coloring, PositiveSet.elt inv: nat.
Qed.

Lemma nbd_not_n_col_graph_not_Sn_col : forall (g : graph) (f : coloring) (p : S.t) n,
    coloring_complete p g f ->
    (exists (v : M.key) (ci : node),
        M.find v f = Some ci /\
          (~ n_coloring (restrict f (nodes (neighborhood g v))) (S.remove ci p) n
           \/ ~ coloring_complete (S.remove ci p)
                                 (neighborhood g v)
                                 (restrict f (nodes (neighborhood g v))))) ->
    ~ n_coloring f p (S n).
Proof.
  qauto l: on use: nbd_Sn_colorable_n.
Qed.

(* if f is a complete coloring of g, then if there is a vertex whose
   neighborhood is not 2-colorable or the coloring is not complete
   then f cannot be a 3-coloring
 *)
Lemma nbd_not_2_col_graph_not_3_col : forall (g : graph) (f : coloring) (p : S.t),
    coloring_complete p g f ->
    (exists (v : M.key) (ci : node),
        M.find v f = Some ci /\
          (~ two_coloring' (restrict f (nodes (neighborhood g v))) (S.remove ci p)
           \/ ~ coloring_complete (S.remove ci p)
                                 (neighborhood g v)
                                 (restrict f (nodes (neighborhood g v))))) ->
    ~ three_coloring' f p.
Proof.
  qauto l: on use: nbd_2_colorable_3'.
Qed.

Definition constant_color {A} (s : S.t) c := S.fold (fun v => M.add v c) s (@M.empty A).

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

(* two_color_step
 - let g be a graph, v be a vertex, c1 and c2 the colors we have
 - this function colors v with c1 and colors its neighbors with c2
 *)
Definition two_color_step (g : graph) (v : node) c1 c2 (f : coloring) : coloring :=
  M.add v c1 (constant_color (adj g v) c2).

Lemma two_color_step_colors_v_c1 : forall g v c1 c2 f, M.find v (two_color_step g v c1 c2 f) = Some c1.
Proof.
  intros g v c1 c2 f.
  unfold two_color_step.
  scongruence use: PositiveMap.gss unfold: PositiveMap.key, nodeset, node, adj, PositiveOrderedTypeBits.t.
Qed.

Lemma two_color_step_colors_adj_c2 : forall g v c1 c2 f i,
    no_selfloop g -> S.In i (adj g v) -> M.find i (two_color_step g v c1 c2 f) = Some c2.
Proof.
  hauto use: PositiveMap.gso, @constant_color_colors unfold: two_color_step, PositiveSet.In, PositiveOrderedTypeBits.t, nodeset, node, PositiveSet.t, PositiveMap.key, PositiveSet.empty, PositiveSet.elt, no_selfloop, adj.
Qed.

Lemma two_color_step_inv : forall g v c1 c2 f ci j,
    ~ M.In v f ->
    M.find j (two_color_step g v c1 c2 f) = Some ci ->
    j = v \/ S.In j (adj g v).
Proof.
  intros g v c1 c2 f ci j H H0.
  unfold two_color_step in H0.
  destruct (E.eq_dec j v).
  - subst. left. reflexivity.
  - right.
    rewrite M.gso in H0 by auto.
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
    pose proof (two_color_step_inv g _ _ _ _ _ _ H4 H3).
    pose proof (two_color_step_inv g _ _ _ _ _ _ H4 H2).
    destruct H5, H6; subst.
    + contradiction.
    + rewrite two_color_step_colors_adj_c2 in H2 by auto.
      sfirstorder.
    + rewrite two_color_step_colors_v_c1 in H2.
      rewrite two_color_step_colors_adj_c2 in H3 by auto.
      scongruence.
    + rewrite two_color_step_colors_adj_c2 in H2, H3 by auto.
      (* Contradiction! We supposed that the graph was 2-colorable to
         begin with, but where we have two  *)
      destruct H0 as [m [p [Hm Hm']]].
      pose proof (Hm i ltac:(sauto use: undirected_adj_in)).
      pose proof (Hm j ltac:(sauto use: undirected_adj_in)).
      destruct H0 as [ii Hii].
      destruct H7 as [jj Hjj].
      unfold M.MapsTo in *.
      assert (ii = c1 \/ ii = c2).
      {
        pose proof (proj1 (Hm' _ _ H1) ii Hii).
        hauto l: on use: in_two_set_inv.
      }
      assert (jj = c1 \/ jj = c2).
      {
        pose proof (proj1 (Hm' _ _ (Hu _ _ H1)) jj Hjj).
        hauto l: on use: in_two_set_inv.
      }
      pose proof (Hm v ltac:(sauto use: undirected_adj_in)).
      destruct H8 as [vv Hvv].
      assert (vv = c1 \/ vv = c2).
      {
        pose proof (proj1 (Hm' _ _ H5) vv Hvv).
        hauto l: on use: in_two_set_inv.
      }
      (* so i and j have colors given by the magic coloring function,
         but no matter what colors we give them something is going to go
         wrong *)
      destruct H0, H7, H8; strivial unfold: coloring_ok.
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
  unfold coloring_complete.
  split.
  - intros i H0.
    exists c.
    unfold M.MapsTo.
    apply constant_color_colors.
    unfold nodes.
    apply Sin_domain.
    assumption.
  - split.
    + intros ci H1.
      assert (S.In i (nodes g)).
      {
        unfold adj in H0.
        destruct (M.find i g) eqn:E.
        - pose proof (max_deg_max _ _ _ E).
          rewrite H in H2.
          hfcrush use: SP.remove_cardinal_1 unfold: nodeset inv: Peano.le.
        - sauto q: on.
      }
      pose proof (constant_color_colors (nodes g) c i H2).
      unfold S.elt, node, E.t in *.
      assert (ci = c) by scongruence.
      sfirstorder use: PositiveSet.singleton_2 unfold: PositiveSet.elt.
    + intros ci cj H1 H2.
      unfold adj in H0.
      destruct (M.find i g) eqn:E.
      * pose proof (max_deg_max _ _ _ E).
        rewrite H in H3.
        hauto use: SP.remove_cardinal_1 unfold: nodeset inv: Peano.le.
      * fcrush.
Qed.

(* If a graph has a vertex of degree d then color that vertex with c *)
Definition color_d (g : graph) (d : nat) c (v : {v | M.In v g /\ S.cardinal (adj g v) = d})
  : coloring :=
  M.add (`v) c (@M.empty _).

Lemma max_degree_colorable : forall 


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
