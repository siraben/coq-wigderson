(** * graph_notations.v - Optional notation for graph proofs *)

Require Import graph.
Require Import subgraph.

(** These notations expose the relations and operations that dominate graph
    proof statements while keeping the underlying definitions unchanged. *)
Declare Scope graph_scope.
Delimit Scope graph_scope with graph.

(** Sets and finite maps. *)
Notation "x ∈ s" := (S.In x s)
  (at level 70, no associativity) : graph_scope.
Notation "v ∈ 'dom' g" := (M.In v g)
  (at level 70, no associativity) : graph_scope.
Notation "s ⊆ t" := (S.Subset s t)
  (at level 70, no associativity) : graph_scope.
Notation "m !! k" := (M.find k m)
  (at level 20, left associativity) : graph_scope.

(** Graph structure and transformations. *)
Notation "'V[' g ']'" := (nodes g)
  (at level 0, g at level 99) : graph_scope.
Notation "u ~[ g ] v" := (S.In v (adj g u))
  (at level 70, no associativity) : graph_scope.
Infix "⊑" := is_subgraph
  (at level 70, no associativity) : graph_scope.
(** [Adj[g; v]] is a vertex set; [N[g; v]] is the neighborhood graph. *)
Notation "'Adj[' g ; v ']'" := (adj g v)
  (at level 0, g at level 99, v at level 99) : graph_scope.
Notation "'N[' g ; v ']'" := (neighborhood g v)
  (at level 0, g at level 99, v at level 99) : graph_scope.
Notation "g ⇂ s" := (subgraph_of g s)
  (at level 40, left associativity) : graph_scope.
Notation "g ∖ s" := (remove_nodes g s)
  (at level 40, left associativity) : graph_scope.
Notation "'deg[' g ']' v" := (degree v g)
  (at level 0, g at level 99, v at level 9) : graph_scope.
Notation "'Δ[' g ']'" := (max_deg g)
  (at level 0, g at level 99) : graph_scope.
