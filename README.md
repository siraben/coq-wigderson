# Towards the Formal Verification of Wigderson’s Algorithm
**Created by: Ben Siraphob (siraben) and Jamison Homatas (jhomatas48)**

We present progress towards the formal verification of Wigderson's
graph coloring algorithm in Coq. We have created a library of
formalized graph theory that aims to bridge the literature gap between
introductory material on Coq and large-scale formal developments,
while providing a motivating case study. Our library contains over 300
proven theorems.

Using Nix, run `nix develop`, then run `make` to compile the complete proof
development (including the computational Coq examples). Run `make check` to
also execute the independent Python cross-check, or `make rebuild` for a safe
from-clean rebuild.

The accompanying paper source is `wigderson-paper.tex`.

## Proof notation

Import `graph_notations` and open `graph_scope` to use the optional compact
notation employed by the higher-level proofs:

```coq
Require Import graph_notations.
Local Open Scope graph_scope.
```

- `x ∈ s`, `v ∈ dom g`, and `s ⊆ t` denote set membership,
  map-domain membership, and set inclusion.
- `m !! k` denotes `M.find k m`; `V[g]` is the vertex set.
- `Adj[g; v]` is the adjacency set, `N[g; v]` is the neighborhood graph,
  and `u ~[g] v` states that `v` is adjacent from `u` in `g`.
- `h ⊑ g`, `g ⇂ s`, and `g ∖ s` denote the subgraph relation, induced
  subgraph, and vertex removal.
- `deg[g] v` and `Δ[g]` denote degree lookup and maximum degree.

## License
This software is licensed under the MIT license.
