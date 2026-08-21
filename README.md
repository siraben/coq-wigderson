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

## License
This software is licensed under the MIT license.
