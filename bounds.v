Require Import Arith.
Require Import Psatz.
Import Nat.
Require Import List.
Import ListNotations.

Check sqrt_up.
(* sqrt_up *)
(*      : nat -> nat *)

Compute (map (sqrt_up) [1;2;3;4;5;6;7;8;9;10;11;12;13]).

Lemma loop_iters :
  forall n, n / (sqrt n + 1) <= sqrt n.
Proof.
  intros n.
  Search (_ / _ <= _).
  pose proof (div_le_upper_bound n (sqrt n + 1) (sqrt n) ltac:(lia)).
  apply H.
Admitted.
