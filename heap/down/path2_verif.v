Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.down.path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.down.path2.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
Admitted.

End SH_Proof.
