Require Import utils.VSTALib.

Require Import cprogs.heap.program.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.annotation.
Require cprogs.heap.down.path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.heap.down.path2.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros; Intros Hl0 pos1 a pos size.
Admitted.

End SH_Proof.
