Require Import utils.VSTALib.

Require Import cprogs.heap.program.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.annotation.
Require cprogs.heap.top.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.heap.top.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  (* forward. *)
  sep_apply list_length; [lia |].
  Intros.
  forward.
  unfold POSTCONDITION.
  unfold abbreviate.
  
  forward.
Admitted.

End SH_Proof.
