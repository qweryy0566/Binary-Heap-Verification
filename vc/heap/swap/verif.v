Require Import utils.VSTALib.

Require Import cprogs.heap.program.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.annotation.
Require cprogs.heap.swap.path0_verif.

Theorem f_swap_functionally_correct :
  semax_body Vprog Gprog f_swap swap_spec.
Proof.
  VST_A_start_function f_swap_hint.
  + apply path0_verif.SH_Proof.proof.
Qed.
