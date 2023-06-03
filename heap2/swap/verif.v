Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.swap.path0_verif.

Theorem f_swap_functionally_correct :
  semax_body Vprog Gprog f_swap swap_spec.
Proof.
  VST_A_start_function f_swap_hint.
  + apply path0_verif.SH_Proof.proof.
Qed.
