Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.push.path0_verif.

Theorem f_push_functionally_correct :
  semax_body Vprog Gprog f_push push_spec.
Proof.
  VST_A_start_function f_push_hint.
  + apply path0_verif.SH_Proof.proof.
Qed.
