Require Import utils.VSTALib.

Require Import cprogs.heap.program.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.annotation.
Require cprogs.heap.push.path0_verif.

Theorem f_push_functionally_correct :
  semax_body Vprog Gprog f_push push_spec.
Proof.
  VST_A_start_function f_push_hint.
  + apply path0_verif.SH_Proof.proof.
Qed.
