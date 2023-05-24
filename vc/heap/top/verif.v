Require Import utils.VSTALib.

Require Import cprogs.heap.program.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.annotation.
Require cprogs.heap.top.ret_path0_verif.

Theorem f_top_functionally_correct :
  semax_body Vprog Gprog f_top top_spec.
Proof.
  VST_A_start_function f_top_hint.
  + apply ret_path0_verif.SH_Proof.proof.
Qed.
