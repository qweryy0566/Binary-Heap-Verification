Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.pop.ret_path0_verif.
Require heap.pop.ret_path1_verif.
Require heap.pop.ret_path2_verif.

Theorem f_pop_functionally_correct :
  semax_body Vprog Gprog f_pop pop_spec.
Proof.
  VST_A_start_function f_pop_hint.
  + apply ret_path0_verif.SH_Proof.proof.
  + apply ret_path1_verif.SH_Proof.proof.
  + apply ret_path2_verif.SH_Proof.proof.
Qed.
