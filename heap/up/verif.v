Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.up.path0_verif.
Require heap.up.path1_verif.
Require heap.up.path2_verif.
Require heap.up.path3_verif.

Theorem f_up_functionally_correct :
  semax_body Vprog Gprog f_up up_spec.
Proof.
  VST_A_start_function f_up_hint.
  + apply path0_verif.SH_Proof.proof.
  + apply path1_verif.SH_Proof.proof.
  + apply path2_verif.SH_Proof.proof.
  + apply path3_verif.SH_Proof.proof.
Qed.
