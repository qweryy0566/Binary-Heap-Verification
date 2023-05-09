Require Import utils.VSTALib.

Require Import cprogs.heap.program.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.annotation.
Require cprogs.heap.down.path0_verif.
Require cprogs.heap.down.path1_verif.
Require cprogs.heap.down.path2_verif.
Require cprogs.heap.down.path3_verif.
Require cprogs.heap.down.path4_verif.
Require cprogs.heap.down.path5_verif.
Require cprogs.heap.down.path6_verif.
Require cprogs.heap.down.path7_verif.
Require cprogs.heap.down.path8_verif.
Require cprogs.heap.down.path9_verif.

Theorem f_down_functionally_correct :
  semax_body Vprog Gprog f_down down_spec.
Proof.
  VST_A_start_function f_down_hint.
  + apply path0_verif.SH_Proof.proof.
  + apply path1_verif.SH_Proof.proof.
  + apply path2_verif.SH_Proof.proof.
  + apply path3_verif.SH_Proof.proof.
  + apply path4_verif.SH_Proof.proof.
  + apply path5_verif.SH_Proof.proof.
  + apply path6_verif.SH_Proof.proof.
  + apply path7_verif.SH_Proof.proof.
  + apply path8_verif.SH_Proof.proof.
  + apply path9_verif.SH_Proof.proof.
Admitted.
