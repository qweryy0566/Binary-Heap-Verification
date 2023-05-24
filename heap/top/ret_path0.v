From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Csplit.semantics.
Require Import utils.AClightNotations.
Require VST.floyd.proofauto.
Require Import FloydSeq.proofauto.
Require Import Csplit.strong.
Require Import FloydSeq.client_lemmas.
Require Import Csplit.strongSoundness.
Require Import Csplit.AClightFunc.
Local Open Scope Z_scope.
Import AClightNotations.
Require Import cprogs.heap.program.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.annotation.
Import compcert.cfrontend.Clight.

Definition functional_correctness_statement: Prop :=
  forall (Espec: OracleKind) Hl Maxsize a',
  let Delta_specs := Delta_specs_top in
  let Delta := Delta_top Delta_specs in
  semax Delta (PROP ((Z.ge Maxsize 2))
  LOCAL (temp _a a')
  SEP ((store_int_array a' Hl Maxsize)))
  (Ssequence
    (Sset _t'1
      (Ederef
        (Ebinop Oadd (Etempvar _a (tptr tint)) (Econst_int (Int.repr 1) tint)
          (tptr tint)) tint))
    (Sreturn (Some (Etempvar _t'1 tint))))
  (return_split_assert (RA_return (frame_ret_assert (function_body_ret_assert tint 
  (EX a __return,
    (PROP ((__return = (Vint (IntRepr (Znth 1 Hl)))))
    LOCAL (temp _a a; temp ___return __return)
    SEP ((store_int_array a Hl Maxsize))))%assert) (stackframe_of f_top)))).
