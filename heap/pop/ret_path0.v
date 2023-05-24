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
  forall (Espec: OracleKind) Hl Maxsize size0 a' size',
  let Delta_specs := Delta_specs_pop in
  let Delta := Delta_pop Delta_specs in
  semax Delta (PROP ((MaxHeap Hl size0); (size' = (Vint (IntRepr size0))); (Z.le size0 Maxsize); (Z.le 0 size0))
  LOCAL (temp _a a'; temp _size size')
  SEP ((store_int_array a' Hl Maxsize)))
  (Ssequence
    (Sset _t'5 (Ederef (Etempvar _size (tptr tint)) tint))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        Sbreak)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))))
  (return_split_assert (RA_return (frame_ret_assert (function_body_ret_assert tint 
  (EX Hl_final size1 a size __return,
    (PROP ((MaxHeap Hl_final size1); (pop Hl size0 Hl_final); (size = (Vint (IntRepr size1))); (size1 = (pop_length Hl size0)); (__return = (Vint (IntRepr (pop_result Hl size0)))))
    LOCAL (temp _a a; temp _size size; temp ___return __return)
    SEP ((store_int_array a Hl_final Maxsize))))%assert) (stackframe_of f_pop)))).
