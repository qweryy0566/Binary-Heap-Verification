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
  forall (Espec: OracleKind) Hl Maxsize size0 val0 a' size' val',
  let Delta_specs := Delta_specs_push in
  let Delta := Delta_push Delta_specs in
  semax Delta (PROP ((MaxHeap Hl size0); (size' = (Vint (IntRepr size0))); (val' = (Vint (IntRepr val0))); (Z.lt size0 Maxsize); (Z.le 0 size0))
  LOCAL (temp _a a'; temp _size size'; temp _val val')
  SEP ((store_int_array a' Hl Maxsize)))
  (Ssequence
    (Sset _t'3 (Ederef (Etempvar _size (tptr tint)) tint))
    (Ssequence
      (Sassign (Ederef (Etempvar _size (tptr tint)) tint)
        (Ebinop Oadd (Etempvar _t'3 tint) (Econst_int (Int.repr 1) tint)
          tint))
      (Ssequence
        (Sset _t'2 (Ederef (Etempvar _size (tptr tint)) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t'2 tint)
                (tptr tint)) tint) (Etempvar _val tint))
          (Ssequence
            (Sset _t'1 (Ederef (Etempvar _size (tptr tint)) tint))
            (Scall None
              (Evar _up (Tfunction (Tcons (tptr tint) (Tcons tint Tnil))
                          tvoid cc_default))
              ((Etempvar _a (tptr tint)) :: (Etempvar _t'1 tint) :: nil)))))))
  (normal_split_assert (RA_normal (frame_ret_assert (function_body_ret_assert tvoid 
  (EX Hl_final a size val,
    (PROP ((MaxHeap Hl_final (Z.add size0 1)); (Hl_final = (push Hl size0 val0)); (size = (Vint (IntRepr (Z.add size0 1)))); (val = (Vint (IntRepr val0))))
    LOCAL (temp _a a; temp _size size; temp _val val)
    SEP ((store_int_array a Hl_final Maxsize))))%assert) (stackframe_of f_push)))).
