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
Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Import compcert.cfrontend.Clight.

Definition functional_correctness_statement: Prop :=
  forall (Espec: OracleKind) Hl Maxsize size0 size_p val0 a0 a' size' val',
  let Delta_specs := Delta_specs_push in
  let Delta := Delta_push Delta_specs in
  semax Delta (PROP ((size' = size_p); (val' = (Vint (IntRepr val0))); (a0 = a'); (Z.le (Z.add (Z.add size0 1) 1) Maxsize); (Z.le 0 size0); (Z.le Maxsize (Int.max_signed )); (Z.le 1 Maxsize); (Z.le val0 (Int.max_signed )); (Z.le (Int.min_signed ) val0); (all_int Hl))
  LOCAL (temp _a a'; temp _size size'; temp _val val')
  SEP ((store_int_array a0 Hl Maxsize); (store_int size_p size0)))
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
  (EX Hl_final,
    (PROP ((push Hl size0 val0 Hl_final))
    LOCAL ()
    SEP ((store_int_array a0 Hl_final Maxsize); (store_int size_p (Z.add size0 1)))))%assert) (stackframe_of f_push)))).
