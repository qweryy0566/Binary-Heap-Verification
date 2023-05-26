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
  forall (Espec: OracleKind) Hl Maxsize size0 pos0 a0,
  let Delta_specs := Delta_specs_up in
  let Delta := Delta_up Delta_specs in
  semax Delta (EX Hl0 pos1 a pos,
                (PROP ((up Hl size0 pos0 pos1 Hl0); (pos = (Vint (IntRepr pos1))); (a = a0); (Z.le pos1 size0); (Z.le 1 pos1); (Z.le (Z.add size0 1) Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0); (Z.le Maxsize (Int.max_signed )); (Z.le 2 Maxsize); (all_int Hl))
                LOCAL (temp _a a; temp _pos pos)
                SEP ((store_int_array a0 Hl0 Maxsize))))%assert
  (Sifthenelse (Ebinop Ogt (Etempvar _pos tint)
                 (Econst_int (Int.repr 1) tint) tint)
    Sbreak
    Sskip)
  (normal_split_assert (RA_normal (frame_ret_assert (function_body_ret_assert tvoid 
  (EX Hl_final pos1 pos,
    (PROP ((up Hl size0 pos0 pos1 Hl_final); (pos = (Vint (IntRepr pos1))))
    LOCAL (temp _pos pos)
    SEP ((store_int_array a0 Hl_final Maxsize))))%assert) (stackframe_of f_up)))).
