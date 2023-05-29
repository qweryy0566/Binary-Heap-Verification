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
  forall (Espec: OracleKind) Hl Maxsize size0 pos0 a0 a' pos' size',
  let Delta_specs := Delta_specs_down in
  let Delta := Delta_down Delta_specs in
  semax Delta (PROP ((size' = (Vint (IntRepr size0))); (pos' = (Vint (IntRepr pos0))); (a' = a0); (Z.le (Z.add size0 1) Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0); (Z.le Maxsize (Int.max_signed )); (Z.le 2 Maxsize); (all_int Hl))
  LOCAL (temp _a a'; temp _pos pos'; temp _size size')
  SEP ((store_int_array a0 Hl Maxsize)))
  Sskip
  (normal_split_assert
  (EX Hl0 pos1 a pos size,
    (PROP ((down_inv Hl size0 pos0 pos1 Hl0); (size = (Vint (IntRepr size0))); (pos = (Vint (IntRepr pos1))); (Z.le pos1 size0); (a = a0); (Z.le pos1 size0); (Z.le 1 pos1); (Z.le (Z.add size0 1) Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0); (Z.le Maxsize (Int.max_signed )); (Z.le 2 Maxsize); (all_int Hl))
    LOCAL (temp _a a; temp _pos pos; temp _size size)
    SEP ((store_int_array a0 Hl0 Maxsize))))%assert).
