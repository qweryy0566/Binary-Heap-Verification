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
  forall (Espec: OracleKind) Hl Maxsize size0 pos0 a' pos',
  let Delta_specs := Delta_specs_up in
  let Delta := Delta_up Delta_specs in
  semax Delta (PROP ((MaxHeap_p Hl (Z.add pos0 1) size0); (MaxHeap Hl (Z.sub pos0 1)); (pos' = (Vint (IntRepr pos0))); (Z.le size0 Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0))
  LOCAL (temp _a a'; temp _pos pos')
  SEP ((store_int_array a' Hl Maxsize)))
  Sskip
  (normal_split_assert
  (EX Hl0 pos1 n a pos,
    (PROP ((MaxHeap_p Hl0 (Z.add pos1 1) size0); (MaxHeap Hl0 (Z.sub pos1 1)); (Hl0 = (up Hl size0 pos0 pos1)); (pos1 = (shr pos0 n)); (pos = (Vint (IntRepr pos1))))
    LOCAL (temp _a a; temp _pos pos)
    SEP ((store_int_array a Hl0 Maxsize))))%assert).
