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
  forall (Espec: OracleKind) Hl Maxsize size0 pos0,
  let Delta_specs := Delta_specs_up in
  let Delta := Delta_up Delta_specs in
  semax Delta (EX Hl0 pos1 n a pos,
                (PROP ((MaxHeap_p Hl0 pos1 size0); (MaxHeap Hl0 (Z.sub pos1 1)); (up Hl size0 pos0 pos1 Hl0); (pos = (Vint (IntRepr pos1))))
                LOCAL (temp _a a; temp _pos pos)
                SEP ((store_int_array a Hl0 Maxsize))))%assert
  (Sifthenelse (Ebinop Ogt (Etempvar _pos tint)
                 (Econst_int (Int.repr 1) tint) tint)
    Sbreak
    Sskip)
  (normal_split_assert (RA_normal (frame_ret_assert (function_body_ret_assert tvoid 
  (EX Hl_final pos1 n a pos,
    (PROP ((MaxHeap Hl_final size0); (up Hl size0 pos0 pos1 Hl_final); (pos = (Vint (IntRepr pos1))))
    LOCAL (temp _a a; temp _pos pos)
    SEP ((store_int_array a Hl_final Maxsize))))%assert) (stackframe_of f_up)))).
