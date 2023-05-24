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
  forall (Espec: OracleKind) x y px0 py0 a' b',
  let Delta_specs := Delta_specs_swap in
  let Delta := Delta_swap Delta_specs in
  semax Delta (PROP ((b' = py0); (a' = px0))
  LOCAL (temp _a a'; temp _b b')
  SEP ((store_int px0 x); (store_int py0 y)))
  (Ssequence
    (Sset _t (Ederef (Etempvar _a (tptr tint)) tint))
    (Ssequence
      (Sset _t'1 (Ederef (Etempvar _b (tptr tint)) tint))
      (Ssequence
        (Sassign (Ederef (Etempvar _a (tptr tint)) tint)
          (Etempvar _t'1 tint))
        (Sassign (Ederef (Etempvar _b (tptr tint)) tint) (Etempvar _t tint)))))
  (normal_split_assert (RA_normal (frame_ret_assert (function_body_ret_assert tvoid (PROP ()
  LOCAL ()
  SEP ((store_int px0 y); (store_int py0 x)))) (stackframe_of f_swap)))).
