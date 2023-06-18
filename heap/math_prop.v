Require Import FloydSeq.proofauto.
(* Require Import cprogs.heap.program. *)
Require Import Notations Logic Datatypes.
From Coq Require Import String List ZArith. 
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.

Require Import Coq.micromega.Psatz.
Local Open Scope string.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Require Import SetsClass.SetsClass.
Local Open Scope sets.
Import SetsNotation.

Lemma Div_2_gt_0: forall (n: Z), 
  1 <= n/2 -> n/2 < n.
Proof.
  intros.
  assert (n >= 1 \/ n <= 0) by lia.
  destruct H0.
  + pose proof Z.div_lt_upper_bound n 2 n ltac:(lia) ltac:(lia).
    lia.
  + pose proof Z.div_le_upper_bound n 2 0 ltac:(lia) ltac:(lia).
    lia.    
Qed.

Lemma Odd_Div2: forall (n: Z),
  n >= 1 -> (n*2+1)/2 = n.
Proof.
  intros.
  pose proof Z.div_lt_upper_bound (n*2+1) 2 (n + 1) ltac:(lia) ltac:(lia).
  pose proof Z.div_le_lower_bound (n*2+1) 2 n ltac:(lia) ltac:(lia).
  lia.
Qed.

Lemma Even_Div2: forall (n: Z),
  n >= 1 -> (n*2)/2 = n.
Proof.
  intros.
  rewrite Z.div_mul by lia.
  lia.
Qed.