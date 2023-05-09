Require Import FloydSeq.proofauto.
(* Require Import cprogs.heap.program. *)
Require Import Notations Logic Datatypes.
From Coq Require Import String List ZArith. 
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.

Require Import Coq.micromega.Psatz.
Local Open Scope string.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Require Import SetsClass.SetsClass.
Local Open Scope sets.
Import SetsNotation.

Definition list_swap (x: nat) (y: nat):
  list Z -> list Z -> Prop :=
  fun l1 l2 =>
    length l1 = length l2 /\
    nth x l1 0 = nth y l2 0 /\ nth y l1 0 = nth x l2 0 /\
    forall i, (i < length l1)%nat /\ i <> x /\ i <> y ->
      nth i l1 0 = nth i l2 0.

Import ListNotations.

Require Import BinNums.
Require Coq.micromega.Lia.

Definition state: Type := ((list Z) * nat).

Definition get_num(l: state): Z := 
  nth ((snd l) - 1) (fst l) 0.

Definition list_up_succeed:
  state -> state -> Prop :=
  fun l1 l2 =>
    (1%nat < (snd l1))%nat /\ ((snd l2) = (snd l1)/2)%nat /\
    get_num l1 > (nth ((snd l2)-1) (fst l1) 0) /\
    (list_swap ((snd l1)-1) ((snd l2)-1) (fst l1) (fst l2)).

Definition list_up_fail:
  state -> state -> Prop:=
  Rels.test(fun l =>
    (1%nat = (snd l))%nat \/
    ((1%nat < (snd l))%nat /\ 
    get_num l <= (nth ((snd l)/2) (fst l) 0))).

Fixpoint iter_n (n: nat):
  state -> state -> Prop :=
  match n with
  | O => list_up_fail
  | S n0 => list_up_succeed ∘ (iter_n n0)
  end.

Definition heap_up:
  state -> state -> Prop :=
  ⋃ (iter_n).

Example test : list_swap 2%nat 1%nat [2; 3; 4; 5] [2; 4; 3; 5].
Proof.
  unfold list_swap.
  unfold length.
  unfold nth at 1 2 3 4.
  split; [tauto | ].
  split; [tauto | ].
  split; [tauto | ].
  intros.
  assert (i = 0%nat \/ i = 3%nat) by lia.
  destruct H0.
  + rewrite H0.
    tauto.
  + rewrite H0.
    tauto.  
Qed.

Example check_succeed : list_up_succeed (pair [2; 3; 4; 5] 2%nat) (pair [3; 2; 4; 5] 1%nat).
Proof.
  unfold list_up_succeed.
  split; [simpl; lia|].
  split; [simpl; tauto|].
  split; [unfold get_num; simpl; lia|].
  simpl.
  unfold list_swap. unfold length.
  split; [tauto|].
  split; [tauto|].
  split; [tauto|].
  intros.
  destruct H as [H0 [H1 H2]].
  assert (i = 2%nat \/ i = 3%nat) by lia.
  destruct H; subst; tauto.
Qed.

Example check_heap_up : heap_up (pair [2; 3; 4; 5] 2%nat) (pair [3; 2; 4; 5] 1%nat).
Proof.
  unfold heap_up.
  sets_unfold.
  exists 1%nat.
  unfold iter_n.
  sets_unfold.
  exists (pair [3; 2; 4; 5] 1%nat).
  split.
  + apply check_succeed.
  + unfold list_up_fail.
    simpl.
    split.
    - left; tauto.
    - sets_unfold.
      tauto.
Qed.

Example check_heap_up2 : heap_up (pair [100;3;2;5] 4%nat) (pair [100;5;2;3] 2%nat).
Proof.
  unfold heap_up.
  sets_unfold.
  exists 1%nat.
  unfold iter_n.
  sets_unfold.
  exists (pair [100;5;2;3] 2%nat).
  split.
  + unfold list_up_succeed.
    split; [unfold snd; lia|].
    split; [unfold snd; tauto|].
    split; [unfold get_num; simpl; lia|].
    simpl.
    unfold list_swap. unfold length.
    split; [tauto|].
    split; [tauto|].
    split; [tauto|].
    intros.
    destruct H as [H0 [H1 H2]].
    assert (i = 0%nat \/ i = 2%nat) by lia.
    destruct H; subst; tauto.
  + unfold list_up_fail.
    simpl.
    split.
    - right.
      split; [lia|].
      unfold get_num; simpl; lia.
    - sets_unfold.
      tauto.
Qed.

Definition list_swap_rev (x: nat) (y: nat):
  list Z -> list Z -> Prop := (list_swap x y) ∘ (list_swap x y).

Lemma swap_rev: forall (x y: nat) (l1 l3: list Z),
  (list_swap_rev x y) l1 l3 -> l1 = l3.
Proof.
  intros ? ? ? ?.
  unfold list_swap_rev.
  sets_unfold.
  (* unfold_RELS_tac. *)
  unfold list_swap.
  intros.
  destruct H as [H [? ?] ].
  destruct H0 as [? [? [? ?]]].
  destruct H1 as [? [? [? ?]]].
  rewrite <- H0 in H1, H7.
  rewrite <- H3 in H5.
  rewrite <- H2 in H6.
  clear H0 H2 H3.
  assert (forall (i: nat), (i < length l1)%nat -> nth i l1 0 = nth i l3 0). {
    intros.
    assert (i = x \/ i = y \/ (i < length l1)%nat /\ i <> x /\ i <> y) by lia.
    destruct H2; [rewrite H2; tauto | ].
    destruct H2; [rewrite H2; tauto | ].
    specialize (H4 i H2).
    specialize (H7 i H2).
    rewrite H4.
    apply H7.
  }
  apply (nth_ext l1 l3 0 0 H1 H0).
Qed.
