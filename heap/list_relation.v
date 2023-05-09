Require Import FloydSeq.proofauto.
(* Require Import cprogs.heap.program. *)
Require Import Notations Logic Datatypes.
Require Export Coq.Classes.Init.
(* Require Import Coq.Program.Basics. *)
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
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
Lemma list_equal : forall (A: Type) (l1 l2: list A) (d: A),
  l1 = l2 <-> length l1 = length l2 /\
  forall (i: nat), (i < length l1)%nat -> nth i l1 d = nth i l2 d.
Proof.
  split.
  + intros.
    rewrite H.
    tauto.
  + intros.
    destruct H.
    apply (nth_ext l1 l2 d d); [tauto | tauto].
Qed.

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
  nth ((snd l)) (fst l) 0.

Definition legal_state(l: state): Prop:=
  ((snd l) <= (length (fst l)))%nat /\ (1%nat <= (snd l))%nat.

Definition list_up_succeed:
  state -> state -> Prop :=
  fun l1 l2 => legal_state l1 /\ legal_state l2 /\
    (1%nat < (snd l1))%nat /\ ((snd l2) = (snd l1)/2)%nat /\
    get_num l1 > (nth (snd l2) (fst l1) 0) /\
    (list_swap (snd l1) (snd l2) (fst l1) (fst l2)).

Definition list_up_fail:
  state -> state -> Prop:=
  Rels.test(fun l =>  legal_state l /\
    ((1%nat = (snd l))%nat \/
    ((1%nat < (snd l))%nat /\ 
    get_num l <= (nth ((snd l)/2) (fst l) 0)))).

Fixpoint iter_n_up (n: nat):
  state -> state -> Prop :=
  match n with
  | O => list_up_fail
  | S n0 => list_up_succeed ∘ (iter_n_up n0)
  end.

Definition heap_up:
  state -> state -> Prop :=
  ⋃ (iter_n_up).

Definition left_son(l: state): state :=
  pair (fst l) ((snd l) * 2)%nat.

Definition left_son_swap(l1 l2: state): Prop :=
  (list_swap (snd l1) (snd l2) (fst l1) (fst l2)) /\ ((snd l1) * 2 = (snd l2))%nat.
  
Definition right_son_swap(l1 l2: state): Prop :=
  (list_swap (snd l1) (snd l2) (fst l1) (fst l2)) /\ ((snd l1) * 2 + 1 = (snd l2))%nat.

Definition right_son(l: state): state :=
  pair (fst l) ((snd l) * 2 + 1)%nat.

Definition left_son_check (l: state): Prop :=
  legal_state (left_son l) /\
  get_num l < get_num (left_son l).
  
Definition right_son_check (l: state): Prop :=
  legal_state (right_son l) /\
  get_num l < get_num (right_son l).

Definition list_down_succeed:
  state -> state -> Prop :=
  fun l1 l2 =>
    ((left_son_check l1) /\ ~(right_son_check l1) /\ l2 = (left_son l1)) \/
    ((left_son_check l1) /\ (right_son_check l1) /\ (
      ((get_num (left_son l1)) > (get_num (right_son l1)) /\ (left_son_swap l1 l2))  \/
      ((get_num (left_son l1)) <= (get_num (right_son l1)) /\ (right_son_swap l1 l2))
    )) \/
    (~(left_son_check l1) /\ (right_son_check l1) /\ l2 = (left_son l1)).

Definition list_down_fail:
  state -> state -> Prop :=
  Rels.test(fun l =>
    ~(left_son_check l) /\ ~(right_son_check l)).

Fixpoint iter_n_down (n: nat):
  state -> state -> Prop :=
  match n with
  | O => list_down_fail
  | S n0 => list_down_succeed ∘ (iter_n_down n0)
  end.

Definition heap_down:
  state -> state -> Prop :=
  ⋃ (iter_n_down).

Ltac try_unfold_son :=
  unfold left_son_check; unfold left_son_swap; unfold left_son; 
  unfold right_son_check; unfold right_son_swap; unfold right_son;
  unfold get_num; unfold legal_state; simpl.

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

Example check_succeed_up : list_up_succeed (pair [233;2; 3; 4; 5] 2%nat) (pair [233;3; 2; 4; 5] 1%nat).
Proof.
  unfold list_up_succeed.
  split; [unfold legal_state; simpl; lia|].
  split; [unfold legal_state; simpl; lia|].
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
  assert (i = 0%nat \/ i = 3%nat \/ i = 4%nat) by lia.
  destruct H;[ subst; tauto|].
  destruct H; subst; tauto.
Qed.

Example check_heap_up : heap_up (pair [233;2; 3; 4; 5] 2%nat) (pair [233;3; 2; 4; 5] 1%nat).
Proof.
  unfold heap_up.
  unfold_RELS_tac.
  exists 1%nat.
  unfold iter_n_up.
  unfold_RELS_tac.
  exists (pair [233;3; 2; 4; 5] 1%nat).
  split.
  + apply check_succeed_up.
  + unfold list_up_fail.
    simpl.
    split.
    - split; unfold legal_state; simpl; lia.
    - tauto.
Qed.

Example check_heap_up2 : heap_up (pair [233;100;3;2;5] 4%nat) (pair [233;100;5;2;3] 2%nat).
Proof.
  unfold heap_up.
  unfold_RELS_tac.
  exists 1%nat.
  unfold iter_n_up.
  unfold_RELS_tac.
  exists (pair [233;100;5;2;3] 2%nat).
  split.
  + unfold list_up_succeed.
    split; [unfold legal_state; simpl; lia|].
    split; [unfold legal_state; simpl; lia|].
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
    assert (i = 0%nat \/ i = 1%nat \/ i = 3%nat) by lia.
    destruct H;[ subst; tauto|].
    destruct H; subst; tauto.
  + unfold list_up_fail.
    simpl.
    split.
    - split.
      unfold legal_state; simpl; lia.
      right; split; [lia|].
      unfold get_num; simpl; lia.
    - tauto.
Qed.

Example check_succeed_down : list_down_succeed (pair [233;4;6;9;2;4;1;3] 1%nat) (pair [233;9;6;4;2;4;1;3] 3%nat).
Proof.
  unfold list_down_succeed.
  right; left.
  split; try_unfold_son; [lia|].
  split; [lia|].
  right; split; [lia|].
  unfold list_swap; unfold length.
  split; [|tauto].
  split; [tauto|].
  split; [tauto|].
  split; [tauto|].
  intros.
  assert (i = 0%nat \/ i = 2%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat \/ i = 7%nat) by lia.
  destruct H0; [subst; tauto|].
  destruct H0; [subst; tauto|].
  destruct H0; [subst; tauto|].
  destruct H0; [subst; tauto|].
  destruct H0; subst; tauto.
Qed.


Example check_heap_down : heap_down (pair [233;4;6;9;2;4;1;3] 1%nat) (pair [233;9;6;4;2;4;1;3] 3%nat).
Proof.
  unfold heap_down.
  unfold_RELS_tac.
  exists 1%nat.
  unfold iter_n_down.
  unfold_RELS_tac.
  exists ([233; 9; 6; 4; 2; 4; 1; 3], 3%nat).
  split.
  + exact check_succeed_down.
  + unfold list_down_fail.
    simpl; split; [|tauto].
    try_unfold_son; lia.
Qed.