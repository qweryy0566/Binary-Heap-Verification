Require Import FloydSeq.proofauto.
(* Require Import cprogs.heap_list_down.program. *)
Require Import Notations Logic Datatypes.
Require Export Coq.Classes.Init.
(* Require Import Coq.Program.Basics. *)
(* Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions. *)
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

Lemma list_equal : forall (A: Type) (l1 l2: list A) {d: Inhabitant A},
  l1 = l2 <-> Zlength l1 = Zlength l2 /\
  forall (i: Z), 0 <= i < Zlength l1 -> Znth i l1 = Znth i l2.
Proof.
  split.
  + intros.
    rewrite H.
    tauto.
  + intros.
    destruct H.
    apply (Znth_eq_ext l1 l2); [tauto | tauto].
Qed.

Definition list_swap (x: Z) (y: Z):
  list Z -> list Z -> Prop :=
  fun l1 l2 =>
    Zlength l1 = Zlength l2 /\
    Znth x l1 = Znth y l2 /\ Znth y l1 = Znth x l2 /\
    forall i, 0 <= i < Zlength l1 /\ i <> x /\ i <> y ->
      Znth i l1 = Znth i l2.

Import ListNotations.

Require Import BinNums.
Require Coq.micromega.Lia.

Definition list_state: Type := ((list Z) * Z).

Definition get_list_val(l: list_state): Z := 
  Znth ((snd l)) (fst l).

Definition legal_list_state(l: list_state): Prop:=
  ((snd l) < Zlength (fst l)) /\ 1 <= (snd l).

Definition list_up_succeed:
  list_state -> list_state -> Prop :=
  fun l1 l2 => legal_list_state l1 /\ legal_list_state l2 /\
    1 < (snd l1) /\ (snd l2) = (snd l1) / 2 /\
    get_list_val l1 > (Znth (snd l2) (fst l1)) /\
    (list_swap (snd l1) (snd l2) (fst l1) (fst l2)).

Definition list_up_fail:
  list_state -> list_state -> Prop:=
  Rels.test(fun l =>  legal_list_state l /\
    (1 = (snd l) \/
    (1 < (snd l) /\ 
    get_list_val l <= (Znth ((snd l) / 2) (fst l))))).

(* Fixpoint iter_n_list_up (n: nat):
  list_state -> list_state -> Prop :=
  match n with
  | O => list_up_fail
  | S n0 => list_up_succeed ∘ (iter_n_list_up n0)
  end. *)

Definition heap_list_up:
  list_state -> list_state -> Prop :=
  (clos_refl_trans list_up_succeed) ∘ list_up_fail.
  (* ⋃ (iter_n_list_up). *)

Definition left_son(l: list_state): list_state :=
  pair (fst l) (2 * (snd l)).

Definition left_son_swap(l1 l2: list_state): Prop :=
  (list_swap (snd l1) (snd l2) (fst l1) (fst l2)) /\ 2 * (snd l1) = (snd l2).
  
Definition right_son_swap(l1 l2: list_state): Prop :=
  (list_swap (snd l1) (snd l2) (fst l1) (fst l2)) /\ 2 * (snd l1) + 1 = (snd l2).

Definition right_son(l: list_state): list_state :=
  pair (fst l) (2 * (snd l) + 1).

Definition left_son_check_list (l: list_state): Prop :=
  legal_list_state (left_son l) /\
  get_list_val l < get_list_val (left_son l).
  
Definition right_son_check_list (l: list_state): Prop :=
  legal_list_state (right_son l) /\
  get_list_val l < get_list_val (right_son l).

Definition list_down_succeed:
  list_state -> list_state -> Prop :=
  fun l1 l2 =>
    ((left_son_check_list l1) /\ ~(right_son_check_list l1) /\ (left_son_swap l1 l2)) \/
    ((left_son_check_list l1) /\ (right_son_check_list l1) /\ (
      ((get_list_val (left_son l1)) >= (get_list_val (right_son l1)) /\ (left_son_swap l1 l2))  \/
      ((get_list_val (left_son l1)) < (get_list_val (right_son l1)) /\ (right_son_swap l1 l2))
    )) \/
    (~(left_son_check_list l1) /\ (right_son_check_list l1) /\ (right_son_swap l1 l2)).

Definition list_down_fail:
  list_state -> list_state -> Prop :=
  Rels.test(fun l =>
    ~(left_son_check_list l) /\ ~(right_son_check_list l)).

(* Fixpoint iter_n_list_down (n: nat):
  list_state -> list_state -> Prop :=
  match n with
  | O => list_down_fail
  | S n0 => list_down_succeed ∘ (iter_n_list_down n0)
  end. *)

Definition heap_list_down:
  list_state -> list_state -> Prop :=
  (clos_refl_trans list_down_succeed) ∘ list_down_fail.
  (* ⋃ (iter_n_list_down). *)

Ltac simpl_Z :=
  simpl; unfold Zlength, Zlength_aux; unfold Znth; simpl.

Ltac try_list_unfold :=
  unfold left_son_check_list; unfold left_son_swap; unfold left_son; 
  unfold right_son_check_list; unfold right_son_swap; unfold right_son;
  unfold get_list_val; unfold legal_list_state; simpl_Z.

Ltac try_list_unfold_witout_Z :=
  unfold left_son_check_list; unfold left_son_swap; unfold left_son; 
  unfold right_son_check_list; unfold right_son_swap; unfold right_son;
  unfold get_list_val; unfold legal_list_state; simpl.

Example test : list_swap 2 1 [2; 3; 4; 5] [2; 4; 3; 5].
Proof.
  unfold list_swap.
  unfold Zlength, Zlength_aux.
  unfold Znth at 1 2 3 4.
  split; [tauto | ].
  split; [tauto | ].
  split; [tauto | ].
  intros.
  assert (i = 0 \/ i = 3) by lia.
  destruct H0.
  + rewrite H0.
    tauto.
  + rewrite H0.
    tauto.  
Qed.

Example check_succeed_up : list_up_succeed (pair [233;2; 3; 4; 5] 2) (pair [233;3; 2; 4; 5] 1).
Proof.
  unfold list_up_succeed.
  split; [unfold legal_list_state; simpl_Z; lia|].
  split; [unfold legal_list_state; simpl_Z; lia|].
  split; [simpl; lia|].
  split; [simpl; tauto|].
  split; [unfold get_list_val; simpl_Z; lia|].
  simpl.
  unfold list_swap. simpl_Z.
  split; [tauto|].
  split; [tauto|].
  split; [tauto|].
  intros.
  destruct H as [H0 [H1 H2]].
  assert (i = 0 \/ i = 3 \/ i = 4) by lia.
  destruct H;[ subst; tauto|].
  destruct H; subst; tauto.
Qed.

Example check_heap_list_up : heap_list_up (pair [233;2; 3; 4; 5] 2) (pair [233;3; 2; 4; 5] 1).
Proof.
  unfold heap_list_up.
  unfold_RELS_tac.
  exists (pair [233;3; 2; 4; 5] 1).
  split.
  + exists 1%nat.
    unfold list_up_succeed.
    unfold nsteps.
    unfold_RELS_tac.
    exists (pair [233;3; 2; 4; 5] 1).
    try_list_unfold.
    split; [|reflexivity].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [reflexivity|].
    split; [lia|].
    unfold list_swap.
    split; [tauto|]. split; [tauto|]. split; [tauto|].
    unfold Zlength, Zlength_aux; simpl.
    intros.
    destruct H, H, H0.
    assert (i = 0 \/ i = 3 \/ i = 4) by lia.
    destruct H3; [subst; reflexivity|].
    destruct H3; subst; reflexivity.
  + unfold list_up_fail.
    unfold_RELS_tac.
    try_list_unfold.
    split; [|reflexivity].
    split; [lia|].
    left; reflexivity.
Qed.

Example check_heap_list_up2 : heap_list_up (pair [233;100;3;2;5] 4) (pair [233;100;5;2;3] 2).
Proof.
  unfold heap_list_up.
  unfold_RELS_tac.
  exists (pair [233;100;5;2;3] 2).
  split.
  + exists 1%nat.
    unfold nsteps.
    unfold_RELS_tac.
    exists (pair [233;100;5;2;3] 2).
    split; [|reflexivity].
    unfold list_up_succeed.
    try_list_unfold.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [reflexivity|]. split; [lia|].
    unfold list_swap. simpl_Z.
    split; [tauto|]. split; [tauto|]. split; [tauto|].
    intros.
    destruct H as [H0 [H1 H2]].
    assert (i = 0 \/ i = 1 \/ i = 3) by lia.
    destruct H;[ subst; tauto|].
    destruct H; subst; tauto.
  + unfold list_up_fail.
    unfold_RELS_tac.
    try_list_unfold.
    split; [split; lia |reflexivity].
Qed.

Example check_succeed_down : list_down_succeed (pair [233;4;6;9;2;4;1;3] 1) (pair [233;9;6;4;2;4;1;3] 3).
Proof.
  unfold list_down_succeed.
  right; left.
  split; try_list_unfold; [lia|].
  split; [lia|].
  right; split; [lia|].
  unfold list_swap; simpl_Z.
  split; [|tauto].
  split; [tauto|].
  split; [tauto|].
  split; [tauto|].
  intros.
  assert (i = 0 \/ i = 2 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct H0; [subst; tauto|].
  destruct H0; [subst; tauto|].
  destruct H0; [subst; tauto|].
  destruct H0; [subst; tauto|].
  destruct H0; subst; tauto.
Qed.

Example check_heap_list_down : heap_list_down (pair [233;4;6;9;2;4;1;3] 1) (pair [233;9;6;4;2;4;1;3] 3).
Proof.
  unfold heap_list_down.
  unfold_RELS_tac.
  exists (pair [233;9;6;4;2;4;1;3] 3).
  split.
  + exists 1%nat.
    unfold nsteps.
    unfold_RELS_tac.
    exists ([233; 9; 6; 4; 2; 4; 1; 3], 3).
    split; [exact check_succeed_down|reflexivity].
  + unfold list_down_fail.
    unfold_RELS_tac.
    split; [|reflexivity].
    try_list_unfold.
    lia.
Qed.