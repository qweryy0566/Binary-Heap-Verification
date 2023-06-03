Require Import FloydSeq.proofauto.
Require Import cprogs.heap.program.
Require Import cprogs.heap.list_relation.

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
Require Import Classical_Prop.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
Notation "'store_int' p x" :=
  (@data_at CompSpecs Tsh tint (Vint(IntRepr(x))) p)
  (x at level 0, p at level 0, at level 0).
Notation "'store_int_array' p l size" :=
  (@data_at CompSpecs Tsh (tarray tint size) (map Vint (map Int.repr l)) p)
  (p at level 0, l at level 0, size at level 0, at level 0).

(* Parameter MaxHeap : list Z -> Z -> Prop. *)
(* Parameter MaxHeap_p : list Z -> Z -> Z -> Prop. *)
(* Parameter shr : Z -> Z -> Z. *)

(* Parameter up : list Z -> Z -> Z -> Z -> list Z. *)
(* Parameter down : list Z -> Z -> Z -> Z -> list Z. *)
(* Parameter push : list Z -> Z -> Z -> list Z. *)
(* Parameter pop : list Z -> Z -> list Z. *)
(* Parameter pop_length : list Z -> Z -> Z. *)
(* Parameter pop_result : list Z -> Z -> Z. *)

Import ListNotations.

Lemma int_array_is_ptr: forall (p: val) (l: list Z) (size: Z),
  !!(size >= 0) && store_int_array p l size |-- !!isptr p.
Proof.
  intros.
  entailer!.
Qed.

Definition heap_push: list Z -> Z -> list Z -> Prop :=
  fun l val l' =>
    exists (p: Z), heap_list_up (pair (l ++ [val]) (Zlength l)) (pair l' p).

Definition heap_pop: list Z -> list Z -> Prop :=
  fun l l' =>
    exists (p: Z), heap_list_down (pair (removelast ([Znth 0 l; Znth (Zlength l - 1) l] ++ (skipn 2%nat l))) 1) (pair l' p).

Lemma list_length: forall (p: val) (l: list Z) (size: Z),
  !!(size >= 0) && store_int_array p l size |-- !!(Zlength l = size).
Proof.
  intros.
  entailer!.
  rewrite Zlength_map, Zlength_map.
  reflexivity.
Qed.

Definition up: list Z -> Z -> Z -> Z -> list Z -> Prop :=
  fun l size p0 p1 l' =>
    heap_list_up ((firstn (Z.to_nat (size + 1)) l), p0) ((firstn (Z.to_nat (size + 1)) l'), p1).

Definition up_inv: list Z -> Z -> Z -> Z -> list Z -> Prop :=
  fun l size p0 p1 l' =>
    (clos_refl_trans list_up_succeed) ((firstn (Z.to_nat (size + 1)) l), p0) ((firstn (Z.to_nat (size + 1)) l'), p1).

Definition down: list Z -> Z -> Z -> Z -> list Z -> Prop :=
  fun l size p0 p1 l' =>
    heap_list_down ((firstn (Z.to_nat (size + 1)) l), p0) ((firstn (Z.to_nat (size + 1)) l'), p1).

Definition down_inv: list Z -> Z -> Z -> Z -> list Z -> Prop :=
  fun l size p0 p1 l' =>
    (clos_refl_trans list_down_succeed) ((firstn (Z.to_nat (size + 1)) l), p0) ((firstn (Z.to_nat (size + 1)) l'), p1).

Definition push: list Z -> Z -> Z -> list Z -> Prop :=
  fun l size val l' =>
    heap_push (firstn (Z.to_nat (size + 1)) l) val (firstn (Z.to_nat (size + 2)) l').

Definition pop: list Z -> Z -> list Z -> Prop :=
  fun l size l' =>
    size = 0 /\ l = l' \/ size > 0 /\ heap_pop (firstn (Z.to_nat (size + 1)) l) (firstn (Z.to_nat size) l').

Definition pop_length (l: list Z) (size: Z): Z :=
  match size with
    | 0 => 0
    | _ => size - 1
  end.

Definition pop_result (l: list Z) (size: Z): Z :=
  match size with
    | 0 => -1
    | _ => 0
  end.

Fixpoint all_int (l: list Z): Prop :=
  match l with
  | nil => True
  | h :: l0 => Int.min_signed <= h <= Int.max_signed /\ all_int l0
  end.

Lemma all_int_app: forall (l1 l2: list Z),
  all_int l1 -> all_int l2 -> all_int (l1 ++ l2).
Proof.
  intros.
  induction l1; [tauto|].
  rewrite <- app_comm_cons.
  revert H.
  unfold all_int; fold all_int.
  intros.
  destruct H.
  split; tauto.
Qed.

Lemma all_int_sublist: forall (Hl: list Z) (l r: Z),
  all_int Hl -> all_int (sublist l r Hl).
Proof.
  intros.
  unfold sublist.
  assert (forall (lt: list Z) (p: nat), all_int lt -> all_int (skipn p lt)). {
    intros; revert lt H0.
    induction p.
    + unfold skipn; tauto.
    + intros.
      destruct lt; [rewrite skipn_nil; tauto|].
      assert (skipn p lt = skipn (S p) (z :: lt)) by reflexivity.
      rewrite <- H1.
      unfold all_int in H0; fold all_int in H0.
      destruct H0.
      apply IHp; tauto.
  }
  assert (forall (lt: list Z) (p: nat), all_int lt -> all_int (firstn p lt)). {
    intros; revert lt H1.
    induction p.
    + unfold firstn, all_int. tauto.
    + intros.
      destruct lt; [rewrite firstn_nil; tauto|].
      assert (z :: firstn p lt = firstn (S p) (z :: lt)) by reflexivity.
      rewrite <- H2.
      revert H1.
      unfold all_int; fold all_int; intros.
      destruct H1.
      split; [tauto|].
      apply IHp; tauto.
  }
  apply H1.
  apply H0.
  tauto.
Qed.

Lemma all_int_Znth: forall (l: list Z) (p: Z),
  all_int l -> 0 <= p < (Zlength l) -> 
  Int.min_signed <= (Znth p l) <= Int.max_signed.
Proof.
  intros.
  destruct H0.
  assert (p + 1 <= Zlength l) by lia.
  pose proof sublist_one p (p+1) l H0 H2 ltac:(lia).
  pose proof all_int_sublist l p (p+1) H.
  rewrite H3 in H4.
  unfold all_int in H4.
  tauto.
Qed.

Lemma all_int_upd_Znth: forall (l: list Z) (p val: Z),
  all_int l ->
  Int.min_signed <= val -> val <= Int.max_signed ->
  all_int (upd_Znth p l val).
Proof.
  intros.
  unfold upd_Znth.
  apply all_int_app.
  + apply all_int_sublist; tauto.
  + unfold all_int; fold all_int.
    split; [tauto|].
    apply all_int_sublist; tauto.
Qed.

Lemma firstn_app_upd_Znth: forall (l: list Z) (val: Z) (pos: nat), 
  (Z.of_nat pos) < Zlength l ->
  firstn (pos + 1) (upd_Znth (Z.of_nat pos) l val) = (firstn pos l) ++ [val].
Proof.
  intros.
  revert l H.
  induction pos; intros; [tauto|].
  destruct l; [discriminate|].
  replace (upd_Znth (Z.of_nat (S pos)) (z :: l) val) with (z :: (upd_Znth (Z.of_nat pos) l val)).
  + assert ( ((S pos) + 1 = S (pos +1))%nat ) by lia.
    rewrite H0.
    rewrite ! firstn_cons.
    rewrite <- app_comm_cons.
    rewrite Zlength_cons in H.
    assert (Z.of_nat pos < Zlength l ) by lia.
    pose proof (IHpos l H1).
    rewrite H2.
    reflexivity.
  + assert (z::l = [z]++l) by reflexivity.
    rewrite H0 in H.
    assert (1<= (Z.of_nat (S pos)) <= Zlength ([z] ++ l)) by lia.
    rewrite H0.
    rewrite Zlength_app in H1.
    pose proof (upd_Znth_app2 [z] l (Z.of_nat (S pos)) val H1).
    rewrite H2.
    replace (Z.of_nat pos) with (Z.of_nat (S pos) - Zlength [z]); [reflexivity|].
    unfold Zlength; unfold Zlength_aux.
    lia.
Qed.

Lemma left_son_check_hold: forall l pos len1 len2,
  len2 <= len1 -> len2 >= 1 ->
  ~left_son_check_list (firstn (Z.to_nat len1) l, pos) ->
  ~left_son_check_list (firstn (Z.to_nat len2) l, pos).
Proof.
  unfold left_son_check_list.
  intros.
  apply or_not_and.
  apply not_and_or in H1.
  destruct H1.
  + left.
    revert H1.
    unfold legal_list_state.
    simpl fst; simpl snd.
    rewrite !Zlength_firstn.
    lia.
  + assert (pos*2 > len2 - 1 \/ pos*2 <= len2 - 1) by lia.
    destruct H2.
    - left.
      unfold legal_list_state.
      simpl fst; simpl snd.
      rewrite !Zlength_firstn.
      apply or_not_and.
      lia.
    - right.
      revert H1.
      unfold get_list_val.
      simpl fst; simpl snd.
      intros.
      pose proof (Zfirstn_firstn l len2 len1 H).
      rewrite <- H3.
      assert (pos < len2) by lia.
      assert (pos * 2 < len2) by lia.
      pose proof (Znth_firstn (firstn (Z.to_nat len1) l) pos len2 H4).
      pose proof (Znth_firstn (firstn (Z.to_nat len1) l) (pos*2) len2 H5).
      rewrite H6, H7.
      tauto.
Qed.

Lemma right_son_check_hold: forall l pos len1 len2,
  len2 <= len1 -> len2 >= 1 ->
  ~right_son_check_list (firstn (Z.to_nat len1) l, pos) ->
  ~right_son_check_list (firstn (Z.to_nat len2) l, pos).
Proof.
  unfold left_son_check_list.
  intros.
  apply or_not_and.
  apply not_and_or in H1.
  destruct H1.
  + left.
    revert H1.
    unfold legal_list_state.
    simpl fst; simpl snd.
    rewrite !Zlength_firstn.
    lia.
  + assert (pos*2+1 > len2 - 1 \/ pos*2+1 <= len2 - 1) by lia.
    destruct H2.
    - left.
      unfold legal_list_state.
      simpl fst; simpl snd.
      rewrite !Zlength_firstn.
      lia.
    - right.
      revert H1.
      unfold get_list_val.
      simpl fst; simpl snd.
      intros.
      pose proof (Zfirstn_firstn l len2 len1 H).
      rewrite <- H3.
      assert (pos < len2) by lia.
      assert (pos*2+1 < len2) by lia.
      pose proof (Znth_firstn (firstn (Z.to_nat len1) l) pos len2 H4).
      pose proof (Znth_firstn (firstn (Z.to_nat len1) l) (pos*2+1) len2 H5).
      rewrite H6, H7.
      tauto.
Qed.

Lemma son_check_hold: forall l pos len1 len2,
  len2 <= len1 -> len2 >= 1 ->
  ~left_son_check_list (firstn (Z.to_nat len1) l, pos) /\
  ~right_son_check_list (firstn (Z.to_nat len1) l, pos) ->
  ~left_son_check_list (firstn (Z.to_nat len2) l, pos) /\ ~right_son_check_list (firstn (Z.to_nat len2) l, pos).
Proof.
  intros.
  destruct H1.
  split.
  + apply (left_son_check_hold l pos len1 len2 H H0 H1).
  + apply (right_son_check_hold l pos len1 len2 H H0 H2).
Qed.

(* Lemma MaxHeap_p_coincidence_for_idx: forall l (x1 y1 x2 y2: Z),
  MaxHeap_p l x1 y1 -> 0 <= x1 <= x2 -> 0 <= y2 <= y1 -> MaxHeap_p l x2 y2.
Proof.
  intros.
  unfold MaxHeap_p in H.
  unfold MaxHeap_p.
  intros.
  apply (son_check_hold l i (y1 + 1) (y2 + 1)); [lia | lia | ].
  apply H.
  lia.
Qed. *)

(* Search sublist.
Print sublist. *)

Definition list_swap (l: list Z) (i j: Z) : list Z :=
  upd_Znth i (upd_Znth j l (Znth i l)) (Znth j l).

Lemma list_swap_len: forall l i j,
  0 <= i < Zlength l -> 0 <= j < Zlength l ->
  Zlength (list_swap l i j) = Zlength l.
Proof.
  intros.
  unfold list_swap.
  rewrite !upd_Znth_Zlength.
  + reflexivity.
  + lia.
  + rewrite upd_Znth_Zlength by lia.
    lia.
Qed.

Lemma all_int_swap: forall l i j,
  all_int l ->
  0 <= i < Zlength l -> 0 <= j < Zlength l ->
  all_int (list_swap l i j).
Proof.
  intros.
  unfold list_swap.
  apply all_int_upd_Znth.
  + apply all_int_upd_Znth; [exact H |  |].
    - pose proof all_int_Znth _ _ H H0.
      lia.
    - pose proof all_int_Znth _ _ H H0.
      lia.
  + pose proof all_int_Znth _ _ H H1.
    lia.
  + pose proof all_int_Znth _ _ H H1.
    lia.
Qed.

Lemma list_swap_rela_correct: forall l i j,
  0 <= i < Zlength l -> 0 <= j < Zlength l ->
  list_relation.list_swap i j l (list_swap l i j).
Proof.
  intros.
  unfold list_relation.list_swap.
  unfold list_swap.
  split.
  + rewrite !upd_Znth_Zlength.
    - reflexivity.
    - lia.
    - rewrite upd_Znth_Zlength by lia.
      lia.
  + split.
    assert (i = j \/ i <> j) by lia.
    destruct H1.
    - subst.
      rewrite upd_Znth_same; [reflexivity | ].
      rewrite upd_Znth_Zlength by lia.
      lia. 
    - rewrite upd_Znth_diff.
      * rewrite upd_Znth_same; [reflexivity | lia].
      * rewrite upd_Znth_Zlength; lia.
      * rewrite upd_Znth_Zlength; lia.
      * lia.
    - split.
      assert (i = j \/ i <> j) by lia.
      destruct H1.
      * subst.
        rewrite upd_Znth_same; [reflexivity |].
        rewrite upd_Znth_Zlength by lia.
        lia. 
      * rewrite upd_Znth_same; [reflexivity |].
        rewrite upd_Znth_Zlength; lia.
      * intros.
        destruct H1 as [? [? ?] ].
        rewrite upd_Znth_diff.
        rewrite upd_Znth_diff by lia.
        reflexivity.
        rewrite upd_Znth_Zlength; lia.
        rewrite upd_Znth_Zlength; lia.
        lia.
Qed.

Lemma firstn_eq_sublist: forall {A: Type} (l: list A) i,
  firstn (Z.to_nat i) l = sublist 0 i l.
Proof.
  intros.
  unfold sublist.
  simpl.
  replace (i - 0) with i by lia.
  tauto.
Qed.

Lemma list_swap_firstn: forall l i j len,
  0 <= i < len -> 0 <= j < len -> len <= Zlength l ->
  firstn (Z.to_nat len) (list_swap l i j) = list_swap (firstn (Z.to_nat len) l) i j.
Proof.
  intros.
  unfold list_swap.
  rewrite !firstn_eq_sublist.
  rewrite !sublist_upd_Znth_lr; try lia.
  + rewrite !Znth_sublist; try lia.
    replace (i - 0) with i by lia.
    replace (j - 0) with j by lia.
    replace (i + 0) with i by lia.
    replace (j + 0) with j by lia.
    reflexivity.
  + rewrite upd_Znth_Zlength; lia.  
Qed.

Lemma list_swap_rela_correct_firstn: forall l i j len,
  0 <= i < len -> 0 <= j < len -> len <= Zlength l ->
  list_relation.list_swap i j (firstn (Z.to_nat len) l) (firstn (Z.to_nat len) (list_swap l i j)).
Proof.
  intros.
  rewrite list_swap_firstn by lia.
  apply list_swap_rela_correct.
  + rewrite Zlength_firstn.
    lia.
  + rewrite Zlength_firstn.
    lia.  
Qed.

Lemma list_swap_eq: forall l i j,
  0 <= i < Zlength l -> 0 <= j < Zlength l ->
  list_swap l i j = list_swap l j i.
Proof.
  intros.
  eapply Znth_eq_ext.
  + rewrite !list_swap_len by lia.
    reflexivity.
  + intros.
    unfold list_swap.
    assert (i = i0 \/ i <> i0) by lia.
    destruct H2.
    - subst.
      rewrite upd_Znth_same.
      assert (j = i0 \/ j <> i0) by lia.
      destruct H2.
      * subst.
        rewrite upd_Znth_same; [reflexivity | rewrite upd_Znth_Zlength; lia].
      * rewrite upd_Znth_diff.
        rewrite upd_Znth_same; [reflexivity | lia ].
        rewrite upd_Znth_Zlength; lia.
        rewrite upd_Znth_Zlength; lia.
        lia.
      * rewrite upd_Znth_Zlength; lia.
    - rewrite list_swap_len in H1 by lia.
      rewrite upd_Znth_diff.
      assert (j = i0 \/ j <> i0) by lia. 
      destruct H3.
      * subst.
        rewrite !upd_Znth_same; [reflexivity | rewrite upd_Znth_Zlength; lia | lia].
      * rewrite !upd_Znth_diff; try lia.
        ++ rewrite upd_Znth_Zlength by lia; lia.
        ++ rewrite upd_Znth_Zlength by lia; lia.
      * rewrite upd_Znth_Zlength; lia.
      * rewrite upd_Znth_Zlength; lia.
      * lia.     
Qed.
(* Lemma up_pos_in_range: forall l l' x y size,
  (up l size x y l') -> (1 <= y /\ y <= size).
Proof.
  intros.
  unfold up,heap_list_up in H.
  induction H.
  induction x0.
  + unfold nsteps in H.
Qed. *)


(* Lemma MaxHeap_p_coincidence_for_list: forall l l' x y,
  MaxHeap_p l x y ->
  (forall i, x <= i <= y -> Znth i l = Znth i l') ->
  MaxHeap_p l' x y.
Proof. Admitted.

Lemma MaxHeap_up_succeed: forall l l' pos size,
  Zlength l >= size + 1 -> size >= 1 ->
  MaxHeap l (pos-1) -> MaxHeap_p l pos size -> list_up_succeed ((firstn (Z.to_nat (size+1)) l),pos) (l',(pos/2))
  -> MaxHeap l' (pos/2 - 1) /\ MaxHeap_p l' (pos/2) size.
Proof.
  intros.
  unfold list_up_succeed in H3.
  unfold legal_list_state in H3.
  simpl fst in H3.
  simpl snd in H3.
  rewrite !Zlength_firstn in H3.
  replace (Z.min (Z.max 0 (size + 1)) (Zlength l)) with (size + 1) in H3 by lia.
  destruct H3 as [? [?  [? [? [? ?] ] ] ] ].
  split.
  + Admitted.

Lemma MaxHeap_up_fail: forall l pos size, 
  MaxHeap l (pos-1) -> MaxHeap_p l pos size
  -> list_up_fail ((firstn (Z.to_nat (size + 1)) l), pos) ((firstn (Z.to_nat (size + 1)) l), pos)
  -> MaxHeap l size.
Proof.
  intros.
  unfold list_up_fail in H1.
  revert H1; unfold_RELS_tac; intros.
  destruct H1; clear H2.
  destruct H1, H2.
  + unfold snd in H2; subst.
    apply H0.
  + revert H2; unfold fst, snd; intros.
    destruct H2.
    Admitted. *)