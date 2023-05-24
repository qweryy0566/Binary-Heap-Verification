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


Definition MaxHeap_p (l: list Z) (lo hi: Z): Prop :=
  True.
  (* forall (i: Z), lo <= i <= hi ->
    ~(left_son_check_list ((firstn (Z.to_nat (hi + 1)) l), i)) /\ ~(right_son_check_list ((firstn (Z.to_nat (hi + 1)) l), i)). *)

Definition MaxHeap (l: list Z) (size: Z): Prop :=
  True.
  (* MaxHeap_p l 1 size. *)

Definition up: list Z -> Z -> Z -> Z -> list Z -> Prop :=
  fun l size p0 p1 l' =>
    heap_list_up ((firstn (Z.to_nat (size + 1)) l), p0) ((firstn (Z.to_nat (size + 1)) l'), p1).

Definition down: list Z -> Z -> Z -> Z -> list Z -> Prop :=
  fun l size p0 p1 l' =>
    heap_list_down ((firstn (Z.to_nat (size + 1)) l), p0) ((firstn (Z.to_nat (size + 1)) l'), p1).

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

Fixpoint all_nonneg (l: list Z): Prop :=
  match l with
  | nil => True
  | h :: l0 => 0 <= h <= Int.max_signed /\ all_nonneg l0
  end.

Lemma left_son_check_hold: forall l pos len1 len2,
  len2 <= len1 -> len2 >= 0 ->
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
      (* lia. *)
      give_up.
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
(* Qed. *)
Admitted.

Lemma right_son_check_hold: forall l pos len1 len2,
  len2 <= len1 -> len2 >= 0 ->
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
      (* lia. *)
      give_up.
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
(* Qed. *)
Admitted.

Lemma son_check_hold: forall l pos len1 len2,
  len2 <= len1 -> len2 >= 0 ->
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

Lemma sublist_eq_ext: forall l l' x y,
  0 <= x ->
  (sublist x y l = sublist x y l' <->
  forall i, x <= i < y -> Znth i l = Znth i l').
Proof.
  intros.
  split.
  + intros.
    pose proof (Znth_sublist x (i - x) y l).
    replace (i - x + x) with i in H2 by lia.
    rewrite <- H2; [| lia | lia].
    pose proof (Znth_sublist x (i - x) y l').
    replace (i - x + x) with i in H3 by lia.
    rewrite <- H3; [| lia | lia].
    rewrite H0.
    reflexivity.
  +   
Admitted.

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