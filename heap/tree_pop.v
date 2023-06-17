Require Import FloydSeq.proofauto.
(* Require Import cprogs.heap.program. *)
Require Import Notations Logic Datatypes.
From Coq Require Import String List ZArith. 
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Classical_Prop.

Require Import Coq.micromega.Psatz.
Local Open Scope string.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import cprogs.heap.list_relation.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.tree_list.
Require Import cprogs.heap.tree_down.

Fixpoint tree_to_partial_tree_pop_fix (tl: partial_tree) (t: tree) (d: Z): partial_tree :=
  match t with
    | Leaf => tl
    | Node v ls rs => 
      match (full_tree_b (d - 2) rs) with
      | false => tree_to_partial_tree_pop_fix ((false, v, ls) :: tl) rs (d-1)
      | true => tree_to_partial_tree_pop_fix ((true, v, rs) :: tl) ls (d-1)
      end (*true go right and right is cut*)
  end.

Definition tree_to_partial_tree_pop(t: tree) (d: Z): partial_tree := 
  tree_to_partial_tree_pop_fix nil t d.

Definition get_last_val(l: partial_tree): Z :=
  match l with
    | nil => 0
    | (flg, v, tr)::lt => v
  end.

Definition tree_cut_last(ls rs: tree) (d: Z): tree :=
  if (full_tree_b (d - 2) rs) then
    (Node (get_last_val (tree_to_partial_tree_pop ls (d-1)))
        (tree_compose (skipn 1%nat (tree_to_partial_tree_pop ls (d-1))) Leaf) rs)
  else (Node (get_last_val (tree_to_partial_tree_pop rs (d-1)))
        ls (tree_compose (skipn 1%nat (tree_to_partial_tree_pop rs (d-1))) Leaf)).

Definition tree_pop: tree -> tree -> Prop :=
  fun t t' => (tree_size t <= 1  /\ t' = Leaf) \/
    (exists v ls rs ts d, t = (Node v ls rs) /\ complete_tree_pop d t /\ heap_tree_down (nil,(tree_cut_last ls rs d)) ts /\ t' = (tree_compose (fst ts) (snd ts))).

Lemma list_on_tree_impl_state: forall (l: list Z) (ls rs: tree) (v: Z),
  Zlength l > 2 -> list_on_tree l (Node v ls rs) ->
  exists d, list_on_tree_state (firstn (Z.to_nat (Zlength l - 1)) (upd_Znth 1 l (Znth (Zlength l - 1) l)), 1) (nil, tree_cut_last ls rs d) /\  complete_tree_pop d (Node v ls rs).
Proof.
Admitted.

Lemma tree_not_emp: forall (t: tree),
  tree_size t >= 1 -> exists v ls rs, t = Node v ls rs.
Proof.
Admitted.

Lemma MaxHeap_tree_down_state: forall (ls rs: tree) (d v: Z),
  MaxHeap (Node v ls rs) -> complete_tree_pop d (Node v ls rs) -> MaxHeap_tree_down ([], tree_cut_last ls rs d).
Proof.
Admitted.

Lemma Pop_tree_list_rel: forall (l l': list Z) (t: tree),
  list_on_tree l t -> heap_pop l l' -> MaxHeap t ->
  exists t', list_on_tree l' t' /\ MaxHeap t' /\ tree_pop t t'.
Proof.
  intros.
  unfold heap_pop in H0.
  destruct H0.
  + exists Leaf.
    unfold list_on_tree in H.
    destruct H, H2, H0.
    unfold list_on_tree.
    split.
    * split; [apply list_nth_on_tree_Leaf|].
      split; [simpl; lia|].
      exists 1.
      apply complete_tree_push_Leaf.
      lia.
    * split;[apply MaxHeap_Leaf; reflexivity|].
      unfold tree_pop; left.
      split;[lia|reflexivity].
  + destruct H0.
    destruct H2 as [pl].
    remember H as H'; clear HeqH'.
    unfold list_on_tree in H.
    pose proof tree_not_emp t ltac:(lia).
    destruct H3 as [v [ls [rs]]].
    rewrite H3 in H'.
    pose proof list_on_tree_impl_state _ _ _ _ H0 H'.
    destruct H4 as [d].
    destruct H4.
    assert (Zlength (fst (firstn (Z.to_nat (Zlength l - 1))
          (upd_Znth 1 l (Znth (Zlength l - 1) l)), 1)) >= 2). {
      give_up.
    }
    pose proof Down_tree_list_rel _ _ _ H6 H4 H2.
    subst.
    pose proof MaxHeap_tree_down_state _ _ _ _ H1 H5.
    specialize (H7 H3).
    destruct H7 as [t'].
    destruct H7, H8.
    pose proof list_on_tree_state_impl_tree_compose _ _ H8.
    simpl in H10.
    exists (tree_compose (fst t') (snd t')).
    split; [tauto|].
    split; [tauto|].
    unfold tree_pop; right.
    exists v, ls, rs, t', d.
    tauto.
Admitted.