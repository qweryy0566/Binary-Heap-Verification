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
Require Import cprogs.heap.list_relation.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.tree_list.
Require Import cprogs.heap.math_prop.

Require Import SetsClass.SetsClass.
Local Open Scope sets.
Import SetsNotation.

Definition tree_up_succeed:
  tree_state -> tree_state -> Prop:=
    fun t1 t2 => exists t3 l', 
    (t3::l' = (fst t1)) /\ (l' = (fst t2)) /\
    (exists v ls rs, (swap_up_and_combine v ls rs t3) = (snd t2) /\ (snd t1) = (Node v ls rs)) /\ 
    ((get_tree_val (snd t1)) > (snd (fst t3))).

Definition tree_up_fail:
  tree_state -> tree_state -> Prop:=
    Rels.test(fun t => 
      match (fst t) with
      | nil => True
      | t2::lt => snd (fst t2) >= (get_tree_val (snd t))
      end).

Definition heap_tree_up:
  tree_state -> tree_state -> Prop:=
  (clos_refl_trans tree_up_succeed) ∘ tree_up_fail.

Definition MaxHeap_tree_up(ts: tree_state): Prop :=
  MaxHeap_partial_tree (fst ts) /\ MaxHeap (snd ts) /\ (exists v ls rs, snd ts = Node v ls rs /\ 
  (ls = Leaf \/ MaxHeap_partial_tree_v (fst ts) (get_tree_val ls)) /\ 
  (rs = Leaf \/ MaxHeap_partial_tree_v (fst ts) (get_tree_val rs))).

Lemma swap_up_right_hold_true: forall (l l': list_state) (ls rs tr: tree) (v1 v2: Z) (lt: partial_tree),
  list_on_tree_state l ((true,v2,tr) :: lt, Node v1 ls rs) -> list_relation.list_swap (snd l) (snd l') (fst l) (fst l') -> snd l / 2 = snd l' -> list_on_tree_state l' (lt, Node v1 tr (Node v2 ls rs)).
Proof.
  unfold list_on_tree_state.
  unfold list_on_tree_state_fix.
  destruct l as [l n].
  destruct l' as [l' n'].
  simpl; intros; subst.
  destruct H, H1.
  inversion H1; [discriminate |].
  apply cons_inv in H3; destruct H3.
  inversion H2; subst; clear H2.
  assert (1 <= n / 2 < n). {
    split.
    + lia.
    + apply Div_2_gt_0.
      lia. 
  }
  inversion H.
  pose proof list_swap_rela_rewrite l l' n (n / 2) ltac:(lia) ltac:(lia) H0.
  subst; clear H0.
  split.
  + eapply list_nth_on_tree_Node; eauto.
    - rewrite list_swap_Zlength by lia; lia.
    - unfold list_swap.
      rewrite upd_Znth_diff.
      * rewrite upd_Znth_same; [auto | lia].
      * rewrite upd_Znth_Zlength by lia; lia.
      * rewrite upd_Znth_Zlength by lia; lia.
      * lia.
    - injection H3; intros; subst.
      replace (n / 2 * 2) with (n + -1) by lia. 
      unfold list_swap.
      apply list_nth_on_tree_upd.
      * apply list_nth_on_tree_upd; [auto | lia |].
        apply less_is_not_child_index; lia.
      * rewrite upd_Znth_Zlength by lia; lia.
      * apply rchild_is_not_lchild with (pp := n / 2); [lia | lia |].
        apply is_child_index_self; auto.
    - injection H3; intros; subst.
      rewrite <- H5.
      eapply list_nth_on_tree_Node.
      * rewrite list_swap_Zlength by lia; lia.
      * unfold list_swap.
        rewrite upd_Znth_same; [reflexivity | ].
        rewrite upd_Znth_Zlength by lia; lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           apply less_is_not_child_index; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply less_is_not_child_index; lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           apply less_is_not_child_index; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply less_is_not_child_index; lia.
  + split.
    inversion H8; subst.
    - eapply nil_partial_tree; eauto.
    - pose proof Z.div_lt_upper_bound (n / 2) 2 (n / 2) ltac:(lia) ltac:(lia).
      pose proof Z.div_le_lower_bound (n / 2) 2 1 ltac:(lia) ltac:(lia).
      eapply cons_partial_tree. eauto.
      * rewrite list_swap_Zlength by lia; lia. 
      * unfold list_swap.
        tauto.
      * unfold list_swap.
        rewrite upd_Znth_diff.
        -- rewrite upd_Znth_diff by lia; reflexivity.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- lia.
      * inversion H3; subst.
        unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           destruct flg0.
           ++ apply rchild_is_not_lchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_self; auto.
           ++ apply less_is_not_child_index; lia. 
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- destruct flg0.
           ++ apply rchild_is_not_lchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_gp; [lia | apply is_child_index_self; auto].
           ++ apply lchild_is_not_rchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_gp; [lia | apply is_child_index_self; auto].
      * apply list_on_partial_tree_upd.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply is_child_index_gp; [lia | ].
           apply is_child_index_gp; [lia | apply is_child_index_self; auto].
        -- apply list_on_partial_tree_upd; [lia | lia | |auto].
           apply is_child_index_gp; [lia | apply is_child_index_self; auto].
    - assert (tree_same (Node (Znth n l) tr (Node v2 ls rs)) (Node v2 tr (Node (Znth n l) ls rs))). {
      apply Node_same; [apply tree_same_rel; reflexivity|].
      apply Node_same; apply tree_same_rel; reflexivity.
    }
      split.
      * rewrite list_swap_Zlength by lia.
        rewrite <- H10.
        apply tree_same_size.
        apply tree_compose_same.
        apply H0.
      * destruct H11 as [dep].
        exists dep.
        apply (tree_same_complete_tree (tree_compose lt0 (Node v2 tr (Node (Znth n l) ls rs)))); [|tauto].
        apply tree_compose_same.
        apply tree_same_swap.
        apply H0.
Qed.

Lemma swap_up_left_hold_true: forall (l l': list_state) (ls rs tr: tree) (v1 v2: Z) (lt: partial_tree),
  list_on_tree_state l ((false,v2,tr) :: lt, Node v1 ls rs) -> list_relation.list_swap (snd l) (snd l') (fst l) (fst l') -> snd l / 2 = snd l' -> list_on_tree_state l' (lt, (Node v1 (Node v2 ls rs) tr)).
Proof.
  unfold list_on_tree_state.
  unfold list_on_tree_state_fix.
  destruct l as [l n].
  destruct l' as [l' n'].
  simpl; intros; subst.
  destruct H, H1.
  inversion H1; [discriminate |].
  apply cons_inv in H3; destruct H3.
  inversion H2; subst; clear H2.
  assert (1 <= n / 2 < n). {
    split.
    + lia.
    + apply Div_2_gt_0.
      lia. 
  }
  inversion H.
  inversion H5.
  pose proof list_swap_rela_rewrite l l' n (n / 2) ltac:(lia) ltac:(lia) H0.
  subst; clear H0.
  split.
  + eapply list_nth_on_tree_Node; eauto.
    - rewrite list_swap_Zlength by lia; rewrite <- H17; lia.
    - unfold list_swap.
      rewrite upd_Znth_diff; try rewrite <- H17.
      * rewrite upd_Znth_same; [auto | lia].
      * rewrite upd_Znth_Zlength by lia; lia.
      * rewrite upd_Znth_Zlength by lia; lia.
      * lia.
    - injection H3; intros; subst.
      rewrite <- H5.
      replace (n / 2 * 2) with (n) by lia. 
      eapply list_nth_on_tree_Node.
      * rewrite list_swap_Zlength by lia; lia.
      * unfold list_swap.
        rewrite upd_Znth_same; [reflexivity | ].
        rewrite upd_Znth_Zlength by lia; lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           apply less_is_not_child_index; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply less_is_not_child_index; lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           apply less_is_not_child_index; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply less_is_not_child_index; lia. 
    - inversion H3; subst.
      replace (n / 2 * 2 + 1) with (n + 1) by lia.
      unfold list_swap.
      apply list_nth_on_tree_upd.
      * apply list_nth_on_tree_upd; [auto | lia |].
        rewrite <- H5.
        replace (n / 2 * 2) with n by lia.
        apply H7.
        apply less_is_not_child_index.
        rewrite <- H5.
        lia.
      * rewrite upd_Znth_Zlength by lia; lia.
      * rewrite <- H17. 
        apply lchild_is_not_rchild with (pp := n / 2); [lia | lia |].
        apply is_child_index_self; auto.
        lia.
  + split. inversion H8; subst.
    - eapply nil_partial_tree; eauto.
      rewrite <- H17.
      lia.
    - pose proof Z.div_lt_upper_bound (n / 2) 2 (n / 2) ltac:(lia) ltac:(lia).
      pose proof Z.div_le_lower_bound (n / 2) 2 1 ltac:(lia) ltac:(lia).
      eapply cons_partial_tree; eauto.
      * rewrite list_swap_Zlength by lia; rewrite <- H17; lia. 
      * unfold list_swap.
        rewrite <- ! H17.
        rewrite <- ! H9.
        lia.
      * unfold list_swap.
        rewrite <- H17.
        rewrite upd_Znth_diff.
        -- rewrite upd_Znth_diff by lia; reflexivity.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- lia.
      * apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           destruct flg0; rewrite <- H17; tauto.
           destruct flg0; rewrite <- H17.
           ++ apply rchild_is_not_lchild with (pp := n / 2 / 2); [lia | lia |].
           apply is_child_index_self; auto.
           ++ apply less_is_not_child_index; lia. 
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- destruct flg0; rewrite <- H17.
           ++ apply rchild_is_not_lchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_gp; [lia | apply is_child_index_self; auto].
           ++ apply lchild_is_not_rchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_gp; [lia | apply is_child_index_self; auto].
      * unfold list_swap.
        apply list_on_partial_tree_upd; try rewrite <- H17.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply is_child_index_gp; [lia | ].
           apply is_child_index_gp; [lia | apply is_child_index_self; auto].
        -- apply list_on_partial_tree_upd; [lia | lia | |auto].
           apply is_child_index_gp; [lia | apply is_child_index_self; auto].
     - assert (tree_same (Node (Znth n l) (Node v2 ls rs) tr) (Node v2 (Node (Znth n l) ls rs) tr)). {
      apply Node_same; [|apply tree_same_rel; reflexivity].
      apply Node_same; apply tree_same_rel; reflexivity.
    }
      split.
      * rewrite list_swap_Zlength by lia.
        rewrite <- H10.
        apply tree_same_size.
        apply tree_compose_same.
        apply H0.
      * destruct H11 as [dep].
        exists dep.
        apply (tree_same_complete_tree (tree_compose lt0 (Node v2 (Node (Znth n l) ls rs) tr))); [|tauto].
        apply tree_compose_same.
        apply tree_same_swap.
        apply H0.
Qed.

Lemma Up_tree_list_succeed: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> list_up_succeed l l' -> MaxHeap_tree_up t ->
  exists t', tree_up_succeed t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_up t'.
Proof.
  intros.
  unfold list_up_succeed in H0.
  destruct H0, H2, H3, H4, H5.
  pose proof list_on_tree_state_impl_up_val _ _ H H0 ltac:(lia).
  destruct H7 as [lt [v [tr [flg]]]].
  destruct H7, H8.
  pose proof legal_list_impl_legal_tree_state _ _ H H0.
  unfold legal_tree_state in H10.
  destruct H10 as [v2 [ls [rs]]].
  rewrite H4 in H5.
  unfold get_list_val in H9; simpl in H9.
  rewrite H10 in H8; unfold get_tree_val in H8.
  assert (v2 > v) by lia.
  destruct flg.
  + exists (lt, (Node v2 tr (Node v ls rs))).
    split.
    - unfold tree_up_succeed.
      exists (true, v, tr), lt.
      split; [tauto|].
      split; [tauto|].
      split; [|rewrite H10; simpl; lia].
      exists v2, ls, rs.
      split; [|tauto].
      unfold swap_up_and_combine; simpl.
      reflexivity.
    - split.
      * eapply swap_up_right_hold_true; eauto.
        rewrite H7, <- H10.
        auto.
      * unfold MaxHeap_tree_up; simpl.
        unfold MaxHeap_tree_up in H1.
        destruct H1.
        rewrite <- H7 in H1.
        unfold MaxHeap_partial_tree in H1.
        destruct H1, H13.
        split; [apply (MaxHeap_partial_tree_v_impl _ _ H14)|].
        destruct H12.
        destruct H15 as [v3 [ls2 [rs2]]].
        rewrite H10 in H12; simpl in H12.
        destruct H15.
        rewrite H10 in H15.
        injection H15; intros; subst.
        split. destruct H13.
        ++ eapply MaxHeap_Node; [ reflexivity |apply H1 | |left; tauto|right; unfold get_tree_val; lia].
           destruct H16.
           inversion H12;[discriminate|].
           injection H16; intros; subst.
           eapply MaxHeap_Node; [reflexivity| | | | ]; try tauto.
           destruct H9; [left; tauto|].
           inversion H8; rewrite H9 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
           destruct H13; [left; tauto|]. inversion H8; rewrite H13 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
        ++ eapply MaxHeap_Node;[reflexivity|apply H1| | right; lia| right; unfold get_tree_val; lia].
           destruct H16.
           inversion H12;[discriminate|].
           injection H16; intros; subst.
           eapply MaxHeap_Node; [reflexivity| | | | ]; try tauto.
           destruct H9; [left; tauto|].
           inversion H9; rewrite H21 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
           destruct H13; [left; tauto|].
           inversion H13; rewrite H21 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
        ++ exists (get_list_val l), tr, (Node (Znth (snd l / 2) (fst l)) ls2 rs2); simpl.
           split; [reflexivity|].
           split; [|right; tauto].
           destruct H13; [left; tauto|right].
           apply (MaxHeap_partial_tree_v_change_v _ _ _ H14 H8).
  + exists (lt, (Node v2 (Node v ls rs) tr)).
    split.
    - unfold tree_up_succeed.
      exists (false, v, tr), lt.
      split; [tauto|].
      split; [tauto|].
      split; [|rewrite H10; simpl; lia].
      exists v2, ls, rs.
      split; [|tauto].
      unfold swap_up_and_combine; simpl.
      reflexivity.
    - split.
      * eapply swap_up_left_hold_true; eauto.
        rewrite H7, <- H10.
        auto.
      * unfold MaxHeap_tree_up. simpl.
        unfold MaxHeap_tree_up in H1.
        destruct H1.
        rewrite <- H7 in H1.
        unfold MaxHeap_partial_tree in H1.
        destruct H1, H13.
        split; [apply (MaxHeap_partial_tree_v_impl _ _ H14)|].
        destruct H12.
        destruct H15 as [v3 [ls2 [rs2]]].
        rewrite H10 in H12; simpl in H12.
        destruct H15.
        rewrite H10 in H15.
        injection H15; intros; subst.
        split. destruct H13.
        ++ eapply MaxHeap_Node; [ reflexivity | |apply H1 |right; unfold get_tree_val; lia|left; tauto].
           destruct H16.
           inversion H12;[discriminate|].
           injection H16; intros; subst.
           eapply MaxHeap_Node; [reflexivity| | | | ]; try tauto.
           destruct H9; [left; tauto|].
           inversion H8; rewrite H9 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
           destruct H13; [left; tauto|]. inversion H8; rewrite H13 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
        ++ eapply MaxHeap_Node; [ reflexivity | |apply H1 |right; unfold get_tree_val; lia|right; lia].
           destruct H16.
           inversion H12;[discriminate|].
           injection H16; intros; subst.
           eapply MaxHeap_Node; [reflexivity| | | | ]; try tauto.
           destruct H9; [left; tauto|].
           inversion H9; rewrite H21 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
           destruct H13; [left; tauto|].
           inversion H13; rewrite H21 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
        ++ exists (get_list_val l), (Node (Znth (snd l / 2) (fst l)) ls2 rs2), tr; simpl.
           split; [reflexivity|].
           split; [right; tauto |].
           destruct H13; [left; tauto|right].
           apply (MaxHeap_partial_tree_v_change_v _ _ _ H14 H8).
Qed.

Lemma Up_tree_list_succeed_clos_refl_trans: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> (clos_refl_trans list_up_succeed) l l' -> MaxHeap_tree_up t ->
  exists t', (clos_refl_trans tree_up_succeed) t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_up t'.
Proof.
  intros.
  revert t H H1.
  induction_1n H0.
  + exists t.
    split; [|tauto].
    exists 0%nat.
    unfold nsteps.
    reflexivity.
  + pose proof Up_tree_list_succeed _ _ _ H H2 H1.
    destruct H3 as [t'].
    destruct H3; destruct H4.
    specialize (IHrt _ H4 H5).
    destruct IHrt as [t'0].
    exists t'0.
    destruct H6, H7.
    split; [|tauto].
    etransitivity_1n; [apply H3|apply H6].
Qed.

Lemma Up_tree_list_fail: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> list_up_fail l l ->
  tree_up_fail t t.
Proof.
  intros.
  unfold list_up_fail in H0.
  destruct t as [lt t].
  revert H0; unfold_RELS_tac; intros.
  destruct H0; clear H1.
  destruct H0, H1.
  + pose proof list_on_tree_state_impl_all _ _  H ltac:(lia).
    simpl in H2.
    unfold tree_up_fail; unfold_RELS_tac.
    simpl.
    split; [|reflexivity].
    destruct lt; [tauto|discriminate].
  + destruct H1.
    pose proof list_on_tree_state_impl_up_val _ _ H H0 ltac:(lia).
    destruct H3 as [lt0].
    destruct H3, H3, H3, H3, H4.
    unfold tree_up_fail; unfold_RELS_tac.
    split; [|reflexivity].
    simpl; destruct lt; [discriminate|].
    simpl in H4.
    rewrite H4.
    simpl in H3.
    destruct p as [[flg v] tr]; subst.
    simpl.
    unfold get_list_val in H3.
    simpl in H3.
    injection H3.
    intros.
    lia.
Qed.

Lemma Up_fail_impl_MaxHeap: forall (t: tree_state),
  tree_up_fail t t -> MaxHeap_tree_up t -> MaxHeap (tree_compose (fst t) (snd t)).
Proof.
  intros.
  destruct t as [lt t].
  unfold tree_up_fail in H.
  revert H; unfold_RELS_tac; intros.
  simpl in H.
  destruct lt.
  + simpl.
    unfold MaxHeap_tree_up in H0.
    tauto.
  + destruct p as [[flg val] t2 ].
    simpl in H.
    simpl fst; simpl snd.
    destruct H; clear H1.
    unfold MaxHeap_tree_up in H0.
    simpl in H0.
    destruct H0, H0, H2.
    assert (MaxHeap_partial_tree ((flg, val, t2) :: lt)). {
      unfold MaxHeap_partial_tree.
      split; tauto.
    }
    destruct t.
    - pose proof MaxHeap_partial_tree_v_impl _ _ H3.
      destruct H1.
      apply (tree_compose_MaxHeap ((flg, val, t2) :: lt) Leaf H1 ltac:(tauto)).
    - assert (MaxHeap_partial_tree_v ((flg, val, t2) :: lt) v). {
        eapply MaxHeap_partial_tree_v_app; [reflexivity| | | | ]; try tauto.
        simpl in H.
        lia.
      }
      destruct H1.
      apply (tree_compose_MaxHeap ((flg, val, t2) :: lt) (Node v t1 t3) H1 ltac:(tauto)).
Qed.

Lemma list_up_fail_impl_eq: forall (l l': list_state),
  list_up_fail l l' -> l = l'.
Proof.
  intros; revert H.
  unfold list_up_fail.
  unfold_RELS_tac.
  tauto.
Qed.

Lemma Up_tree_list_rel: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> heap_list_up l l' -> MaxHeap_tree_up t ->
  exists t', heap_tree_up t t' /\ list_on_tree_state l' t' /\ MaxHeap (tree_compose (fst t') (snd t')).
Proof.
  intros.
  unfold heap_list_up in H0.
  revert H0; unfold_RELS_tac; intros.
  destruct H0 as [l1]; destruct H0.
  pose proof Up_tree_list_succeed_clos_refl_trans _ _ _ H H0 H1.
  pose proof list_up_fail_impl_eq _ _ H2.
  subst.
  destruct H3 as [t'].
  destruct H3, H4.
  exists t'.
  split.
  pose proof Up_tree_list_fail _ _ H4 H2.
  + unfold heap_tree_up.
    unfold_RELS_tac.
    exists t'.
    tauto.
  + split;[tauto|].
    pose proof Up_tree_list_fail _ _ H4 H2.
    apply (Up_fail_impl_MaxHeap _ H6 H5).
Qed.