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

Require Import SetsClass.SetsClass.
Local Open Scope sets.
Import SetsNotation.

Definition tree_down_succeed:
  tree_state -> tree_state -> Prop:=
    fun t1 t2 => exists t, (t::(fst t1)) = (fst t2) /\ (exists v ls rs, (snd t1) = (Node v ls rs) /\ (
      ((left_son_check_tree v ls rs) /\ ~(right_son_check_tree v ls rs) /\ (swap_down_left v ls rs (snd t2) t)) \/
      (~(left_son_check_tree v ls rs) /\ (right_son_check_tree v ls rs) /\ (swap_down_right v ls rs (snd t2) t)) \/
      ((left_son_check_tree v ls rs) /\ (right_son_check_tree v ls rs) /\ (
        ((get_tree_val rs) > (get_tree_val ls) /\ (swap_down_right v ls rs (snd t2) t)) \/
        ((get_tree_val rs) <= (get_tree_val ls) /\ (swap_down_left v ls rs (snd t2) t)))
      ))
    ).

Definition tree_down_fail:
  tree_state -> tree_state -> Prop:=
  Rels.test(
    fun t => exists v ls rs, ((snd t) = Node v ls rs) /\ (legal_tree_state t) /\ ~(left_son_check_tree v ls rs) /\ ~(right_son_check_tree v ls rs)
  ).

Definition heap_tree_down:
  tree_state -> tree_state -> Prop:=
  (clos_refl_trans tree_down_succeed) ∘ tree_down_fail.

Definition MaxHeap_tree_down(ts: tree_state): Prop :=
  MaxHeap_partial_tree_v (fst ts) (get_tree_val (snd ts)) /\ MaxHeap_no_rt (snd ts) /\
  (exists v ls rs, snd ts = Node v ls rs /\
  (ls = Leaf \/ MaxHeap_partial_tree_v (fst ts) (get_tree_val ls)) /\
  (rs = Leaf \/ MaxHeap_partial_tree_v (fst ts) (get_tree_val rs))).

Lemma left_son_check_equal: forall l n v ls rs,
  list_nth_on_tree l n (Node v ls rs) ->
  left_son_check_list (l, n) <-> left_son_check_tree v ls rs.
Proof.
  intros.
  inversion H; [discriminate | ].
  inversion H0; subst.
  split; intros.
  + unfold left_son_check_list in H2.
    unfold left_son in H2; simpl in H2.
    destruct H2 as [? ?].
    unfold legal_list_state in H2; simpl in H2.
    inversion H3; [lia | subst].
    unfold left_son_check_tree; split.
    - unfold not; intros.
      discriminate.
    - unfold get_tree_val.
      unfold get_list_val in H5; simpl in H5.
      replace (n * 2) with (2 * n) by lia.
      lia.
  + unfold left_son_check_tree in H2; destruct H2.
    inversion H3; [tauto | subst].
    unfold left_son_check_list; unfold left_son; simpl.
    split.
    - unfold legal_list_state; simpl; lia.
    - unfold get_list_val; simpl.
      unfold get_tree_val in H5.
      replace (n * 2) with (2 * n) in H5 by lia.
      lia.
Qed.

Lemma right_son_check_equal: forall l n v ls rs,
  list_nth_on_tree l n (Node v ls rs) ->
  right_son_check_list (l, n) <-> right_son_check_tree v ls rs.
Proof.
  intros.
  inversion H; [discriminate | ].
  inversion H0; subst.
  split; intros.
  + unfold right_son_check_list in H2.
    unfold right_son in H2; simpl in H2.
    destruct H2 as [? ?].
    unfold legal_list_state in H2; simpl in H2.
    inversion H4; [lia | subst].
    unfold right_son_check_tree; split.
    - unfold not; intros.
      discriminate.
    - unfold get_tree_val.
      unfold get_list_val in H5; simpl in H5.
      replace (n * 2) with (2 * n) by lia.
      lia.
  + unfold right_son_check_tree in H2; destruct H2.
    inversion H4; [tauto | subst].
    unfold right_son_check_list; unfold right_son; simpl.
    split.
    - unfold legal_list_state; simpl; lia.
    - unfold get_list_val; simpl.
      unfold get_tree_val in H5.
      replace (n * 2) with (2 * n) in H5 by lia.
      lia.
Qed.

Lemma converse_neg: forall (P Q: Prop),
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros.
  unfold not; intros.
  apply H0; apply H; assumption.
Qed.

Lemma swap_down_left_hold: forall l n l' n' pt v ls rs v0 ls0 rs0,
  list_on_tree_state (l, n) (pt, Node v ls rs) ->
  left_son_swap (l, n) (l', n') ->
  ls = Node v0 ls0 rs0 ->
  list_on_tree_state (l', n') ((false, v0, rs) :: pt, Node v ls0 rs0).
Proof.
  intros.
  unfold list_on_tree_state in H.
  unfold list_on_tree_state_fix in H.
  simpl in H; destruct H as [? ?].
  subst.
  unfold left_son_swap in H0; simpl in H0.
  destruct H0; subst.
  inversion H; [discriminate | ].
  inversion H1; subst v1 ls rs1.
  inversion H5; [discriminate | ].
  inversion H4; subst v1 ls rs1.
  pose proof list_swap_rela_rewrite l l' n (2 * n) ltac:(lia) ltac:(lia) H0.
  subst l'.
  assert (Zlength (list_swap l n (2 * n)) = Zlength l). {
    rewrite list_swap_Zlength by lia; lia.
  }
  assert (Zlength (upd_Znth (2 * n) l (Znth n l)) = Zlength l). {
    rewrite upd_Znth_Zlength; lia.
  }
  assert (Zlength (upd_Znth (n * 2) l (Znth n l)) = Zlength l). {
    rewrite upd_Znth_Zlength; lia.
  }
  unfold list_on_tree_state.
  unfold list_on_tree_state_fix.
  simpl; split.
  + eapply list_nth_on_tree_Node; eauto.
    - lia.
    - unfold list_swap.
      rewrite upd_Znth_diff by lia.
      rewrite upd_Znth_same by lia; reflexivity.
    - unfold list_swap.
      apply list_nth_on_tree_upd; [ | lia | ].
      * apply list_nth_on_tree_upd; [ | lia | ].
        ++ replace (2 * n) with (n * 2) by lia; assumption.
        ++ apply less_is_not_child_index; lia.
      * apply less_is_not_child_index; lia.
    - unfold list_swap.
      apply list_nth_on_tree_upd; [ | lia | ].
      * apply list_nth_on_tree_upd; [ | lia | ].
        ++ replace (2 * n) with (n * 2) by lia; assumption.
        ++ apply less_is_not_child_index; lia.
      * apply less_is_not_child_index; lia.
  + eapply cons_partial_tree; eauto; simpl.
    - lia.
    - replace (2 * n) with (n * 2) by lia; rewrite Z.div_mul by lia; lia.
    - replace (2 * n) with (n * 2) by lia; rewrite Z.div_mul by lia.
      unfold list_swap.
      rewrite upd_Znth_same by lia; reflexivity.
    - unfold list_swap.
      apply list_nth_on_tree_upd; [ | lia | ].
      * apply list_nth_on_tree_upd; [ | lia | ].
        ++ replace (2 * n) with (n * 2) by lia; assumption.
        ++ apply less_is_not_child_index; lia.
      * apply less_is_not_child_index; lia.
    - replace (2 * n) with (n * 2) by lia; rewrite Z.div_mul by lia.
      apply list_on_partial_tree_upd; try lia.
      * apply is_child_index_self; reflexivity.
      * apply list_on_partial_tree_upd; try lia.
        ++ apply is_child_index_gp_inv_left; [lia | ].
           apply is_child_index_self; reflexivity.
        ++ assumption.
Qed.

Lemma swap_down_right_hold: forall l n l' n' pt v ls rs v0 ls0 rs0,
  list_on_tree_state (l, n) (pt, Node v ls rs) ->
  right_son_swap (l, n) (l', n') ->
  rs = Node v0 ls0 rs0 ->
  list_on_tree_state (l', n') ((true, v0, ls) :: pt, Node v ls0 rs0).
Proof.
  intros.
  unfold list_on_tree_state in H.
  unfold list_on_tree_state_fix in H.
  simpl in H; destruct H as [? ?].
  subst.
  unfold right_son_swap in H0; simpl in H0.
  destruct H0; subst.
  inversion H; [discriminate | ].
  inversion H1; subst v1 ls1 rs.
  inversion H6; [discriminate | ].
  inversion H4; subst v1 ls1 rs.
  pose proof list_swap_rela_rewrite l l' n (2 * n + 1) ltac:(lia) ltac:(lia) H0.
  subst l'.
  assert (Zlength (list_swap l n (2 * n + 1)) = Zlength l). {
    rewrite list_swap_Zlength by lia; lia.
  }
  assert (Zlength (upd_Znth (2 * n + 1) l (Znth n l)) = Zlength l). {
    rewrite upd_Znth_Zlength; lia.
  }
  assert (Zlength (upd_Znth (n * 2 + 1) l (Znth n l)) = Zlength l). {
    rewrite upd_Znth_Zlength; lia.
  }
  unfold list_on_tree_state.
  unfold list_on_tree_state_fix.
  simpl; split.
  + eapply list_nth_on_tree_Node; eauto.
    - lia.
    - unfold list_swap.
      rewrite upd_Znth_diff by lia.
      rewrite upd_Znth_same by lia; reflexivity.
    - unfold list_swap.
      apply list_nth_on_tree_upd; [ | lia | ].
      * apply list_nth_on_tree_upd; [ | lia | ].
        ++ replace (2 * n) with (n * 2) by lia; assumption.
        ++ apply less_is_not_child_index; lia.
      * apply less_is_not_child_index; lia.
    - unfold list_swap.
      apply list_nth_on_tree_upd; [ | lia | ].
      * apply list_nth_on_tree_upd; [ | lia | ].
        ++ replace (2 * n) with (n * 2) by lia; assumption.
        ++ apply less_is_not_child_index; lia.
      * apply less_is_not_child_index; lia.
  + assert ((n * 2 + 1) / 2 = n). {
      pose proof Z.div_lt_upper_bound (n * 2 + 1) 2 (n + 1) ltac:(lia) ltac:(lia).
      pose proof Z.div_le_lower_bound (n * 2 + 1) 2 n ltac:(lia) ltac:(lia).
      lia.
    }
    eapply cons_partial_tree; eauto; simpl.
    - lia.
    - replace (2 * n) with (n * 2) by lia; lia.
    - replace (2 * n) with (n * 2) by lia. rewrite H15.
      unfold list_swap.
      rewrite upd_Znth_same by lia; reflexivity.
    - unfold list_swap.
      apply list_nth_on_tree_upd; [ | lia | ].
      * apply list_nth_on_tree_upd; [ | lia | ].
        ++ replace (2 * n + 1 + -1) with (n * 2) by lia; assumption.
        ++ apply rchild_is_not_lchild with (pp := n); try lia.
           apply is_child_index_self; lia.
      * apply less_is_not_child_index; lia.
    - replace (2 * n) with (n * 2) by lia; rewrite H15.
      apply list_on_partial_tree_upd; try lia.
      * apply is_child_index_self; reflexivity.
      * apply list_on_partial_tree_upd; try lia.
        ++ apply is_child_index_gp_inv_right; [lia | ].
           apply is_child_index_self; reflexivity.
        ++ assumption.
Qed.

Lemma MaxHeap_no_rt_impl_lchild: forall v ls rs,
  MaxHeap_no_rt (Node v ls rs) -> MaxHeap ls.
Proof.
  intros.
  unfold MaxHeap_no_rt in H.
  destruct H as [v0 [ls0 [rs0 [? [? ?] ]] ] ].
  inversion H; subst.
  tauto.
Qed.
Lemma MaxHeap_no_rt_impl_rchild: forall v ls rs,
  MaxHeap_no_rt (Node v ls rs) -> MaxHeap rs.
Proof.
  intros.
  unfold MaxHeap_no_rt in H.
  destruct H as [v0 [ls0 [rs0 [? [? ?] ]] ] ].
  inversion H; subst.
  tauto.
Qed.
Lemma MaxHeap_impl_MaxHeap_no_rt: forall v v0 ls rs, 
  MaxHeap (Node v ls rs) -> MaxHeap_no_rt (Node v0 ls rs).
Proof.
  intros.
  inversion H; [discriminate | ].
  inversion H0; subst.
  unfold MaxHeap_no_rt.
  exists v0, ls0, rs0.
  tauto.
Qed.

Lemma not_inequal_impl_equal: forall {A: Type} (a b: A),
  ~ a <> b -> a = b.
Proof.
  intros.
  destruct (classic (a = b)); [assumption | ].
  unfold not in H at 1.
  apply H in H0.
  contradiction.
Qed.

Lemma MaxHeap_tree_down_hold_left: forall pt v ls rs v0 ls0 rs0,
  MaxHeap_tree_down (pt, Node v ls rs) ->
  ls = Node v0 ls0 rs0 ->
  v0 >= v ->
  (~ right_son_check_tree v ls rs \/ get_tree_val rs <= v0) ->
  MaxHeap_tree_down ((false, v0, rs) :: pt, Node v ls0 rs0).
Proof.
  intros.
  unfold MaxHeap_tree_down in H; simpl in H.
  destruct H as [? [? [? [? [? [? [? ?] ] ] ] ] ] ].
  inversion H4; subst x x0 x1 ls.
  unfold MaxHeap_tree_down; simpl.
  unfold get_tree_val in H5; simpl in H5.
  destruct H5; [discriminate | ].
  unfold right_son_check_tree in H2.
  split; [ | split].
  - eapply MaxHeap_partial_tree_v_app; eauto.
    * eapply MaxHeap_no_rt_impl_rchild; eauto.
    * destruct rs; [tauto | right].
      unfold get_tree_val.
      destruct H2.
      ++ apply not_and_or in H2.
         destruct H2; [apply not_inequal_impl_equal in H2; discriminate | ].
         unfold get_tree_val in H2; lia.
      ++ unfold get_tree_val in H2; lia. 
    * lia.
  - pose proof MaxHeap_no_rt_impl_lchild _ _ _ H3.
    eapply MaxHeap_impl_MaxHeap_no_rt; eauto.
  - exists v, ls0, rs0.
    split; [reflexivity | split].
    * destruct ls0; [tauto | right].
      unfold get_tree_val.
      eapply MaxHeap_partial_tree_v_app; eauto.
      ++ eapply MaxHeap_no_rt_impl_rchild; eauto.
      ++ destruct H2; [ | tauto].
         apply not_and_or in H2.
         destruct H2; [left; apply not_inequal_impl_equal; tauto | right; lia].
      ++ pose proof MaxHeap_no_rt_impl_lchild _ _ _ H3.
         inversion H5; [discriminate | ].
         inversion H7; subst v2 ls rs1.
         destruct H10; [discriminate | ].
         unfold get_tree_val in H10; lia.
    * destruct rs0; [tauto | right].
      unfold get_tree_val.
      eapply MaxHeap_partial_tree_v_app; eauto.
      ++ eapply MaxHeap_no_rt_impl_rchild; eauto.
      ++ destruct H2; [ | tauto].
         apply not_and_or in H2.
         destruct H2; [left; apply not_inequal_impl_equal; tauto | right; lia].
      ++ pose proof MaxHeap_no_rt_impl_lchild _ _ _ H3.
         inversion H5; [discriminate | ].
         inversion H7. subst v2 ls rs0.
         destruct H11; [discriminate | ].
         unfold get_tree_val in H11; lia. 
Qed.

Lemma MaxHeap_tree_down_hold_right: forall pt v ls rs v0 ls0 rs0,
  MaxHeap_tree_down (pt, Node v ls rs) ->
  rs = Node v0 ls0 rs0 ->
  v0 >= v ->
  (~ left_son_check_tree v ls rs \/ get_tree_val ls <= v0) ->
  MaxHeap_tree_down ((true, v0, ls) :: pt, Node v ls0 rs0).
Proof.
  intros.
  unfold MaxHeap_tree_down in H; simpl in H.
  destruct H as [? [? [? [? [? [? [? ?] ] ] ] ] ] ].
  inversion H4. subst x x0 x1 rs.
  unfold MaxHeap_tree_down; simpl.
  unfold get_tree_val in H6; simpl in H6.
  destruct H6; [discriminate | ].
  unfold left_son_check_tree in H2.
  split; [ | split].
  - eapply MaxHeap_partial_tree_v_app; eauto.
    * eapply MaxHeap_no_rt_impl_lchild; eauto.
    * destruct ls; [tauto | right].
      unfold get_tree_val.
      destruct H2.
      ++ apply not_and_or in H2.
         destruct H2; [apply not_inequal_impl_equal in H2; discriminate | ].
         unfold get_tree_val in H2; lia.
      ++ unfold get_tree_val in H2; lia. 
    * lia.
  - pose proof MaxHeap_no_rt_impl_rchild _ _ _ H3.
    eapply MaxHeap_impl_MaxHeap_no_rt; eauto.
  - exists v, ls0, rs0.
    split; [reflexivity | split].
    * destruct ls0; [tauto | right].
      unfold get_tree_val.
      eapply MaxHeap_partial_tree_v_app; eauto.
      ++ eapply MaxHeap_no_rt_impl_lchild; eauto.
      ++ destruct H2; [ | tauto].
         apply not_and_or in H2.
         destruct H2; [left; apply not_inequal_impl_equal; tauto | right; lia].
      ++ pose proof MaxHeap_no_rt_impl_rchild _ _ _ H3.
         inversion H6; [discriminate | ].
         inversion H7. subst v2 ls0 rs.
         destruct H10; [discriminate | ].
         unfold get_tree_val in H10; lia.
    * destruct rs0; [tauto | right].
      unfold get_tree_val.
      eapply MaxHeap_partial_tree_v_app; eauto.
      ++ eapply MaxHeap_no_rt_impl_lchild; eauto.
      ++ destruct H2; [ | tauto].
         apply not_and_or in H2.
         destruct H2; [left; apply not_inequal_impl_equal; tauto | right; lia].
      ++ pose proof MaxHeap_no_rt_impl_rchild _ _ _ H3.
         inversion H6; [discriminate | ].
         inversion H7. subst v2 ls1 rs.
         destruct H11; [discriminate | ].
         unfold get_tree_val in H11; lia. 
Qed.

Lemma Down_tree_list_succeed: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> list_down_succeed l l' -> MaxHeap_tree_down t ->
  exists t', tree_down_succeed t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_down t'.
Proof.
  intros.
  unfold list_down_succeed in H0.
  remember H1 as H1'; clear HeqH1'.
  unfold MaxHeap_tree_down in H1.
  destruct H1 as [? [? ?] ].
  destruct H3 as [v [ls [rs ?]]].
  destruct t as [pt tr].
  destruct l as [l n].
  destruct l' as [l' n'].
  simpl in H3; simpl in H2; simpl in H1.
  destruct H3 as [? [? ?] ]; subst.
  remember H as H'; clear HeqH'.
  unfold list_on_tree_state in H.
  unfold list_on_tree_state_fix in H.
  simpl in H; destruct H as [? ?].
  inversion H; [discriminate | ].
  inversion H6; subst v0 ls0 rs0.
  destruct H0; [ | destruct H0].
  {
    destruct H0 as [? [? ?] ].
    remember H0 as H0'; clear HeqH0'.
    unfold left_son_check_list in H0.
    unfold left_son in H0; simpl in H0.
    destruct H0.
    remember H8 as H8'; clear HeqH8'.
    apply not_and_or in H8.
    unfold legal_list_state in H0; simpl in H0.
    inversion H9; [lia | ].
    rewrite H14 in H4.
    destruct H4; [discriminate | unfold get_tree_val in H4].
    exists ((false, v0, rs) :: pt, Node v ls0 rs0).
    split; [| split].
    + unfold tree_down_succeed.
      exists (false, v0, rs); simpl.
      split; [reflexivity | ].
      exists v, ls, rs.
      split; [rewrite <- H12; reflexivity | ].
      left; split; [| split].
      - eapply left_son_check_equal; eauto.
      - rewrite <- right_son_check_equal; eauto.
      - unfold swap_down_left.
        exists v0, ls0, rs0; tauto.
    + eapply swap_down_left_hold; eauto.
    + eapply MaxHeap_tree_down_hold_left; eauto.
      - unfold get_list_val in H13; simpl in H13.
        replace (2 * n) with (n * 2) in H13 by lia; lia.
      - rewrite <- right_son_check_equal; eauto.
  } {
    destruct H0 as [? [? ?] ].
    remember H0 as H0'; clear HeqH0'.
    remember H8 as H8'; clear HeqH8'.
    unfold left_son_check_list in H0.
    unfold left_son in H0; simpl in H0.
    unfold right_son_check_list in H8.
    unfold right_son in H8; simpl in H8.
    unfold left_son in H11; unfold right_son in H11; simpl in H11.
    destruct H0, H8.
    unfold legal_list_state in H8; simpl in H8.
    inversion H9; [lia | ].
    rewrite H15 in H4.
    destruct H4; [discriminate | unfold get_tree_val in H4].
    inversion H10; [lia | ].
    rewrite H20 in H5.
    destruct H5; [discriminate | unfold get_tree_val in H5].
    destruct H11; destruct H11 as [H11a H11b].
    + exists ((false, v0, rs) :: pt, Node v ls0 rs0).
      assert (get_tree_val rs <= get_tree_val ls). {
        rewrite H15, H20; unfold get_tree_val.
        unfold get_list_val in H11a; simpl in H11a.
        replace (2 * n) with (n * 2) in H11a by lia.
        lia.
      }
      split; [| split].
      - unfold tree_down_succeed.
        exists (false, v0, rs); simpl.
        split; [reflexivity | ].
        exists v, ls, rs.
        split; [rewrite <- H12; reflexivity | ].
        right. right.
        split; [| split].
        * eapply left_son_check_equal; eauto.
        * eapply right_son_check_equal; eauto.
        * right. split; [lia | ].
          unfold swap_down_left.
          exists v0, ls0, rs0; tauto.
      - eapply swap_down_left_hold; eauto.
      - eapply MaxHeap_tree_down_hold_left; eauto.
        * unfold get_list_val in H14; simpl in H14.
          replace (2 * n) with (n * 2) in H14 by lia.
          unfold get_list_val in H11a; simpl in H11a.
          replace (2 * n) with (n * 2) in H11a by lia.
          lia.
        * rewrite H15 in H11.
          unfold get_tree_val in H11 at 2.
          lia.
    + exists ((true, v1, ls) :: pt, Node v ls1 rs1).
      assert (get_tree_val rs > get_tree_val ls). {
        rewrite H15, H20; unfold get_tree_val.
        unfold get_list_val in H11a; simpl in H11a.
        replace (2 * n) with (n * 2) in H11a by lia.
        lia.
      }
      split; [| split].
      - unfold tree_down_succeed.
        exists (true, v1, ls); simpl.
        split; [reflexivity | ].
        exists v, ls, rs.
        split; [rewrite <- H12; reflexivity | ].
        right. right.
        split; [| split].
        * eapply left_son_check_equal; eauto.
        * eapply right_son_check_equal; eauto.
        * left. split; [lia | ].
          unfold swap_down_right.
          exists v1, ls1, rs1; tauto.
      - eapply swap_down_right_hold; eauto.
      - eapply MaxHeap_tree_down_hold_right; eauto.
        * unfold get_list_val in H14; simpl in H14.
          replace (2 * n) with (n * 2) in H14 by lia.
          unfold get_list_val in H11a; simpl in H11a.
          replace (2 * n) with (n * 2) in H11a by lia.
          lia.
        * rewrite H20 in H11.
          unfold get_tree_val in H11 at 1.
          lia.
  } {
    destruct H0 as [? [? ?] ].
    remember H0 as H0'; clear HeqH0'.
    remember H8 as H8'; clear HeqH8'.
    unfold right_son_check_list in H8.
    unfold right_son in H8; simpl in H8.
    destruct H8.
    apply not_and_or in H0.
    unfold legal_list_state in H8; simpl in H8.
    inversion H10; [lia | ].
    rewrite H14 in H5.
    destruct H5; [discriminate | unfold get_tree_val in H5].
    exists ((true, v0, ls) :: pt, Node v ls0 rs0).
    split; [| split].
    + unfold tree_down_succeed.
      exists (true, v0, ls); simpl.
      split; [reflexivity | ].
      exists v, ls, rs.
      split; [rewrite <- H12; reflexivity | ].
      right; left; split; [| split].
      - rewrite <- left_son_check_equal; eauto.
      - eapply right_son_check_equal; eauto.
      - unfold swap_down_right.
        exists v0, ls0, rs0; tauto.
    + eapply swap_down_right_hold; eauto.
    + eapply MaxHeap_tree_down_hold_right; eauto.
      - unfold get_list_val in H13; simpl in H13.
        replace (2 * n) with (n * 2) in H13 by lia; lia.
      - rewrite <- left_son_check_equal; eauto.
  }
Qed.

(* Lemma Down_tree_list_succeed_clos_refl_trans: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> (clos_refl_trans list_down_succeed) l l' -> MaxHeap_tree_up t ->
  exists t', (clos_refl_trans tree_up_succeed) t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_up t'.
Proof.
Admitted. *)

Lemma Down_tree_list_fail: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> list_down_fail l l ->
  tree_down_fail t t.
Proof.
  intros.
  unfold list_down_fail in H0.
  destruct l as [l n].
  destruct t as [pt tr].
  unfold tree_down_fail.
  revert H0; unfold_RELS_tac; intros; simpl.
  unfold list_on_tree_state in H.
  unfold list_on_tree_state_fix in H.
  simpl in H.
  destruct H.
  destruct H0 as [[? ?] ?]; clear H3.
  unfold left_son_check_list in H0.
  unfold left_son in H0; simpl in H0.
  apply not_and_or in H0.
  unfold right_son_check_list in H2.
  unfold right_son in H2; simpl in H2.
  apply not_and_or in H2.
  unfold legal_list_state in H0; simpl in H0.
  unfold legal_list_state in H2; simpl in H2.
  assert (n >= 1). {
    inversion H; lia.
  }
  destruct H2.
  + apply not_and_or in H2.
    destruct H2; [ | lia].
    destruct H0.
    - apply not_and_or in H0.
      destruct H0; [ | lia].
      inversion H1.
      * inversion H.
        
Admitted.

Lemma Down_fail_impl_MaxHeap: forall (t: tree_state),
  tree_down_fail t t -> MaxHeap_tree_down t -> MaxHeap (tree_compose (fst t) (snd t)).
Proof.
Admitted.

Lemma Down_tree_list_rel: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> heap_list_down l l' -> MaxHeap_tree_down t ->
  exists t', heap_tree_down t t' /\ list_on_tree_state l' t' /\ MaxHeap (tree_compose (fst t') (snd t')).
Proof.
Admitted.