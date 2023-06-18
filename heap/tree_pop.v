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
Require Import cprogs.heap.math_prop.

Fixpoint tree_to_partial_tree_pop_fix (tl: partial_tree) (t: tree) (d: Z): partial_tree :=
  match t with
    | Leaf => tl
    | Node v ls rs => 
      match (full_tree_b (d - 2) rs) with
      | false => tree_to_partial_tree_pop_fix ((true, v, ls) :: tl) rs (d-1)
      | true => tree_to_partial_tree_pop_fix ((false, v, rs) :: tl) ls (d-1)
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
  else (Node (get_last_val ( tree_to_partial_tree_pop rs (d-1)))
        ls (tree_compose (skipn 1%nat (tree_to_partial_tree_pop rs (d-1))) Leaf)).

Definition tree_pop: tree -> tree -> Prop :=
  fun t t' => (tree_size t <= 1  /\ t' = Leaf) \/ 
    (exists v ls rs ts d, t = (Node v ls rs) /\ complete_tree_pop d t /\ heap_tree_down (nil,(tree_cut_last ls rs d)) ts /\ t' = (tree_compose (fst ts) (snd ts))).

Lemma complete_tree_pop_not_fullb: forall d t,
  complete_tree_pop d t -> full_tree_b (d - 1) t = false.
Proof.
  intros.
  induction H; subst; simpl.
  + reflexivity.
  + apply andb_false_intro1; auto.
  + apply andb_false_intro2; auto.
Qed.

Fixpoint tree_last_pow2 (d: Z) (tr: tree): Z :=
  match tr with
    | Leaf => 1
    | Node v ls rs =>
      if (full_tree_b (d - 2) rs) then
        2 * (tree_last_pow2 (d - 1) ls)
      else
        2 * (tree_last_pow2 (d - 1) rs) 
  end.

Lemma last_index_lowbit: forall d n tr,
  complete_tree_pop d tr -> 
  last_index d n tr = n * (tree_last_pow2 d tr) / 2 + last_index d 0 tr.
Proof.
  intros.
  revert d n H.
  induction tr; simpl; intros.
  + rewrite Zdiv_0_l.
    replace (n * 1) with n by lia. 
    lia.
  + inversion H; subst; simpl.
    - rewrite full_tree_equiv1 in H4.
      rewrite H4.
      erewrite IHtr1; eauto.
      rewrite Z.mul_assoc.
      lia.
    - pose proof complete_tree_pop_not_fullb _ _ H4.
      replace (d - 1 - 1) with (d - 2) in H0 by lia.
      rewrite H0.
      erewrite IHtr2; eauto.
      rewrite Z.mul_assoc.
      specialize (IHtr2 _ 1 H4).
      rewrite IHtr2.
      destruct (classic (Zodd (tree_last_pow2 (d - 1) tr2))).
      * pose proof Zodd_2p_plus_1 n.
        replace (n * 2) with (2 * n) by lia. 
        pose proof Zodd_mult_Zodd _ _ H3 H1.
        pose proof Zodd_div2 _ H5.
        replace (2 * n * tree_last_pow2 (d - 1) tr2) with (n * tree_last_pow2 (d - 1) tr2 * 2) by lia.
        rewrite Z.div_mul by lia.
        assert (Zodd 1). {
          rewrite <- Zodd_bool_iff; auto.
        }
        pose proof Zodd_mult_Zodd _ _ H7 H1.
        pose proof Zodd_div2 _ H8.
        lia.
      * pose proof Zeven_odd_dec (tree_last_pow2 (d - 1) tr2).
        assert (Zeven (tree_last_pow2 (d - 1) tr2)). {
          destruct H3; auto.
          exfalso.
          auto.
        }
        pose proof Zeven_mult_Zeven_r (n * 2 + 1) _ H5.
        pose proof Zeven_div2 _ H6.
        replace (n * 2 * tree_last_pow2 (d - 1) tr2) with (n * tree_last_pow2 (d - 1) tr2 * 2) by lia.
        rewrite Z.div_mul by lia.
        replace (1 * tree_last_pow2 (d - 1) tr2) with (tree_last_pow2 (d - 1) tr2) by lia.
        pose proof Zeven_div2 _ H5.
        lia.
Qed.

Lemma tree_last_pow2_even: forall tr d,
  tr <> Leaf ->
  tree_last_pow2 d tr = 2 * (tree_last_pow2 d tr / 2).
Proof.
  intros tr.
  induction tr; simpl; intros; [contradiction |].
  destruct (full_tree_b (d - 2) tr2) eqn:?.
  + replace (2 * tree_last_pow2 (d - 1) tr1) with (tree_last_pow2 (d - 1) tr1 * 2) by lia.
    rewrite Z.div_mul by lia.
    lia.
  + replace (2 * tree_last_pow2 (d - 1) tr2) with (tree_last_pow2 (d - 1) tr2 * 2) by lia.
    rewrite Z.div_mul by lia.
    lia.
Qed.

Lemma full_tree_b_dep_restrict_less: forall tr d,
  full_tree_b d tr = true ->
  full_tree_b (d - 1) tr = false.
Proof.
  intros tr.
  induction tr; simpl; intros.
  + rewrite Z.eqb_neq; rewrite Z.eqb_eq in H; lia.
  + apply andb_prop in H; destruct H.
    specialize (IHtr1 _ H).
    apply andb_false_intro1; assumption. 
Qed.

Lemma full_tree_last_pow2: forall tr d,
  full_tree d tr -> tree_last_pow2 d tr = tree_size tr + 1.
Proof.
  intros.
  induction H; subst; simpl.
  + lia.
  + remember H0 as H0'; clear HeqH0'.
    rewrite full_tree_equiv1 in H0.
    apply full_tree_b_dep_restrict_less in H0.
    replace (dep - 1 - 1) with (dep - 2) in H0 by lia.
    rewrite H0.
    rewrite (full_tree_same_size _ _ _ H H0').
    lia.
Qed.

Lemma complete_tree_pop_nonneg: forall tr d,
  complete_tree_pop d tr -> 0 <= d.
Proof.
  intros.
  induction H; subst; simpl; lia.
Qed.

Lemma complete_tree_pop_last_pow2: forall tr d,
  complete_tree_pop d tr ->
  tree_last_pow2 d tr = 2 ^ d.
Proof.
  intros.
  induction H; subst; simpl.
  + reflexivity.
  + rewrite full_tree_equiv1 in H0.
    rewrite H0.
    rewrite IHcomplete_tree_pop; eauto.
    pose proof complete_tree_pop_nonneg _ _ H.
    replace dep with (dep - 1 + 1) at 2 by lia.
    rewrite Zpower_exp by lia.
    lia.
  + pose proof complete_tree_pop_not_fullb _ _ H0.
    replace (dep - 1 - 1) with (dep - 2) in H1 by lia.
    rewrite H1.
    rewrite IHcomplete_tree_pop; eauto.
    replace dep with (dep - 1 + 1) at 2 by lia.
    pose proof complete_tree_pop_nonneg _ _ H0.
    rewrite Zpower_exp by lia.
    lia. 
Qed.

Lemma tree_last_index_size: forall tr d,
  complete_tree_pop d tr -> 
  last_index d 1 tr = tree_size tr.
Proof.
  intros tr.
  induction tr; simpl; intros.
  + rewrite Z.div_1_l by lia; lia.
  + inversion H; subst.
    - rewrite full_tree_equiv1 in H4.
      rewrite H4.
      erewrite last_index_lowbit; eauto.
      specialize (IHtr1 _ H2).
      erewrite last_index_lowbit in IHtr1; eauto.
      destruct (classic (tr1 = Leaf)).
      * subst; simpl.
        inversion H2.
        rewrite <- full_tree_equiv1 in H4.
        pose proof full_tree_nonneg _ _ H4.
        lia.
      * replace (2 * tree_last_pow2 (d - 1) tr1) with (tree_last_pow2 (d - 1) tr1 * 2) by lia.
        rewrite Z.div_mul by lia.
        pose proof tree_last_pow2_even _ (d - 1) H0.
        pose proof complete_tree_pop_last_pow2 _ _ H2.
        rewrite <- full_tree_equiv1 in H4.
        pose proof full_tree_size _ _ H4.
        pose proof full_tree_nonneg _ _ H4.
        replace (d - 1) with (d - 2 + 1) in H3 by lia.
        rewrite Zpower_exp in H3 by lia.
        replace (d - 2 + 1) with (d - 1) in H3 by lia.
        rewrite H3, !H5; rewrite <- IHtr1.
        replace (2 ^ 1) with 2 by lia.
        replace (2 ^ 1) with 2 in H3 by lia. 
        rewrite H3. 
        rewrite Z.mul_assoc, Z.div_mul by lia.
        lia.
    - pose proof complete_tree_pop_not_fullb _ _ H4.
      replace (d - 1 - 1) with (d - 2) in H0 by lia.
      rewrite H0.
      erewrite last_index_lowbit; eauto.
      specialize (IHtr2 _ H4).
      erewrite last_index_lowbit in IHtr2; eauto.
      destruct (classic (tr2 = Leaf)).
      * subst; simpl.
        inversion H4.
        inversion H2; subst; simpl; auto.
        pose proof full_tree_nonneg _ _ H5; lia.
      * pose proof tree_last_pow2_even _ (d - 1) H1.
        rewrite <- IHtr2.
        pose proof full_tree_size _ _ H2; rewrite H5.
        pose proof complete_tree_pop_last_pow2 _ _ H4.
        rewrite H6.
        rewrite H6 in H3.
        replace (2 * (2 ^ (d - 1) / 2)) with ((2 ^ (d - 1) / 2) * 2) in H3 by lia.
        rewrite H3, !Z.mul_assoc, !Z.div_mul by lia.
        lia.
Qed.

Lemma list_on_tree_last_val: forall l pt tr d n,
  Zlength l > 2 -> list_on_tree_state (l, n) (pt, tr) ->
  complete_tree_pop d tr ->
  get_last_val (tree_to_partial_tree_pop_fix pt tr d) = Znth (last_index d n tr) l.
Proof.
  intros.
  revert l pt n d H H0 H1.
  induction tr; simpl; intros.
  + unfold list_on_tree_state in H0; simpl in H0.
    unfold list_on_tree_state_fix in H0; simpl in H0.
    destruct H0 as [? [? [? [? ?]]]].
    inversion H2; subst; simpl.
    - simpl in H3; lia.
    - reflexivity.
  + unfold list_on_tree_state in H0; simpl in H0.
    unfold list_on_tree_state_fix in H0; simpl in H0.
    destruct H0 as [? [? [? [d' ?]]]].
    inversion H1; subst; simpl.
    - rewrite full_tree_equiv1 in H9.
      rewrite H9.
      apply IHtr1; [lia | | auto].
      unfold list_on_tree_state; simpl.
      unfold list_on_tree_state_fix; simpl.
      inversion H0; subst.
      split; [ | split; [ | split]].
      * auto.
      * eapply cons_partial_tree; eauto; simpl; rewrite Z.div_mul by lia;
          [lia | lia | auto | auto].
      * auto.
      * exists d'; auto.
    - pose proof complete_tree_pop_not_fullb _ _ H9.
      replace (d - 1 - 1) with (d - 2) in H5 by lia.
      rewrite H5.
      apply IHtr2; [lia | | auto].
      unfold list_on_tree_state; simpl.
      unfold list_on_tree_state_fix; simpl.
      inversion H0; subst.
      split; [ | split; [ | split]].
      * auto.
      * pose proof Odd_Div2 n ltac:(lia).
        eapply cons_partial_tree; eauto; simpl;
          try rewrite H6; try lia; auto.
        replace (n * 2 + 1 + -1) with (n * 2) by lia.
        auto.
      * auto.
      * exists d'; auto.   
Qed.

Lemma complete_tree_pop_not_leaf: forall d t,
  d >= 1 -> complete_tree_pop d t -> t <> Leaf.
Proof.
  intros.
  induction H0; subst; simpl.
  + lia.
  + unfold not; intros; discriminate.
  + unfold not; intros; discriminate.
Qed.

Lemma full_tree_not_leaf: forall d t,
  d >= 1 -> full_tree_b d t = true -> t <> Leaf.
Proof.
  intros.
  revert d H H0; induction t; simpl; intros.
  + rewrite Z.eqb_eq in H0; lia.
  + unfold not; intros; discriminate. 
Qed.

Lemma get_last_val_coincidence: forall d tr pt1 pt2,
  complete_tree_pop d tr ->
  tr <> Leaf ->
  get_last_val (tree_to_partial_tree_pop_fix pt1 tr d) =
  get_last_val (tree_to_partial_tree_pop_fix pt2 tr d).
Proof.
  intros.
  revert d pt1 pt2 H.
  induction tr; simpl; intros; [contradiction |].
  inversion H; subst; simpl.
  + rewrite full_tree_equiv1 in H5.
    rewrite H5.
    apply IHtr1; auto.
    eapply complete_tree_pop_not_leaf; eauto.
    rewrite <- full_tree_equiv1 in H5.
    pose proof full_tree_nonneg _ _ H5.
    lia.
  + pose proof complete_tree_pop_not_fullb _ _ H5.
    replace (d - 1 - 1) with (d - 2) in H1 by lia.
    rewrite H1.
    destruct (classic (tr2 = Leaf)).
    1: { subst; simpl; auto. }
    apply IHtr2; auto.
Qed.

Lemma list_on_tree_impl_state: forall (l: list Z) (ls rs: tree) (v: Z),
  Zlength l > 2 -> list_on_tree l (Node v ls rs) ->
  exists d, list_on_tree_state (firstn (Z.to_nat (Zlength l - 1)) (upd_Znth 1 l (Znth (Zlength l - 1) l)), 1) (nil, tree_cut_last ls rs d) /\  complete_tree_pop d (Node v ls rs).
Proof.
  intros.
  unfold list_on_tree in H0.
  destruct H0 as [? [? ?]].
  rewrite <- complete_tree_equality in H2.
  destruct H2 as [d].
  exists d; split; [| auto].
  unfold list_on_tree_state; simpl.
  unfold list_on_tree_state_fix.
  simpl.
  split; [| split; [| split]].
  2: {
    apply nil_partial_tree; tauto.
  }
  1: {
    unfold tree_cut_last.
    inversion H2; subst.
    + rewrite full_tree_equiv1 in H7.
      rewrite H7.
      apply list_nth_on_tree_Node.
      - rewrite Zlength_firstn.
        rewrite upd_Znth_Zlength by lia.
        lia.
      - rewrite Znth_firstn by lia.
        rewrite upd_Znth_same by lia.
        unfold tree_to_partial_tree_pop.
        assert (Zlength l - 1 = last_index d 1 (Node v ls rs)). {
          rewrite tree_last_index_size by auto; lia.
        }
        assert (ls <> Leaf). {
          rewrite <- full_tree_equiv1 in H7.
          pose proof full_tree_nonneg _ _ H7.
          eapply complete_tree_pop_not_leaf; eauto; lia.
        }
        rewrite get_last_val_coincidence with (pt2 := (false, v, rs) :: nil); auto.
        replace (tree_to_partial_tree_pop_fix [(false, v, rs)] ls (d - 1)) with (tree_to_partial_tree_pop_fix nil (Node v ls rs) d).
        2: { simpl; rewrite H7; auto. }
        erewrite list_on_tree_last_val; eauto.
        * rewrite H3.
          reflexivity.
        * unfold list_on_tree_state; simpl.
          unfold list_on_tree_state_fix; simpl.
          split; [ | split; [ | split]].
          -- auto.
          -- apply nil_partial_tree; auto.
          -- simpl in H1; lia. 
          -- apply complete_tree_equality.
             exists d; auto.
      - admit.
      - admit.
    + pose proof complete_tree_pop_not_fullb _ _ H7.
      replace (d - 1 - 1) with (d - 2) in H3 by lia.
      rewrite H3.
      apply list_nth_on_tree_Node.
      - rewrite Zlength_firstn.
        rewrite upd_Znth_Zlength by lia.
        lia.
      - rewrite Znth_firstn by lia.
        rewrite upd_Znth_same by lia.
        unfold tree_to_partial_tree_pop.
        assert (rs <> Leaf). {
          destruct (classic (ls = Leaf)).
          + inversion H5; [ | rewrite H4 in H9; discriminate].
            inversion H7.
            2: { pose proof full_tree_nonneg _ _ H10; lia. }
            2: { pose proof full_tree_nonneg _ _ H9; lia. }
            subst.
            simpl in H1; lia.
        }
        assert (Zlength l - 1 = last_index d 1 (Node v ls rs)). {
          rewrite tree_last_index_size by auto; lia.
        }
        rewrite get_last_val_coincidence with (pt2 := (true, v, ls) :: nil); auto.
        replace (get_last_val (tree_to_partial_tree_pop_fix [(true, v, ls)] rs (d - 1))) with (get_last_val (tree_to_partial_tree_pop_fix nil (Node v ls rs) d)).
        2: { simpl; rewrite H3. auto. }
        erewrite list_on_tree_last_val; eauto.
        * rewrite H6.
          reflexivity.
        * unfold list_on_tree_state; simpl.
          unfold list_on_tree_state_fix; simpl.
          split; [ | split; [ | split]].
          -- auto.
          -- apply nil_partial_tree; auto.
          -- simpl in H1; lia. 
          -- apply complete_tree_equality.
             exists d; auto.
      - admit.
      - admit. 
  } 
  
Admitted.

Lemma tree_not_emp: forall (t: tree),
  tree_size t >= 1 -> exists v ls rs, t = Node v ls rs.
Proof.
  intros.
  destruct t.
  + simpl in H; lia. 
  + exists v, t1, t2; reflexivity. 
Qed.

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