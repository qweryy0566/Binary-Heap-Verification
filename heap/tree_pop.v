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
Require Import cprogs.heap.tree_push.

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
    | (flg, v, tr) :: lt => v
  end.

Definition tree_cut_last(ls rs: tree) (d: Z): tree :=
  if (full_tree_b (d - 2) rs) then
    (Node (get_last_val (tree_to_partial_tree_pop ls (d-1)))
        (tree_compose (skipn 1%nat (tree_to_partial_tree_pop ls (d-1))) Leaf) rs)
  else (Node (get_last_val (tree_to_partial_tree_pop rs (d-1)))
        ls (tree_compose (skipn 1%nat (tree_to_partial_tree_pop rs (d-1))) Leaf)).

Definition tree_pop: tree -> tree -> Prop :=
  fun t t' => (tree_size t <= 1  /\ t' = Leaf) \/
    (tree_size t >= 2 /\ exists v ls rs ts d, t = (Node v ls rs) /\ complete_tree_pop d t /\ heap_tree_down (nil,(tree_cut_last ls rs d)) ts /\ t' = (tree_compose (fst ts) (snd ts))).

Lemma tree_not_emp: forall (t: tree),
  tree_size t >= 1 -> exists v ls rs, t = Node v ls rs.
Proof.
  intros.
  induction t; simpl in *; try lia.
  exists v, t1, t2; auto.
Qed.

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

Lemma MaxHeap_tree_partial_tree_skip: forall (lt: partial_tree),
  MaxHeap_partial_tree lt -> MaxHeap_partial_tree (skipn 1 lt).
Proof.
  intros.
  induction lt.
  + simpl; tauto.
  + destruct a as [[flg val] tr].
    inversion H.
    simpl.
    apply (MaxHeap_partial_tree_v_impl _ val).
    tauto.
Qed.

Lemma tree_to_partial_tree_pop_get: forall (t tr: tree) (lt: partial_tree) (flg: bool) (v d: Z), 
  tree_to_partial_tree_pop_fix (lt ++ [(flg,v,tr)]) t d = (tree_to_partial_tree_pop_fix lt t d) ++ [(flg,v,tr)].
Proof.
  intros.
  revert v tr flg d lt.
  induction t; intros.
  + unfold tree_to_partial_tree_pop_fix; tauto.
  + simpl.
    destruct (full_tree_b (d - 2) t2).
    - replace ((false, v, t2) :: (lt ++ [(flg, v0, tr)])) with ([(false, v, t2)] ++ (lt ++ [(flg, v0, tr)])) by reflexivity.
      replace ((false, v, t2) :: lt) with ([(false, v, t2)] ++ lt) by reflexivity.
      rewrite app_assoc.
      apply IHt1.
    - replace ((true, v, t1) :: (lt ++ [(flg, v0, tr)])) with ([(true, v, t1)] ++ (lt ++ [(flg, v0, tr)])) by reflexivity.
      replace ((true, v, t1) :: lt) with ([(true, v, t1)] ++ lt) by reflexivity.
      rewrite app_assoc.
      apply IHt2.
Qed.

Lemma MaxHeap_tree_partial_hold: forall (t: tree) (d: Z) (lt: partial_tree),
  complete_tree_pop d t -> MaxHeap t -> (t = Leaf \/ MaxHeap_partial_tree_v lt (get_tree_val t)) -> MaxHeap_partial_tree lt -> 
  MaxHeap_partial_tree (tree_to_partial_tree_pop_fix lt t d).
Proof.
  intros.
  revert lt d H H2 H1.
  induction H0; intros; subst.
  + simpl; tauto.
  + simpl; inversion H2; subst.
    - apply full_tree_equiv1 in H8.
      rewrite H8.
      destruct H4; [discriminate|unfold get_tree_val in H].
      apply IHMaxHeap1; [tauto| | ].
      * unfold MaxHeap_partial_tree; tauto.
      * destruct H0; [left; tauto|right].
        eapply MaxHeap_partial_tree_v_app; try reflexivity; try tauto.
    - pose proof complete_tree_pop_not_fullb _ _ H8.
      replace (d-1-1) with (d-2) in H by lia.
      rewrite H.
      destruct H4; [discriminate|unfold get_tree_val in H4].
      apply IHMaxHeap2; [tauto| | ].
      * unfold MaxHeap_partial_tree; tauto.
      * destruct H1; [left; tauto|right].
        eapply MaxHeap_partial_tree_v_app; try reflexivity; try tauto.
Qed.

Lemma tree_to_partial_tree_len: forall (t: tree) (d: Z),
  t <> Leaf -> 1 <= Zlength (tree_to_partial_tree_pop t d).
Proof.
  intros.
  revert d.
  induction t; [tauto|].
  intros.
  unfold tree_to_partial_tree_pop; simpl.
  destruct (full_tree_b (d-2) t2); simpl.
  + replace ((false, v, t2) :: nil) with (nil ++ [(false, v, t2)]); [|rewrite app_nil_l; tauto].
    rewrite tree_to_partial_tree_pop_get.
    rewrite Zlength_app.
    replace (Zlength [(false, v, t2)]) with 1 by tauto.
    pose proof initial_world.zlength_nonneg _ (tree_to_partial_tree_pop_fix [] t1 (d - 1)).
    lia.
  + replace ((true, v, t1) :: nil) with (nil ++ [(true, v, t1)]); [|rewrite app_nil_l; tauto].
    rewrite tree_to_partial_tree_pop_get.
    rewrite Zlength_app.
    replace (Zlength [(true, v, t1)]) with 1 by tauto.
    pose proof initial_world.zlength_nonneg _ (tree_to_partial_tree_pop_fix [] t2 (d - 1)).
    lia.
Qed.

Lemma full_tree_gt_0: forall (t: tree) (d: Z),
  full_tree d t -> d >= 0.
Proof.
  intros.
  induction H.
  + lia.
  + lia.
Qed.

Lemma tree_compose_size_pop: forall (t: tree) (d: Z),
  complete_tree_pop d t -> t <> Leaf -> tree_size
  (tree_compose (skipn 1 (tree_to_partial_tree_pop t d)) Leaf) + 1 = tree_size t.
Proof.
  intros.
  revert d H.
  induction t; intros; [tauto|].
  unfold tree_to_partial_tree_pop.
  inversion H; subst.
  + apply full_tree_equiv1 in H5.
    unfold tree_to_partial_tree_pop_fix; fold tree_to_partial_tree_pop_fix.
    rewrite H5.
    destruct t1.
    - inversion H3.
      replace (d-2) with (-1) in H5 by lia.
      apply full_tree_equiv1 in H5.
      pose proof full_tree_gt_0 _ _ H5.
      lia. 
    - replace ((false, v, t2) :: nil) with (nil ++ [(false, v, t2)]); [|rewrite app_nil_l; tauto].
      rewrite tree_to_partial_tree_pop_get.
      replace 1%nat with (Z.to_nat 1) by lia.
      pose proof tree_to_partial_tree_len (Node v0 t1_1 t1_2) (d-1).
      unfold tree_to_partial_tree_pop in H1.
      rewrite Zskipn_app1; [|apply H1; discriminate].
      rewrite tree_compose_append.
      unfold tree_size; fold tree_size.
      unfold tree_to_partial_tree_pop in IHt1.
      replace (Z.to_nat 1) with 1%nat by lia.
      specialize (IHt1 ltac:(discriminate) (d-1) H3).
      replace (tree_size (tree_compose (skipn 1 (tree_to_partial_tree_pop_fix [] (Node v0 t1_1 t1_2) (d - 1))) Leaf)) with (tree_size (Node v0 t1_1 t1_2) - 1) by lia.
      simpl; lia.
  + pose proof complete_tree_pop_not_fullb _ _ H5.
    unfold tree_to_partial_tree_pop_fix; fold tree_to_partial_tree_pop_fix.
    replace (d-1-1) with (d-2) in H1 by lia.
    rewrite H1.
    destruct t2.
    - simpl.
      inversion H3; [simpl; tauto|].
      inversion H5.
      replace (d-1-1) with (-1) in H2 by lia.
      pose proof full_tree_gt_0 _ _ H2; lia.
    - replace ((true, v, t1) :: nil) with (nil ++ [(true, v, t1)]); [|  rewrite app_nil_l; tauto].
      rewrite tree_to_partial_tree_pop_get.
      replace 1%nat with (Z.to_nat 1) by lia.
      pose proof tree_to_partial_tree_len (Node v0 t2_1 t2_2) (d-1).
      unfold tree_to_partial_tree_pop in H2.
      rewrite Zskipn_app1; [|apply H2; discriminate].
      rewrite tree_compose_append.
      unfold tree_size; fold tree_size.
      unfold tree_to_partial_tree_pop in IHt2.
      replace (Z.to_nat 1) with 1%nat by lia.
      specialize (IHt2 ltac:(discriminate) (d-1) H5).
      replace (tree_size (tree_compose (skipn 1 (tree_to_partial_tree_pop_fix [] (Node v0 t2_1 t2_2) (d - 1))) Leaf)) with (tree_size (Node v0 t2_1 t2_2) - 1) by lia.
      simpl; lia.
Qed.

Lemma tree_cut_last_size: forall (ls rs: tree) (v d: Z),
  tree_size (Node v ls rs) >= 2 -> complete_tree_pop d (Node v ls rs) -> tree_size (tree_cut_last ls rs d) = tree_size ls + tree_size rs.
Proof.
  intros.
  unfold tree_cut_last.
  inversion H0; subst. 
  + apply full_tree_equiv1 in H5; rewrite H5.
    unfold tree_size; fold tree_size.
    inversion H3.
    - replace (d-2) with (-1) in H5 by lia; apply full_tree_equiv1 in H5.
      pose proof full_tree_gt_0 _ _ H5; lia.
    - assert (ls <> Leaf); [rewrite <- H4;discriminate|].
      pose proof tree_compose_size_pop _ _ H3 H6.
      rewrite <- H4 in H7.
      replace (tree_size (tree_compose (skipn 1 (tree_to_partial_tree_pop (Node v0 ls0 rs0) (d - 1))) Leaf)) with (tree_size (Node v0 ls0 rs0) - 1) by lia.
      lia.
    - assert (ls <> Leaf); [rewrite <- H4;discriminate|].
      pose proof tree_compose_size_pop _ _ H3 H6.
      rewrite <- H4 in H7.
      replace (tree_size (tree_compose (skipn 1 (tree_to_partial_tree_pop (Node v0 ls0 rs0) (d - 1))) Leaf)) with (tree_size (Node v0 ls0 rs0) - 1) by lia.
      lia.
  + pose proof complete_tree_pop_not_fullb _ _ H5.
    replace (d-1-1) with (d-2) in H1 by lia; rewrite H1.
    unfold tree_size; fold tree_size.
    inversion H5.
    - rewrite H2 in H3; inversion H3.
      assert (tree_size (Node v ls rs) = 1); [simpl;rewrite <- H4; rewrite <- H7; tauto | ].
      lia.
      pose proof full_tree_gt_0 _ _ H6; lia.
    - assert (rs <> Leaf); [rewrite <- H6;discriminate|].
      pose proof tree_compose_size_pop _ _ H5 H7.
      rewrite <- H6 in H8.
      replace (tree_size (tree_compose (skipn 1 (tree_to_partial_tree_pop (Node v0 ls0 rs0) (d - 1))) Leaf)) with (tree_size (Node v0 ls0 rs0) - 1) by lia.
      lia.
    - assert (rs <> Leaf); [rewrite <- H6;discriminate|].
      pose proof tree_compose_size_pop _ _ H5 H7.
      rewrite <- H6 in H8.
      replace (tree_size (tree_compose (skipn 1 (tree_to_partial_tree_pop (Node v0 ls0 rs0) (d - 1))) Leaf)) with (tree_size (Node v0 ls0 rs0) - 1) by lia.
      lia.
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

Lemma list_nth_on_tree_decompose: forall l pt tr p n,
  list_nth_on_tree l p tr ->
  list_nth_on_partial_tree l n p pt ->
  list_nth_on_tree l n (tree_compose pt tr).
Proof.
  intros.
  revert l tr p n H H0.
  induction pt; simpl; intros.
  + inversion H0; [subst; auto | discriminate].
  + inversion H0; [discriminate | subst].
    injection H1; intros; subst.
    destruct flg.
    - eapply IHpt; [ | apply H6].
      apply list_nth_on_tree_Node; try lia.
      * replace (p / 2 * 2) with (p + -1) by lia; auto.
      * rewrite <- H3; auto.
    - eapply IHpt; [ | apply H6].
      apply list_nth_on_tree_Node; try lia.
      * replace (p / 2 * 2) with p by lia; auto.
      * replace (p / 2 * 2) with p by lia; auto.
Qed.

Lemma list_nth_on_tree_update_less: forall l tr p n v,
  list_nth_on_tree l p tr ->
  0 <= n < p ->
  list_nth_on_tree (upd_Znth n l v) p tr.
Proof.
  intros.
  revert n v H0.
  induction H; simpl; intros.
  + apply list_nth_on_tree_Leaf.
  + apply list_nth_on_tree_Node.
    - rewrite upd_Znth_Zlength by lia; lia.
    - rewrite upd_Znth_diff by lia; auto.
    - apply IHlist_nth_on_tree1; lia.
    - apply IHlist_nth_on_tree2; lia.  
Qed.

Lemma list_nth_on_partial_tree_update: forall l pt p n upd_pos v,
  list_nth_on_partial_tree l n p pt ->
  0 <= upd_pos < Zlength l -> upd_pos < n ->
  list_nth_on_partial_tree (upd_Znth upd_pos l v) n p pt.
Proof.
  intros.
  revert upd_pos v H0 H1.
  induction H; simpl; subst; intros.
  + apply nth_partial_tree_nil; auto.
  + pose proof list_nth_on_partial_tree_no_less _ _ _ _ H4.
    eapply nth_partial_tree_cons; eauto.
    - rewrite upd_Znth_Zlength by lia.
      lia. 
    - rewrite upd_Znth_diff by lia; auto.
    - apply list_nth_on_tree_update_less.
      * auto.
      * destruct flg; lia.
Qed.

Lemma list_nth_on_tree_impl_leaf: forall l tr p,
  list_nth_on_tree l p tr ->
  p >= Zlength l ->
  tr = Leaf.
Proof.
  intros.
  inversion H; [auto | lia].
Qed.


Lemma list_nth_on_tree_coin: forall tr l n len d,
  complete_tree_pop d tr ->
  list_nth_on_tree l n tr ->
  len >= last_index d n tr ->
  n < len <= Zlength l ->
  list_nth_on_tree (firstn (Z.to_nat len) l) n tr.
Proof.
  intros tr.
  induction tr; simpl; intros.
  + apply list_nth_on_tree_Leaf.
  + inversion H; subst.
    - rewrite full_tree_equiv1 in H7.
      rewrite H7 in H1.
      inversion H0; subst.
      apply list_nth_on_tree_Node.
      * rewrite Zlength_firstn; lia.
      * rewrite Znth_firstn; [auto | lia].
      * assert (n * 2 >= len \/ n * 2 < len) by lia.
        destruct H3.
        ++ pose proof list_nth_on_tree_impl_leaf.
Admitted.

Lemma list_on_tree_coincidence_r: forall v ls rs l p d,
  list_nth_on_tree l p (Node v ls rs) ->
  complete_tree_pop d (Node v ls rs) ->
  full_tree_b (d - 2) rs = true ->
  list_nth_on_tree (firstn (Z.to_nat (Zlength l - 1)) l) (p * 2 + 1) rs.
Proof.
  intros.
  revert l p d v ls H H1 H0.
  induction rs; simpl; intros.
  + apply list_nth_on_tree_Leaf.
  + inversion H; subst.
    inversion H8; subst.
    apply list_nth_on_tree_Node.
    - rewrite Zlength_firstn by lia.
      
Admitted.

Lemma list_on_tree_coincidence_l: forall v ls rs l p d,
  list_nth_on_tree l p (Node v ls rs) ->
  complete_tree_pop d (Node v ls rs) ->
  full_tree_b (d - 2) rs = false ->
  list_nth_on_tree (firstn (Z.to_nat (Zlength l - 1)) l) (p * 2) ls.
Proof.
  intros.
Admitted.

Lemma list_on_tree_to_pt_pop: forall l tr pt d1 d2 n p,
  tr <> Leaf ->
  list_nth_on_tree l p tr ->
  list_nth_on_partial_tree (firstn (Z.to_nat (Zlength l - 1)) l) n p pt ->
  complete_tree_pop d1 (tree_compose pt tr) ->
  complete_tree_pop d2 tr ->
  list_nth_on_partial_tree (firstn (Z.to_nat (Zlength l - 1)) l) n (last_index d2 p tr) (skipn 1 (tree_to_partial_tree_pop_fix pt tr d2)).
Proof.
  intros.
  revert l d1 d2 n p pt H0 H1 H2 H3.
  induction tr; simpl; intros.
  + contradiction.
  + inversion H3; subst.
    - rewrite full_tree_equiv1 in H8.
      rewrite H8.
      fold (skipn 1 (tree_to_partial_tree_pop_fix ((false, v, tr2) :: pt) tr1
      (d2 - 1))).
      destruct (classic (tr1 = Leaf)).
      1: {
        subst.
        inversion H6.
        rewrite <- full_tree_equiv1 in H8.
        pose proof full_tree_nonneg _ _ H8.
        lia.
      }
      eapply IHtr1; eauto; inversion H0; subst.
      * auto.
      * inversion H12.
        1: { rewrite H5 in H4; contradiction. }
        eapply nth_partial_tree_cons; eauto.
        ++ rewrite Z.div_mul by lia.
           rewrite Zlength_firstn.
           lia.
        ++ rewrite Z.div_mul by lia; lia.
        ++ rewrite Z.div_mul by lia.
           rewrite Znth_firstn by lia.
           auto.
        ++ simpl.
           eapply list_on_tree_coincidence_r; eauto.
        ++ rewrite Z.div_mul by lia; auto.  
    - pose proof complete_tree_pop_not_fullb _ _ H8.
      replace (d2 - 1 - 1) with (d2 - 2) in H4 by lia.
      rewrite H4.
      inversion H0; subst.
      destruct (classic (tr2 = Leaf)).
      1: {
        subst; simpl.
        rewrite Odd_Div2 by lia; auto.
      }
      fold (skipn 1 ( tree_to_partial_tree_pop_fix ((true, Znth p l, tr1) :: pt) tr2
      (d2 - 1))).
      eapply IHtr2; eauto.
      inversion H13.
      1: { rewrite H7 in H5; contradiction. }
      eapply nth_partial_tree_cons; eauto.
      * rewrite Odd_Div2 by lia.
        rewrite Zlength_firstn.
        lia.
      * rewrite Odd_Div2 by lia; lia.
      * rewrite Odd_Div2 by lia.
        rewrite Znth_firstn by lia.
        auto.
      * simpl.
        replace (p * 2 + 1 + -1) with (p * 2) by lia.
        eapply list_on_tree_coincidence_l; eauto.
      * rewrite Odd_Div2 by lia; auto.    
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
      assert (Zlength l - 1 = last_index d 1 (Node v ls rs)). {
        rewrite tree_last_index_size by auto; lia.
      }
      assert (ls <> Leaf). {
        rewrite <- full_tree_equiv1 in H7.
        pose proof full_tree_nonneg _ _ H7.
        eapply complete_tree_pop_not_leaf; eauto; lia.
      }
      apply list_nth_on_tree_Node.
      - rewrite Zlength_firstn.
        rewrite upd_Znth_Zlength by lia.
        lia.
      - rewrite Znth_firstn by lia.
        rewrite upd_Znth_same by lia.
        unfold tree_to_partial_tree_pop.
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
      - apply list_nth_on_tree_decompose with (p := last_index d 1 (Node v ls rs)).
        1: {apply list_nth_on_tree_Leaf. }
        unfold tree_to_partial_tree_pop.
        simpl.
        rewrite H7.
        fold (skipn 1 (tree_to_partial_tree_pop_fix [] ls (d - 1))).
        rewrite <- sublist_firstn.
        rewrite sublist_upd_Znth_lr by lia.
        rewrite sublist_firstn.
        apply list_nth_on_partial_tree_update; [ | rewrite Zlength_firstn by lia; lia | lia].
        eapply list_on_tree_to_pt_pop; eauto.
        * inversion H0; replace (1 * 2) with 2 in H12 by lia; auto.
        * apply nth_partial_tree_nil; auto.   
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
          + give_up. 
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

Lemma MaxHeap_tree_down_state: forall (ls rs: tree) (d v: Z),
  tree_size (Node v ls rs) >= 2 -> MaxHeap (Node v ls rs) -> complete_tree_pop d (Node v ls rs) ->
  MaxHeap_tree_down ([], tree_cut_last ls rs d).
Proof.
  intros.
  unfold MaxHeap_tree_down; simpl.
  split; [apply MaxHeap_partial_tree_v_nil; reflexivity|].
  split.
  + unfold tree_cut_last.
    inversion H0; [discriminate|].
    unfold MaxHeap_no_rt.
    inversion H1; subst.
    - apply full_tree_equiv1 in H11.
      rewrite H11.
      exists (get_last_val (tree_to_partial_tree_pop ls (d - 1))), (tree_compose (skipn 1 (tree_to_partial_tree_pop ls (d - 1))) Leaf), rs.
      injection H2; intros; subst.
      split; [tauto|].
      split; [|tauto].
      apply tree_compose_MaxHeap; [apply MaxHeap_Leaf; tauto|left].
      split; [reflexivity|].
      apply MaxHeap_tree_partial_tree_skip.
      unfold tree_to_partial_tree_pop.
      apply MaxHeap_tree_partial_hold; try tauto; [|unfold MaxHeap_partial_tree; tauto].
      destruct H5; [left;tauto|right].
      apply MaxHeap_partial_tree_v_nil.
      reflexivity.
    - pose proof complete_tree_pop_not_fullb _ _ H11.
      replace (d-1-1) with (d-2) in H7 by lia.
      rewrite H7.
      exists (get_last_val (tree_to_partial_tree_pop rs (d - 1))), ls, (tree_compose (skipn 1 (tree_to_partial_tree_pop rs (d - 1))) Leaf).
      injection H2; intros; subst.
      split; [tauto|].
      split; [tauto|].
      apply tree_compose_MaxHeap; [apply MaxHeap_Leaf; tauto|left].
      split; [reflexivity|].
      apply MaxHeap_tree_partial_tree_skip.
      unfold tree_to_partial_tree_pop.
      apply MaxHeap_tree_partial_hold; try tauto; [|unfold MaxHeap_partial_tree; tauto].
      destruct H6; [left;tauto|right].
      apply MaxHeap_partial_tree_v_nil.
      reflexivity.
  + pose proof tree_cut_last_size ls rs v d H H1.
    simpl in H.
    pose proof tree_not_emp (tree_cut_last ls rs d) ltac:(lia).
    destruct H3 as [v0 [ls0 [rs0]]].
    exists v0, ls0, rs0.
    split; [tauto|].
    split; right; apply MaxHeap_partial_tree_v_nil; tauto.
Qed.

Lemma complete_tree_pop_holds: forall (t: tree)(d: Z), 
   t <> Leaf -> complete_tree_pop d t -> complete_tree_push d (tree_compose (skipn 1%nat (tree_to_partial_tree_pop t d)) Leaf).
Proof.
  intros.
  induction H0.
  + tauto.
  + unfold tree_to_partial_tree_pop.
    unfold tree_to_partial_tree_pop_fix; fold tree_to_partial_tree_pop_fix.
    apply full_tree_equiv1 in H1; rewrite H1.
    apply full_tree_equiv1 in H1.
    destruct ls.
    - inversion H0.
      replace (dep-2) with (-1) in H1 by lia.
      pose proof full_tree_gt_0 _ _ H1; lia.
    - replace ((false, v, rs) :: nil) with (nil ++ [(false, v, rs)]); [|  rewrite app_nil_l; tauto].
      rewrite tree_to_partial_tree_pop_get.
      pose proof tree_to_partial_tree_len (Node v0 ls1 ls2) (dep - 1) ltac:(discriminate).
      replace 1%nat with (Z.to_nat 1) by lia.
      rewrite Zskipn_app1; [|unfold tree_to_partial_tree_pop in H2; lia].
      rewrite tree_compose_append.
      apply complete_tree_push_right_full; [|tauto].
      apply IHcomplete_tree_pop; discriminate.
  + unfold tree_to_partial_tree_pop.
    unfold tree_to_partial_tree_pop_fix; fold tree_to_partial_tree_pop_fix.
    pose proof complete_tree_pop_not_fullb _ _ H1.
    replace (dep-1-1) with (dep-2) in H2 by lia; rewrite H2.
    destruct rs.
    - inversion H1.
      simpl.
      replace dep with 1 by lia.
      apply complete_tree_push_Leaf; lia.
    - replace ((true, v, ls) :: nil) with (nil ++ [(true, v, ls)]); [|  rewrite app_nil_l; tauto].
      rewrite tree_to_partial_tree_pop_get.
      pose proof tree_to_partial_tree_len (Node v0 rs1 rs2) (dep - 1) ltac:(discriminate).
      replace 1%nat with (Z.to_nat 1) by lia.
      rewrite Zskipn_app1; [|unfold tree_to_partial_tree_pop in H3; lia].
      rewrite tree_compose_append.
      apply complete_tree_push_left_full; [tauto|].
      apply IHcomplete_tree_pop; discriminate.
Qed. 

Lemma complete_tree_pop_holds_all: forall (ls rs: tree)(d v: Z), 
   complete_tree_pop d (Node v ls rs) -> tree_size (Node v ls rs) >= 2 -> complete_tree_push d (tree_cut_last ls rs d).
Proof.
  intros.
  rename H0 into HH.
  unfold tree_cut_last.
  inversion H; subst.
  + apply full_tree_equiv1 in H4; rewrite H4.
    apply full_tree_equiv1 in H4.
    apply complete_tree_push_right_full; [|tauto].
    apply complete_tree_pop_holds; [|tauto].
    destruct ls; [|discriminate].
    inversion H2; replace (d-2) with (-1) in H4 by lia.
    pose proof full_tree_gt_0 _ _ H4; lia.
  + pose proof complete_tree_pop_not_fullb _ _ H4.
    replace (d-1-1) with (d-2) in H0 by lia; rewrite H0.
    apply complete_tree_push_left_full; [tauto|].
    apply complete_tree_pop_holds; [|tauto].
    destruct rs; [|discriminate].
    inversion H4.
    rewrite H1 in H2.
    inversion H2.
    - rewrite <- H5 in HH; simpl in HH; lia.
    - pose proof full_tree_gt_0 _ _ H5; lia.
Qed.

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
      simpl.
      rewrite Zlength_firstn.
      replace (Z.max 0 (Zlength l -1)) with (Zlength l -1) by lia.
      rewrite upd_Znth_Zlength; [|lia].
      lia.
    }
    pose proof Down_tree_list_rel _ _ _ H6 H4 H2.
    subst.
    assert (tree_size (Node v ls rs) >= 2). {
      destruct H, H3.
      rewrite H3; lia.
    }
    rename H3 into HH.
    pose proof MaxHeap_tree_down_state _ _ _ _ HH H1 H5.
    specialize (H7 H3).
    destruct H7 as [t'].
    destruct H7, H8.
    pose proof list_on_tree_state_impl_tree_compose _ _ H8.
    simpl in H10.
    exists (tree_compose (fst t') (snd t')).
    split; [tauto|].
    split; [tauto|].
    unfold tree_pop; right.
    destruct H, H11.
    split; [lia|].
    exists v, ls, rs, t', d.
    tauto.
Qed.