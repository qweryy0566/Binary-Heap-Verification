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
Require Import cprogs.heap.tree_up.

Require Import SetsClass.SetsClass.
Local Open Scope sets.
Import SetsNotation.

Fixpoint tree_next_pow2 (d: Z) (tr: tree): Z :=
  match tr with
  | Leaf => 1
  | Node v ls rs => 
    if full_tree_b (d - 1) ls then
      2 * tree_next_pow2 (d - 1) rs
    else
      2 * tree_next_pow2 (d - 1) ls
  end.

Lemma full_tree_next_pow2: forall d t,
  full_tree d t ->
  tree_next_pow2 (d + 1) t = tree_size t + 1.
Proof.
  intros.
  induction H; simpl. 
  + lia.
  + replace (dep + 1 - 1) with dep by lia.
    remember H as H'; clear HeqH'.
    rewrite full_tree_equiv1 in H.
    apply full_tree_b_dep_restrict in H.
    replace (dep - 1 + 1) with dep in H by lia.
    rewrite H; simpl.
    replace (dep - 1 + 1) with dep in IHfull_tree1 by lia.
    rewrite IHfull_tree1.
    rewrite (full_tree_same_size _ _ _ H' H0).
    lia.
Qed.

Lemma full_tree_next_index: forall d t, 
  full_tree d t -> next_index (d + 1) 0 t = 0.
Proof.
  intros.
  induction H; subst; simpl; auto.
  replace (dep + 1 - 1) with dep by lia.
  rewrite full_tree_equiv1 in H.
  pose proof full_tree_b_dep_restrict _ _ H.
  replace (dep - 1 + 1) with dep in H1 by lia.
  rewrite H1; simpl.
  replace (dep - 1 + 1) with dep in IHfull_tree1 by lia.
  tauto.
Qed.

Lemma next_index_lowbit: forall n d t,
  complete_tree_push d t ->
  next_index d n t = n * (tree_next_pow2 d t) + next_index d 0 t.
Proof.
  intros.
  revert d n H.
  induction t; simpl; intros.
  + lia.
  + inversion H; subst v t1 t2.
    - rewrite full_tree_equiv1 in H2.
      rewrite H2; simpl.   
      specialize (IHt2 (d - 1)).
      remember IHt2 as IHt2'; clear HeqIHt2'.
      specialize (IHt2' 1 H4).
      rewrite IHt2'.
      specialize (IHt2 (n * 2 + 1) H4).
      rewrite IHt2.
      lia. 
    - pose proof complete_tree_push_not_fullb _ _ H2.
      rewrite H0; simpl.   
      specialize (IHt1 (d - 1) (n * 2) H2).
      rewrite IHt1.
      lia. 
Qed.

Lemma complete_tree_push_same_next_pow2: forall d t1 t2,
  complete_tree_push d t1 -> complete_tree_push d t2 ->
  tree_next_pow2 d t1 = tree_next_pow2 d t2.
Proof.
  intros.
  revert t2 H0.
  induction H; subst; simpl; intros.
  + inversion H0; subst; simpl.
    - reflexivity.
    - pose proof complete_tree_push_dep_positve _ _ H1; lia.
    - pose proof complete_tree_push_dep_positve _ _ H; lia.
  + rewrite full_tree_equiv1 in H.
    rewrite H; simpl.
    inversion H1; subst; simpl.
    - pose proof complete_tree_push_dep_positve _ _ H0; lia.
    - rewrite full_tree_equiv1 in H2.
      rewrite H2; simpl.
      specialize (IHcomplete_tree_push _ H3).
      lia.
    - pose proof complete_tree_push_not_fullb _ _ H2.
      rewrite H4; simpl.
      specialize (IHcomplete_tree_push _ H2).
      lia.
  + pose proof complete_tree_push_not_fullb _ _ H.
    rewrite H2; simpl.
    inversion H1; subst; simpl.
    - pose proof complete_tree_push_dep_positve _ _ H; lia.
    - rewrite full_tree_equiv1 in H3. 
      rewrite H3; simpl.
      specialize (IHcomplete_tree_push _ H4).
      lia.
    - pose proof complete_tree_push_not_fullb _ _ H3.
      rewrite H5; simpl.
      specialize (IHcomplete_tree_push _ H3).
      lia. 
Qed.

Lemma tree_next_index_size: forall t d,
  complete_tree_push d t ->
  next_index d 1 t = tree_size t + 1.
Proof.
  intros.
  revert d H.
  induction t; simpl; intros; [lia |].
  inversion H; subst v t1 t2.
  + remember H2 as H2'; clear HeqH2'.
    rewrite full_tree_equiv1 in H2'.
    rewrite H2'; simpl.
    specialize (IHt2 (d - 1) H4).
    rewrite next_index_lowbit by auto.
    rewrite next_index_lowbit in IHt2 by auto.
    pose proof full_tree_complete_tree_push _ _ H2.
    replace (d - 1 + 1) with d in H0 by lia.
    specialize (IHt1 d H0).
    rewrite next_index_lowbit in IHt1 by auto.
    pose proof full_tree_next_pow2 _ _ H2.
    replace (d - 1 + 1) with d in H1 by lia.
    pose proof complete_tree_push_same_next_pow2 _ _ _ H0 H.
    simpl in H3; rewrite H2' in H3.
    lia.
  + pose proof complete_tree_push_not_fullb _ _ H2.
    rewrite H0; simpl.
    specialize (IHt1 (d - 1) H2).
    rewrite next_index_lowbit by auto.
    rewrite next_index_lowbit in IHt1 by auto.
    pose proof full_tree_complete_tree_push _ _ H4.
    replace (d - 2 + 1) with (d - 1) in H1 by lia.
    specialize (IHt2 (d - 1) H1).
    rewrite next_index_lowbit in IHt2 by auto.
    pose proof full_tree_next_pow2 _ _ H4.
    replace (d - 1 + 1) with d in H3 by lia.
    pose proof complete_tree_push_same_next_pow2 _ _ _ H1 H2.
    pose proof full_tree_next_index _ _ H4.
    replace (d - 2 + 1) with (d - 1) in H6 by lia.
    lia.     
Qed.

(* Lemma list_on_tree_compose: forall l n d t,
  list_nth_on_tree l n t ->
  complete_tree_push d t ->
  exists pt, t = tree_compose pt Leaf /\
  list_nth_on_partial_tree l n (next_index d n t) pt.
Proof.
  intros.
  revert n H.
  induction H0; intros.
  + exists nil.
    split; auto.
    constructor; auto.
  + inversion H1; subst v0 ls0 rs0.
    specialize (IHcomplete_tree_push _ H8).
    destruct IHcomplete_tree_push as [pt [? ?] ].
    exists (pt ++ [(true, v, ls)]).
    split.
    - rewrite tree_compose_append.
      rewrite H2.
      auto.
    - apply list_nth_on_partial_tree_app; [ | lia].
      split; [ | split].
      * simpl.
        assert (full_tree_b (dep - 2) rs = false) by admit.
        rewrite H4; tauto.
      * tauto.
      * tauto.
  + inversion H1; subst v0 ls0 rs0.
    specialize (IHcomplete_tree_push _ H7).
    destruct IHcomplete_tree_push as [pt [? ?] ].
    exists (pt ++ [(false, v, rs)]).
    split.
    - rewrite tree_compose_append.
      rewrite H2.
      auto.
    - apply list_nth_on_partial_tree_app; [ | lia].
      split; [ | split].
      * simpl.
        assert (full_tree_b (dep - 2) rs = true) by admit.
        rewrite H4; tauto.
      * tauto.
      * tauto. 
Admitted.
  *)

Lemma list_nth_on_tree_app:  forall (l: list Z) (v n: Z) (t: tree),
  list_nth_on_tree l n t -> list_nth_on_tree (l++[v]) n t.
Proof.
  intros.
  induction H.
  + apply list_nth_on_tree_Leaf.
  + eapply list_nth_on_tree_Node; try tauto.
    - rewrite Zlength_app.
      replace (Zlength [v]) with 1 by tauto.
      lia.
    - rewrite app_Znth1; [tauto|lia].
Qed.

Lemma list_on_partial_tree_app: forall (l: list Z) (lt: partial_tree) (v n: Z),
  list_on_partial_tree l n lt -> list_on_partial_tree (l ++ [v]) n lt.
Proof.
  intros.
  revert n H.
  induction lt; intros.
  + inversion H; [|discriminate].
    apply nil_partial_tree; tauto.
  + destruct a as [[flg val] tr].
    inversion H; [discriminate|].
    injection H0; intros; subst.
    eapply cons_partial_tree; try reflexivity; try tauto.
    - rewrite Zlength_app.
      replace (Zlength [v]) with 1 by tauto.
      lia.
    - rewrite app_Znth1; [tauto|lia].
    - apply list_nth_on_tree_app; tauto.
    - apply IHlt; tauto.
Qed.

Lemma list_on_tree_state_app2: forall (l: list Z) (t: tree) (lt: partial_tree) (v n  d: Z), 
  list_on_tree_state (l,n) (lt,t) -> complete_tree_push d t ->
  list_on_partial_tree (l++[v]) (next_index d n t) (tree_to_partial_tree_fix lt t d).
Proof.
  intros.
  revert lt n d H H0.
  induction t; intros.
  + simpl.
    unfold list_on_tree_state in H.
    unfold list_on_tree_state_fix in H; simpl in H.
    destruct H, H1, H2. 
    apply list_on_partial_tree_app; tauto.
  + simpl.
    remember (full_tree_b (d - 1) t1) as HQ.
    destruct HQ; simpl.
    - apply IHt2.
      2: {
        inversion H0; [tauto|].
        pose proof full_tree_complete_tree_push _ _ H5.
        replace (d-2+1) with (d-1) in H6 by lia.
        tauto.
      }
      revert H; unfold list_on_tree_state.
      unfold list_on_tree_state_fix; simpl; intros.
      destruct H, H1, H2.
      inversion H.
      split; [tauto|].
      split; [|tauto].
      eapply cons_partial_tree; try reflexivity; try rewrite Odd_Div2; try lia.
      * simpl.
        replace (n * 2 + 1 + -1) with (n*2) by lia.
        tauto.
      * tauto.
    - apply IHt1.
      2: {
        inversion H0; [|tauto].
        apply full_tree_equiv1 in H3.
        rewrite H3 in HeqHQ.
        discriminate.
      }
      revert H; unfold list_on_tree_state.
      unfold list_on_tree_state_fix; simpl; intros.
      destruct H, H1, H2.
      inversion H.
      split; [tauto|].
      split; [|tauto].
      eapply cons_partial_tree; try reflexivity; try rewrite Even_Div2; try lia.
      * simpl; tauto.
      * tauto.
Qed.


Lemma tree_to_partial_tree_get: forall (t tr: tree) (lt: partial_tree) (flg: bool) (v d: Z), 
  tree_to_partial_tree_fix (lt ++ [(flg,v,tr)]) t d = (tree_to_partial_tree_fix lt t d) ++ [(flg,v,tr)].
Proof.
  intros.
  revert v tr flg d lt.
  induction t; intros.
  + unfold tree_to_partial_tree.
    simpl. tauto.
  + simpl.
    destruct (full_tree_b (d - 1)).
    - replace ((true, v, t1) :: (lt ++ [(flg, v0, tr)])) with ([(true, v, t1)] ++ (lt ++ [(flg, v0, tr)])) by reflexivity.
      replace ((true, v, t1) :: lt) with ([(true, v, t1)] ++ lt) by reflexivity.
      rewrite app_assoc.
      apply IHt2.
    - replace ((false, v, t2) :: (lt ++ [(flg, v0, tr)])) with ([(false, v, t2)] ++ (lt ++ [(flg, v0, tr)])) by reflexivity.
      replace ((false, v, t2) :: lt) with ([(false, v, t2)] ++ lt) by reflexivity.
      rewrite app_assoc.
      apply IHt1.
Qed.
 
Lemma complete_tree_holds: forall (t: tree)(d v: Z), 
  complete_tree_push d t -> complete_tree_pop d (tree_compose (tree_to_partial_tree t d) (Node v Leaf Leaf)). 
Proof.
  intros.
  induction H; intros.
  + subst; simpl.
    apply complete_tree_pop_right_hole.
    - apply full_tree_Leaf; lia.
    - apply complete_tree_pop_Leaf; lia.  
  + unfold tree_to_partial_tree.
    apply full_tree_equiv1 in H.
    simpl.
    rewrite H.
    replace ((true, v0, ls) :: nil) with (nil ++ [(true,v0,ls)]). 2: {
      rewrite app_nil_l; auto.
    }
    rewrite tree_to_partial_tree_get.
    rewrite tree_compose_append.
    apply full_tree_equiv1 in H.
    apply complete_tree_pop_right_hole; tauto.
  + unfold tree_to_partial_tree.
    pose proof complete_tree_push_not_fullb _ _ H.
    simpl.
    rewrite H1.
    replace ((false, v0, rs) :: nil) with (nil ++ [(false,v0, rs)]). 2: {
      rewrite app_nil_l; auto.
    }
    rewrite tree_to_partial_tree_get.
    rewrite tree_compose_append.
    apply full_tree_equiv1 in H0.
    apply complete_tree_pop_left_hole; auto.
    apply full_tree_equiv1 in H0.
    auto.
Qed.

Lemma tree_to_partial_tree_size: forall (t: tree) (d: Z),
  complete_tree_push d t -> tree_size t = partial_tree_size (tree_to_partial_tree t d).
Proof.
  intros.
  revert d H.
  induction t; intros.
  + simpl; lia.
  + unfold tree_to_partial_tree.
    simpl.
    inversion H; subst.
    - rewrite full_tree_equiv1 in H2.
      rewrite H2; simpl.
      replace ((true, v, t1) :: nil) with (nil ++ [(true, v, t1)]); [|rewrite app_nil_l; auto]. 
      rewrite tree_to_partial_tree_get.
      rewrite partial_tree_append_size.
      rewrite (IHt2 (d-1)); [reflexivity|tauto].
    - pose proof complete_tree_push_not_fullb _ _ H2.
      rewrite H0; simpl.
      replace ((false, v, t2) :: nil) with (nil ++ [(false, v, t2)]); [|rewrite app_nil_l; auto]. 
      rewrite tree_to_partial_tree_get.
      rewrite partial_tree_append_size.
      rewrite (IHt1 (d - 1)); [unfold tree_to_partial_tree; lia| auto]. 
Qed.

Lemma list_on_tree_state_app: forall (l: list Z) (t: tree) (v: Z),
  Zlength l >= 1 -> list_on_tree l t -> exists d, list_on_tree_state (l++[v], Zlength l) (tree_to_partial_tree t d,Node v Leaf Leaf) /\ complete_tree_push d t.
Proof.
  intros.
  unfold list_on_tree_state; simpl.
  unfold list_on_tree_state_fix.
  unfold list_on_tree in H0.
  destruct H0, H1.
  destruct H2 as [dep].
  exists dep.
  assert (Zlength (l ++ [v]) = Zlength l + 1). {
    rewrite Zlength_app.
    replace (Zlength [v]) with 1; [lia|].
    unfold Zlength; unfold Zlength_aux; reflexivity.
  }
  split; [| tauto].
  split.
  + eapply list_nth_on_tree_Node.
    - rewrite H3.
      pose proof initial_world.zlength_nonneg _ l.
      lia.
    - rewrite app_Znth2; [|lia].
      replace (Zlength l - Zlength l) with 0 by lia.
      reflexivity.
    - eapply list_nth_on_tree_Leaf. 
    - eapply list_nth_on_tree_Leaf. 
  + split.
    assert (list_on_tree_state (l, 1) (nil, t)). {
      unfold list_on_tree_state; simpl.
      unfold list_on_tree_state_fix.
      split; [tauto|].
      split; [apply nil_partial_tree; reflexivity|].
      split; simpl; [|exists dep]; tauto.
    }
    pose proof list_on_tree_state_app2 l t nil v 1 dep H4 H2.
    - replace (Zlength l) with (tree_size t + 1) by lia.
      unfold tree_to_partial_tree.
      rewrite <- (tree_next_index_size _ dep); tauto.
    - split.
      * rewrite tree_compose_size.
        rewrite <- (tree_to_partial_tree_size _ dep); [| tauto].
        simpl.
        rewrite Zlength_app.
        replace (Zlength [v]) with 1 by tauto.
        lia.
      * apply complete_tree_equality.
        pose proof complete_tree_holds _ _ v H2.
        exists dep; tauto.
Qed.

Definition tree_push: tree -> Z -> tree -> Prop :=
  fun t val t' =>
    exists ts d d2, heap_tree_up ((tree_to_partial_tree t d), Node val Leaf Leaf) ts /\ complete_tree_push d t /\ t' = (tree_compose (fst ts) (snd ts)) /\ complete_tree_push d2 t'.

Lemma tree_to_partial_tree_fix_hold: forall (lt: partial_tree) (t: tree) (d: Z),
  MaxHeap_partial_tree lt -> MaxHeap t -> (t = Leaf \/ MaxHeap_partial_tree_v lt (get_tree_val t)) -> complete_tree_push d t -> MaxHeap_partial_tree (tree_to_partial_tree_fix lt t d).
Proof.
  intros.
  revert lt d H H1 H2.
  induction H0; intros.
  + rewrite H.
    simpl.
    apply H0.
  + subst.
    destruct H3; [discriminate|].
    simpl in H.
    simpl.
    inversion H4.
    - apply full_tree_equiv1 in H6.
      rewrite H6.
      apply IHMaxHeap2; [ | |tauto].
      * unfold MaxHeap_partial_tree; try tauto.
      * destruct H1; [left; tauto|right].
        eapply MaxHeap_partial_tree_v_app; try reflexivity; tauto.
    - pose proof complete_tree_push_not_fullb _ _ H6.
      rewrite H9.
      apply IHMaxHeap1; [ | |tauto].
      * unfold MaxHeap_partial_tree; try tauto.
      * destruct H0; [left; tauto|right].
        eapply MaxHeap_partial_tree_v_app; try reflexivity; tauto.
Qed.

Lemma MaxHeap_impl_MaxHeap_tree_up: forall (t: tree) (v d: Z),
  MaxHeap t -> complete_tree_push d t -> MaxHeap_tree_up (tree_to_partial_tree t d,Node v Leaf Leaf).
Proof.
  intros.
  revert d H H0.
  induction t; intros.
  + unfold tree_to_partial_tree.
    unfold MaxHeap_tree_up.
    simpl.
    split; [tauto|].
    split.
    - eapply MaxHeap_Node; [reflexivity| | | | ]; tauto.
    - exists v, Leaf, Leaf.
      tauto.
  + unfold MaxHeap_tree_up.
    unfold fst, snd.
    inversion H; [discriminate|].
    injection H1; intros; subst.
    split.
      2: {
        split; [|exists v, Leaf, Leaf; tauto].
        eapply MaxHeap_Node; [reflexivity| | | |]; try tauto.
        apply MaxHeap_Leaf; reflexivity.
        apply MaxHeap_Leaf; reflexivity.
      }
      unfold tree_to_partial_tree.
      apply tree_to_partial_tree_fix_hold; [unfold MaxHeap_partial_tree; tauto|tauto|right|tauto].
      apply MaxHeap_partial_tree_v_nil; reflexivity.
Qed.

Lemma Push_tree_list_rel: forall (l l': list Z) (t: tree) (v: Z),
  list_on_tree l t -> heap_push l v l' -> MaxHeap t ->
  exists t', list_on_tree l' t' /\ MaxHeap t' /\ tree_push t v t'.
Proof.
  intros.
  assert (Zlength l >= 1). {
    unfold list_on_tree in H.
    destruct H, H2.
    pose proof tree_size_nonneg t.
    lia.
  }
  unfold heap_push in H0.
  destruct H0.
  pose proof list_on_tree_state_app _ _ v H2 H.
  destruct H3 as [d].
  destruct H3.
  pose proof MaxHeap_impl_MaxHeap_tree_up _ v d H1 H4.
  pose proof Up_tree_list_rel _ _ _ H3 H0 H5.
  destruct H6 as [t'].
  destruct H6, H7.
  pose proof list_on_tree_state_impl_tree_compose _ _ H7.
  simpl in H9.
  exists (tree_compose (fst t') (snd t')).
  split; [tauto|].
  split; [tauto|].
  unfold tree_push.
  unfold list_on_tree in H9.
  destruct H9, H10.
  destruct H11 as [d2].
  exists t', d, d2.
  split; [tauto|].
  split; [tauto|].
  split; [reflexivity|tauto].
Qed.