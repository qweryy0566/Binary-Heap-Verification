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

Require Import SetsClass.SetsClass.
Local Open Scope sets.
Import SetsNotation.

Inductive list_nth_on_partial_tree (l: list Z) (n: Z) (p: Z) (lt: partial_tree) : Prop :=
  | nth_partial_tree_nil: p = n -> lt = nil -> list_nth_on_partial_tree l n p lt
  | nth_partial_tree_cons: forall flg v t lt0, 
    lt = (flg, v, t) :: lt0 ->
    1 <= (p / 2) < Zlength l -> 
    p = (p / 2) * 2 + (if flg then 1 else 0) ->
    Znth (p / 2) l = v -> 
    list_nth_on_tree l (p + (if flg then -1 else 1)) t -> 
    list_nth_on_partial_tree l n (p / 2) lt0 -> 
    list_nth_on_partial_tree l n p lt.


Lemma list_nth_on_partial_tree_app: forall l n p lt (flg: bool) v t,
  (if flg then
    list_nth_on_partial_tree l (n * 2 + 1) p lt /\ list_nth_on_tree l (n * 2) t /\ Znth n l = v
  else
    list_nth_on_partial_tree l (n * 2) p lt /\ list_nth_on_tree l (n * 2 + 1) t /\ Znth n l = v) ->
  1 <= n < Zlength l ->
  list_nth_on_partial_tree l n p (lt ++ [(flg, v, t)]).
Proof.
  intros.
  destruct flg.
  {
    revert l p v n t H H0.
    induction lt; intros; simpl; destruct H as [? [? ?] ].
    + inversion H; [ | discriminate].
      pose proof Z.div_lt_upper_bound p 2 (n + 1) ltac:(lia) ltac:(lia).
      pose proof Z.div_le_lower_bound p 2 n ltac:(lia) ltac:(lia).
      eapply nth_partial_tree_cons; eauto; simpl.
      * inversion H; [lia | discriminate].
      * lia. 
      * replace (p / 2) with n by lia; tauto.
      * replace (p + -1) with (n * 2) by lia; tauto.
      * apply nth_partial_tree_nil; [lia | tauto].
    + destruct a as [[flga va] ta].
      inversion H; [discriminate | ].
      injection H3; intros; subst lt0 ta va flga.
      eapply nth_partial_tree_cons; eauto.
  }
  {
    revert l p v n t H H0.
    induction lt; intros; simpl; destruct H as [? [? ?] ].
    + inversion H; [ | discriminate].
      pose proof Z.div_lt_upper_bound p 2 (n + 1) ltac:(lia) ltac:(lia).
      pose proof Z.div_le_lower_bound p 2 n ltac:(lia) ltac:(lia).
      eapply nth_partial_tree_cons; eauto; simpl.
      * inversion H; [lia | discriminate].
      * lia. 
      * replace (p / 2) with n by lia; tauto.
      * replace (p + 1) with (n * 2 + 1) by lia; tauto.
      * apply nth_partial_tree_nil; [lia | tauto].
    + destruct a as [[flga va] ta].
      inversion H; [discriminate | ].
      injection H3; intros; subst lt0 ta va flga.
      eapply nth_partial_tree_cons; eauto.
  }
Qed.

Lemma full_tree_equiv1: forall d t,
  full_tree d t <-> full_tree_b d t = true.
Proof.
  intros.
  split; intros.
  + induction H; subst; simpl.
    - reflexivity.
    - rewrite IHfull_tree1, IHfull_tree2; reflexivity.
  + revert d H.
    induction t; simpl; intros.
    - apply Z.eqb_eq in H; subst.
      constructor; reflexivity.
    - apply andb_prop in H; destruct H.
      specialize (IHt1 _ H).
      specialize (IHt2 _ H0).
      constructor; auto.
Qed.

Lemma complete_tree_push_not_fullb: forall d t,
  complete_tree_push d t ->
  full_tree_b d t = false.
Proof.
  intros.
  induction H; subst; simpl.
  + reflexivity.
  + apply andb_false_intro2; assumption.
  + apply andb_false_intro1; assumption.
Qed.

Lemma full_tree_b_dep_restrict: forall t d,
  full_tree_b d t = true -> full_tree_b (d + 1) t = false.
Proof.
  intros t.
  induction t; simpl; intros.
  + rewrite Z.eqb_neq.
    rewrite Z.eqb_eq in H.
    lia.
  + apply andb_prop in H; destruct H.
    specialize (IHt1 _ H).
    replace (d - 1 + 1) with (d + 1 - 1) in IHt1 by lia.
    apply andb_false_intro1; assumption. 
Qed.

Fixpoint tree_next_pow2 (d: Z) (tr: tree): Z :=
  match tr with
  | Leaf => 1
  | Node v ls rs => 
    if full_tree_b (d - 1) ls then
      2 * tree_next_pow2 (d - 1) rs
    else
      2 * tree_next_pow2 (d - 1) ls
  end.

Lemma full_tree_nonneg: forall d t,
  full_tree d t -> 0 <= d.
Proof.
  intros.
  induction H; lia.
Qed.

Lemma full_tree_same_size: forall d t1 t2,
  full_tree d t1 -> full_tree d t2 -> tree_size t1 = tree_size t2.
Proof.
  intros.
  revert t2 H0.
  induction H; intros.
  + inversion H0; [reflexivity | ]. 
    pose proof full_tree_nonneg _ _ H1; lia.
  + inversion H1; subst.
    - pose proof full_tree_nonneg _ _ H; lia.
    - simpl.
      rewrite (IHfull_tree1 _ H2).
      rewrite (IHfull_tree2 _ H3).
      reflexivity.  
Qed.

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

Lemma complete_tree_push_dep_positve: forall d t,
  complete_tree_push d t -> 1 <= d.
Proof.
  intros.
  induction H; lia.
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
  
Lemma complete_tree_next_index: forall d t,
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

Lemma list_on_tree_state_app: forall (l: list Z) (t: tree) (v: Z),
  Zlength l >= 1 -> list_on_tree l t -> 
  exists pt, list_on_tree_state (l++[v], Zlength l) (pt, Node v Leaf Leaf).
Proof.
  intros.
  unfold list_on_tree in H0.
  destruct H0 as [? [? [d ?]]].
  unfold list_on_tree_state; simpl.
  unfold list_on_tree_state_fix.
  pose proof tree_push_trompose_sound _ _ v H2.
  destruct H3 as [pt [? ?] ].
  exists pt.
  split.
  + apply list_nth_on_tree_Node.
    - rewrite Zlength_app.
      replace (Zlength [v]) with 1 by auto.
      lia.
    - rewrite app_Znth2 by lia.
      replace (Zlength l - Zlength l) with 0 by lia.
      auto.
    - constructor.
    - constructor.
  +      
Qed. *)