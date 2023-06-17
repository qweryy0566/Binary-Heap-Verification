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

Fixpoint tree_next_log (d: Z) (tr: tree): Z :=
  match tr with
  | Leaf => 1
  | Node v ls rs => 
    if full_tree_b (d - 2) rs then
      2 * tree_next_log (d - 1) ls
    else
      2 * tree_next_log (d - 1) rs
  end.

Lemma next_index_lowbit: forall n d t,
  complete_tree_push d t ->
  next_index d n t = n * (tree_next_log d t) + next_index d 0 t.
Proof.
  intros.
  revert d n H.
  induction t; simpl; intros.
  + lia.
  + inversion H; subst v t1 t2.
    - assert (full_tree_b (d - 1) ls = true) by admit.
      rewrite H0; simpl.   
      specialize (IHt2 (d - 1)).
      remember IHt2 as IHt2'; clear HeqIHt2'.
      specialize (IHt2' 1 H4).
      rewrite IHt2'.
      specialize (IHt2 (n * 2 + 1) H4).
      rewrite IHt2.
      lia. 
    - assert (full_tree_b (d - 2) rs = true) by admit.
      rewrite H0; simpl.   
      specialize (IHt1 (d - 1) (n * 2) H2).
      rewrite IHt1.
      lia. 
Admitted.
  
Lemma complete_tree_next_index: forall d t,
  complete_tree_push d t ->
  next_index d 1 t = tree_size t + 1.
Proof.
  intros.
  revert d H.
  induction t; simpl; intros.
  2: {
    inversion H; subst v t1 t2.
    + assert (full_tree_b (d - 2) rs = false) by admit.
      rewrite H0; simpl.
      specialize (IHt2 (d - 1) H4).
      rewrite IHt2.
      lia.  
  }  
Qed.

Lemma list_on_tree_decompose: forall l n d t,
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
  pose proof tree_push_decompose_sound _ _ v H2.
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
Qed.