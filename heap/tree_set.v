Require Import FloydSeq.proofauto.
(* Require Import cprogs.heap.program. *)
Require Import Notations Logic Datatypes.
From Coq Require Import String List ZArith. 
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Classical_Prop.
Require Export SetsClass.SetsClass.

Require Import Coq.micromega.Psatz.
Local Open Scope string.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import cprogs.heap.list_relation.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.tree_list.
Require Import cprogs.heap.tree_down.
Require Import cprogs.heap.tree_push.
Require Import cprogs.heap.tree_up.
Require Import cprogs.heap.tree_pop.
Local Open Scope sets.
Local Open Scope logic.

Definition SetZ: Type := Z -> Prop.

Definition Singleton (k: Z): SetZ:=
  fun x => x = k.

Fixpoint SetOf_tree(t: tree): SetZ:=
  match t with
    | Leaf => ∅
    | Node v ls rs => 
        Singleton v ∪ (SetOf_tree ls) ∪ (SetOf_tree rs)
  end.

Fixpoint SetOf_partial_tree(lt: partial_tree): SetZ:=
  match lt with
    | nil => ∅
    | (flg, v, tr) :: lt0 => Singleton v ∪ SetOf_tree tr ∪ SetOf_partial_tree lt0
  end.

Definition tree_set_rel(t: tree) (s: SetZ): Prop :=
  forall x, SetOf_tree t x <-> s x.

Definition SetOf_tree_state(t: tree_state): SetZ:=
  SetOf_partial_tree (fst t) ∪ SetOf_tree (snd t).

Lemma Set_eq_on_tree: forall (t: tree),
  tree_set_rel t (SetOf_tree t).
Proof.
  intros.
  unfold tree_set_rel.
  intros x.
  reflexivity.
Qed.

Lemma SetSplit: forall (ls rs: tree) (s: SetZ) (v: Z),
  tree_set_rel (Node v ls rs) s -> 
  exists L R, tree_set_rel ls L /\ tree_set_rel rs R /\ s == Singleton v ∪ L ∪ R.
Proof.
  intros.
  exists (SetOf_tree ls), (SetOf_tree rs).
  split; [apply Set_eq_on_tree|].
  split; [apply Set_eq_on_tree|].
  unfold_RELS_tac; intros.
  split.
  + unfold tree_set_rel in H.
    apply H.
  + unfold tree_set_rel in H.
    apply H.
Qed.

Lemma tree_compose_set_union: forall (lt: partial_tree) (t: tree),
  SetOf_tree (tree_compose lt t) == SetOf_tree t ∪ SetOf_partial_tree lt.
Proof.
  intros.
  revert t.
  induction lt; intros.
  + simpl.
    rewrite Sets_union_empty.
    reflexivity.
  + destruct a as [[flg val] tr].
    simpl.
    destruct flg.
    - rewrite IHlt.
      unfold SetOf_tree; fold SetOf_tree.
      unfold_RELS_tac.
      intros.
      tauto.
    - rewrite IHlt.
      unfold SetOf_tree; fold SetOf_tree.
      unfold_RELS_tac.
      intros.
      tauto.
Qed.

Lemma tree_to_partial_tree_set_eq: forall (t: tree) (lt: partial_tree) (d: Z),
  complete_tree_push d t -> SetOf_tree t ∪ SetOf_partial_tree lt == SetOf_partial_tree (tree_to_partial_tree_fix lt t d).
Proof.
  intros.
  revert lt.
  induction H; intros.
  + simpl.
    rewrite Sets_empty_union.
    reflexivity.
  + simpl.
    apply full_tree_equiv1 in H.
    rewrite H.
    rewrite <- IHcomplete_tree_push.
    simpl.
    unfold_RELS_tac; intros; tauto.
  + simpl.
    pose proof complete_tree_push_not_fullb _ _ H.
    rewrite H1.
    rewrite <- IHcomplete_tree_push.
    simpl.
    unfold_RELS_tac; intros; tauto.
Qed.

Lemma tree_up_succeed_Set_eq: forall (t t': tree_state),
  tree_up_succeed t t' -> SetOf_tree_state t == SetOf_tree_state t'.
Proof.
  intros.
  unfold tree_up_succeed in H.
  destruct H as [t3 [l']].
  destruct H, H0.
  destruct H1.
  destruct H1 as [v [ls [rs]]].
  destruct H1.
  unfold SetOf_tree_state.
  rewrite <- H; rewrite <- H0.
  unfold swap_up_and_combine in H1.
Admitted.
(* Qed. *)

Lemma Push_to_Set: forall (t t': tree) (s: SetZ) (v d: Z),
  tree_set_rel t s -> complete_tree_push d t -> tree_push t v t' ->
  exists s', tree_set_rel t' s' /\ s' == s ∪ Singleton v.
Proof.
  intros.
  unfold tree_push in H1.
  destruct H1 as [ts [dep1 [dep2]]].
  exists (SetOf_tree t').
  split.
  + unfold tree_set_rel.
    tauto.
  + 
(* Qed. *)
Admitted.

Lemma tree_max_set: forall (t: tree) (s: SetZ),
  tree_set_rel t s -> MaxHeap t -> (t = Leaf \/ (exists v ls rs, t = Node v ls rs /\ s v /\ forall x, s x -> x <= v)).
Proof.
  intros.
  revert s H.
  induction H0.
  + left; tauto.
  + right.
    rewrite H; simpl.
    rewrite H in H2.
    pose proof SetSplit _ _ _ _ H2.
    destruct H3 as [L [R]].
    destruct H3, H4.
    exists v, ls, rs.
    split; [reflexivity|].
    revert H5; unfold_RELS_tac; intros.
    split.
    - rewrite H5.
      left; left.
      unfold Singleton.
      reflexivity.
    - intros.
      apply H5 in H6.
      destruct H6.
      * destruct H6.
        unfold Singleton in H6.
        lia.
        specialize (IHMaxHeap1 L H3).
        rename IHMaxHeap1 into HH.
        destruct HH.
        ++ rewrite H7 in H3.
           unfold tree_set_rel in H3.
           simpl in H3.
           apply (H3 x) in H6.
           tauto.
        ++ destruct H7 as [val [lls [rrs]]].
           destruct H7, H8.
           specialize (H9 x H6).
           rewrite H7 in H0.
           destruct H0; [discriminate|].
           unfold get_tree_val in H0.
           lia.
      * specialize (IHMaxHeap2 R H4).
        rename IHMaxHeap2 into HH.
        destruct HH.
        ++ rewrite H7 in H4.
           unfold tree_set_rel in H4.
           simpl in H4.
           apply (H4 x) in H6.
           tauto.
        ++ destruct H7 as [val [lls [rrs]]].
           destruct H7, H8.
           specialize (H9 x H6).
           rewrite H7 in H1.
           destruct H1; [discriminate|].
           unfold get_tree_val in H1.
           lia.
Qed.