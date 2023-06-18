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
  destruct t3 as [[flg val] tr].
  unfold swap_up_and_combine in H1; simpl in H1.
  destruct flg.
  + rewrite H3.
    rewrite <- H1.
    simpl.
    unfold_RELS_tac; intros; tauto.
  + rewrite H3.
    rewrite <- H1.
    simpl.
    unfold_RELS_tac; intros; tauto.
Qed.

Lemma heap_tree_up_Set_eq: forall (t t': tree_state),
  heap_tree_up t t' -> SetOf_tree_state t == SetOf_tree_state t'.
Proof.
  intros.
  unfold heap_tree_up in H.
  revert H; unfold_RELS_tac; intros.
  destruct H as [t0].
  destruct H.
  unfold tree_up_fail in H0.
  revert H0; simpl; intros.
  destruct H0; subst.
  induction_1n H.
  + reflexivity.
  + pose proof tree_up_succeed_Set_eq _ _ H1.
    revert H2; unfold_RELS_tac; intros.
    specialize (H2 a).
    rewrite H2.
    apply IHrt.
    tauto.
Qed.

Lemma Push_to_Set: forall (t t': tree) (s: SetZ) (v: Z),
  tree_set_rel t s -> (exists d, complete_tree_push d t) -> tree_push t v t' -> MaxHeap t ->
  exists s', tree_set_rel t' s' /\ s' == s ∪ Singleton v.
Proof.
  intros.
  clear H2.
  destruct H0 as [d].
  unfold tree_push in H1.
  destruct H1 as [ts [dep1 [dep2]]].
  exists (SetOf_tree t').
  split.
  + unfold tree_set_rel.
    tauto.
  + destruct H1, H2, H3.
    pose proof heap_tree_up_Set_eq _ _ H1.
    unfold tree_to_partial_tree in H5.
    pose proof tree_to_partial_tree_set_eq _ nil _ H2.
    simpl in H6.
    unfold SetOf_tree_state in H5; simpl in H5.
    rewrite <- H6 in H5.
    pose proof tree_compose_set_union (fst ts) (snd ts).
    rewrite <- H3 in H7.
    rewrite H7.
    assert (SetOf_tree t ∪ ∅ ∪ (Singleton v ∪ ∅ ∪ ∅) == s ∪ Singleton v). {
      rewrite ! Sets_union_empty.
      unfold tree_set_rel in H.
      assert (SetOf_tree t == s). {
        unfold_RELS_tac; apply H.
      }
      rewrite H8.
      reflexivity.
    }
    rewrite H8 in H5.
    rewrite H5.
    unfold_RELS_tac; tauto.
Qed.

Definition MaxSetElement(x: Z) (s: SetZ): Prop := 
  s x /\ (forall v, s v -> v <= x).

Lemma tree_max_set: forall (t: tree) (s: SetZ),
  tree_set_rel t s -> MaxHeap t -> (exists d, complete_tree_push d t) -> 
  (t = Leaf \/ (exists v ls rs, t = Node v ls rs /\ MaxSetElement v s)).
Proof.
  intros.
  clear H1.
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
           apply (H3 v0) in H6.
           tauto.
        ++ destruct H7 as [val [lls [rrs]]].
           destruct H7, H8.
           specialize (H9 v0 H6).
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
           apply (H4 v0) in H6.
           tauto.
        ++ destruct H7 as [val [lls [rrs]]].
           destruct H7, H8.
           specialize (H9 v0 H6).
           rewrite H7 in H1.
           destruct H1; [discriminate|].
           unfold get_tree_val in H1.
           lia.
Qed.

Lemma get_last_val_len_gt_1: forall (lt: partial_tree) (flg: bool) (v: Z) (t: tree),
  1 <= Zlength lt -> get_last_val (lt ++ [(flg,v,t)]) = get_last_val lt.
Proof.
  intros.
  destruct lt.
  + replace (Zlength []) with 0 in H by tauto.
    lia.
  + replace (p :: lt) with ([p] ++ lt) by reflexivity.
    rewrite <- app_assoc.
    simpl; tauto. 
Qed.

Lemma get_skipn_len_gt_1: forall (lt: partial_tree) (flg: bool) (v: Z) (t: tree),
  1 <= Zlength lt -> SetOf_partial_tree (skipn 1 (lt ++ [(flg,v,t)])) == SetOf_partial_tree (skipn 1 lt) ∪ (SetOf_tree t) ∪ (Singleton v).
Proof.
  intros.
  induction lt.
  + replace (Zlength []) with 0 in H by tauto.
    lia.
  + simpl. 
    destruct lt.
    - simpl; unfold_RELS_tac; tauto.
    - destruct p as [[flg0 val] tr].
      simpl.
      simpl in IHlt.
      rewrite IHlt.
      * unfold_RELS_tac; tauto.
      * rewrite Zlength_cons.
        pose proof initial_world.zlength_nonneg _ lt.
        lia.
Qed.

Lemma partial_tree_splt2: forall (lt1 lt2: partial_tree),
  SetOf_partial_tree (lt1 ++ lt2) == SetOf_partial_tree lt1 ∪ SetOf_partial_tree lt2.
Proof.
  intros.
  induction lt1.
  + simpl; unfold_RELS_tac; tauto.
  + destruct a as [[flg1 val] tr].
    simpl.
    rewrite IHlt1. 
    unfold_RELS_tac; tauto.
Qed.

Lemma partial_tree_split: forall (t: tree) (d: Z),
  t <> Leaf -> complete_tree_pop d t -> Singleton (get_last_val (tree_to_partial_tree_pop t d)) ∪ (SetOf_partial_tree (skipn 1 (tree_to_partial_tree_pop t d))) == SetOf_tree t.
Proof.
  intros.
  induction H0.
  + tauto.
  + unfold tree_to_partial_tree_pop.
    unfold tree_to_partial_tree_pop_fix;
    fold tree_to_partial_tree_pop_fix.
    apply full_tree_equiv1 in H1; rewrite ! H1.
    apply full_tree_equiv1 in H1.
    destruct ls.
    - simpl; inversion H0.
      replace (dep-2) with (-1) in H1 by lia.
      pose proof full_tree_gt_0 _ _ H1; lia.
    - pose proof tree_to_partial_tree_len (Node v0 ls1 ls2) (dep-1).
      replace ((false, v, rs) :: nil) with (nil ++ [(false, v, rs)]); [|rewrite app_nil_l; tauto].
      rewrite tree_to_partial_tree_pop_get.
      unfold tree_to_partial_tree_pop in H2.
      replace 1%nat with (Z.to_nat 1) by lia.
      rewrite Zskipn_app1; [|apply H2; discriminate].
      rewrite get_last_val_len_gt_1; [|apply H2; discriminate].
      replace (Z.to_nat 1) with 1%nat by lia.
      rewrite partial_tree_splt2.
      unfold tree_to_partial_tree_pop in IHcomplete_tree_pop.
      rewrite <- Sets_union_assoc.
      rewrite IHcomplete_tree_pop; [|discriminate].
      simpl; unfold_RELS_tac; tauto.
  + unfold tree_to_partial_tree_pop.
    unfold tree_to_partial_tree_pop_fix;
    fold tree_to_partial_tree_pop_fix.
    pose proof complete_tree_pop_not_fullb _ _ H1.
    replace (dep-1-1) with (dep-2) in H2 by lia.
    rewrite H2.
    destruct rs.
    - inversion H1.
      rewrite H3 in H0.
      inversion H0.
      simpl; unfold_RELS_tac; tauto.
      pose proof full_tree_gt_0 _ _ H5; lia.
    - pose proof tree_to_partial_tree_len (Node v0 rs1 rs2) (dep-1).
      replace ((true, v, ls) :: nil) with (nil ++ [(true, v, ls)]); [|rewrite app_nil_l; tauto].
      rewrite tree_to_partial_tree_pop_get.
      unfold tree_to_partial_tree_pop in H3.
      replace 1%nat with (Z.to_nat 1) by lia.
      rewrite Zskipn_app1; [|apply H3; discriminate].
      rewrite get_last_val_len_gt_1; [|apply H3; discriminate].
      replace (Z.to_nat 1) with 1%nat by lia.
      rewrite partial_tree_splt2.
      unfold tree_to_partial_tree_pop in IHcomplete_tree_pop.
      rewrite <- Sets_union_assoc.
      rewrite IHcomplete_tree_pop; [|discriminate].
      simpl; unfold_RELS_tac; tauto.
Qed.

Lemma tree_to_partial_tree_pop_set_eq: forall (t: tree) (lt: partial_tree) (d: Z),
  complete_tree_pop d t -> SetOf_tree t ∪ SetOf_partial_tree lt == SetOf_partial_tree (tree_to_partial_tree_pop_fix lt t d).
Proof.
  intros.
  revert lt.
  induction H; intros.
  + simpl.
    rewrite Sets_empty_union.
    reflexivity.
  + simpl.
    apply full_tree_equiv1 in H0.
    rewrite H0.
    rewrite <- IHcomplete_tree_pop.
    simpl.
    unfold_RELS_tac; intros; tauto.
  + simpl.
    pose proof complete_tree_pop_not_fullb _ _ H0.
    replace (dep-1-1) with (dep-2) in H1 by lia.
    rewrite H1.
    rewrite <- IHcomplete_tree_pop.
    simpl.
    unfold_RELS_tac; intros; tauto.
Qed.

Lemma tree_cut_last_set: forall (ls rs: tree) (d v: Z),
  tree_size (Node v ls rs) >= 2 -> complete_tree_pop d (Node v ls rs) -> (SetOf_tree (tree_cut_last ls rs d)) ∪ Singleton v == SetOf_tree (Node v ls rs).
Proof.
  intros.
  inversion H0; subst.
  + unfold tree_cut_last.
    apply full_tree_equiv1 in H5.
    rewrite H5.
    unfold SetOf_tree; fold SetOf_tree.
    rewrite tree_compose_set_union. 
    inversion H3.
    - replace (d-2) with (-1) in H5 by lia.
      apply full_tree_equiv1 in H5.
      pose proof full_tree_gt_0 _ _ H5; lia.
    - unfold tree_to_partial_tree_pop.
      simpl SetOf_tree.
      rewrite Sets_empty_union.
      rewrite partial_tree_split.
      * simpl; unfold_RELS_tac; tauto.
      * discriminate.
      * rewrite H4; tauto.
    - unfold tree_to_partial_tree_pop.
      simpl SetOf_tree.
      rewrite Sets_empty_union.
      rewrite partial_tree_split.
      * simpl; unfold_RELS_tac; tauto.
      * discriminate.
      * rewrite H4; tauto.
  + unfold tree_cut_last.
    pose proof complete_tree_pop_not_fullb _ _ H5.
    replace (d-1-1) with (d-2) in H1 by lia.
    rewrite H1.
    unfold SetOf_tree; fold SetOf_tree.
    rewrite tree_compose_set_union. 
    inversion H5.
    - rewrite H2 in H3.
      inversion H3.
      * simpl in H.
        rewrite <- H4 in H.
        rewrite <- H7 in H.
        simpl in H; lia.
      * pose proof full_tree_gt_0 _ _ H7; lia.
    - unfold tree_to_partial_tree_pop.
      rewrite ! Sets_union_assoc.
      assert( (Singleton (get_last_val (tree_to_partial_tree_pop_fix []%list (Node v0 ls0 rs0) (d - 1))) ∪ (SetOf_tree ls ∪ (SetOf_tree Leaf ∪ (SetOf_partial_tree (skipn 1 (tree_to_partial_tree_pop_fix []%list (Node v0 ls0 rs0) (d - 1))) ∪ Singleton v)))) == ((Singleton (get_last_val (tree_to_partial_tree_pop_fix []%list (Node v0 ls0 rs0) (d - 1))) ∪ SetOf_partial_tree (skipn 1 (tree_to_partial_tree_pop_fix []%list (Node v0 ls0 rs0) (d - 1))) )∪(SetOf_tree Leaf ∪ Singleton v ∪ SetOf_tree ls)) ). {
        unfold_RELS_tac.
        tauto.
      }
      rewrite H7.
      rewrite partial_tree_split.
      * simpl; unfold_RELS_tac; tauto.
      * discriminate.
      * rewrite H6; tauto.
    - unfold tree_to_partial_tree_pop.
      rewrite ! Sets_union_assoc.
      assert( (Singleton (get_last_val (tree_to_partial_tree_pop_fix []%list (Node v0 ls0 rs0) (d - 1))) ∪ (SetOf_tree ls ∪ (SetOf_tree Leaf ∪ (SetOf_partial_tree (skipn 1 (tree_to_partial_tree_pop_fix []%list (Node v0 ls0 rs0) (d - 1))) ∪ Singleton v)))) == ((Singleton (get_last_val (tree_to_partial_tree_pop_fix []%list (Node v0 ls0 rs0) (d - 1))) ∪ SetOf_partial_tree (skipn 1 (tree_to_partial_tree_pop_fix []%list (Node v0 ls0 rs0) (d - 1))) )∪(SetOf_tree Leaf ∪ Singleton v ∪ SetOf_tree ls)) ). {
        unfold_RELS_tac.
        tauto.
      }
      rewrite H7.
      rewrite partial_tree_split.
      * simpl; unfold_RELS_tac; tauto.
      * discriminate.
      * rewrite H6; tauto.
Qed.

Lemma tree_down_succeed_Set_eq: forall (t t': tree_state),
  tree_down_succeed t t' -> SetOf_tree_state t == SetOf_tree_state t'.
Proof.
  intros.
  unfold tree_down_succeed in H.
  destruct H.
  destruct x as [[flg v] tr].
  destruct H.
  destruct H0 as [v0 [ls [rs]]].
  destruct H0.
  destruct H1.
  + destruct H1, H2.
    unfold swap_down_left in H3.
    destruct H3 as [vl [lls [lrs]]].
    destruct H3, H4.
    injection H5; intros; subst.
    unfold SetOf_tree_state.
    rewrite <- H.
    rewrite H0, H4.
    simpl.
    unfold_RELS_tac; tauto.
  + destruct H1.
    - destruct H1, H2.
      unfold swap_down_right in H3.
      destruct H3 as [vr [rls [rrs]]].
      destruct H3, H4.
      injection H5; intros; subst.
      unfold SetOf_tree_state.
      rewrite <- H.
      rewrite H0, H4.
      simpl.
      unfold_RELS_tac; tauto.
    - destruct H1, H2, H3, H3.
      * unfold swap_down_right in H4.
        destruct H4 as [vr [rls [rrs]]].
        destruct H4, H5.
        injection H6; intros; subst.
        unfold SetOf_tree_state.
        rewrite <- H.
        rewrite H0, H5.
        simpl; unfold_RELS_tac; tauto.
      * unfold swap_down_left in H4.
        destruct H4 as [vl [lls [lrs]]].
        destruct H4, H5.
        injection H6; intros; subst.
        unfold SetOf_tree_state.
        rewrite <- H.
        rewrite H0, H5.
        simpl; unfold_RELS_tac; tauto.
Qed.

Lemma heap_tree_down_Set_eq: forall (t t': tree_state),
  heap_tree_down t t' -> SetOf_tree_state t == SetOf_tree_state t'.
Proof.
  intros.
  unfold heap_tree_down in H.
  revert H; unfold_RELS_tac; intros.
  destruct H as [t0].
  destruct H.
  unfold tree_down_fail in H0.
  revert H0; unfold_RELS_tac; intros.
  destruct H0; subst.
  induction_1n H; [reflexivity|].
  pose proof tree_down_succeed_Set_eq _ _ H1.
  revert H2; unfold_RELS_tac; intros.
  rewrite H2.
  rewrite IHrt; tauto.
Qed.

Lemma Pop_from_Set: forall (t t': tree) (s: SetZ),
  tree_set_rel t s -> (exists d, complete_tree_pop d t) -> MaxHeap t -> tree_pop t t' ->
  exists s', tree_set_rel t' s' /\
  ((tree_size t <= 1 /\ s' = ∅) \/ (tree_size t >= 2 /\ (exists x, s' ∪ Singleton x == s /\ MaxSetElement x s))).
Proof.
  intros.
  unfold tree_pop in H2.
  destruct H2. 1: {
    destruct H2.
    exists ∅.
    split.
    + rewrite H3.
      unfold tree_set_rel; simpl.
      reflexivity.
    + left. tauto. 
  }
  destruct H2.
  rename H2 into HH.
  rename H3 into H2.
  destruct H2 as [v [ls [rs [ts [d0] ] ] ] ].
  destruct H2, H3, H4; subst.
  pose proof complete_tree_equality (Node v ls rs).
  apply H2 in H0.
  pose proof tree_max_set _ _ H H1 H0.
  destruct H5; [discriminate|].
  destruct H5 as [v0 [ls0 [rs0]]].
  destruct H5.
  injection H5; intros; subst.
  pose proof heap_tree_down_Set_eq _ _ H4.
  unfold SetOf_tree_state in H7; simpl in H7.
  rewrite Sets_empty_union in H7.
  exists (SetOf_tree (tree_cut_last ls0 rs0 d0)).
  split.
  + unfold tree_set_rel.
    pose proof tree_compose_set_union (fst ts) (snd ts).
    revert H8 H7; unfold_RELS_tac; intros.
    rewrite (H8 x).
    rewrite H7.
    tauto.
  + right.
    split; [lia|].
    exists v0.
    split; [|tauto].
    pose proof tree_cut_last_set _ _ _ _ HH H3.
    rewrite H8.
    unfold tree_set_rel in H.
    unfold_RELS_tac.
    tauto.
Qed.
