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
    exists v, ls, rs, t', d.
    tauto.
Qed.