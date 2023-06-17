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
Require Import cprogs.heap.math_prop.

Require Import SetsClass.SetsClass.
Local Open Scope sets.
Import SetsNotation.

Inductive tree: Type :=
  | Leaf: tree
  | Node (v: Z) (ls: tree) (rs: tree): tree.

(* Fixpoint list_nth_on_tree (l: list Z) (n: Z) (tr: tree): Prop :=
  match tr with
    | Leaf => Zlength l <= n
    | Node v ls rs =>
        0 <= n < Zlength l /\ Znth n l = v /\
        list_nth_on_tree l (n * 2) ls /\ list_nth_on_tree l (n * 2 + 1) rs
  end. *)

Inductive list_nth_on_tree (l: list Z) (n: Z): tree -> Prop :=
  | list_nth_on_tree_Leaf: list_nth_on_tree l n Leaf
  | list_nth_on_tree_Node: forall v ls rs,
      1 <= n < Zlength l -> Znth n l = v ->
      list_nth_on_tree l (n * 2) ls -> list_nth_on_tree l (n * 2 + 1) rs ->
      list_nth_on_tree l n (Node v ls rs).

Inductive full_tree (dep: Z): tree -> Prop :=
  | full_tree_Leaf: dep = 0 -> full_tree dep Leaf
  | full_tree_Node: forall v ls rs,
      full_tree (dep - 1) ls -> full_tree (dep - 1) rs ->
      full_tree dep (Node v ls rs).

Fixpoint full_tree_b (dep: Z) (t : tree): bool :=
  match t with
  | Leaf => dep =? 0
  | Node v ls rs => 
      full_tree_b (dep - 1) ls && full_tree_b (dep - 1) rs
  end.


Inductive complete_tree_pop (dep: Z): tree -> Prop :=
  | complete_tree_pop_Leaf: dep = 0 -> complete_tree_pop dep Leaf
  | complete_tree_pop_left_hole: forall v ls rs,
      complete_tree_pop (dep - 1) ls -> full_tree (dep - 2) rs ->
      complete_tree_pop dep (Node v ls rs)
  | complete_tree_pop_right_hole: forall v ls rs,
      full_tree (dep - 1) ls -> complete_tree_pop (dep - 1) rs ->
      complete_tree_pop dep (Node v ls rs).

Inductive complete_tree_push (dep: Z): tree -> Prop :=
  | complete_tree_push_Leaf: dep = 1 -> complete_tree_push dep Leaf
  | complete_tree_push_left_full: forall v ls rs,
      full_tree (dep - 1) ls -> complete_tree_push (dep - 1) rs ->
      complete_tree_push dep (Node v ls rs)
  | complete_tree_push_right_full: forall v ls rs,
      complete_tree_push (dep - 1) ls -> full_tree (dep - 2) rs ->
      complete_tree_push dep (Node v ls rs).

Lemma full_tree_complete_tree_pop: forall dep t,
  full_tree dep t -> complete_tree_pop dep t.
Proof.
  intros.
  induction H.
  + apply complete_tree_pop_Leaf; auto.
  + apply complete_tree_pop_right_hole; auto.
Qed.

Lemma full_tree_complete_tree_push: forall dep t,
  full_tree dep t -> complete_tree_push (dep + 1) t.
Proof.
  intros.
  induction H.
  + apply complete_tree_push_Leaf; lia.
  + apply complete_tree_push_right_full.
    - replace (dep + 1 - 1) with (dep - 1 + 1) by lia; auto.
    - replace (dep + 1 - 2) with (dep - 1) by lia; auto. 
Qed.

Lemma not_full_tree_complete_tree_imp_pop: forall dep t,
  ~ full_tree (dep - 1) t ->
  complete_tree_push dep t -> complete_tree_pop dep t.
Proof.
  intros.
  revert H; induction H0; intros.
  + pose proof full_tree_Leaf (dep - 1) ltac:(lia).
    contradiction.
  + destruct (classic (full_tree (dep - 2) rs)).
    - pose proof full_tree_complete_tree_pop _ _ H.
      apply complete_tree_pop_left_hole; auto.
    - replace (dep - 1 - 1) with (dep - 2) in IHcomplete_tree_push by lia.
      specialize (IHcomplete_tree_push H2).
      apply complete_tree_pop_right_hole; auto.
  + destruct (classic (full_tree (dep - 2) ls)).
    - replace (dep - 2) with ((dep - 1) - 1) in H by lia.
      replace (dep - 2) with ((dep - 1) - 1) in H2 by lia.
      pose proof full_tree_Node _ v ls rs H2 H; contradiction.
    - replace (dep - 1 - 1) with (dep - 2) in IHcomplete_tree_push by lia.
      specialize (IHcomplete_tree_push H2).
      apply complete_tree_pop_left_hole; auto.
Qed.

Lemma not_full_tree_complete_tree_imp_push: forall dep t,
  ~ full_tree dep t ->
  complete_tree_pop dep t -> complete_tree_push dep t.
Proof.
  intros.
  revert H; induction H0; intros.
  + pose proof full_tree_Leaf dep ltac:(lia).
    contradiction.
  + destruct (classic (full_tree (dep - 1) ls)).
    - pose proof full_tree_complete_tree_push _ _ H.
      apply complete_tree_push_left_full; auto.
      replace (dep - 2 + 1) with (dep - 1) in H3 by lia; auto.
    - specialize (IHcomplete_tree_pop H2).
      apply complete_tree_push_right_full; auto.
  + destruct (classic (full_tree (dep - 1) rs)).
    - pose proof full_tree_Node _ v ls rs H H2; contradiction.
    - specialize (IHcomplete_tree_pop H2).
      apply complete_tree_push_left_full; auto.
Qed.

Lemma complete_tree_equality: forall t,
  (exists d, complete_tree_pop d t) <-> (exists d, complete_tree_push d t).
Proof.
  intros; split; intros; destruct H as [d H].
  + destruct (classic (full_tree d t)).
    - exists (d + 1).
      apply full_tree_complete_tree_push; auto.
    - exists d.
      apply not_full_tree_complete_tree_imp_push; auto.
  + destruct (classic (full_tree (d - 1) t)).
    - exists (d - 1).
      apply full_tree_complete_tree_pop; auto.
    - exists d.
      apply not_full_tree_complete_tree_imp_pop; auto.   
Qed.

Fixpoint last_index (d: Z) (rt_n: Z) (tr: tree): Z :=
  match tr with
    | Leaf => rt_n / 2
    | Node v ls rs =>
      if (full_tree_b (d - 2) rs) then
        last_index (d - 1) (rt_n * 2) ls
      else
        last_index (d - 1) (rt_n * 2 + 1) rs
  end.

Fixpoint next_index (d: Z) (rt_n: Z) (tr: tree): Z :=
  match tr with
    | Leaf => rt_n
    | Node v ls rs =>
      if (full_tree_b (d - 1) ls) then
        next_index (d - 1) (rt_n * 2 + 1) rs
      else
        next_index (d - 1) (rt_n * 2) ls
  end.

Definition partial_tree: Type := list (bool * Z * tree).
(* true:right_son is cut
   false:left_son is cut*)
Definition tree_state: Type := partial_tree * tree.

Definition legal_tree_state (t: tree_state): Prop :=
  exists v ls rs, (snd t) = Node v ls rs.

Definition swap_up_and_combine (v: Z) (ls rs: tree) (t2: bool * Z * tree): tree :=
  match (fst (fst t2)) with
  | true => Node v (snd t2) (Node (snd (fst t2)) ls rs)  
  | false => Node v (Node (snd (fst t2)) ls rs) (snd t2)
  end.

Definition get_tree_val (t: tree): Z :=
  match (t) with
  | Leaf => default
  | Node v l r => v
  end.

Definition left_son_check_tree (v: Z) (ls rs: tree): Prop:=
  ~(ls = Leaf) /\ (get_tree_val ls) > v.

Definition right_son_check_tree (v: Z) (ls rs: tree): Prop:=
  ~(rs = Leaf) /\ (get_tree_val rs) > v.

Definition swap_down_left (v: Z) (ls rs t2: tree) (t: bool*Z*tree): Prop:=
  exists vl lls lrs, ls = (Node vl lls lrs) /\
  t2 = (Node v lls lrs) /\ t = (false, vl, rs).

Definition swap_down_right (v: Z) (ls rs t2: tree) (t: bool*Z*tree): Prop:=
  exists vr rls rrs, rs = (Node vr rls rrs) /\
  t2 = (Node v rls rrs) /\ t = (true, vr, ls).

Ltac try_unfold_tree :=
  unfold swap_down_left; unfold left_son_check_tree; 
  unfold swap_down_right; unfold right_son_check_tree;
  unfold get_tree_val; unfold legal_tree_state; simpl.

(* Fixpoint MaxHeap(t: tree): Prop :=
  match t with 
    | Leaf => True
    | Node v ls rs => 
      (ls = Leaf \/ (get_tree_val ls) <= v) /\
      (rs = Leaf \/ (get_tree_val rs) <= v) /\ 
      MaxHeap ls /\ MaxHeap rs
  end. *)

Inductive MaxHeap(t: tree): Prop :=
  | MaxHeap_Leaf: t = Leaf -> MaxHeap t
  | MaxHeap_Node: forall v ls rs,
      t = Node v ls rs -> MaxHeap ls -> MaxHeap rs -> 
      (ls = Leaf \/ (get_tree_val ls) <= v) ->
      (rs = Leaf \/ (get_tree_val rs) <= v) -> MaxHeap t.

(* Fixpoint MaxHeap_partial_tree_v(lt: partial_tree) (vt: Z): Prop :=
  match lt with
    | nil => True
    | (fl, v, t) :: lt0 => (MaxHeap t) /\ (t = Leaf \/ (get_tree_val t) <= v)
                          /\ (vt <= v) /\ (MaxHeap_partial_tree_v lt0 v)
  end. *)

Inductive MaxHeap_partial_tree_v(lt: partial_tree) (vt: Z): Prop :=
  | MaxHeap_partial_tree_v_nil: lt = nil -> MaxHeap_partial_tree_v lt vt
  | MaxHeap_partial_tree_v_app: forall fl v t lt0,
      lt = (fl, v, t) :: lt0 -> MaxHeap_partial_tree_v lt0 v ->
      MaxHeap t -> (t = Leaf \/ (get_tree_val t) <= v) ->
      vt <= v -> MaxHeap_partial_tree_v lt vt.
  

Definition MaxHeap_partial_tree(lt: partial_tree): Prop :=
  match lt with
    | nil => True
    | (fl, v, t) :: lt0 => (MaxHeap t) /\ (t = Leaf \/ (get_tree_val t) <= v) /\ (MaxHeap_partial_tree_v lt0 v)
  end.

Lemma MaxHeap_partial_tree_v_impl: forall (lt: partial_tree) (v: Z),
  MaxHeap_partial_tree_v lt v -> MaxHeap_partial_tree lt.
Proof.
  intros.
  destruct lt; [simpl; tauto|].
  destruct p as [[flg val] t].
  unfold MaxHeap_partial_tree.
  inversion H; [discriminate|].
  injection H0; intros; subst.
  tauto.
Qed.

Lemma MaxHeap_partial_tree_v_change_v: forall (lt: partial_tree) (v1 v2: Z),
  MaxHeap_partial_tree_v lt v1 -> v2 <= v1 -> MaxHeap_partial_tree_v lt v2.
Proof.
  intros.
  inversion H.
  + apply MaxHeap_partial_tree_v_nil; tauto.
  + apply (MaxHeap_partial_tree_v_app lt v2 fl v t lt0); try tauto.
    lia.
Qed.

Fixpoint tree_compose (pt: partial_tree) (t: tree) :=
  match pt with
    | nil => t
    | (true, v, son) :: pt0  => tree_compose pt0 (Node v son t)
    | (false, v, son) :: pt0 => tree_compose pt0 (Node v t son)
  end.

Lemma tree_compose_append: forall pt t flg v ch,
  tree_compose (pt ++ [(flg, v, ch)]) t = 
  if (flg) then
    Node v ch (tree_compose pt t)
  else
    Node v (tree_compose pt t) ch.
Proof.
  intros pt.
  induction pt.
  + simpl. reflexivity.
  + intros; simpl; simpl in IHpt.
    destruct a as [[flg' v'] ch'].
    destruct flg', flg; simpl.
    - specialize (IHpt (Node v' ch' t) true v ch).
      simpl in IHpt. rewrite IHpt. reflexivity.
    - specialize (IHpt (Node v' ch' t) false v ch).
      simpl in IHpt. rewrite IHpt. reflexivity.
    - specialize (IHpt (Node v' t ch') true v ch).
      simpl in IHpt. rewrite IHpt. reflexivity.
    - specialize (IHpt (Node v' t ch') false v ch).
      simpl in IHpt. rewrite IHpt. reflexivity.  
Qed.

Fixpoint tree_size (t: tree): Z :=
  match t with
    | Leaf => 0
    | Node v ls rs => 1 + (tree_size ls) + (tree_size rs)
  end.

Fixpoint partial_tree_size (pt: partial_tree): Z :=
  match pt with
    | nil => 0
    | (fl, v, t) :: pt0 => 1 + (tree_size t) + (partial_tree_size pt0)
  end.

Lemma partial_tree_append_size: forall pt flg v ch,
  partial_tree_size (pt ++ [(flg, v, ch)]) = 
  1 + (tree_size ch) + (partial_tree_size pt).
Proof.
  intros pt.
  induction pt; simpl; intros.
  + lia.
  + destruct a as [[flga va] ta].
    rewrite IHpt; lia. 
Qed.

Definition list_on_tree (l: list Z) (tr: tree): Prop :=
  list_nth_on_tree l 1 tr /\ tree_size tr = Zlength l - 1 /\
  exists d, complete_tree_push d tr. 

Lemma tree_size_nonneg: forall t,
  0 <= (tree_size t).
Proof.
  intros.
  induction t; simpl; lia.  
Qed.
Lemma partial_tree_size_nonneg: forall pt,
  0 <= (partial_tree_size pt).
Proof.
  intros.
  induction pt; simpl.
  + lia.
  + destruct a.
    destruct p.
    destruct b; pose proof tree_size_nonneg t; lia. 
Qed.

Lemma tree_compose_size: forall pt t,
  tree_size (tree_compose pt t) = (tree_size t) + (partial_tree_size pt).
Proof.
  (* intros ?. *)
  induction pt.
  + simpl; lia. 
  + intros.
    induction t.
    - simpl. 
      destruct a.
      destruct p; destruct b.
      * rewrite IHpt; simpl; lia.
      * rewrite IHpt; simpl; lia.
    - simpl.
      destruct a.
      destruct p; destruct b.
      * rewrite IHpt.
        simpl in IHt1, IHt2.
        rewrite IHpt in IHt1, IHt2.
        simpl; lia.
      * rewrite IHpt.
        simpl in IHt1, IHt2.
        rewrite IHpt in IHt1, IHt2.
        simpl; lia.
Qed.

Example tree4: tree := Node 4 Leaf Leaf.
Example tree5: tree := Node 5 Leaf Leaf.
Example tree6: tree := Node 6 Leaf Leaf.
Example tree3: tree := Node 3 Leaf Leaf.
Example tree2: tree := Node 2 tree4 tree5.
Example tree1: tree := Node 1 tree2 tree3.

Definition list_example: list Z := [0; 1; 2; 3; 4; 5].


Lemma tree_compose_emp: forall pt t,
  tree_compose pt t = t -> pt = nil.
Proof.
  intros.
  destruct pt.
  + reflexivity.
  + pose proof tree_compose_size (p :: pt) t.
    assert (tree_size t = tree_size (tree_compose (p :: pt) t)). {
      rewrite H; reflexivity.
    }
    rewrite <- H1 in H0.
    unfold partial_tree_size in H0; fold partial_tree_size in H0.
    destruct p; destruct p.
    pose proof tree_size_nonneg t0.
    pose proof partial_tree_size_nonneg pt.
    lia.
Qed.

Lemma tree_compose_MaxHeap2: forall (lt: partial_tree) (t: tree), 
  MaxHeap t -> MaxHeap_partial_tree lt -> (t = Leaf \/ MaxHeap_partial_tree_v lt (get_tree_val t)) -> MaxHeap (tree_compose lt t).
Proof.
  intros.
  revert t H H1.
  induction lt; intros; [simpl; tauto|].
  destruct a as [[flg val] t2].
  unfold MaxHeap_partial_tree in H0.
  destruct H0, H2.
  pose proof MaxHeap_partial_tree_v_impl _ _ H3.
  destruct flg.
  - assert (MaxHeap (Node val t2 t)). {
      apply (MaxHeap_Node (Node val t2 t) val t2 t); try tauto.
      destruct H1; [left; tauto|].
      inversion H1; [discriminate|].
      injection H5; intros; subst.
      tauto.
    }
    unfold tree_compose; fold tree_compose.
    destruct H1.
    * apply (IHlt H4 (Node val t2 t) H5 ltac:(tauto)).
    * apply (IHlt H4 (Node val t2 t) H5 ltac:(tauto)).
  - assert (MaxHeap (Node val t t2)). {
      apply (MaxHeap_Node (Node val t t2) val t t2); try tauto.
      destruct H1; [left; tauto|].
      inversion H1; [discriminate|].
      injection H5; intros; subst.
      tauto.
    }
    unfold tree_compose; fold tree_compose.
    destruct H1.
    * apply (IHlt H4 (Node val t t2) H5 ltac:(tauto)).
    * apply (IHlt H4 (Node val t t2) H5 ltac:(tauto)).
Qed.

Lemma tree_compose_MaxHeap: forall (lt: partial_tree) (t: tree), 
  MaxHeap t -> ((t = Leaf /\ MaxHeap_partial_tree lt) \/ MaxHeap_partial_tree_v lt (get_tree_val t)) -> MaxHeap (tree_compose lt t).
Proof.
  intros.
  destruct H0.
  + destruct H0.
    apply (tree_compose_MaxHeap2 _ _ H H1 ltac:(tauto)).
  + pose proof MaxHeap_partial_tree_v_impl _ _ H0.
    apply (tree_compose_MaxHeap2 _ _ H H1 ltac:(tauto)).
Qed.

Definition MaxHeap_no_rt(t: tree): Prop :=
  exists v ls rs, t = (Node v ls rs) /\ MaxHeap ls /\ MaxHeap rs.

(* p 为洞的位置且洞在 Zlength l 内 *)
Inductive list_on_partial_tree (l: list Z) (p: Z) (lt: partial_tree) : Prop :=
  | nil_partial_tree: p = 1 -> lt = nil -> list_on_partial_tree l p lt
  | cons_partial_tree: forall flg v t lt0, 
    lt = (flg, v, t) :: lt0 ->
    1 <= p / 2 < Zlength l -> 
    p = (p / 2) * 2 + (if flg then 1 else 0) ->
    Znth (p / 2) l = v -> 
    list_nth_on_tree l (p + (if flg then -1 else 1)) t -> 
    list_on_partial_tree l (p / 2) lt0 -> 
    list_on_partial_tree l p lt.

Definition is_child_index (ch: Z) (p: Z) : Prop :=
  ch >= p /\ exists n, (Z.shiftr ch n) = p.

Lemma is_child_index_self: forall (ch: Z) (p: Z),
  ch = p -> is_child_index ch p.
Proof.
  intros.
  unfold is_child_index.
  split; [lia |].
  exists 0.
  rewrite Z.shiftr_0_r; lia.
Qed.

Lemma less_is_not_child_index: forall (ch: Z) (p: Z),
  ch < p -> ~ is_child_index ch p.
Proof.
  unfold not, is_child_index.
  intros.
  destruct H0.
  lia.
Qed.

Lemma is_child_index_gp: forall (p: Z) (ch: Z),
  p >= 0 -> is_child_index ch p -> is_child_index ch (p / 2).
Proof.
  intros.
  destruct H0 as [? [x ?] ].
  unfold is_child_index.
  split.
  + pose proof Z.div_le_upper_bound p 2 p ltac:(lia) ltac:(lia).
    lia. 
  + exists (x + 1).
    replace (p / 2) with (Z.shiftr p 1) by (apply Z.shiftr_div_pow2; lia).
  rewrite <- H1.
  rewrite Z.shiftr_shiftr by lia.
  auto.
Qed.

Lemma is_child_index_gp_inv_left: forall (p: Z) (ch: Z),
  p >= 0 -> is_child_index ch (p * 2) -> is_child_index ch p.
Proof.
  intros.
  pose proof is_child_index_gp (p * 2) ch ltac:(lia) H0.
  replace (p * 2 / 2) with p in H1; [auto | ].
  rewrite Z.div_mul by lia.
  auto.
Qed.

Lemma is_child_index_gp_inv_right: forall (p: Z) (ch: Z),
  p >= 0 -> is_child_index ch (p * 2 + 1) -> is_child_index ch p.
Proof.
  intros.
  pose proof is_child_index_gp (p * 2 + 1) ch ltac:(lia) H0.
  replace ((p * 2 + 1) / 2) with p in H1; [auto | ].
  rewrite Z.div_add_l by lia.
  rewrite Z.div_1_l by lia.
  lia.
Qed.

Lemma rchild_is_not_lchild: forall (ch: Z) (p: Z) (pp: Z),
  pp >= 1 -> 
  p = pp * 2 + 1 -> is_child_index ch p -> ~is_child_index ch (p + -1).
Proof.
  intros.
  destruct H1 as [? [n ?] ].
  unfold not; intros.
  destruct H3 as [? [n' ?] ].
  pose proof Z.log2_shiftr ch n ltac:(lia).
  rewrite H2 in H5.
  pose proof Z.log2_shiftr ch n' ltac:(lia).
  rewrite H4 in H6.
  replace (p + -1) with (2 * pp) in H6 by lia.
  replace p with (2 * pp + 1) in H5 by lia.
  rewrite Z.log2_double in H6 by lia.
  rewrite Z.log2_succ_double in H5 by lia.
  rewrite H5 in H6.
  pose proof Z.log2_nonneg pp.
  replace (Z.max 0 (Z.log2 ch - n)) with (Z.log2 ch - n) in H6 by lia.
  replace (Z.max 0 (Z.log2 ch - n')) with (Z.log2 ch - n') in H6 by lia.
  assert (n = n') by lia.
  subst.
  lia.
Qed.

Lemma lchild_is_not_rchild: forall (ch: Z) (p: Z) (pp: Z),
  pp >= 1 -> 
  p = pp * 2 -> is_child_index ch p -> ~is_child_index ch (p + 1).
Proof.
  intros.
  destruct H1 as [? [n ?] ].
  unfold not; intros.
  destruct H3 as [? [n' ?] ].
  pose proof Z.log2_shiftr ch n ltac:(lia).
  rewrite H2 in H5.
  pose proof Z.log2_shiftr ch n' ltac:(lia).
  rewrite H4 in H6.
  replace (p + 1) with (2 * pp + 1) in H6 by lia.
  replace p with (2 * pp) in H5 by lia.
  rewrite Z.log2_double in H5 by lia.
  rewrite Z.log2_succ_double in H6 by lia.
  rewrite H5 in H6.
  pose proof Z.log2_nonneg pp.
  replace (Z.max 0 (Z.log2 ch - n)) with (Z.log2 ch - n) in H6 by lia.
  replace (Z.max 0 (Z.log2 ch - n')) with (Z.log2 ch - n') in H6 by lia.
  assert (n = n') by lia.
  subst.
  lia.
Qed.

Lemma list_nth_on_tree_upd: forall (l: list Z) (t: tree) (n: Z) (v: Z) (p: Z),
  list_nth_on_tree l n t ->
  0 <= p < Zlength l -> ~is_child_index p n ->
  list_nth_on_tree (upd_Znth p l v) n t.
Proof.
  intros.
  induction H; subst.
  + constructor; auto.
  + eapply list_nth_on_tree_Node; eauto.
    - rewrite upd_Znth_Zlength by lia.
      lia.
    - assert (p = n \/ p <> n) by lia.
      destruct H2.
      * pose proof is_child_index_self p n H2; tauto.
      * rewrite upd_Znth_diff by lia; tauto.
    - apply IHlist_nth_on_tree1.
      unfold not; intros.
      pose proof is_child_index_gp_inv_left n p ltac:(lia) H2.
      auto.
    - apply IHlist_nth_on_tree2.
      unfold not; intros.
      pose proof is_child_index_gp_inv_right n p ltac:(lia) H2.
      auto.
Qed.

Lemma list_on_partial_tree_upd: forall l ch p lt v,
  p < Zlength l ->
  ch < Zlength l -> 
  is_child_index ch p ->
  list_on_partial_tree l p lt -> list_on_partial_tree (upd_Znth ch l v) p lt.
Proof.
  intros.
  induction H2.
  + subst; constructor; auto.
  + remember H1 as H1'; clear HeqH1'.
    destruct H1 as [? [n ?] ].
    destruct flg; eapply cons_partial_tree; eauto.
    - rewrite upd_Znth_Zlength by lia; lia. 
    - rewrite upd_Znth_diff by lia; auto.
    - simpl.
      apply list_nth_on_tree_upd; [auto | lia |].
      apply rchild_is_not_lchild with (pp := (p / 2));
        [lia | lia | auto].
    - pose proof is_child_index_gp p ch ltac:(lia) H1'.
      specialize (IHlist_on_partial_tree ltac:(lia) H9).
      auto.
    - rewrite upd_Znth_Zlength by lia; lia.
    - rewrite upd_Znth_diff by lia; auto.
    - simpl.
      apply list_nth_on_tree_upd; [auto | lia |].
      apply lchild_is_not_rchild with (pp := (p / 2));
        [lia | lia | auto].
    - pose proof is_child_index_gp p ch ltac:(lia) H1'.
      specialize (IHlist_on_partial_tree ltac:(lia) H9).
      auto.  
Qed.

(* Fixpoint list_on_tree_state_fix(l: list Z) (ind: Z) (lt: partial_tree) (t: tree): Prop :=
  (list_nth_on_tree l ind t ) /\ 
  match lt with
    | nil => ind = 1
    | (true, v, tl) :: lt0 => list_on_tree_state_fix l (ind/2) lt0 (Node v tl t) /\ ind > 1 /\ ind =  (ind/2) * 2 + 1
    | (false, v, tr) :: lt0 => list_on_tree_state_fix l (ind/2) lt0 (Node v t tr) /\ ind > 1 /\ ind =  (ind/2) * 2
  end. *)

Definition list_on_tree_state_fix(l: list Z) (p: Z) (lt: partial_tree) (t: tree): Prop :=
  list_nth_on_tree l p t /\ list_on_partial_tree l p lt /\ tree_size (tree_compose lt t) = Zlength l - 1 /\ exists d, complete_tree_push d (tree_compose lt t).

Lemma nil_rev_nil: forall {A: Type} (l: list A),
  nil = rev l -> l = nil.
Proof.
  intros.
  destruct l; auto.
  simpl in H.
  assert (rev (rev l ++ [a]) = rev []%list) by (rewrite <- H; tauto).
  simpl in H0.
  rewrite rev_unit in H0.
  discriminate.
Qed.

Lemma list_on_tree_state_compose: forall l p lt t,
  list_on_tree_state_fix l p lt t -> list_on_tree l (tree_compose lt t).
Proof.
  intros.
  unfold list_on_tree_state_fix in H.
  destruct H as [? [? [? [? ?] ] ] ].
  unfold list_on_tree.
  split. {
    clear H1 H2.
    revert H H0. revert l t p.
    induction lt; simpl; intros.
    + inversion H0; [subst; tauto | discriminate].
    + destruct a as [[flg v] ts].
      destruct flg.
      - specialize (IHlt l (Node v ts t) (p / 2)).
        inversion H0; [discriminate | ].
        injection H1; intros; subst lt0 t0 v0 flg.
        assert (list_nth_on_tree l (p / 2) (Node v ts t)). {
          apply list_nth_on_tree_Node.
          + lia.
          + rewrite H9; auto.
          + replace (p / 2 * 2) with (p + -1) by lia; tauto.
          + rewrite <- H3; tauto.
        }
        apply IHlt; tauto.
      - specialize (IHlt l (Node v t ts) (p / 2)).
        inversion H0; [discriminate | ].
        injection H1; intros; subst lt0 t0 v0 flg.
        assert (list_nth_on_tree l (p / 2) (Node v t ts)). {
          apply list_nth_on_tree_Node.
          + lia.
          + rewrite H9; auto.
          + replace (p / 2 * 2) with p by lia; tauto.
          + replace (p / 2 * 2 + 1) with (p + 1) by lia; tauto.
        }
        apply IHlt; tauto. 
  }
  split; auto.
  exists x; tauto.
Qed.

Definition list_on_tree_state(l: list_state) (t: tree_state): Prop :=
  list_on_tree_state_fix (fst l) (snd l) (fst t) (snd t).



(*
Lemma list_on_tree_inj: forall (l: list Z) (t1 t2: tree),
  list_on_tree l t1 -> list_on_tree l t2 -> t1 = t2.
Proof.
  intros.
  unfold list_on_tree in H.
  unfold list_on_tree in H0.
  apply (list_nth_on_tree_inj _ 1 _ _ H H0).
Qed.
*)
Lemma list_on_tree_state_impl_all: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> (snd l) = 1 -> (fst t) = nil.
Proof.
  intros.
  unfold list_on_tree_state in H.
  destruct t as [lt t].
  simpl in H; simpl.
  unfold list_on_tree_state_fix in H.
  destruct H.
  destruct H1.
  inversion H1; [auto | ].
  pose proof Z.div_lt_upper_bound (snd l) 2 1 ltac:(lia) ltac:(lia). 
  lia.
Qed.

Lemma complete_pt_size: forall d n pt l,
  complete_tree_push d (tree_compose pt Leaf) ->
  list_on_partial_tree l n pt ->
  n > tree_size (tree_compose pt Leaf).
Proof.
  intros.
  revert d n H H0.
  induction pt; simpl; intros.
  + inversion H0; [lia | discriminate].
  + destruct a as [[flg v] tr].
    destruct flg.
    - inversion H0; [discriminate | ].
      injection H1; intros. subst lt0 t v0 flg. 
Admitted. 

Lemma legal_list_impl_legal_tree_state: forall (l: list_state) (t: tree_state),
 list_on_tree_state l t -> legal_list_state l -> legal_tree_state t.
Proof.
  destruct l as [l n].
  destruct t as [pt tr].
  unfold list_on_tree_state.
  unfold list_on_tree_state_fix.
  simpl; intros.
  destruct H, H1, H2.
  unfold legal_list_state in H0; simpl in H0.
  unfold legal_tree_state; simpl.
  destruct tr; [ | exists v, tr1, tr2; auto].
  destruct H3.
  pose proof complete_pt_size _ _ _ _ H3 H1.
  lia.
Qed.

Lemma list_on_tree_state_impl_up_val: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> legal_list_state l -> (snd l) > 1 -> 
  exists lt v bro flg, (flg,v,bro)::lt = (fst t) /\ (get_tree_val (snd t) = (get_list_val l)) /\ v = get_list_val ((fst l),(snd l)/2).
Proof.
  intros.
  pose proof legal_list_impl_legal_tree_state _ _ H H0.
  unfold list_on_tree_state in H.
  unfold list_on_tree_state_fix in H.
  destruct t as [lt t].
  simpl; simpl in H.
  destruct H, H3.
  inversion H3; [lia | ].
  exists lt0, v, t0, flg.
  split; [auto | ].
  unfold legal_tree_state in H2.
  destruct H2 as [v' [ls [rs]]].
  simpl in H2; subst.
  inversion H; subst.
  split; simpl.
  + unfold get_list_val; auto.
  + unfold get_list_val; simpl; auto.
Qed.

Lemma list_on_tree_state_impl_tree_compose: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> list_on_tree (fst l) (tree_compose (fst t) (snd t)).
Proof.
  destruct t as [lt t].
  destruct l as [l n].
  intros.
  destruct H, H0, H1.
  destruct H2 as [d].
  unfold list_on_tree.
  split.
  2: {
    split; [tauto|].
    exists d.
    tauto.
  }
  revert n t H H0 H1 H2. 
  induction lt; intros.
  + simpl.
    simpl in H, H0, H1, H2.
    inversion H0.
    - rewrite H3 in H.
      tauto.
    - discriminate.
  + unfold fst, snd.
    destruct a as [[flg v] tr].
    simpl in IHlt.
    destruct flg.
    - simpl; simpl in H, H0.
      inversion H0; [discriminate|].
      injection H3; intros; subst.
      apply (IHlt (n/2)); try tauto.
      eapply list_nth_on_tree_Node; try tauto.
      replace (n/2*2) with(n-1) by lia; tauto.
      rewrite <- H5; tauto.
    - simpl; simpl in H, H0.
      inversion H0; [discriminate|].
      injection H3; intros; subst.
      apply (IHlt (n/2)); try tauto.
      eapply list_nth_on_tree_Node; try tauto.
      replace (n / 2 * 2) with n by lia; tauto.
      replace (n / 2 * 2 + 1) with (n+1) by lia; tauto.
Qed.


Lemma list_nth_on_tree_replace: forall (l l': list Z) (t: tree) (n: Z),
  Zlength l = Zlength l' -> n >= 0 -> (forall i, i >= n -> Znth i l = Znth i l') -> list_nth_on_tree l n t -> list_nth_on_tree l' n t.
Proof.
  intros.
  revert H1 H; revert l'.
  induction H2; subst; simpl; intros.
  + apply list_nth_on_tree_Leaf; auto; lia.
  + eapply list_nth_on_tree_Node; eauto.
    - lia.
    - specialize (H1 n ltac:(lia)); auto.
    - specialize (IHlist_nth_on_tree1 ltac:(lia) l').
      apply IHlist_nth_on_tree1; [ intros | auto].
      specialize (H1 i ltac:(lia)); auto.
    - specialize (IHlist_nth_on_tree2 ltac:(lia) l').
      apply IHlist_nth_on_tree2; [ intros | auto].
      specialize (H1 i ltac:(lia)); auto. 
Qed.

Inductive tree_same: tree -> tree -> Prop :=
  | Leaf_same: tree_same Leaf Leaf
  | Node_same: forall v1 ls1 rs1 v2 ls2 rs2,
      tree_same ls1 ls2 -> tree_same rs1 rs2 -> tree_same (Node v1 ls1 rs1) (Node v2 ls2 rs2).

Lemma tree_same_rel: forall (t1 t2: tree),
  t1 = t2 -> tree_same t1 t2.
Proof.
  intros.
  revert t2 H.
  induction t1; intros.
  + rewrite <- H; apply Leaf_same; reflexivity.
  + rewrite H.
    destruct t2; [discriminate|].
    injection H; intros; subst.
    eapply Node_same; try reflexivity.
    - apply IHt1_1; reflexivity.
    - apply IHt1_2. reflexivity.
Qed.

Lemma tree_compose_same: forall (t1 t2: tree) (lt: partial_tree),
  tree_same t1 t2 -> tree_same (tree_compose lt t1) (tree_compose lt t2).
Proof.
  intros.
  revert t1 t2 H.
  induction lt; intros.
  + simpl.
    apply H.
  + destruct a as [[flg val] tr].
    destruct flg.
    - simpl.
      apply IHlt.
      eapply Node_same; eauto.
      apply tree_same_rel; reflexivity.
    - simpl.
      apply IHlt.
      eapply Node_same; eauto.
      apply tree_same_rel; reflexivity.
Qed.

Lemma tree_same_size: forall (t1 t2: tree),
  tree_same t1 t2 -> tree_size t1 = tree_size t2.
Proof.
  intros.
  induction H.
  + tauto.
  + simpl.
    lia.
Qed.

Lemma tree_same_full_tree: forall (t1 t2: tree) (d: Z),
  tree_same t1 t2 -> full_tree d t1 -> full_tree d t2.
Proof.
  intros.
  revert d H0.
  induction H; intros.
  + tauto.
  + inversion H1; subst.
    eapply full_tree_Node.
    apply IHtree_same1; tauto.
    apply IHtree_same2; tauto.
Qed.

Lemma tree_same_complete_tree: forall (t1 t2: tree) (d: Z),
  tree_same t1 t2 -> complete_tree_push d t1 -> complete_tree_push d t2.
Proof.
  intros.
  revert d H0.
  induction H; intros.
  + inversion H0.
    rewrite H.
    apply complete_tree_push_Leaf; lia.
  + inversion H1; subst.
    - eapply complete_tree_push_left_full.
      * apply (tree_same_full_tree ls1); tauto.
      * apply IHtree_same2; tauto.
    - eapply complete_tree_push_right_full.
      * apply IHtree_same1; tauto.
      * apply (tree_same_full_tree rs1); tauto.
Qed.

Lemma tree_same_swap: forall (t1 t2: tree),
  tree_same t1 t2 -> tree_same t2 t1.
Proof.
  intros.
  induction H.
  + apply Leaf_same.
  + apply Node_same; tauto.  
Qed.

Definition get_snd_01(n p k: Z): bool:=
  if (p*2+1 =? (Z.shiftr n (k-1))) then true
  else false.

Fixpoint tree_to_partial_tree_fix (tl: partial_tree) (t: tree) (d: Z): partial_tree :=
  match t with
    | Leaf => tl
    | Node v ls rs => 
      match (full_tree_b (d - 1) ls) with
      | true => tree_to_partial_tree_fix ((true, v, ls) :: tl) rs (d-1)
      | false => tree_to_partial_tree_fix ((false, v, rs) :: tl) ls (d-1)
      end (*true go right and right is cut*)
  end.

Definition tree_to_partial_tree (t: tree) (d: Z): partial_tree := 
  tree_to_partial_tree_fix nil t d.