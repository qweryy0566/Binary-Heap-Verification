Require Import FloydSeq.proofauto.
(* Require Import cprogs.heap.program. *)
Require Import Notations Logic Datatypes.
From Coq Require Import String List ZArith. 
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import Coq.micromega.Psatz.
Local Open Scope string.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import cprogs.heap.list_relation.
Require Import cprogs.heap.definitions.

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

Inductive complete_tree (dep: Z): tree -> Prop :=
  | complete_tree_Leaf: dep = 0 -> complete_tree dep Leaf
  | complete_tree_left_hull: forall v ls rs,
      complete_tree (dep - 1) ls -> full_tree (dep - 2) rs ->
      complete_tree dep (Node v ls rs)
  | complete_tree_right_hull: forall v ls rs,
      full_tree (dep - 1) ls -> complete_tree (dep - 1) rs ->
      complete_tree dep (Node v ls rs).

Lemma full_tree_complete_tree: forall dep t,
  full_tree dep t -> complete_tree dep t.
Proof.
  intros.
  induction H.
  + apply complete_tree_Leaf; auto.
  + apply complete_tree_right_hull; auto.
Qed.

Definition partial_tree: Type := list (bool * Z * tree).
(* true:right_son is cut
   false:left_son is cut*)
Definition tree_state: Type := partial_tree * tree.

Definition legal_tree_state (t: tree_state): Prop :=
  exists v ls rs, (snd t) = Node v ls rs.

Fixpoint tree_compose (pt: partial_tree) (t: tree) :=
  match pt with
    | nil => t
    | (true, v, son) :: pt0  => tree_compose pt0 (Node v son t)
    | (false, v, son) :: pt0 => tree_compose pt0 (Node v t son)
  end.

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

Definition list_on_tree (l: list Z) (tr: tree): Prop :=
  list_nth_on_tree l 1 tr /\ tree_size tr = Zlength l - 1 /\
  exists d, complete_tree d tr. 

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

Definition tree_up_succeed:
  tree_state -> tree_state -> Prop:=
    fun t1 t2 => exists t3 l', 
    (t3::l' = (fst t1)) /\ (l' = (fst t2)) /\
    (exists v ls rs, (swap_up_and_combine v ls rs t3) = (snd t2) /\ (snd t1) = (Node v ls rs)) /\ 
    ((get_tree_val (snd t1)) > (snd (fst t3))).

Definition tree_up_fail:
  tree_state -> tree_state -> Prop:=
    Rels.test(fun t => 
      match (fst t) with
      | nil => True
      | t2::lt => snd (fst t2) >= (get_tree_val (snd t))
      end).

Definition heap_tree_up:
  tree_state -> tree_state -> Prop:=
  (clos_refl_trans tree_up_succeed) ∘ tree_up_fail.

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

Definition MaxHeap_tree_up(ts: tree_state): Prop :=
  MaxHeap_partial_tree (fst ts) /\ MaxHeap (snd ts) /\ (exists v ls rs, snd ts = Node v ls rs /\ 
  (ls = Leaf \/ MaxHeap_partial_tree_v (fst ts) (get_tree_val ls)) /\ 
  (rs = Leaf \/ MaxHeap_partial_tree_v (fst ts) (get_tree_val rs))).

(* p 为洞的位置且洞在 Zlength l 内 *)
Inductive list_on_partial_tree (l: list Z) (p: Z) (lt: partial_tree) : Prop :=
  | nil_partial_tree: p = 1 -> lt = nil -> list_on_partial_tree l p lt
  | cons_partial_tree: forall flg v t lt0, 
    lt = (flg, v, t) :: lt0 ->
    1 < p < Zlength l -> 
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
      * pose proof is_child_index_self p n H; tauto.
      * rewrite upd_Znth_diff by lia; tauto.
    - apply IHlist_nth_on_tree1.
      unfold not; intros.
      pose proof is_child_index_gp_inv_left n p ltac:(lia) H.
      auto.
    - apply IHlist_nth_on_tree2.
      unfold not; intros.
      pose proof is_child_index_gp_inv_right n p ltac:(lia) H.
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
  list_nth_on_tree l p t /\ list_on_partial_tree l p lt.

Definition list_on_tree_state(l: list_state) (t: tree_state): Prop :=
  list_on_tree_state_fix (fst l) (snd l) (fst t) (snd t).

Lemma list_nth_on_tree_inj: forall (l: list Z) (n: Z) (t1 t2: tree),
  list_nth_on_tree l n t1 -> list_nth_on_tree l n t2 -> t1 = t2.
Proof.
  intros; revert H0; revert t2.
  induction H; intros.
  + inversion H1; subst; auto; lia.
  + inversion H4; subst.
    - lia.
    - specialize (IHlist_nth_on_tree1 _ H8).
      specialize (IHlist_nth_on_tree2 _ H9).
      subst; auto. 
Qed.

Lemma list_on_tree_inj: forall (l: list Z) (t1 t2: tree),
  list_on_tree l t1 -> list_on_tree l t2 -> t1 = t2.
Proof.
  intros.
  unfold list_on_tree in H.
  unfold list_on_tree in H0.
  apply (list_nth_on_tree_inj _ 1 _ _ H H0).
Qed.

Lemma list_on_tree_state_impl_all: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> (snd l) = 1 -> (fst t) = nil.
Proof.
  intros.
  unfold list_on_tree_state in H.
  destruct t as [lt t].
  simpl in H; simpl.
  unfold list_on_tree_state_fix in H.
  destruct H.
  inversion H1; [auto | lia].
Qed.

Lemma legal_list_impl_legal_tree_state: forall (l: list_state) (t: tree_state),
 list_on_tree_state l t -> legal_list_state l -> legal_tree_state t.
Proof.
  unfold list_on_tree_state.
  intros.
  destruct t as [lt t].
  simpl in H. 
  destruct t.
  + unfold list_on_tree_state_fix in H.
    destruct H.
    unfold legal_list_state in H0.
    inversion H; [lia | discriminate].
  + unfold legal_tree_state.
    exists v, t1, t2.
    tauto.
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
  destruct H.
  inversion H3; [lia | ].
  exists lt0, v, t0, flg.
  split; [auto | ].
  unfold legal_tree_state in H2.
  destruct H2 as [v' [ls [rs]]].
  simpl in H2; subst.
  inversion H; [discriminate | ].
  inversion H2; subst.
  split; simpl.
  + unfold get_list_val; auto.
  + unfold get_list_val; simpl; auto.
Qed.

Lemma list_on_tree_state_impl_tree_compose: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> list_on_tree (fst l) (tree_compose (fst t) (snd t)).
Proof.
  intros.
  destruct t as [lt t].
  destruct l as [l n].
  unfold list_on_tree_state, list_on_tree_state_fix in H.
  revert H; revert l n t.
  induction lt; simpl; intros; destruct H.
  + inversion H0; [| discriminate].
    unfold list_on_tree.
    rewrite <- H1.
    tauto.
  + simpl in IHlt.
    inversion H0; [discriminate | ].
    apply cons_inv in H1; destruct H1.
    rewrite H1; subst.
    destruct flg.
    - specialize (IHlt l  (n / 2) (Node (Znth (n / 2) l) t0 t)).
      apply IHlt.
      split; [ | auto].
      eapply list_nth_on_tree_Node; eauto; [lia | | ].
      * replace (n / 2 * 2) with (n + -1) by lia; auto.
      * replace (n / 2 * 2 + 1) with n by lia; auto.
    - specialize (IHlt l  (n / 2) (Node (Znth (n / 2) l) t t0)).
      apply IHlt.
      split; [ | auto].
      eapply list_nth_on_tree_Node; eauto; [lia | | ].
      * replace (n / 2 * 2) with n by lia; auto.
      * replace (n / 2 * 2 + 1) with (n + 1) by lia; auto.
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
    - specialize (H2 n ltac:(lia)); auto.
    - specialize (IHlist_nth_on_tree1 ltac:(lia) l').
      apply IHlist_nth_on_tree1; [ intros | auto].
      specialize (H2 i ltac:(lia)); auto.
    - specialize (IHlist_nth_on_tree2 ltac:(lia) l').
      apply IHlist_nth_on_tree2; [ intros | auto].
      specialize (H2 i ltac:(lia)); auto. 
Qed.

Lemma swap_up_right_hold_true: forall (l l': list_state) (ls rs tr: tree) (v1 v2: Z) (lt: partial_tree),
  list_on_tree_state l ((true,v2,tr) :: lt, Node v1 ls rs) -> list_relation.list_swap (snd l) (snd l') (fst l) (fst l') -> snd l / 2 = snd l' -> list_on_tree_state l' (lt, Node v1 tr (Node v2 ls rs)).
Proof.
  unfold list_on_tree_state.
  unfold list_on_tree_state_fix.
  destruct l as [l n].
  destruct l' as [l' n'].
  simpl; intros; subst.
  destruct H.
  inversion H1; [discriminate |].
  apply cons_inv in H2; destruct H2.
  inversion H2; subst; clear H2.
  assert (1 <= n / 2 < n). {
    split.
    + pose proof Z.div_le_lower_bound n 2 1 ltac:(lia) ltac:(lia).
      lia.
    + pose proof Z.div_lt_upper_bound n 2 n ltac:(lia) ltac:(lia).
      lia. 
  }
  inversion H; [discriminate |].
  inversion H5.
  pose proof list_swap_rela_rewrite l l' n (n / 2) ltac:(lia) ltac:(lia) H0.
  subst; clear H0.
  split.
  + eapply list_nth_on_tree_Node; eauto.
    - rewrite list_swap_Zlength by lia; lia.
    - unfold list_swap.
      rewrite upd_Znth_diff.
      * rewrite upd_Znth_same; [auto | lia].
      * rewrite upd_Znth_Zlength by lia; lia.
      * rewrite upd_Znth_Zlength by lia; lia.
      * lia.
    - replace (n / 2 * 2) with (n + -1) by lia. 
      unfold list_swap.
      apply list_nth_on_tree_upd.
      * apply list_nth_on_tree_upd; [auto | lia |].
        apply less_is_not_child_index; lia.
      * rewrite upd_Znth_Zlength by lia; lia.
      * apply rchild_is_not_lchild with (pp := n / 2); [lia | lia |].
        apply is_child_index_self; auto.
    - rewrite <- H4.
      eapply list_nth_on_tree_Node.
      * reflexivity.
      * rewrite list_swap_Zlength by lia; lia.
      * unfold list_swap.
        rewrite upd_Znth_same; [reflexivity | ].
        rewrite upd_Znth_Zlength by lia; lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           apply less_is_not_child_index; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply less_is_not_child_index; lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           apply less_is_not_child_index; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply less_is_not_child_index; lia.
  + inversion H7; subst.
    - eapply nil_partial_tree; eauto.
    - pose proof Z.div_lt_upper_bound (n / 2) 2 (n / 2) ltac:(lia) ltac:(lia).
      pose proof Z.div_le_lower_bound (n / 2) 2 1 ltac:(lia) ltac:(lia).
      eapply cons_partial_tree; eauto.
      * rewrite list_swap_Zlength by lia; lia. 
      * unfold list_swap.
        rewrite upd_Znth_diff.
        -- rewrite upd_Znth_diff by lia; reflexivity.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           destruct flg.
           ++ apply rchild_is_not_lchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_self; auto.
           ++ apply less_is_not_child_index; lia. 
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- destruct flg.
           ++ apply rchild_is_not_lchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_gp; [lia | apply is_child_index_self; auto].
           ++ apply lchild_is_not_rchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_gp; [lia | apply is_child_index_self; auto].
      * unfold list_swap.
        apply list_on_partial_tree_upd.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply is_child_index_gp; [lia | ].
           apply is_child_index_gp; [lia | apply is_child_index_self; auto].
        -- apply list_on_partial_tree_upd; [lia | lia | |auto].
           apply is_child_index_gp; [lia | apply is_child_index_self; auto].
Qed.

Lemma swap_up_left_hold_true: forall (l l': list_state) (ls rs tr: tree) (v1 v2: Z) (lt: partial_tree),
  list_on_tree_state l ((false,v2,tr) :: lt, Node v1 ls rs) -> list_relation.list_swap (snd l) (snd l') (fst l) (fst l') -> snd l / 2 = snd l' -> list_on_tree_state l' (lt, (Node v1 (Node v2 ls rs) tr)).
Proof.
  unfold list_on_tree_state.
  unfold list_on_tree_state_fix.
  destruct l as [l n].
  destruct l' as [l' n'].
  simpl; intros; subst.
  destruct H.
  inversion H1; [discriminate |].
  apply cons_inv in H2; destruct H2.
  inversion H2; subst; clear H2.
  assert (1 <= n / 2 < n). {
    split.
    + pose proof Z.div_le_lower_bound n 2 1 ltac:(lia) ltac:(lia).
      lia.
    + pose proof Z.div_lt_upper_bound n 2 n ltac:(lia) ltac:(lia).
      lia. 
  }
  inversion H; [discriminate |].
  inversion H5.
  pose proof list_swap_rela_rewrite l l' n (n / 2) ltac:(lia) ltac:(lia) H0.
  subst; clear H0.
  split.
  + eapply list_nth_on_tree_Node; eauto.
    - rewrite list_swap_Zlength by lia; lia.
    - unfold list_swap.
      rewrite upd_Znth_diff.
      * rewrite upd_Znth_same; [auto | lia].
      * rewrite upd_Znth_Zlength by lia; lia.
      * rewrite upd_Znth_Zlength by lia; lia.
      * lia.
    - replace (n / 2 * 2) with n by lia.
      eapply list_nth_on_tree_Node.
      * reflexivity.
      * rewrite list_swap_Zlength by lia; lia.
      * unfold list_swap.
        rewrite upd_Znth_same; [reflexivity | ].
        rewrite upd_Znth_Zlength by lia; lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           apply less_is_not_child_index; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply less_is_not_child_index; lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           apply less_is_not_child_index; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply less_is_not_child_index; lia. 
    - replace (n / 2 * 2 + 1) with (n + 1) by lia.
      unfold list_swap.
      apply list_nth_on_tree_upd.
      * apply list_nth_on_tree_upd; [auto | lia |].
        apply less_is_not_child_index; lia.
      * rewrite upd_Znth_Zlength by lia; lia.
      * apply lchild_is_not_rchild with (pp := n / 2); [lia | lia |].
        apply is_child_index_self; auto.
  + inversion H7; subst.
    - eapply nil_partial_tree; eauto.
    - pose proof Z.div_lt_upper_bound (n / 2) 2 (n / 2) ltac:(lia) ltac:(lia).
      pose proof Z.div_le_lower_bound (n / 2) 2 1 ltac:(lia) ltac:(lia).
      eapply cons_partial_tree; eauto.
      * rewrite list_swap_Zlength by lia; lia. 
      * unfold list_swap.
        rewrite upd_Znth_diff.
        -- rewrite upd_Znth_diff by lia; reflexivity.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- lia.
      * unfold list_swap.
        apply list_nth_on_tree_upd.
        -- apply list_nth_on_tree_upd; [auto | lia |].
           destruct flg.
           ++ apply rchild_is_not_lchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_self; auto.
           ++ apply less_is_not_child_index; lia. 
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- destruct flg.
           ++ apply rchild_is_not_lchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_gp; [lia | apply is_child_index_self; auto].
           ++ apply lchild_is_not_rchild with (pp := n / 2 / 2); [lia | lia |].
              apply is_child_index_gp; [lia | apply is_child_index_self; auto].
      * unfold list_swap.
        apply list_on_partial_tree_upd.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- rewrite upd_Znth_Zlength by lia; lia.
        -- apply is_child_index_gp; [lia | ].
           apply is_child_index_gp; [lia | apply is_child_index_self; auto].
        -- apply list_on_partial_tree_upd; [lia | lia | |auto].
           apply is_child_index_gp; [lia | apply is_child_index_self; auto].
Qed.

Lemma Up_tree_list_succeed: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> list_up_succeed l l' -> MaxHeap_tree_up t ->
  exists t', tree_up_succeed t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_up t'.
Proof.
  intros.
  unfold list_up_succeed in H0.
  destruct H0, H2, H3, H4, H5.
  pose proof list_on_tree_state_impl_up_val _ _ H H0 ltac:(lia).
  destruct H7 as [lt [v [tr [flg]]]].
  destruct H7, H8.
  pose proof legal_list_impl_legal_tree_state _ _ H H0.
  unfold legal_tree_state in H10.
  destruct H10 as [v2 [ls [rs]]].
  rewrite H4 in H5.
  unfold get_list_val in H9; simpl in H9.
  rewrite H10 in H8; unfold get_tree_val in H8.
  assert (v2 > v) by lia.
  destruct flg.
  + exists (lt, (Node v2 tr (Node v ls rs))).
    split.
    - unfold tree_up_succeed.
      exists (true, v, tr), lt.
      split; [tauto|].
      split; [tauto|].
      split; [|rewrite H10; simpl; lia].
      exists v2, ls, rs.
      split; [|tauto].
      unfold swap_up_and_combine; simpl.
      reflexivity.
    - split.
      * eapply swap_up_right_hold_true; eauto.
        rewrite H7, <- H10.
        auto.
      * unfold MaxHeap_tree_up; simpl.
        unfold MaxHeap_tree_up in H1.
        destruct H1.
        rewrite <- H7 in H1.
        unfold MaxHeap_partial_tree in H1.
        destruct H1, H13.
        split; [apply (MaxHeap_partial_tree_v_impl _ _ H14)|].
        destruct H12.
        destruct H15 as [v3 [ls2 [rs2]]].
        rewrite H10 in H12; simpl in H12.
        destruct H15.
        rewrite H10 in H15.
        injection H15; intros; subst.
        split. destruct H13.
        ++ eapply MaxHeap_Node; [ reflexivity |apply H1 | |left; tauto|right; unfold get_tree_val; lia].
           destruct H16.
           inversion H12;[discriminate|].
           injection H16; intros; subst.
           eapply MaxHeap_Node; [reflexivity| | | | ]; try tauto.
           destruct H9; [left; tauto|].
           inversion H8; rewrite H9 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
           destruct H13; [left; tauto|]. inversion H8; rewrite H13 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
        ++ eapply MaxHeap_Node;[reflexivity|apply H1| | right; lia| right; unfold get_tree_val; lia].
           destruct H16.
           inversion H12;[discriminate|].
           injection H16; intros; subst.
           eapply MaxHeap_Node; [reflexivity| | | | ]; try tauto.
           destruct H9; [left; tauto|].
           inversion H9; rewrite H21 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
           destruct H13; [left; tauto|].
           inversion H13; rewrite H21 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
        ++ exists (get_list_val l), tr, (Node (Znth (snd l / 2) (fst l)) ls2 rs2); simpl.
           split; [reflexivity|].
           split; [|right; tauto].
           destruct H13; [left; tauto|right].
           apply (MaxHeap_partial_tree_v_change_v _ _ _ H14 H8).
  + exists (lt, (Node v2 (Node v ls rs) tr)).
    split.
    - unfold tree_up_succeed.
      exists (false, v, tr), lt.
      split; [tauto|].
      split; [tauto|].
      split; [|rewrite H10; simpl; lia].
      exists v2, ls, rs.
      split; [|tauto].
      unfold swap_up_and_combine; simpl.
      reflexivity.
    - split.
      * eapply swap_up_left_hold_true; eauto.
        rewrite H7, <- H10.
        auto.
      * unfold MaxHeap_tree_up. simpl.
        unfold MaxHeap_tree_up in H1.
        destruct H1.
        rewrite <- H7 in H1.
        unfold MaxHeap_partial_tree in H1.
        destruct H1, H13.
        split; [apply (MaxHeap_partial_tree_v_impl _ _ H14)|].
        destruct H12.
        destruct H15 as [v3 [ls2 [rs2]]].
        rewrite H10 in H12; simpl in H12.
        destruct H15.
        rewrite H10 in H15.
        injection H15; intros; subst.
        split. destruct H13.
        ++ eapply MaxHeap_Node; [ reflexivity | |apply H1 |right; unfold get_tree_val; lia|left; tauto].
           destruct H16.
           inversion H12;[discriminate|].
           injection H16; intros; subst.
           eapply MaxHeap_Node; [reflexivity| | | | ]; try tauto.
           destruct H9; [left; tauto|].
           inversion H8; rewrite H9 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
           destruct H13; [left; tauto|]. inversion H8; rewrite H13 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
        ++ eapply MaxHeap_Node; [ reflexivity | |apply H1 |right; unfold get_tree_val; lia|right; lia].
           destruct H16.
           inversion H12;[discriminate|].
           injection H16; intros; subst.
           eapply MaxHeap_Node; [reflexivity| | | | ]; try tauto.
           destruct H9; [left; tauto|].
           inversion H9; rewrite H21 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
           destruct H13; [left; tauto|].
           inversion H13; rewrite H21 in H7; [discriminate|].
           injection H7; intros; subst.
           right; lia.
        ++ exists (get_list_val l), (Node (Znth (snd l / 2) (fst l)) ls2 rs2), tr; simpl.
           split; [reflexivity|].
           split; [right; tauto |].
           destruct H13; [left; tauto|right].
           apply (MaxHeap_partial_tree_v_change_v _ _ _ H14 H8).
Qed.

Lemma Up_tree_list_succeed_clos_refl_trans: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> (clos_refl_trans list_up_succeed) l l' -> MaxHeap_tree_up t ->
  exists t', (clos_refl_trans tree_up_succeed) t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_up t'.
Proof.
  intros.
  revert t H H1.
  induction_1n H0.
  + exists t.
    split; [|tauto].
    exists 0%nat.
    unfold nsteps.
    reflexivity.
  + pose proof Up_tree_list_succeed _ _ _ H H2 H1.
    destruct H3 as [t'].
    destruct H3; destruct H4.
    specialize (IHrt _ H4 H5).
    destruct IHrt as [t'0].
    exists t'0.
    destruct H6, H7.
    split; [|tauto].
    etransitivity_1n; [apply H3|apply H6].
Qed.

Lemma Up_tree_list_fail: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> list_up_fail l l ->
  tree_up_fail t t.
Proof.
  intros.
  unfold list_up_fail in H0.
  destruct t as [lt t].
  revert H0; unfold_RELS_tac; intros.
  destruct H0; clear H1.
  destruct H0, H1.
  + pose proof list_on_tree_state_impl_all _ _  H ltac:(lia).
    simpl in H2.
    unfold tree_up_fail; unfold_RELS_tac.
    simpl.
    split; [|reflexivity].
    destruct lt; [tauto|discriminate].
  + destruct H1.
    pose proof list_on_tree_state_impl_up_val _ _ H H0 ltac:(lia).
    destruct H3 as [lt0].
    destruct H3, H3, H3, H3, H4.
    unfold tree_up_fail; unfold_RELS_tac.
    split; [|reflexivity].
    simpl; destruct lt; [discriminate|].
    simpl in H4.
    rewrite H4.
    simpl in H3.
    destruct p as [[flg v] tr]; subst.
    simpl.
    unfold get_list_val in H3.
    simpl in H3.
    injection H3.
    intros.
    lia.
Qed.

Lemma Up_fail_impl_MaxHeap: forall (t: tree_state),
  tree_up_fail t t -> MaxHeap_tree_up t -> MaxHeap (tree_compose (fst t) (snd t)).
Proof.
  intros.
  destruct t as [lt t].
  unfold tree_up_fail in H.
  revert H; unfold_RELS_tac; intros.
  simpl in H.
  destruct lt.
  + simpl.
    unfold MaxHeap_tree_up in H0.
    tauto.
  + destruct p as [[flg val] t2 ].
    simpl in H.
    simpl fst; simpl snd.
    destruct H; clear H1.
    unfold MaxHeap_tree_up in H0.
    simpl in H0.
    destruct H0, H0, H2.
    assert (MaxHeap_partial_tree ((flg, val, t2) :: lt)). {
      unfold MaxHeap_partial_tree.
      split; tauto.
    }
    destruct t.
    - pose proof MaxHeap_partial_tree_v_impl _ _ H3.
      destruct H1.
      apply (tree_compose_MaxHeap ((flg, val, t2) :: lt) Leaf H1 ltac:(tauto)).
    - assert (MaxHeap_partial_tree_v ((flg, val, t2) :: lt) v). {
        eapply MaxHeap_partial_tree_v_app; [reflexivity| | | | ]; try tauto.
        simpl in H.
        lia.
      }
      destruct H1.
      apply (tree_compose_MaxHeap ((flg, val, t2) :: lt) (Node v t1 t3) H1 ltac:(tauto)).
Qed.

Lemma list_up_fail_impl_eq: forall (l l': list_state),
  list_up_fail l l' -> l = l'.
Proof.
  intros; revert H.
  unfold list_up_fail.
  unfold_RELS_tac.
  tauto.
Qed.

Lemma Up_tree_list_rel: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> heap_list_up l l' -> MaxHeap_tree_up t ->
  exists t', heap_tree_up t t' /\ list_on_tree_state l' t' /\ MaxHeap (tree_compose (fst t') (snd t')).
Proof.
  intros.
  unfold heap_list_up in H0.
  revert H0; unfold_RELS_tac; intros.
  destruct H0 as [l1]; destruct H0.
  pose proof Up_tree_list_succeed_clos_refl_trans _ _ _ H H0 H1.
  pose proof list_up_fail_impl_eq _ _ H2.
  subst.
  destruct H3 as [t'].
  destruct H3, H4.
  exists t'.
  split.
  pose proof Up_tree_list_fail _ _ H4 H2.
  + unfold heap_tree_up.
    unfold_RELS_tac.
    exists t'.
    tauto.
  + split;[tauto|].
    pose proof Up_tree_list_fail _ _ H4 H2.
    apply (Up_fail_impl_MaxHeap _ H6 H5).
Qed.


Fixpoint get_snd_01_pos(n: positive): bool:=
  match n with
  | 1%positive => true
  | 2%positive => false
  | (x~1)%positive | (x~0)%positive => (get_snd_01_pos x)
  end.

Definition get_snd_01(n: Z): bool:=
  match n with
    | 0 => true
    | Z.pos p => (get_snd_01_pos p)
    | Z.neg _ => false
  end.

Fixpoint tree_to_partial_tree_fix (tl: partial_tree) (t: tree): partial_tree :=
  match t with
    | Leaf => tl
    | Node v ls rs => 
      match get_snd_01(tree_size t) with
      | true => tree_to_partial_tree_fix ((true, v, ls) :: tl) rs
      | false => tree_to_partial_tree_fix ((true, v, rs) :: tl) ls
      end (*true go right and right is cut*)
  end.

Definition tree_to_partial_tree (t: tree): partial_tree := 
  tree_to_partial_tree_fix nil t.

Lemma list_on_tree_state_app: forall (l: list Z) (t: tree) (v: Z),
  list_on_tree l t -> list_on_tree_state (l++[v], Zlength l) (tree_to_partial_tree t,Node v Leaf Leaf).
Proof.
  intros.
Admitted.

Definition tree_push: tree -> Z -> tree -> Prop :=
  fun t val t' =>
    exists (ts: tree_state), heap_tree_up ((tree_to_partial_tree t), Node val Leaf Leaf) ts /\ t' = (tree_compose (fst ts) (snd ts)).

Lemma tree_to_partial_tree_fix_hold: forall (lt: partial_tree) (t: tree),
  MaxHeap_partial_tree lt -> MaxHeap t -> (t = Leaf \/ MaxHeap_partial_tree_v lt (get_tree_val t)) -> MaxHeap_partial_tree (tree_to_partial_tree_fix lt t).
Proof.
  intros.
  revert lt H H1.
  induction H0; intros.
  + rewrite H.
    simpl.
    apply H0.
  + subst.
    destruct H3; [discriminate|].
    simpl in H.
    simpl.
    destruct (get_snd_01 (1 + tree_size ls + tree_size rs)).
    - apply IHMaxHeap2; [simpl; tauto|].
      destruct H1; [left; tauto|right].
      eapply MaxHeap_partial_tree_v_app; [reflexivity| | | | ]; tauto.
    - apply IHMaxHeap1; [simpl; tauto|].
      destruct H0; [left; tauto|right].
      eapply MaxHeap_partial_tree_v_app; [reflexivity| | | | ]; tauto.
Qed.

Lemma MaxHeap_impl_MaxHeap_tree_up: forall (t: tree) (v: Z),
  MaxHeap t -> MaxHeap_tree_up (tree_to_partial_tree t,Node v Leaf Leaf).
Proof.
  intros.
  revert H.
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
    injection H0; intros; subst.
    specialize (IHt1 H1).
    specialize (IHt2 H2).
    split.
    2: {
      split; [|exists v, Leaf, Leaf; tauto].
      eapply MaxHeap_Node; [reflexivity| | | |]; try tauto.
      apply MaxHeap_Leaf; reflexivity.
      apply MaxHeap_Leaf; reflexivity.
    }
    unfold tree_to_partial_tree.
    apply tree_to_partial_tree_fix_hold; [unfold MaxHeap_partial_tree; tauto|tauto|right].
    apply MaxHeap_partial_tree_v_nil; reflexivity.
Qed.

Lemma Push_tree_list_rel: forall (l l': list Z) (t: tree) (v: Z),
  list_on_tree l t -> heap_push l v l' -> MaxHeap t ->
  exists t', list_on_tree l' t' /\ MaxHeap t' /\ tree_push t v t'.
Proof.
  intros.
  unfold heap_push in H0.
  destruct H0.
  pose proof list_on_tree_state_app _ _ v H.
  pose proof MaxHeap_impl_MaxHeap_tree_up _ v H1.
  pose proof Up_tree_list_rel _ _ _ H2 H0 H3.
  destruct H4 as [t'].
  destruct H4, H5.
  pose proof list_on_tree_state_impl_tree_compose _ _ H5.
  simpl fst in H7.
  exists (tree_compose (fst t') (snd t')).
  split; [tauto|].
  split; [tauto|].
  unfold tree_push.
  exists t'.
  tauto.
Qed.

Definition tree_pop: tree -> tree -> Prop :=
  fun t t' =>
    exists (ts: tree_state), heap_tree_down (nil, t) ts /\ t' = (tree_compose (fst ts) (snd ts)).

Lemma Pop_tree_list_rel: forall (l l': list Z) (t: tree),
  list_on_tree l t -> heap_pop l l' -> MaxHeap t ->
  exists t', list_on_tree l' t' /\ MaxHeap t' /\ tree_pop t t'.
Proof.
Admitted.

Example list1: list Z:= [4;8;5].
Example tree_state_end: tree_state:=
  (nil, Node 8 (Node 4 Leaf Leaf) (Node 5 Leaf Leaf)).
Example tree_state_begin: tree_state:=
  ([(false,4,(Node 5 Leaf Leaf))]%list, Node 8 Leaf Leaf).

Example test_heap_tree_up:
  heap_tree_up tree_state_begin tree_state_end.
Proof.
  unfold heap_tree_up.
  unfold_RELS_tac.
  exists tree_state_end.
  split.
  + exists 1%nat.
    unfold nsteps.
    unfold_RELS_tac.
    exists tree_state_end.
    split; [|tauto].
    unfold tree_up_succeed.
    exists (false,4,(Node 5 Leaf Leaf)), nil.
    unfold tree_state_begin; unfold tree_state_end; simpl.
    split; [tauto|].
    split; [tauto|].
    split.
    - unfold swap_up_and_combine; simpl.
      exists 8, Leaf, Leaf; tauto.
    - lia.
  + unfold tree_up_fail.
    unfold_RELS_tac; simpl.
    tauto.
Qed.

Example up_fail_val_err: tree_up_fail
  ([(false,9,(Node 5 Leaf Leaf))]%list, Node 8 Leaf Leaf)
  ([(false,9,(Node 5 Leaf Leaf))]%list, Node 8 Leaf Leaf).
Proof.
  unfold tree_up_fail.
  unfold_RELS_tac; simpl.
  split; [lia|tauto].
Qed.

Example tree_state_begin2: tree_state:=
  (nil, Node 4 (Node 8 Leaf Leaf) (Node 5 Leaf Leaf)).
Example tree_state_end2: tree_state:=
  ([(false,8,(Node 5 Leaf Leaf))]%list, Node 4 Leaf Leaf).

Example test_heap_tree_down:
  heap_tree_down tree_state_begin2 tree_state_end2.
Proof.
  unfold heap_tree_down.
  unfold_RELS_tac.
  exists tree_state_end2.
  split.
  + exists 1%nat.
    unfold nsteps.
    unfold_RELS_tac.
    exists tree_state_end2.
    split; [|tauto].
    unfold tree_down_succeed.
    exists (false,8,(Node 5 Leaf Leaf)).
    split; [tauto|].
    exists 4, (Node 8 Leaf Leaf), (Node 5 Leaf Leaf).
    try_unfold_tree.
    split; [reflexivity|].
    right. right.
    split; [split; [discriminate|lia] | ]. 
    split; [split; [discriminate|lia] | ].
    right.
    split; [lia|].
    exists 8, Leaf, Leaf.
    split; [reflexivity|].
    split; reflexivity.
  + unfold tree_down_fail.
    unfold_RELS_tac.
    try_unfold_tree.
    split; [|tauto].
    exists 4, Leaf, Leaf.
    split; [reflexivity|].
    split; [|tauto].
    exists 4, Leaf, Leaf.
    reflexivity.
Qed.

Example down_fail_val_err: tree_down_fail
  (nil, Node 9 (Node 8 Leaf Leaf) (Node 5 Leaf Leaf))
  (nil, Node 9 (Node 8 Leaf Leaf) (Node 5 Leaf Leaf)).
Proof.
  unfold tree_down_fail.
  unfold_RELS_tac; simpl.
  try_unfold_tree.
  split; [|tauto].
  exists 9, (Node 8 Leaf Leaf), (Node 5 Leaf Leaf).
  split; [reflexivity|].
  split.
  + exists 9, (Node 8 Leaf Leaf), (Node 5 Leaf Leaf).
    reflexivity.
  + split; apply Classical_Prop.or_not_and;
    right; lia.
Qed.