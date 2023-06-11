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

Fixpoint list_nth_on_tree (l: list Z) (n: Z) (tr: tree): Prop :=
  match tr with
    | Leaf => Zlength l <= n
    | Node v ls rs =>
        n < Zlength l /\ Znth n l = v /\
        list_nth_on_tree l (n * 2) ls /\ list_nth_on_tree l (n * 2 + 1) rs
  end.

Example tree4: tree := Node 4 Leaf Leaf.
Example tree5: tree := Node 5 Leaf Leaf.
Example tree6: tree := Node 6 Leaf Leaf.
Example tree3: tree := Node 3 Leaf Leaf.
Example tree2: tree := Node 2 tree4 tree5.
Example tree1: tree := Node 1 tree2 tree3.

Definition list_example: list Z := [0; 1; 2; 3; 4; 5].

Example list_to_tree1: list_nth_on_tree [1] 1 Leaf.
Proof.
  simpl.
  unfold Zlength.
  simpl.
  lia.
Qed.

Example list_to_tree2: list_nth_on_tree list_example 2 tree2.
Proof.
  simpl.
  unfold list_example, Zlength.
  simpl.
  split; [lia | ].
  split; [tauto | ].
  split; [split; [lia | ] | split; [lia | ] ].
  + split; [tauto | lia].
  + split; [tauto | lia].  
Qed.

Example list_to_tree3: list_nth_on_tree list_example 1 tree1.
Proof.
  unfold tree1, list_nth_on_tree.
  fold list_nth_on_tree.
  split.
  + unfold list_example, Zlength.
    simpl.
    lia.
  + split; [tauto | ].
    split; [apply list_to_tree2 | simpl].
    unfold list_example, Zlength.
    simpl.
    split; [lia | ].
    split; [tauto | lia].
Qed.

Definition list_on_tree (l: list Z) (tr: tree): Prop :=
  list_nth_on_tree l 1 tr.

Example list_to_tree_example: list_on_tree list_example tree1.
Proof.
  unfold list_on_tree.
  apply list_to_tree3.
Qed.

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

Fixpoint MaxHeap(t: tree): Prop :=
  match t with 
    | Leaf => True
    | Node v ls rs => 
      (ls = Leaf \/ (get_tree_val ls) <= v) /\
      (rs = Leaf \/ (get_tree_val rs) <= v) /\ 
      MaxHeap ls /\ MaxHeap rs
  end.

Fixpoint MaxHeap_partial_tree_v(lt: partial_tree) (vt: Z): Prop :=
  match lt with
    | nil => True
    | (fl, v, t) :: lt0 => (MaxHeap t) /\ (t = Leaf \/ (get_tree_val t) <= v)
                          /\ (vt <= v) /\ (MaxHeap_partial_tree_v lt0 v)
  end.

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
  unfold MaxHeap_partial_tree_v in H; fold MaxHeap_partial_tree_v in H.
  destruct H, H0, H1.
  tauto.
Qed.

Lemma MaxHeap_partial_tree_v_change_v: forall (lt: partial_tree) (v1 v2: Z),
  MaxHeap_partial_tree_v lt v1 -> v2 <= v1 -> MaxHeap_partial_tree_v lt v2.
Proof.
  intros.
  destruct lt; [tauto|].
  destruct p as [[flg val] t].
  simpl in H; simpl.
  split; [tauto|].
  split; [tauto|].
  split; [lia|].
  tauto.
Qed.

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
  - unfold MaxHeap_partial_tree_v in H1; fold MaxHeap_partial_tree_v in H1.
    assert (MaxHeap (Node val t2 t)). {
      unfold MaxHeap; fold MaxHeap.
      split; [tauto|].
      destruct H1.
      + split; [left|]; tauto.
      + destruct H1, H5, H6.
        split; [right|]; tauto.
    }
    unfold tree_compose; fold tree_compose.
    destruct H1.
    * apply (IHlt H4 (Node val t2 t) H5 ltac:(tauto)).
    * apply (IHlt H4 (Node val t2 t) H5 ltac:(tauto)).
  - unfold MaxHeap_partial_tree_v in H1; fold MaxHeap_partial_tree_v in H1.
    assert (MaxHeap (Node val t t2)). {
      unfold MaxHeap; fold MaxHeap.
      split; [tauto|].
      destruct H2.
      + split; [left|]; tauto.
      + split; [right|]; tauto.
    }
    unfold tree_compose; fold tree_compose.
    pose proof MaxHeap_partial_tree_v_impl _ _ H3.
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

Definition MaxHeap_tree_down(ts: tree_state): Prop :=
  MaxHeap_partial_tree (fst ts) /\ MaxHeap_no_rt (snd ts) /\
  (exists fl v ts0 lt, (fst ts) = (fl, v, ts0) :: lt -> v >= get_tree_val (snd ts)).

Fixpoint list_on_tree_state_fix(l: list Z) (ind: Z) (lt: partial_tree) (t: tree): Prop :=
  (list_nth_on_tree l ind t ) /\ 
  match lt with
    | nil => ind = 1
    | (true, v, tl) :: lt0 => list_on_tree_state_fix l (ind/2) lt0 (Node v tl t) /\ ind > 1
    | (false, v, tr) :: lt0 => list_on_tree_state_fix l (ind/2) lt0 (Node v t tr) /\ ind > 1
  end.

Definition list_on_tree_state(l: list_state) (t: tree_state): Prop :=
  list_on_tree_state_fix (fst l) (snd l) (fst t) (snd t).

Lemma list_nth_on_tree_inj: forall (l: list Z) (n: Z) (t1 t2: tree),
  list_nth_on_tree l n t1 -> list_nth_on_tree l n t2 -> t1 = t2.
Proof.
  intros.
  revert n t2 H H0.
  induction t1; intros.
  + unfold list_nth_on_tree in H.
    destruct t2; [reflexivity|].
    unfold list_nth_on_tree in H0.
    destruct H0.
    lia.
  + unfold list_nth_on_tree in H; fold list_nth_on_tree in H.
    destruct H, H1, H2. 
    destruct t2.
    - unfold list_nth_on_tree in H0.
      lia.
    - unfold list_nth_on_tree in H0; fold list_nth_on_tree in H0.
      destruct H0, H4, H5.
      specialize (IHt1_1 (n*2) t2_1 H2 H5).
      specialize (IHt1_2 (n*2+1) t2_2 H3 H6).
      replace v with v0 by lia.
      rewrite IHt1_1.  
      rewrite IHt1_2.
      reflexivity.
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
  simpl in H.
  destruct lt; [simpl; tauto|].
  destruct p as [ [flg v] tr ].
  destruct flg.
  + simpl in H.
    destruct H, H1.
    destruct lt;
    unfold list_on_tree_state_fix in H1;
    destruct H1; rewrite H0 in H1;
    replace (1/2) with 0 in H1 by tauto;
    lia.
  + simpl in H.
    destruct H, H1.
    destruct lt;
    unfold list_on_tree_state_fix in H1;
    destruct H1; rewrite H0 in H1;
    replace (1/2) with 0 in H1 by tauto;
    lia.
Qed.

Lemma legal_list_impl_legal_tree_state: forall (l: list_state) (t: tree_state),
 list_on_tree_state l t -> legal_list_state l -> legal_tree_state t.
Proof.
  intros.
  destruct t as [lt t].
  destruct t.
  + unfold list_on_tree_state in H.
    simpl in H.
    destruct lt;
    simpl in H;
    destruct H;
    unfold legal_list_state in H0;
    lia.
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
  destruct t as [lt t].
  destruct lt.
  + simpl in H; destruct H.
    lia.
  + destruct p as [[flg val] tr].
    exists lt, val, tr, flg.
    simpl.
    split; [reflexivity|].
    unfold legal_tree_state in H2.
    destruct H2 as [v [ls [rs]]].
    simpl in H2; subst.
    simpl in H.
    destruct H, H, H3, H4.
    split; [simpl; unfold get_list_val; lia|].
    unfold get_list_val; simpl.
    destruct flg.
    - destruct H2.
      destruct lt; simpl in H2; lia.
    - destruct H2.
      destruct lt; simpl in H2; lia.
Qed.

Lemma list_on_tree_state_impl_tree_compose: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> list_on_tree (fst l) (tree_compose (fst t) (snd t)).
Proof.
  intros.
  destruct t as [lt t].
  simpl.
  revert t l H.
  induction lt; intros.
  + unfold list_on_tree_state in H.
    simpl in H.
    destruct H.
    simpl.
    unfold list_on_tree.
    rewrite <- H0.
    tauto.
  + destruct a as [[flg v] tr ].
    destruct flg.
    - simpl.
      unfold list_on_tree_state in H; simpl in H.
      specialize (IHlt (Node v tr t) (fst l,snd l / 2)).
      simpl in IHlt; apply IHlt.
      unfold list_on_tree_state; simpl.
      tauto.
    - simpl.
      unfold list_on_tree_state in H; simpl in H.
      specialize (IHlt (Node v t tr) (fst l,snd l / 2)).
      simpl in IHlt; apply IHlt.
      unfold list_on_tree_state; simpl.
      tauto.
Qed.

Lemma list_nth_on_tree_replace: forall (l l': list Z) (t: tree) (n: Z),
  Zlength l = Zlength l' -> n >= 0-> (forall i, i >= n -> Znth i l = Znth i l') -> list_nth_on_tree l n t -> list_nth_on_tree l' n t.
Proof.
  intros.
  revert n l l' H H0 H1 H2.
  induction t; intros.
  + simpl in H1; simpl.
    rewrite <- H.
    apply H2.
  + simpl in H2; simpl.
    destruct H2, H3.
    split; [rewrite <- H; tauto|].
    pose proof (H1 n ltac:(lia)).
    split; [rewrite <- H5; tauto|].
    assert (forall i : Z, i >= (n*2) -> Znth i l = Znth i l'). {
      intros.
      assert (i >= n) by lia.
      apply (H1 i H7).
    }
    assert (forall i : Z, i >= (n*2+1) -> Znth i l = Znth i l'). {
      intros.
      assert (i >= n) by lia.
      apply (H1 i H8).
    }
    destruct H4.
    split.
    - apply (IHt1 (n*2) _ _ H ltac:(lia)); tauto.
    - apply (IHt2 (n*2+1) _ _ H ltac:(lia)); tauto.
Qed.

Lemma swap_up_hold_true: forall (l l': list_state) (ls rs tr: tree) (v1 v2: Z) (lt: partial_tree),
  list_on_tree_state l ((true,v2,tr)::lt, Node v1 ls rs) -> list_relation.list_swap (snd l) (snd l) (fst l) (fst l') -> snd l / 2 = snd l' -> list_on_tree_state l' (lt, Node v1 tr (Node v2 ls rs)).
Proof.
Admitted.

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
  destruct flg.
  + exists (lt, (Node v2 tr (Node v ls rs))).
    rewrite H4 in H5.
    unfold get_list_val in H9; simpl in H9.
    rewrite H10 in H8; unfold get_tree_val in H8.
    assert (v2 > v) by lia.
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
      * give_up.
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
        ++ split; [left; tauto|].
           split; [right; lia|].
           split; [tauto|].
           destruct H16.
           split. destruct H9; [tauto|rewrite <- H7 in H9; simpl in H9; right; tauto].
           split. destruct H13; [tauto|rewrite <- H7 in H13; simpl in H13; right; tauto].
           tauto.
        ++ split;[right; lia|].
           split; [right; lia|].
           split; [tauto|].
           destruct H16.
           split. destruct H9; [tauto|rewrite <- H7 in H9; simpl in H9; right; tauto].
           split. destruct H13; [tauto|rewrite <- H7 in H13; simpl in H13; right; tauto].
           tauto.
        ++ exists (get_list_val l), tr, (Node (Znth (snd l / 2) (fst l)) ls2 rs2); simpl.
           split; [reflexivity|].
           split; [|right; tauto].
           destruct H13; [left; tauto|right].
           apply (MaxHeap_partial_tree_v_change_v _ _ _ H14 H8).
Admitted.

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
        unfold MaxHeap_partial_tree_v; fold MaxHeap_partial_tree_v.
        simpl in H.
        assert (v <= val) by lia.
        tauto.
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

Lemma Down_tree_list_succeed: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> list_down_succeed l l' -> MaxHeap_tree_down t ->
  exists t', tree_down_succeed t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_down t'.
Proof.
Admitted.

(* Lemma Down_tree_list_succeed_clos_refl_trans: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> (clos_refl_trans list_down_succeed) l l' -> MaxHeap_tree_up t ->
  exists t', (clos_refl_trans tree_up_succeed) t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_up t'.
Proof.
Admitted. *)

Lemma Down_tree_list_fail: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> list_down_fail l l ->
  tree_down_fail t t.
Proof.
Admitted.

Lemma Down_fail_impl_MaxHeap: forall (t: tree_state),
  tree_down_fail t t -> MaxHeap_tree_down t -> MaxHeap (tree_compose (fst t) (snd t)).
Proof.
Admitted.

Lemma Down_tree_list_rel: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> heap_list_down l l' -> MaxHeap_tree_down t ->
  exists t', heap_tree_down t t' /\ list_on_tree_state l' t' /\ MaxHeap (tree_compose (fst t') (snd t')).
Proof.
Admitted.

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

Fixpoint tree_to_partial_tree (t: tree): partial_tree :=
  match t with
    | Leaf => nil
    | Node v ls rs => 
      match get_snd_01(tree_size t) with
      | true => (tree_to_partial_tree rs) ++ [(true, v, ls)]
      | false => (tree_to_partial_tree ls) ++ [(false, v, rs)]
      end (*true go right and right is cut*)
  end.

Lemma tree_to_partial_tree_rt_max: forall (rt tmp: tree) (lt: partial_tree) (v: Z) (flg: bool),
  (flg,v,tmp)::lt = tree_to_partial_tree rt -> v <= get_tree_val rt.
Proof.
  intros.
  revert v flg tmp lt H.
  induction rt; intros.
  + simpl in H.
    discriminate.
  + simpl.
    simpl in H.
(* Qed. *)
Admitted.

Lemma partial_tree_MaxHeap_app: forall (rt tmp: tree) (v: Z) (flg: bool),
  MaxHeap_partial_tree (tree_to_partial_tree rt) -> (rt = Leaf \/ v >= get_tree_val rt) -> MaxHeap tmp -> (tmp = Leaf \/ get_tree_val tmp <= v) -> MaxHeap_partial_tree ((tree_to_partial_tree rt) ++ [(flg,v,tmp)]).
Proof.
  intros.
  revert v tmp H1 H2 H H0.
  remember (tree_to_partial_tree rt) as Hq.
  induction Hq; intros.
  + give_up.
  + subst.
    rewrite <- app_comm_cons.
    destruct a as [[flg2 val] tr ].
    unfold MaxHeap_partial_tree.
    simpl in H.
    split; [tauto|].  
    split; [tauto|].
    destruct H, H3.
    pose proof MaxHeap_partial_tree_v_impl _ _ H4.
    (* specialize IHp.
    pose proof tree_to_partial_tree_rt_max _ _ _ _ _ HeqHq.
    destruct Hq.
    - destruct H0; [rewrite H0 in HeqHq; simpl in HeqHq; discriminate|].
      simpl.
      simpl in H.
      split; [tauto|].
      split; [tauto|].
      split; [lia|tauto].
    -
      tauto.
    assert (MaxHeap_partial_tree p). {
      unfold MaxHeap_partial_tree.
      (* destruct p *)
    }
    unfold s *)
Admitted.

Lemma list_on_tree_state_app: forall (l: list Z) (t: tree) (v: Z),
  list_on_tree l t -> list_on_tree_state (l++[v], Zlength l) (tree_to_partial_tree t,Node v Leaf Leaf).
Proof.
Admitted.

Definition tree_push: tree -> Z -> tree -> Prop :=
  fun t val t' =>
    exists (ts: tree_state), heap_tree_up ((tree_to_partial_tree t), Node val Leaf Leaf) ts /\ t' = (tree_compose (fst ts) (snd ts)).

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
    split; [tauto|].
    exists v, Leaf, Leaf.
    tauto.
  + unfold MaxHeap_tree_up.
    unfold fst, snd.
    unfold MaxHeap in H; fold MaxHeap in H.
    destruct H, H0, H1.
    specialize (IHt1 H1).
    specialize (IHt2 H2).
    unfold MaxHeap.
    split.
    unfold tree_to_partial_tree; fold tree_to_partial_tree.
    destruct (get_snd_01 (tree_size (Node v0 t1 t2))).
    - unfold MaxHeap_tree_up in IHt2.
      destruct IHt2.
      unfold fst in H3.
      assert (t2 = Leaf \/ v0 >= get_tree_val t2). {
        destruct H0; [left;tauto|right;lia].
      }
      apply (partial_tree_MaxHeap_app t2 t1 v0 true H3 H5); tauto.
    - unfold MaxHeap_tree_up in IHt1.
      destruct IHt1.
      unfold fst in H3.
      assert (t1 = Leaf \/ v0 >= get_tree_val t1). {
        destruct H; [left;tauto|right;lia].
      }
      apply (partial_tree_MaxHeap_app t1 t2 v0 false H3 H5); tauto.
    - split; [tauto|].
      exists v, Leaf, Leaf.
      tauto.
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