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

Fixpoint iter_n_tree_up (n: nat):
  tree_state -> tree_state -> Prop:=
  match n with
  | O => tree_up_fail
  | S n0 => tree_up_succeed ∘ (iter_n_tree_up n0)
  end.

Definition heap_tree_up:
  tree_state -> tree_state -> Prop:=
  ⋃ (iter_n_tree_up).

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

Fixpoint iter_n_tree_down (n: nat):
  tree_state -> tree_state -> Prop:=
  match n with
  | O => tree_down_fail
  | S n0 => tree_down_succeed ∘ (iter_n_tree_down n0)
  end.

Definition heap_tree_down:
  tree_state -> tree_state -> Prop:=
  ⋃ (iter_n_tree_down).

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
                          /\ (v <= vt) /\ (MaxHeap_partial_tree_v lt0 v)
  end.

Definition MaxHeap_partial_tree(lt: partial_tree): Prop :=
  match lt with
    | nil => True
    | (fl, v, t) :: lt0 => (MaxHeap t) /\ (t = Leaf \/ (get_tree_val t) <= v) /\ (MaxHeap_partial_tree_v lt0 v)
  end.

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

Definition MaxHeap_no_rt(t: tree): Prop :=
  exists v ls rs, t = (Node v ls rs) /\ MaxHeap ls /\ MaxHeap rs.

Definition MaxHeap_tree_up(ts: tree_state): Prop :=
  MaxHeap_partial_tree (fst ts) /\ MaxHeap (snd ts).

Definition MaxHeap_tree_down(ts: tree_state): Prop :=
  MaxHeap_partial_tree (fst ts) /\ MaxHeap_no_rt (snd ts) /\
  (exists fl v ts0 lt, (fst ts) = (fl, v, ts0) :: lt -> v >= get_tree_val (snd ts)).

Definition list_on_tree_state(l: list_state) (t: tree_state): Prop :=
  True.

Lemma Up_tree_list_succeed: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> list_up_succeed l l' -> MaxHeap_tree_up t ->
  exists t', tree_up_succeed t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_up t'.
Proof.
Admitted.

Lemma Up_tree_list_fail: forall (l: list_state) (t: tree_state),
  list_on_tree_state l t -> list_up_fail l l ->
  tree_up_fail t t.
Proof.
Admitted.

Lemma Up_fail_impl_MaxHeap: forall (t: tree_state),
  tree_up_fail t t -> MaxHeap_tree_up t -> MaxHeap (tree_compose (fst t) (snd t)).
Proof.
Admitted.

Lemma Up_tree_list_rel: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> heap_list_up l l' -> MaxHeap_tree_up t ->
  exists t', heap_tree_up t t' /\ list_on_tree_state l' t' /\ MaxHeap (tree_compose (fst t') (snd t')).
Proof.
Admitted.

Lemma Down_tree_list_succeed: forall (l l': list_state) (t: tree_state),
  list_on_tree_state l t -> list_down_succeed l l' -> MaxHeap_tree_down t ->
  exists t', tree_down_succeed t t' /\ list_on_tree_state l' t' /\ MaxHeap_tree_down t'.
Proof.
Admitted.

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

Fixpoint tree_to_partical_tree (t: tree): partial_tree :=
  match t with
    | Leaf => nil
    | Node v ls rs => (true, v, ls) :: (tree_to_partical_tree rs)
  end.

Definition tree_push: tree -> Z -> tree -> Prop :=
  fun t val t' =>
    exists (ts: tree_state), heap_tree_up ((tree_to_partical_tree t), Node val Leaf Leaf) ts /\ t' = (tree_compose (fst ts) (snd ts)).

Lemma Push_tree_list_rel: forall (l l': list Z) (t: tree) (v: Z),
  list_on_tree l t -> heap_push l v l' -> MaxHeap t ->
  exists t', list_on_tree l' t' /\ MaxHeap t' /\ tree_push t v t'.
Proof.
Admitted.

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
  exists 1%nat. unfold iter_n_tree_up.
  unfold_RELS_tac.
  exists tree_state_end.
  split.
  + unfold tree_up_succeed.
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
  exists 1%nat. unfold iter_n_tree_down.
  unfold_RELS_tac.
  exists tree_state_end2.
  split.
  + unfold tree_down_succeed.
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