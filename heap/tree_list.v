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

Definition left_son_check_tree (t: tree): Prop:=
  exists v ls rs, t = (Node v ls rs) /\ ~(ls = Leaf) /\ (get_tree_val ls) > v.

Definition right_son_check_tree (t: tree): Prop:=
  exists v ls rs, t = (Node v ls rs) /\ ~(rs = Leaf) /\ (get_tree_val rs) > v.

Definition swap_down_left (t1 t2: tree) (t: bool*Z*tree): Prop:=
  exists v ls rs vl lls lrs, t1 = (Node v ls rs) /\ ls = (Node vl lls lrs) /\
  t2 = (Node v lls lrs) /\ t = (false, vl, rs).

Definition swap_down_right (t1 t2: tree) (t: bool*Z*tree): Prop:=
  exists v ls rs vr rls rrs, t1 = (Node v ls rs) /\ rs = (Node vr rls rrs) /\
  t2 = (Node v rls rrs) /\ t = (true, vr, ls).

Definition tree_down_succeed:
  tree_state -> tree_state -> Prop:=
    fun t1 t2 => exists t, (t::(fst t1)) = (fst t2) /\ (
      ((left_son_check_tree (snd t1)) /\ ~(right_son_check_tree (snd t1)) /\ (swap_down_left (snd t1) (snd t2) t)) \/
      (~(left_son_check_tree (snd t1)) /\ (right_son_check_tree (snd t1)) /\ (swap_down_right (snd t1) (snd t2) t)) \/
      ((left_son_check_tree (snd t1)) /\ (right_son_check_tree (snd t1)) /\ (exists v ls rs, (snd t1) = (Node v ls rs) /\ (
        ((get_tree_val rs) > (get_tree_val ls) /\ (swap_down_right (snd t1) (snd t2) t)) \/
        ((get_tree_val rs) <= (get_tree_val ls) /\ (swap_down_left (snd t1) (snd t2) t)))
      ))
    ).

Definition tree_down_fail:
  tree_state -> tree_state -> Prop:=
  Rels.test(
    fun t => (legal_tree_state t) /\ ~(left_son_check_tree (snd t)) /\ ~(right_son_check_tree (snd t))
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
    right. right. 
    try_unfold_tree.
    split. 
      exists 4, (Node 8 Leaf Leaf), (Node 5 Leaf Leaf).
      split; [tauto|].
      split; [discriminate|lia].
    split.
      exists 4, (Node 8 Leaf Leaf), (Node 5 Leaf Leaf).
      split; [tauto|].
      split; [discriminate|lia].
    exists 4, (Node 8 Leaf Leaf), (Node 5 Leaf Leaf).
    split; [tauto|].
    right.
    split; [lia|].
    exists 4, (Node 8 Leaf Leaf), (Node 5 Leaf Leaf), 8, Leaf, Leaf.
    tauto.
  + unfold tree_down_fail.
    unfold_RELS_tac.
    try_unfold_tree.
    split; [|tauto].
    split; [exists 4, Leaf, Leaf; tauto|].
    split;
    apply all_not_not_ex; intros;
    apply all_not_not_ex; intros;
    apply all_not_not_ex; intros;
    apply Classical_Prop.or_not_and;
    apply Classical_Prop.imply_to_or;
    intros;
    injection H;
    intros; subst;
    apply Classical_Prop.or_not_and;
    left; tauto.
Qed.

Example down_fail_val_err: tree_down_fail
  (nil, Node 9 (Node 8 Leaf Leaf) (Node 5 Leaf Leaf))
  (nil, Node 9 (Node 8 Leaf Leaf) (Node 5 Leaf Leaf)).
Proof.
  unfold tree_down_fail.
  unfold_RELS_tac; simpl.
  try_unfold_tree.
  split; [|tauto].
  split.
  + exists 9, (Node 8 Leaf Leaf), (Node 5 Leaf Leaf); tauto.
  + split;
    apply all_not_not_ex; intros;
    apply all_not_not_ex; intros;
    apply all_not_not_ex; intros;
    apply Classical_Prop.or_not_and;
    apply Classical_Prop.imply_to_or;
    intros;
    injection H;
    intros; subst;
    apply Classical_Prop.or_not_and;
    right; lia.
Qed.