Require Import FloydSeq.proofauto.
(* Require Import cprogs.heap.program. *)
Require Import Notations Logic Datatypes.
From Coq Require Import String List ZArith. 
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.

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


