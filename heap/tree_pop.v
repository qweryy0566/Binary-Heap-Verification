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

Fixpoint tree_to_partial_tree_pop_fix (tl: partial_tree) (t: tree) (d: Z): partial_tree :=
  match t with
    | Leaf => tl
    | Node v ls rs => 
      match (full_tree_b (d - 2) rs) with
      | false => tree_to_partial_tree_pop_fix ((false, v, ls) :: tl) rs (d-1)
      | true => tree_to_partial_tree_pop_fix ((true, v, rs) :: tl) ls (d-1)
      end (*true go right and right is cut*)
  end.

Definition tree_to_partial_tree_pop(t: tree) (d: Z): partial_tree := 
  tree_to_partial_tree_pop_fix nil t d.

Definition get_last_val(l: partial_tree): Z :=
  match l with
    | nil => 0
    | (flg, v, tr)::lt => v
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

Lemma Pop_tree_list_rel: forall (l l': list Z) (t: tree),
  list_on_tree l t -> heap_pop l l' -> MaxHeap t ->
  exists t', list_on_tree l' t' /\ MaxHeap t' /\ tree_pop t t'.
Proof.
  intros.
Admitted.