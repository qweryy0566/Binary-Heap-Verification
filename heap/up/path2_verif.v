Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require Import SetsClass.SetsClass.
Require heap.up.path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.up.path2.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros; Intros Hl0 pos1 a pos; subst.
  forward. forward.
  Exists Hl0 pos1.
  sep_apply list_length; [lia|]; Intros.
  entailer!.
  unfold up.
  unfold list_relation.heap_list_up.
  unfold up_inv in H. 
  unfold_RELS_tac.
  exists (firstn (Z.to_nat (size0 + 1)) Hl0, pos1).
  split; [tauto |].
  unfold list_relation.list_up_fail.
  unfold_RELS_tac.
  split; [| reflexivity].
  split. 
  + unfold list_relation.legal_list_state.
    simpl.
    split; [| tauto].
    rewrite Zlength_firstn.
    replace (Z.max 0 (size0 + 1)) with (size0 + 1) by lia.
    lia.
  + left.
    simpl.
    lia.
Qed.

End SH_Proof.
