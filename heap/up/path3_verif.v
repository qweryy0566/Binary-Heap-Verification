Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require Import SetsClass.SetsClass.
Require heap.up.path3.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.up.path3.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros; Intros Hl0 pos1 a pos; subst.
  forward.
  sep_apply list_length; [lia|]; Intros.
  forward.
  assert (1 <= pos1 / 2 /\ pos1 / 2 < pos1). {
    split.
    + pose proof Z.div_le_lower_bound pos1 2 1 ltac:(lia) ltac:(lia).
      lia.
    + pose proof Z.div_lt_upper_bound pos1 2 pos1 ltac:(lia) ltac:(lia).
      lia.
  }
  assert ((Int.shr (IntRepr pos1) (IntRepr 1)) = Int.repr (pos1 / 2)). {
    unfold Int.shr.
    rewrite Int.signed_repr by rep_lia.
    rewrite Int.unsigned_repr by rep_lia.
    unfold Z.shiftr.
    simpl.
    rewrite Z.div2_div.
    reflexivity.
  }
  assert (Int.unsigned (Int.shr (IntRepr pos1) (IntRepr 1)) = pos1 / 2). {
    rewrite H12.
    rewrite Int.unsigned_repr by rep_lia.
    reflexivity.
  }
  forward. forward. forward.
  Exists Hl0 pos1.
  entailer!.
  unfold up.
  unfold list_relation.heap_list_up.
  unfold up_inv in H. 
  unfold_RELS_tac.
  exists (firstn (Z.to_nat (size0 + 1)) Hl0, pos1).
  split; [apply H|].
  unfold list_relation.list_up_fail.
  unfold_RELS_tac.
  split; [|reflexivity].
  split.
  + unfold list_relation.legal_list_state.
    simpl.
    split; [|tauto].
    rewrite Zlength_firstn.
    replace (Z.max 0 (size0 + 1)) with (size0 + 1) by lia.
    lia.
  + right; simpl.
    split; [lia|].
    unfold list_relation.get_list_val; simpl.
    rewrite H13 in H14.
    rewrite ! Znth_firstn; [ | lia | lia].
    pose proof all_int_Znth Hl0 pos1 H10 ltac:(lia).
    pose proof all_int_Znth Hl0 (pos1/2) H10 ltac:(lia).
    rewrite ! Int.signed_repr in H14 by tauto.
    lia.
Qed.

End SH_Proof.
