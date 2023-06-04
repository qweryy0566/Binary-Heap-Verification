Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require Import SetsClass.SetsClass.
Require Import Classical_Prop.
Require heap.down.path7.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.down.path7.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros Hl0 pos1 a pos size.
  subst.
  sep_apply list_length; [lia | ].
  Intros.
  sep_apply int_array_is_ptr; [lia | ].
  Intros.
  forward.
  assert ((Int.shl (IntRepr pos1) (IntRepr 1)) = Int.repr (2 * pos1)). {
    unfold Int.shl.
    unfold Z.shiftl.
    simpl.
    rewrite Int.unsigned_repr by rep_lia.
    f_equal; lia.
  }
  rewrite H3, Int.signed_repr in H1 by rep_lia.
  forward.
  Exists Hl0 pos1.
  entailer!.
  unfold down, list_relation.heap_list_down.
  unfold_RELS_tac.
  exists (pair (firstn (Z.to_nat (size0 + 1)) Hl0) pos1).
  split; [tauto | ].
  unfold list_relation.list_down_fail.
  unfold_RELS_tac.
  split; [ | reflexivity].
  list_relation.try_list_unfold_witout_Z.
  rewrite !Zlength_firstn.
  lia.
Qed.

End SH_Proof.
