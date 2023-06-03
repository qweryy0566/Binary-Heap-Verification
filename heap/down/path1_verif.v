Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.down.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.down.path1.

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
  forward.
  assert ((Int.shl (IntRepr pos1) (IntRepr 1)) = Int.repr (pos1 * 2)). {
    unfold Int.shl.
    unfold Z.shiftl.
    simpl.
    rewrite Int.unsigned_repr by rep_lia.
    f_equal; lia.
  }
  rewrite H3, Int.signed_repr in H1 by rep_lia.
  assert (Int.unsigned (Int.shl (IntRepr pos1) (IntRepr 1)) = pos1 * 2). {
    rewrite H3.
    rewrite Int.unsigned_repr by rep_lia.
    reflexivity.
  }
  forward.
  forward.
  forward.
  forward.
  forward.
  rewrite H3 in H13.
  rewrite H3 in H14.
  assert (Int.or (IntRepr (pos1 * 2)) (IntRepr 1) = IntRepr(pos1 * 2 + 1)). {
    unfold Int.or.
    f_equal.
    rewrite !Int.unsigned_repr by rep_lia.
    apply Zlor_add_one; lia.
  }
  rewrite H15 in H14.
  rewrite Int.signed_repr in H14 by rep_lia.
  assert (Int.unsigned (Int.or (Int.shl (IntRepr pos1) (IntRepr 1)) (IntRepr 1))  = pos1 * 2 + 1). {
    rewrite H3, H15.
    rewrite Int.unsigned_repr by rep_lia.
    reflexivity.
  }
  forward.
  forward.
  forward.
  forward.
  forward.
  forward_call (Znth (pos1 * 2 + 1) Hl0, Znth pos1 Hl0, 
                field_address (tarray tint Maxsize) [ArraySubsc (pos1 * 2 + 1)] a0,
                field_address (tarray tint Maxsize) [ArraySubsc pos1] a0,
                field_address (tarray tint Maxsize) [ArraySubsc pos1] a0,
                field_address (tarray tint Maxsize) [ArraySubsc (pos1 * 2 + 1)] a0).
  {
    entailer!.
    split.
    + f_equal.
      apply offset_val_field_address; [lia | tauto].
    + f_equal.
      rewrite H3, H15, floyd.forward.sem_add_pi'.
      - apply offset_val_field_address; [lia | tauto].
      - tauto. 
      - tauto.
      - rep_lia. 
  }
  {
     
  }
Admitted.

End SH_Proof.
