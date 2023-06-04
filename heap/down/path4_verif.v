Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require Import SetsClass.SetsClass.
Require Import Classical_Prop.
Require heap.down.path4.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.down.path4.

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
  assert ((Int.shl (IntRepr pos1) (IntRepr 1)) = Int.repr (2 * pos1)). {
    unfold Int.shl.
    unfold Z.shiftl.
    simpl.
    rewrite Int.unsigned_repr by rep_lia.
    f_equal; lia.
  }
  rewrite H3, Int.signed_repr in H1 by rep_lia.
  assert (Int.unsigned (Int.shl (IntRepr pos1) (IntRepr 1)) = 2 * pos1). {
    rewrite H3.
    rewrite Int.unsigned_repr by rep_lia.
    reflexivity.
  }
  forward.
  rewrite H12.
  forward.
  forward.
  forward.
  rewrite H3 in H14.
  assert (Int.or (IntRepr (2 * pos1)) (IntRepr 1) = IntRepr(2 * pos1 + 1)). {
    unfold Int.or.
    f_equal.
    rewrite !Int.unsigned_repr by rep_lia.
    apply Zlor_add_one; lia.
  }
  rewrite H15 in H14.
  rewrite Int.signed_repr in H14 by rep_lia.
  assert (Int.unsigned (Int.or (Int.shl (IntRepr pos1) (IntRepr 1)) (IntRepr 1))  = 2 * pos1 + 1). {
    rewrite H3, H15.
    rewrite Int.unsigned_repr by rep_lia.
    reflexivity.
  }
  forward.
  rewrite H16.
  forward.
  forward.
  forward.
  rewrite H3, H15.
  forward.
  assert_PROP (field_compatible (tarray tint Maxsize) [] a0) by entailer!.
  forward_call (Znth (2 * pos1 + 1) Hl0, Znth pos1 Hl0, 
                field_address (tarray tint Maxsize) [ArraySubsc (2 * pos1 + 1)] a0,
                field_address (tarray tint Maxsize) [ArraySubsc pos1] a0,
                field_address (tarray tint Maxsize) [ArraySubsc pos1] a0,
                field_address (tarray tint Maxsize) [ArraySubsc (2 * pos1 + 1)] a0).
  {
    entailer!.
    split.
    + f_equal; apply offset_val_field_address; [lia | tauto].
    + f_equal; apply offset_val_field_address; [lia | tauto].
  }
  {
    sep_apply (int_array_with_two_holes a0 Hl0 Maxsize pos1 (2 * pos1 + 1));
      [lia | lia | lia | entailer!].  
  }
  forward.
  Exists (list_swap Hl0 pos1 (2 * pos1 + 1)) (2 * pos1 + 1) a0 (Vint (IntRepr (2 * pos1 + 1))) (Vint (IntRepr size0)).
  entailer!.
  2: {
    sep_apply (int_array_with_two_holes_inv a0 Hl0 pos1 (2 * pos1 + 1) (Znth (2 * pos1 + 1) Hl0) (Znth pos1 Hl0));
      [lia | lia | entailer!].
  }
  split.
  2: apply all_int_swap; [tauto | lia | lia].
  unfold down_inv.
  etransitivity_n1; [apply H | ].
  rewrite !Int.signed_repr in H13, H17.
  2: apply all_int_Znth; [tauto | lia].
  2: apply all_int_Znth; [tauto | lia].
  2: apply all_int_Znth; [tauto | lia].
  2: apply all_int_Znth; [tauto | lia].
  unfold list_relation.list_down_succeed.
  right; right.
  list_relation.try_list_unfold_witout_Z.
  split; try split; try split.
  + apply or_not_and; right.
    rewrite !Znth_firstn by lia.
    lia.
  + rewrite Zlength_firstn; lia.
  + rewrite !Znth_firstn by lia; lia.
  + apply list_swap_rela_correct_firstn; lia.
  + lia.
Qed.

End SH_Proof.
