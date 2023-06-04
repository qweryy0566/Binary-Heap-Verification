Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.up.path1.
Require Import SetsClass.SetsClass.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.up.path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros Hl0 pos1 a pos.
  subst.
  sep_apply list_length; [lia | ]; Intros.
  forward.
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
  forward.
  rewrite H12.
  forward.
  sep_apply int_array_is_ptr; [lia | ]; Intros.
  assert_PROP (field_compatible (tarray tint (Zlength Hl0)) [] a0) by entailer!.
  forward_call (Znth (pos1 / 2) Hl0, Znth pos1 Hl0, 
                field_address (tarray tint Maxsize) [ArraySubsc (pos1 / 2)] a0,
                field_address (tarray tint Maxsize) [ArraySubsc pos1] a0,
                field_address (tarray tint Maxsize) [ArraySubsc pos1] a0,
                field_address (tarray tint Maxsize) [ArraySubsc (pos1 / 2)] a0).
  {
    entailer!.
    split.
    + f_equal.
      apply offset_val_field_address; [lia | tauto].
    + f_equal.
      rewrite H12, floyd.forward.sem_add_pi'.
      - apply offset_val_field_address; [lia | tauto].
      - tauto. 
      - tauto.
      - rep_lia.
  }
  {
    sep_apply (int_array_with_two_holes a0 Hl0 Maxsize (pos1 / 2) pos1);
      [lia | lia | lia |].
    entailer!.
  }
  forward.
  Exists (list_swap Hl0 (pos1 / 2) pos1) (pos1 / 2) a0 (Vint (IntRepr (pos1 / 2))).
  entailer!.
  2: {
    sep_apply (int_array_with_two_holes_inv a0 Hl0 (pos1 / 2) pos1 (Znth pos1 Hl0) (Znth (pos1 / 2) Hl0));
      [ lia | lia | entailer! ].
  }
  split.
  2: {
    split; [ | f_equal; rewrite H12; reflexivity].
    apply all_int_swap; [tauto | lia | lia ].
  }
  unfold up_inv.
  etransitivity_n1; [apply H | ].
  unfold list_relation.list_up_succeed.
  unfold list_relation.legal_list_state.
  unfold list_relation.get_list_val.
  simpl; split.
  + split; [| lia].
    rewrite Zlength_firstn.
    lia.
  + split.
    - split; [| lia].
      rewrite Zlength_firstn.
      assert (Zlength (list_swap Hl0 (pos1 / 2) pos1) = Zlength Hl0) by (rewrite list_swap_len; lia).
      lia.
    - split; [lia | ].
      split; [lia | ].
      split.
      * rewrite !Int.signed_repr in H14.
        ++ rewrite !Znth_firstn by lia.
           lia.
        ++ apply all_int_Znth; [tauto | lia].
        ++ apply all_int_Znth; [tauto | lia].
      * rewrite list_swap_eq by lia.
        apply list_swap_rela_correct_firstn; lia.
Qed.

End SH_Proof.
