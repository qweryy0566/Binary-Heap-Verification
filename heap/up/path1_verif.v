Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.up.path1.
Require Export SetsClass.SetsClass.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.up.path1.

Lemma offset_val_field_address:
  forall pos len a,
    0 <= pos < len ->
    field_compatible (tarray tint len) [] a ->
    offset_val (sizeof tint * pos) a = field_address (tarray tint len) [ArraySubsc pos] a.
Proof.
  intros.
  assert (field_compatible (tarray tint len) [ArraySubsc pos] a). {
    apply field_compatible_cons.
    split; [lia | tauto].
  }
  pose proof field_compatible_field_address _ _ _ H1.
  rewrite H2.
  tauto. 
Qed.

(* Lemma array_after_swap:  *)

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
    entailer!.
    pose proof split2_data_at_Tarray Tsh tint (Zlength Hl0) (pos1).
    erewrite H18; [| lia | rewrite H17; lia | | |].
    2: rewrite sublist_same; [tauto | tauto | rewrite H17; tauto].
    2: rewrite !sublist_map; reflexivity.
    2: rewrite !sublist_map; reflexivity.
    change (Tarray tint (pos1) noattr) with (tarray tint (pos1)).
    change (Tarray tint (Zlength Hl0 - pos1) noattr) with (tarray tint (Zlength Hl0 - pos1)).
    pose proof SingletonHole.array_with_hole_intro Tsh tint (pos1 / 2) pos1 (map Vint (map Int.repr (sublist 0 pos1 Hl0))) a0 ltac:(lia).
    rewrite !Znth_map in H19.
    2: rewrite Zlength_sublist by lia; lia.
    2: rewrite Zlength_map, Zlength_sublist by lia; lia.
    rewrite !Znth_sublist in H19 by lia.
    replace (pos1 / 2 + 0) with (pos1 / 2) in H19 by lia.
    replace (store_int (field_address (tarray tint pos1) [ArraySubsc (pos1 / 2)] a0) (Znth (pos1 / 2) Hl0))
      with (store_int (field_address (tarray tint (Zlength Hl0)) [ArraySubsc (pos1 / 2)] a0) (Znth (pos1 / 2) Hl0)) in H19.
    2: {
      rewrite <- offset_val_field_address; [ | lia | tauto].
      eapply field_compatible_Tarray_split in H16.
      + destruct H16.
        rewrite <- offset_val_field_address; [tauto | lia | apply H16].
      + lia.
    }
    sep_apply H19.
    entailer!.
    clear H18 H19 H20.
    change (Tarray tint (Zlength Hl0) noattr) with (tarray tint (Zlength Hl0)).
    pose proof SingletonHole.array_with_hole_intro Tsh tint 0 (Zlength Hl0 - pos1).
    sep_apply H18; [lia |].
    rewrite !Znth_map.
    2: rewrite Zlength_sublist by lia; lia.
    2: rewrite Zlength_map, Zlength_sublist by lia; lia.
    rewrite !Znth_sublist by lia.
    replace (0 + pos1) with (pos1) by lia.
    replace (field_address (tarray tint (Zlength Hl0 - pos1)) [ArraySubsc 0] (field_address0 (tarray tint (Zlength Hl0)) [ArraySubsc pos1] a0))
      with (field_address (tarray tint (Zlength Hl0)) [ArraySubsc pos1] a0).
    2: {
      rewrite field_address0_offset.
      2: {
        apply field_compatible0_cons.
        simpl; split; [lia | tauto].
      }
      rewrite !field_address_offset.
      3: {
        apply field_compatible_cons.
        simpl; split; [lia | tauto].
      }
      2: {
        simpl.
        apply field_compatible_cons.
        simpl; split; [lia |].
        rewrite field_address0_offset in H22.
        + tauto.
        + apply field_compatible0_cons.
          simpl; split; [lia | tauto].  
      }
      simpl.
      rewrite offset_offset_val.
      f_equal; lia.
    }
    entailer!.
  }
  forward.
  Exists (list_swap Hl0 (pos1 / 2) pos1) (pos1 / 2) a0 (Vint (IntRepr (pos1 / 2))).
  entailer!.
  2: {
    pose proof split2_data_at_Tarray Tsh tint (Zlength Hl0) (pos1).
    erewrite H0; [ | lia | | | |].
    3: {
      rewrite sublist_same; [reflexivity | lia | rewrite !Zlength_map].
      rewrite list_swap_len by lia.
      reflexivity.
    }
    2: {
      rewrite !Zlength_map.
      rewrite list_swap_len by lia.
      lia.
    }
    2: rewrite !sublist_map; reflexivity.
    2: rewrite !sublist_map; reflexivity.
    change (Tarray tint (pos1) noattr) with (tarray tint (pos1)).
    change (Tarray tint (Zlength Hl0 - pos1) noattr) with (tarray tint (Zlength Hl0 - pos1)).
    pose proof SingletonHole.array_with_hole_elim Tsh tint (pos1 / 2) pos1
      (Vint(IntRepr((Znth pos1 Hl0)))) (map Vint (map IntRepr (sublist 0 pos1 Hl0))) a0.
    rewrite !upd_Znth_map in H20.
    replace (sublist 0 pos1 (list_swap Hl0 (pos1 / 2) pos1))
      with (upd_Znth (pos1 / 2) (sublist 0 pos1 Hl0) (Znth pos1 Hl0)).
    replace (field_address (tarray tint (Zlength Hl0)) [ArraySubsc (pos1 / 2)] a0)
      with (field_address (tarray tint pos1) [ArraySubsc (pos1 / 2)] a0).
    3: {
      unfold list_swap.
      rewrite sublist_upd_Znth_lr; [ | lia | rewrite upd_Znth_Zlength; lia].
      rewrite sublist_upd_Znth_l by lia.
      replace (pos1 / 2 - 0) with (pos1 / 2) by lia.
      tauto.
    }
    2: {
      rewrite <- !offset_val_field_address; [ tauto | lia | tauto | lia | ].
      eapply field_compatible_Tarray_split in H15.
      + destruct H15.
        apply H15.
      + lia.
    }
    sep_apply H20.
    entailer!.
    pose proof SingletonHole.array_with_hole_elim Tsh tint 0 (Zlength Hl0 - pos1)
      (Vint(IntRepr((Znth (pos1/2) Hl0)))) (map Vint (map IntRepr (sublist pos1 (Zlength Hl0) Hl0)))
      (field_address0 (Tarray tint (Zlength Hl0) noattr) [ArraySubsc pos1] a0).
    rewrite !upd_Znth_map in H26.
    replace (sublist pos1 (Zlength Hl0) (list_swap Hl0 (pos1 / 2) pos1))
      with (upd_Znth 0 (sublist pos1 (Zlength Hl0) Hl0) (Znth (pos1 / 2) Hl0)).
    replace (field_address (tarray tint (Zlength Hl0)) [ArraySubsc pos1] a0)
      with (field_address (tarray tint (Zlength Hl0 - pos1)) [ArraySubsc 0] (field_address0 (Tarray tint (Zlength Hl0) noattr) [ArraySubsc pos1] a0)).
    3: {
      unfold list_swap.
      rewrite sublist_upd_Znth_r; [ | lia | rewrite upd_Znth_Zlength; lia].
      rewrite sublist_upd_Znth_lr by lia.
      replace (pos1 - pos1) with 0 by lia.
      tauto.
    }
    2: {
      rewrite field_address0_offset.
      2: {
        apply field_compatible0_cons.
        simpl; split; [lia | tauto].
      }
      rewrite !field_address_offset.
      3: {
        apply field_compatible_cons.
        simpl; split; [lia |].
        pose proof field_compatible_Tarray_split tint pos1 (Zlength Hl0) a0 ltac:(lia).
        apply H27 in H15.
        + destruct H15.
          rewrite field_address0_offset in H28; simpl in H28.
          - apply H28.
          - apply field_compatible0_cons.
            simpl; split; [lia | apply H27; tauto]. 
      }
      2: {
        apply field_compatible_cons.
        simpl; split; [lia | tauto].
      }
      simpl.
      rewrite offset_offset_val.
      f_equal; lia.
    }
    sep_apply H26.
    entailer!.
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
