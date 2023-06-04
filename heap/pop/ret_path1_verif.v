Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.pop.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.pop.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros; Intros; subst.
  forward. forward. forward.
  sep_apply list_length; [lia|].
  Intros.
  forward. forward. forward. forward. forward. forward. forward.
  forward_call ((size0-1), 1, a0, Maxsize, upd_Znth 1 Hl (Znth size0 Hl), a0, (Vint (IntRepr 1)), (Vint (IntRepr (size0-1)))).
  + rewrite ! upd_Znth_map.
    entailer!.
  + split; [reflexivity|]. 
    split; [reflexivity|].
    split; [reflexivity|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    pose proof all_int_Znth Hl size0 H5 ltac:(lia).
    destruct H7.
    apply all_int_upd_Znth; tauto.
  + Intros vret; destruct vret as [l2 pos1]; subst.
    forward.
    Exists l2 (size0-1) (Vint (IntRepr (0))).
    entailer!.
    split.
    - unfold pop.
      right.
      split; [lia|].
      unfold heap_pop; right.
      split; [rewrite Zlength_firstn; lia|].
      exists pos1.
      unfold down in H7.
      unfold fst, snd in H7.
      rewrite Zlength_firstn.
      replace (Z.max 0 (size0 + 1)) with (size0 + 1) by lia.
      replace (Z.min (size0 + 1) (Zlength Hl)) with (size0 + 1) by lia.
      replace (size0 + 1 - 1) with size0 by lia.
      replace (size0 - 1 + 1) with size0 in H7 by lia.
      assert (firstn (Z.to_nat size0) (upd_Znth 1 Hl (Znth size0 Hl)) = firstn (Z.to_nat size0)
        (upd_Znth 1 (firstn (Z.to_nat (size0 + 1)) Hl)
          (Znth size0 (firstn (Z.to_nat (size0 + 1)) Hl)))); [|rewrite <- H15; tauto].
      rewrite ! Znth_firstn; [|lia].
      rewrite ! firstn_eq_sublist.
      rewrite ! sublist_upd_Znth_lr; try lia; [|rewrite Zlength_sublist; lia].
      rewrite ! sublist_firstn.
      rewrite List.firstn_firstn.
      replace (Init.Nat.min (Z.to_nat size0) (Z.to_nat (size0 + 1))) with (Z.to_nat size0) by lia.
      reflexivity.
    - split.
      * destruct size0; [lia | unfold pop_length; reflexivity| lia ].
      * destruct size0; [lia | unfold pop_result; reflexivity| lia ].
Qed.

End SH_Proof.
