Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.push.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.push.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros; Intros; subst.
  sep_apply list_length; [lia|]; Intros.
  forward. forward. forward. forward. forward.
  forward_call ((size0+1), (size0+1), a', Maxsize, upd_Znth (size0+1) Hl val0, a', (Vint (IntRepr (size0+1)))). 
  + rewrite ! upd_Znth_map.
    entailer!.
  + pose proof (all_int_upd_Znth Hl (size0+1) val0 H8 H7 H6).
    split; [reflexivity|].
    split; [reflexivity|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [tauto|].
    split; [lia|tauto].
  + Intros vret.
    sep_apply list_length; [lia|]; Intros.
    destruct vret as [l2 pos2].
    simpl fst; simpl snd. 
    Exists l2.
    entailer!.
    unfold push.
    unfold fst, snd in H0.
    unfold heap_push.
    exists pos2.
    unfold up in H0.
    unfold fst in H1.
    replace (Zlength (firstn (Z.to_nat (size0 + 1)) l2)) with (size0 + 1).
    2: {
      rewrite Zlength_firstn.
      simpl fst in H2.
      replace (Z.max 0 (size0+1)) with (size0 + 1) by lia.
      lia.
    }
    replace (Zlength (firstn (Z.to_nat (size0 + 1)) Hl)) with (size0 + 1).
    2: {
      rewrite Zlength_firstn.
      simpl fst in H2.
      replace (Z.max 0 (size0+1)) with (size0 + 1) by lia.
      lia.
    }
    replace (firstn (Z.to_nat (size0 + 1)) Hl ++ [val0]) with (firstn (Z.to_nat (size0 + 1 + 1)) (upd_Znth (size0 + 1) Hl val0)).
    replace (size0 + 2) with (size0 + 1 + 1) by lia.
    - tauto.
    - assert (Z.of_nat (Z.to_nat (size0 + 1))  < Zlength Hl) by lia.
    pose proof (firstn_app_upd_Znth Hl val0 (Z.to_nat (size0 + 1)) H13).
    rewrite Z2Nat_id' in H14.
    replace (Z.max 0 (size0 + 1)) with (size0+1) in H14 by lia.
    assert ((Z.to_nat (size0 + 1) + 1) = Z.to_nat (size0 + 1 + 1))%nat by lia.
    rewrite <- H15.
    tauto.
Qed.

End SH_Proof.