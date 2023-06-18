Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.pop.ret_path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.pop.ret_path2.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros; Intros; subst.
  sep_apply list_length; [lia|]; Intros.
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  Exists (upd_Znth 1 Hl (Znth size0 Hl)) (size0-1) (Vint (IntRepr (0))).
  rewrite ! upd_Znth_map.
  entailer!.
  split.
   unfold pop.
    right.
    split; [lia|].
    assert (size0 = 1) by lia.
    subst.
    unfold heap_pop.
    
    left.
    split.
    - rewrite Zlength_firstn.
      lia. 
    - rewrite Zlength_firstn.
      rewrite upd_Znth_Zlength; [|lia].
      lia.
  + split.
    - destruct size0; [lia | unfold pop_length; reflexivity| lia ].
    - destruct size0; [lia | unfold pop_result; reflexivity| lia ].
Qed.

End SH_Proof.