Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.top.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.top.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros; Intros; subst.
  sep_apply list_length; [lia|].
  Intros.
  forward. forward.
  Exists  (Vint (IntRepr (Znth 1 Hl))).
  entailer!.
Qed.

End SH_Proof.
