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
  forward.
  (* forward. forward.
  forward. forward.
  forward_call (size0-1, 1, a0, Maxsize, Hl, a0, (Vint (IntRepr 1)), (Vint (Int.sub (IntRepr size0) (IntRepr 1)))). *)
Admitted.

End SH_Proof.
