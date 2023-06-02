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
  forward. forward. forward. forward. forward.
  forward_call ((size0+1), (size0+1), a', Maxsize, Hl ++ [val0], a', (Vint (IntRepr (size0+1)))).
  
Admitted.

End SH_Proof.
