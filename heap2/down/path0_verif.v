Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require heap.down.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.down.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros; Intros; subst.
  forward.
  Exists Hl pos0 a0 (Vint (IntRepr pos0)) (Vint (IntRepr size0)).
  entailer!.
  unfold down_inv.
  exists 0%nat.
  unfold RelsDomain.nsteps.
  reflexivity.
Qed.

End SH_Proof.
