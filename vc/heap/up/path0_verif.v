Require Import utils.VSTALib.

Require Import cprogs.heap.program.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.annotation.
Require cprogs.heap.up.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.heap.up.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros; Intros.
  forward.
  Exists Hl pos0 a' (Vint (IntRepr pos0)).
  entailer!.
  unfold up.
  unfold list_relation.heap_list_up.
  exists 0%nat.
  unfold RelsDomain.nsteps.
  reflexivity.
Qed.

End SH_Proof.