Require Import utils.VSTALib.

Require Import heap.program.
Require Import heap.definitions.
Require Import heap.annotation.
Require Import SetsClass.SetsClass.
Require Import Classical_Prop.
Require heap.down.path6.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include heap.down.path6.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros Hl0 pos1 a pos size.
  subst.
  sep_apply list_length; [lia | ].
  Intros.
  sep_apply int_array_is_ptr; [lia | ].
  Intros.
  forward.
  forward.
  assert ((Int.shl (IntRepr pos1) (IntRepr 1)) = Int.repr (2 * pos1)). {
    unfold Int.shl.
    unfold Z.shiftl.
    simpl.
    rewrite Int.unsigned_repr by rep_lia.
    f_equal; lia.
  }
  rewrite H3, Int.signed_repr in H1 by rep_lia.
  assert (Int.unsigned (Int.shl (IntRepr pos1) (IntRepr 1)) = 2 * pos1). {
    rewrite H3.
    rewrite Int.unsigned_repr by rep_lia.
    reflexivity.
  }
  forward.
  rewrite H12.
  forward.
  forward.
  forward.
  forward.
  lia.
Qed.

End SH_Proof.
