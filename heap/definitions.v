Require Import FloydSeq.proofauto.
Require Import cprogs.heap.program.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
Notation "'store_int' p x" :=
  (@data_at CompSpecs Tsh tint (Vint(IntRepr(x))) p)
  (x at level 0, p at level 0, at level 0).
Notation "'store_int_array' p l size" :=
  (@data_at CompSpecs Tsh (tarray tint size) (map Vint (map Int.repr l)) p)
  (p at level 0, l at level 0, size at level 0, at level 0).

Parameter MaxHeap : list Z -> Z -> Prop.
Parameter MaxHeap_p : list Z -> Z -> Z -> Prop.
Parameter shr : Z -> Z -> Z.

Parameter up : list Z -> Z -> Z -> Z -> list Z.
Parameter down : list Z -> Z -> Z -> Z -> list Z.
Parameter push : list Z -> Z -> Z -> list Z.
Parameter pop : list Z -> Z -> list Z.
Parameter pop_length : list Z -> Z -> Z.
Parameter pop_result : list Z -> Z -> Z.

Lemma MaxHeap_MaxHeap_p : forall l size, MaxHeap l size -> MaxHeap_p l 1 size.
Proof. Admitted.