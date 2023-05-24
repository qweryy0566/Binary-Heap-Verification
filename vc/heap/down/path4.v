From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Csplit.semantics.
Require Import utils.AClightNotations.
Require VST.floyd.proofauto.
Require Import FloydSeq.proofauto.
Require Import Csplit.strong.
Require Import FloydSeq.client_lemmas.
Require Import Csplit.strongSoundness.
Require Import Csplit.AClightFunc.
Local Open Scope Z_scope.
Import AClightNotations.
Require Import cprogs.heap.program.
Require Import cprogs.heap.definitions.
Require Import cprogs.heap.annotation.
Import compcert.cfrontend.Clight.

Definition functional_correctness_statement: Prop :=
  forall (Espec: OracleKind) Hl Maxsize size0 pos0,
  let Delta_specs := Delta_specs_down in
  let Delta := Delta_down Delta_specs in
  semax Delta (EX Hl0 pos1 a pos size,
                (PROP ((MaxHeap_p Hl0 (Z.add pos1 1) size0); (MaxHeap Hl0 pos1); (down Hl size0 pos0 pos1 Hl0); (size = (Vint (IntRepr size0))); (pos = (Vint (IntRepr pos1))); (Z.le pos1 size0))
                LOCAL (temp _a a; temp _pos pos; temp _size size)
                SEP ((store_int_array a Hl0 Maxsize))))%assert
  (Ssequence
    (Sifthenelse (Ebinop Ole
                   (Ebinop Oshl (Etempvar _pos tint)
                     (Econst_int (Int.repr 1) tint) tint)
                   (Etempvar _size tint) tint)
      Sskip
      Sbreak)
    (Ssequence
      (Sset _t (Etempvar _pos tint))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tint))
              (Ebinop Oshl (Etempvar _pos tint)
                (Econst_int (Int.repr 1) tint) tint) (tptr tint)) tint))
        (Ssequence
          (Sset _t'4
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t tint)
                (tptr tint)) tint))
          (Ssequence
            (Sifthenelse (Ebinop Ogt (Etempvar _t'3 tint)
                           (Etempvar _t'4 tint) tint)
              Sbreak
              Sskip)
            (Ssequence
              (Sifthenelse (Ebinop Ole
                             (Ebinop Oor
                               (Ebinop Oshl (Etempvar _pos tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                               (Econst_int (Int.repr 1) tint) tint)
                             (Etempvar _size tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Etempvar _a (tptr tint))
                      (Ebinop Oor
                        (Ebinop Oshl (Etempvar _pos tint)
                          (Econst_int (Int.repr 1) tint) tint)
                        (Econst_int (Int.repr 1) tint) tint) (tptr tint))
                    tint))
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd (Etempvar _a (tptr tint))
                        (Etempvar _t tint) (tptr tint)) tint))
                  (Ssequence
                    (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tint)
                                   (Etempvar _t'2 tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t
                        (Ebinop Oor
                          (Ebinop Oshl (Etempvar _pos tint)
                            (Econst_int (Int.repr 1) tint) tint)
                          (Econst_int (Int.repr 1) tint) tint))
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Etempvar _t tint)
                                       (Etempvar _pos tint) tint)
                          Sbreak
                          Sskip)
                        (Ssequence
                          (Scall None
                            (Evar _swap (Tfunction
                                          (Tcons (tptr tint)
                                            (Tcons (tptr tint) Tnil)) tvoid
                                          cc_default))
                            ((Ebinop Oadd (Etempvar _a (tptr tint))
                               (Etempvar _pos tint) (tptr tint)) ::
                             (Ebinop Oadd (Etempvar _a (tptr tint))
                               (Etempvar _t tint) (tptr tint)) :: nil))
                          (Sset _pos (Etempvar _t tint))))))))))))))
  (normal_split_assert
  (EX Hl0 pos1 a pos size,
    (PROP ((MaxHeap_p Hl0 (Z.add pos1 1) size0); (MaxHeap Hl0 pos1); (down Hl size0 pos0 pos1 Hl0); (size = (Vint (IntRepr size0))); (pos = (Vint (IntRepr pos1))); (Z.le pos1 size0))
    LOCAL (temp _a a; temp _pos pos; temp _size size)
    SEP ((store_int_array a Hl0 Maxsize))))%assert).
