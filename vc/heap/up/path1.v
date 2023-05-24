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
  let Delta_specs := Delta_specs_up in
  let Delta := Delta_up Delta_specs in
  semax Delta (EX Hl0 pos1 a pos,
                (PROP ((MaxHeap_p Hl0 pos1 size0); (MaxHeap Hl0 (Z.sub pos1 1)); (up Hl size0 pos0 pos1 Hl0); (pos = (Vint (IntRepr pos1))))
                LOCAL (temp _a a; temp _pos pos)
                SEP ((store_int_array a Hl0 Maxsize))))%assert
  (Ssequence
    (Sifthenelse (Ebinop Ogt (Etempvar _pos tint)
                   (Econst_int (Int.repr 1) tint) tint)
      Sskip
      Sbreak)
    (Ssequence
      (Sset _t'1
        (Ederef
          (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _pos tint)
            (tptr tint)) tint))
      (Ssequence
        (Sset _t'2
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tint))
              (Ebinop Oshr (Etempvar _pos tint)
                (Econst_int (Int.repr 1) tint) tint) (tptr tint)) tint))
        (Ssequence
          (Sifthenelse (Ebinop Ole (Etempvar _t'1 tint) (Etempvar _t'2 tint)
                         tint)
            Sbreak
            Sskip)
          (Ssequence
            (Scall None
              (Evar _swap (Tfunction
                            (Tcons (tptr tint) (Tcons (tptr tint) Tnil))
                            tvoid cc_default))
              ((Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _pos tint)
                 (tptr tint)) ::
               (Ebinop Oadd (Etempvar _a (tptr tint))
                 (Ebinop Oshr (Etempvar _pos tint)
                   (Econst_int (Int.repr 1) tint) tint) (tptr tint)) :: nil))
            (Sset _pos
              (Ebinop Oshr (Etempvar _pos tint)
                (Econst_int (Int.repr 1) tint) tint)))))))
  (normal_split_assert
  (EX Hl0 pos1 a pos,
    (PROP ((MaxHeap_p Hl0 pos1 size0); (MaxHeap Hl0 (Z.sub pos1 1)); (up Hl size0 pos0 pos1 Hl0); (pos = (Vint (IntRepr pos1))))
    LOCAL (temp _a a; temp _pos pos)
    SEP ((store_int_array a Hl0 Maxsize))))%assert).
