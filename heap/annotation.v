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
Definition ___return := ret_temp.

Definition f_swap_spec_annotation :=
  ANNOTATION_WITH y x py0 px0 a' b',
  ((PROP ((b' = py0); (a' = px0))
  LOCAL (temp _a a'; temp _b b')
  SEP ((store_int px0 x); (store_int py0 y))),
  (PROP ()
  LOCAL ()
  SEP ((store_int px0 y); (store_int py0 x)))).

Definition f_swap_spec_complex :=
  ltac:(uncurry_funcspec f_swap_spec_annotation).

Definition f_swap_funsig: funsig :=
  ((_a, (tptr tint)) :: (_b, (tptr tint)) :: nil, tvoid).

Definition swap_spec :=
  ltac:(make_funcspec _swap f_swap_funsig f_swap_spec_complex).

Definition f_swap_hint (para: GET_PARA_TYPE f_swap_spec_annotation) :=
  match para with
  | (y, x, py0, px0, a', b') =>
  (Csequence
    (Cset _t (Ederef (Etempvar _a (tptr tint)) tint))
    (Csequence
      (Csequence
        (Cset _t'1 (Ederef (Etempvar _b (tptr tint)) tint))
        (Cassign (Ederef (Etempvar _a (tptr tint)) tint)
          (Etempvar _t'1 tint)))
      (Cassign (Ederef (Etempvar _b (tptr tint)) tint) (Etempvar _t tint))))  end.


Definition f_up_spec_annotation :=
  ANNOTATION_WITH size0 pos0 Maxsize Hl a' pos',
  ((PROP ((MaxHeap_p Hl (Z.add pos0 1) size0); (MaxHeap Hl (Z.sub pos0 1)); (pos' = (Vint (IntRepr pos0))); (Z.le size0 Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0))
  LOCAL (temp _a a'; temp _pos pos')
  SEP ((store_int_array a' Hl Maxsize))),
  (EX Hl_final pos1 n a pos,
    (PROP ((MaxHeap Hl_final size0); (Hl_final = (up Hl size0 pos0 pos1)); (pos1 = (shr pos0 n)); (pos = (Vint (IntRepr pos1))))
    LOCAL (temp _a a; temp _pos pos)
    SEP ((store_int_array a Hl_final Maxsize))))%assert).

Definition f_up_spec_complex :=
  ltac:(uncurry_funcspec f_up_spec_annotation).

Definition f_up_funsig: funsig :=
  ((_a, (tptr tint)) :: (_pos, tint) :: nil, tvoid).

Definition up_spec :=
  ltac:(make_funcspec _up f_up_funsig f_up_spec_complex).

Definition f_up_hint (para: GET_PARA_TYPE f_up_spec_annotation) :=
  match para with
  | (size0, pos0, Maxsize, Hl, a', pos') =>
  (Cloop
    (Csequence
      (Cassert
        (EX Hl0 pos1 n a pos,
          (PROP ((MaxHeap_p Hl0 (Z.add pos1 1) size0); (MaxHeap Hl0 (Z.sub pos1 1)); (Hl0 = (up Hl size0 pos0 pos1)); (pos1 = (shr pos0 n)); (pos = (Vint (IntRepr pos1))))
          LOCAL (temp _a a; temp _pos pos)
          SEP ((store_int_array a Hl0 Maxsize))))%assert)
      (Csequence
        (Cifthenelse (Ebinop Ogt (Etempvar _pos tint)
                       (Econst_int (Int.repr 1) tint) tint)
          Cskip
          Cbreak)
        (Csequence
          (Csequence
            (Cset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _pos tint)
                  (tptr tint)) tint))
            (Csequence
              (Cset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _a (tptr tint))
                    (Ebinop Oshr (Etempvar _pos tint)
                      (Econst_int (Int.repr 1) tint) tint) (tptr tint)) tint))
              (Cifthenelse (Ebinop Ole (Etempvar _t'1 tint)
                             (Etempvar _t'2 tint) tint)
                Cbreak
                Cskip)))
          (Csequence
            (Ccall None
              (Evar _swap (Tfunction
                            (Tcons (tptr tint) (Tcons (tptr tint) Tnil))
                            tvoid cc_default))
              ((Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _pos tint)
                 (tptr tint)) ::
               (Ebinop Oadd (Etempvar _a (tptr tint))
                 (Ebinop Oshr (Etempvar _pos tint)
                   (Econst_int (Int.repr 1) tint) tint) (tptr tint)) :: nil))
            (Cset _pos
              (Ebinop Oshr (Etempvar _pos tint)
                (Econst_int (Int.repr 1) tint) tint))))))
    Cskip)  end.


Definition f_down_spec_annotation :=
  ANNOTATION_WITH size0 pos0 Maxsize Hl a' pos' size',
  ((PROP ((MaxHeap_p Hl (Z.add pos0 1) size0); (MaxHeap Hl (Z.sub pos0 1)); (size' = (Vint (IntRepr size0))); (pos' = (Vint (IntRepr pos0))); (Z.le size0 Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0))
  LOCAL (temp _a a'; temp _pos pos'; temp _size size')
  SEP ((store_int_array a' Hl Maxsize))),
  (EX Hl_final pos1 n a pos size,
    (PROP ((MaxHeap Hl_final size0); (Hl_final = (down Hl size0 pos0 pos1)); (size = (Vint (IntRepr size0))); (pos0 = (shr pos1 n)); (pos = (Vint (IntRepr pos1))); (Z.le pos1 size0))
    LOCAL (temp _a a; temp _pos pos; temp _size size)
    SEP ((store_int_array a Hl_final Maxsize))))%assert).

Definition f_down_spec_complex :=
  ltac:(uncurry_funcspec f_down_spec_annotation).

Definition f_down_funsig: funsig :=
  ((_a, (tptr tint)) :: (_size, tint) :: (_pos, tint) :: nil, tvoid).

Definition down_spec :=
  ltac:(make_funcspec _down f_down_funsig f_down_spec_complex).

Definition f_down_hint (para: GET_PARA_TYPE f_down_spec_annotation) :=
  match para with
  | (size0, pos0, Maxsize, Hl, a', pos', size') =>
  (Cloop
    (Csequence
      (Cassert
        (EX Hl0 pos1 n a pos size,
          (PROP ((MaxHeap_p Hl0 (Z.add pos1 1) size0); (MaxHeap Hl0 (Z.sub pos1 1)); (Hl0 = (down Hl size0 pos0 pos1)); (size = (Vint (IntRepr size0))); (pos0 = (shr pos1 n)); (pos = (Vint (IntRepr pos1))); (Z.le pos1 size0))
          LOCAL (temp _a a; temp _pos pos; temp _size size)
          SEP ((store_int_array a Hl0 Maxsize))))%assert)
      (Csequence
        (Cifthenelse (Ebinop Ole
                       (Ebinop Oshl (Etempvar _pos tint)
                         (Econst_int (Int.repr 1) tint) tint)
                       (Etempvar _size tint) tint)
          Cskip
          Cbreak)
        (Csequence
          (Cset _t (Etempvar _pos tint))
          (Csequence
            (Csequence
              (Cset _t'3
                (Ederef
                  (Ebinop Oadd (Etempvar _a (tptr tint))
                    (Ebinop Oshl (Etempvar _pos tint)
                      (Econst_int (Int.repr 1) tint) tint) (tptr tint)) tint))
              (Csequence
                (Cset _t'4
                  (Ederef
                    (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t tint)
                      (tptr tint)) tint))
                (Cifthenelse (Ebinop Ogt (Etempvar _t'3 tint)
                               (Etempvar _t'4 tint) tint)
                  (Cset _t
                    (Ebinop Oshl (Etempvar _pos tint)
                      (Econst_int (Int.repr 1) tint) tint))
                  Cskip)))
            (Csequence
              (Cifthenelse (Ebinop Ole
                             (Ebinop Oor
                               (Ebinop Oshl (Etempvar _pos tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                               (Econst_int (Int.repr 1) tint) tint)
                             (Etempvar _size tint) tint)
                (Csequence
                  (Cset _t'1
                    (Ederef
                      (Ebinop Oadd (Etempvar _a (tptr tint))
                        (Ebinop Oor
                          (Ebinop Oshl (Etempvar _pos tint)
                            (Econst_int (Int.repr 1) tint) tint)
                          (Econst_int (Int.repr 1) tint) tint) (tptr tint))
                      tint))
                  (Csequence
                    (Cset _t'2
                      (Ederef
                        (Ebinop Oadd (Etempvar _a (tptr tint))
                          (Etempvar _t tint) (tptr tint)) tint))
                    (Cifthenelse (Ebinop Ogt (Etempvar _t'1 tint)
                                   (Etempvar _t'2 tint) tint)
                      (Cset _t
                        (Ebinop Oor
                          (Ebinop Oshl (Etempvar _pos tint)
                            (Econst_int (Int.repr 1) tint) tint)
                          (Econst_int (Int.repr 1) tint) tint))
                      Cskip)))
                Cskip)
              (Csequence
                (Cifthenelse (Ebinop Oeq (Etempvar _t tint)
                               (Etempvar _pos tint) tint)
                  Cbreak
                  Cskip)
                (Csequence
                  (Ccall None
                    (Evar _swap (Tfunction
                                  (Tcons (tptr tint)
                                    (Tcons (tptr tint) Tnil)) tvoid
                                  cc_default))
                    ((Ebinop Oadd (Etempvar _a (tptr tint))
                       (Etempvar _pos tint) (tptr tint)) ::
                     (Ebinop Oadd (Etempvar _a (tptr tint))
                       (Etempvar _t tint) (tptr tint)) :: nil))
                  (Cset _pos (Etempvar _t tint)))))))))
    Cskip)  end.


Definition f_push_spec_annotation :=
  ANNOTATION_WITH val0 size0 Maxsize Hl a' size' val',
  ((PROP ((MaxHeap Hl size0); (size' = (Vint (IntRepr size0))); (val' = (Vint (IntRepr val0))); (Z.lt size0 Maxsize); (Z.le 0 size0))
  LOCAL (temp _a a'; temp _size size'; temp _val val')
  SEP ((store_int_array a' Hl Maxsize))),
  (EX Hl_final a size val,
    (PROP ((MaxHeap Hl_final (Z.add size0 1)); (Hl_final = (push Hl size0 val0)); (size = (Vint (IntRepr (Z.add size0 1)))); (val = (Vint (IntRepr val0))))
    LOCAL (temp _a a; temp _size size; temp _val val)
    SEP ((store_int_array a Hl_final Maxsize))))%assert).

Definition f_push_spec_complex :=
  ltac:(uncurry_funcspec f_push_spec_annotation).

Definition f_push_funsig: funsig :=
  ((_a, (tptr tint)) :: (_size, (tptr tint)) :: (_val, tint) :: nil, tvoid).

Definition push_spec :=
  ltac:(make_funcspec _push f_push_funsig f_push_spec_complex).

Definition f_push_hint (para: GET_PARA_TYPE f_push_spec_annotation) :=
  match para with
  | (val0, size0, Maxsize, Hl, a', size', val') =>
  (Csequence
    (Csequence
      (Cset _t'3 (Ederef (Etempvar _size (tptr tint)) tint))
      (Cassign (Ederef (Etempvar _size (tptr tint)) tint)
        (Ebinop Oadd (Etempvar _t'3 tint) (Econst_int (Int.repr 1) tint)
          tint)))
    (Csequence
      (Csequence
        (Cset _t'2 (Ederef (Etempvar _size (tptr tint)) tint))
        (Cassign
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t'2 tint)
              (tptr tint)) tint) (Etempvar _val tint)))
      (Csequence
        (Cset _t'1 (Ederef (Etempvar _size (tptr tint)) tint))
        (Ccall None
          (Evar _up (Tfunction (Tcons (tptr tint) (Tcons tint Tnil)) tvoid
                      cc_default))
          ((Etempvar _a (tptr tint)) :: (Etempvar _t'1 tint) :: nil)))))  end.


Definition f_pop_spec_annotation :=
  ANNOTATION_WITH size0 Maxsize Hl a' size',
  ((PROP ((MaxHeap Hl size0); (size' = (Vint (IntRepr size0))); (Z.le size0 Maxsize); (Z.le 0 size0))
  LOCAL (temp _a a'; temp _size size')
  SEP ((store_int_array a' Hl Maxsize))),
  (EX Hl_final size1 a size __return,
    (PROP ((MaxHeap Hl_final (Z.add size0 1)); (Hl_final = (pop Hl size0)); (size = (Vint (IntRepr size1))); (size1 = (pop_length Hl size0)); (__return = (Vint (IntRepr (pop_result Hl size0)))))
    LOCAL (temp _a a; temp _size size; temp ___return __return)
    SEP ((store_int_array a Hl_final Maxsize))))%assert).

Definition f_pop_spec_complex :=
  ltac:(uncurry_funcspec f_pop_spec_annotation).

Definition f_pop_funsig: funsig :=
  ((_a, (tptr tint)) :: (_size, (tptr tint)) :: nil, tint).

Definition pop_spec :=
  ltac:(make_funcspec _pop f_pop_funsig f_pop_spec_complex).

Definition f_pop_hint (para: GET_PARA_TYPE f_pop_spec_annotation) :=
  match para with
  | (size0, Maxsize, Hl, a', size') =>
  (Csequence
    (Csequence
      (Cset _t'5 (Ederef (Etempvar _size (tptr tint)) tint))
      (Cifthenelse (Ebinop Oeq (Etempvar _t'5 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Creturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        Cskip))
    (Csequence
      (Csequence
        (Cset _t'3 (Ederef (Etempvar _size (tptr tint)) tint))
        (Csequence
          (Cset _t'4
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t'3 tint)
                (tptr tint)) tint))
          (Cassign
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint)) tint)
            (Etempvar _t'4 tint))))
      (Csequence
        (Csequence
          (Cset _t'2 (Ederef (Etempvar _size (tptr tint)) tint))
          (Cassign (Ederef (Etempvar _size (tptr tint)) tint)
            (Ebinop Osub (Etempvar _t'2 tint) (Econst_int (Int.repr 1) tint)
              tint)))
        (Csequence
          (Csequence
            (Cset _t'1 (Ederef (Etempvar _size (tptr tint)) tint))
            (Ccall None
              (Evar _down (Tfunction
                            (Tcons (tptr tint)
                              (Tcons tint (Tcons tint Tnil))) tvoid
                            cc_default))
              ((Etempvar _a (tptr tint)) :: (Etempvar _t'1 tint) ::
               (Econst_int (Int.repr 1) tint) :: nil)))
          (Creturn (Some (Econst_int (Int.repr 0) tint)))))))  end.


Definition f_top_spec_annotation :=
  ANNOTATION_WITH Maxsize Hl a',
  ((PROP ((Z.ge Maxsize 1))
  LOCAL (temp _a a')
  SEP ((store_int_array a' Hl Maxsize))),
  (EX a __return,
    (PROP ((__return = (Vint (IntRepr (Znth 1 Hl)))))
    LOCAL (temp _a a; temp ___return __return)
    SEP ((store_int_array a Hl Maxsize))))%assert).

Definition f_top_spec_complex :=
  ltac:(uncurry_funcspec f_top_spec_annotation).

Definition f_top_funsig: funsig :=
  ((_a, (tptr tint)) :: nil, tint).

Definition top_spec :=
  ltac:(make_funcspec _top f_top_funsig f_top_spec_complex).

Definition f_top_hint (para: GET_PARA_TYPE f_top_spec_annotation) :=
  match para with
  | (Maxsize, Hl, a') =>
  (Csequence
    (Cset _t'1
      (Ederef
        (Ebinop Oadd (Etempvar _a (tptr tint)) (Econst_int (Int.repr 1) tint)
          (tptr tint)) tint))
    (Creturn (Some (Etempvar _t'1 tint))))  end.


Definition Gprog : funspecs :=
  ltac:(with_library prog (swap_spec :: up_spec :: down_spec :: push_spec :: pop_spec :: top_spec :: nil)).

Notation "'Delta_specs_swap'" := (DELTA_SPECS (f_swap, Vprog, Gprog)).

Notation "'Delta_swap' DS" := (DELTA (f_swap, Vprog, Gprog, @nil (prod ident Annotation), DS)) (at level 99).

Notation "'Delta_specs_up'" := (DELTA_SPECS (f_up, Vprog, Gprog)).

Notation "'Delta_up' DS" := (DELTA (f_up, Vprog, Gprog, @nil (prod ident Annotation), DS)) (at level 99).

Notation "'Delta_specs_down'" := (DELTA_SPECS (f_down, Vprog, Gprog)).

Notation "'Delta_down' DS" := (DELTA (f_down, Vprog, Gprog, @nil (prod ident Annotation), DS)) (at level 99).

Notation "'Delta_specs_push'" := (DELTA_SPECS (f_push, Vprog, Gprog)).

Notation "'Delta_push' DS" := (DELTA (f_push, Vprog, Gprog, @nil (prod ident Annotation), DS)) (at level 99).

Notation "'Delta_specs_pop'" := (DELTA_SPECS (f_pop, Vprog, Gprog)).

Notation "'Delta_pop' DS" := (DELTA (f_pop, Vprog, Gprog, @nil (prod ident Annotation), DS)) (at level 99).

Notation "'Delta_specs_top'" := (DELTA_SPECS (f_top, Vprog, Gprog)).

Notation "'Delta_top' DS" := (DELTA (f_top, Vprog, Gprog, @nil (prod ident Annotation), DS)) (at level 99).