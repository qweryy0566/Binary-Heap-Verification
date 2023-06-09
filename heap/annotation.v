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
Require Import heap.program.
Require Import heap.definitions.
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
  ANNOTATION_WITH size0 pos0 a0 Maxsize Hl a' pos',
  ((PROP ((pos' = (Vint (IntRepr pos0))); (a' = a0); (Z.le (Z.add size0 1) Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0); (Z.le Maxsize (Int.max_signed )); (Z.le 2 Maxsize); (all_int Hl))
  LOCAL (temp _a a'; temp _pos pos')
  SEP ((store_int_array a0 Hl Maxsize))),
  (EX Hl_final pos1,
    (PROP ((up Hl size0 pos0 pos1 Hl_final))
    LOCAL ()
    SEP ((store_int_array a0 Hl_final Maxsize))))%assert).

Definition f_up_spec_complex :=
  ltac:(uncurry_funcspec f_up_spec_annotation).

Definition f_up_funsig: funsig :=
  ((_a, (tptr tint)) :: (_pos, tint) :: nil, tvoid).

Definition up_spec :=
  ltac:(make_funcspec _up f_up_funsig f_up_spec_complex).

Definition f_up_hint (para: GET_PARA_TYPE f_up_spec_annotation) :=
  match para with
  | (size0, pos0, a0, Maxsize, Hl, a', pos') =>
  (Cloop
    (Csequence
      (Cassert
        (EX Hl0 pos1 a pos,
          (PROP ((up_inv Hl size0 pos0 pos1 Hl0); (pos = (Vint (IntRepr pos1))); (a = a0); (Z.le pos1 size0); (Z.le 1 pos1); (Z.le (Z.add size0 1) Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0); (Z.le Maxsize (Int.max_signed )); (Z.le 2 Maxsize); (all_int Hl0))
          LOCAL (temp _a a; temp _pos pos)
          SEP ((store_int_array a0 Hl0 Maxsize))))%assert)
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
  ANNOTATION_WITH size0 pos0 a0 Maxsize Hl a' pos' size',
  ((PROP ((size' = (Vint (IntRepr size0))); (pos' = (Vint (IntRepr pos0))); (a' = a0); (Z.le (Z.add size0 1) Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0); (Z.le (Z.mul 2 Maxsize) (Int.max_signed )); (Z.le 2 Maxsize); (all_int Hl))
  LOCAL (temp _a a'; temp _pos pos'; temp _size size')
  SEP ((store_int_array a0 Hl Maxsize))),
  (EX Hl_final pos1,
    (PROP ((down Hl size0 pos0 pos1 Hl_final); (Z.le pos1 size0))
    LOCAL ()
    SEP ((store_int_array a0 Hl_final Maxsize))))%assert).

Definition f_down_spec_complex :=
  ltac:(uncurry_funcspec f_down_spec_annotation).

Definition f_down_funsig: funsig :=
  ((_a, (tptr tint)) :: (_size, tint) :: (_pos, tint) :: nil, tvoid).

Definition down_spec :=
  ltac:(make_funcspec _down f_down_funsig f_down_spec_complex).

Definition f_down_hint (para: GET_PARA_TYPE f_down_spec_annotation) :=
  match para with
  | (size0, pos0, a0, Maxsize, Hl, a', pos', size') =>
  (Cloop
    (Csequence
      (Cassert
        (EX Hl0 pos1 a pos size,
          (PROP ((down_inv Hl size0 pos0 pos1 Hl0); (size = (Vint (IntRepr size0))); (pos = (Vint (IntRepr pos1))); (Z.le pos1 size0); (a = a0); (Z.le pos1 size0); (Z.le 1 pos1); (Z.le (Z.add size0 1) Maxsize); (Z.le 1 size0); (Z.le pos0 size0); (Z.le 1 pos0); (Z.le (Z.mul 2 Maxsize) (Int.max_signed )); (Z.le 2 Maxsize); (all_int Hl0))
          LOCAL (temp _a a; temp _pos pos; temp _size size)
          SEP ((store_int_array a0 Hl0 Maxsize))))%assert)
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
  ANNOTATION_WITH val0 size_p size0 a0 Maxsize Hl a' size' val',
  ((PROP ((size' = size_p); (val' = (Vint (IntRepr val0))); (a0 = a'); (Z.le (Z.add (Z.add size0 1) 1) Maxsize); (Z.le 0 size0); (Z.le Maxsize (Int.max_signed )); (Z.le 1 Maxsize); (Z.le val0 (Int.max_signed )); (Z.le (Int.min_signed ) val0); (all_int Hl))
  LOCAL (temp _a a'; temp _size size'; temp _val val')
  SEP ((store_int_array a0 Hl Maxsize); (store_int size_p size0))),
  (EX Hl_final,
    (PROP ((push Hl size0 val0 Hl_final))
    LOCAL ()
    SEP ((store_int_array a0 Hl_final Maxsize); (store_int size_p (Z.add size0 1)))))%assert).

Definition f_push_spec_complex :=
  ltac:(uncurry_funcspec f_push_spec_annotation).

Definition f_push_funsig: funsig :=
  ((_a, (tptr tint)) :: (_size, (tptr tint)) :: (_val, tint) :: nil, tvoid).

Definition push_spec :=
  ltac:(make_funcspec _push f_push_funsig f_push_spec_complex).

Definition f_push_hint (para: GET_PARA_TYPE f_push_spec_annotation) :=
  match para with
  | (val0, size_p, size0, a0, Maxsize, Hl, a', size', val') =>
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
  ANNOTATION_WITH size_p size0 a0 Maxsize Hl a' size',
  ((PROP ((size' = size_p); (a' = a0); (Z.le (Z.add size0 1) Maxsize); (Z.le 0 size0); (Z.le (Z.mul 2 Maxsize) (Int.max_signed )); (Z.le 1 Maxsize); (all_int Hl))
  LOCAL (temp _a a'; temp _size size')
  SEP ((store_int_array a0 Hl Maxsize); (store_int size_p size0))),
  (EX Hl_final size1 __return,
    (PROP ((pop Hl size0 Hl_final); (size1 = (pop_length Hl size0)); (__return = (Vint (IntRepr (pop_result Hl size0)))))
    LOCAL (temp ___return __return)
    SEP ((store_int_array a0 Hl_final Maxsize); (store_int size_p size1))))%assert).

Definition f_pop_spec_complex :=
  ltac:(uncurry_funcspec f_pop_spec_annotation).

Definition f_pop_funsig: funsig :=
  ((_a, (tptr tint)) :: (_size, (tptr tint)) :: nil, tint).

Definition pop_spec :=
  ltac:(make_funcspec _pop f_pop_funsig f_pop_spec_complex).

Definition f_pop_hint (para: GET_PARA_TYPE f_pop_spec_annotation) :=
  match para with
  | (size_p, size0, a0, Maxsize, Hl, a', size') =>
  (Csequence
    (Csequence
      (Cset _t'6 (Ederef (Etempvar _size (tptr tint)) tint))
      (Cifthenelse (Ebinop Oeq (Etempvar _t'6 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Creturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        Cskip))
    (Csequence
      (Csequence
        (Cset _t'4 (Ederef (Etempvar _size (tptr tint)) tint))
        (Csequence
          (Cset _t'5
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t'4 tint)
                (tptr tint)) tint))
          (Cassign
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint)) tint)
            (Etempvar _t'5 tint))))
      (Csequence
        (Csequence
          (Cset _t'3 (Ederef (Etempvar _size (tptr tint)) tint))
          (Cassign (Ederef (Etempvar _size (tptr tint)) tint)
            (Ebinop Osub (Etempvar _t'3 tint) (Econst_int (Int.repr 1) tint)
              tint)))
        (Csequence
          (Csequence
            (Cset _t'1 (Ederef (Etempvar _size (tptr tint)) tint))
            (Cifthenelse (Ebinop Oge (Etempvar _t'1 tint)
                           (Econst_int (Int.repr 1) tint) tint)
              (Csequence
                (Cset _t'2 (Ederef (Etempvar _size (tptr tint)) tint))
                (Ccall None
                  (Evar _down (Tfunction
                                (Tcons (tptr tint)
                                  (Tcons tint (Tcons tint Tnil))) tvoid
                                cc_default))
                  ((Etempvar _a (tptr tint)) :: (Etempvar _t'2 tint) ::
                   (Econst_int (Int.repr 1) tint) :: nil)))
              Cskip))
          (Creturn (Some (Econst_int (Int.repr 0) tint)))))))  end.


Definition f_top_spec_annotation :=
  ANNOTATION_WITH a0 Maxsize Hl a',
  ((PROP ((Z.le Maxsize (Int.max_signed )); (Z.le 2 Maxsize); (a' = a0))
  LOCAL (temp _a a')
  SEP ((store_int_array a0 Hl Maxsize))),
  (EX __return,
    (PROP ((__return = (Vint (IntRepr (Znth 1 Hl)))))
    LOCAL (temp ___return __return)
    SEP ((store_int_array a0 Hl Maxsize))))%assert).

Definition f_top_spec_complex :=
  ltac:(uncurry_funcspec f_top_spec_annotation).

Definition f_top_funsig: funsig :=
  ((_a, (tptr tint)) :: nil, tint).

Definition top_spec :=
  ltac:(make_funcspec _top f_top_funsig f_top_spec_complex).

Definition f_top_hint (para: GET_PARA_TYPE f_top_spec_annotation) :=
  match para with
  | (a0, Maxsize, Hl, a') =>
  (Csequence
    (Cset _t'1
      (Ederef
        (Ebinop Oadd (Etempvar _a (tptr tint)) (Econst_int (Int.repr 1) tint)
          (tptr tint)) tint))
    (Creturn (Some (Etempvar _t'1 tint))))  end.


Definition Gprog : funspecs :=
  ltac:(with_library prog (swap_spec :: up_spec :: down_spec :: push_spec :: pop_spec :: top_spec :: nil)).

Notation "'Delta_specs_swap'" := (DELTA_SPECS (f_swap, Vprog, Gprog)).

Notation "'Delta_swap' DS" := (DELTA (f_swap, Vprog, Gprog, @nil (ident * Annotation), DS)) (at level 99).

Notation "'Delta_specs_up'" := (DELTA_SPECS (f_up, Vprog, Gprog)).

Notation "'Delta_up' DS" := (DELTA (f_up, Vprog, Gprog, @nil (ident * Annotation), DS)) (at level 99).

Notation "'Delta_specs_down'" := (DELTA_SPECS (f_down, Vprog, Gprog)).

Notation "'Delta_down' DS" := (DELTA (f_down, Vprog, Gprog, @nil (ident * Annotation), DS)) (at level 99).

Notation "'Delta_specs_push'" := (DELTA_SPECS (f_push, Vprog, Gprog)).

Notation "'Delta_push' DS" := (DELTA (f_push, Vprog, Gprog, @nil (ident * Annotation), DS)) (at level 99).

Notation "'Delta_specs_pop'" := (DELTA_SPECS (f_pop, Vprog, Gprog)).

Notation "'Delta_pop' DS" := (DELTA (f_pop, Vprog, Gprog, @nil (ident * Annotation), DS)) (at level 99).

Notation "'Delta_specs_top'" := (DELTA_SPECS (f_top, Vprog, Gprog)).

Notation "'Delta_top' DS" := (DELTA (f_top, Vprog, Gprog, @nil (ident * Annotation), DS)) (at level 99).