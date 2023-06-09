From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "../FinalProject/heap.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 1%positive.
Definition ___builtin_annot : ident := 10%positive.
Definition ___builtin_annot_intval : ident := 11%positive.
Definition ___builtin_bswap : ident := 3%positive.
Definition ___builtin_bswap16 : ident := 5%positive.
Definition ___builtin_bswap32 : ident := 4%positive.
Definition ___builtin_bswap64 : ident := 2%positive.
Definition ___builtin_clz : ident := 36%positive.
Definition ___builtin_clzl : ident := 37%positive.
Definition ___builtin_clzll : ident := 38%positive.
Definition ___builtin_ctz : ident := 39%positive.
Definition ___builtin_ctzl : ident := 40%positive.
Definition ___builtin_ctzll : ident := 41%positive.
Definition ___builtin_debug : ident := 53%positive.
Definition ___builtin_fabs : ident := 6%positive.
Definition ___builtin_fmadd : ident := 44%positive.
Definition ___builtin_fmax : ident := 42%positive.
Definition ___builtin_fmin : ident := 43%positive.
Definition ___builtin_fmsub : ident := 45%positive.
Definition ___builtin_fnmadd : ident := 46%positive.
Definition ___builtin_fnmsub : ident := 47%positive.
Definition ___builtin_fsqrt : ident := 7%positive.
Definition ___builtin_membar : ident := 12%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_nop : ident := 52%positive.
Definition ___builtin_read16_reversed : ident := 48%positive.
Definition ___builtin_read32_reversed : ident := 49%positive.
Definition ___builtin_sel : ident := 9%positive.
Definition ___builtin_va_arg : ident := 14%positive.
Definition ___builtin_va_copy : ident := 15%positive.
Definition ___builtin_va_end : ident := 16%positive.
Definition ___builtin_va_start : ident := 13%positive.
Definition ___builtin_write16_reversed : ident := 50%positive.
Definition ___builtin_write32_reversed : ident := 51%positive.
Definition ___compcert_i64_dtos : ident := 21%positive.
Definition ___compcert_i64_dtou : ident := 22%positive.
Definition ___compcert_i64_sar : ident := 33%positive.
Definition ___compcert_i64_sdiv : ident := 27%positive.
Definition ___compcert_i64_shl : ident := 31%positive.
Definition ___compcert_i64_shr : ident := 32%positive.
Definition ___compcert_i64_smod : ident := 29%positive.
Definition ___compcert_i64_smulh : ident := 34%positive.
Definition ___compcert_i64_stod : ident := 23%positive.
Definition ___compcert_i64_stof : ident := 25%positive.
Definition ___compcert_i64_udiv : ident := 28%positive.
Definition ___compcert_i64_umod : ident := 30%positive.
Definition ___compcert_i64_umulh : ident := 35%positive.
Definition ___compcert_i64_utod : ident := 24%positive.
Definition ___compcert_i64_utof : ident := 26%positive.
Definition ___compcert_va_composite : ident := 20%positive.
Definition ___compcert_va_float64 : ident := 19%positive.
Definition ___compcert_va_int32 : ident := 17%positive.
Definition ___compcert_va_int64 : ident := 18%positive.
Definition _a : ident := 54%positive.
Definition _b : ident := 55%positive.
Definition _down : ident := 61%positive.
Definition _main : ident := 66%positive.
Definition _pop : ident := 64%positive.
Definition _pos : ident := 58%positive.
Definition _push : ident := 63%positive.
Definition _size : ident := 60%positive.
Definition _swap : ident := 57%positive.
Definition _t : ident := 56%positive.
Definition _top : ident := 65%positive.
Definition _up : ident := 59%positive.
Definition _val : ident := 62%positive.
Definition _t'1 : ident := 67%positive.
Definition _t'2 : ident := 68%positive.
Definition _t'3 : ident := 69%positive.
Definition _t'4 : ident := 70%positive.
Definition _t'5 : ident := 71%positive.
Definition _t'6 : ident := 72%positive.

Definition f_swap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tint)) :: (_b, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t (Ederef (Etempvar _a (tptr tint)) tint))
  (Ssequence
    (Ssequence
      (Sset _t'1 (Ederef (Etempvar _b (tptr tint)) tint))
      (Sassign (Ederef (Etempvar _a (tptr tint)) tint) (Etempvar _t'1 tint)))
    (Sassign (Ederef (Etempvar _b (tptr tint)) tint) (Etempvar _t tint))))
|}.

Definition f_up := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tint)) :: (_pos, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Swhile
  (Ebinop Ogt (Etempvar _pos tint) (Econst_int (Int.repr 1) tint) tint)
  (Ssequence
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
        (Sifthenelse (Ebinop Ole (Etempvar _t'1 tint) (Etempvar _t'2 tint)
                       tint)
          Sbreak
          Sskip)))
    (Ssequence
      (Scall None
        (Evar _swap (Tfunction (Tcons (tptr tint) (Tcons (tptr tint) Tnil))
                      tvoid cc_default))
        ((Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _pos tint)
           (tptr tint)) ::
         (Ebinop Oadd (Etempvar _a (tptr tint))
           (Ebinop Oshr (Etempvar _pos tint) (Econst_int (Int.repr 1) tint)
             tint) (tptr tint)) :: nil))
      (Sset _pos
        (Ebinop Oshr (Etempvar _pos tint) (Econst_int (Int.repr 1) tint)
          tint)))))
|}.

Definition f_down := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tint)) :: (_size, tint) :: (_pos, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, tint) :: (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Swhile
  (Ebinop Ole
    (Ebinop Oshl (Etempvar _pos tint) (Econst_int (Int.repr 1) tint) tint)
    (Etempvar _size tint) tint)
  (Ssequence
    (Sset _t (Etempvar _pos tint))
    (Ssequence
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
          (Sifthenelse (Ebinop Ogt (Etempvar _t'3 tint) (Etempvar _t'4 tint)
                         tint)
            (Sset _t
              (Ebinop Oshl (Etempvar _pos tint)
                (Econst_int (Int.repr 1) tint) tint))
            Sskip)))
      (Ssequence
        (Sifthenelse (Ebinop Ole
                       (Ebinop Oor
                         (Ebinop Oshl (Etempvar _pos tint)
                           (Econst_int (Int.repr 1) tint) tint)
                         (Econst_int (Int.repr 1) tint) tint)
                       (Etempvar _size tint) tint)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tint))
                  (Ebinop Oor
                    (Ebinop Oshl (Etempvar _pos tint)
                      (Econst_int (Int.repr 1) tint) tint)
                    (Econst_int (Int.repr 1) tint) tint) (tptr tint)) tint))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t tint)
                    (tptr tint)) tint))
              (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tint)
                             (Etempvar _t'2 tint) tint)
                (Sset _t
                  (Ebinop Oor
                    (Ebinop Oshl (Etempvar _pos tint)
                      (Econst_int (Int.repr 1) tint) tint)
                    (Econst_int (Int.repr 1) tint) tint))
                Sskip)))
          Sskip)
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _t tint) (Etempvar _pos tint)
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
               (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t tint)
                 (tptr tint)) :: nil))
            (Sset _pos (Etempvar _t tint))))))))
|}.

Definition f_push := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tint)) :: (_size, (tptr tint)) :: (_val, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3 (Ederef (Etempvar _size (tptr tint)) tint))
    (Sassign (Ederef (Etempvar _size (tptr tint)) tint)
      (Ebinop Oadd (Etempvar _t'3 tint) (Econst_int (Int.repr 1) tint) tint)))
  (Ssequence
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _size (tptr tint)) tint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t'2 tint)
            (tptr tint)) tint) (Etempvar _val tint)))
    (Ssequence
      (Sset _t'1 (Ederef (Etempvar _size (tptr tint)) tint))
      (Scall None
        (Evar _up (Tfunction (Tcons (tptr tint) (Tcons tint Tnil)) tvoid
                    cc_default))
        ((Etempvar _a (tptr tint)) :: (Etempvar _t'1 tint) :: nil)))))
|}.

Definition f_pop := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tint)) :: (_size, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'6 (Ederef (Etempvar _size (tptr tint)) tint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'4 (Ederef (Etempvar _size (tptr tint)) tint))
      (Ssequence
        (Sset _t'5
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _t'4 tint)
              (tptr tint)) tint))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint)) tint)
          (Etempvar _t'5 tint))))
    (Ssequence
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _size (tptr tint)) tint))
        (Sassign (Ederef (Etempvar _size (tptr tint)) tint)
          (Ebinop Osub (Etempvar _t'3 tint) (Econst_int (Int.repr 1) tint)
            tint)))
      (Ssequence
        (Ssequence
          (Sset _t'1 (Ederef (Etempvar _size (tptr tint)) tint))
          (Sifthenelse (Ebinop Oge (Etempvar _t'1 tint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Ssequence
              (Sset _t'2 (Ederef (Etempvar _size (tptr tint)) tint))
              (Scall None
                (Evar _down (Tfunction
                              (Tcons (tptr tint)
                                (Tcons tint (Tcons tint Tnil))) tvoid
                              cc_default))
                ((Etempvar _a (tptr tint)) :: (Etempvar _t'2 tint) ::
                 (Econst_int (Int.repr 1) tint) :: nil)))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_top := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Etempvar _a (tptr tint)) (Econst_int (Int.repr 1) tint)
        (tptr tint)) tint))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_swap, Gfun(Internal f_swap)) :: (_up, Gfun(Internal f_up)) ::
 (_down, Gfun(Internal f_down)) :: (_push, Gfun(Internal f_push)) ::
 (_pop, Gfun(Internal f_pop)) :: (_top, Gfun(Internal f_top)) :: nil).

Definition public_idents : list ident :=
(_top :: _pop :: _push :: _down :: _up :: _swap :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


