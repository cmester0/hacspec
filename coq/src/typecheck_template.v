(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition t  : bool :=
  true.

Definition f  : bool :=
  false.

Definition ui  : uint_size :=
  usize 123.

Definition ui8  : int8 :=
  repr 123.

Definition ui16  : int16 :=
  repr 123.

Definition ui32  : int32 :=
  repr 123.

Definition ui64  : int64 :=
  repr 123.

Definition ui128  : int128 :=
  repr 123.

Definition si  : int_size :=
  isize 123.

Definition si8  : int8 :=
  repr 123.

Definition si16  : int16 :=
  repr 123.

Definition si32  : int32 :=
  repr 123.

Definition si64  : int64 :=
  repr 123.

Definition si128  : int128 :=
  repr 123.

Definition ch  : unit :=
  let _ :=
    "a" in 
  tt.

Definition sequnit  : unit :=
  tt.

Definition seqtup  : (bool × int8 × int64) :=
  (true, repr 12, repr 93).

Definition arri32 := nseq (int32) (usize 3).

Definition arr  : arri32 :=
  array_from_list int32 (let l := [repr 0; repr 21; repr 42] in  l).

Definition seqslice  : seq int32 :=
  array_slice (
    array_from_list int32 (let l := [repr 0; repr 21; repr 42] in  l)) (
    usize 0) (usize 3).

Inductive enm :=
| FirstEnum : enm
| SecondEnum : bool -> enm.

Definition eqb_enm (x y : enm) : bool := match x with
   | FirstEnum => match y with | FirstEnum=> true | _ => false end
   | SecondEnum a => match y with | SecondEnum b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_enm (x y : enm) : eqb_enm x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_enm : EqDec (enm) :=
Build_EqDec (enm) (eqb_enm) (eqb_leibniz_enm).


Definition enmfun  : enm :=
  SecondEnum (false).

Definition eqs  : unit :=
  let _ :=
    (false) =.? (true) in 
  let _ :=
    (repr 0) =.? (repr 4) in 
  let _ :=
    (repr 0) =.? (repr 0) in 
  let _ :=
    (repr 4) =.? (repr 7) in 
  let _ :=
    (repr 4) =.? (repr 4) in 
  let _ :=
    (repr 4) =.? (repr 4) in 
  let _ :=
    (usize 4) =.? (usize 4) in 
  let _ :=
    (repr 0) =.? (repr 4) in 
  let _ :=
    (repr 0) =.? (repr 0) in 
  let _ :=
    (repr 4) =.? (repr 7) in 
  let _ :=
    (repr 4) =.? (repr 4) in 
  let _ :=
    (repr 4) =.? (repr 4) in 
  let _ :=
    (isize 4) =.? (isize 4) in 
  let _ :=
    ((true, repr 12, repr 93)) =.? ((true, repr 12, repr 92)) in 
  let _ :=
    (
      array_from_list int32 (
        let l :=
          [repr 0; repr 21; repr 42] in  l)) array_eq (
      array_from_list int32 (let l := [repr 0; repr 21; repr 42] in  l)) in 
  tt.

