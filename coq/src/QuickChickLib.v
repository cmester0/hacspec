(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import Hacspec.Lib.
Require Import Coq.Lists.List.

Instance show_int8 : Show (int8) :=
  Build_Show (int8) (fun x => show (int8_to_nat x)).
Definition g_int8 : G (int8) :=
  bindGen arbitrary (fun x => returnGen (pub_u8 x)).
Instance gen_int8 : Gen (int8) := Build_Gen int8 g_int8.

Instance show_int32 : Show (int32) :=
  Build_Show (int32) (fun x => show (int32_to_nat x)).
Definition g_int32 : G (int32) :=
  bindGen arbitrary (fun x => returnGen (pub_u32 x)).
Instance gen_int32 : Gen (int32) := Build_Gen int32 g_int32.

Instance show_int64 : Show (int64) :=
  Build_Show (int64) (fun x => show (int64_to_nat x)).
Definition g_int64 : G (int64) :=
  bindGen arbitrary (fun x => returnGen (pub_u64 x)).
Instance gen_int64 : Gen (int64) := Build_Gen int64 g_int64.

Instance show_nseq n : Show (nseq (int8) (usize n)) :=
  Build_Show (nseq (int8) (usize n)) (fun x => fold_left (fun a b => (a ++ " " ++ show b)%string) x ""%string).
Definition g_nseq n : G (nseq (int8) (usize n)).
  intros.
  apply (@bindGen' (list int8) (nseq int8 n) (vectorOf n arbitrary)).
  intros l sem.
  apply returnGen.
  pose (array_from_list int8 l).
  
  assert (Datatypes.length l = n).
  { unfold semGen in sem.
    unfold "\bigcup_" in sem.
    destruct sem as [i [a b]].

    apply (semVectorOfSize _ arbitrary i l).
    apply b. }
  rewrite <- H.
  apply n0.
Defined.  

Instance gen_nseq n : Gen (nseq (int8) (usize n)) := Build_Gen (nseq (int8) (usize n)) (g_nseq n).

           

           
