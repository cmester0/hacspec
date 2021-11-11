Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import Hacspec.Lib.
Require Import Coq.Lists.List.

#[global] Instance show_unit : Show (unit) := Build_Show (unit) (fun _ => "tt"%string).
Definition g_unit : G (unit) := returnGen tt.
#[global] Instance gen_unit : Gen (unit) := Build_Gen unit g_unit.

#[global] Instance show_int8 : Show (int8) :=
  Build_Show (int8) (fun x => show (int8_to_nat x)).
Definition g_int8 : G (int8) :=
  bindGen arbitrary (fun x => returnGen (pub_u8 x)).
#[global] Instance gen_int8 : Gen (int8) := Build_Gen int8 g_int8.

#[global] Instance show_int32 : Show (int32) :=
  Build_Show (int32) (fun x => show (int32_to_nat x)).
Definition g_int32 : G (int32) :=
  bindGen arbitrary (fun x => returnGen (pub_u32 x)).
#[global] Instance gen_int32 : Gen (int32) := Build_Gen int32 g_int32.

#[global] Instance show_int64 : Show (int64) :=
  Build_Show (int64) (fun x => show (int64_to_nat x)).
Definition g_int64 : G (int64) :=
  bindGen arbitrary (fun x => returnGen (pub_u64 x)).
#[global] Instance gen_int64 : Gen (int64) := Build_Gen int64 g_int64.

#[global] Instance show_nseq n : Show (nseq (int8) (usize n)) :=
  Build_Show (nseq (int8) (usize n)) (fun x =>
     match x with
     | Vector.nil _ => "[]"%string
     | Vector.cons _ x n xs => ("[" ++ fold_left (fun a b => (a ++ " " ++ show b)) xs (show x) ++ "]")%string
     end).
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
#[global] Instance gen_nseq n : Gen (nseq (int8) (usize n)) := Build_Gen (nseq (int8) (usize n)) (g_nseq n).

#[global] Instance show_public_byte_seq : Show (public_byte_seq) :=
  Build_Show (public_byte_seq) (fun x =>
    match x with 
    | [] => "[]"%string
    | x :: xs => ("[" ++ fold_left (fun a b => (a ++ " " ++ show b)) xs (show x) ++ "]")%string
    end).
Definition g_public_byte_seq : G (public_byte_seq) :=
  listOf arbitrary.
  (* @genList int8 gen_int8. *)
  (* listOf (g_int8). *)
  (* bindGen g_int8 (fun y => *)
  (* bindGen g_int8 (fun x => returnGen ([y ; x]))). *)
  (* listOf (g_int8). (*arbitrary*) *)
#[global] Instance gen_public_byte_seq : Gen (public_byte_seq) :=
  Build_Gen public_byte_seq g_public_byte_seq.
