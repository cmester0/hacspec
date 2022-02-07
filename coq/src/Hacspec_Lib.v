Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".

(*** Integers *)
From Coq Require Import ZArith List.
Import ListNotations.
(* Require Import IntTypes. *)

Require Import MachineIntegers.
From Coqprime Require GZnZ.

(* Set Warnings "-notation-overridden". *)
From mathcomp Require Import all_ssreflect (* all_algebra  *)ssreflect (* seq tuple *). (* vector *)
Locate introT.
(* Declare Scope hacspec_scope. *)

From Crypt Require Import choice_type Package.
Import PackageNotation.

Open Scope Z_scope.

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

(* Set Warnings "-notation-overridden,-ambiguous-paths". *)
(* From mathcomp Require Import all_ssreflect all_algebra reals distr realsum *)
(*   ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq. *)
Set Warnings "notation-overridden,ambiguous-paths".

(* From Mon Require Import SPropBase. *)
From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

(* From Coq Require Import Utf8. *)
(* From extructures Require Import ord fset fmap. *)

(* From Coq Require Import Uint63. *)

Section IntDefinition.

  Context (WS : WORDSIZE).

  (* Compute (2 ^ (N.of_nat 100))%N. *)
  
  Theorem modulus_is_pow2 : Z.to_N modulus = (N.pow 2 (N.of_nat wordsize))%N.
  Proof.
    intros.
    unfold modulus.
    
    rewrite (two_power_nat_equiv wordsize).
    rewrite Z2N.inj_pow.
    (* rewrite Z2Nat.inj_pow. *)
    - rewrite <- nat_N_Z.
      rewrite N2Z.id.
      (* rewrite Nat2Z.id. *)
      cbn.
      reflexivity.
    - easy.
    - induction wordsize.
      + reflexivity.
      + easy.
  Qed.
  
  Definition int_max : N := Z.to_N modulus.
  Definition int_pos : Prelude.Positive (N.to_nat int_max).
  Proof.    
    unfold int_max.
    rewrite Z_N_nat.
    unfold modulus.
    rewrite (two_power_nat_equiv wordsize).
    rewrite Z2Nat.inj_pow.
    - rewrite Nat2Z.id.
      replace (Z.to_nat 2) with 2%nat by reflexivity.

      pose (PositiveExp2 (wordsize)).
      induction wordsize.
      + cbn in *.
        apply p.
      + rewrite Nat.pow_succ_r'.
        apply Positive_prod.
        easy.
        easy.
        easy.
    - induction wordsize.
      + reflexivity.
      + easy.
  Defined. 

  (* Compute (2 ^ 16)%N. *)
  (* Definition Words : finType := [finType of 'Z_modulus]. *)
  
  Definition int_spec : {int : choice_type | (int = chFin (@Prelude.mkpos (N.to_nat int_max) int_pos))}.
    apply (@exist choice_type (fun int => (int = chFin (@Prelude.mkpos (N.to_nat int_max) int_pos))) (chFin (@Prelude.mkpos (N.to_nat int_max) int_pos))).
    reflexivity.
  Qed.
  
  Definition int : choice_type.
    apply (proj1_sig int_spec).
  Defined.  
  Definition int_compute : int = chFin (@Prelude.mkpos (N.to_nat int_max) int_pos).
  Proof.
    apply (proj2_sig int_spec).
  Qed.    

  Theorem repr_helper : forall n k, (n mod 2 ^ k < 2 ^ k)%nat.
  Proof.
    intros.
    apply (introT ltP).  
    apply Nat.mod_upper_bound.
    induction k.
    - easy.
    - rewrite expnSr.
      apply Nat.neq_mul_0.
      split ; easy.
  Qed.
  Theorem repr_helper_2 : forall {n m}, (0 < m)%nat -> (n mod m < m)%nat.
  Proof.
    intros.
    apply (introT ltP).  
    apply Nat.mod_upper_bound.
    induction m ; easy.
  Qed.
  Check (fun x => @repr_helper_2 (x) (Z.to_nat modulus)).
  Theorem repr_helper_3 : (0 < Z.to_nat modulus)%N.
  Proof.
    intros.
    (* unfold modulus in *. *)
    pose (introT (Nat.ltb_spec0 0 (Z.to_nat (@modulus WS)))).
    pose (Z2Nat.inj_lt (0) (@modulus WS) ).
    replace 0%nat with (Z.to_nat 0) by reflexivity.
    apply (introT (ltP)).
    apply i0 ; try easy.
  Qed.

  Definition repr (x : Z) : int.
    (* rewrite int_compute. *)
    unfold int.
    unfold sval.
    destruct int_spec.
    subst.
    
    apply (Ordinal (n:=Z.to_nat modulus) (m:= Z.to_nat x mod Z.to_nat modulus) (repr_helper_2 (repr_helper_3))).
  Qed.

  Definition unsigned (x : int) : Z.
  Proof.
    (* rewrite int_compute. *)
    unfold int in x.
    unfold sval in x.
    destruct int_spec.
    subst.

    destruct x.
    apply (Z.of_nat m).    
  Qed.  

  Definition signed (x : int) : Z.
  Proof.
    rewrite int_compute in x.
    destruct WS.
    destruct x.
    apply (Z.of_nat m).
  Qed.  

  (* Theorem repr_unsigned_id : forall n, repr (unsigned n) = n. *)
  (* Proof. *)
  (*   intros. *)
  (*   pose int_compute. *)
  (*   unfold int_compute. *)
    
  Axiom repr_unsigned_id : forall n, repr (unsigned n) = n.
  Axiom unsigned_repr_id : forall n, unsigned (repr n) = n. (* `{n mod modulus = n} *)
  (* Theorem unsigned_repr_id : forall n `{n mod modulus = n}, unsigned (repr n) = n. *)
  (* Proof. *)
  (*   intros. *)

  (*   assert (modulus_not_zero : @modulus WS <> 0). *)
  (*   { *)
  (*     destruct WS. *)
  (*     destruct wordsize. *)
  (*     - contradiction. *)
  (*     - easy. *)
  (*   } *)
        
  (*   unfold unsigned. *)
  (*   unfold repr. *)

  (*   destruct int_spec. *)
  (*   subst. *)

  (*   cbn. *)
  (*   rewrite <- Z2Nat.inj_pos. *)
    
  (*   rewrite Nat2Z.inj_mod. *)
    
  (*   rewrite Z2Nat.id. *)
  (*   - rewrite Z2Nat.id. *)
  (*     + apply H. *)
  (*     + easy. *)
  (*   - destruct n. *)
  (*     + reflexivity. *)
  (*     + easy. *)
  (*     + apply (Z.mod_small_iff (Z.neg p) _ modulus_not_zero) in H. *)
  (*       destruct H. *)
  (*       * easy. *)
  (*       * easy. *)
  (* Qed. *)

  Opaque int.
  Opaque repr.
  Opaque unsigned.
End IntDefinition.

Definition int8 : choice_type := @int WORDSIZE8.
Definition int16 : choice_type := @int WORDSIZE16.
Definition int32 : choice_type := @int WORDSIZE32.
Definition int64 : choice_type := @int WORDSIZE64.
Definition int128 : choice_type := @int WORDSIZE128.

Compute int16.
Print repr.
Print int.
Compute repr WORDSIZE16 100.

Axiom secret : forall {WS : WORDSIZE},  (@int WS) -> (@int WS).

Locate Ordinal.


Print int.

(* Global Instance Z_uint_sizable : UInt_sizable Z := { *)
(*   usize n := repr n; *)
(*   from_uint_size n := unsigned n; *)
(* }. *)

Axiom uint8_declassify : int8 -> int8.
Axiom int8_declassify : int8 -> int8.
Axiom uint16_declassify : int16 -> int16.
Axiom int16_declassify : int16 -> int16.
Axiom uint32_declassify : int32 -> int32.
Axiom int32_declassify : int32 -> int32.
Axiom uint64_declassify : int64 -> int64.
Axiom int64_declassify : int64 -> int64.
Axiom uint128_declassify : int128 -> int128.
Axiom int128_declassify : int128 -> int128.

Axiom uint8_classify : int8 -> int8.
Axiom int8_classify : int8 -> int8.
Axiom uint16_classify : int16 -> int16.
Axiom int16_classify : int16 -> int16.
Axiom uint32_classify : int32 -> int32.
Axiom int32_classify : int32 -> int32.
Axiom uint64_classify : int64 -> int64.
Axiom int64_classify : int64 -> int64.
Axiom uint128_classify : int128 -> int128.
Axiom int128_classify : int128 -> int128.


(* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
 *)

Definition uint8 := int8.
Definition uint16 := int16.
Definition uint32 := int32.
Definition uint64 :=  int64.
Definition uint128 := int128.

Definition uint_size := int32. (* int32. *)
Definition int_size := int32. (* int32. *)

Axiom declassify_usize_from_uint8 : uint8 -> uint_size.

(* Represents any type that can be converted to uint_size and back *)
Class UInt_sizable (A : Type) := {
  usize : A -> Choice.sort uint_size;
  from_uint_size : uint_size -> A;
}.
Arguments usize {_} {_}.
Arguments from_uint_size {_} {_}.

Global Instance nat_uint_sizable : UInt_sizable nat := {
  usize n := repr WORDSIZE32 (Z.of_nat n);
  from_uint_size n := Z.to_nat (unsigned WORDSIZE32 n);
}.

Global Instance N_uint_sizable : UInt_sizable N := {
  usize n := repr WORDSIZE32 (Z.of_N n);
  from_uint_size n := Z.to_N (unsigned WORDSIZE32 n);
}.

Global Instance Z_uint_sizable : UInt_sizable Z.
Proof.
  split.
  intros n. apply (repr WORDSIZE32 n).
  intros n. apply (unsigned WORDSIZE32 n).
Defined.
  
(*   := { *)
(*   usize n := repr WORDSIZE32 n; *)
(*   from_uint_size n := unsigned WORDSIZE32 n; *)
(* }. *)


(* Same, but for int_size *)
Class Int_sizable (A : Type) := {
  isize : A -> int_size;
  from_int_size : int_size -> A;
}.

Arguments isize {_} {_}.
Arguments from_int_size {_} {_}.

Global Instance nat_Int_sizable : Int_sizable nat := {
  isize n := repr WORDSIZE32 (Z.of_nat n);
  from_int_size n := Z.to_nat (signed WORDSIZE32 n);
}.

Global Instance N_Int_sizable : Int_sizable N := {
  isize n := repr WORDSIZE32 (Z.of_N n);
  from_int_size n := Z.to_N (signed WORDSIZE32 n);
}.

Global Instance Z_Int_sizable : Int_sizable Z := {
  isize n := repr WORDSIZE32 n;
  from_int_size n := signed WORDSIZE32 n;
}.


(**** Public integers *)

(* Definition pub_u8 (n:range_t U8) : u:pub_uint8{v u == n} := uint #U8 #PUB n *)
Definition pub_u8 (n : Z) : int8 := repr WORDSIZE8 n. (* repr *)

(* Definition pub_i8 (n:N) : u:pub_int8{v u == n} := sint #S8 #PUB n *)
Definition pub_i8 (n : Z) : int8 := repr WORDSIZE8 n.

(* Definition pub_u16 (n:N) : u:pub_uint16{v u == n} := uint #U16 #PUB n *)
Definition pub_u16 (n : Z) : int16 := repr WORDSIZE16 n.

(* Definition pub_i16 (n:N) : u:pub_int16{v u == n} := sint #S16 #PUB n *)
Definition pub_i16 (n : Z) : int16 := repr WORDSIZE16 n.

(* Definition pub_u32 (n:N) : u:pub_uint32{v u == n} := uint #U32 #PUB n *)
Definition pub_u32 (n : Z) : int32 := repr WORDSIZE32 n.

(* Definition pub_i32 (n:N) : u:pub_int32{v u == n} := sint #S32 #PUB n *)
Definition pub_i32 (n : Z) : int32 := repr WORDSIZE32 n.

(* Definition pub_u64 (n:N) : u:pub_uint64{v u == n} := uint #U64 #PUB n *)
Definition pub_u64 (n : Z) : int64 := repr WORDSIZE64 n.

(* Definition pub_i64 (n:N) : u:pub_int64{v u == n} := sint #S64 #PUB n *)
Definition pub_i64 (n : Z) : int64 := repr WORDSIZE64 n.

(* Definition pub_u128 (n:N) : u:pub_uint128{v u == n} := uint #U128 #PUB n *)
Definition pub_u128 (n : Z) : int128 := repr WORDSIZE128 n.

(* Definition pub_i128 (n:N) : u:pub_int128{v u == n} := sint #S128 #PUB n *)
Definition pub_i128 (n : Z) : int128 := repr WORDSIZE128 n.

(**** Operations *)

(* TODO START *)
(* (* Should maybe use size of s instead? *) *)
(* Definition uint8_rotate_left (u: int8) (s: int8) : int8 := rol u s. *)

(* Definition uint8_rotate_right (u: int8) (s: int8) : int8 := ror u s. *)

(* Definition uint16_rotate_left (u: int16) (s: int16) : int16 := *)
(*   rol u s. *)

(* Definition uint16_rotate_right (u: int16) (s: int16) : int16 := *)
(*   ror u s. *)

(* Definition uint32_rotate_left (u: int32) (s: int32) : int32 := *)
(*   rol u s. *)

(* Definition uint32_rotate_right (u: int32) (s: int32) : int32 := *)
(*   ror u s. *)

(* Definition uint64_rotate_left (u: int64) (s: int64) : int64 := *)
(*   rol u s. *)

(* Definition uint64_rotate_right (u: int64) (s: int64) : int64 := *)
(*   ror u s. *)

(* Definition uint128_rotate_left (u: int128) (s: int128) : int128 := *)
(*   rol u s. *)

(* Definition uint128_rotate_right (u: int128) (s: int128) : int128 := *)
(*   ror u s. *)

(* (* should use size u instead of u? *) *)
(* Definition usize_shift_right (u: uint_size) (s: int32) : uint_size := *)
(*   (ror u s). *)
(* Infix "usize_shift_right" := (usize_shift_right) (at level 77) : hacspec_scope. *)

(* (* should use size u instead of u? *) *)
(* Definition usize_shift_left (u: uint_size) (s: int32) : uint_size := *)
(*   (rol u s). *)
(* Infix "usize_shift_left" := (usize_shift_left) (at level 77) : hacspec_scope. *)

(* Definition pub_uint128_wrapping_add (x y: int128) : int128 := *)
(*   add x y. *)

(* Definition shift_left_ `{WS : WORDSIZE} (i : @int WS) (j : uint_size) := *)
(*   MachineIntegers.shl i (repr (from_uint_size j)). *)

(* Definition shift_right_ `{WS : WORDSIZE} (i : @int WS) (j : uint_size) := *)
(*   MachineIntegers.shr i (repr (from_uint_size j)) . *)

(* Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope. *)
(* Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope. *)

(* (* Infix "%%" := Z.rem (at level 40, left associativity) : hacspec_scope. *) *)
(* Infix ".+" := (MachineIntegers.add) (at level 77) : hacspec_scope. *)
Theorem int_max_is_succ : forall {WS : WORDSIZE}, exists k, int_max WS = N.succ k.
Proof.
  intros.
  unfold int_max.
  unfold modulus.
  unfold two_power_nat.
  cbn.
  unfold N.succ.
  exists (N.pos (Pos.pred (shift_nat wordsize 1))).
  f_equal.
  rewrite Pos.succ_pred.
  reflexivity.

  intro a.
  destruct wordsize eqn:ow.
  - destruct WS.
    contradiction.
  - inversion a.
Qed.

Definition do_add {WS : WORDSIZE} (x y : @int WS) : @int WS.
  assert (N.to_nat (int_max WS) = (N.to_nat (int_max WS)).-1.+1).
  {
    apply S_pred_pos.
    destruct int_max_is_succ.
    rewrite H.
    rewrite Nnat.N2Nat.inj_succ.
    apply Nat.lt_0_succ.    
  }
  unfold int in *.
  unfold sval in *.
  destruct int_spec.
  subst.
  
  apply (Ordinal (n := N.to_nat (int_max WS)) (m := (x + y) %% (N.to_nat (int_max WS)))).
  apply ltn_pmod.
  rewrite H.
  easy.
Qed.

Definition add {WS : WORDSIZE} (x y: int WS) := repr WS ((unsigned WS x) + (unsigned WS y)).
Infix ".+" := (do_add) (at level 77) : hacspec_scope. 
(* Infix ".-" := (MachineIntegers.sub) (at level 77) : hacspec_scope. *)
Definition mul {WS : WORDSIZE} (x y: int WS) := repr WS ((unsigned WS x) * (unsigned WS y)).
Infix ".*" := mul (at level 77) : hacspec_scope.

Definition divs {WS : WORDSIZE} (x y: int WS) : int WS :=
  repr WS (Z.quot (signed WS x) (signed WS y)).
Infix "./" := (divs) (at level 77) : hacspec_scope.
(* Infix ".%" := (MachineIntegers.mods) (at level 77) : hacspec_scope. *)
(* Infix ".^" := (MachineIntegers.xor) (at level 77) : hacspec_scope. *)
Definition and {WS : WORDSIZE} (x y: int WS): int WS := repr WS (Z.land (unsigned WS x) (unsigned WS y)).
Infix ".&" := and (at level 77) : hacspec_scope.
(* Infix ".|" := (MachineIntegers.or) (at level 77) : hacspec_scope. *)
(* (* Infix "==" := (MachineIntegers.eq) (at level 32) : hacspec_scope. *) *)
(* (* Definition one := (@one WORDSIZE32). *) *)
(* (* Definition zero := (@zero WORDSIZE32). *) *)
(* (* Notation "A × B" := (prod A B) (at level 79, left associativity) : hacspec_scope. *) *)
(* TODO END *)

Definition uint8_rotate_right (u: int8) (s: int8) : int8 := ror u s.

Definition uint16_rotate_left (u: int16) (s: int16) : int16 :=
  rol u s.

Definition uint16_rotate_right (u: int16) (s: int16) : int16 :=
  ror u s.

Definition uint32_rotate_left (u: int32) (s: int32) : int32 :=
  rol u s.

Definition uint32_rotate_right (u: int32) (s: int32) : int32 :=
  ror u s.

Definition uint64_rotate_left (u: int64) (s: int64) : int64 :=
  rol u s.

Definition uint64_rotate_right (u: int64) (s: int64) : int64 :=
  ror u s.

Definition uint128_rotate_left (u: int128) (s: int128) : int128 :=
  rol u s.

Definition uint128_rotate_right (u: int128) (s: int128) : int128 :=
  ror u s.

(* should use size u instead of u? *)
Definition usize_shift_right (u: uint_size) (s: int32) : uint_size :=
  (ror u s).
Infix "usize_shift_right" := (usize_shift_right) (at level 77) : hacspec_scope.

(* should use size u instead of u? *)
Definition usize_shift_left (u: uint_size) (s: int32) : uint_size :=
  (rol u s).
Infix "usize_shift_left" := (usize_shift_left) (at level 77) : hacspec_scope.

Lemma int_eqb_eq : forall {WS : WORDSIZE} (a b : int WS), a == b = true <-> a = b. (* eq  *)
Proof.
Admitted.

Global Instance int_eqdec `{WS: WORDSIZE} : EqDec (int WS) := {
  eqb := eq_op;
  eqb_leibniz := int_eqb_eq ;
}.

Definition shift_right_ `{WS : WORDSIZE} (i : @int WS) (j : uint_size) :=
  MachineIntegers.shr i (repr (from_uint_size j)) .

Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope.
Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope.

(* Infix "%%" := Z.rem (at level 40, left associativity) : hacspec_scope. *)
Infix ".+" := (MachineIntegers.add) (at level 77) : hacspec_scope.
Infix ".-" := (MachineIntegers.sub) (at level 77) : hacspec_scope.
Notation "-" := (MachineIntegers.neg) (at level 77) : hacspec_scope.
Infix ".*" := (MachineIntegers.mul) (at level 77) : hacspec_scope.
Infix "./" := (MachineIntegers.divs) (at level 77) : hacspec_scope.
Infix ".%" := (MachineIntegers.mods) (at level 77) : hacspec_scope.
Infix ".^" := (MachineIntegers.xor) (at level 77) : hacspec_scope.
Infix ".&" := (MachineIntegers.and) (at level 77) : hacspec_scope.
Infix ".|" := (MachineIntegers.or) (at level 77) : hacspec_scope.
(* Infix "==" := (MachineIntegers.eq) (at level 32) : hacspec_scope. *)
(* Definition one := (@one WORDSIZE32). *)
(* Definition zero := (@zero WORDSIZE32). *)
(* Notation "A × B" := (prod A B) (at level 79, left associativity) : hacspec_scope. *)
(*** Loops *)

(* Open Scope nat_scope. *)

(* TODO START , FORMALIZATION OF MACHINE INTEGERS BASED ON SSREFLET INSTEAD!! *)
(* Definition add {WS : WORDSIZE} (x y: int WS) : int WS := *)
(*   repr WS (unsigned WS x + unsigned WS y). *)
Definition one {WS : WORDSIZE} := repr WS 1.
(* TODO END *)

Fixpoint foldi_
  {acc : Type}
  (fuel : nat)
  (i : uint_size)
  (f : uint_size -> acc -> acc)
  (cur : acc) : acc :=
  match fuel with
  | 0%nat => cur
  | S n' => foldi_ n' (add i one) f (f i cur)
  end.
Close Scope nat_scope.
Definition foldi
  {acc: Type}
  (lo: uint_size)
  (hi: uint_size) (* {lo <= hi} *)
  (f: (uint_size) -> acc -> acc) (* {i < hi} *)
  (init: acc) : acc :=
  match Z.sub (unsigned WORDSIZE32 hi) (unsigned WORDSIZE32 lo) with
  | Z0 => init
  | Zneg p => init
  | Zpos p => foldi_ (Pos.to_nat p) lo f init
  end.

(* Typeclass handling of default elements, for use in sequences/arrays.
   We provide instances for the library integer types *)
Class Default (A : Type) := {
  default : A
}.
Global Arguments default {_} {_}.

(*** Seq *)

(* Definition nseq (T : Type) (n : nat) := n.-tuple T. *)
Fixpoint nseq_nat (T : choice_type) (n : nat) :=
  match n with
  | O => chUnit
  | S n' => chProd T (nseq_nat T n')
  end.
Definition nseq (T : choice_type) (n : uint_size) : choice_type.
Proof.
  apply (nseq_nat T (Z.to_nat (from_uint_size n))).
Defined.

Definition nseq_to_nseq_nat {T} {n : nat} (v : nseq_nat T n) : nseq T (usize n).
  unfold nseq.
  cbn.
  rewrite unsigned_repr_id.
  rewrite Nat2Z.id.
  apply v.
Qed.

(* Theorem nseq_to_nseq_nat : *)
(*   forall T n `{H: Z.of_nat n mod (@modulus WORDSIZE32) = Z.of_nat n}, nseq_nat T n = nseq T (usize n). *)
(* Proof. *)
(*   intros. *)
(*   unfold nseq. *)
(*   cbn. *)
(*   rewrite unsigned_repr_id. *)
(*   rewrite Nat2Z.id. *)
(*   reflexivity. *)
(*   apply H. *)
(* Qed. *)
  

(* Check (usize 32 : @int WORDSIZE32). *)
(* Compute repr WORDSIZE32 32. *)
(* Compute (usize 32%nat : @int WORDSIZE32). *)
(* Compute (from_uint_size (usize 32)). *)
(* Compute nseq (uint8) (usize 32). *)
(* Definition poly_key_t := nseq (uint8) (usize 32). *)


(* Definition nseq (T : choiceType) (n : nat) : choice_type := tuple_choiceType n T. *)

(* (T : finFieldType) (n : nat) *)

   (* (T : finFieldType) (n : nat) := *)
(*   (* Vector.choiceType (regular_vectType T). (* (Fp_finFieldType n) *) *) *)
(* Check VectorDef.t. *)
(* Check Vector.choiceType. (* Zp_ringType *) *)
(* Check (fun n : nat => Vector.choiceType (regular_vectType (Fp_finFieldType n))). *)
(* Check Vector.choiceType (regular_vectType (int_Ring)). *)
(* (* Definition nseq {T : Type} (t : T) (n : nat) := @mathcomp.ssreflect.seq.nseq T n t. *) *)

(* Definition seq (A : Type) := list A. *)
Definition seq (A : choice_type) : Type := seq_choiceType A.

(* Automatic conversion from nseq/vector/array to seq/list *)
Global Coercion VectorDef.to_list : VectorDef.t >-> list.

(* TODO START *)
(* Definition public_byte_seq := seq int8. *)
(* Definition byte_seq := seq int8. *)
(* TODO END *)
Definition list_len := length.

Definition seq_index {A: choice_type} `{Default A} (s: seq A) (i : nat) :=
  List.nth i s default.

(* Definition seq_len {A: choice_type} (s: seq A) : N := N.of_nat (length s). *)
Definition seq_len {A: choice_type} (s: seq A) : uint_size := usize (length s).

Definition seq_new_ {A: choice_type} (init : A) (len: nat) : seq A :=
  VectorDef.const init len.

Definition seq_new {A: choice_type} `{Default A} (len: nat) : seq A :=
  seq_new_ default len.

Fixpoint array_from_list_nat (A: choice_type) (l: list A) : nseq_nat A (length l) :=
  match l with
  | [::] => Datatypes.tt
  | (x :: xs) => (pair x (array_from_list_nat A xs))
  end.
Definition array_from_list (A: choice_type) (l: list A) : nseq A (usize (length l)) :=
  nseq_to_nseq_nat (array_from_list_nat A l).
  
  (* match l return (nseq A (length l)) with *)
  (* | [] => nil_tuple A  (* VectorDef.nil A *) *)
  (* | x :: xs => [tuple of x (in_tuple xs)] (* array_from_list A xs *) *)
  (* end. *)

  (*   match l, length l with *)
(*   | [], O => VectorDef.nil A *)
(*   | (x :: xs), S n => VectorDef.cons A x (length xs) (array_from_list A xs) *)
(*   end. *)
(*   - apply (VectorDef.cons A a (length l) (array_from_list A l)). *)
(* Defined. *)

  (* match l with *)
  (* | [] => VectorDef.nil *)
  (* | (x :: xs) => VectorDef.cons A x (length xs) (array_from_list xs) *)
  (* end. *)

(* Definition array_from_list (A: Type) (l: list A) : nseq A (length l) := *)
  (* VectorDef.of_list l. *)
(* Proof. *)
(*   induction l. *)
(*   - apply (VectorDef.nil A). *)
(*   - apply (VectorDef.cons A a (length l) IHl). *)
(* Defined. *)

(* automatic conversion from list to array *)
(* Global Coercion array_from_list : list >-> nseq. *)


(**** Array manipulation *)

Fixpoint array_new_ {A: choice_type} (init:A) (len: nat) : nseq_nat A len :=
  match len as n return nseq_nat A n with
  | O => Datatypes.tt
  | (n.+1)%N => (init, array_new_ init n)
  end.
(* VectorDef.const init len. *)

(* TODO START *)
Open Scope nat_scope.
Fixpoint array_upd {A: choice_type} {len : nat} (s: nseq_nat A len) (i: nat) (new_v: A) {struct i}: nseq_nat A len.
Proof.
  destruct len.
  - apply Datatypes.tt.
  - destruct s as [s ss].
    induction i.
    + apply (new_v, ss).
    + apply (s, array_upd A len ss i new_v).
Defined.

Fixpoint array_index {A: choice_type} `{Default A} {len : nat} (s: nseq_nat A len) (i : nat) : A.
Proof.
  destruct len.
  - apply default.
  - destruct s as [s ss].
    induction i.
    + apply default.
    + apply s.
Defined.

(* Definition array_upd {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) (new_v: A) : lseq A len := List.upd s i new_v. *)

(* substitutes a sequence (list) into an array (nseq), given index interval  *)
(* Axiom update_sub : forall {A len }, nseq A len -> nat -> nat -> seq A -> t A len. *)
Definition update_sub {A : choice_type} {len slen} `{Default A} (v : nseq_nat A len) (i : nat) (n : nat) (sub : nseq_nat A slen) : nseq_nat A len :=
  let fix rec x acc :=
    match x with
    | 0%nat => acc
    (* | 0 => array_upd acc 0 (array_index sub 0) *)
    | S x => rec x (array_upd acc (i+x) (array_index sub x))
    end in
  rec (n - i + 1) v.

(* Sanity check *)
(* Compute (to_list (update_sub [1;2;3;4;5] 0 4 (of_list [9;8;7;6;12]))). *)

Global Coercion array_from_seq_nat
  {a: choice_type}
 `{Default a}
  (out_len:nat)
  (input: seq a)
  (* {H : List.length input = out_len} *)
  : nseq_nat a out_len :=
  (* tval . *)
  let out := array_new_ default out_len in
    (* let out := VectorDef.const default out_len in *)
    update_sub out 0 (out_len - 1) (array_from_list_nat a input).

Global Coercion array_from_seq
  {a: choice_type}
 `{Default a}
  (out_len:nat)
  (input: seq a)
  (* {H : List.length input = out_len} *)
  : nseq a (usize out_len) :=
  nseq_to_nseq_nat (array_from_seq_nat out_len input).
  
(* Global Coercion array_from_seq : seq >-> nseq. *)

Definition slice {A : choice_type} (l : seq A) (i j : nat) : seq A :=
  if j <=? i then [] else firstn (j-i+1) (skipn i l).

Definition seq_from_list {A : choice_type} (x : seq.seq A) : seq A :=
  match x with
  | [] => [::]
  | (y :: ys) => (y :: ys)
  end.

Fixpoint array_to_list {A : choice_type} {n} (x : nseq_nat A n) {struct n} : seq.seq A.
Proof.
  destruct n.
  - apply nil.
  - destruct x.
    + apply (s :: array_to_list A n s0).
Defined.

Global Coercion seq_from_array {A : choice_type} {n} (l : nseq_nat A n) :=
  seq_from_list (array_to_list l).
  (* seq_from_list (tval l). *)

Definition lseq_slice {A : choice_type} `{Default A} {n} (l : nseq_nat A n) (i j : nat) : nseq_nat A _ :=
    array_from_seq n (slice (seq_from_list (array_to_list l)) i j).
  (* VectorDef.of_list (slice (VectorDef.to_list l) i j). *)

Definition array_from_slice_nat
  {a: choice_type}
 `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start: nat)
  (slice_len: nat)
    : nseq_nat a out_len :=
  let out := array_new_ default out_len in
    (* let out := VectorDef.const default_value out_len in *)
    update_sub out 0 slice_len (lseq_slice (array_from_list_nat a input) start (start + slice_len)).

Definition array_from_slice
  {a: choice_type}
 `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size)
    : nseq a (usize out_len) :=
  nseq_to_nseq_nat (array_from_slice_nat default_value out_len input (from_uint_size start) (from_uint_size slice_len)).


(* Definition array_slice *)
(*   {a: Type} *)
(*  `{Default a} *)
(*   (input: seq a) *)
(*   (start: nat) *)
(*   (slice_len: nat) *)
(*     : nseq a _ := *)
(*   let out := slice input start (start + slice_len) in *)
(*   array_from_seq slice_len out. *)


(* Definition array_from_slice_range *)
(*   {a: Type} *)
(*  `{Default a} *)
(*   (default_value: a) *)
(*   (out_len: nat) *)
(*   (input: seq a) *)
(*   (start_fin: (uint_size * uint_size)) *)
(*     : nseq a out_len := *)
(*     let out := array_new_ default_value out_len in *)
(*     let (start, fin) := start_fin in *)
(*     update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) (VectorDef.of_list (slice input (from_uint_size start) (from_uint_size fin))). *)


(* Definition array_slice_range *)
(*   {a: Type} *)
(*   {len : nat} *)
(*   (input: nseq a len) *)
(*   (start_fin:(uint_size * uint_size)) *)
(*     : nseq a _ := *)
(*   lseq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin)). *)

(* Definition array_update *)
(*   {a: Type} *)
(*  `{Default a} *)
(*   {len: nat} *)
(*   (s: nseq a len) *)
(*   (start : nat) *)
(*   (start_s: seq a) *)
(*     : nseq a len := *)
(*     update_sub s start (length start_s) (VectorDef.of_list start_s). *)

(* Definition array_update_start *)
(*   {a: Type} *)
(*  `{Default a} *)
(*   {len: nat} *)
(*   (s: nseq a len) *)
(*   (start_s: seq a) *)
(*     : nseq a len := *)
(*     update_sub s 0 (length start_s) (VectorDef.of_list start_s). *)


(* Definition array_len  {a: Type} {len: nat} (s: nseq a len) := len. *)
(* (* May also come up as 'length' instead of 'len' *) *)
(* Definition array_length  {a: Type} {len: nat} (s: nseq a len) := len. *)
(* TODO END *)

(**** Seq manipulation *)

Definition seq_slice
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (len: nat)
    : nseq a _ :=
  array_from_seq len (slice s start (start + len)).

Definition seq_slice_range
  {a: Type}
 `{Default a}
  (input: seq a)
  (start_fin:(uint_size * uint_size))
    : nseq a _ :=
  seq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin)).

(* updating a subsequence in a sequence *)
Definition seq_update
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (input: seq a)
    : seq a :=
  update_sub (VectorDef.of_list s) start (length input) (VectorDef.of_list input).

(* updating only a single value in a sequence*)
Definition seq_upd
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (v: a)
    : seq a :=
  update_sub (VectorDef.of_list s) start 1 (VectorDef.of_list [v]).

Definition sub {a} (s : list a) start n :=
  slice s start (start + n).

Definition seq_update_start
  {a: Type}
 `{Default a}
  (s: seq a)
  (start_s: seq a)
    : seq a :=
    update_sub (VectorDef.of_list s) 0 (length start_s) (VectorDef.of_list start_s).

(* Definition array_update_slice *)
(*   {a : Type} *)
(*  `{Default a} *)
(*   {l : nat} *)
(*   (out: nseq a l) *)
(*   (start_out: nat) *)
(*   (input: nseq a l) *)
(*   (start_in: nat) *)
(*   (len: nat) *)
(*     : nseq a (length out) *)
(*   := *)
(*   update_sub (VectorDef.of_list out) start_out len *)
(*     (VectorDef.of_list (sub input start_in len)). *)

Definition array_update_slice
  {a : Type}
 `{Default a}
  {l : nat}
  (out: nseq a l)
  (start_out: nat)
  (input: seq a)
  (start_in: nat)
  (len: nat)
    : nseq a (length out)
  :=
  update_sub (VectorDef.of_list out) start_out len
    (VectorDef.of_list (sub input start_in len)).

Definition seq_update_slice
  {a : Type}
 `{Default a}
  (out: seq a)
  (start_out: nat)
  (input: seq a)
  (start_in: nat)
  (len: nat)
    : nseq a (length out)
  :=
  update_sub (VectorDef.of_list out) start_out len
    (VectorDef.of_list (sub input start_in len)).

Definition seq_concat
  {a : Type}
  (s1 :seq a)
  (s2: seq a)
  : seq a :=
  VectorDef.of_list (s1 ++ s2).

Definition seq_push
  {a : Type}
  (s1 :seq a)
  (s2: a)
  : seq a :=
  VectorDef.of_list (s1 ++ [s2]).

Definition seq_from_slice_range
  {a: Type}
 `{Default a}
  (input: seq a)
  (start_fin: (uint_size * uint_size))
  : seq a :=
  let out := array_new_ (default) (length input) in
  let (start, fin) := start_fin in
    update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) (VectorDef.of_list (slice input (from_uint_size start) (from_uint_size fin))).

Definition seq_from_seq {A} (l : seq A) := l.


(**** Chunking *)

Definition seq_num_chunks {a: choice_type} (s: seq a) (chunk_len: nat) : nat :=
  ((length s) + chunk_len - 1) / chunk_len.

Definition seq_chunk_len
  {a: choice_type}
  (s: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
    : nat :=
  let idx_start := chunk_len * chunk_num in
  if (length s) <? idx_start + chunk_len then
    (length s) - idx_start
  else
    chunk_len.

(* (* Definition seq_chunk_same_len_same_chunk_len *) *)
(* (*   {a: Type} *) *)
(* (*   (s1 s2: seq a) *) *)
(* (*   (chunk_len: nat) *) *)
(* (*   (chunk_num: nat) *) *)
(* (*   : Lemma *) *)
(* (*     (requires (LSeq.length s1 := LSeq.length s2 /\ chunk_len * chunk_num <= Seq.length s1)) *) *)
(* (*     (ensures (seq_chunk_len s1 chunk_len chunk_lseq. Admitted. *) *)

Definition seq_get_chunk
  {a: choice_type}
  (s: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
  : (uint_size * seq a)
    (* (requires (chunk_len * chunk_num <= Seq.length s))
    (ensures (fun '(out_len, chunk) =>
      out_len := seq_chunk_len s chunk_len chunk_num /\ LSeq.length chunk := out_len
    )) *)
 :=
  let idx_start := chunk_len * chunk_num in
  let out_len := seq_chunk_len s chunk_len chunk_num in
  (usize out_len, slice
    s idx_start (idx_start + seq_chunk_len s chunk_len chunk_num)).

Definition seq_set_chunk
  {a: Type}
 `{Default a}
  (s: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
  (chunk: seq a ) : seq a :=
 let idx_start := chunk_len * chunk_num in
 let out_len := seq_chunk_len s chunk_len chunk_num in
  VectorDef.to_list (update_sub (VectorDef.of_list s) idx_start out_len (VectorDef.of_list chunk)).


Definition seq_num_exact_chunks {a} (l : seq a) (chunk_size : uint_size) : uint_size :=
  divs (repr (Z.of_nat (length l))) chunk_size.

(* (* Until #84 is fixed this returns an empty sequence if not enough *) *)
Definition seq_get_exact_chunk {a : choice_type} (l : seq a) (chunk_size chunk_num: uint_size) : seq a :=
  let '(len, chunk) := seq_get_chunk l (from_uint_size chunk_size) (from_uint_size chunk_num) in
  if eqb len chunk_size then [] else chunk.

Definition seq_set_exact_chunk {a} `{H : Default a} := @seq_set_chunk a H.

Definition seq_get_remainder_chunk : forall {a : choice_type}, seq a -> uint_size -> seq a :=
  fun _ l chunk_size =>
    let chunks := seq_num_chunks l (from_uint_size chunk_size) in
    let last_chunk := if 0 <? chunks then
      chunks - 1
    else 0 in
    let (len, chunk) := seq_get_chunk l (from_uint_size chunk_size) last_chunk in
    if eqb len chunk_size then
      []
    else chunk.

Fixpoint seq_xor_ {WS} (x : seq int) (y : seq int) : seq int :=
  match x, y with
  | (x :: xs), (y :: ys) => @MachineIntegers.xor WS x y :: (seq_xor_ xs ys)
  | [], y => y
  | x, [] => x
  end.
Infix "seq_xor" := seq_xor_ (at level 33) : hacspec_scope.

Fixpoint seq_truncate {a} (x : seq a) (n : nat) : seq a := (* uint_size *)
  match x, n with
  | _, 0 => []
  | [], _ => []
  | (x :: xs), S n' => x :: (seq_truncate xs n')
  end.

(**** Numeric operations *)

(* Fixpoint seq_truncate {a} (x : seq a) (n : nat) : seq a := (* uint_size *) *)
(*   match x, n with *)
(*   | _, 0 => [] *)
(*   | [], _ => [] *)
(*   | (x :: xs), S n' => x :: (seq_truncate xs n') *)
(*   end. *)

(* (**** Numeric operations *) *)

(* (* takes two nseq's and joins them using a function op : a -> a -> a *) *)
(* Definition array_join_map *)
(*   {a: Type} *)
(*  `{Default a} *)
(*   {len: nat} *)
(*   (op: a -> a -> a) *)
(*   (s1: nseq a len) *)
(*   (s2 : nseq a len) := *)
(*   let out := s1 in *)
(*   foldi (usize 0) (usize len) (fun i out => *)
(*     let i := from_uint_size i in *)
(*     array_upd out i (op (array_index s1 i) (array_index s2 i)) *)
(*   ) out. *)

(* Infix "array_xor" := (array_join_map xor) (at level 33) : hacspec_scope. *)
(* Infix "array_add" := (array_join_map add) (at level 33) : hacspec_scope. *)
(* Infix "array_minus" := (array_join_map sub) (at level 33) : hacspec_scope. *)
(* Infix "array_mul" := (array_join_map mul) (at level 33) : hacspec_scope. *)
(* Infix "array_div" := (array_join_map divs) (at level 33) : hacspec_scope. *)
(* Infix "array_or" := (array_join_map or) (at level 33) : hacspec_scope. *)
(* Infix "array_and" := (array_join_map and) (at level 33) : hacspec_scope. *)

(* Definition array_eq_ *)
(*   {a: Type} *)
(*   {len: nat} *)
(*   (eq: a -> a -> bool) *)
(*   (s1: nseq a len) *)
(*   (s2 : nseq a len) *)
(*     : bool := Vector.eqb _ eq s1 s2. *)

(* Infix "array_eq" := (array_eq_ eq) (at level 33) : hacspec_scope. *)
(* Infix "array_neq" := (fun s1 s2 => negb (array_eq_ eq s1 s2)) (at level 33) : hacspec_scope. *)

(* TODO END *)

(**** Integers to arrays *)
Axiom uint32_to_le_bytes : int32 -> nseq_nat int8 4.
(* Definition uint32_to_le_bytes (x: uint32) : nseq uint8 4 := *)
(*   LBSeq.uint_to_bytes_le x. *)

Axiom uint32_to_be_bytes : int32 -> nseq_nat int8 4.
(* Definition uint32_to_be_bytes (x: uint32) : nseq uint8 4 := *)
(*   LBSeq.uint_to_bytes_be x *)

Axiom uint32_from_le_bytes : nseq_nat int8 4 -> int32.
(* Definition uint32_from_le_bytes (s: nseq uint8 4) : uint32 := *)
(*   LBSeq.uint_from_bytes_le s *)

Axiom uint32_from_be_bytes : nseq_nat int8 4 -> int32.
(* Definition uint32_from_be_bytes (s: nseq uint8 4) : uint32 := *)
(*   LBSeq.uint_from_bytes_be s *)

Axiom uint64_to_le_bytes : int64 -> nseq_nat int8 8.
(* Definition uint64_to_le_bytes (x: uint64) : nseq uint8 8 := *)
(*   LBSeq.uint_to_bytes_le x *)

Axiom uint64_to_be_bytes : int64 -> nseq_nat int8 8.
(* Definition uint64_to_be_bytes (x: uint64) : nseq uint8 8 := *)
(*   LBSeq.uint_to_bytes_be x *)

Axiom uint64_from_le_bytes : nseq_nat int8 8 -> int64.
(* Definition uint64_from_le_bytes (s: nseq uint8 8) : uint64 := *)
(*   LBSeq.uint_from_bytes_le s *)

Axiom uint64_from_be_bytes : nseq_nat int8 8 -> int64.
(* Definition uint64_from_be_bytes (s: nseq uint8 8) : uint64 := *)
(*   LBSeq.uint_from_bytes_be s *)

Axiom uint128_to_le_bytes : int128 -> nseq_nat int8 16.
(* Definition uint128_to_le_bytes (x: uint128) : nseq uint8 16 := *)
(*   LBSeq.uint_to_bytes_le x *)

Axiom uint128_to_be_bytes : int128 -> nseq_nat int8 16.
(* Definition uint128_to_be_bytes (x: uint128) : nseq uint8 16 := *)
(*   LBSeq.uint_to_bytes_be x *)

Axiom uint128_from_le_bytes : nseq uint8 (usize 16) -> int128.
(* Axiom uint128_from_le_bytes : nseq int8 16 -> int128. *)
(* Definition uint128_from_le_bytes (input: nseq uint8 16) : uint128 := *)
(*   LBSeq.uint_from_bytes_le input *)

Axiom uint128_from_be_bytes : nseq_nat int8 16 -> int128.
(* Definition uint128_from_be_bytes (s: nseq uint8 16) : uint128 := *)
(*   LBSeq.uint_from_bytes_be s *)

Axiom u32_to_le_bytes : int32 -> nseq_nat int8 4.
(* Definition u32_to_le_bytes (x: pub_uint32) : nseq pub_uint8 4 := *)
(*   LBSeq.uint_to_bytes_le x *)

Axiom u32_to_be_bytes : int32 -> nseq_nat int8 4.
(* Definition u32_to_be_bytes (x: pub_uint32) : nseq pub_uint8 4 := *)
(*   LBSeq.uint_to_bytes_be x *)

Axiom u32_from_le_bytes : nseq_nat int8 4 -> int32.
(* Definition u32_from_le_bytes (s: nseq pub_uint8 4) : pub_uint32 := *)
(*   LBSeq.uint_from_bytes_le s *)

Axiom u32_from_be_bytes : nseq_nat int8 4 -> int32.
(* Definition u32_from_be_bytes (s: nseq pub_uint8 4) : pub_uint32 := *)
(*   LBSeq.uint_from_bytes_be s *)

Axiom u64_to_le_bytes : int64 -> nseq_nat int8 8.
(* Definition u64_to_le_bytes (x: int64) : nseq int8 8 := *)
(*   LBSeq.uint_to_bytes_le x *)

Axiom u64_from_le_bytes : nseq_nat int8 8 -> int64.
(* Definition u64_from_le_bytes (s: nseq int8 8) : int64 := *)
(*   LBSeq.uint_from_bytes_le s *)

Axiom u128_to_le_bytes : int128 -> nseq_nat int8 16.
(* Definition u128_to_le_bytes (x: int128) : nseq int8 16 := *)
(*   LBSeq.uint_to_bytes_le x *)

Axiom u128_to_be_bytes : int128 -> nseq_nat int8 16.
(* Definition u128_to_be_bytes (x: int128) : nseq int8 16 := *)
(*   LBSeq.uint_to_bytes_be x *)

Axiom u128_from_le_bytes : nseq_nat int8 16 -> int128.
(* Definition u128_from_le_bytes (input: nseq int8 16) : int128 := *)
(*   LBSeq.uint_from_bytes_le input *)

Axiom u128_from_be_bytes : nseq_nat int8 16 -> int128.
(* Definition u128_from_be_bytes (s: nseq int8 16) : pub_uint128 := *)
(*   LBSeq.uint_from_bytes_be s *)


(* (*** Nats *) *)


Definition nat_mod (p : Z) : Set := GZnZ.znz p.


(* Definition nat_mod_equal {p} (a b : nat_mod p) : bool := *)
(*   Z.eqb (GZnZ.val p a) (GZnZ.val p b). *)

(* Definition nat_mod_zero {p} : nat_mod p := GZnZ.zero p. *)
(* Definition nat_mod_one {p} : nat_mod p := GZnZ.one p. *)
(* Definition nat_mod_two {p} : nat_mod p := GZnZ.mkznz p _ (GZnZ.modz p 2). *)


(* convenience coercions from nat_mod to Z and N *)
Coercion Z.of_N : N >-> Z.

(* Definition nat_mod_add {n : Z} (a : nat_mod n) (b : nat_mod n) : nat_mod n := GZnZ.add n a b. *)

(* Infix "+%" := nat_mod_add (at level 33) : hacspec_scope. *)

(* Definition nat_mod_mul {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.mul n a b. *)
(* Infix "*%" := nat_mod_mul (at level 33) : hacspec_scope. *)

(* Definition nat_mod_sub {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.sub n a b. *)
(* Infix "-%" := nat_mod_sub (at level 33) : hacspec_scope. *)

(* Definition nat_mod_div {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.div n a b. *)
(* Infix "/%" := nat_mod_div (at level 33) : hacspec_scope. *)

(* (* A % B = (a * B + r) *) *)

(* Definition nat_mod_neg {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.opp n a. *)

(* Definition nat_mod_inv {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.inv n a. *)

(* Definition nat_mod_exp {p : Z} (a:nat_mod p) (n : uint_size) : nat_mod p := *)
(*   let n : nat := Z.to_nat (from_uint_size n) in *)
(*   let fix exp_ (e : nat_mod p) (n : nat) := *)
(*     match n with *)
(*     | 0%nat => nat_mod_one *)
(*     | S n => nat_mod_mul a (exp_ a n) *)
(*     end in *)
(*   exp_ a n. *)

(* Definition nat_mod_pow {p} := @nat_mod_exp p. *)
(* Definition nat_mod_pow_self {p} := @nat_mod_exp p. *)

Close Scope nat_scope.
Open Scope Z_scope.

(* (* We assume x < m *) *)
Definition nat_mod_from_secret_literal {m : Z} (x:int128) : nat_mod m.
Proof.
  unfold nat_mod.
  (* since we assume x < m, it will be true that (unsigned x) = (unsigned x) mod m  *)
  remember ((unsigned WORDSIZE128 x) mod m) as zmodm.
  apply (GZnZ.mkznz m zmodm).
  rewrite Heqzmodm.
  rewrite Zmod_mod.
  reflexivity.
Defined.

Definition nat_mod_from_literal (m : Z) (x:int128) : nat_mod m := nat_mod_from_secret_literal x.

(* TODO START *)
(* Axiom nat_mod_to_byte_seq_le : forall {n : Z}, nat_mod n -> seq int8. *)
(* Axiom nat_mod_to_byte_seq_be : forall {n : Z}, nat_mod n -> seq int8. *)
(* Axiom nat_mod_to_public_byte_seq_le : forall (n : Z), nat_mod n -> seq int8. *)
(* Axiom nat_mod_to_public_byte_seq_be : forall (n : Z), nat_mod n -> seq int8. *)
Axiom chFin_to_byte_seq_le : forall {n}, chFin n -> seq int8.
(* Axiom chFin_to_byte_seq_le : forall {n : Z}, chFin (Z.to_nat n) -> seq int8. *)

Definition Z_pos_to_pos (p : BinNums.positive) : Prelude.positive.
Proof.
  intros.
  apply (@Prelude.mkpos (Pos.to_nat p)).
  unfold Prelude.Positive.
  pose proof (Pos2Nat.is_pos p).
  destruct Pos.to_nat.
  - inversion H.
  - reflexivity.
Defined.


Axiom chFin_to_byte_seq_be : forall {n : Z}, chFin (Z_pos_to_pos (Z.to_pos n)) -> seq int8.
Axiom chFin_to_public_byte_seq_le : forall (n : Z), chFin (Z_pos_to_pos (Z.to_pos n)) -> seq int8.
Axiom chFin_to_public_byte_seq_be : forall (n : Z), chFin (Z_pos_to_pos (Z.to_pos n)) -> seq int8.

(* TODO END *)

(* Definition nat_mod_bit {n : Z} (a : nat_mod n) (i : uint_size) := *)
(*   Z.testbit (GZnZ.val n a) (from_uint_size i). *)

(* Alias for nat_mod_bit *)
(* Definition nat_get_mod_bit {p} (a : nat_mod p) := nat_mod_bit a. *)
(* *)
(* Definition nat_mod_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod_mod n) : lseq pub_uint8 len = *)
(*   Definition n' := n % (pow2 (8 * len)) in *)
(*   Lib.ByteSequence.nat_mod_to_bytes_le len n'*)

(* Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len = *)
(*   Definition n' := n % (pow2 (8 * len)) in *)
(*   Lib.ByteSequence.nat_to_bytes_be len n' *)

Axiom array_declassify_eq : forall  {A l}, nseq A l -> nseq A l -> bool.
(* TODO START *)
(* Axiom array_to_le_uint32s : forall {A l}, nseq A l -> nseq uint32 l. *)
(* Axiom array_to_be_uint32s : forall {l}, nseq uint8 l -> nseq uint32 (l/4). *)
(* Axiom array_to_le_bytes : forall {A l}, nseq A l -> seq uint8. *)
(* Axiom array_to_be_bytes : forall {A l}, nseq A l -> seq uint8. *)
(* TODO END *)
(* Axiom nat_mod_from_byte_seq_le : forall  {A n}, seq A -> nat_mod n. *)
(* Axiom most_significant_bit : forall {m}, nat_mod m -> uint_size -> uint_size. *)


(* We assume 2^x < m *)
Definition nat_mod_pow2 (m : Z) (x : N) : nat_mod m.
Proof.
  remember (Z.pow 2 (Z.of_N x) mod m) as y.
  apply (GZnZ.mkznz m y).
  rewrite Heqy.
  rewrite Zmod_mod.
  reflexivity.
Defined.


Section Casting.

  (* Type casts, as defined in Section 4.5 in https://arxiv.org/pdf/1106.3448.pdf *)
  Class Cast A B := cast : A -> B.

  Arguments cast {_} _ {_}.

  Notation "' x" := (cast _ x) (at level 20) : hacspec_scope.
  Open Scope hacspec_scope.

  (* Casting to self is always possible *)
  Global Instance cast_self {A} : Cast A A := {
    cast a := a
  }.

  Global Instance cast_transitive {A B C} `{Hab: Cast A B} `{Hbc: Cast B C} : Cast A C := {
    cast a := Hbc (Hab a)
  }.

  Global Instance cast_prod {A B C D} `{Cast A B} `{Cast C D} : Cast (A * C) (B * D) := {
    cast '(a, c) := (cast B a, cast D c)
  }.

  Global Instance cast_option {A B} `{Cast A B} : Cast (option A) (option B) := {
    cast a := match a with Some a => Some (cast B a) | None => None end
  }.

  Global Instance cast_option_b {A B} `{Cast A B} : Cast A (option B) := {
    cast a := Some (cast B a)
  }.

  (* Global Instances for common types *)

  Global Instance cast_nat_to_N : Cast nat N := {
    cast := N.of_nat
  }.

  Global Instance cast_N_to_Z : Cast N Z := {
    cast := Z.of_N
  }.

  Global Instance cast_Z_to_int {WS: WORDSIZE} : Cast Z (@int WS) := {
    cast n := repr WS n
  }.

  (* Global Instance cast_natmod_to_Z {p} : Cast (nat_mod p) Z := { *)
  (*   cast n := GZnZ.val p n *)
  (* }. *)

  (* Note: should be aware of typeclass resolution with int/uint since they are just aliases of each other currently *)
  Global Instance cast_int8_to_uint32 : Cast int8 uint32 := {
    cast n := repr WORDSIZE32 (unsigned WORDSIZE8 n)
  }.
  Global Instance cast_int8_to_int32 : Cast int8 int32 := {
    cast n := repr WORDSIZE32 (signed WORDSIZE8 n)
  }.

  Global Instance cast_uint8_to_uint32 : Cast uint8 uint32 := {
    cast n := repr WORDSIZE32 (unsigned WORDSIZE8 n)
  }.

  Global Instance cast_int_to_nat `{WS: WORDSIZE} : Cast (int WS) nat := {
    cast n := Z.to_nat (signed WS n)
  }.

  Close Scope hacspec_scope.
End Casting.


Global Arguments pair {_ _} & _ _.
(* Global Arguments id {_} & _. *)
Section Coercions.
  (* First, in order to have automatic coercions for tuples, we add bidirectionality hints: *)

  (* Integer coercions *)
  (* We have nat >-> N >-> Z >-> int/int32 *)
  (* and uint >-> Z *)
  (* and N >-> nat *)

  Global Coercion N.to_nat : N >-> nat.
  (* Global Coercion Z.of_N : N >-> Z. *)

  Global Coercion repr : Z >-> int.

  Global Coercion Z_to_int `{WS: WORDSIZE} (n : Z) : (int WS) := repr WS n.
  (* Global Coercion  Z_to_int : Z >-> int. *)

  Global Coercion Z_to_uint_size (n : Z) : uint_size.
  Proof.
    unfold uint_size.
    unfold int32.
    unfold int.

    apply (repr WORDSIZE32 n).
  Qed.
  (* Global Coercion Z_to_uint_size : Z >-> uint_size. *)
  Global Coercion Z_to_int_size (n : Z) : int_size := repr WORDSIZE32 n.
  (* Global Coercion Z_to_int_size : Z >-> int_size. *)

  Global Coercion N_to_int `{WS: WORDSIZE} (n : N) : (int WS) := repr WS (Z.of_N n).
  Global Coercion N.of_nat : nat >-> N.
  (* Global Coercion N_to_int : N >-> int. *)
  Global Coercion N_to_uint_size (n : Z) : uint_size := repr WORDSIZE32 n.
  (* Global Coercion N_to_uint_size : Z >-> uint_size. *)
  Global Coercion nat_to_int `{WS: WORDSIZE} (n : nat) := repr WS (Z.of_nat n).
  (* Global Coercion nat_to_int : nat >-> int. *)

  Global Coercion uint_to_uint_sizable {A : choice_type} `{H : UInt_sizable A} (n : uint_size) : A.
  Proof.
    apply (from_uint_size n).
  Defined.
  
  Global Coercion  uint_size_to_nat (n : uint_size) : nat := from_uint_size n.
  Notation uint_sort := (Choice.sort uint_size).
  Definition  uint_size_choice_to_nat (n : uint_sort) : nat := from_uint_size n.
  Global Coercion uint_size_choice_to_nat : uint_sort >-> nat.
  
  Global Coercion uint_size_to_Z (n : uint_size) : Z := from_uint_size n.
  (* Global Coercion uint_size_to_Z : uint_size >-> Z. *)

  Global Coercion uint32_to_nat (n : uint32) : nat := Z.to_nat (unsigned WORDSIZE32 n).
  (* Global Coercion uint32_to_nat : uint32 >-> nat. *)

  Global Coercion uint_size_to_N (n : uint_size) : N := from_uint_size n.
  (* Global Coercion uint_size_to_Z : uint_size >-> Z. *)

  Global Coercion GZnZ.val : GZnZ.znz >-> Z.

  Global Coercion int_to_nat {WS : WORDSIZE} (n : @int WS) : nat := Z.to_nat (unsigned WS n).
  
  Global Coercion int8_to_nat (n : int8) : nat := Z.to_nat (unsigned WORDSIZE8 n).
  (* Global Coercion int8_to_nat : int8 >-> nat. *)
  Global Coercion int16_to_nat (n : int16) : nat := Z.to_nat (unsigned WORDSIZE16 n).
  (* Global Coercion int16_to_nat : int16 >-> nat. *)
  Global Coercion int32_to_nat (n : int32) : nat := Z.to_nat (unsigned WORDSIZE32 n).
  (* Global Coercion int32_to_nat : int32 >-> nat. *)
  Global Coercion int64_to_nat (n : int64) : nat := Z.to_nat (unsigned WORDSIZE64 n).
  (* Global Coercion int64_to_nat : int64 >-> nat. *)
  Global Coercion int128_to_nat (n : int128) : nat := Z.to_nat (unsigned WORDSIZE128 n).
  (* Global Coercion int128_to_nat : int128 >-> nat. *)

  (* coercions int8 >-> int16 >-> ... int128 *)

  Global Coercion  int8_to_int16 (n : int8) : int16 := repr WORDSIZE16 (unsigned WORDSIZE8 n).
  (* Global Coercion int8_to_int16 : int8 >-> int16. *)

  Global Coercion int8_to_int32 (n : int8) : int32 := repr WORDSIZE32 (unsigned WORDSIZE8 n).
  (* Global Coercion int8_to_int32 : int8 >-> int32. *)

  Global Coercion int16_to_int32 (n : int16) : int32 := repr WORDSIZE32 (unsigned WORDSIZE16 n).
  (* Global Coercion int16_to_int32 : int16 >-> int32. *)

  Global Coercion int32_to_int64 (n : int32) : int64 := repr WORDSIZE64 (unsigned WORDSIZE32 n).
  (* Global Coercion int32_to_int64 : int32 >-> int64. *)

  (* TODO *)
  Global Coercion int64_to_int128 (n : int64) : int128 := repr WORDSIZE128 (unsigned WORDSIZE64 n).
  (* Global Coercion int64_to_int128 : int64 >-> int128. *)

  Global Coercion int32_to_int128 (n : int32) : int128 := repr WORDSIZE128 (unsigned WORDSIZE32 n).
  (* Global Coercion int32_to_int128 : int32 >-> int128. *)

  Global Coercion uint_size_to_int64 (n : uint_size) : int64 := repr WORDSIZE64 (unsigned WORDSIZE32 n).
  (* Global Coercion uint_size_to_int64 : uint_size >-> int64. *)


  (* coercions into nat_mod *)
  (* Global Coercion Z_in_nat_mod {m : Z} (x:Z) : nat_mod m. *)
  (* Proof. *)
  (*   unfold nat_mod. *)
  (*   remember ((x) mod m) as zmodm. *)
  (*   apply (GZnZ.mkznz m zmodm). *)
  (*   rewrite Heqzmodm. *)
  (*   rewrite Zmod_mod. *)
  (*   reflexivity. *)
  (* Defined. *)
  (* (* Global Coercion Z_in_nat_mod : Z >-> nat_mod.  *) *)

  (* Global Coercion int_in_nat_mod {m : Z} `{WS: WORDSIZE} (x:int) : nat_mod m. *)
  (* Proof. *)
  (*   unfold nat_mod. *)
  (*   (* since we assume x < m, it will be true that (unsigned x) = (unsigned x) mod m  *) *)
  (*   remember ((unsigned x) mod m) as zmodm. *)
  (*   apply (GZnZ.mkznz m zmodm). *)
  (*   rewrite Heqzmodm. *)
  (*   rewrite Zmod_mod. *)
  (*   reflexivity. *)
  (*   Show Proof. *)
  (* Defined. *)
  (* (* Global Coercion int_in_nat_mod : int >-> nat_mod. *) *)

  (* Global Coercion uint_size_in_nat_mod (n : uint_size) : nat_mod 16 := int_in_nat_mod n. *)
  (* Global Coercion uint_size_in_nat_mod : uint_size >-> nat_mod. *)

End Coercions.


(*** Casting *)

Definition uint128_from_usize (n : uint_size) : int128 := repr WORDSIZE128 (unsigned WORDSIZE32 n).
Definition uint64_from_usize (n : uint_size) : int64 := repr WORDSIZE64 (unsigned WORDSIZE32 n).
Definition uint32_from_usize (n : uint_size) : int32 := repr WORDSIZE32 (unsigned WORDSIZE32 n).
Definition uint16_from_usize (n : uint_size) : int16 := repr WORDSIZE16 (unsigned WORDSIZE32 n).
Definition uint8_from_usize (n : uint_size) : int8 := repr WORDSIZE8 (unsigned WORDSIZE32 n).

Definition uint128_from_uint8 (n : int8) : int128 := repr WORDSIZE128 (unsigned WORDSIZE8 n).
Definition uint64_from_uint8 (n : int8) : int64 := repr WORDSIZE64 (unsigned WORDSIZE8 n).
Definition uint32_from_uint8 (n : int8) : int32 := repr WORDSIZE32 (unsigned WORDSIZE8 n).
Definition uint16_from_uint8 (n : int8) : int16 := repr WORDSIZE16 (unsigned WORDSIZE8 n).
Definition usize_from_uint8 (n : int8) : uint_size := repr WORDSIZE32 (unsigned WORDSIZE8 n).

Definition uint128_from_uint16 (n : int16) : int128 := repr WORDSIZE128 (unsigned WORDSIZE16 n).
Definition uint64_from_uint16 (n : int16) : int64 := repr WORDSIZE64 (unsigned WORDSIZE16 n).
Definition uint32_from_uint16 (n : int16) : int32 := repr WORDSIZE32 (unsigned WORDSIZE16 n).
Definition uint8_from_uint16 (n : int16) : int8 := repr WORDSIZE8 (unsigned WORDSIZE16 n).
Definition usize_from_uint16 (n : int16) : uint_size := repr WORDSIZE32 (unsigned WORDSIZE16 n).

Definition uint128_from_uint32 (n : int32) : int128 := repr WORDSIZE128 (unsigned WORDSIZE32 n).
Definition uint64_from_uint32 (n : int32) : int64 := repr WORDSIZE64 (unsigned WORDSIZE32 n).
Definition uint16_from_uint32 (n : int32) : int16 := repr WORDSIZE16 (unsigned WORDSIZE32 n).
Definition uint8_from_uint32 (n : int32) : int8 := repr WORDSIZE8 (unsigned WORDSIZE32 n).
Definition usize_from_uint32 (n : int32) : uint_size := repr WORDSIZE32 (unsigned WORDSIZE32 n).

Definition uint128_from_uint64 (n : int64) : int128 := repr WORDSIZE128 (unsigned WORDSIZE64 n).
Definition uint32_from_uint64 (n : int64) : int32 := repr WORDSIZE32 (unsigned WORDSIZE64 n).
Definition uint16_from_uint64 (n : int64) : int16 := repr WORDSIZE16 (unsigned WORDSIZE64 n).
Definition uint8_from_uint64 (n : int64) : int8 := repr WORDSIZE8 (unsigned WORDSIZE64 n).
Definition usize_from_uint64 (n : int64) : uint_size := repr WORDSIZE32 (unsigned WORDSIZE64 n).

Definition uint64_from_uint128 (n : int128) : int64 := repr WORDSIZE64 (unsigned WORDSIZE128 n).
Definition uint32_from_uint128 (n : int128) : int32 := repr WORDSIZE32 (unsigned WORDSIZE128 n).
Definition uint16_from_uint128 (n : int128) : int16 := repr WORDSIZE16 (unsigned WORDSIZE128 n).
Definition uint8_from_uint128 (n : int128) : int8 := repr WORDSIZE8 (unsigned WORDSIZE128 n).
Definition usize_from_uint128 (n : int128) : uint_size := repr WORDSIZE32 (unsigned WORDSIZE128 n).

(** Equalities **)

(* Comparisons, boolean equality, and notation *)

Class EqDec (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true <-> x = y }.

Infix "=.?" := eqb (at level 40) : hacspec_scope.
Infix "!=.?" := (fun a b => negb (eqb a b)) (at level 40) : hacspec_scope.

Class Comparable (A : Type) := {
  ltb : A -> A -> bool;
  leb : A -> A -> bool;
  gtb : A -> A -> bool;
  geb : A -> A -> bool;
}.
Infix "<.?" := ltb (at level 42) : hacspec_scope.
Infix "<=.?" := leb (at level 42) : hacspec_scope.
Infix ">.?" := gtb (at level 42) : hacspec_scope.
Infix ">=.?" := geb (at level 42) : hacspec_scope.

Theorem eqb_refl : forall {A} {H : EqDec A} (x : A), @eqb A H x x = true.
Proof.
  intros.
  now rewrite eqb_leibniz.
Qed.

Global Program Instance nat_eqdec : EqDec nat := {
  eqb := Nat.eqb;
  eqb_leibniz := Nat.eqb_eq ;
}.

Global Instance nat_comparable : Comparable nat := {
  ltb := Nat.ltb;
  leb := Nat.leb;
  gtb a b := Nat.ltb b a;
  geb a b := Nat.leb b a;
}.

Global Instance N_eqdec : EqDec N := {
  eqb := N.eqb;
    eqb_leibniz := N.eqb_eq ;
}.

Global Instance N_comparable : Comparable N := {
  ltb := N.ltb;
  leb := N.leb;
  gtb a b := N.ltb b a;
  geb a b := N.leb b a;
}.

Global Instance Z_eqdec : EqDec Z := {
  eqb := Z.eqb;
  eqb_leibniz := Z.eqb_eq ;
}.

Global Instance Z_comparable : Comparable Z := {
  ltb := Z.ltb;
  leb := Z.leb;
  gtb a b := Z.ltb b a;
  geb a b := Z.leb b a;
}.

Lemma int_eqb_eq : forall {WS : WORDSIZE} (a b : int), eq a b = true <-> a = b.
Proof.
  intros. split.
  - apply same_if_eq.
  - intros. rewrite H. apply eq_true.
Qed.

Global Instance int_eqdec `{WORDSIZE}: EqDec int := {
  eqb := eq;
  eqb_leibniz := int_eqb_eq ;
}.

Global Instance int_comparable `{WORDSIZE} : Comparable int := {
  ltb := lt;
  leb a b := if eq a b then true else lt a b ;
  gtb a b := lt b a;
  geb a b := if eq a b then true else lt b a;
}.

Definition uint8_equal : int8 -> int8 -> bool := eqb.

(* Definition nat_mod_val (p : Z) (a : nat_mod p) : Z := GZnZ.val p a. *)

(* Theorem nat_mod_eqb_spec : forall {p} (a b : nat_mod p), Z.eqb (nat_mod_val p a) (nat_mod_val p b) = true <-> a = b. *)
(* Proof. *)
(*   split ; intros. *)
(*   - apply Z.eqb_eq in H. *)
(*     destruct a, b. *)
(*     cbn in H. *)
(*     apply (GZnZ.zirr p val val0 inZnZ inZnZ0 H). *)
(*   - subst. *)
(*     apply Z.eqb_eq. *)
(*     reflexivity. *)
(* Qed. *)

(* Global Instance nat_mod_eqdec {p} : EqDec (nat_mod p) := { *)
(*   eqb a b := Z.eqb (nat_mod_val p a) (nat_mod_val p b); *)
(*   eqb_leibniz := nat_mod_eqb_spec; *)
(* }. *)

(* Global Instance nat_mod_comparable `{p : Z} : Comparable (nat_mod p) := { *)
(*   ltb a b := Z.ltb (nat_mod_val p a) (nat_mod_val p b); *)
(*   leb a b := if Zeq_bool a b then true else Z.ltb (nat_mod_val p a) (nat_mod_val p b) ; *)
(*   gtb a b := Z.ltb (nat_mod_val p b) (nat_mod_val p a); *)
(*   geb a b := if Zeq_bool b a then true else Z.ltb (nat_mod_val p b) (nat_mod_val p a) ; *)
(* }. *)

(* Fixpoint nat_mod_rem_aux {n : Z} (a:nat_mod n) (b:nat_mod n) (f : nat) {struct f} : nat_mod n := *)
(*   match f with *)
(*   | O => a *)
(*   | S f' => *)
(*       if geb a b *)
(*       then nat_mod_rem_aux (nat_mod_sub a b) b f' *)
(*       else a *)
(*   end. *)

Definition nat_mod_rem {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n :=
  if nat_mod_equal b nat_mod_zero
  then nat_mod_one
  else nat_mod_rem_aux a b (S (nat_mod_div a b)).

Infix "rem" := nat_mod_rem (at level 33) : hacspec_scope.

Global Instance bool_eqdec : EqDec bool := {
  eqb := Bool.eqb;
  eqb_leibniz := Bool.eqb_true_iff;
}.

Global Instance string_eqdec : EqDec String.string := {
  eqb := String.eqb;
  eqb_leibniz := String.eqb_eq ;
}.

(* TODO START  *)
(* Global Instance unit_eqdec : EqDec unit := { *)
(*   eqb := fun _ _ => true ; *)
(*   eqb_leibniz := fun 'tt 'tt => (conj (fun _ => eq_refl) (fun _ => eq_refl)) ; *)
(* }. *)
(* TODO END *)

Require Import Sumbool.
Open Scope list_scope.

Fixpoint list_eqdec {A} `{EqDec A} (l1 l2 : list A) : bool :=
  match l1, l2 with
  | x::xs, y::ys => if eqb x y then list_eqdec xs ys else false
  | [], [] => true
  | _,_ => false
  end.

Lemma list_eqdec_refl : forall {A} `{EqDec A} (l1 : list A), list_eqdec l1 l1 = true.
Proof.
  intros ; induction l1 ; cbn ; try rewrite eqb_refl ; easy.
Qed.

Lemma list_eqdec_sound : forall {A} `{EqDec A} (l1 l2 : list A), list_eqdec l1 l2 = true <-> l1 = l2.
Proof.
  intros A H l1.
  induction l1 ; induction l2 ; split ; intros ; simpl in * ; try easy ; try inversion H0.
  - (* inductive case *)
    apply Field_theory.if_true in H0; destruct H0.
    f_equal.
    (* show heads are equal *)
    + apply (proj1 (eqb_leibniz a a0) H0).
    (* show tails are equal using induction hypothesis *)
    + apply IHl1. assumption.
  - rewrite eqb_refl.
    apply list_eqdec_refl.
Qed.

Global Instance List_eqdec {A} `{EqDec A} : EqDec (list A) := {
  eqb := list_eqdec;
  eqb_leibniz := list_eqdec_sound;
}.

Lemma vector_eqb_sound : forall {A : Type} {n : nat} `{EqDec A} (v1 v2 : VectorDef.t A n), Vector.eqb _ eqb v1 v2 = true <-> v1 = v2.
Proof.
  intros.
  apply Vector.eqb_eq.
  intros.
  apply eqb_leibniz.
Qed.

Global Program Instance Vector_eqdec {A n} `{EqDec A}: EqDec (VectorDef.t A n) := {
  eqb := Vector.eqb _ eqb;
  eqb_leibniz := vector_eqb_sound;
}.

Global Program Instance Dec_eq_prod (A B : Type) `{EqDec A} `{EqDec B} : EqDec (A * B) := {
  eqb '(a0, b0) '(a1, b1) := andb (eqb a0 a1) (eqb b0 b1)
}.
Next Obligation.
  split ; intros.
  - symmetry in H1.
    destruct x, y.
    apply Bool.andb_true_eq in H1. destruct H1.
    symmetry in H1. apply (eqb_leibniz a a0) in H1.
    symmetry in H2. apply (eqb_leibniz b b0) in H2.
    rewrite H1. rewrite H2. reflexivity.
  - destruct x, y.
    inversion_clear H1. cbn.
    now do 2 rewrite eqb_refl.
Defined.

(*** Result *)

Inductive result (a: Type) (b: Type) :=
  | Ok : a -> result a b
  | Err : b -> result a b.

Arguments Ok {_ _}.
Arguments Err {_ _}.

(*** Be Bytes *)

Fixpoint log2_positive (z : BinNums.positive) {struct z} : nat :=
  match z with
  | 1%positive => 0
  | (p~0)%positive => S (log2_positive p)
  | (p~1)%positive => S (log2_positive p)
  end    .
Definition log2_WS {WS : WORDSIZE} : nat :=
  @log2_positive (Pos.of_nat (@wordsize WS)).

Fixpoint nat_be_range_at_position (k : nat) (z : Z) (n : Z) : list bool :=
  match k with
  | O => []
  | S k' => Z.testbit z (n + Z.of_nat k') :: nat_be_range_at_position k' z n
  end.

Fixpoint nat_be_range_to_position_ (z : list bool) (val : Z) : Z :=
  match z with
  | [] => val
  | x :: xs => nat_be_range_to_position_ xs ((if x then 2 ^ List.length xs else 0) + val)
  end.

Definition nat_be_range_to_position (k : nat) (z : list bool) (n : Z) : Z :=
  (nat_be_range_to_position_ z 0 * 2^(Z.of_nat k * n)).

Definition nat_be_range (k : nat) (z : Z) (n : nat) : Z :=
  nat_be_range_to_position_ (nat_be_range_at_position k z (Z.of_nat n * Z.of_nat k)) 0. (* * 2^(k * n) *)

Definition int_to_be_bytes {WS : WORDSIZE} : @int WS -> nseq_nat int8 8 :=
  fun k =>
    let chunks := Z.to_nat (2 ^ (Z.of_nat (@log2_WS WS) / Z.of_nat (@log2_WS WORDSIZE8))) in
    let k_nat := Z.of_nat (int_to_nat k) in
    array_from_list_nat (int8) [
            @repr WORDSIZE8 (nat_be_range chunks k_nat 7) ;
            @repr WORDSIZE8 (nat_be_range chunks k_nat 6) ;
            @repr WORDSIZE8 (nat_be_range chunks k_nat 5) ;
            @repr WORDSIZE8 (nat_be_range chunks k_nat 4) ;
            @repr WORDSIZE8 (nat_be_range chunks k_nat 3) ;
            @repr WORDSIZE8 (nat_be_range chunks k_nat 2) ;
            @repr WORDSIZE8 (nat_be_range chunks k_nat 1) ;
            @repr WORDSIZE8 (nat_be_range chunks k_nat 0)].

Open Scope hacspec_scope.

Definition int_from_be_bytes_fold_fun [WS : WORDSIZE] (i : int8) (s : prod nat (@int WS)) : prod nat (@int WS).
Proof.
  pose (chunks := 2 ^ (@log2_WS WS / @log2_WS WORDSIZE8)).
  destruct s as [n v].
  split.
  apply (S n).
  pose (@repr WS (((int8_to_nat i) * (2 ^ (chunks * n)))%Z)).
  unfold int in *.
  destruct WS.
  destruct wordsize.
  - contradiction.
  - Locate ".+".
    apply (s .+ v).
Defined.

  (* let chunks := 2 ^ (@log2_WS WS / @log2_WS WORDSIZE8) in *)
  (* let (n,v) := s in *)
  (* (S n, (v .+ (@repr WS _ (((int8_to_nat i) * (2 ^ (chunks * n)))%Z)))). *)
  
Definition int_from_be_bytes {WS : WORDSIZE} : nseq_nat int8 8 -> int WS :=
  (fun v => snd (fold_right (@int_from_be_bytes_fold_fun WS) (0%nat, @repr WS 0) (array_to_list v))).
                                                                                
Definition u64_to_be_bytes : int64 -> nseq_nat int8 8 := @int_to_be_bytes WORDSIZE64.
Definition u64_from_be_bytes : nseq_nat int8 8 -> int64 := @int_from_be_bytes WORDSIZE64.

(* Unimplemented in library *)
(* Axiom nat_mod_to_byte_seq_be : forall {n : Z}, Fp_finFieldType (Z.to_nat n) -> seq int8. *)
  
  
  (*    @seq . *)

(* (*** Monad / Bind *) *)

(* Class Monad (M : Type -> Type) := *)
(*   { bind {A B} (x : M A) (f : A -> M B) : M B ; *)
(*     ret {A} (x : A) : M A ; *)
(*   }. *)

(* Definition result2 (b: Type) (a: Type) := result a b. *)

(* Definition result_bind {A B C} (r : result2 C A) (f : A -> result2 C B) : result2 C B := *)
(*   match r with *)
(*     Ok a => f a *)
(*   | Err e => Err e *)
(*   end. *)

(* Definition result_ret {A C} (a : A) : result2 C A := Ok a. *)

(* Global Instance result_monad {C} : Monad (result2 C) := *)
(*   Build_Monad (result2 C) (fun A B => @result_bind A B C) (fun A => @result_ret A C). *)

(* Definition option_bind {A B} (r : option A) (f : A -> option B) : option B := *)
(*   match r with *)
(*     Some (a) => f a *)
(*   | None => None *)
(*   end. *)



(* Definition option_ret {A} (a : A) : option A := Some a. *)

(* Global Instance option_monad : Monad option := *)
(*   Build_Monad option (@option_bind) (@option_ret). *)

(* Definition option_is_none {A} (x : option A) : bool := *)
(*   match x with *)
(*   | None => true *)
(*   | _ => false *)
(*   end. *)

(* Definition foldi_bind {A : Type} {M : Type -> Type} `{Monad M} (a : uint_size) (b : uint_size) (f : uint_size -> A -> M A) (init : M A) : M A := *)
(*   @foldi (M A) a b (fun x y => bind y (f x)) init. *)

(* Definition lift_to_result {A B C} (r : result A C) (f : A -> B) : result B C := *)
(*   result_bind r (fun x => result_ret (f x)). *)

(* Definition result_uint_size_to_result_int64 {C} (r : result uint_size C) := lift_to_result r uint_size_to_int64. *)

(* Definition result_uint_size_unit := (result uint_size unit). *)
(* Definition result_int64_unit := (result int64 unit). *)

(* Definition result_uint_size_unit_to_result_int64_unit (r : result_uint_size_unit) : result_int64_unit := result_uint_size_to_result_int64 r. *)

(* Global Coercion lift_to_result_coerce {A B C} (f : A -> B) := (fun (r : result A C) => lift_to_result r f). *)

(* Global Coercion result_uint_size_unit_to_result_int64_unit : result_uint_size_unit >-> result_int64_unit. *)

(* (*** Notation *) *)

(* Notation "'ifbnd' b 'then' x 'else' y '>>' f" := (if b then f x else f y) (at level 200). *)
(* Notation "'ifbnd' b 'thenbnd' x 'else' y '>>' f" := (if b then (bind x) f else f y) (at level 200). *)
(* Notation "'ifbnd' b 'then' x 'elsebnd' y '>>' f" := (if b then f x else (bind y) f) (at level 200). *)
(* Notation "'ifbnd' b 'thenbnd' x 'elsebnd' y '>>' f" := (if b then bind x f else bind y f) (at level 200). *)

(* Notation "'foldibnd' s 'to' e 'for' z '>>' f" := (foldi s e (fun x y => bind y (f x)) (Ok z)) (at level 50). *)

(* Axiom nat_mod_from_byte_seq_be : forall  {A n}, seq A -> nat_mod n. *)

(*** Default *)

(* Default instances for common types *)
Global Instance nat_default : Default nat := {
  default := 0%nat
}.
Global Instance N_default : Default N := {
  default := 0%N
}.
Global Instance Z_default : Default Z := {
  default := Z.of_nat 0
}.
(* Global Instance uint_size_default : Default uint_size := { *)
(*   default := Zp0 *)
(* }. *)
(* Global Instance int_size_default : Default int_size := { *)
(*   default := Zp0 *)
(* }. *)
Global Instance int_default {WS : WORDSIZE} : Default (@int WS) := {
  default := repr WS 0
}.
(* Global Instance nat_mod_default {p : Z} : Default (nat_mod p) := { *)
(*   default := nat_mod_zero *)
(* }. *)
Global Instance prod_default {A B} `{Default A} `{Default B} : Default (prod A B) := {
  default := (default, default)
}.

(*** chFin *)

Definition helper : forall (z m : Z), z = z mod m -> 0 < m -> 0 <= z.
Proof.
  intros.
  destruct (Z.mod_pos_bound z m H0) as [H1 _].
  rewrite H.
  apply H1.
Qed.    

Theorem helper2 : forall (a b : nat), (a < b)%N -> a < b.
Proof.
  induction a ; destruct b ; intros.
  - discriminate H.
  - easy.
  - discriminate H.
  - do 2 rewrite Nnat.Nat2N.inj_succ.
    do 2 rewrite N2Z.inj_succ.
    apply Zsucc_lt_compat.
    apply IHa.
    apply ltnSE.
    apply H.
Qed.

Theorem helper3 : forall (a b : nat), a < b -> (a < b)%N.
Proof.
  induction a ; destruct b ; intros.
  - discriminate H.
  - easy.
  - discriminate H.
  - do 2 rewrite Nnat.Nat2N.inj_succ in H.
    do 2 rewrite N2Z.inj_succ in H.
    apply Zsucc_lt_reg in H.
    apply IHa.
    apply H.
Qed.

(* Theorem helper3 : forall (a b : N), (a < b)%N -> (a < b)%num. *)
(* Proof. *)
(*   induction a ; destruct b ; intros. *)
(*   - discriminate H. *)
(*   - easy. *)
(*   - discriminate H. *)
(*   - rewrite Npos_P_of_succ_nat. *)
(*     rewrite Zpos_P_of_succ_nat. *)
(*     apply Zsucc_lt_compat. *)
(*     apply IHa. *)
(*     apply ltnSE. *)
(*     apply H. *)
(* Qed. *)

Definition chFin_from_nat_mod {m : nat} (a : nat_mod (Z.of_nat m)) {H : Prelude.Positive (m)} : 'fin (m).
Proof.
  apply (Ordinal (n:=m) (m:=Z.to_nat (GZnZ.val (Z.of_nat m) a))).
  rewrite (GZnZ.inZnZ (Z.of_nat m) a).

  assert (0 < Z.of_nat m).
  {
    pose Prelude.is_positive.
    induction (m) eqn:mo.
    - discriminate i.
    - easy.
  }

  rewrite Z2Nat.inj_mod.
  - rewrite Nat2Z.id.
    pose (Nat.mod_upper_bound (Z.to_nat a) m).
    pose (@ltP (Z.to_nat a mod m) m).
    (* Set Printing All. *)
    apply (introT r), l.
    intros H2.
    rewrite H2 in H.
    inversion H.
  - apply (helper (GZnZ.val (Z.of_nat m) a) (Z.of_nat m) (GZnZ.inZnZ (Z.of_nat m) a)).
    apply H0.
    apply Z.lt_le_incl, H0.
Qed.
  
Global Coercion chFin_from_nat_mod_coerce {m : nat} (a : nat_mod (Z.of_nat m)) {H : Prelude.Positive m} : 'fin m := chFin_from_nat_mod a.

Definition chFin_from_secret_literal {m : nat} (x : int128) {H : Prelude.Positive m} : 'fin m :=
  chFin_from_nat_mod (@nat_mod_from_secret_literal (Z.of_nat m) x).

Definition chFin_pow2 m n `{Prelude.Positive m} : 'fin m :=
  chFin_from_nat_mod (@nat_mod_pow2 (Z.of_nat m) (from_uint_size n)).

(* Coercion code_from_nat_mod {m : nat} (a : nat_mod m) : raw_code (chFin m) := *)
(*   ret (chFin_from_nat_mod a). *)

Program Definition sanatize_val {n : nat} `{Prelude.Positive n} (val : nat) :=
  match (val <? n) as H_vo with
  | true => Ordinal (n:=n) (m:=val) (helper3 _ _ (proj1 (Z.ltb_lt val n) (Logic.eq_sym _)))
  | false =>
    match n with
    | O => _
    | S n' => @ord0 n'
    end
  end.

Definition chFin_add {n : nat} `{Prelude.Positive n} (a: 'fin n) (b:'fin n) : 'fin n :=
  sanatize_val (nat_of_ord a + nat_of_ord b)%nat.
Infix "+%" := chFin_add (at level 33) : hacspec_scope.

Program Definition chFin_mul {n : nat} `{Prelude.Positive n} (a: 'fin n) (b:'fin n) : 'fin n :=
  sanatize_val (nat_of_ord a * nat_of_ord b)%nat.
Infix "*%" := chFin_mul (at level 33) : hacspec_scope.

Definition chFin_sub {n : nat} `{Prelude.Positive n} (a: 'fin n) (b: 'fin n) : 'fin n := 
  sanatize_val (nat_of_ord a - nat_of_ord b)%nat.
Infix "-%" := chFin_sub (at level 33) : hacspec_scope.

Definition chFin_div {n : nat} `{Prelude.Positive n} (a: 'fin n) (b: 'fin n) : 'fin n := 
  sanatize_val (nat_of_ord a / nat_of_ord b)%nat.
Infix "/%" := chFin_div (at level 33) : hacspec_scope.

Definition chFin_zero {n : nat} := @ord0 n.

Notation "A '× B" :=
  (chProd A B : choice_type) (at level 79, left associativity) : hacspec_scope.

(* Definition usize_choiceType : nat -> choiceType := Fp_finFieldType 32. *)

(* Check GRing.Zmodule.choiceType. Check int_ZmodType. *)
(*                                  (* FinRing.Zmodule.choiceType *) *)



(* (*** FinFieldType *) *)

(* Set Warnings "-notation-overridden,-ambiguous-paths". *)
(* From mathcomp Require Import all_algebra . *)

(* (* finFieldType_from_nat_mod *) *)
(* Global Coercion finFieldType_from_nat_mod {m : nat} (a : nat_mod m) : Fp_finFieldType m := *)
(*   inZp m. *)
(* (* Proof. *) *)
(* (*   apply (inZp (Z.to_nat m)). *) *)
(* (*   (* destruct a. *) *) *)
(* (*   (* apply inZp. *) *) *)
(* (*   (* apply (Z.to_nat val). *) *) *)
(* (* Defined. *) *)

(* Definition finFieldType_from_secret_literal {m : nat} (x : int128) : Fp_finFieldType m := *)
(*   finFieldType_from_nat_mod (@nat_mod_from_secret_literal m x). *)

(* Definition finFieldType_pow2 m n : Fp_finFieldType m := *)
(*   finFieldType_from_nat_mod (@nat_mod_pow2 m n). *)

(* (* Coercion code_from_nat_mod {m : nat} (a : nat_mod m) : raw_code (Fp_finFieldType m) := *) *)
(* (*   ret (finFieldType_from_nat_mod a). *) *)

(* Definition finFieldType_add {n : nat} (a:Fp_finFieldType n) (b:Fp_finFieldType n) : Fp_finFieldType n := a + b. *)
(* Infix "+%" := finFieldType_add (at level 33) : hacspec_scope. *)

(* Definition finFieldType_mul {n : nat} (a:Fp_finFieldType n) (b:Fp_finFieldType n) : Fp_finFieldType n := a * b. *)
(* Infix "*%" := finFieldType_mul (at level 33) : hacspec_scope. *)

(* Definition finFieldType_sub {n : nat} (a:Fp_finFieldType n) (b:Fp_finFieldType n) : Fp_finFieldType n := a - b. *)
(* Infix "-%" := finFieldType_sub (at level 33) : hacspec_scope. *)

(* Definition finFieldType_div {n : nat} (a:Fp_finFieldType n) (b:Fp_finFieldType n) : Fp_finFieldType n := a / b. *)
(* Infix "/%" := finFieldType_div (at level 33) : hacspec_scope. *)

(* Definition finFieldType_zero {n : nat} := @Zp0 n. *)

(* Notation "A '× B" := *)
(*   (prod_choiceType A B : choice_type) (at level 79, left associativity) : hacspec_scope. *)

(* (* Definition usize_choiceType : nat -> choiceType := Fp_finFieldType 32. *) *)

(* (* Check GRing.Zmodule.choiceType. Check int_ZmodType. *) *)
(* (*                                  (* FinRing.Zmodule.choiceType *) *) *)
