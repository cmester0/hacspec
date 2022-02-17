Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".

From mathcomp Require Import all_ssreflect (* ssreflect *) (* seq tuple *).
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.

(*** Integers *)
From Coq Require Import ZArith List.
Import ListNotations.
(* Require Import IntTypes. *)

Require Import MachineIntegers.
From Coqprime Require GZnZ.

Declare Scope hacspec_scope.

Axiom secret : forall {WS : WORDSIZE},  (@int WS) -> (@int WS).

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

Compute @modulus WORDSIZE32.

Axiom choice_type_from_type : Type -> choice_type.
(* Coercion choice_type_from_type : Type >-> choice_type. *)

Definition modulus_pos {WS} : Positive (Z.to_nat (@modulus WS)).
Proof.
  unfold modulus.
  rewrite two_power_nat_equiv.
  replace 2%Z with (Z.of_nat 2%nat) by reflexivity.
  rewrite <- (Nat2Z.inj_pow).
  rewrite Nat2Z.id.

  induction wordsize.
  - apply (PositiveExp2 0).
  - apply Positive_prod.
    + easy.
    + apply IHn.
Defined.

Definition int_to_choice_helper {WS} (i : @int WS) : Z.to_nat (intval i) < Z.to_nat (modulus).
Proof.
  destruct i.
  destruct intrange.
  apply (introT ltP).
  assert (0 <= intval)%Z.
  {
    replace 0%Z with (Z.succ (-1)) by reflexivity.
    apply (Zlt_le_succ (-1) intval l).
  }
  assert (0 <= modulus)%Z.
  {
    apply Z.lt_le_incl.
    apply (Z.le_lt_trans 0 intval modulus H l0).
  }
  (* pose (proj1 (Z2Nat.inj_le intval modulus H1 H2)). *)
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id.
  2 : { apply H. }

  rewrite Z2Nat.id.
  2 : { apply H0. }

  apply l0.
Qed.

Definition modulus_pos2 {WS} k `{H: (Z.to_nat (@modulus WS)) = k} : Positive k.
Proof.
  subst.
  apply modulus_pos.
Defined.


Definition int_to_choice {WS} (x : @int WS) k `{H: (Z.to_nat (@modulus WS)) = k} : chFin (@mkpos k (@modulus_pos2 WS k H)).
Proof.
  subst.
  apply (Ordinal (m := Z.to_nat (intval x)) (n := Z.to_nat modulus) (int_to_choice_helper x)).
Defined.

Fixpoint hex_pow_two_helper (n : nat) (t : Hexadecimal.uint) : Hexadecimal.uint :=
  match n with
  | 0 => t (* Hexadecimal.Nil *)
  | S n' => Hexadecimal.D0 (hex_pow_two_helper n' t)
  end.

Theorem hex_pow_two_helper_succ : forall n t, hex_pow_two_helper n.+1 t = hex_pow_two_helper n (Hexadecimal.D0 t).
Proof.
  induction n.
  - reflexivity.
  - intros t.
    cbn in *.
    rewrite IHn.
    reflexivity.
Qed.

Definition hex_pow_two' (n : nat) (t : Hexadecimal.uint) : nat :=
  Init.Nat.of_num_uint
     (Number.UIntHexadecimal
        (Hexadecimal.D1 (hex_pow_two_helper n t))).

Definition hex_pow_two'_positive : forall n t, Positive (hex_pow_two' n t).
Proof.
  intros n.
  induction n.
  + unfold hex_pow_two'.
    unfold hex_pow_two_helper.
    admit.
  + intros t.
    unfold Positive.
    unfold hex_pow_two' in *.
    rewrite hex_pow_two_helper_succ.
    apply IHn.
Admitted.

Definition hex_pow_two (n : nat) : nat.
  apply (hex_pow_two' n Hexadecimal.Nil).
Qed.

Theorem hex_pow_two_positive : forall n, Positive (hex_pow_two n).
Proof.
  (* apply hex_pow_two'_positive. *)
  admit.
Admitted.

Definition modulus_8_repr : Z.to_nat (@modulus WORDSIZE8) = (hex_pow_two 2). Admitted.
Definition modulus_16_repr : Z.to_nat (@modulus WORDSIZE16) = (hex_pow_two 4). Admitted.
Definition modulus_32_repr : Z.to_nat (@modulus WORDSIZE32) = (hex_pow_two 8). Admitted.
Definition modulus_64_repr : Z.to_nat (@modulus WORDSIZE64) = (hex_pow_two 16). Admitted.
Definition modulus_128_repr : Z.to_nat (@modulus WORDSIZE128) = (hex_pow_two 32). Admitted.

Definition int8_to_choice (x : @int WORDSIZE8) : 'fin (hex_pow_two 2) := int_to_choice (WS := WORDSIZE8) x (hex_pow_two 2) (H := modulus_8_repr).
Definition int16_to_choice (x : @int WORDSIZE16) : 'fin (hex_pow_two 4) := int_to_choice (WS := WORDSIZE16) x (hex_pow_two 4) (H := modulus_16_repr).
Definition int32_to_choice (x : @int WORDSIZE32) : 'fin (hex_pow_two 8) := int_to_choice (WS := WORDSIZE32) x (hex_pow_two 8) (H := modulus_32_repr).
Definition int64_to_choice (x : @int WORDSIZE64) : 'fin (hex_pow_two 16) := int_to_choice (WS := WORDSIZE64) x (hex_pow_two 16) (H := modulus_64_repr).
Definition int128_to_choice (x : @int WORDSIZE128) : 'fin (hex_pow_two 32) := int_to_choice (WS := WORDSIZE128) x (hex_pow_two 32) (H := modulus_128_repr).


(* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
 *)

Definition uint8 := int8.
Definition uint16 := int16.
Definition uint32 := int32. (* chFin (@mkpos (hex_pow_two 8) (hex_pow_two_positive 8)). *)
Definition uint64 := int64.
Definition uint128 := int128.

Definition uint_size := int32.
Definition int_size := int32.

Axiom declassify_usize_from_uint8 : uint8 -> uint_size.

(* Represents any type that can be converted to uint_size and back *)
Class UInt_sizable (A : Type) := {
  usize : A -> uint_size;
  from_uint_size : uint_size -> A;
}.
Arguments usize {_} {_}.
Arguments from_uint_size {_} {_}.

Global Instance nat_uint_sizable : UInt_sizable nat := {
  usize n := repr (Z.of_nat n);
  from_uint_size n := Z.to_nat (unsigned n);
}.

Global Instance N_uint_sizable : UInt_sizable N := {
  usize n := repr (Z.of_N n);
  from_uint_size n := Z.to_N (unsigned n);
}.

Global Instance Z_uint_sizable : UInt_sizable Z := {
  usize n := repr n;
  from_uint_size n := unsigned n;
}.


(* Same, but for int_size *)
Class Int_sizable (A : Type) := {
  isize : A -> int_size;
  from_int_size : int_size -> A;
}.

Arguments isize {_} {_}.
Arguments from_int_size {_} {_}.

Global Instance nat_Int_sizable : Int_sizable nat := {
  isize n := repr (Z.of_nat n);
  from_int_size n := Z.to_nat (signed n);
}.

Global Instance N_Int_sizable : Int_sizable N := {
  isize n := repr (Z.of_N n);
  from_int_size n := Z.to_N (signed n);
}.

Global Instance Z_Int_sizable : Int_sizable Z := {
  isize n := repr n;
  from_int_size n := signed n;
}.


(**** Public integers *)

(* Definition pub_u8 (n:range_t U8) : u:pub_uint8{v u == n} := uint #U8 #PUB n *)
Definition pub_u8 (n : Z) : int8 := repr n.

(* Definition pub_i8 (n:N) : u:pub_int8{v u == n} := sint #S8 #PUB n *)
Definition pub_i8 (n : Z) : int8 := repr n.

(* Definition pub_u16 (n:N) : u:pub_uint16{v u == n} := uint #U16 #PUB n *)
Definition pub_u16 (n : Z) : int16 := repr n.

(* Definition pub_i16 (n:N) : u:pub_int16{v u == n} := sint #S16 #PUB n *)
Definition pub_i16 (n : Z) : int16 := repr n.

(* Definition pub_u32 (n:N) : u:pub_uint32{v u == n} := uint #U32 #PUB n *)
Definition pub_u32 (n : Z) : int32 := repr n.

(* Definition pub_i32 (n:N) : u:pub_int32{v u == n} := sint #S32 #PUB n *)
Definition pub_i32 (n : Z) : int32 := repr n.

(* Definition pub_u64 (n:N) : u:pub_uint64{v u == n} := uint #U64 #PUB n *)
Definition pub_u64 (n : Z) : int64 := repr n.

(* Definition pub_i64 (n:N) : u:pub_int64{v u == n} := sint #S64 #PUB n *)
Definition pub_i64 (n : Z) : int64 := repr n.

(* Definition pub_u128 (n:N) : u:pub_uint128{v u == n} := uint #U128 #PUB n *)
Definition pub_u128 (n : Z) : int128 := repr n.

(* Definition pub_i128 (n:N) : u:pub_int128{v u == n} := sint #S128 #PUB n *)
Definition pub_i128 (n : Z) : int128 := repr n.

(**** Operations *)

(* Should maybe use size of s instead? *)
Definition uint8_rotate_left (u: int8) (s: int8) : int8 := rol u s.

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

Definition pub_uint128_wrapping_add (x y: int128) : int128 :=
  add x y.

Definition shift_left_ `{WS : WORDSIZE} (i : @int WS) (j : uint_size) :=
  MachineIntegers.shl i (repr (from_uint_size j)).

Definition shift_right_ `{WS : WORDSIZE} (i : @int WS) (j : uint_size) :=
  MachineIntegers.shr i (repr (from_uint_size j)) .

Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope.
Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope.

(* Infix "%%" := Z.rem (at level 40, left associativity) : Z_scope. *)
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
Definition one := (@one WORDSIZE32).
Definition zero := (@zero WORDSIZE32).

Notation "A '× B" := (chProd A B : choice_type) (at level 79, left associativity) : hacspec_scope.
(* Notation "A '× B" := (chProd A B) (at level 79, left associativity) : hacspec_scope. *)
(*** Loops *)

Open Scope nat_scope.
Fixpoint foldi_
  {acc : Type}
  (fuel : nat)
  (i : uint_size)
  (f : uint_size -> acc -> acc)
  (cur : acc) : acc :=
  match fuel with
  | 0 => cur
  | S n' => foldi_ n' (add i one) f (f i cur)
  end.
Close Scope nat_scope.
Definition foldi
  {acc: Type}
  (lo: uint_size)
  (hi: uint_size) (* {lo <= hi} *)
  (f: (uint_size) -> acc -> acc) (* {i < hi} *)
  (init: acc) : acc :=
  match Z.sub (unsigned hi) (unsigned lo) with
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

Definition nseq_vec := VectorDef.t.

From extructures Require Import ord fset fmap.

Definition nseq' (A : choice_type) (len : nat) : choice_type :=  
  match len with
  | O => chUnit (* A *)
  | S n => chMap ('fin (S n)) A
  end.
    (* {fmap 'fin len -> nat} *)

(* Example nseq' (A : choice_type) (len : nat) {H : Positive len} : choice_type := *)
(*   chMap ('fin len) A (* {fmap 'fin len -> nat} *). *)

Example nseq (A : Type) (len : nat) : choice_type :=
  nseq' (choice_type_from_type A) len.


Definition seq (A : Type) := list A.

(* Automatic conversion from nseq/vector/array to seq/list *)
Global Coercion VectorDef.to_list : VectorDef.t >-> list.

Definition public_byte_seq := seq int8.
Definition byte_seq := seq int8.
Definition list_len := length.

Definition seq_index {A: Type} `{Default A} (s: seq A) (i : nat) :=
  List.nth i s default.

Definition seq_len {A: Type} (s: seq A) : N := N.of_nat (length s).

Definition seq_new_ {A: Type} (init : A) (len: nat) : seq A :=
  VectorDef.const init len.

Definition seq_new {A: Type} `{Default A} (len: nat) : seq A :=
  seq_new_ default len.

Fixpoint vec_array_from_list (A: Type) (l: list A) : nseq_vec A (length l) :=
  match l return (nseq_vec A (length l)) with
  | [] => VectorDef.nil A
  | x :: xs => VectorDef.cons A x (length xs) (vec_array_from_list A xs)
  end.    

Compute (fun f => enum_fmap f []).

Definition lift_ordinal {n : nat} (X : 'I_n) : 'I_n.+1.
Proof.
  destruct X.
  apply (Ordinal (n := n.+1) (m := m.+1)). (* n -  *)

  apply i.
  
  (* apply sub_ord_proof. *)
  
  (* apply leqW. *)
  (* apply ltnW. *)
  (* apply i. *)
  
  (* rewrite (@ltn_predK 0 m). *)
  (* - apply ltnW. *)
  (*   apply leqW. *)
  (*   apply i. *)
  (* -  *)
Defined.

Compute (nat_of_ord (lift_ordinal (Ordinal (n := 2) (m := 0) _))).

Definition mapm2' {x y} {z} `{Positive x} `{Positive y} (w : (chElement_ordType 'fin x -> chElement_ordType 'fin y)) :=
  @mapm2 (chElement_ordType 'fin x) (chElement_ordType 'fin y) z z w (fun k => k).

(* Definition mapm2'' {x y z} w :=  *)
(*   @mapm2 (@lift_ordinal x) (@lift_ordinal y) z z w (fun k => k). *)

Definition list_ind:
  forall [A : Type] (P : seq.seq A -> Prop),
    P [] ->
    (forall (a : A), P ([a])%SEQ) ->
    (forall (a b : A) (l : seq.seq A), P (b :: l) -> P (a :: b :: l)%SEQ) -> forall l : seq.seq A, P l.
Proof.
  intros.
  apply list_ind with (P:=P) (l := l).
  - apply H.
  - intros.
    destruct l0.
    + apply H0.
    + apply H1.
      apply H2.
Qed.

Axiom transform_to_choice_type : forall {T : Type} (x : T), (choice_type_from_type T).
Axiom transform_from_choice_type : forall {T : Type} (x : choice_type_from_type T), T.
Fixpoint list_to_choice {T : Type} (l : seq T) : seq (choice_type_from_type T).
Proof.
  destruct l.
  - apply nil.
  - apply cons.
    apply (transform_to_choice_type t).
    apply (list_to_choice T l).
Defined.
Fixpoint list_from_choice {T : Type} (l : seq (choice_type_from_type T)) : seq T.
Proof.
  destruct l.
  - apply nil.
  - apply cons.
    apply (transform_from_choice_type s).
    apply (list_from_choice T l).
Defined.
Theorem list_to_choice_length : forall T l, length (@list_to_choice T l) = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - cbn.
    rewrite IHl.
    reflexivity.
Defined.
Theorem list_from_choice_length : forall T l, length (@list_from_choice T l) = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - cbn.
    rewrite IHl.
    reflexivity.
Defined.


Fixpoint list_iter (n : nat) (k : nat) `{(n <= k)%nat} : seq { x : nat | (x < k)%nat }.
  destruct n.
  - apply [].
  - apply app.
    + assert (H0: (n <= k)%nat).
      {
        apply ltnSE.
        apply leqW.
        (* apply ltnW. *)
        apply H.
      }
      apply (list_iter n k H0).
    + apply cons.
      * assert (H1: (n < k)%nat).
        {
          apply ltnSE.
          (* apply leqW. *)
          (* apply ltnW. *)
          apply H.
        }
        apply (@exist nat (fun x => (x < k)%nat) n H1).
      * apply nil.
Defined.

Definition array_from_list_helper'
           (A: choice_type)
           (l: list A) : nseq' A (length l).
Proof.
  destruct l as [ | x xs ].
  - apply tt.
  - pose (l := x :: xs).
    pose (zip l (@list_iter (length l) (length l) (leqnn (length l)))).
    apply (foldr (fun (x : A * { x : nat | (x < length l)%nat }) y =>
                   setm
                     (S := A)
                     y
                     (Ordinal (n := length l) (m := proj1_sig (snd x)) (proj2_sig (snd x)))
                     (fst x))
                emptym
                (zip l (@list_iter (length l) (length l) (leqnn (length l))))).
Defined.  

Fixpoint array_from_list_helper (A: Type) (l: list A) : nseq A (length l).

  pose (@array_from_list_helper' (choice_type_from_type A) (list_to_choice l)).
  unfold nseq.
  rewrite <- list_to_choice_length.
  apply s.
Defined.  

(* automatic conversion from list to array *)
Global Coercion vec_array_from_list : list >-> nseq_vec.

Global Coercion array_from_list' (A: choice_type) (l: list A) : nseq' A (length l).
  apply (@array_from_list_helper' A).
Defined.



Global Coercion array_from_list (A: Type) (l: list A) : nseq A (length l).
Proof.
  rewrite <- (list_to_choice_length A l).  
  apply (@array_from_list' (choice_type_from_type A) (list_to_choice l)).
Defined.

(**** Array manipulation *)


Definition vec_array_new_ {A: Type} (init:A) (len: nat)  : nseq_vec A len :=
  VectorDef.const init len.
Definition array_new_' {A: choice_type} (init:A) (len: nat) : nseq' A len.
  rewrite <- (repeat_length init len).
  intros.
  apply (@array_from_list' A (repeat init len)).
Defined.
Definition array_new_ {A: Type} (init:A) (len: nat) : nseq A len.
  apply (array_new_' (transform_to_choice_type init) len).
Defined.

Open Scope nat_scope.
Definition vec_array_index {A: Type} `{Default A} {len : nat} (s: nseq_vec A len) (i: nat) : A.
Proof.
  destruct (i <? len) eqn:H1.
  (* If i < len, index normally *)
  - apply Nat.ltb_lt in H1.
    exact (VectorDef.nth s (Fin.of_nat_lt H1)).
  (* otherwise return default element *)
  - exact default.
Defined.

Definition array_index' {A: choice_type} `{Default A} {len : nat} (s: nseq' A len) (i: nat) : A.
Proof.
  destruct (i < len) eqn:H1.
  (* If i < len, index normally *)
  - (* apply Nat.ltb_lt in H1. *)
    destruct len. { inversion H1. }
    destruct (@getm _ _ s (Ordinal (n := len.+1) (m := i) H1)).
    + exact s0.
    + exact default.

  (* otherwise return default element *)
  - exact default.
Defined.

Global Instance default_choice_type {A : Type} `{Default A} : Default (choice_type_from_type A) :=
  {
    default := transform_to_choice_type default ;
  }.


Definition array_index {A: Type} `{Default A} {len : nat} (s: nseq A len) (i: nat) : A.
Proof.  
  apply transform_from_choice_type.
  apply (@array_index' (choice_type_from_type A) (default_choice_type) len s i).
Defined.


Definition vec_array_upd {A: Type} {len : nat} (s: nseq_vec A len) (i: nat) (new_v: A) : nseq_vec A len.
Proof.
  destruct (i <? len) eqn:H.
  (* If i < len, update normally *)
  - apply Nat.ltb_lt in H.
    exact (VectorDef.replace s (Fin.of_nat_lt H) new_v).
  (* otherwise return original array *)
  - exact s.
Defined.

Definition array_upd' {A: choice_type} {len : nat} (s: nseq' A len) (i: nat) (new_v: A) : nseq' A len.
Proof.
  destruct (i < len) eqn:v.
  (* If i < len, update normally *)
  - (* apply Nat.ltb_lt in H. *)
    destruct len. { inversion v. }
    apply (setm s (Ordinal (m := i) v) new_v).

    (* exact (VectorDef.replace s (Fin.of_nat_lt H) new_v). *)
  (* otherwise return original array *)
  - exact s.
Defined.


Definition array_upd {A: choice_type} {len : nat} (s: nseq A len) (i: nat) (new_v: A) : nseq A len.
Proof.
  apply (array_upd' s i (transform_to_choice_type new_v)).
Defined.


(* Definition array_upd {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) (new_v: A) : lseq A len := List.upd s i new_v. *)

(* substitutes a sequence (list) into an array (nseq), given index interval  *)
(* Axiom update_sub : forall {A len }, nseq A len -> nat -> nat -> seq A -> t A len. *)
Definition vec_update_sub {A len slen} `{Default A} (v : nseq_vec A len) (i : nat) (n : nat) (sub : nseq_vec A slen) : nseq_vec A len :=
  let fix rec x acc :=
    match x with
    | 0 => acc
    (* | 0 => array_upd acc 0 (array_index sub 0) *)
    | S x => rec x (vec_array_upd acc (i+x) (vec_array_index sub x))
    end in
  rec (n - i + 1) v.

Definition update_sub' {A : choice_type} {len slen} `{Default A} (v : nseq' A len) (i : nat) (n : nat) (sub : nseq' A slen) : nseq' A len :=
  let fix rec x acc :=
    match x with
    | 0 => acc
    (* | 0 => array_upd acc 0 (array_index sub 0) *)
    | S x => rec x (array_upd' acc (i+x) (array_index' sub x))
    end in
  rec (n - i + 1) v.

Definition update_sub {A : Type} {len slen} `{Default A} (v : nseq A len) (i : nat) (n : nat) (sub : nseq A slen) : nseq A len.
Proof.
  apply (@update_sub' (choice_type_from_type A) len slen (default_choice_type) v i n sub).
Defined.
  
(* Sanity check *)
(* Compute (to_list (update_sub [1;2;3;4;5] 0 4 (of_list [9;8;7;6;12]))). *)

Definition vec_array_from_seq
  {a: Type}
 `{Default a}
  (out_len:nat)
  (input: seq a)
  (* {H : List.length input = out_len} *)
    : nseq_vec a out_len :=
    let out := VectorDef.const default out_len in
    vec_update_sub out 0 (out_len - 1) input.
  (* VectorDef.of_list input. *)

(* Set Printing All. *)
(* Print vec_array_from_seq. *)

(* Global Instance prod_default {A : choice_type} : Default (chElement A) := { *)
(*   default := chCanonical A *)
(* }. *)

Global Coercion array_from_seq'
  {a: choice_type}
  `{Default a}
  (out_len:nat)
  (input: seq a)
  : nseq' a out_len.
Proof.
  pose (out := array_new_' default out_len).
  apply (update_sub' out 0 (out_len - 1) (@array_from_list' _ input)).
Defined.

Global Coercion array_from_seq
  {a: Type}
  `{Default a}
  (out_len:nat)
  (input: seq a)
  : nseq a out_len.
Proof.
  pose (@array_from_seq' (choice_type_from_type a) (default_choice_type) out_len (list_to_choice input) ).
  apply s.
Defined.

Global Coercion vec_array_from_seq : seq >-> nseq_vec.

Definition slice {A} (l : seq A) (i j : nat) : seq.seq A :=
  if j <=? i then [] else firstn (j-i+1) (skipn i l).

Definition vec_lseq_slice {A n} (l : nseq_vec A n) (i j : nat) : nseq_vec A _ :=
  VectorDef.of_list (slice (VectorDef.to_list l) i j).

Fixpoint array_to_list_helper {A : choice_type} `{Default A} (n k : nat) (f : nseq' A (k + n)) {struct n} : list A.
Proof.
  destruct n.
  - apply [].
  - apply cons.
    + apply (array_index' f k).
    + apply (@array_to_list_helper A _ n (S k)).
      replace (k.+1 + n) with (k + n.+1).
      apply f.
      rewrite addnS.
      rewrite addSn.
      reflexivity.
Defined.
      
Definition array_to_list' {A : choice_type} `{Default A} {n} (f : nseq' A n) : list A :=
  array_to_list_helper n 0 f.

Definition array_to_list {A : Type} `{Default A} {n} (f : nseq A n) : list A.
Proof.
  apply (list_from_choice (@array_to_list' (choice_type_from_type A) (default_choice_type) n f)).
Defined.

Global Coercion array_to_seq {A : Type} `{Default A} {n} (f : nseq A n) : seq A :=
  array_to_list f.

Definition positive_slice' {A : choice_type} `{Hd: Default A} {n} `{H: Positive n} (l : nseq' A n) (i j : nat) `{H1: i < j} `{j - i < length (array_to_list' l) - i} : Positive (length (slice (array_to_list' l) i j)).
Proof.
  unfold slice.
  rewrite (proj2 (Nat.leb_gt j i) (elimT (@ltP i j) H1)).
  rewrite firstn_length_le.
  - unfold Positive.
    pose subn_gt0.
    rewrite <- e in H1.
    apply ltn_addr.
    assumption.
  - rewrite skipn_length.
    apply lt_n_Sm_le.
    replace (length (array_to_list' l) - i)%coq_nat.+1 with (length (array_to_list' l) - i + 1) by apply addn1.
    apply (plus_lt_compat_r).
    apply (elimT ltP), H0.
Defined.

Theorem slice_length :
  forall A (l : list A) (i j : nat),
  length (slice l i j) =
    if j <=? i then @length A ([]) else length (firstn (j - i + 1) (skipn i l)).
Proof.
  intros.
  unfold slice.
  destruct (j <=? i).
  - reflexivity.
  - reflexivity.
Qed.      

Definition positive_slice {A : Type} `{Hd: Default A} {n} `{H: Positive n} (l : nseq A n) (i j : nat) `{H1: i < j} `{j - i < length (array_to_list l) - i} : Positive (length (slice (array_to_list l) i j)).
  
  unfold array_to_list.
  rewrite slice_length.
  rewrite firstn_length.
  rewrite skipn_length.
  rewrite list_from_choice_length.
  rewrite <- skipn_length.
  rewrite <- firstn_length.
  rewrite <- (slice_length (choice_type_from_type A)).
  apply (@positive_slice' (choice_type_from_type A) _ n H l i j H1).

  unfold array_to_list in H0.
  rewrite list_from_choice_length in H0.
  apply H0.
Defined.  

Definition lseq_slice' {A : choice_type} `{Default A} {n} (l : nseq' A n) (i j : nat) : @nseq' A (length (slice (array_to_list' l) i j)) :=
  array_from_list' _ (slice (array_to_list' l) i j).

Definition lseq_slice {A : Type} `{Default A} {n} (l : nseq A n) (i j : nat) : @nseq A (length (slice (array_to_list l) i j)) :=
  array_from_list _ (slice (array_to_list l) i j).

(* TODO Continue from here *)

Definition vec_array_from_slice
  {a: Type}
 `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start: nat)
  (slice_len: nat)
    : nseq_vec a out_len :=
    let out := VectorDef.const default_value out_len in
    vec_update_sub out 0 slice_len (vec_lseq_slice (VectorDef.of_list input) start (start + slice_len)).

Definition array_from_slice'
  {a: choice_type}
 `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start: nat)
  (* `{length input = out_len}   *)
  (slice_len: nat)
  (* `{0 < slice_len} *)
  : nseq' a out_len.
  pose (out := array_new_' default out_len).
  pose (@array_from_seq' _ _ out_len input (* H1 *)).

  (* assert (K : start < start + slice_len). *)
  (* { *)
  (*   rewrite <- ltn_subLR by easy. *)
  (*   replace (start - start) with 0 by (rewrite subnn; reflexivity). *)
  (*   assumption. *)
  (* } *)
    
  (* assert (K' : start + slice_len - start < length (array_to_list' s) - start). *)
  (* { *)
  (*   admit. *)
  (* } *)


  (* pose (@lseq_slice' a _ _ _ s start (start + slice_len) K K'). *)
  
  (* apply (update_sub' out 0 slice_len s0). *)
Admitted.
    (* let out := array_new_' default out_len in *)
    (* update_sub' out 0 slice_len (lseq_slice (VectorDef.of_list input) start (start + slice_len)). *)

Definition array_from_slice
  {a: Type}
 `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start: nat)
  (* `{length input = out_len} *)
  (slice_len: nat)
  (* `{0 < slice_len} *)
  : nseq a out_len.
Proof.
  pose (@array_from_seq'
          (choice_type_from_type a)
          (default_choice_type)
          out_len
          (list_to_choice input) ).
  apply s.
Defined.

Definition vec_array_slice
  {a: Type}
 `{Default a}
  (input: seq a)
  (start: nat)
  (slice_len: nat)
    : nseq_vec a _ :=
  let out := slice input start (start + slice_len) in
  vec_array_from_seq slice_len out.


Definition vec_array_from_slice_range
  {a: Type}
 `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start_fin: (uint_size * uint_size))
    : nseq_vec a out_len :=
    let out := vec_array_new_ default_value out_len in
    let (start, fin) := start_fin in
    vec_update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) (VectorDef.of_list (slice input (from_uint_size start) (from_uint_size fin))).


Definition vec_array_slice_range
  {a: Type}
  {len : nat}
  (input: nseq_vec a len)
  (start_fin:(uint_size * uint_size))
    : seq a :=
  VectorDef.to_list (vec_lseq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin))).

Definition array_slice_range'
  {a: choice_type}
 `{Default a}
  {len : nat}
  (input: nseq' a len)
  (start_fin:(uint_size * uint_size))
    : seq a :=
  array_to_list' (lseq_slice' input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin))).

Definition array_slice_range
  {a: Type}
 `{Default a}
  {len : nat}
  (input: nseq a len)
  (start_fin:(uint_size * uint_size))
    : seq a :=
  array_to_list (lseq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin))).

Definition vec_array_update
  {a: Type}
 `{Default a}
  {len: nat}
  (s: nseq_vec a len)
  (start : nat)
  (start_s: seq a)
    : nseq_vec a len :=
    vec_update_sub s start (length start_s) (VectorDef.of_list start_s).

Definition vec_array_update_start
  {a: Type}
 `{Default a}
  {len: nat}
  (s: nseq_vec a len)
  (start_s: seq a)
    : nseq_vec a len :=
    vec_update_sub s 0 (length start_s) (VectorDef.of_list start_s).


Definition vec_array_len  {a: Type} {len: nat} (s: nseq_vec a len) := len.
(* May also come up as 'length' instead of 'len' *)
Definition vec_array_length  {a: Type} {len: nat} (s: nseq_vec a len) := len.
Definition array_length'  {a: choice_type} {len: nat} (s: nseq' a len) := len.
Definition array_length  {a: Type} {len: nat} (s: nseq a len) := len.

(**** Seq manipulation *)

Definition vec_seq_slice
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (len: nat)
    : nseq_vec a _ :=
  vec_array_from_seq len (slice s start (start + len)).

Definition vec_seq_slice_range
  {a: Type}
 `{Default a}
  (input: seq a)
  (start_fin:(uint_size * uint_size))
    : nseq_vec a _ :=
  vec_seq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin)).

(* updating a subsequence in a sequence *)
Definition vec_seq_update
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (input: seq a)
  : seq a :=
  VectorDef.to_list (vec_update_sub (VectorDef.of_list s) start (length input) (VectorDef.of_list input)).

(* updating only a single value in a sequence*)
Definition vec_seq_upd
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (v: a)
    : seq a :=
  VectorDef.to_list (vec_update_sub (VectorDef.of_list s) start 1 (VectorDef.of_list [v])).

Definition sub {a} (s : list a) start n :=
  slice s start (start + n).

Definition vec_seq_update_start
  {a: Type}
 `{Default a}
  (s: seq a)
  (start_s: seq a)
    : seq a :=
   VectorDef.to_list  (vec_update_sub (VectorDef.of_list s) 0 (length start_s) (VectorDef.of_list start_s)).

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

Definition vec_array_update_slice
  {a : Type}
 `{Default a}
  {l : nat}
  (out: nseq_vec a l)
  (start_out: nat)
  (input: seq a)
  (start_in: nat)
  (len: nat)
    : nseq_vec a (length out)
  :=
  vec_update_sub (VectorDef.of_list out) start_out len
    (VectorDef.of_list (sub input start_in len)).

Definition vec_seq_update_slice
  {a : Type}
 `{Default a}
  (out: seq a)
  (start_out: nat)
  (input: seq a)
  (start_in: nat)
  (len: nat)
    : nseq_vec a (length out)
  :=
  vec_update_sub (VectorDef.of_list out) start_out len
    (VectorDef.of_list (sub input start_in len)).

Definition seq_concat
  {a : Type}
  (s1 :seq a)
  (s2: seq a)
  : seq a :=
  (* VectorDef.of_list *) (s1 ++ s2).

Definition seq_push
  {a : Type}
  (s1 :seq a)
  (s2: a)
  : seq a :=
  (* VectorDef.of_list *) (s1 ++ [s2]).

Definition vec_seq_from_slice_range
  {a: Type}
 `{Default a}
  (input: seq a)
  (start_fin: (uint_size * uint_size))
  : seq a :=
  let out := vec_array_new_ (default) (length input) in
  let (start, fin) := start_fin in
    VectorDef.to_list (vec_update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) (VectorDef.of_list (slice input (from_uint_size start) (from_uint_size fin)))).

Definition seq_from_seq {A} (l : seq A) := l.


(**** Chunking *)

Definition seq_num_chunks {a: Type} (s: seq a) (chunk_len: nat) : nat :=
  ((length s) + chunk_len - 1) / chunk_len.

Definition seq_chunk_len
  {a: Type}
  (s: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
    : nat :=
  let idx_start := chunk_len * chunk_num in
  if (length s) <? idx_start + chunk_len then
    (length s) - idx_start
  else
    chunk_len.

(* Definition seq_chunk_same_len_same_chunk_len
  {a: Type}
  (s1 s2: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
  : Lemma
    (requires (LSeq.length s1 := LSeq.length s2 /\ chunk_len * chunk_num <= Seq.length s1))
    (ensures (seq_chunk_len s1 chunk_len chunk_lseq. Admitted. *)

Definition seq_get_chunk
  {a: Type}
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

Definition vec_seq_set_chunk
  {a: Type}
 `{Default a}
  (s: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
  (chunk: seq a ) : seq a :=
 let idx_start := chunk_len * chunk_num in
 let out_len := seq_chunk_len s chunk_len chunk_num in
  VectorDef.to_list (vec_update_sub (VectorDef.of_list s) idx_start out_len (VectorDef.of_list chunk)).


Definition seq_num_exact_chunks {a} (l : seq a) (chunk_size : uint_size) : uint_size :=
  divs (repr (Z.of_nat (length l))) chunk_size.

(* Until #84 is fixed this returns an empty sequence if not enough *)
Definition seq_get_exact_chunk {a} (l : seq a) (chunk_size chunk_num: uint_size) : seq a :=
  let '(len, chunk) := seq_get_chunk l (from_uint_size chunk_size) (from_uint_size chunk_num) in
  if eq len chunk_size then [] else chunk.

Definition vec_seq_set_exact_chunk {a} `{H : Default a} := @vec_seq_set_chunk a H.

Definition seq_get_remainder_chunk : forall {a}, seq a -> uint_size -> seq a :=
  fun _ l chunk_size =>
    let chunks := seq_num_chunks l (from_uint_size chunk_size) in
    let last_chunk := if 0 <? chunks then
      chunks - 1
    else 0 in
    let (len, chunk) := seq_get_chunk l (from_uint_size chunk_size) last_chunk in
    if eq len chunk_size then
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

(* takes two nseq's and joins them using a function op : a -> a -> a *)
Definition vec_array_join_map
  {a: Type}
 `{Default a}
  {len: nat}
  (op: a -> a -> a)
  (s1: nseq_vec a len)
  (s2 : nseq_vec a len) :=
  let out := s1 in
  foldi (usize 0) (usize len) (fun i out =>
    let i := from_uint_size i in
    vec_array_upd out i (op (vec_array_index s1 i) (vec_array_index s2 i))
  ) out.

Infix "vec_array_xor" := (vec_array_join_map xor) (at level 33) : hacspec_scope.
Infix "vec_array_add" := (vec_array_join_map add) (at level 33) : hacspec_scope.
Infix "vec_array_minus" := (vec_array_join_map sub) (at level 33) : hacspec_scope.
Infix "vec_array_mul" := (vec_array_join_map mul) (at level 33) : hacspec_scope.
Infix "vec_array_div" := (vec_array_join_map divs) (at level 33) : hacspec_scope.
Infix "vec_array_or" := (vec_array_join_map or) (at level 33) : hacspec_scope.
Infix "vec_array_and" := (vec_array_join_map and) (at level 33) : hacspec_scope.

Definition vec_array_eq_
  {a: Type}
  {len: nat}
  (eq: a -> a -> bool)
  (s1: nseq_vec a len)
  (s2 : nseq_vec a len)
    : bool := Vector.eqb _ eq s1 s2.

Infix "vec_array_eq" := (vec_array_eq_ eq) (at level 33) : hacspec_scope.
Infix "vec_array_neq" := (fun s1 s2 => negb (vec_array_eq_ eq s1 s2)) (at level 33) : hacspec_scope.


(**** Integers to arrays *)
Axiom vec_uint32_to_le_bytes : int32 -> nseq_vec int8 4.
(* Definition uint32_to_le_bytes (x: uint32) : nseq uint8 4 :=
  LBSeq.uint_to_bytes_le x. *)

Axiom vec_uint32_to_be_bytes : int32 -> nseq_vec int8 4.
(* Definition uint32_to_be_bytes (x: uint32) : nseq uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom vec_uint32_from_le_bytes : nseq_vec int8 4 -> int32.
(* Definition uint32_from_le_bytes (s: nseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom vec_uint32_from_be_bytes : nseq_vec int8 4 -> int32.
(* Definition uint32_from_be_bytes (s: nseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom vec_uint64_to_le_bytes : int64 -> nseq_vec int8 8.
(* Definition uint64_to_le_bytes (x: uint64) : nseq uint8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom vec_uint64_to_be_bytes : int64 -> nseq_vec int8 8.
(* Definition uint64_to_be_bytes (x: uint64) : nseq uint8 8 :=
  LBSeq.uint_to_bytes_be x *)

Axiom vec_uint64_from_le_bytes : nseq_vec int8 8 -> int64.
(* Definition uint64_from_le_bytes (s: nseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom vec_uint64_from_be_bytes : nseq_vec int8 8 -> int64.
(* Definition uint64_from_be_bytes (s: nseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_be s *)

Axiom vec_uint128_to_le_bytes : int128 -> nseq_vec int8 16.
Axiom uint128_to_le_bytes : int128 -> nseq int8 16.

Axiom vec_uint128_to_be_bytes : int128 -> nseq_vec int8 16.
(* Definition uint128_to_be_bytes (x: uint128) : nseq uint8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom vec_uint128_from_le_bytes : nseq_vec int8 16 -> int128.
Axiom uint128_from_le_bytes : nseq int8 16 -> int128.

Axiom vec_uint128_from_be_bytes : nseq_vec int8 16 -> int128.
(* Definition uint128_from_be_bytes (s: nseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_be s *)

Axiom vec_u32_to_le_bytes : int32 -> nseq_vec int8 4.
(* Definition u32_to_le_bytes (x: pub_uint32) : nseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_le x *)

Axiom vec_u32_to_be_bytes : int32 -> nseq_vec int8 4.
(* Definition u32_to_be_bytes (x: pub_uint32) : nseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom vec_u32_from_le_bytes : nseq_vec int8 4 -> int32.
(* Definition u32_from_le_bytes (s: nseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom vec_u32_from_be_bytes : nseq_vec int8 4 -> int32.
(* Definition u32_from_be_bytes (s: nseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom vec_u64_to_le_bytes : int64 -> nseq_vec int8 8.
(* Definition u64_to_le_bytes (x: int64) : nseq int8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom vec_u64_from_le_bytes : nseq_vec int8 8 -> int64.
(* Definition u64_from_le_bytes (s: nseq int8 8) : int64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom vec_u128_to_le_bytes : int128 -> nseq_vec int8 16.
(* Definition u128_to_le_bytes (x: int128) : nseq int8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom vec_u128_to_be_bytes : int128 -> nseq_vec int8 16.
(* Definition u128_to_be_bytes (x: int128) : nseq int8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom vec_u128_from_le_bytes : nseq_vec int8 16 -> int128.
(* Definition u128_from_le_bytes (input: nseq int8 16) : int128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom vec_u128_from_be_bytes : nseq_vec int8 16 -> int128.
(* Definition u128_from_be_bytes (s: nseq int8 16) : pub_uint128 :=
  LBSeq.uint_from_bytes_be s *)


(*** Nats *)

Definition nat_mod (p : Z) : Set := GZnZ.znz p.

(* {H : Z.gt (Z.of_nat p) 0} *)
Definition chFin_from_nat_mod {p} {H : Positive p} : nat_mod (Z.of_nat p) -> 'I_(p).
Proof.
  intro a.
  destruct a.
  apply (Ordinal (m := Z.to_nat val)).

  assert (H2: Z.gt (Z.of_nat p) 0).
  {
    replace 0%Z with (Z.of_nat 0%nat) by reflexivity.
    apply inj_gt, (elimT ltP), H.
  }

  destruct (@Z_mod_lt val (Z.of_nat p) H2).

  rewrite <- inZnZ in H0.
  rewrite <- inZnZ in H1.

  apply (introT ltP).
  apply (Nat2Z.inj_lt).
  rewrite Z2Nat.id ; assumption.
Qed.

Definition nat_mod_from_chFin {p} {H : Positive p} : 'fin p -> nat_mod (Z.of_nat p).
Proof.
  intros.
  destruct X.
  apply (GZnZ.mkznz (Z.of_nat p) (Z.of_nat m)).
  symmetry.
  apply Z.mod_small.
  split.
  destruct m ; easy.

  apply (Z2Nat.inj_lt).
  - destruct m ; easy.
  - destruct p ; easy.
  - apply (elimT ltP).
    rewrite Nat2Z.id.
    rewrite Nat2Z.id.
    apply i.
Qed.


Definition nat_mod_equal {p} (a b : nat_mod p) : bool :=
  Z.eqb (GZnZ.val p a) (GZnZ.val p b).

Definition chFin_equal {p} {H : Positive p} (a b : 'fin p) : bool :=
  nat_mod_equal (nat_mod_from_chFin a) (nat_mod_from_chFin b).

Definition nat_mod_zero {p} : nat_mod p := GZnZ.zero p.
Definition nat_mod_one {p} : nat_mod p := GZnZ.one p.
Definition nat_mod_two {p} : nat_mod p := GZnZ.mkznz p _ (GZnZ.modz p 2).

Definition chFin_zero {p} {H : Positive p} : 'fin p := chFin_from_nat_mod nat_mod_zero.
Definition chFin_one {p} {H : Positive p} : 'fin p := chFin_from_nat_mod nat_mod_one.
Definition chFin_two {p} {H : Positive p} : 'fin p := chFin_from_nat_mod nat_mod_two.

(* convenience coercions from nat_mod to Z and N *)
(* Coercion Z.of_N : N >-> Z. *)

Definition nat_mod_add {n : Z} (a b : nat_mod n) : nat_mod n := GZnZ.add n a b.
Definition chFin_add {n}  {H : Positive n} (a b : 'fin n) : 'fin n :=
  chFin_from_nat_mod (nat_mod_add (nat_mod_from_chFin a) (nat_mod_from_chFin b)).

(* Infix "+%" := nat_mod_add (at level 33) : hacspec_scope. *)
Infix "+%" := chFin_add (at level 33) : hacspec_scope.

Definition nat_mod_mul {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.mul n a b.
Definition chFin_mul {n}  {H : Positive n} (a b : 'fin n) : 'fin n :=
  chFin_from_nat_mod (nat_mod_mul (nat_mod_from_chFin a) (nat_mod_from_chFin b)).

(* Infix "*%" := nat_mod_mul (at level 33) : hacspec_scope. *)
Infix "*%" := chFin_mul (at level 33) : hacspec_scope.

Definition nat_mod_sub {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.sub n a b.
Definition chFin_sub {n}  {H : Positive n} (a b : 'fin n) : 'fin n :=
  chFin_from_nat_mod (nat_mod_sub (nat_mod_from_chFin a) (nat_mod_from_chFin b)).

(* Infix "-%" := nat_mod_sub (at level 33) : hacspec_scope. *)
Infix "-%" := chFin_sub (at level 33) : hacspec_scope.

Definition nat_mod_div {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.div n a b.
Definition chFin_div {n}  {H : Positive n} (a b : 'fin n) : 'fin n :=
  chFin_from_nat_mod (nat_mod_div (nat_mod_from_chFin a) (nat_mod_from_chFin b)).

(* Infix "/%" := nat_mod_div (at level 33) : hacspec_scope. *)
Infix "/%" := chFin_div (at level 33) : hacspec_scope.

(* A % B = (a * B + r) *)

Definition nat_mod_neg {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.opp n a.
Definition chFin_neg {n}  {H : Positive n} (a : 'fin n) : 'fin n :=
  chFin_from_nat_mod (nat_mod_neg (nat_mod_from_chFin a)).

Definition nat_mod_inv {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.inv n a.
Definition chFin_inv {n}  {H : Positive n} (a : 'fin n) : 'fin n :=
  chFin_from_nat_mod (nat_mod_inv (nat_mod_from_chFin a)).

Definition nat_mod_exp_def {p : Z} (a:nat_mod p) (n : nat) : nat_mod p :=
  let fix exp_ (e : nat_mod p) (n : nat) :=
    match n with
    | 0%nat => nat_mod_one
    | S n => nat_mod_mul a (exp_ a n)
    end in
  exp_ a n.
Definition chFin_exp_def {p} {H : Positive p} (a: 'fin p) (n : nat) : 'fin p :=
  chFin_from_nat_mod (nat_mod_exp_def (nat_mod_from_chFin a) n).


Definition nat_mod_exp {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow_self {p} a n := @nat_mod_exp_def p a (Z.to_nat (from_uint_size n)).

Definition chFin_exp {WS} {p} {H : Positive p} (a: 'fin p) n : 'fin p :=
  chFin_from_nat_mod (@nat_mod_exp WS (Z.of_nat p) (nat_mod_from_chFin a) n).
Definition chFin_pow {WS} {p} {H : Positive p} (a: 'fin p) n : 'fin p :=
  chFin_from_nat_mod (@nat_mod_pow WS (Z.of_nat p) (nat_mod_from_chFin a) n).
Definition chFin_pow_self {p} {H : Positive p} (a: 'fin p) n : 'fin p :=
  chFin_from_nat_mod (nat_mod_pow_self (nat_mod_from_chFin a) n).


Close Scope nat_scope.
Open Scope Z_scope.

(* We assume x < m *)
Definition nat_mod_from_secret_literal {m : Z} (x:int128) : nat_mod m.
Proof.
  unfold nat_mod.
  (* since we assume x < m, it will be true that (unsigned x) = (unsigned x) mod m  *)
  remember ((unsigned x) mod m) as zmodm.
  apply (GZnZ.mkznz m zmodm).
  rewrite Heqzmodm.
  rewrite Zmod_mod.
  reflexivity.
Defined.
Definition chFin_from_secret_literal {m} {H : Positive m} (x: int128) : 'fin m :=
  chFin_from_nat_mod (nat_mod_from_secret_literal x).

Definition nat_mod_from_literal (m : Z) (x:int128) : nat_mod m := nat_mod_from_secret_literal x.
Definition chFin_from_literal (m : nat) {H : Positive m} (x: int128) : 'fin m :=
  chFin_from_nat_mod (nat_mod_from_literal (Z.of_nat m) x).

Axiom nat_mod_to_byte_seq_le : forall {n : Z}, nat_mod n -> seq int8.
Axiom nat_mod_to_byte_seq_be : forall {n : Z}, nat_mod n -> seq int8.
Axiom nat_mod_to_public_byte_seq_le : forall (n : Z), nat_mod n -> seq int8.
Axiom nat_mod_to_public_byte_seq_be : forall (n : Z), nat_mod n -> seq int8.

Axiom chFin_to_byte_seq_le : forall {n : nat} {H : Positive n}, 'fin n -> seq int8.
Axiom chFin_to_byte_seq_be : forall {n : nat} {H : Positive n}, 'fin n -> seq int8.
Axiom chFin_to_public_byte_seq_le : forall (n : nat) {H : Positive n}, 'fin n -> seq int8.
Axiom chFin_to_public_byte_seq_be : forall (n : nat) {H : Positive n}, 'fin n -> seq int8.

Definition nat_mod_bit {n : Z} (a : nat_mod n) (i : uint_size) :=
  Z.testbit (GZnZ.val n a) (from_uint_size i).
Definition chFin_bit {n} {H : Positive n} (a : 'fin n) (i : uint_size) :=
  nat_mod_bit (nat_mod_from_chFin a) i.

(* Alias for nat_mod_bit *)
Definition nat_get_mod_bit {p} (a : nat_mod p) := nat_mod_bit a.
Definition nat_mod_get_bit {p} (a : nat_mod p) n :=
  if (nat_mod_bit a n)
  then @nat_mod_one p
  else @nat_mod_zero p.

Definition chFin_get_bit {n} {H : Positive n} (a : 'fin n) (i : uint_size) :=
  nat_mod_get_bit (nat_mod_from_chFin a) i.

(*
Definition nat_mod_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_mod_to_bytes_le len n'*)

(* Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n' *)

Axiom vec_array_declassify_eq : forall  {A l}, nseq_vec A l -> nseq_vec A l -> bool.
Axiom vec_array_to_le_uint32s : forall {A l}, nseq_vec A l -> nseq_vec uint32 l.
Axiom vec_array_to_be_uint32s : forall {l}, nseq_vec uint8 l -> nseq_vec uint32 (l/4).
Axiom vec_array_to_le_bytes : forall {A l}, nseq_vec A l -> seq uint8.
Axiom vec_array_to_be_bytes : forall {A l}, nseq_vec A l -> seq uint8.
Axiom nat_mod_from_byte_seq_le : forall  {A n}, seq A -> nat_mod n.
(* Axiom most_significant_bit : forall {m}, nat_mod m -> uint_size -> uint_size. *)

Axiom chFin_from_byte_seq_le : forall  {A n} {H : Positive n}, seq A -> 'fin n.
Axiom most_significant_bit : forall {m} {H : Positive m}, 'fin m -> uint_size -> uint_size.


(* We assume 2^x < m *)
Definition nat_mod_pow2 (m : Z) (x : N) : nat_mod m.
Proof.
  remember (Z.pow 2 (Z.of_N x) mod m) as y.
  apply (GZnZ.mkznz m y).
  rewrite Heqy.
  rewrite Zmod_mod.
  reflexivity.
Defined.

Definition chFin_pow2 (m : nat) {H : Positive m} (x : N) : 'fin m :=
  chFin_from_nat_mod (nat_mod_pow2 (Z.of_nat m) x).
(* Definition chFin_pow2 (m : Z) {H : Positive (Z.to_nat m)} (x : N) : 'fin (Z.to_nat m). *)
(*   pose (nat_mod_pow2 m x). *)
(*   apply chFin_from_nat_mod. *)
(*   cbn. *)
(*   rewrite Z2Nat.id. *)
(*   apply n. *)

(*   unfold Positive in H. *)
(*   destruct m ; easy. *)
(* Defined. *)

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
    cast '(a, c) := (cast _ a, cast _ c)
  }.

  Global Instance cast_option {A B} `{Cast A B} : Cast (option A) (option B) := {
    cast a := match a with Some a => Some (cast _ a) | None => None end
  }.

  Global Instance cast_option_b {A B} `{Cast A B} : Cast A (option B) := {
    cast a := Some (cast _ a)
  }.

  (* Global Instances for common types *)

  Global Instance cast_nat_to_N : Cast nat N := {
    cast := N.of_nat
  }.

  Global Instance cast_N_to_Z : Cast N Z := {
    cast := Z.of_N
  }.

  Global Instance cast_Z_to_int {WORDSIZE} : Cast Z (@int WORDSIZE) := {
    cast n := repr n
  }.

  Global Instance cast_natmod_to_Z {p} : Cast (nat_mod p) Z := {
    cast n := GZnZ.val p n
  }.

  (* Note: should be aware of typeclass resolution with int/uint since they are just aliases of each other currently *)
  Global Instance cast_int8_to_uint32 : Cast int8 uint32 := {
    cast n := (* int32_to_choice *) (repr (unsigned n))
  }.
  Global Instance cast_int8_to_int32 : Cast int8 int32 := {
    cast n := repr (signed n)
  }.

  Global Instance cast_uint8_to_uint32 : Cast uint8 uint32 := {
    cast n := (* int32_to_choice *) (repr (unsigned n))
  }.

  Global Instance cast_int_to_nat `{WORDSIZE} : Cast int nat := {
    cast n := Z.to_nat (signed n)
  }.

  Close Scope hacspec_scope.
End Casting.


Global Arguments pair {_ _} & _ _.
(* Global Arguments id {_} & _. *) (* TODO *)
Section Coercions.
  (* First, in order to have automatic coercions for tuples, we add bidirectionality hints: *)

  (* Integer coercions *)
  (* We have nat >-> N >-> Z >-> int/int32 *)
  (* and uint >-> Z *)
  (* and N >-> nat *)

  Global Coercion N.to_nat : N >-> nat.
  Global Coercion Z.of_N : N >-> Z.

  Global Coercion repr : Z >-> int.

  Definition Z_to_int `{WORDSIZE} (n : Z) : int := repr n.
  Global Coercion  Z_to_int : Z >-> int.

  Definition Z_to_uint_size (n : Z) : uint_size := repr n.
  Global Coercion Z_to_uint_size : Z >-> uint_size.
  Definition Z_to_int_size (n : Z) : int_size := repr n.
  Global Coercion Z_to_int_size : Z >-> int_size.

  Definition N_to_int `{WORDSIZE} (n : N) : int := repr (Z.of_N n).
  Global Coercion N.of_nat : nat >-> N.
  Global Coercion N_to_int : N >-> int.
  Definition N_to_uint_size (n : Z) : uint_size := repr n.
  Global Coercion N_to_uint_size : Z >-> uint_size.
  Definition nat_to_int `{WORDSIZE} (n : nat) := repr (Z.of_nat n).
  Global Coercion nat_to_int : nat >-> int.

  Definition uint_size_to_nat (n : uint_size) : nat := from_uint_size n.
  Global Coercion uint_size_to_nat : uint_size >-> nat.

  Definition uint_size_to_Z (n : uint_size) : Z := from_uint_size n.
  Global Coercion uint_size_to_Z : uint_size >-> Z.

  Definition uint32_to_nat (n : uint32) : nat := unsigned n.
  Global Coercion uint32_to_nat : uint32 >-> nat.


  Global Coercion GZnZ.val : GZnZ.znz >-> Z.

  Definition int8_to_nat (n : int8) : nat := unsigned n.
  Global Coercion int8_to_nat : int8 >-> nat.
  Definition int16_to_nat (n : int16) : nat := unsigned n.
  Global Coercion int16_to_nat : int16 >-> nat.
  Definition int32_to_nat (n : int32) : nat := unsigned n.
  Global Coercion int32_to_nat : int32 >-> nat.
  Definition int64_to_nat (n : int64) : nat := unsigned n.
  Global Coercion int64_to_nat : int64 >-> nat.
  Definition int128_to_nat (n : int128) : nat := unsigned n.
  Global Coercion int128_to_nat : int128 >-> nat.

  (* coercions int8 >-> int16 >-> ... int128 *)

  Definition int8_to_int16 (n : int8) : int16 := repr n.
  Global Coercion int8_to_int16 : int8 >-> int16.

  Definition int8_to_int32 (n : int8) : int32 := repr n.
  Global Coercion int8_to_int32 : int8 >-> int32.

  Definition int16_to_int32 (n : int16) : int32 := repr n.
  Global Coercion int16_to_int32 : int16 >-> int32.

  Definition int32_to_int64 (n : int32) : int64 := repr n.
  Global Coercion int32_to_int64 : int32 >-> int64.

  Definition int64_to_int128 (n : int64) : int128 := repr n.
  Global Coercion int64_to_int128 : int64 >-> int128.

  Definition int32_to_int128 (n : int32) : int128 := repr n.
  Global Coercion int32_to_int128 : int32 >-> int128.

  Definition uint_size_to_int64 (n : uint_size) : int64 := repr n.
  Global Coercion uint_size_to_int64 : uint_size >-> int64.


  (* coercions into nat_mod *)
  Definition Z_in_nat_mod {m : Z} (x:Z) : nat_mod m.
  Proof.
    unfold nat_mod.
    remember ((x) mod m) as zmodm.
    apply (GZnZ.mkznz m zmodm).
    rewrite Heqzmodm.
    rewrite Zmod_mod.
    reflexivity.
  Defined.
  (* Global Coercion Z_in_nat_mod : Z >-> nat_mod.  *)

  Definition int_in_nat_mod {m : Z} `{WORDSIZE} (x:int) : nat_mod m.
  Proof.
    unfold nat_mod.
    (* since we assume x < m, it will be true that (unsigned x) = (unsigned x) mod m  *)
    remember ((unsigned x) mod m) as zmodm.
    apply (GZnZ.mkznz m zmodm).
    rewrite Heqzmodm.
    rewrite Zmod_mod.
    reflexivity.
    Show Proof.
  Defined.
  Global Coercion int_in_nat_mod : int >-> nat_mod.

  Definition uint_size_in_nat_mod (n : uint_size) : nat_mod 16 := int_in_nat_mod n.
  Global Coercion uint_size_in_nat_mod : uint_size >-> nat_mod.

End Coercions.


(*** Casting *)

Definition uint128_from_usize (n : uint_size) : int128 := repr n.
Definition uint64_from_usize (n : uint_size) : int64 := repr n.
Definition uint32_from_usize (n : uint_size) : int32 := repr n.
Definition uint16_from_usize (n : uint_size) : int16 := repr n.
Definition uint8_from_usize (n : uint_size) : int8 := repr n.

Definition uint128_from_uint8 (n : int8) : int128 := repr n.
Definition uint64_from_uint8 (n : int8) : int64 := repr n.
Definition uint32_from_uint8 (n : int8) : int32 := repr n.
Definition uint16_from_uint8 (n : int8) : int16 := repr n.
Definition usize_from_uint8 (n : int8) : uint_size := repr n.

Definition uint128_from_uint16 (n : int16) : int128 := repr n.
Definition uint64_from_uint16 (n : int16) : int64 := repr n.
Definition uint32_from_uint16 (n : int16) : int32 := repr n.
Definition uint8_from_uint16 (n : int16) : int8 := repr n.
Definition usize_from_uint16 (n : int16) : uint_size := repr n.

Definition uint128_from_uint32 (n : int32) : int128 := repr n.
Definition uint64_from_uint32 (n : int32) : int64 := repr n.
Definition uint16_from_uint32 (n : int32) : int16 := repr n.
Definition uint8_from_uint32 (n : int32) : int8 := repr n.
Definition usize_from_uint32 (n : int32) : uint_size := repr n.

Definition uint128_from_uint64 (n : int64) : int128 := repr n.
Definition uint32_from_uint64 (n : int64) : int32 := repr n.
Definition uint16_from_uint64 (n : int64) : int16 := repr n.
Definition uint8_from_uint64 (n : int64) : int8 := repr n.
Definition usize_from_uint64 (n : int64) : uint_size := repr n.

Definition uint64_from_uint128 (n : int128) : int64 := repr n.
Definition uint32_from_uint128 (n : int128) : int32 := repr n.
Definition uint16_from_uint128 (n : int128) : int16 := repr n.
Definition uint8_from_uint128 (n : int128) : int8 := repr n.
Definition usize_from_uint128 (n : int128) : uint_size := repr n.


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

Definition nat_mod_val (p : Z) (a : nat_mod p) : Z := GZnZ.val p a.

Theorem nat_mod_eqb_spec : forall {p} (a b : nat_mod p), Z.eqb (nat_mod_val p a) (nat_mod_val p b) = true <-> a = b.
Proof.
  split ; intros.
  - apply Z.eqb_eq in H.
    destruct a, b.
    cbn in H.
    apply (GZnZ.zirr p val val0 inZnZ inZnZ0 H).
  - subst.
    apply Z.eqb_eq.
    reflexivity.
Qed.

Global Instance nat_mod_eqdec {p} : EqDec (nat_mod p) := {
  eqb a b := Z.eqb (nat_mod_val p a) (nat_mod_val p b);
  eqb_leibniz := nat_mod_eqb_spec;
}.

Global Instance nat_mod_comparable `{p : Z} : Comparable (nat_mod p) := {
  ltb a b := Z.ltb (nat_mod_val p a) (nat_mod_val p b);
  leb a b := if Zeq_bool a b then true else Z.ltb (nat_mod_val p a) (nat_mod_val p b) ;
  gtb a b := Z.ltb (nat_mod_val p b) (nat_mod_val p a);
  geb a b := if Zeq_bool b a then true else Z.ltb (nat_mod_val p b) (nat_mod_val p a) ;
}.

Fixpoint nat_mod_rem_aux {n : Z} (a:nat_mod n) (b:nat_mod n) (f : nat) {struct f} : nat_mod n :=
  match f with
  | O => a
  | S f' =>
      if geb a b
      then nat_mod_rem_aux (nat_mod_sub a b) b f'
      else a
  end.

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

(* TODO *)
(* Global Instance unit_eqdec : EqDec unit := { *)
(*   eqb := fun _ _ => true ; *)
(*   eqb_leibniz := fun 'tt 'tt => (conj (fun _ => eq_refl) (fun _ => eq_refl)) ; *)
(* }. *)

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
    destruct x as [a0 b0].
    destruct y as [a b].
    apply Bool.andb_true_eq in H1. destruct H1.
    symmetry in H1. apply (eqb_leibniz a0 a) in H1.
    symmetry in H2. apply (eqb_leibniz b0 b) in H2.
    rewrite H1. rewrite H2. reflexivity.
  - inversion_clear H1. destruct x, y. now do 2 rewrite eqb_refl.
Defined.

(*** Result *)

Inductive result (a: Type) (b: Type) :=
  | Ok : a -> result a b
  | Err : b -> result a b.

Arguments Ok {_ _}.
Arguments Err {_ _}.

(*** Be Bytes *)


Fixpoint nat_be_range_at_position (k : nat) (z : Z) (n : Z) : list bool :=
  match k with
  | O => []
  | S k' => Z.testbit z (n + k') :: nat_be_range_at_position k' z n
  end.

Fixpoint nat_be_range_to_position_ (z : list bool) (val : Z) : Z :=
  match z with
  | [] => val
  | x :: xs => nat_be_range_to_position_ xs ((if x then 2 ^ List.length xs else 0) + val)
  end.

Definition nat_be_range_to_position (k : nat) (z : list bool) (n : Z) : Z :=
  (nat_be_range_to_position_ z 0 * 2^(k * n)).

Definition nat_be_range (k : nat) (z : Z) (n : nat) : Z :=
  nat_be_range_to_position_ (nat_be_range_at_position k z (n * k)) 0. (* * 2^(k * n) *)

Compute nat_be_range 4 0 300.

Definition vec_u64_to_be_bytes' : int64 -> nseq_vec int8 8 :=
  fun k => vec_array_from_list (int8) [@nat_to_int WORDSIZE8 (nat_be_range 4 k 7) ;
                               @nat_to_int WORDSIZE8 (nat_be_range 4 k 6) ;
                               @nat_to_int WORDSIZE8 (nat_be_range 4 k 5) ;
                               @nat_to_int WORDSIZE8 (nat_be_range 4 k 4) ;
                               @nat_to_int WORDSIZE8 (nat_be_range 4 k 3) ;
                               @nat_to_int WORDSIZE8 (nat_be_range 4 k 2) ;
                               @nat_to_int WORDSIZE8 (nat_be_range 4 k 1) ;
                               @nat_to_int WORDSIZE8 (nat_be_range 4 k 0)].

Open Scope hacspec_scope.

Definition u64_from_be_bytes_fold_fun (i : int8) (s : prod nat int64) : prod nat int64 :=
  let (n,v) := s in
  (S n, MachineIntegers.add v (@repr WORDSIZE64 ((int8_to_nat i) * 2 ^ (4 * n)))).

-Definition vec_u64_from_be_bytes' : nseq_vec int8 8 -> int64 :=
  (fun v => snd (VectorDef.fold_right u64_from_be_bytes_fold_fun v (0, @repr WORDSIZE64 0))).

Definition vec_u64_to_be_bytes : int64 -> nseq_vec int8 8 := vec_u64_to_be_bytes'.
Definition vec_u64_from_be_bytes : nseq_vec int8 8 -> int64 := vec_u64_from_be_bytes'.

(* Definition nat_mod_to_byte_seq_be : forall {n : Z}, nat_mod n -> seq int8 := *)
(*   fun k => VectorDef.of_list . *)

(*** Monad / Bind *)

Class Monad (M : Type -> Type) :=
  { bind {A B} (x : M A) (f : A -> M B) : M B ;
    ret {A} (x : A) : M A ;
  }.

Definition result2 (b: Type) (a: Type) := result a b.

Definition result_bind {A B C} (r : result2 C A) (f : A -> result2 C B) : result2 C B :=
  match r with
    Ok a => f a
  | Err e => Err e
  end.

Definition result_ret {A C} (a : A) : result2 C A := Ok a.

Global Instance result_monad {C} : Monad (result2 C) :=
  Build_Monad (result2 C) (fun A B => @result_bind A B C) (fun A => @result_ret A C).

Definition option_bind {A B} (r : option A) (f : A -> option B) : option B :=
  match r with
    Some (a) => f a
  | None => None
  end.



Definition option_ret {A} (a : A) : option A := Some a.

Global Instance option_monad : Monad option :=
  Build_Monad option (@option_bind) (@option_ret).

Definition option_is_none {A} (x : option A) : bool :=
  match x with
  | None => true
  | _ => false
  end.

Definition foldi_bind {A : Type} {M : Type -> Type} `{Monad M} (a : uint_size) (b : uint_size) (f : uint_size -> A -> M A) (init : M A) : M A :=
  @foldi (M A) a b (fun x y => bind y (f x)) init.

Definition lift_to_result {A B C} (r : result A C) (f : A -> B) : result B C :=
  result_bind r (fun x => result_ret (f x)).

Definition result_uint_size_to_result_int64 {C} (r : result uint_size C) := lift_to_result r uint_size_to_int64.

Definition result_uint_size_unit := (result uint_size unit).
Definition result_int64_unit := (result int64 unit).

Definition result_uint_size_unit_to_result_int64_unit (r : result_uint_size_unit) : result_int64_unit := result_uint_size_to_result_int64 r.

Global Coercion lift_to_result_coerce {A B C} (f : A -> B) := (fun (r : result A C) => lift_to_result r f).

Global Coercion result_uint_size_unit_to_result_int64_unit : result_uint_size_unit >-> result_int64_unit.

(*** Notation *)

Notation "'ifbnd' b 'then' x 'else' y '>>' f" := (if b then f x else f y) (at level 200).
Notation "'ifbnd' b 'thenbnd' x 'else' y '>>' f" := (if b then (bind x) f else f y) (at level 200).
Notation "'ifbnd' b 'then' x 'elsebnd' y '>>' f" := (if b then f x else (bind y) f) (at level 200).
Notation "'ifbnd' b 'thenbnd' x 'elsebnd' y '>>' f" := (if b then bind x f else bind y f) (at level 200).

Notation "'foldibnd' s 'to' e 'for' z '>>' f" := (foldi s e (fun x y => bind y (f x)) (Ok z)) (at level 50).

Axiom nat_mod_from_byte_seq_be : forall  {A n}, seq A -> nat_mod n.

(*** Default *)

(* Default instances for common types *)
Global Instance nat_default : Default nat := {
  default := 0%nat
}.
Global Instance N_default : Default N := {
  default := 0%N
}.
Global Instance Z_default : Default Z := {
  default := 0%Z
}.
Global Instance uint_size_default : Default uint_size := {
  default := zero
}.
Global Instance int_size_default : Default int_size := {
  default := zero
}.
Global Instance int_default {WS : WORDSIZE} : Default int := {
  default := repr 0
}.
Global Instance uint8_default : Default uint8 := _.
Global Instance nat_mod_default {p : Z} : Default (nat_mod p) := {
  default := nat_mod_zero
}.
Global Instance prod_default {A B} `{Default A} `{Default B} : Default (prod A B) := {
  default := (default, default)
}.
