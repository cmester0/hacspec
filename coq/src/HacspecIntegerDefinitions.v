From Coq Require Import ZArith List.

(*** Default *)

(* Typeclass handling of default elements, for use in sequences/arrays.
   We provide instances for the library integer types *)
Class Default (A : Type) := {
    default : A
  }.
Global Arguments default {_} {_}.

(*** Comparisions *)
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

Instance lt_eq_comparable `{EqDec} (ltb : A -> A -> bool) : Comparable A :=
  {
    ltb := ltb;
    leb a b := if eqb a b then true else ltb a b ;
    gtb a b := ltb b a;
    geb a b := if eqb a b then true else ltb b a;
  }.

(*** Numeric *)

Section Numerics.
  Context {uint_size : Type} {u128 : Type} {u32 : Type}.

  Class ModNumeric (A : Type) : Type :=
    {
      sub_mod : A -> A -> A -> A ;
      add_mod : A -> A -> A -> A ;
      mul_mod : A -> A -> A -> A ;
      pow_mod : A -> A -> A -> A ;
      modulo : A -> A -> A ;
      signed_modulo : A -> A -> A ;
      absolute : A -> A ;
    }.
  Arguments add_mod {_} ModNumeric.
  Arguments sub_mod {_} ModNumeric.
  Arguments mul_mod {_} ModNumeric.
  Arguments pow_mod {_} ModNumeric.
  Arguments modulo {_} ModNumeric.
  Arguments signed_modulo {_} ModNumeric.
  Arguments absolute {_} ModNumeric.

  (* + Add<Self, Output = Self> *)
  (* + Sub<Self, Output = Self> *)
  (* + Mul<Self, Output = Self> *)
  (* + BitXor<Self, Output = Self> *)
  (* + BitOr<Self, Output = Self> *)
  (* + BitAnd<Self, Output = Self> *)
  (* + Shl<usize, Output = Self> *)
  (* + Shr<usize, Output = Self> *)
  (* + Not<Output = Self> *)
  (* + Default *)
  (* + Clone *)
  (* + Debug *)

  Class Numeric (A : Type) `{Default A} `{EqDec A} `{Comparable A} `{ModNumeric A} : Type :=
    {
      max_val : Z ; (* max_val : A *)
      max_val_pos : (0 < max_val)%Z ;
      wrap_add : A -> A -> A ;
      wrap_sub : A -> A -> A ;
      wrap_mul : A -> A -> A ;
      wrap_div : A -> A -> A ;
      exp : A -> u32 -> A ;
      pow_self : A -> A -> A ;
      divide : A -> A -> A ;
      inv : A -> A -> A ;
      
      equal : A -> A -> bool := eqb ;
      
      greater_than : A -> A -> bool := gtb ;
      greater_than_or_equal : A -> A -> bool  := geb ;
      less_than : A -> A -> bool := ltb ;
      less_than_or_equal : A -> A -> bool := leb ;
      
      not_equal_bm : A -> A -> A ;
      equal_bm : A -> A -> A ;
      
      greater_than_bm : A -> A -> A ;
      greater_than_or_equal_bm : A -> A -> A ;
      less_than_bm : A -> A -> A ;
      less_than_or_equal_bm : A -> A -> A ;
    }.

  Arguments max_val {_} {_} {_} {_} {_} Numeric.
  Arguments wrap_add {_} {_} {_} {_} {_} Numeric.
  Arguments wrap_sub {_} {_} {_} {_} {_} Numeric.
  Arguments wrap_mul {_} {_} {_} {_} {_} Numeric.
  Arguments wrap_div {_} {_} {_} {_} {_} Numeric.
  Arguments exp {_} {_} {_} {_} {_} Numeric.
  Arguments pow_self {_} {_} {_} {_} {_} Numeric.
  Arguments divide {_} {_} {_} {_} {_} Numeric.
  Arguments inv {_} {_} {_} {_} {_} Numeric.

  Arguments equal {_} {_} {_} {_} {_} Numeric.
  Arguments greater_than {_} {_} {_} {_} {_} Numeric.
  Arguments greater_than_or_equal {_} {_} {_} {_} {_} Numeric.
  Arguments less_than {_} {_} {_} {_} {_} Numeric.
  Arguments less_than_or_equal {_} {_} {_} {_} {_} Numeric.

  Arguments not_equal_bm {_} {_} {_} {_} {_} Numeric.
  Arguments equal_bm {_} {_} {_} {_} {_} Numeric.
  Arguments greater_than_bm {_} {_} {_} {_} {_} Numeric.
  Arguments greater_than_or_equal_bm {_} {_} {_} {_} {_} Numeric.
  Arguments less_than_bm {_} {_} {_} {_} {_} Numeric.
  Arguments less_than_or_equal_bm {_} {_} {_} {_} {_} Numeric.

  Class Integer (A : Type) `(Numeric A) :=  {
      NUM_BITS: nat ; (* uint_size ; *)
      zero : A ;
      one : A ;
      two : A ;
      from_literal : u128 -> A ;
      from_hex_string : String.string -> A ;
      get_bit : A -> uint_size -> A ;
      set_bit : A -> A -> uint_size -> A ;
      set : A -> uint_size -> A -> uint_size -> A ;
      rotate_left : A -> uint_size -> A ;
      rotate_right : A -> uint_size -> A ;
    }.

  Instance NumericModNumeric `(x : Numeric) : ModNumeric A := _.
  Coercion NumericModNumeric : Numeric >-> ModNumeric.


  (*** Machine Integers *)
  
  Class MachineInteger T `(Integer T) :=
    {
      (* T : Type := IntType (translate i) ; *)
      
      repr : Z -> T ;
      unsigned : T -> Z ;
      signed : T -> Z ;

      (* rol : forall (s u : T), T ; *)
      (* ror : forall (s u : T), T ; *)

      add_int : forall (s u : T), T ;
      sub_int : forall (s u : T), T ;
      neg_int : forall (s : T), T  ;
      mul_int : forall (s u : T), T  ;
      divs_int : forall (s u : T), T  ;
      mods_int : forall (s u : T), T  ;
      xor_int : forall (s u : T), T ;
      and_int : forall (s u : T), T ;
      or_int : forall (s u : T), T ;

      not : forall (s : T), T  ;
      
      eq_int : forall (s u : T), bool ;
      lt_int : forall (s u : T), bool ;

      shl_int : forall (s u : T), T ;
      shr_int : forall (s u : T), T ;

      (* zero : T ; *)
      (* one : T ; *)
      modulus := (max_val _ + 1)%Z ;  (* two_power_nat NUM_BITS *)

      unsigned_repr : forall z, (0 <= z <= max_val _)%Z -> unsigned (repr z) = z ;
      repr_unsigned : forall x, repr (unsigned x) = x ;
      unsigned_range : forall x, (0 <= unsigned x < modulus)%Z ;

      add_unsigned : forall x y, add_int x y = repr (unsigned x + unsigned y) ;
      add_commut : forall x y , add_int x y = add_int y x ;
      add_assoc: forall x y z, add_int (add_int x y) z = add_int x (add_int y z) ;

      zero_is_repr_zero : repr (0%Z) = zero ;
      add_zero_l : forall n, add_int zero n = n ;

      unsigned_one : unsigned one = 1%Z ;

      eq_leibniz_int : forall x y, eq_int x y = true <-> x = y ;
    }.

  Definition IntegerType `(MachineInteger) : Type := T.
End Numerics.

Global Infix "%%" := Z.rem (at level 40, left associativity) : Z_scope.
Global Infix ".+" := add_int (at level 77) : hacspec_scope.
Global Infix ".-" := sub_int (at level 77) : hacspec_scope.
Global Notation "-" := neg_int (at level 77) : hacspec_scope.
Global Infix ".*" := mul_int (at level 77) : hacspec_scope.
Global Infix "./" := divs_int (at level 77) : hacspec_scope.
Global Infix ".%" := mods_int (at level 77) : hacspec_scope.
Global Infix ".^" := xor_int (at level 77) : hacspec_scope.
Global Infix ".&" := and_int (at level 77) : hacspec_scope.
Global Infix ".|" := or_int (at level 77) : hacspec_scope.
Global Infix "==" := eq_int (at level 32) : hacspec_scope.
