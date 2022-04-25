Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".

(*** Integers *)
Require Import String.
From Coq Require Import ZArith List.
Open Scope Z_scope.
Import ListNotations.
(* Require Import IntTypes. *)

Require MachineIntegers.
From Coqprime Require GZnZ.

Require Import Lia.

Declare Scope hacspec_scope.

Require Import HacspecIntegerDefinitions.
Export HacspecIntegerDefinitions.

Definition string_t := string.

Global Instance int_default {ws : MachineIntegers.WORDSIZE} : Default (@MachineIntegers.int ws) :=
  {| default := @MachineIntegers.repr ws 0 |}.

Global Instance int_eqdec `{ws : MachineIntegers.WORDSIZE}: EqDec (@MachineIntegers.int (ws)) :=
  {|
        eqb := @MachineIntegers.eq _ ;
        eqb_leibniz := ltac:(split ; [ apply MachineIntegers.same_if_eq | intros ; subst ; rewrite MachineIntegers.eq_true ; reflexivity ])
  |}.

Global Instance int_comparable `{ws : MachineIntegers.WORDSIZE} : Comparable (@MachineIntegers.int (ws)) := lt_eq_comparable MachineIntegers.lt.

Global Instance int_modnumeric `{WS : MachineIntegers.WORDSIZE} : ModNumeric (@MachineIntegers.int WS) := {
    sub_mod := fun a b n => MachineIntegers.sub a b ; (* TODO *)
    add_mod := fun a b n => MachineIntegers.add a b ; (* TODO *)
    mul_mod := fun a b n => MachineIntegers.mul a b ; (* TODO *)
    pow_mod := fun a b n => MachineIntegers.add a b ; (* TODO *)
    modulo := fun a n => MachineIntegers.mods a n ; (* TODO *)
    signed_modulo := fun a n => MachineIntegers.mods a n ; (* TODO *)
    absolute := fun a => a ; (* TODO *)
  }.

Definition bool_fun_to_int {WS : MachineIntegers.WORDSIZE} {A} (fb : A -> A -> bool) : A -> A -> @MachineIntegers.int WS :=
  (fun x y => if fb x y then MachineIntegers.one else MachineIntegers.zero).

Instance int_numeric (ws : MachineIntegers.WORDSIZE) :
  Numeric (u32 := MachineIntegers.int32) (@MachineIntegers.int (ws)) := {|
    max_val := @MachineIntegers.max_unsigned (ws) ;
    max_val_pos := ltac:(destruct ws as [ [] ] ; easy) ;
    wrap_add := MachineIntegers.add ;
    wrap_sub := MachineIntegers.sub ;
    wrap_mul := MachineIntegers.mul ;
    wrap_div := MachineIntegers.divs ;
    exp x n := x ; (* TODO *)
    pow_self x y := MachineIntegers.repr (MachineIntegers.unsigned x ^ MachineIntegers.unsigned y) ;
    divide := MachineIntegers.divs ;
    inv := fun a b => a ; (* TODO *)
        
    not_equal_bm := bool_fun_to_int (fun a b => negb (eqb a b)) ;
    equal_bm := bool_fun_to_int eqb ;
    
    greater_than_bm := bool_fun_to_int gtb ;
    greater_than_or_equal_bm := bool_fun_to_int geb ;
    less_than_bm := bool_fun_to_int ltb ;
    less_than_or_equal_bm := bool_fun_to_int leb ;
    |}.
  
  
  
Global Instance int_integer (ws : MachineIntegers.WORDSIZE) :
  Integer (u128 := @MachineIntegers.int128) (u32 := @MachineIntegers.int32) (uint_size := @MachineIntegers.int32) (@MachineIntegers.int (ws)) (int_numeric ws)
  := {
    NUM_BITS := (@MachineIntegers.wordsize (ws)) ;
    zero := MachineIntegers.zero ;
    one := MachineIntegers.one ;
    two := MachineIntegers.repr 2%Z ;
    from_literal x := MachineIntegers.repr (MachineIntegers.unsigned x) ;
    from_hex_string s := MachineIntegers.zero ; (* TODO *)
    get_bit a b := a ; (* TODO *)
    set_bit a b c := a ; (* TODO *)
    set a b c d := a ;
    rotate_left a n := MachineIntegers.rol a (MachineIntegers.repr (MachineIntegers.unsigned n)) ;
    rotate_right a n := MachineIntegers.rol a (MachineIntegers.repr (MachineIntegers.unsigned n)) ;
  }.

(* (@MachineIntegers.int) *)
(* int_WS   *)
(* ws int_WS *)

Instance machine_int {ws : MachineIntegers.WORDSIZE} : MachineInteger (u128 := @MachineIntegers.int128) (u32 := @MachineIntegers.int32) (uint_size := @MachineIntegers.int32) (@MachineIntegers.int (ws)) (int_integer ws) := {|
    
    repr := MachineIntegers.repr ;
    unsigned := MachineIntegers.unsigned ;
    signed := MachineIntegers.signed ;

    (* rotate_left := MachineIntegers.rol ; *)
    (* rotate_right := MachineIntegers.ror ; *)
    add_int := MachineIntegers.add ;
    sub_int := MachineIntegers.sub ;
    neg_int := MachineIntegers.neg ;
    mul_int := MachineIntegers.mul ;
    divs_int := MachineIntegers.divs ;
    mods_int := MachineIntegers.mods ;
    xor_int := MachineIntegers.xor ;
    and_int := MachineIntegers.and ;
    or_int := MachineIntegers.or ;

    not := MachineIntegers.not ;
    
    eq_int := MachineIntegers.eq ;
    lt_int := MachineIntegers.lt ;

    shl_int := MachineIntegers.shl ;
    shr_int := MachineIntegers.shr ;

    (* zero := MachineIntegers.zero ; *)
    (* one := MachineIntegers.one ; *)
    unsigned_repr := ltac:(intros ; rewrite MachineIntegers.unsigned_repr ; easy) ;
    repr_unsigned := (MachineIntegers.repr_unsigned) ;
    unsigned_range := ltac:(intros ; unfold max_val, int_numeric, MachineIntegers.max_unsigned; pose (MachineIntegers.unsigned_range x) ; lia) ;
    add_unsigned := MachineIntegers.add_unsigned ;
    add_commut := MachineIntegers.add_commut ;
    add_assoc := MachineIntegers.add_assoc ;

    zero_is_repr_zero := ltac:(reflexivity) ;
    add_zero_l := MachineIntegers.add_zero_l ;
    unsigned_one := MachineIntegers.unsigned_one ;

    eq_leibniz_int := ltac:(split ; [ apply MachineIntegers.same_if_eq | intros ; subst ; rewrite MachineIntegers.eq_true ; reflexivity ]) ;
    |}.

Definition int {ws : MachineIntegers.WORDSIZE} := machine_int.
Definition int_type {ws : MachineIntegers.WORDSIZE} := IntegerType int.

About max_val.
Print Graph.

Opaque repr.
Opaque unsigned.
Opaque zero.

Opaque add_int.
Opaque sub_int.
Opaque neg_int.
Opaque mul_int.
Opaque divs_int.
Opaque mods_int.

 (* z ltac:(rewrite max_unsigned_eq ; apply k)) ; *)

Axiom secret : forall {WS : MachineIntegers.WORDSIZE},  @int WS -> @int WS.

Axiom declassify : forall {WS : MachineIntegers.WORDSIZE}, @int WS -> @int WS.
Definition uint8_declassify := @declassify MachineIntegers.WORDSIZE8.
Definition int8_declassify := @declassify MachineIntegers.WORDSIZE8.
Definition uint16_declassify := @declassify MachineIntegers.WORDSIZE16.
Definition int16_declassify := @declassify MachineIntegers.WORDSIZE16.
Definition uint32_declassify := @declassify MachineIntegers.WORDSIZE32.
Definition int32_declassify := @declassify MachineIntegers.WORDSIZE32.
Definition uint64_declassify := @declassify MachineIntegers.WORDSIZE64.
Definition int64_declassify := @declassify MachineIntegers.WORDSIZE64.
Definition uint128_declassify := @declassify MachineIntegers.WORDSIZE128.
Definition int128_declassify := @declassify MachineIntegers.WORDSIZE128.

Axiom classify : forall {WS : MachineIntegers.WORDSIZE}, @int WS -> @int WS.
Definition uint8_classify := @classify MachineIntegers.WORDSIZE8.
Definition int8_classify := @classify MachineIntegers.WORDSIZE8.
Definition uint16_classify := @classify MachineIntegers.WORDSIZE16.
Definition int16_classify := @classify MachineIntegers.WORDSIZE16.
Definition uint32_classify := @classify MachineIntegers.WORDSIZE32.
Definition int32_classify := @classify MachineIntegers.WORDSIZE32.
Definition uint64_classify := @classify MachineIntegers.WORDSIZE64.
Definition int64_classify := @classify MachineIntegers.WORDSIZE64.
Definition uint128_classify := @classify MachineIntegers.WORDSIZE128.
Definition int128_classify := @classify MachineIntegers.WORDSIZE128.


(* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
 *)

Definition int8 := @int MachineIntegers.WORDSIZE8.
Definition int16 := @int MachineIntegers.WORDSIZE16.
Definition int32 := @int MachineIntegers.WORDSIZE32.
Definition int64 := @int MachineIntegers.WORDSIZE64.
Definition int128 := @int MachineIntegers.WORDSIZE128.

Definition uint8 := @int MachineIntegers.WORDSIZE8.
Definition uint16 := @int MachineIntegers.WORDSIZE16.
Definition uint32 := @int MachineIntegers.WORDSIZE32.
Definition uint64 := @int MachineIntegers.WORDSIZE64.
Definition uint128 := @int MachineIntegers.WORDSIZE128.

Definition pub_uint8 := @int MachineIntegers.WORDSIZE8.
Definition pub_uint16 := @int MachineIntegers.WORDSIZE16.
Definition pub_uint32 := @int MachineIntegers.WORDSIZE32.
Definition pub_uint64 := @int MachineIntegers.WORDSIZE64.
Definition pub_uint128 := @int MachineIntegers.WORDSIZE128.

Definition uint_size := @int MachineIntegers.WORDSIZE32.
Definition int_size := @int MachineIntegers.WORDSIZE32.

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

Definition pub_u8 (n : Z) : int8 := repr n.
Definition pub_i8 (n : Z) : int8 := repr n.
Definition pub_u16 (n : Z) : int16 := repr n.
Definition pub_i16 (n : Z) : int16 := repr n.
Definition pub_u32 (n : Z) : int32 := repr n.
Definition pub_i32 (n : Z) : int32 := repr n.
Definition pub_u64 (n : Z) : int64 := repr n.
Definition pub_i64 (n : Z) : int64 := repr n.
Definition pub_u128 (n : Z) : int128 := repr n.
Definition pub_i128 (n : Z) : int128 := repr n.

(**** Operations *)

Hint Unfold int8.
Hint Unfold int.
Hint Unfold IntegerType.

(* Should maybe use size of s instead? *)
Definition uint8_rotate_left (u: int8) (s: uint_size) : int8 := rotate_left u s.
Definition uint8_rotate_right (u: int8) (s: uint_size) : int8 := rotate_right u s.

Definition uint16_rotate_left (u: int16) (s: uint_size) : int16 := rotate_left u s.
Definition uint16_rotate_right (u: int16) (s: uint_size) : int16 := rotate_right u s.

Definition uint32_rotate_left (u: int32) (s: uint_size) : int32 := rotate_left u s.
Definition uint32_rotate_right (u: int32) (s: uint_size) : int32 := rotate_right u s.

Definition uint64_rotate_left (u: int64) (s: uint_size) : int64 := rotate_left u s.
Definition uint64_rotate_right (u: int64) (s: uint_size) : int64 := rotate_right u s.

Definition uint128_rotate_left (u: int128) (s: uint_size) : int128 := rotate_left u s.
Definition uint128_rotate_right (u: int128) (s: uint_size) : int128 := rotate_right u s.

(* should use size u instead of u? *)
Definition usize_shift_right (u: uint_size) (s: uint_size) : uint_size := rotate_right u s.
Infix "usize_shift_right" := (usize_shift_right) (at level 77) : hacspec_scope.

(* should use size u instead of u? *)
Definition usize_shift_left (u: uint_size) (s: uint_size) : uint_size := rotate_left u s.
Infix "usize_shift_left" := (usize_shift_left) (at level 77) : hacspec_scope.

Definition pub_uint128_wrapping_add (x y: int128) : int128 := add_int x y.

Definition shift_left_ `{WS : MachineIntegers.WORDSIZE} (i : @int WS) (j : uint_size) :=
  shl_int i (repr (from_uint_size j)).

Definition shift_right_ `{WS : MachineIntegers.WORDSIZE} (i : @int WS) (j : uint_size) :=
  shr_int i (repr (from_uint_size j)) .

Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope.
Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope.

(* Definition one := (@one U32). *)
(* Definition zero := (@zero U32). *)
Notation "A × B" := (prod A B) (at level 79, left associativity) : hacspec_scope.

(*** Positive util *)

Fixpoint binary_representation_pre (n : nat) {struct n}: positive :=
  match n with
  | O => 1
  | S O => 1
  | S n => Pos.succ (binary_representation_pre n)
  end%positive.
Definition binary_representation (n : nat) `(n <> O) := binary_representation_pre n.

Theorem positive_is_succs : forall n, forall (H : n <> O) (K : S n <> O),
    @binary_representation (S n) K = Pos.succ (@binary_representation n H).
Proof. induction n ; [contradiction | reflexivity]. Qed.

(* Conversion of positive to binary representation *)
Theorem positive_to_positive_succs : forall p, binary_representation (Pos.to_nat p) (Nat.neq_sym _ _ (Nat.lt_neq _ _ (Pos2Nat.is_pos p))) = p.
Proof.
  intros p.
  generalize dependent (Nat.neq_sym 0 (Pos.to_nat p) (Nat.lt_neq 0 (Pos.to_nat p) (Pos2Nat.is_pos p))).

  destruct Pos.to_nat eqn:ptno.
  - contradiction.
  - generalize dependent p.
    induction n ; intros.
    + cbn.
      apply Pos2Nat.inj.
      symmetry.
      apply ptno.
    + rewrite positive_is_succs with (H := Nat.neq_succ_0 n).
      rewrite IHn with (p := Pos.of_nat (S n)).
      * rewrite <- Nat2Pos.inj_succ by apply Nat.neq_succ_0.
        rewrite <- ptno.
        apply Pos2Nat.id.
      * apply Nat2Pos.id.
        apply Nat.neq_succ_0.
Qed.

(*** Uint size util *)

(* If a natural number is in bound then a smaller natural number is still in bound *)
Lemma range_of_nat_succ :
  forall {WS : MachineIntegers.WORDSIZE},
  forall i, (0 <= Z.of_nat (S i) < modulus)%Z -> (0 <= Z.of_nat i < modulus)%Z.
Proof. lia. Qed.

(* Conversion to equivalent bound *)
Lemma modulus_range_helper :
  forall {WS : MachineIntegers.WORDSIZE},
  forall i, (0 <= i < modulus)%Z -> (0 <= i <= _.(max_val))%Z.
Proof. intros. unfold modulus in H. lia. Qed.

Definition unsigned_repr_alt {WS : MachineIntegers.WORDSIZE} {a : Z} `((0 <= a < modulus)%Z) :
  unsigned (repr a) = a :=
  unsigned_repr a (@modulus_range_helper WS a H).

Theorem zero_always_modulus {WS : MachineIntegers.WORDSIZE} : (0 <= 0 < modulus)%Z.
Proof. unfold modulus. pose max_val_pos ; lia. Qed.

(* any uint_size can be represented as a natural number and a bound *)
(* this is easier for proofs, however less efficient for computation *)
(* as Z uses a binary representation *)
Theorem uint_size_as_nat :
  forall (us: uint_size),
    { n : nat |
      us = repr (Z.of_nat n) /\ (0 <= Z.of_nat n < modulus (T := int32))%Z}.
Proof.
  intros us.
  pose (bound := unsigned_range us).
  exists (Z.to_nat (unsigned us)).
  rewrite Z2Nat.id by apply bound.
  rewrite repr_unsigned.
  split ; [reflexivity |].
  apply bound.
Qed.

(* destruct uint_size as you would a natural number *)
Definition destruct_uint_size_as_nat  (a : uint_size) : forall (P : uint_size -> Prop),
    forall (zero_case : P (repr 0)),
    forall (succ_case : forall (n : nat), (0 <= Z.of_nat n < modulus (T := int32))%Z -> P (repr (Z.of_nat n))),
    P a.
Proof.
  intros.
  destruct (uint_size_as_nat a) as [ n y ] ; destruct y as [ya yb] ; subst.
  destruct n.
  - apply zero_case.
  - apply succ_case.
    apply yb.
Qed.

Ltac destruct_uint_size_as_nat a :=
  generalize dependent a ;
  intros a ;
  apply (destruct_uint_size_as_nat a) ; [ pose proof (@unsigned_repr_alt MachineIntegers.WORDSIZE32 0 zero_always_modulus) | let n := fresh in let H := fresh in intros n H ; pose proof (@unsigned_repr_alt MachineIntegers.WORDSIZE32 _ H)] ; intros.

(* induction for uint_size as you would do for a natural number *)
Definition induction_uint_size_as_nat :
  forall (P : uint_size -> Prop),
    (P (repr 0)) ->
    (forall n,
        (0 <= Z.succ (Z.of_nat n) < modulus (T := int32))%Z ->
        P (repr (Z.of_nat n)) ->
        P (repr (Z.succ (Z.of_nat n)))) ->
    forall (a : uint_size), P a.
Proof.
  intros P H_zero H_ind a.
  destruct (uint_size_as_nat a) as [ n y ] ; destruct y as [ya yb] ; subst.
  induction n.
  - apply H_zero.
  - rewrite Nat2Z.inj_succ.
    apply H_ind.
    + rewrite <- Nat2Z.inj_succ.
      apply yb.
    + apply IHn.
      lia.
Qed.

Ltac induction_uint_size_as_nat var :=
  generalize dependent var ;
  intros var ;
  apply induction_uint_size_as_nat with (a := var) ; [ pose proof (@unsigned_repr_alt MachineIntegers.WORDSIZE32 0 zero_always_modulus) | let n := fresh in let IH := fresh in intros n IH ; pose proof (@unsigned_repr_alt MachineIntegers.WORDSIZE32 _ IH)] ; intros.

(* conversion of usize to positive or zero and the respective bound *)
Theorem uint_size_as_positive :
  forall (us: uint_size),
    { pu : unit + positive |
      match pu with inl u => us = repr Z0 | inr p => us = repr (Z.pos p) /\ (0 <= Z.pos p < modulus (T := int32))%Z end
      }.
Proof.
  intros.
  destruct (unsigned us) eqn:ous.
  - exists (inl tt). rewrite <- ous. rewrite repr_unsigned. reflexivity.
  - exists (inr p). rewrite <- ous. rewrite repr_unsigned.
    split.
    + reflexivity.
    + apply (unsigned_range us).
  - exfalso.
    pose (unsigned_range us).    
    lia.
Defined.

(* destruction of uint_size as positive *)
Definition destruct_uint_size_as_positive  (a : uint_size) : forall (P : uint_size -> Prop),
    (P (repr 0)) ->
    (forall b, (0 <= Z.pos b < modulus (T := int32))%Z -> P (repr (Z.pos b))) ->
    P a.
Proof.
  intros P H_zero H_succ.
  destruct (uint_size_as_positive a) as [ [ _ | b ] y ] ; [ subst | destruct y as [ya yb] ; subst ].
  - apply H_zero.
  - apply H_succ.
    apply yb.
Qed.

Ltac destruct_uint_size_as_positive a :=
  generalize dependent a ;
  intros a ;
  apply (destruct_uint_size_as_positive a) ; intros.

(* induction of uint_size as positive *)
Definition induction_uint_size_as_positive :
  forall (P : uint_size -> Prop),
    (P (repr 0)) ->
    (P (repr 1)) ->
    (forall b,
        (0 <= Z.succ (Z.pos b) < modulus (T := int32))%Z ->
        P (repr (Z.pos b)) ->
        P (repr (Z.succ (Z.pos b)))) ->
    forall (a : uint_size), P a.
Proof.
  intros P H_zero H_one H_ind a.

  destruct (uint_size_as_positive a) as [ [ _ | b ] y ] ; [ subst | destruct y as [ya yb] ; subst ].
  - apply H_zero.
  - pose proof (pos_succ_b := positive_to_positive_succs b)
    ; symmetry in pos_succ_b
    ; rewrite pos_succ_b in *
    ; clear pos_succ_b.

    generalize dependent (Nat.neq_sym 0 (Pos.to_nat b) (Nat.lt_neq 0 (Pos.to_nat b) (Pos2Nat.is_pos b))).

    induction (Pos.to_nat b).
    + contradiction.
    + intros n_neq yb.
      destruct n.
      * apply H_one.
      * rewrite (positive_is_succs _  (Nat.neq_succ_0 n) n_neq) in *.
        rewrite Pos2Z.inj_succ in *.
        apply H_ind.
        -- apply yb.
        -- apply IHn.
           lia.
Qed.

Ltac induction_uint_size_as_positive var :=
  generalize dependent var ;
  intros var ;
  apply induction_uint_size_as_positive with (a := var) ; intros ; [ | | ].

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
  | S n' => foldi_ n' (add_int i one) f (f i cur)
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

(* Fold done using natural numbers for bounds *)
Fixpoint foldi_nat_
  {acc : Type}
  (fuel : nat)
  (i : nat)
  (f : nat -> acc -> acc)
  (cur : acc) : acc :=
  match fuel with
  | O => cur
  | S n' => foldi_nat_ n' (S i) f (f i cur)
  end.
Definition foldi_nat
  {acc: Type}
  (lo: nat)
  (hi: nat) (* {lo <= hi} *)
  (f: nat -> acc -> acc) (* {i < hi} *)
  (init: acc) : acc :=
  match Nat.sub hi lo with
  | O => init
  | S n' => foldi_nat_ (S n') lo f init
  end.

Lemma foldi__move_S :
  forall {acc: Type}
  (fuel : nat)
  (i : uint_size)
  (f : uint_size -> acc -> acc)
  (cur : acc),
    foldi_ fuel (add_int i one) f (f i cur) = foldi_ (S fuel) i f cur.
Proof. reflexivity. Qed.

Lemma foldi__nat_move_S :
  forall {acc: Type}
  (fuel : nat)
  (i : nat)
  (f : nat -> acc -> acc)
  (cur : acc),
    foldi_nat_ fuel (S i) f (f i cur) = foldi_nat_ (S fuel) i f cur.
Proof. reflexivity. Qed.

(* You can do one iteration of the fold by burning a unit of fuel *)
Lemma foldi__move_S_fuel :
  forall {acc: Type}
  (fuel : nat)
  (i : uint_size)
  (f : uint_size -> acc -> acc)
  (cur : acc),
    (0 <= Z.of_nat fuel <= int32.(@max_val _ _ _ _ _ _))%Z ->
    f (add_int (repr (Z.of_nat fuel)) i) (foldi_ (fuel) i f cur) = foldi_ (S (fuel)) i f cur.
Proof.
  intros acc fuel.
  induction fuel ; intros.
  - unfold Z.of_nat.
    unfold Z.of_nat in H.
    rewrite zero_is_repr_zero.
    rewrite add_zero_l.
    reflexivity.
  - do 2 rewrite <- foldi__move_S.
    unfold uint_size , IntegerType in *.
    replace (add_int (repr (Z.of_nat (S fuel))) i)
      with (add_int (repr (Z.of_nat fuel)) (add_int i one)).    
    2 : {
      clear -H.
      rewrite <- (add_commut one).
      rewrite <- add_assoc.
      f_equal.
      rewrite add_unsigned.
      f_equal.
      rewrite unsigned_one.
      rewrite Z.add_1_r.
      rewrite Nat2Z.inj_succ.
      f_equal.
      apply unsigned_repr.
      destruct H.
      split.
      - lia.
      - rewrite Nat2Z.inj_succ in H0.
        apply Zle_succ_le.
        apply H0.
    }
    
    rewrite IHfuel.
    reflexivity.
    lia.
Qed.

(* You can do one iteration of the fold by burning a unit of fuel *)
Lemma foldi__nat_move_S_fuel :
  forall {acc: Type}
  (fuel : nat)
  (i : nat)
  (f : nat -> acc -> acc)
  (cur : acc),
    (0 <= Z.of_nat fuel <= int32.(max_val))%Z ->
    f (fuel + i)%nat (foldi_nat_ fuel i f cur) = foldi_nat_ (S fuel) i f cur.
Proof.
  induction fuel ; intros.
  - reflexivity.
  - do 2 rewrite <- foldi__nat_move_S.
    replace (S fuel + i)%nat with (fuel + (S i))%nat by (symmetry ; apply plus_Snm_nSm).
    rewrite IHfuel.
    + reflexivity.
    + lia.
Qed.

(* folds and natural number folds compute the same thing *)
Lemma foldi_to_foldi_nat :
  forall {acc: Type}
    (lo: uint_size) (* {lo <= hi} *)
    (hi: uint_size) (* {lo <= hi} *)
    (f: (uint_size) -> acc -> acc) (* {i < hi} *)
    (init: acc),
    (unsigned lo <= unsigned hi)%Z ->
    foldi lo hi f init = foldi_nat (Z.to_nat (unsigned lo)) (Z.to_nat (unsigned hi)) (fun x => f (repr (Z.of_nat x))) init.
Proof.
  intros.

  unfold foldi.
  unfold foldi_nat.


  destruct (uint_size_as_nat hi) as [ hi_n [ hi_eq hi_H ] ] ; subst.
  pose (@unsigned_repr_alt MachineIntegers.WORDSIZE32 _ hi_H).
  unfold uint_size , IntegerType in *.
  rewrite (@unsigned_repr_alt MachineIntegers.WORDSIZE32 _ hi_H) in *.
  rewrite Nat2Z.id.

  destruct (uint_size_as_nat lo) as [ lo_n [ lo_eq lo_H ] ] ; subst.
  unfold uint_size , IntegerType in *.
  rewrite (@unsigned_repr_alt MachineIntegers.WORDSIZE32 _ lo_H) in *.
  rewrite Nat2Z.id.

  remember (hi_n - lo_n)%nat as n.
  apply f_equal with (f := Z.of_nat) in Heqn.
  rewrite (Nat2Z.inj_sub) in Heqn by (apply Nat2Z.inj_le ; apply H).
  rewrite <- Heqn.
  
  assert (loop_bound : forall n m b, m <= n -> 0 <= n < b -> 0 <= m < b -> 0 <= n - m < b ).
  {    
    clear ; intros.
    destruct b ; lia.
  } 

  pose proof (H_bound := loop_bound (Z.of_nat hi_n) (Z.of_nat lo_n) (modulus (T := int32)) H hi_H lo_H) ; rewrite <- Heqn in H_bound.

  clear Heqn.
  induction n.
  - reflexivity.
  - pose proof (H_max_bound := modulus_range_helper _ (range_of_nat_succ _ H_bound)).
    rewrite <- foldi__nat_move_S_fuel by apply H_max_bound.
    cbn.
    rewrite SuccNat2Pos.id_succ.
    rewrite <- foldi__move_S_fuel by apply H_max_bound.


    destruct n.
    + rewrite zero_is_repr_zero.
      cbn in *.
      rewrite add_zero_l.
      reflexivity.
    + cbn in *.
      assert (H_bound_pred: (0 <= Z.pos (Pos.of_succ_nat n) < modulus (T := int32))%Z) by lia.
      rewrite <- (IHn H_bound_pred) ; clear IHn.
      f_equal.
      * rewrite add_unsigned.
        f_equal.
        unfold uint_size, IntegerType in *.
        rewrite (unsigned_repr_alt lo_H) in *.
        rewrite (unsigned_repr_alt H_bound_pred).
        do 2 rewrite Zpos_P_of_succ_nat.
        rewrite Z.add_succ_l.
        f_equal.
        rewrite Nat2Z.inj_add.
        reflexivity.
      * rewrite SuccNat2Pos.id_succ.
        rewrite foldi__move_S.
        reflexivity.
Qed.

(* folds can be computed by doing one iteration and incrementing the lower bound *)
Lemma foldi_nat_split_S :
  forall {acc: Type}
    (lo: nat)
    (hi: nat) (* {lo <= hi} *)
    (f: nat -> acc -> acc) (* {i < hi} *)
    (init: acc),
    (lo < hi)%nat ->
    foldi_nat lo hi f init = foldi_nat (S lo) hi f (foldi_nat lo (S lo) f init).
Proof.
  unfold foldi_nat.
  intros.

  assert (succ_sub_diag : forall n, (S n - n = 1)%nat) by lia.
  rewrite (succ_sub_diag lo).

  induction hi ; [ lia | ].
  destruct (S hi =? S lo)%nat eqn:hi_eq_lo.
  - apply Nat.eqb_eq in hi_eq_lo ; rewrite hi_eq_lo in *.
    rewrite (succ_sub_diag lo).
    rewrite Nat.sub_diag.
    reflexivity.
  - apply Nat.eqb_neq in hi_eq_lo.
    apply Nat.lt_gt_cases in hi_eq_lo.
    destruct hi_eq_lo.
    + lia.
    + rewrite (Nat.sub_succ_l (S lo)) by apply (Nat.lt_le_pred _ _ H0).
      rewrite Nat.sub_succ_l by apply (Nat.lt_le_pred _ _ H).
      replace ((S (hi - S lo))) with (hi - lo)%nat by lia.
      reflexivity.
Qed.

(* folds can be split at some valid offset from lower bound *)
Lemma foldi_nat_split_add :
  forall (k : nat),
  forall {acc: Type}
    (lo: nat)
    (hi: nat) (* {lo <= hi} *)
    (f: nat -> acc -> acc) (* {i < hi} *)
    (init: acc),
  forall {guarantee: (lo + k <= hi)%nat},
  foldi_nat lo hi f init = foldi_nat (k + lo) hi f (foldi_nat lo (k + lo) f init).
Proof.
  induction k ; intros.
  - cbn.
    unfold foldi_nat.
    rewrite Nat.sub_diag.
    reflexivity.
  - rewrite foldi_nat_split_S by lia.
    replace (S k + lo)%nat with (k + S lo)%nat by lia.
    specialize (IHk acc (S lo) hi f (foldi_nat lo (S lo) f init)).
    rewrite IHk by lia.
    f_equal.
    rewrite <- foldi_nat_split_S by lia.
    reflexivity.
Qed.

(* folds can be split at some midpoint *)
Lemma foldi_nat_split :
  forall (mid : nat), (* {lo <= mid <= hi} *)
  forall {acc: Type}
    (lo: nat)
    (hi: nat) (* {lo <= hi} *)
    (f: nat -> acc -> acc) (* {i < hi} *)
    (init: acc),
  forall {guarantee: (lo <= mid <= hi)%nat},
  foldi_nat lo hi f init = foldi_nat mid hi f (foldi_nat lo mid f init).
Proof.
  intros.
  assert (mid_is_low_plus_constant : {k : nat | (mid = lo + k)%nat})  by (exists (mid - lo)%nat ; lia).
  destruct mid_is_low_plus_constant ; subst.
  rewrite Nat.add_comm.
  apply foldi_nat_split_add.
  apply guarantee.
Qed.

(* folds can be split at some midpoint *)
Lemma foldi_split :
  forall (mid : uint_size), (* {lo <= mid <= hi} *)
  forall {acc: Type}
    (lo: uint_size)
    (hi: uint_size) (* {lo <= hi} *)
    (f: uint_size -> acc -> acc) (* {i < hi} *)
    (init: acc),
  forall {guarantee: (unsigned lo <= unsigned mid <= unsigned hi)%Z},
  foldi lo hi f init = foldi mid hi f (foldi lo mid f init).
Proof.
  intros.
  do 3 rewrite foldi_to_foldi_nat by lia.
  apply foldi_nat_split ; lia.
Qed.

(*** List types *)

Definition nseq := VectorDef.t.
Definition seq (A : Type) := list A.

(*** Nseq *)

Definition array_new {A: Type} `{Default A} (len: nat)  : nseq A len :=
  VectorDef.const default len.

Definition array_len  {a: Type} {len: nat} (s: nseq a len) := len.

Definition array_index {A: Type} `{Default A} {len : nat} (s: nseq A len) (i: nat) : A.
Proof.
  destruct (i <? len)%nat eqn:H1.
  (* If i < len, index normally *)
  - rewrite Nat.ltb_lt in H1.
    exact (VectorDef.nth s (Fin.of_nat_lt H1)).
  (* otherwise return default element *)
  - exact default.
Defined.

Axiom array_declassify_eq : forall  {A l}, nseq A l -> nseq A l -> bool.
Axiom array_to_le_bytes : forall {A l}, nseq A l -> seq uint8.
Axiom array_to_be_bytes : forall {A l}, nseq A l -> seq uint8.
Axiom array_to_le_uint32s : forall {l}, nseq uint8 l -> seq uint32.
Axiom array_to_be_uint32s : forall {l}, nseq uint8 l -> seq uint32.
Axiom array_to_le_uint64s : forall {l}, nseq uint8 l -> seq uint64.
Axiom array_to_be_uint64s : forall {l}, nseq uint8 l -> seq uint64.
Axiom array_to_uint128s_le : forall {l}, nseq uint8 l -> seq uint128.
Axiom array_to_uint128s_be : forall {l}, nseq uint8 l -> seq uint128.

Definition array_new_ {A: Type} (init:A) (len: nat)  : nseq A len :=
  VectorDef.const init len.

Definition array_upd {A: Type} {len : nat} (s: nseq A len) (i: nat) (new_v: A) : nseq A len.
Proof.
  destruct (i <? len)%nat eqn:H.
  (* If i < len, update normally *)
  - rewrite Nat.ltb_lt in H.
    exact (VectorDef.replace s (Fin.of_nat_lt H) new_v).
  (* otherwise return original array *)
  - exact s.
Defined.



(* May also come up as 'length' instead of 'len' *)
Definition array_length (len : nat) := len.


Definition slice {A} (l : seq A) (i j : nat) : seq A :=
  (if j <=? i then [] else firstn (j-i+1) (skipn i l))%nat.

Definition lseq_slice {A n} (l : nseq A n) (i j : nat) : nseq A _ :=
  VectorDef.of_list (slice (VectorDef.to_list l) i j).

(* substitutes a sequence (list) into an array (nseq), given index interval  *)
(* Axiom update_sub : forall {A len }, nseq A len -> nat -> nat -> seq A -> t A len. *)
Definition update_sub {A len slen} `{Default A} (v : nseq A len) (i : nat) (n : nat) (sub : nseq A slen) : nseq A len :=
  let fix rec x acc :=
    match x with
    | O => acc
    (* | 0 => array_upd acc 0 (array_index sub 0) *)
    | S x => rec x (array_upd acc (i+x) (array_index sub x))
    end in
  rec (n - i + 1)%nat v.

Definition array_from_slice
  {a: Type}
  `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start: nat)
  (slice_len: nat)
    : nseq a out_len :=
    let out := VectorDef.const default_value out_len in
    update_sub out 0 slice_len (lseq_slice (VectorDef.of_list input) start (start + slice_len)).

Definition array_concat
  {a : Type}
  {l : nat}
  (s1 :nseq a l)
  (s2: seq a)
  : seq a :=
  VectorDef.to_list s1 ++ s2.

Definition array_from_slice_range
  {a: Type}
 `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start_fin: (uint_size * uint_size))
  : nseq a out_len :=
  let (start, fin) := start_fin in
  array_from_slice default_value out_len input (from_uint_size start) ((from_uint_size fin) - (from_uint_size start))%nat.

Definition array_slice
  {a: Type}
  `{Default a}
  {l : nat}
  (input: nseq a l)
  (start: nat)
  (slice_len: nat)
    : nseq a _ :=
  lseq_slice input start (start + slice_len).

Definition array_slice_range
  {a: Type}
  {len : nat}
  (input: nseq a len)
  (start_fin:(uint_size * uint_size))
    : nseq a _ :=
  lseq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin)).

Definition array_num_chunks {a: Type} {l : nat} (s: nseq a l) (chunk_len: nat) : nat :=
  ((array_len s) + chunk_len - 1) / chunk_len.

Definition array_get_chunk_len
  {a: Type}
  {l : nat}
  (s: nseq a l)
  (chunk_len: nat)
  (chunk_num: nat)
    : nat :=
  let idx_start := (chunk_len * chunk_num)%nat in
  if (array_len s <? idx_start + chunk_len)%nat then
    (array_len s) - idx_start
  else
    chunk_len.

Definition array_get_chunk
  {a: Type}
  {l : nat}
  (s: nseq a l)
  (chunk_len: nat)
  (chunk_num: nat)
  : (uint_size * seq a)
 :=
  let idx_start := (chunk_len * chunk_num)%nat in
  let out_len := array_get_chunk_len s chunk_len chunk_num in
  (usize out_len,
    VectorDef.to_list (lseq_slice
    s idx_start (idx_start + array_get_chunk_len s chunk_len chunk_num))).

Definition array_set_chunk
  {a: Type}
  {l : nat}
  `{Default a}
  (s: nseq a l)
  (chunk_len: nat)
  (chunk_num: nat)
  (chunk: seq a ) : nseq a l :=
 let idx_start := (chunk_len * chunk_num)%nat in
 let out_len := array_get_chunk_len s chunk_len chunk_num in
 update_sub s idx_start out_len (VectorDef.of_list chunk).

Instance nseq_default {A : Type} {l : nat} `{Default A} : Default (nseq A l) := {
    default := array_new l
  }.
Definition array_default {A : Type} {l : nat} `{Default A} : nseq A l := default.

Definition array_to_seq  {A : Type} {l : nat} (s : nseq A l) : seq A := VectorDef.to_list s.

Definition array_create {A : Type} `{Default A} (n : nat)  : nseq A n := array_new n.

Definition array_update_slice
  {a : Type}
 `{Default a}
  {l : nat}
  (out: nseq a l)
  (start_out: nat)
  (input: seq a)
  (start_in: nat)
  (len: nat)
    : nseq a (array_len out)
  :=
  update_sub out start_out len (VectorDef.of_list input).

Definition array_update
  {a: Type}
 `{Default a}
  {len: nat}
  (s: nseq a len)
  (start : nat)
  (start_s: seq a)
    : nseq a len :=
    update_sub s start (length start_s) (VectorDef.of_list start_s).

Definition array_update_start
  {a: Type}
 `{Default a}
  {len: nat}
  (s: nseq a len)
  (start_s: seq a)
    : nseq a len :=
    update_sub s 0 (length start_s) (VectorDef.of_list start_s).

(*** Seq *)

Definition public_byte_seq := seq int8.
Definition byte_seq := seq int8.

(**** Unsafe functions *)
Definition seq_new {A: Type} `{Default A} (len: nat) : seq A :=
  VectorDef.to_list (VectorDef.const default len).
Definition seq_with_capacity  {A: Type} (len: nat) : seq A :=
    [].

Definition seq_create {A: Type} `{Default A} (len: nat) : seq A := seq_new len.

Definition seq_reserve  {A: Type} (s : seq A) (additional : nat) : seq A :=
    s.

Definition seq_len {A: Type} (s: seq A) : N := N.of_nat (length s).


Definition seq_index {A: Type} `{Default A} (s: seq A) {WS : MachineIntegers.WORDSIZE} (i : int) :=
  List.nth (Z.to_nat (unsigned i)) s default.

(* Definition seq_index {A: Type} `{Default A} (s: seq A) (i : nat) := *)
(*   List.nth i s default. *)

Definition seq_new_ {A: Type} (init : A) (len: nat) : seq A :=
  VectorDef.to_list (VectorDef.const init len).

(* Automatic conversion from nseq/vector/array to seq/list *)
Global Coercion VectorDef.to_list : VectorDef.t >-> list.

Definition list_len := length.

Fixpoint array_from_list (A: Type) (l: list A) : nseq A (length l) :=
  match l return (nseq A (length l)) with
  | [] => VectorDef.nil A
  | x :: xs => VectorDef.cons A x (length xs) (array_from_list A xs)
  end.

(* automatic conversion from list to array *)
Global Coercion array_from_list : list >-> nseq.


(**** Array manipulation *)


Open Scope nat_scope.


(* Definition array_upd {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) (new_v: A) : lseq A len := List.upd s i new_v. *)


(* Sanity check *)
(* Compute (to_list (update_sub [1;2;3;4;5] 0 4 (of_list [9;8;7;6;12]))). *)

Definition array_from_seq
  {a: Type}
 `{Default a}
  (out_len:nat)
  (input: seq a)
  (* {H : List.length input = out_len} *)
    : nseq a out_len :=
    let out := VectorDef.const default out_len in
    update_sub out 0 (out_len - 1) input.
  (* VectorDef.of_list input. *)

Global Coercion array_from_seq : seq >-> nseq.










(**** Seq manipulation *)

Definition seq_slice
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (len: nat)
    : seq a :=
  array_from_seq len (slice s start (start + len)).

Definition seq_into_slice
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (len: nat)
    : seq a :=
  array_from_seq len (slice s start (start + len)).

Definition seq_slice_range
  {a: Type}
 `{Default a}
  (input: seq a)
  (start_fin:(uint_size * uint_size))
    : seq a :=
  seq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin)).

Definition seq_into_slice_range
  {a: Type}
 `{Default a}
  (input: seq a)
  (start_fin:(uint_size * uint_size))
    : seq a :=
  seq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin)).

Definition seq_split_off
           {a: Type}
           `{Default a}
           (input: seq a)
           (pos : uint_size)
  : seq a * seq a :=
  (seq_slice input 0 (from_uint_size pos),
   seq_slice input (from_uint_size pos) (length input)).

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

Definition seq_concat_owned
  {a : Type}
  (s1 :seq a)
  (s2: seq a)
  : seq a :=
  seq_concat s1 s2.

Definition seq_push
  {a : Type}
  (s1 :seq a)
  (s2: a)
  : seq a :=
  VectorDef.of_list (s1 ++ [s2]).

Definition seq_push_owned
  {a : Type}
  (s1 :seq a)
  (s2: a)
  : seq a :=
  seq_push s1 s2.

Definition seq_from_slice
  {a: Type}
 `{Default a}
  (input: seq a)
  (start: uint_size)
  (fin : uint_size)
  : seq a :=
  let out := array_new_ (default) (length input) in
    update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) (VectorDef.of_list (slice input (from_uint_size start) (from_uint_size fin))).

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
Definition seq_from_public_seq {A} (l : seq A) := l.

Module IntToHex.
  Require Import Coq.Numbers.HexadecimalString.

  (* Compute Number.IntHexadecimal 2. *)


  Definition positive_to_hex (p : positive) : Hexadecimal.uint.
  Proof.
    induction p.
    - exact (Hexadecimal.Little.succ_double IHp).
    - exact (Hexadecimal.Little.double IHp).
    - exact (Hexadecimal.D1 Hexadecimal.Nil).
  Defined.

  Definition int_to_hex (n : int8) : Hexadecimal.int.
    destruct n as [n _].
    destruct n.
    + exact (Hexadecimal.Pos Hexadecimal.zero).
    + exact (Hexadecimal.Pos (positive_to_hex p)).
    + exact (Hexadecimal.Neg (positive_to_hex p)).
  Defined.

  Require Import Hexadecimal Ascii String.

  Definition string_of_uint_digit (d:uint) :=
    match d with
    | Nil => EmptyString
    | D0 d => String "0" EmptyString
    | D1 d => String "1" EmptyString
    | D2 d => String "2" EmptyString
    | D3 d => String "3" EmptyString
    | D4 d => String "4" EmptyString
    | D5 d => String "5" EmptyString
    | D6 d => String "6" EmptyString
    | D7 d => String "7" EmptyString
    | D8 d => String "8" EmptyString
    | D9 d => String "9" EmptyString
    | Da d => String "a" EmptyString
    | Db d => String "b" EmptyString
    | Dc d => String "c" EmptyString
    | Dd d => String "d" EmptyString
    | De d => String "e" EmptyString
    | Df d => String "f" EmptyString
    end.

  Definition string_of_uint (d:uint) :=
    match d with
    | Nil => EmptyString
    | D0 Nil | D1 Nil | D2 Nil | D3 Nil | D4 Nil | D5 Nil | D6 Nil | D7 Nil | D8 Nil | D9 Nil | Da Nil | Db Nil | Dc Nil | Dd Nil | De Nil | Df Nil => String "0" (string_of_uint_digit d)
    | D0 d => String "0" (string_of_uint_digit d)
    | D1 d => String "1" (string_of_uint_digit d)
    | D2 d => String "2" (string_of_uint_digit d)
    | D3 d => String "3" (string_of_uint_digit d)
    | D4 d => String "4" (string_of_uint_digit d)
    | D5 d => String "5" (string_of_uint_digit d)
    | D6 d => String "6" (string_of_uint_digit d)
    | D7 d => String "7" (string_of_uint_digit d)
    | D8 d => String "8" (string_of_uint_digit d)
    | D9 d => String "9" (string_of_uint_digit d)
    | Da d => String "a" (string_of_uint_digit d)
    | Db d => String "b" (string_of_uint_digit d)
    | Dc d => String "c" (string_of_uint_digit d)
    | Dd d => String "d" (string_of_uint_digit d)
    | De d => String "e" (string_of_uint_digit d)
    | Df d => String "f" (string_of_uint_digit d)
    end.

  Definition string_of_int (d: MachineIntegers.int) :=
    match int_to_hex d with
    | Pos d => string_of_uint d
    | Neg d => String "-" (string_of_uint d)
    end.
End IntToHex.

Fixpoint seq_to_hex (l : seq int8) :=
  match l with
  | [] => String.EmptyString
  | (x :: xs) => String.append (IntToHex.string_of_int x) (seq_to_hex xs)
  end.

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
  divs_int (repr (Z.of_nat (length l))) chunk_size.

(* Until #84 is fixed this returns an empty sequence if not enough *)
Definition seq_get_exact_chunk {a} (l : seq a) (chunk_size chunk_num: uint_size) : seq a :=
  let '(len, chunk) := seq_get_chunk l (from_uint_size chunk_size) (from_uint_size chunk_num) in
  if eq_int len chunk_size then [] else chunk.

Definition seq_set_exact_chunk {a} `{H : Default a} := @seq_set_chunk a H.

Definition seq_get_remainder_chunk : forall {a}, seq a -> uint_size -> seq a :=
  fun _ l chunk_size =>
    let chunks := seq_num_chunks l (from_uint_size chunk_size) in
    let last_chunk := if 0 <? chunks then
      chunks - 1
    else 0 in
    let (len, chunk) := seq_get_chunk l (from_uint_size chunk_size) last_chunk in
    if eq_int len chunk_size then
      []
    else chunk.

Fixpoint seq_xor_ {WS : MachineIntegers.WORDSIZE} (x : seq int) (y : seq int) : seq int :=
  match x, y with
  | (x :: xs), (y :: ys) => xor_int x y :: (seq_xor_ xs ys)
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

Fixpoint seq_declassify {WS: MachineIntegers.WORDSIZE} (x : seq (@int WS)) : seq int := (* uint_size *)
  match x with
  | [] => []
  | (x :: xs) => declassify x :: seq_declassify xs
  end.

(**** Numeric operations *)

(* takes two nseq's and joins them using a function op : a -> a -> a *)
Definition array_join_map
  {a: Type}
 `{Default a}
  {len: nat}
  (op: a -> a -> a)
  (s1: nseq a len)
  (s2 : nseq a len) :=
  let out := s1 in
  foldi (usize 0) (usize len) (fun i out =>
    let i := from_uint_size i in
    array_upd out i (op (array_index s1 i) (array_index s2 i))
  ) out.

Infix "array_xor" := (array_join_map xor_int) (at level 33) : hacspec_scope.
Infix "array_add" := (array_join_map add_int) (at level 33) : hacspec_scope.
Infix "array_minus" := (array_join_map sub_int) (at level 33) : hacspec_scope.
Infix "array_mul" := (array_join_map mul_int) (at level 33) : hacspec_scope.
Infix "array_div" := (array_join_map divs_int) (at level 33) : hacspec_scope.
Infix "array_or" := (array_join_map or_int) (at level 33) : hacspec_scope.
Infix "array_and" := (array_join_map and_int) (at level 33) : hacspec_scope.

Definition array_eq_
  {a: Type}
  {len: nat}
  (eq: a -> a -> bool)
  (s1: nseq a len)
  (s2 : nseq a len)
    : bool := Vector.eqb _ eq s1 s2.

Infix "array_eq" := (array_eq_ eq) (at level 33) : hacspec_scope.
Infix "array_neq" := (fun s1 s2 => negb (array_eq_ eq s1 s2)) (at level 33) : hacspec_scope.


(**** Integers to arrays *)

Definition uint16_word_t := nseq uint8 2.
Definition uint32_word_t := nseq uint8 4.
Definition uint64_word_t := nseq uint8 8.
Definition uint128_word_t := nseq uint8 16.

Definition u16_word_t := nseq uint8 2.
Definition u32_word_t := nseq uint8 4.
Definition u64_word_t := nseq uint8 8.
Definition u128_word_t := nseq uint8 16.

Axiom uint16_to_le_bytes : int16 -> uint16_word_t.
Axiom uint16_to_be_bytes : int16 -> uint16_word_t.

Axiom uint16_from_le_bytes : uint16_word_t -> int16.
Axiom uint16_from_be_bytes : uint16_word_t -> int16.

Axiom uint32_to_le_bytes : int32 -> uint32_word_t.
Axiom uint32_to_be_bytes : int32 -> uint32_word_t.
Axiom uint32_from_le_bytes : uint32_word_t -> int32.
Axiom uint32_from_be_bytes : uint32_word_t -> int32.

Axiom uint64_to_le_bytes : int64 -> uint64_word_t.
Axiom uint64_to_be_bytes : int64 -> uint64_word_t.
Axiom uint64_from_le_bytes : uint64_word_t -> int64.
Axiom uint64_from_be_bytes : uint64_word_t -> int64.

Axiom uint128_to_le_bytes : int128 -> uint128_word_t.
Axiom uint128_to_be_bytes : int128 -> uint128_word_t.
Axiom uint128_from_le_bytes : uint128_word_t -> int128.
Axiom uint128_from_be_bytes : uint128_word_t -> int128.

Axiom u16_to_le_bytes : int16 -> nseq int8 2.
Axiom u16_to_be_bytes : int16 -> nseq int8 2.
Axiom u16_from_le_bytes : nseq int8 2 -> int16.
Axiom u16_from_be_bytes : nseq int8 2 -> int16.

Axiom u32_to_le_bytes : int32 -> nseq int8 4.
Axiom u32_to_be_bytes : int32 -> nseq int8 4.
Axiom u32_from_le_bytes : nseq int8 4 -> int32.
Axiom u32_from_be_bytes : nseq int8 4 -> int32.

Axiom u64_to_le_bytes : int64 -> nseq int8 8.
Axiom u64_from_le_bytes : nseq int8 8 -> int64.

Axiom u128_to_le_bytes : int128 -> nseq int8 16.
Axiom u128_to_be_bytes : int128 -> nseq int8 16.
Axiom u128_from_le_bytes : nseq int8 16 -> int128.
Axiom u128_from_be_bytes : nseq int8 16 -> int128.


(*** Nats *)


Definition nat_mod (p : Z) : Set := GZnZ.znz p.


Definition nat_mod_equal {p} (a b : nat_mod p) : bool :=
  Z.eqb (GZnZ.val p a) (GZnZ.val p b).

Definition nat_mod_zero {p} : nat_mod p := GZnZ.zero p.
Definition nat_mod_one {p} : nat_mod p := GZnZ.one p.
Definition nat_mod_two {p} : nat_mod p := GZnZ.mkznz p _ (GZnZ.modz p 2).


(* convenience coercions from nat_mod to Z and N *)
(* Coercion Z.of_N : N >-> Z. *)

Definition nat_mod_add {n : Z} (a : nat_mod n) (b : nat_mod n) : nat_mod n := GZnZ.add n a b.

Infix "+%" := nat_mod_add (at level 33) : hacspec_scope.

Definition nat_mod_mul {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.mul n a b.
Infix "*%" := nat_mod_mul (at level 33) : hacspec_scope.

Definition nat_mod_sub {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.sub n a b.
Infix "-%" := nat_mod_sub (at level 33) : hacspec_scope.

Definition nat_mod_div {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.div n a b.
Infix "/%" := nat_mod_div (at level 33) : hacspec_scope.

(* A % B = (a * B + r) *)

Definition nat_mod_neg {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.opp n a.

Definition nat_mod_inv {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.inv n a.

Definition nat_mod_exp_def {p : Z} (a:nat_mod p) (n : nat) : nat_mod p :=
  let fix exp_ (e : nat_mod p) (n : nat) :=
    match n with
    | 0%nat => nat_mod_one
    | S n => nat_mod_mul a (exp_ a n)
    end in
  exp_ a n.

Definition nat_mod_exp {WS : MachineIntegers.WORDSIZE} {p} a n := @nat_mod_exp_def p a (Z.to_nat (unsigned n)).
Definition nat_mod_pow {WS : MachineIntegers.WORDSIZE} {p} a n := @nat_mod_exp_def p a (Z.to_nat (unsigned n)).
Definition nat_mod_pow_self {p} a n := @nat_mod_exp_def p a (Z.to_nat (from_uint_size n)).

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

Definition nat_mod_from_literal (m : Z) (x:int128) : nat_mod m := nat_mod_from_secret_literal x.

Axiom nat_mod_to_byte_seq_le : forall {n : Z}, nat_mod n -> seq int8.
Axiom nat_mod_to_byte_seq_be : forall {n : Z}, nat_mod n -> seq int8.
Axiom nat_mod_to_public_byte_seq_le : forall (n : Z), nat_mod n -> seq int8.
Axiom nat_mod_to_public_byte_seq_be : forall (n : Z), nat_mod n -> seq int8.

Definition nat_mod_bit {n : Z} (a : nat_mod n) (i : uint_size) :=
  Z.testbit (GZnZ.val n a) (from_uint_size i).

(* Alias for nat_mod_bit *)
Definition nat_get_mod_bit {p} (a : nat_mod p) := nat_mod_bit a.
Definition nat_mod_get_bit {p} (a : nat_mod p) n :=
  if (nat_mod_bit a n)
  then @nat_mod_one p
  else @nat_mod_zero p.

(*
Definition nat_mod_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_mod_to_bytes_le len n'*)

(* Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n' *)


Axiom nat_mod_from_byte_seq_le : forall  {A n}, seq A -> nat_mod n.
Axiom most_significant_bit : forall {m}, nat_mod m -> uint_size -> uint_size.


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
    cast '(a, c) := ('a, 'c)
  }.

  Global Instance cast_option {A B} `{Cast A B} : Cast (option A) (option B) := {
    cast a := match a with Some a => Some ('a) | None => None end
  }.

  Global Instance cast_option_b {A B} `{Cast A B} : Cast A (option B) := {
    cast a := Some ('a)
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
    cast n := repr (unsigned n)
  }.
  Global Instance cast_int8_to_int32 : Cast int8 int32 := {
    cast n := repr (signed n)
  }.

  Global Instance cast_uint8_to_uint32 : Cast uint8 uint32 := {
    cast n := repr (unsigned n)
  }.

  Global Instance cast_int_to_nat `{WS : MachineIntegers.WORDSIZE} : Cast (@int WS) nat := {
    cast n := Z.to_nat (signed n)
  }.

  Close Scope hacspec_scope.
End Casting.


Global Arguments pair {_ _} & _ _.
Global Arguments id {_} & _.
Section Coercions.
  (* First, in order to have automatic coercions for tuples, we add bidirectionality hints: *)

  (* Integer coercions *)
  (* We have nat >-> N >-> Z >-> int/int32 *)
  (* and uint >-> Z *)
  (* and N >-> nat *)

  Global Coercion N.to_nat : N >-> nat.
  Global Coercion Z.of_N : N >-> Z.

  (* Definition repr_int {WS : MachineIntegers.WORDSIZE} (n : Z) : int := repr n. *)
  (* About repr. *)
  (* Global Coercion repr : Z >-> T. (* int. *) *)

  Definition temp_int_type `{WS : MachineIntegers.WORDSIZE} : Type := @int WS.

  Definition int8_type := @int_type MachineIntegers.WORDSIZE8.
  Definition Z_to_int8 (n : Z) : int8_type := repr n.
  Global Coercion  Z_to_int8 : Z >-> int8_type.
  Set Printing All.
  Check (fun (a : Z) => (a : int8_type) : int8).

  
  Definition Z_to_int `{WS : MachineIntegers.WORDSIZE} (n : Z) : @int_type WS := repr n.
  Global Coercion  Z_to_int : Z >-> int_type.
  Check (fun (a : Z) => (a : @int_type _) : int8).
  Check (forall (a : Z), (a : @int_type _)).
  Check ((2%Z : IntegerType int32) : int32).

  Definition Z_to_uint_size (n : Z) : uint_size := repr n.
  Global Coercion Z_to_uint_size : Z >-> uint_size.
  Definition Z_to_int_size (n : Z) : int_size := repr n.
  Global Coercion Z_to_int_size : Z >-> int_size.

  Definition N_to_int `{WS : MachineIntegers.WORDSIZE} (n : N) : @int WS := repr (Z.of_N n).
  Global Coercion N.of_nat : nat >-> N.
  Global Coercion N_to_int : N >-> IntegerType.
  Definition N_to_uint_size (n : Z) : uint_size := repr n.
  Global Coercion N_to_uint_size : Z >-> uint_size.
  Global Coercion nat_to_int `{WS : MachineIntegers.WORDSIZE} (n : nat) : @int WS := repr (Z.of_nat n).

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

  Definition int_in_nat_mod {m : Z} `{WS: MachineIntegers.WORDSIZE} (x:@int WS) : nat_mod m.
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
  Global Coercion int_in_nat_mod : IntegerType >-> nat_mod.

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


Definition uint8_equal : int8 -> int8 -> bool := eqb.

Definition nat_mod_val (p : Z) (a : nat_mod p) : Z := GZnZ.val p a.

Theorem nat_mod_eqb_spec : forall {p} (a b : nat_mod p), Z.eqb (nat_mod_val p a) (nat_mod_val p b) = true <-> a = b.
Proof.
  split ; intros.
  - apply Z.eqb_eq in H.
    destruct a, b ; apply (GZnZ.zirr p val val0 inZnZ inZnZ0 H).
  - subst.
    apply Z.eqb_eq.
    reflexivity.
Qed.

Global Instance nat_mod_eqdec {p} : EqDec (nat_mod p) := {
  eqb a b := Z.eqb (nat_mod_val p a) (nat_mod_val p b);
  eqb_leibniz := nat_mod_eqb_spec;
}.

Global Instance nat_mod_comparable `{p : Z} : Comparable (nat_mod p) :=
  lt_eq_comparable (fun a b => Z.ltb (nat_mod_val p a) (nat_mod_val p b)).

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

Global Instance unit_eqdec : EqDec unit := {
  eqb := fun _ _ => true ;
  eqb_leibniz := fun 'tt 'tt => (conj (fun _ => eq_refl) (fun _ => eq_refl)) ;
}.

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
    apply Bool.andb_true_eq in H1. destruct H1.
    symmetry in H1. apply (eqb_leibniz a0 a) in H1.
    symmetry in H2. apply (eqb_leibniz b0 b) in H2.
    rewrite H1, H2. reflexivity.
  - inversion_clear H1. now do 2 rewrite eqb_refl.
Defined.

Fixpoint seq_ltb {A} `{EqDec A} `{Comparable A} (a b : seq A) : bool :=
  match a , b with
  | [] , [] => true
  | x :: xs , y :: ys => if eqb x y then seq_ltb xs ys else ltb x y
  | _ , _ => false
  end.           
  
Global Instance seq_comparable {A} `{EqDec A} `{Comparable A} : Comparable (seq A) :=
  lt_eq_comparable seq_ltb.


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

Definition u64_to_be_bytes' : int64 -> nseq int8 8 :=
  fun k => array_from_list (int8) [@nat_to_int MachineIntegers.WORDSIZE8 (nat_be_range 4 k 7) ;
                               @nat_to_int MachineIntegers.WORDSIZE8 (nat_be_range 4 k 6) ;
                               @nat_to_int MachineIntegers.WORDSIZE8 (nat_be_range 4 k 5) ;
                               @nat_to_int MachineIntegers.WORDSIZE8 (nat_be_range 4 k 4) ;
                               @nat_to_int MachineIntegers.WORDSIZE8 (nat_be_range 4 k 3) ;
                               @nat_to_int MachineIntegers.WORDSIZE8 (nat_be_range 4 k 2) ;
                               @nat_to_int MachineIntegers.WORDSIZE8 (nat_be_range 4 k 1) ;
                               @nat_to_int MachineIntegers.WORDSIZE8 (nat_be_range 4 k 0)].

Open Scope hacspec_scope.

Definition u64_from_be_bytes_fold_fun (i : int8) (s : nat × int64) : nat × int64 :=
  let (n,v) := s in
  (S n, v .+ (repr (Z.of_nat (int8_to_nat i) * 2 ^ (4 * n)))).

Definition u64_from_be_bytes' : nseq int8 8 -> int64 :=
  (fun v => snd (VectorDef.fold_right u64_from_be_bytes_fold_fun v (0, repr 0))).

Definition u64_to_be_bytes : int64 -> nseq int8 8 := u64_to_be_bytes'.
Definition u64_from_be_bytes : nseq int8 8 -> int64 := u64_from_be_bytes'.

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
Global Instance uint8_default : Default uint8 := _.
Global Instance nat_mod_default {p : Z} : Default (nat_mod p) := {
  default := nat_mod_zero
}.
Global Instance prod_default {A B} `{Default A} `{Default B} : Default (A × B) := {
  default := (default, default)
}.

Global Instance seq_default {A} : Default (seq A) := {
  default := seq_with_capacity 0
}.
