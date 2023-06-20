Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".
Global Set Warnings "-notation-overridden,-ambiguous-paths".

Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Sumbool.

From mathcomp Require Import fintype.

From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset fmap.

From mathcomp Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith List.
Import List.ListNotations.

(********************************************************)
(*   Implementation of all Hacspec library functions    *)
(* for Both types.                                      *)
(********************************************************)

(*** Integers *)

Declare Scope hacspec_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.

Open Scope bool_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.
Open Scope list_scope.

Import choice.Choice.Exports.

Definition lift3_both_ {A B C D : choice_type} {L} {I} (f : A -> B -> C -> D) (x : both L I A) (y : both L I B) (z : both L I C) :=
  bind_both_ x (fun x' =>
  bind_both_ y (fun y' =>
  bind_both_ z (fun z' =>
  lift_to_both (f x' y' z')))).

Notation lift3_both(*  {A B C D : choice_type} {L1 L2 L3 L4 : {fset Location}} {I1 I2 I3 I4 : Interface} (f : A -> B -> C -> D) (x : both L1 I1 A) (y : both L2 I2 B) (z : both L3 I3 C) *)
  (*       `{H_loc_incl_x : List.incl L1 L4} `{H_opsig_incl_x : List.incl I1 I4} *)
  (*       `{H_loc_incl_y : List.incl L2 L4} `{H_opsig_incl_y : List.incl I2 I4} *)
  (*       `{H_loc_incl_z : List.incl L3 L4} `{H_opsig_incl_z : List.incl I3 I4} *)
  (* : both L4 I4 D *) :=
  (fun (f : _ -> _ -> _ -> _) (x : both _ _ _) (y : both _ _ _) (z : both _ _ _) =>
  bind_both (H_loc_incl := _) (H_opsig_incl := _) x (fun x' =>
  bind_both (H_loc_incl := _) (H_opsig_incl := _) y (fun y' =>
  bind_both (H_loc_incl := _) (H_opsig_incl := _) z (fun z' =>
  lift_to_both (f x' y' z'))))).

Definition lift2_both_ {A B C : choice_type} {L} {I} (f : A -> B -> C) (x : both L I A) (y : both L I B) :=
  bind_both_ x (fun x' =>
  bind_both_ y (fun y' =>
  lift_to_both (f x' y'))).

Notation lift2_both (* {A B C : choice_type} {L1 L2 L3 : {fset Location}} {I1 I2 I3 : Interface} *) (* (f : A -> B -> C) (x : both L1 I1 A) (y : both L2 I2 B) *)
  (*       `{H_loc_incl_x : List.incl L1 L3} `{H_opsig_incl_x : List.incl I1 I3} *)
  (*       `{H_loc_incl_y : List.incl L2 L3} `{H_opsig_incl_y : List.incl I2 I3} *)
  (* : both L3 I3 C *)
  :=
  (fun (f : _ -> _ -> _) (x : both _ _ _) (y : both _ _ _) =>
  bind_both (H_loc_incl := _) (H_opsig_incl := _) x (fun x' =>
  bind_both (H_loc_incl := _) (H_opsig_incl := _) y (fun y' =>
  lift_to_both (f x' y')))).

Definition lift1_both_ {A B C : choice_type} {L} {I} (f : A -> B) (x : both L I A) :=
  bind_both_ x (fun x' =>
  lift_to_both (f x')).

Notation lift1_both (* {A B C : choice_type} {L1 L2 : {fset Location}} {I1 I2 : Interface} (f : A -> B) (x : both L1 I1 A) *)
        (* `{H_loc_incl_x : List.incl L1 L2} `{H_opsig_incl_x : List.incl I1 I2} *)
  (* : both L2 I2 B *)
  :=
  (fun f x => bind_both (H_loc_incl := _) (H_opsig_incl := _) x (fun x' => lift_to_both (f x'))).

  Notation int_add := (lift2_both (@int_add _)).
  Check (int_add (lift_to_both (repr _ 3) : both0 _) (lift_to_both (repr _ 4) : both0 _)).

  Notation int_sub := (lift2_both (int_sub : int _ -> int _ -> int _)).
  Notation int_opp := (lift1_both (int_opp : int _ -> int _)).
  Notation int_mul := (lift2_both (int_mul : int _ -> int _ -> int _)).
  Notation int_div := (lift2_both (int_div : int _ -> int _ -> int _)).
  Notation int_mod := (lift2_both (int_mod : int _ -> int _ -> int _)).
  Notation int_xor := (lift2_both (int_xor : int _ -> int _ -> int _)).
  Notation int_and := (lift2_both (int_and : int _ -> int _ -> int _)).
  Notation int_or := (lift2_both (int_or : int _ -> int _ -> int _)).
  Notation int_not := (lift1_both (int_not : int _ -> int _)).
  Notation cast_int := (lift1_both (fun (n : int _) => repr _ (unsigned n))).
(* End IntType. *)

Notation secret := (lift1_both secret).

Infix ".%%" := int_modi (at level 40, left associativity) : Z_scope.
Infix ".+" := int_add (at level 77) : hacspec_scope.
Infix ".-" := int_sub (at level 77) : hacspec_scope.
Notation "-" := int_opp (at level 77) : hacspec_scope.
Infix ".*" := int_mul (at level 77) : hacspec_scope.
Infix "./" := int_div (at level 77) : hacspec_scope.
Infix ".%" := int_mod (at level 77) : hacspec_scope.
Infix ".^" := int_xor (at level 77) : hacspec_scope.
Infix ".&" := int_and (at level 77) : hacspec_scope.
Infix ".|" := int_or (at level 77) : hacspec_scope.
Notation "'not'" := int_not (at level 77) : hacspec_scope.

(* Section Uint. *)
  Notation uint8_declassify := (lift1_both uint8_declassify).
  Notation int8_declassify := (lift1_both int8_declassify).
  Notation uint16_declassify := (lift1_both uint16_declassify).
  Notation int16_declassify := (lift1_both int16_declassify).
  Notation uint32_declassify := (lift1_both uint32_declassify).
  Notation int32_declassify := (lift1_both int32_declassify).
  Notation uint64_declassify := (lift1_both uint64_declassify).
  Notation int64_declassify := (lift1_both int64_declassify).
  Notation uint128_declassify := (lift1_both uint128_declassify).
  Notation int128_declassify := (lift1_both int128_declassify).

  Notation uint8_classify := (lift1_both uint8_classify).
  Notation int8_classify := (lift1_both int8_classify).
  Notation uint16_classify := (lift1_both uint16_classify).
  Notation int16_classify := (lift1_both int16_classify).
  Notation uint32_classify := (lift1_both uint32_classify).
  Notation int32_classify := (lift1_both int32_classify).
  Notation uint64_classify := (lift1_both uint64_classify).
  Notation int64_classify := (lift1_both int64_classify).
  Notation uint128_classify := (lift1_both uint128_classify).
  Notation int128_classify := (lift1_both int128_classify).

  (* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
   *)

  Notation declassify_usize_from_uint8 := (lift1_both declassify_usize_from_uint8).
  Notation declassify_u32_from_uint32 := (lift1_both declassify_u32_from_uint32).

  Notation uint8_rotate_left := (lift2_both uint8_rotate_left).

  Notation uint8_rotate_right := (lift2_both uint8_rotate_right).

  Notation uint16_rotate_left := (lift2_both uint16_rotate_left).

  Notation uint16_rotate_right := (lift2_both uint16_rotate_right).

  Notation uint32_rotate_left := (lift2_both uint32_rotate_left).

  Notation uint32_rotate_right := (lift2_both uint32_rotate_right).

  Notation uint64_rotate_left := (lift2_both uint64_rotate_left).

  Notation uint64_rotate_right := (lift2_both uint64_rotate_right).

  Notation uint128_rotate_left := (lift2_both uint128_rotate_left).

  Notation uint128_rotate_right := (lift2_both uint128_rotate_right).
  Notation usize_shift_right_ := (lift2_both (fun u s => u usize_shift_right s)).

  Notation usize_shift_left_ :=
    (fun (u: both0 uint_size) (s: both0 int32) =>
    {|
      is_pure := (is_pure u) usize_shift_left (is_pure s) ;
      is_state :=
      {code
         temp_u ← is_state u ;;
         temp_s ← is_state s ;;
         ret (temp_u usize_shift_left temp_s)
      }
    |}).
  (* Next Obligation. *)
  (*   intros. *)
  (*   pattern_both Hb Hf Hg. *)
  (*   apply (@r_bind_trans_both (uint_size) (uint_size)). *)
  (*   subst Hf Hg Hb ; hnf. *)
  (*   pattern_both Hb Hf Hg. *)
  (*   apply (@r_bind_trans_both (int32)). *)
  (*   subst Hf Hg Hb ; hnf. *)
  (*   apply r_ret. *)
  (*   easy. *)
  (* Qed. *)

  (**** Operations *)

  Notation shift_left_ := (lift2_both shift_left_).
  Notation shift_right_ := (lift2_both shift_right_).

(* End Uint. *)

Infix "usize_shift_right" := (usize_shift_right_) (at level 77) : hacspec_scope.
Infix "usize_shift_left" := (usize_shift_left_) (at level 77) : hacspec_scope.

Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope.
Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope.

(*** Loops *)

Section Loops.

  Fixpoint foldi_
           {acc : choice_type}
           (fuel : nat)
           (i : uint_size)
           {L I}
           (f: (uint_size) -> acc -> code L I (acc))
           (cur : acc) {struct fuel} : raw_code (acc) :=
    match fuel with
    | O => ret cur
    | S n' =>
        cur' ← f i cur ;;
        Si ← ret (Hacspec_Lib_Pre.int_add i one) ;;
        foldi_ n' Si f (cur')
    end.

  Lemma valid_foldi_ :
    forall {acc : choice_type} L I n i (f : uint_size -> acc -> code L I (acc)) init,
      ValidCode L I (foldi_ n i f init).
  Proof.
    induction n ; intros ; cbn ; ssprove_valid.
    apply f.
  Qed.

  Definition foldi_pre
             {acc: choice_type}
             (lo: uint_size)
             (hi: uint_size) (* {lo <= hi} *)
             {I L}
             (f: (uint_size) -> acc -> code I L (acc)) (* {i < hi} *)
             (init: acc) : raw_code (acc) :=
    match Z.sub (unsigned hi) (unsigned lo) with
    | Z0 => ret (init)
    | Zneg p => ret (init)
    | Zpos p => foldi_ (Pos.to_nat p) lo f init
    end.

  (* Fold done using natural numbers for bounds *)
  Fixpoint foldi_nat_
           {acc : choice_type}
           (fuel : nat)
           (i : nat)
           (f : nat -> acc -> raw_code (acc))
           (cur : acc) : raw_code (acc) :=
    match fuel with
    | O => ret (cur)
    | S n' =>
        cur' ← f i cur ;;
        foldi_nat_ n' (S i) f (cur')
    end.
  Definition foldi_nat
             {acc: choice_type}
             (lo: nat)
             (hi: nat) (* {lo <= hi} *)
             (f: nat -> acc -> raw_code (acc)) (* {i < hi} *)
             (init: acc) : raw_code (acc) :=
    match Nat.sub hi lo with
    | O => ret (init)
    | S n' => foldi_nat_ (S n') lo f init
    end.

  Lemma foldi__move_S :
    forall {acc: choice_type}
      (fuel : nat)
      (i : uint_size)
      {L I}
      (f : uint_size -> acc -> code L I (acc))
      (cur : acc),
      (cur' ← f i cur ;; Si ← ret (Hacspec_Lib_Pre.int_add i one) ;; foldi_ fuel Si f (cur')) = foldi_ (S fuel) i f cur.
  Proof. reflexivity. Qed.

  Lemma foldi__nat_move_S :
    forall {acc: choice_type}
      (fuel : nat)
      (i : nat)
      (f : nat -> acc -> raw_code (acc))
      (cur : acc),
      (cur' ← f i cur ;; foldi_nat_ fuel (S i) f (cur')) = foldi_nat_ (S fuel) i f cur.
  Proof. reflexivity. Qed.

  Lemma foldi__nat_move_S_append :
    forall {acc: choice_type}
      (fuel : nat)
      (i : nat)
      (f : nat -> acc -> raw_code (acc))
      (cur : acc),
      (cur' ← foldi_nat_ fuel i f (cur) ;; f (i + fuel) (cur')) = foldi_nat_ (S fuel) i f cur.
  Proof.

    induction fuel ; intros.
    - rewrite <- foldi__nat_move_S.
      unfold foldi_nat_.
      replace (fun cur' => @ret acc ((cur'))) with (fun cur' => @ret acc cur').
      2: {
        apply functional_extensionality.
        reflexivity.
      }
      rewrite bind_ret.
      unfold bind at 1.
      rewrite Nat.add_0_r.
      reflexivity.
    - rewrite <- foldi__nat_move_S.
      rewrite <- foldi__nat_move_S.
      rewrite bind_assoc.
      f_equal.
      apply functional_extensionality.
      intros.
      replace (i + S fuel) with (S i + fuel) by lia.
      rewrite IHfuel.
      reflexivity.
  Qed.

  Lemma foldi__nat_move_to_function :
    forall {acc: choice_type}
      (fuel : nat)
      (i : nat)
      (f : nat -> acc -> raw_code (acc))
      (cur : acc),
      foldi_nat_ fuel i (fun x => f (S x)) (cur) = foldi_nat_ fuel (S i) f cur.
  Proof.
    induction fuel ; intros.
    - reflexivity.
    - cbn.
      f_equal.
      apply functional_extensionality.
      intros.
      rewrite IHfuel.
      reflexivity.
  Qed.

  Lemma foldi__nat_move_to_function_add :
    forall {acc: choice_type}
      (fuel : nat)
      (i j : nat)
      (f : nat -> acc -> raw_code (acc))
      (cur : acc),
      foldi_nat_ fuel i (fun x => f (x + j)) (cur) = foldi_nat_ fuel (i + j) f cur.
  Proof.
    intros acc fuel i j. generalize dependent i.
    induction j ; intros.
    - rewrite Nat.add_0_r.
      replace (fun x : nat => f (x + 0)) with f.
      reflexivity.
      apply functional_extensionality.
      intros.
      now rewrite Nat.add_0_r.
    - replace (i + S j) with (S i + j) by lia.
      rewrite <- IHj.
      rewrite <- foldi__nat_move_to_function.
      f_equal.
      apply functional_extensionality.
      intros.
      f_equal.
      lia.
  Qed.

  Lemma raw_code_type_from_choice_type_id :
    forall (acc : choice_type) (x : raw_code (acc)),
      (cur' ← x ;;
       ret ((cur')))
      =
        x.
  Proof.
    intros.
    rewrite @bind_cong with (v := x) (g := @ret (acc)).
    rewrite bind_ret.
    reflexivity.
    reflexivity.

    apply functional_extensionality.
    intros.
    reflexivity.
  Qed.

  (* You can do one iteration of the fold by burning a unit of fuel *)
  Lemma foldi__move_S_fuel :
    forall {acc: choice_type}
      (fuel : nat)
      (i : uint_size)
      {L I}
      (f : uint_size -> acc -> code L I (acc))
      (cur : acc),
      (0 <= Z.of_nat fuel <= @wmax_unsigned U32)%Z ->
      (cur' ← foldi_ fuel i f cur ;;
       fuel_add_i ← ret (Hacspec_Lib_Pre.int_add (repr _ (Z.of_nat fuel)) i) ;;
       f fuel_add_i (cur')
      ) = foldi_ (S (fuel)) i f cur.
  Proof.
    intros acc fuel.
    induction fuel ; intros.
    - cbn.
      replace (repr _ 0%Z) with (@zero U32) by (apply word_ext ; reflexivity).
      (* unfold Hacspec_Lib_Pre.int_add. *)
      unfold Hacspec_Lib_Pre.int_add.
      rewrite add0w.
      rewrite raw_code_type_from_choice_type_id.
      reflexivity.
    - unfold foldi_.
      fold (@foldi_ acc fuel).

      rewrite bind_assoc.
      f_equal.
      apply functional_extensionality.
      intros.

      (* unfold Hacspec_Lib_Pre.int_add at 1 3. *)
      (* unfold lift_to_both, is_state at 1 3. *)
      unfold prog, lift_to_code.
      do 2 setoid_rewrite bind_rewrite.

      specialize (IHfuel (Hacspec_Lib_Pre.int_add i one) L I f (x)).



      replace (Hacspec_Lib_Pre.int_add (repr _ (Z.of_nat (S fuel))) _)
        with (Hacspec_Lib_Pre.int_add (repr _ (Z.of_nat fuel)) (Hacspec_Lib_Pre.int_add i one)).
      2 : {
        (* unfold int_add. *)
        unfold Hacspec_Lib_Pre.int_add.
        rewrite <- addwC.
        rewrite <- addwA.
        rewrite addwC.
        f_equal.
        apply word_ext.
        rewrite Z.add_1_l.
        rewrite Nat2Z.inj_succ.

        f_equal.
        f_equal.
        apply Zmod_small.
        unfold wmax_unsigned in H.
        unfold wbase in H.
        lia.
      }

      setoid_rewrite IHfuel.
      reflexivity.
      lia.
  Qed.

  (* You can do one iteration of the fold by burning a unit of fuel *)
  Lemma foldi__nat_move_S_fuel :
    forall {acc: choice_type}
      (fuel : nat)
      (i : nat)
      (f : nat -> acc -> raw_code (acc))
      (cur : acc),
      (0 <= Z.of_nat fuel <= @wmax_unsigned U32)%Z ->
      (cur' ← foldi_nat_ fuel i f cur ;; f (fuel + i)%nat (cur')) = foldi_nat_ (S fuel) i f cur.
  Proof.
    induction fuel ; intros.
    - cbn.
      rewrite raw_code_type_from_choice_type_id.
      reflexivity.
    - unfold foldi_nat_.
      fold (@foldi_nat_ acc fuel).
      rewrite bind_assoc.
      f_equal.
      apply functional_extensionality.
      intros.
      replace (S fuel + i)%nat with (fuel + (S i))%nat by (symmetry ; apply plus_Snm_nSm).
      rewrite IHfuel.
      + reflexivity.
      + lia.
  Qed.

  (* folds and natural number folds compute the same thing *)
  Lemma foldi_to_foldi_nat :
    forall {acc: choice_type}
      (lo: uint_size)
      (hi: uint_size) (* {lo <= hi} *)
      {L I}
      (f: (uint_size) -> acc -> code L I (acc)) (* {i < hi} *)
      (init: acc),
      (unsigned lo <= unsigned hi)%Z ->
      foldi_pre lo hi f init = foldi_nat (Z.to_nat (unsigned lo)) (Z.to_nat (unsigned hi)) (fun x => f (repr _ (Z.of_nat x))) init.
  Proof.
    intros.

    unfold foldi_pre.
    unfold foldi_nat.

    destruct (uint_size_as_nat hi) as [ hi_n [ hi_eq hi_H ] ] ; subst.
    rewrite (@unsigned_repr_alt U32 _ hi_H) in *.
    rewrite Nat2Z.id.

    destruct (uint_size_as_nat lo) as [ lo_n [ lo_eq lo_H ] ] ; subst.
    rewrite (@unsigned_repr_alt U32 _ lo_H) in *.
    rewrite Nat2Z.id.

    remember (hi_n - lo_n)%nat as n.
    apply f_equal with (f := Z.of_nat) in Heqn.
    rewrite (Nat2Z.inj_sub) in Heqn by (apply Nat2Z.inj_le ; apply H).
    rewrite <- Heqn.

    assert (H_bound : (Z.pred 0 < Z.of_nat n < @modulus U32)%Z) by lia.

    clear Heqn.
    induction n.
    - reflexivity.
    - pose proof (H_max_bound := modulus_range_helper _ (range_of_nat_succ _ H_bound)).
      rewrite <- foldi__nat_move_S_fuel by apply H_max_bound.
      cbn.
      rewrite SuccNat2Pos.id_succ.
      rewrite <- foldi__move_S_fuel by apply H_max_bound.

      destruct n.
      + cbn.
        replace (repr _ 0%Z) with (@zero U32) by (apply word_ext ; reflexivity).
        unfold Hacspec_Lib_Pre.int_add.
        rewrite add0w.
        reflexivity.
      + assert (H_bound_pred: (Z.pred 0 < Z.pos (Pos.of_succ_nat n) < @modulus U32)%Z) by lia.
        rewrite <- (IHn H_bound_pred) ; clear IHn.
        f_equal.
        * cbn in *.
          setoid_rewrite foldi__move_S.
          f_equal.
          lia.
        * apply functional_extensionality.
          intros.

          (* unfold int_add. *)

          setoid_rewrite bind_rewrite.
          replace (Hacspec_Lib_Pre.int_add _ _) with (@repr U32 (Z.of_nat (Init.Nat.add (S n) lo_n))). reflexivity.

          apply word_ext.

          replace (urepr _) with (@unsigned U32 (repr _ (Z.of_nat (S n)))) by reflexivity.
          replace (urepr _) with (@unsigned U32 (repr _ (Z.of_nat lo_n))) by reflexivity.
          do 2 rewrite unsigned_repr_alt by lia.
          rewrite Nat2Z.inj_add.
          reflexivity.
  Qed.

  Lemma foldi_nat_to_foldi :
    forall {acc: choice_type}
      (lo: nat)
      (hi: nat) (* {lo <= hi} *)
      {L I}
      (f: nat -> acc -> code L I (acc)) (* {i < hi} *)
      (init: acc),
      (lo <= hi) ->
      (Z.of_nat hi < @modulus U32)%Z ->
      (forall x, f x = f (from_uint_size (repr _ (Z.of_nat x)))) ->
      foldi_nat lo hi f init =
        foldi_pre (usize lo) (usize hi) (fun x => f (from_uint_size x)) init.
  Proof.
    intros.
    rewrite foldi_to_foldi_nat.
    2: {
      unfold nat_uint_sizeable.
      unfold usize, is_pure.
      unfold Hacspec_Lib_Pre.usize.

      do 2 rewrite wunsigned_repr.
      rewrite Zmod_small by (split ; [ lia | apply Z.le_lt_trans with (m := Z.of_nat hi) ; try apply inj_le ; assumption ]).
      rewrite Zmod_small by (split ; try easy ; lia).
      lia.
    }

    unfold nat_uint_sizeable.
    unfold usize, is_pure.
    unfold Hacspec_Lib_Pre.usize.

    do 2 rewrite wunsigned_repr.
    rewrite Zmod_small by (split ; [ lia | apply Z.le_lt_trans with (m := Z.of_nat hi) ; try apply inj_le ; assumption ]).
    rewrite Zmod_small by (split ; try easy ; lia).
    do 2 rewrite Nat2Z.id.

    f_equal.
    apply functional_extensionality. intros.
    rewrite <- H1.
    reflexivity.
  Qed.

  (* folds can be computed by doing one iteration and incrementing the lower bound *)
  Lemma foldi_nat_split_S :
    forall {acc: choice_type}
      (lo: nat)
      (hi: nat) (* {lo <= hi} *)
      (f: nat -> acc -> raw_code (acc)) (* {i < hi} *)
      (init: acc),
      (lo < hi)%nat ->
      foldi_nat lo hi f init = (cur' ← foldi_nat lo (S lo) f init ;; foldi_nat (S lo) hi f (cur')).
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

      rewrite raw_code_type_from_choice_type_id.
      reflexivity.
    - apply Nat.eqb_neq in hi_eq_lo.
      apply Nat.lt_gt_cases in hi_eq_lo.
      destruct hi_eq_lo.
      + lia.
      + rewrite (Nat.sub_succ_l (S lo)) by apply (Nat.lt_le_pred _ _ H0).
        rewrite Nat.sub_succ_l by apply (Nat.lt_le_pred _ _ H).
        replace ((S (hi - S lo))) with (hi - lo)%nat by lia.

        unfold foldi_nat_.
        fold (@foldi_nat_ acc).
        rewrite raw_code_type_from_choice_type_id.
        reflexivity.
  Qed.

  (* folds can be split at some valid offset from lower bound *)
  Lemma foldi_nat_split_add :
    forall (k : nat),
    forall {acc: choice_type}
      (lo: nat)
      (hi: nat) (* {lo <= hi} *)
      (f: nat -> acc -> raw_code (acc)) (* {i < hi} *)
      (init: acc),
    forall {guarantee: (lo + k <= hi)%nat},
      foldi_nat lo hi f init = (cur' ← foldi_nat lo (k + lo) f init ;; foldi_nat (k + lo) hi f (cur')).
  Proof.
    induction k ; intros.
    - cbn.
      unfold foldi_nat.
      rewrite Nat.sub_diag.
      cbn.
      reflexivity.
    - rewrite foldi_nat_split_S by lia.
      replace (S k + lo)%nat with (k + S lo)%nat by lia.
      specialize (IHk acc (S lo) hi f).

      rewrite bind_cong with (v := foldi_nat lo (S lo) (fun (x : nat) (x0 : acc) => f x x0) init) (g := fun v => (cur' ← foldi_nat (S lo) (k + S lo) (fun (x : nat) (x0 : acc) => f x x0) (v) ;;
                                                                                                             foldi_nat (k + S lo) hi (fun (x : nat) (x0 : acc) => f x x0)
                                                                                                                       (cur'))).

      rewrite <- bind_assoc.
      f_equal.

      rewrite <- foldi_nat_split_S by lia.
      reflexivity.

      reflexivity.

      apply functional_extensionality. intros. rewrite IHk by lia. reflexivity.
  Qed.

  (* folds can be split at some midpoint *)
  Lemma foldi_nat_split :
    forall (mid : nat), (* {lo <= mid <= hi} *)
    forall {acc: choice_type}
      (lo: nat)
      (hi: nat) (* {lo <= hi} *)
      (f: nat -> acc -> raw_code (acc)) (* {i < hi} *)
      (init: acc),
    forall {guarantee: (lo <= mid <= hi)%nat},
      foldi_nat lo hi f init = (cur' ← foldi_nat lo mid f init ;; foldi_nat mid hi f (cur')).
  Proof.
    intros.
    assert (mid_is_low_plus_constant : {k : nat | (mid = lo + k)%nat})  by (exists (mid - lo)%nat ; lia).
    destruct mid_is_low_plus_constant ; subst.
    rewrite Nat.add_comm.
    pose foldi_nat_split_add.
    apply foldi_nat_split_add.
    apply guarantee.
  Qed.

  (* folds can be split at some midpoint *)
  Lemma foldi_split :
    forall (mid : uint_size), (* {lo <= mid <= hi} *)
    forall {acc: choice_type}
      (lo: uint_size)
      (hi: uint_size) (* {lo <= hi} *)
      {L I}
      (f: uint_size -> acc -> code L I (acc)) (* {i < hi} *)
      (init: acc),
    forall {guarantee: (unsigned lo <= unsigned mid <= unsigned hi)%Z},
      foldi_pre lo hi f init = (cur' ← foldi_pre lo mid f init ;; foldi_pre mid hi f (cur')).
  Proof.
    intros.
    rewrite foldi_to_foldi_nat by lia.
    rewrite foldi_to_foldi_nat by lia.

    pose @foldi_to_foldi_nat.

    rewrite bind_cong with (v := foldi_nat (Z.to_nat (unsigned lo)) (Z.to_nat (unsigned mid))
                                           (fun x : nat => f (repr _ (Z.of_nat x))) init) (g := fun init => foldi_nat (Z.to_nat (unsigned mid)) (Z.to_nat (unsigned hi))
                                                                                                            (fun x : nat => f (repr _ (Z.of_nat x))) (init)).

    apply foldi_nat_split ; lia.
    reflexivity.
    apply functional_extensionality.
    intros.

    rewrite foldi_to_foldi_nat by lia.
    reflexivity.
  Qed.


  Lemma valid_foldi_pre :
    forall {acc : choice_type} (lo hi : int _) {L : {fset Location}} {I : Interface} (f : int _ -> _ -> code L I (_)),
      forall init : (_),
        ValidCode L I (foldi_pre (acc := acc) lo hi f init).
  Proof.
    intros.
    unfold foldi_pre.
    destruct (unsigned hi - unsigned lo)%Z.
    - ssprove_valid.
    - apply valid_foldi_.
    - ssprove_valid.
  Qed.

  Definition foldi
             {acc: choice_type}
             (lo: uint_size)
             (hi: uint_size) (* {lo <= hi} *)
             {L}
             {I}
             (f: (uint_size) -> acc -> code L I (acc))
             (init: acc)
    :
    code L I (acc) :=
    {| prog := foldi_pre lo hi f init;
      prog_valid := @valid_foldi_pre acc lo hi L I f init |}.

  Definition foldi'
             {acc: choice_type}
             (lo: uint_size)
             (hi: uint_size) (* {lo <= hi} *)
             {L1 L2 : {fset Location}} {H_loc_incl : List.incl L1 L2}
             {I1 I2 : Interface} {H_opsig_incl : List.incl I1 I2}
             (f: (uint_size) -> acc -> code L1 I1 (acc))
             (init: acc)
    :
    code L2 I2 (acc)
  .
    eapply lift_code_scope.
    apply (foldi lo hi f init).
    apply H_loc_incl.
    apply H_opsig_incl.
  Defined.

  Lemma valid_remove_back :
    forall x (xs : {fset Location}) I {ct} c,
      ValidCode (fset xs) I c ->
      @ValidCode (fset (xs ++ [x])) I ct c.
  Proof.
    intros.
    apply (valid_injectLocations) with (L1 := fset xs).
    - rewrite fset_cat.
      apply fsubsetUl.
    - apply H.
  Qed.

  Lemma list_constructor : forall {A : Type} (x : A) (xs : list A) (l : list A) (H : (x :: xs) = l), (l <> []).
  Proof.
    intros.
    subst.
    easy.
  Qed.

  Definition pop_back {A : Type} (l : list A) :=
    match (rev l) with
    | [] => []
    | (x :: xs) => rev xs ++ [x]
    end.

  Theorem pop_back_ignore_front : forall {A} (a : A) (l : list A), pop_back (a :: l) = a :: pop_back l.
  Proof.
    intros.
    induction l ; intros.
    - reflexivity.
    - unfold pop_back.
      destruct (rev (a :: a0 :: l)) eqn:orev.
      { apply f_equal with (f := @rev A) in orev.
        rewrite (rev_involutive) in orev.
        discriminate orev.
      }
      cbn in orev.

      destruct (rev (a0 :: l)) eqn:orev2.
      { apply f_equal with (f := @rev A) in orev2.
        rewrite (rev_involutive) in orev2.
        discriminate orev2.
      }
      cbn in orev2.
      rewrite orev2 in orev ; clear orev2.

      inversion_clear orev.
      rewrite rev_unit.
      reflexivity.
  Qed.

  Theorem pop_back_is_id : forall {A} (l : list A), l = pop_back l.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - destruct l.
      + reflexivity.
      + rewrite pop_back_ignore_front.
        rewrite <- IHl.
        reflexivity.
  Qed.

  Ltac valid_remove_back' :=
    match goal with
    | _ : _ |- (ValidCode (fset (?l)) _ _) =>
        rewrite (@pop_back_is_id _ l)
    end ;
    apply valid_remove_back.


  Lemma valid_remove_front :
    forall x xs I {ct} c,
      ValidCode (fset xs) I c ->
      @ValidCode (fset (x :: xs)) I ct c.
  Proof.
    intros.
    apply (@valid_injectLocations) with (L1 := fset xs).
    - replace (x :: xs) with (seq.cat [x] xs) by reflexivity.
      rewrite fset_cat.
      apply fsubsetUr.
    - apply H.
  Qed.

Theorem for_loop_unfold :
  forall c n,
  for_loop (fun m : nat => c m) (S n) =
    (c 0 ;; for_loop (fun m : nat => c (S m)) (n) ).
  cbn.
  induction n ; intros.
  - reflexivity.
  - unfold for_loop ; fold for_loop.
    cbn.
    rewrite IHn.
    rewrite bind_assoc.
    reflexivity.
Qed.

End Loops.

(*** Seq *)

(* Section Seqs. *)

  (**** Unsafe functions *)

  Notation seq_new_ := (lift2_both seq_new_).
  Notation seq_new := (lift1_both seq_new).
  Notation seq_len := (lift1_both seq_len).
  Notation seq_index := (lift2_both seq_index).

(**** Seq manipulation *)

Notation seq_slice := (lift3_both seq_slice).

Notation seq_slice_range :=
  (lift2_both seq_slice_range).

(* updating a subsequence in a sequence *)
Definition seq_update
  {a: choice_type}
  (s: ((seq a)))
  (start: uint_size)
  (input: ((seq a)))
  : both0 ((seq a)) :=
  lift_to_both (seq_update s start input).

(* updating only a single value in a sequence*)
Definition seq_upd
  {a: choice_type}
 
  (s: ((seq a)))
  (start: uint_size)
  (v: ((a)))
  : both0 ((seq a)) :=
  lift_to_both (seq_upd s start v).

Definition seq_update_start
  {a: choice_type}
 
  (s: ( (seq a)))
  (start_s: ( (seq a)))
    : both0 ((seq a)) :=
    lift_to_both (seq_update_start s start_s).

Definition seq_update_slice
  {A : choice_type}
  (out: ( (seq A)))
  (start_out: nat)
  (input: ( (seq A)))
  (start_in: nat)
  (len: nat)
    : both0 ((seq A)) :=
  lift_to_both (seq_update_slice out start_out input start_in len).

Definition seq_concat
           {a : choice_type}
           
  (s1 :( (seq a)))
  (s2: ( (seq a)))
  : both0 ((seq a)) :=
   lift_to_both (seq_concat s1 s2).

Notation seq_push := (lift2_both seq_push).

Definition seq_from_slice
  {a: choice_type}
 
  (input: ( (seq a)))
  (start_fin: uint_size × uint_size)
  : both0 ((seq a)) :=
  lift_to_both (seq_from_slice input start_fin).

Definition seq_from_slice_range
  {a: choice_type}
 
  (input: ( (seq a)))
  (start_fin: uint_size × uint_size)
  : both0 ((seq a)) :=
  lift_to_both (seq_from_slice_range input start_fin).

Definition seq_from_seq {A} (l : (seq A)) : both0 (seq A) :=
  lift_to_both (seq_from_seq l).

(**** Chunking *)

Definition seq_num_chunks {a: choice_type} (s: ( (seq a))) (chunk_len: uint_size) : both0 (uint_size) :=
  lift_to_both (seq_num_chunks s chunk_len).

Definition seq_chunk_len
  {a: choice_type}
  (s: ( (seq a)))
  (chunk_len: nat)
  (chunk_num: nat)
    : both0 (('nat)) :=
  lift_to_both (seq_chunk_len s chunk_len chunk_num).

Definition seq_get_chunk
  {a: choice_type}
  
  (s: ( (seq a)))
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : both0 (((uint_size × seq a))) :=
  lift_to_both (seq_get_chunk s chunk_len chunk_num).

Definition seq_set_chunk
  {a: choice_type}
 
  (s: ( (seq a)))
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  (chunk: ( (seq a)) ) : both0 ((seq a)) :=
  lift_to_both (seq_set_chunk s chunk_len chunk_num chunk).


Definition seq_num_exact_chunks {a} (l : ( (seq a))) (chunk_size : ( (uint_size))) : (both0 uint_size) :=
  lift_to_both (seq_num_exact_chunks l chunk_size).

Definition seq_get_exact_chunk {a : choice_type}  (l : ( (seq a))) (chunk_size chunk_num: ( (uint_size))) :
  both0 ((seq a)) :=
  lift_to_both (seq_get_exact_chunk l chunk_size chunk_num).

Definition seq_set_exact_chunk {a : choice_type} :=
  @seq_set_chunk a.

Definition seq_get_remainder_chunk {a : choice_type}  (l : (seq a)) (chunk_size : (uint_size)) : both0 ((seq a)) :=
  lift_to_both (seq_get_remainder_chunk l chunk_size).

Definition seq_xor_ {WS} (x y : seq (@int WS)) : both0 (seq (@int WS)) :=
  lift_to_both (seq_xor_ x y).

Definition seq_truncate {a : choice_type}  (x : seq a) (n : nat) : both0 (seq a) :=
  lift_to_both (seq_truncate x n).

(* End Seqs. *)
Infix "seq_xor" := seq_xor_ (at level 33) : hacspec_scope.

(* Section Arrays. *)
  (**** types *)

  (***** prelude.rs *)
  Definition uint128_word_t : choice_type := nseq_ uint8 16.
  Definition uint64_word_t : choice_type := nseq_ uint8 8.
  Definition uint32_word_t : choice_type := nseq_ uint8 4.
  Definition uint16_word_t : choice_type := nseq_ uint8 2.

  (**** Array manipulation *)
  Program Definition array_new_ {A: choice_type} {L I} (init: both L I A) `(len: uint_size) : both L I (nseq A len) :=
    lift1_both (fun x => array_new_ x (from_uint_size len)) init.
  Next Obligation.
    intros.
    apply incl_refl.
  Qed.
  Next Obligation.
    intros.
    apply incl_refl.
  Qed.
  
  Notation array_index := (lift2_both (fun x y => array_index x y)).

  Notation array_upd :=
    (fun (s: both _ _ (nseq_ _ _)) (i: both _ _ (@int _)) (new_v: both _ _ _) => (lift3_both (fun s i new_v => array_upd s i new_v) s i new_v)).

    (* substitutes a sequence (seq) into an array (nseq), given index interval  *)
  Definition update_sub {A : choice_type} {len slen}  (v : (nseq_ A len)) (i : nat) (n : nat) (sub : (nseq_ A slen)) : both0 ((nseq_ A len)) :=
    lift_to_both (update_sub v i n sub).

  Program Fixpoint array_from_list_helper {A: choice_type} {L I} (x : both L I A) (xs: list (both L I A)) (k : nat) {measure (length xs)} : both L I (nseq_ A (S k)) :=
    match xs with
    | [] => lift1_both (fun x => setm emptym (Ordinal (ssrbool.introT ssrnat.ltP (lt_succ_diag_r_sub k O))) x : nseq_ A (S k)) x
    | y :: ys => {|
        is_pure :=
        setm
          (is_pure (array_from_list_helper y ys k) : nseq_ A (S k))
          (Ordinal (ssrbool.introT ssrnat.ltP (lt_succ_diag_r_sub k (length (y :: ys)))))
          (is_pure x) : nseq_ A (S k) ;
        is_state :=
        {code
           temp_x ← (is_state x) ;;
           temp_y ← is_state (array_from_list_helper y ys k) ;;
           ret (setm (temp_y : nseq_ A (S k)) (Ordinal (ssrbool.introT ssrnat.ltP (lt_succ_diag_r_sub k (length (y :: ys))))) temp_x)
        }
      |}
    end.
    Next Obligation.
    intros.
    apply incl_refl.
  Qed.
  Next Obligation.
    intros.
    apply incl_refl.
  Qed.
  Next Obligation.
    intros.
    pattern_both_fresh.
    replace (H1 H) with (temp_x ← ret (is_pure H) ;; H1 temp_x) by reflexivity.

    eapply r_bind.
    - apply x.
      intros.
      apply rpre_hypothesis_rule.
      intros ? ? [[] ?] ; subst.
      eapply rpre_weaken_rule.
      subst H H0 H1. hnf.

      pattern_both_fresh.
      replace (H1 H) with (temp_x ← ret (is_pure H) ;; H1 temp_x) by reflexivity.

      eapply r_bind.
      apply H.
      intros.
      apply r_ret.
      intros ? ? [[] ?] ; subst.
      easy.
    - easy.
  Qed.

  Definition array_from_list {A: choice_type} {L I} (l: list (both L I A))
    : both L I (nseq_ A (length l)) :=
    match l as k return both L I (nseq_ A (length k)) with
      [] => lift_to_both (tt : nseq_ A 0)
    | (x :: xs) => array_from_list_helper x xs (length xs)
    end.

  Program Definition array_from_seq {A: choice_type} {L I} (out_len: nat) (input: both L I (seq A)) : both L I (nseq_ A out_len) :=
    lift1_both (array_from_seq out_len) input.
  Next Obligation.
    intros.
    apply incl_refl.
  Qed.
  Next Obligation.
    intros.
    apply incl_refl.
  Qed.

  Notation array_to_seq := (lift1_both array_to_seq).

  Definition array_from_slice
             {a: choice_type}
             
             (default_value: ( a))
             (out_len: nat)
             (input: (seq a))
             (start: uint_size)
             (slice_len: uint_size)  : both0 ((nseq_ a out_len)) :=
    lift_to_both (array_from_slice default_value out_len input (from_uint_size start) (from_uint_size slice_len)).

  Definition array_slice
             {a: choice_type}
             
             (input: (seq a))
             (start: nat)
             (slice_len: nat)
    : both0 ((nseq_ a slice_len)) :=
    lift_to_both (array_slice input start slice_len).

  Definition array_from_slice_range
             {a: choice_type}
             
             (default_value: a)
             (out_len: nat)
             (input: (seq a))
             (start_fin: (uint_size × uint_size))
    : both0 ((nseq_ a out_len)) :=
    lift_to_both (array_from_slice_range default_value out_len input start_fin).

  Definition array_slice_range
             {a: choice_type}
             
             {len : nat}
             (input: (nseq_ a len))
             (start_fin:(uint_size × uint_size))
    : both0 ((seq a)) :=
    lift_to_both (array_slice_range input start_fin).

  Definition array_update
             {a: choice_type}
             
             {len: nat}
             (s: (nseq_ a len))
             (start : uint_size)
             (start_s: (seq a))
    : both0 ((nseq_ a len)) :=
    lift_to_both (array_update s start start_s).

  Definition array_update_start
             {a: choice_type}
             
             {len: nat}
             (s: (nseq_ a len))
             (start_s: (seq a))
    : both0 ((nseq_ a len)) :=
    lift_to_both (array_update_start s start_s).

  Definition array_len  {a: choice_type} {len: nat} (s: (nseq_ a len)) : both0 (uint_size) := lift_to_both (array_len s).
  (* May also come up as 'length' instead of 'len' *)
  Definition array_length  {a: choice_type} {len: nat} (s: (nseq_ a len)) : both0 (uint_size) := lift_to_both (array_length s).

  Definition array_update_slice
             {a : choice_type}
             
             {l : nat}
             (out: ( (nseq_ a l)))
             (start_out: uint_size)
             (input: ( (seq a)))
             (start_in: uint_size)
             (len: uint_size)
    : both0 ((nseq_ a _)) :=
    lift_to_both (array_update_slice (l := l) out start_out input start_in (from_uint_size len)).

  (**** Numeric operations *)

(* End Arrays. *)


(**** Integers to arrays *)
Definition uint32_to_le_bytes (n : int32) : both0 ((nseq_ int8 4)) := lift_to_both (uint32_to_le_bytes n).
Definition uint32_to_be_bytes (n : int32) : both0 ((nseq_ int8 4)) := lift_to_both (uint32_to_be_bytes n).
Definition uint32_from_le_bytes (n : (nseq_ int8 4)) : both0 ((int32)) := lift_to_both (uint32_from_le_bytes n).
Definition uint32_from_be_bytes (n : (nseq_ int8 4)) : both0 ((int32)) := lift_to_both (uint32_from_be_bytes n).
Definition uint64_to_le_bytes (n : int64) : both0 ((nseq_ int8 8)) := lift_to_both (uint64_to_le_bytes n).
Definition uint64_to_be_bytes (n : int64) : both0 ((nseq_ int8 8)) := lift_to_both (uint64_to_be_bytes n).
Definition uint64_from_le_bytes (n : (nseq_ int8 8)) : both0 ((int64)) := lift_to_both (uint64_from_le_bytes n).
Definition uint64_from_be_bytes (n : (nseq_ int8 8)) : both0 ((int64)) := lift_to_both (uint64_from_be_bytes n).
Definition uint128_to_le_bytes (n : int128) : both0 ((nseq_ int8 16)) := lift_to_both (uint128_to_le_bytes n).
Definition uint128_to_be_bytes (n : int128) : both0 ((nseq_ int8 16)) := lift_to_both (uint128_to_be_bytes n).
Definition uint128_from_le_bytes (n : (nseq_ int8 16)) : both0 (int128) := lift_to_both (uint128_from_le_bytes n).
Definition uint128_from_be_bytes (n : (nseq_ int8 16)) : both0 ((int128)) := lift_to_both (uint128_from_be_bytes n).
Definition u32_to_le_bytes (n : int32) : both0 ((nseq_ int8 4)) := lift_to_both (u32_to_le_bytes n).
Definition u32_to_be_bytes (n : int32) : both0 ((nseq_ int8 4)) := lift_to_both (u32_to_be_bytes n).
Definition u32_from_le_bytes (n : (nseq_ int8 4)) : both0 ((int32)) := lift_to_both (u32_from_le_bytes n).
Definition u32_from_be_bytes (n : (nseq_ int8 4)) : both0 ((int32)) := lift_to_both (u32_from_be_bytes n).
Definition u64_to_le_bytes (n : int64) : both0 ((nseq_ int8 8)) := lift_to_both (u64_to_le_bytes n).
Definition u64_from_le_bytes (n : (nseq_ int8 8)) : both0 ((int64)) := lift_to_both (u64_from_le_bytes n).
Definition u128_to_le_bytes (n : int128) : both0 ((nseq_ int8 16)) := lift_to_both (u128_to_le_bytes n).
Definition u128_to_be_bytes (n : int128) : both0 ((nseq_ int8 16)) := lift_to_both (u128_to_be_bytes n).
Definition u128_from_le_bytes (n : (nseq_ int8 16)) : both0 ((int128)) := lift_to_both (u128_from_le_bytes n).
Definition u128_from_be_bytes (n : (nseq_ int8 16)) : both0 ((int128)) := lift_to_both (u128_from_be_bytes n).

(*** Nats *)


Section Todosection.

Definition nat_mod_equal {p} (a b : nat_mod p) : both0 'bool :=
  lift_to_both (@eqtype.eq_op (ordinal_eqType (S (Init.Nat.pred (Z.to_nat p)))) a b : 'bool).

Definition nat_mod_equal_reflect {p} {a b} : Bool.reflect (a = b) (is_pure (@nat_mod_equal p a b)) :=
  @eqtype.eqP (ordinal_eqType (S (Init.Nat.pred (Z.to_nat p)))) a b.

Definition nat_mod_zero {p} : both0 ((nat_mod p)) := lift_to_both (nat_mod_zero).
Definition nat_mod_one {p} : both0 ((nat_mod p)) := lift_to_both (nat_mod_one).
Definition nat_mod_two {p} : both0 ((nat_mod p)) := lift_to_both (nat_mod_two).

Definition nat_mod_add {n : Z} (a : nat_mod n) (b : nat_mod n) : both0 (nat_mod n) := lift_to_both (nat_mod_add a b).
Definition nat_mod_mul {n : Z} (a:nat_mod n) (b:nat_mod n) : both0 (nat_mod n) := lift_to_both (nat_mod_mul a b).
Definition nat_mod_sub {n : Z} (a:nat_mod n) (b:nat_mod n) : both0 (nat_mod n) := lift_to_both (nat_mod_sub a b).
Definition nat_mod_div {n : Z} (a:nat_mod n) (b:nat_mod n) : both0 (nat_mod n) := lift_to_both (nat_mod_div a b).

Definition nat_mod_neg {n : Z} (a:nat_mod n) : both0 (nat_mod n) := lift_to_both (nat_mod_neg a).

Definition nat_mod_inv {n : Z} (a:nat_mod n) : both0 (nat_mod n) := lift_to_both (nat_mod_inv a).

Definition nat_mod_exp_def {p : Z} (a:nat_mod p) (n : nat) : both0 (nat_mod p) :=
  lift_to_both (nat_mod_exp_def a n).

Definition nat_mod_exp {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow_felem {p} (a n : nat_mod p) := @nat_mod_exp_def p a (Z.to_nat (nat_of_ord n)).
Definition nat_mod_pow_self {p} (a n : nat_mod p) := nat_mod_pow_felem a n.

Close Scope nat_scope.

Definition nat_mod_from_secret_literal {m : Z} (x:int128) : both0 (nat_mod m) :=
 lift_to_both (@nat_mod_from_secret_literal m x).

Definition nat_mod_from_literal (m : Z) (x:int128) : both0 ((nat_mod m)) := nat_mod_from_secret_literal x.

Definition nat_mod_to_byte_seq_le {n : Z} (m : nat_mod n) : both0 (seq int8) := lift_to_both (nat_mod_to_byte_seq_le m).
Definition nat_mod_to_byte_seq_be {n : Z} (m : nat_mod n) : both0 (seq int8) := lift_to_both (nat_mod_to_byte_seq_be m).
Definition nat_mod_to_public_byte_seq_le (n : Z) (m : nat_mod n) : both0 (seq int8) := lift_to_both (nat_mod_to_public_byte_seq_le n m).
Definition nat_mod_to_public_byte_seq_be (n : Z) (m : nat_mod n) : both0 (seq int8) := lift_to_both (nat_mod_to_public_byte_seq_be n m).

Definition nat_mod_bit {n : Z} (a : nat_mod n) (i : uint_size) : both0 'bool :=
  lift_to_both (nat_mod_bit a i).

(* Alias for nat_mod_bit *)
Definition nat_get_mod_bit {p} (a : nat_mod p) (i : uint_size) : both0 'bool := lift_to_both (nat_get_mod_bit a i).
Definition nat_mod_get_bit {p} (a : nat_mod p) n : both0 (nat_mod p) :=
  lift_to_both (nat_mod_get_bit a n).

Definition array_declassify_eq {A l} (x : nseq_ A l) (y : nseq_ A l) : both0 'bool := lift_to_both (array_declassify_eq x y).
Definition array_to_le_uint32s {A l} (x : nseq_ A l) : both0 (seq uint32) := lift_to_both (array_to_le_uint32s x).
Definition array_to_be_uint32s {l} (x : nseq_ uint8 l) : both0 (seq uint32) := lift_to_both (array_to_be_uint32s x).
Definition array_to_le_uint64s {A l} (x : nseq_ A l) : both0 (seq uint64) := lift_to_both (array_to_le_uint64s x).
Definition array_to_be_uint64s {l} (x : nseq_ uint8 l) : both0 (seq uint64) := lift_to_both (array_to_be_uint64s x).
Definition array_to_le_uint128s {A l} (x : nseq_ A l) : both0 (seq uint128) := lift_to_both (array_to_le_uint128s x).
Definition array_to_be_uint128s {l} (x : nseq_ uint8 l) : both0 (seq uint128) := lift_to_both (array_to_be_uint128s x).
Definition array_to_le_bytes {A l} (x : nseq_ A l) : both0 (seq uint8) := lift_to_both (array_to_le_bytes x).
Definition array_to_be_bytes {A l} (x : nseq_ A l) : both0 (seq uint8) := lift_to_both (array_to_be_bytes x).
Definition nat_mod_from_byte_seq_le {A n} (x : seq A) : both0 (nat_mod n) := lift_to_both (nat_mod_from_byte_seq_le x).
Definition most_significant_bit {m} (x : nat_mod m) (n : uint_size) : both0 (uint_size) := lift_to_both (most_significant_bit x n).


(* We assume 2^x < m *)

Definition nat_mod_pow2 (m : Z) {WS} (x : (@int WS)) : both0 ((nat_mod m)) :=
  lift_to_both (nat_mod_pow2 m (Z.to_nat (unsigned x))).

End Todosection.

Infix "+%" := nat_mod_add (at level 33) : hacspec_scope.
Infix "*%" := nat_mod_mul (at level 33) : hacspec_scope.
Infix "-%" := nat_mod_sub (at level 33) : hacspec_scope.
Infix "/%" := nat_mod_div (at level 33) : hacspec_scope.

(*** Casting *)

Section TodoSection2.

Definition uint128_from_usize (n : uint_size) : both0 int128 := lift_to_both (repr _ (unsigned n)).
Definition uint64_from_usize (n : uint_size) : both0 int64 := lift_to_both (repr _ (unsigned n)).
Definition uint32_from_usize (n : uint_size) : both0 int32 := lift_to_both (repr _ (unsigned n)).
Definition uint16_from_usize (n : uint_size) : both0 int16 := lift_to_both (repr _ (unsigned n)).
Definition uint8_from_usize (n : uint_size) : both0 int8 := lift_to_both (repr _ (unsigned n)).

Definition uint128_from_uint8 (n : int8) : both0 int128 := lift_to_both (repr _ (unsigned n)).
Definition uint64_from_uint8 (n : int8) : both0 int64 := lift_to_both (repr _ (unsigned n)).
Definition uint32_from_uint8 (n : int8) : both0 int32 := lift_to_both (repr _ (unsigned n)).
Definition uint16_from_uint8 (n : int8) : both0 int16 := lift_to_both (repr _ (unsigned n)).
Definition usize_from_uint8 (n : int8) : both0 uint_size := lift_to_both (repr _ (unsigned n)).

Definition uint128_from_uint16 (n : int16) : both0 int128 := lift_to_both (repr _ (unsigned n)).
Definition uint64_from_uint16 (n : int16) : both0 int64 := lift_to_both (repr _ (unsigned n)).
Definition uint32_from_uint16 (n : int16) : both0 int32 := lift_to_both (repr _ (unsigned n)).
Definition uint8_from_uint16 (n : int16) : both0 int8 := lift_to_both (repr _ (unsigned n)).
Definition usize_from_uint16 (n : int16) : both0 uint_size := lift_to_both (repr _ (unsigned n)).

Definition uint128_from_uint32 (n : int32) : both0 int128 := lift_to_both (repr _ (unsigned n)).
Definition uint64_from_uint32 (n : int32) : both0 int64 := lift_to_both (repr _ (unsigned n)).
Definition uint16_from_uint32 (n : int32) : both0 int16 := lift_to_both (repr _ (unsigned n)).
Definition uint8_from_uint32 (n : int32) : both0 int8 := lift_to_both (repr _ (unsigned n)).
Definition usize_from_uint32 (n : int32) : both0 uint_size := lift_to_both (repr _ (unsigned n)).

Definition uint128_from_uint64 (n : int64) : both0 int128 := lift_to_both (repr _ (unsigned n)).
Definition uint32_from_uint64 (n : int64) : both0 int32 := lift_to_both (repr _ (unsigned n)).
Definition uint16_from_uint64 (n : int64) : both0 int16 := lift_to_both (repr _ (unsigned n)).
Definition uint8_from_uint64 (n : int64) : both0 int8 := lift_to_both (repr _ (unsigned n)).
Definition usize_from_uint64 (n : int64) : both0 uint_size := lift_to_both (repr _ (unsigned n)).

Definition uint64_from_uint128 (n : int128) : both0 int64 := lift_to_both (repr _ (unsigned n)).
Definition uint32_from_uint128 (n : int128) : both0 int32 := lift_to_both (repr _ (unsigned n)).
Definition uint16_from_uint128 (n : int128) : both0 int16 := lift_to_both (repr _ (unsigned n)).
Definition uint8_from_uint128 (n : int128) : both0 int8 := lift_to_both (repr _ (unsigned n)).
Definition usize_from_uint128 (n : int128) : both0 uint_size := lift_to_both (repr _ (unsigned n)).


(* Comparisons, boolean equality, and notation *)

Global Instance int_eqdec `{WS : wsize}: EqDec (@int WS) := {
  eqb := eqtype.eq_op ;
  eqb_leibniz := int_eqb_eq ;
}.

Global Instance int_comparable `{WS : wsize} : Comparable (@int WS) :=
    eq_dec_lt_Comparable (wlt Unsigned).

Definition uint8_equal (x y : int8) : both0 'bool := lift_to_both (eqb x y : 'bool).

Theorem nat_mod_eqb_spec : forall {p} (a b : nat_mod p),
    is_pure (nat_mod_equal a b) = true <-> a = b.
Proof.
  symmetry ; apply (ssrbool.rwP nat_mod_equal_reflect).
Qed.

Global Instance nat_mod_eqdec {p} : EqDec (nat_mod p) := {
  eqb a b := is_pure (nat_mod_equal a b);
  eqb_leibniz := nat_mod_eqb_spec;
}.

Global Instance nat_mod_comparable `{p : Z} : Comparable (nat_mod p) :=
  eq_dec_lt_Comparable (@order.Order.lt order.Order.OrdinalOrder.ord_display (order.Order.OrdinalOrder.porderType _)).

Definition nat_mod_rem {n : Z} (a:nat_mod n) (b:nat_mod n) : both0 (nat_mod n) :=
  lift_to_both (nat_mod_rem a b).


Infix "rem" := nat_mod_rem (at level 33) : hacspec_scope.

Global Instance bool_eqdec : EqDec bool := {
  eqb := Bool.eqb;
  eqb_leibniz := Bool.eqb_true_iff;
}.

Global Instance string_eqdec : EqDec String.string := {
  eqb := String.eqb;
  eqb_leibniz := String.eqb_eq ;
}.

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
  split ; intros ; destruct x ; destruct y.
  - (* symmetry in H1. *)
    (* apply Bool.andb_true_eq in H1. destruct H1. *)
    rewrite is_true_split_and in H1. destruct H1.
    rewrite (eqb_leibniz) in H1.
    rewrite (eqb_leibniz) in H2. now subst.
  - inversion_clear H1. now do 2 rewrite eqb_refl.
Defined.

End TodoSection2.


(*** Monad / Bind *)

Definition result_unwrap {a b} (x : result b a) : both0 (a) :=
  lift_to_both (result_unwrap x).
Definition result_unwrap_safe {a b} (x : result b a) `{match x with inl _ => True | inr _ => False end} : both0 (a) :=
  lift_to_both (result_unwrap_safe x (H := H)).

Module choice_typeMonad.

  Class BindCode (M : choice_type -> choice_type) `{mnd : @choice_typeMonad.CEMonad M}  :=
    { bind_code [L : {fset Location}] {I} {A B : choice_type} (x : code L I (M A)) (f : A -> code L I (M B)) : code L I (M B) }.
  
  Class BindBoth (M : choice_type -> choice_type) `{mnd : @choice_typeMonad.CEMonad M} `{H_bind_code : @BindCode M mnd} :=
     {
       code_eq : forall [L : {fset Location}] {I} {A B : choice_type} (x : both L I (M A)) (f : A -> both L I (M B)), ⊢ ⦃ true_precond ⦄
                     bind_code x (fun x0 : A => f x0)
                     ≈
                     ret (y m(M) ⇠ x ;; f y)
                     ⦃ pre_to_post_ret true_precond ((y m(M) ⇠ x ;; f y)) ⦄ ;
       bind_both [L : {fset Location}] {I} {A B : choice_type} (x : both L I (M A)) (f : A -> both L I (M B))  :=
       {|
         is_state := bind_code x f ;
         is_pure := y m(M) ⇠ x ;; f y ;
         code_eq_proof_statement := code_eq x f
       |}
    }.

  Theorem bind_both_proj_code : forall  `{H_bind_code : BindCode} `{@BindBoth M mnd H_bind_code} {L : {fset Location}}  {I}  {A B : choice_type} (x : both L I (M A)) (y : code L I (M A)) (f : A -> both L I (M B)) (g : A -> code L I (M B)),
      (prog (is_state x) = prog y) ->
      (forall v, prog (is_state (f v)) = prog (g v)) ->
      is_state (choice_typeMonad.bind_both x f) = choice_typeMonad.bind_code  (BindCode := H_bind_code) y g.
    intros.
    unfold bind_both.
    unfold is_state at 1, lift_scope, is_state at 1.
    f_equal.
    apply code_ext. apply H0.
    apply Coq.Logic.FunctionalExtensionality.functional_extensionality. intros.
    apply code_ext. apply H1.
  Qed.

  #[global] Program Instance result_bind_code C : BindCode (result C) :=
    {| bind_code L I A B x f :=
      {code t_x ← x ;;
       match t_x with
       | inl s => f s
       | inr s => ret (Err s)
       end} |}.
  Next Obligation.
    intros.
    apply valid_bind.
    apply prog_valid.
    intros; cbn.
    destruct x0.
    - apply prog_valid.
    - apply valid_ret.
  Qed.

  #[global] Program Instance result_bind_both C : BindBoth (result C).
  Next Obligation.
    intros.

    pattern_both_fresh.
    subst H.
    apply (@r_bind_trans_both) with (b := x) (C := result C B).
    intros ; subst H0 H1 ; hnf.

    destruct (is_pure x).
    - exact (code_eq_proof_statement (f s)).
    - now apply r_ret.
  Qed.

  #[global] Program Instance option_bind_code : BindCode (option) :=
    {| bind_code L I A B x f :=
      {code t_x ← x ;;
       match t_x with
       | Some s => f s
       | None => ret ((@None B : option B))
       end} |}.
  Next Obligation.
    intros.
    apply valid_bind.
    apply prog_valid.
    intros; cbn.
    destruct x0.
    - apply prog_valid.
    - apply valid_ret.
  Qed.

  #[global] Program Instance option_bind_both : BindBoth (option).
  Next Obligation.
    intros.

    pattern_both_fresh.
    subst H.
    apply (@r_bind_trans_both) with (b := x) (C := option B).
    intros ; subst H0 H1 ; hnf.

    destruct (is_pure x).
    - exact (code_eq_proof_statement (f s)).
    - now apply r_ret.
  Qed.

End choice_typeMonad.

(*** Result *)

Definition Ok {a b : choice_type} (x : a) : both0 (result b a) :=
  lift_to_both (Ok x : result b a).
Definition Err {a b : choice_type} (x : b) : both0 (result b a) :=   lift_to_both (Err x : result b a).

Arguments Ok {_ _}.
Arguments Err {_ _}.


(*** Notation *)

Notation "'bnd(' M ',' A ',' B ',' L ')' x '⇠' y 'in' f" := (choice_typeMonad.bind_code (BindCode := M) (A := A) (B := B) (L := L) (lift_code_scope (H_loc_incl := _) (H_opsig_incl := _) y) (fun x => f)) (at level 100, x pattern, right associativity).
Notation "'bnd(' M ',' A ',' B ',' L ')' ' x '⇠' y 'in' f" := (choice_typeMonad.bind_code (BindCode := M) (A := A) (B := B) (L := L) (lift_code_scope (H_loc_incl := _) (H_opsig_incl := _) y) (fun x => f)) (at level 100, x pattern, right associativity).

Notation "'letbnd(' M ')' x ':=' y 'in' f" := (choice_typeMonad.bind_both (BindBoth := M) (lift_scope (H_loc_incl := _) (H_opsig_incl := _) y) (fun x => f)) (at level 100, x pattern, right associativity).
Notation "'letbnd(' M ')' ' x ':=' y 'in' f" := (choice_typeMonad.bind_both (BindBoth := M) (lift_scope (H_loc_incl := _) (H_opsig_incl := _) y) (fun x => f)) (at level 100, x pattern, right associativity).

Program Definition bind_code_mut  {L : {fset Location}} {I} `{H_bind_code : choice_typeMonad.BindCode} {B : choice_type} (x_loc : Location) {A : choice_type} `{H_loc : M A = (x_loc)} `{H_in: is_true (ssrbool.in_mem (x_loc) (ssrbool.mem L))} (x : code L I (x_loc)) (f : A -> code L I (M B)) : code L I (M B) .
Proof.
  destruct x_loc as [? n].
  cbn in *. subst.
  refine ({code choice_typeMonad.bind_code x (fun temp => {code
         #put ((M A) ; n) := (choice_typeMonad.ret temp) ;;
                                f temp}) }).
Defined.

Notation "'bndm(' M ',' A ',' B ',' L ')' x 'loc(' ℓ ')'  '⇠' y 'in' f" := (bind_code_mut (H_bind_code := M) (A := A) (B := B) (L := L) (H_loc := eq_refl) ℓ y (fun x => f)) (at level 100, x pattern, right associativity).
Notation "'bndm(' M ',' A ',' B ',' L ')' ' x 'loc(' ℓ ')'  '⇠' y 'in' f" := (bind_code_mut (H_bind_code := M) (A := A) (B := B) (L := L) (H_loc := eq_refl) ℓ y (fun x => f)) (at level 100, x pattern, right associativity).


Definition bind_both_mut  {L : {fset Location}} {I} {A B : choice_type} (x_loc : Location) `{H_in: is_true (ssrbool.in_mem (x_loc) (ssrbool.mem L))} `{H_bind_both : choice_typeMonad.BindBoth} {H_loc : M A = (x_loc)} (x : both L I (x_loc)) (f : A -> both L I (M B)) : both L I (M B).
Proof.
  destruct x_loc as [C n] eqn:x_loc_eq.
  cbn in *.
  rewrite <- H_loc in x , H_in.
  refine {|
    is_pure :=  'y m(M) ⇠ is_pure x ;; is_pure (f y);
      is_state := bind_code_mut ((M A ; n) : Location ) (is_state x) (fun x => is_state (f x)) (H_in := H_in)
    |}.

  Unshelve.
  2: apply eq_refl.

  intros.
  subst.

  unfold bind_code_mut.
  unfold eq_rect.
  unfold prog.

  refine (code_eq_proof_statement (@choice_typeMonad.bind_both _ _ _ H_bind_both L I A B x (fun temp => {| is_state := {code #put (((M A); n) : Location) := choice_typeMonad.ret temp ;; f temp } |}))).
  unfold prog.
  apply better_r_put_lhs.
  eapply rpre_weaken_rule with (pre := true_precond).
  apply (code_eq_proof_statement (f temp)).
  easy.
Defined.

Notation "'bndm(' M ',' A ',' B ',' L ')' x '⇠' y 'in' f" := (choice_typeMonad.bind_code (BindCode := M) (A := A) (B := B) (L := L) y (fun x => f)) (at level 100, x pattern, right associativity).
Notation "'bndm(' M ',' A ',' B ',' L ')' ' x '⇠' y 'in' f" := (choice_typeMonad.bind_code (BindCode := M) (A := A) (B := B) (L := L) y (fun x => f)) (at level 100, x pattern, right associativity).

Notation "'letbndm(' M ')' x ':=' y 'in' f" := (choice_typeMonad.bind_both (BindBoth := M) (lift_scope (H_loc_incl := _) (H_opsig_incl := _) y) (fun x => f)) (at level 100, x pattern, right associativity).
Notation "'letbndm(' M ')' ' x ':=' y 'in' f" := (choice_typeMonad.bind_both (BindBoth := M) (lift_scope (H_loc_incl := _) (H_opsig_incl := _) y) (fun x => f)) (at level 100, x pattern, right associativity).

Program Definition foldi_bind_code' {A : choice_type} {L : {fset Location}} {I} `{H_bind_code : choice_typeMonad.BindCode} (a : uint_size) (b : uint_size) (f : uint_size -> A -> code (L) I ((M A))) (init : A)  : code (L) I (M A) :=
  {code
   foldi
     a b
     (fun x y =>
        choice_typeMonad.bind_code
          (lift_to_code y)
          (f x))
     (choice_typeMonad.ret init)
  }.

Program Definition foldi_bind_code {A : choice_type} {L : {fset Location}} {I} `{H_bind_code : choice_typeMonad.BindCode} (lo : uint_size) (hi : uint_size) (f : uint_size -> A -> code (L) I ((M A))) (init : code (L) I (M A)) : code (L) I (M A) :=
  {code
     t ← init ;;
   foldi lo hi
     (fun x y =>
        choice_typeMonad.bind_code
          (lift_to_code y)
          (f x)) (t)
  }.

Program Definition foldi_both
             {acc: choice_type}
             {L}
             {I}
             (lo: uint_size)
             (hi: uint_size) (* {lo <= hi} *)
             (init: both L I acc)
             (f: (both L I uint_size) -> (both L I) acc -> both L I acc)
              : both L I acc :=
  {|
    is_pure := Hacspec_Lib_Pre.foldi lo hi (fun x y => f (lift_to_both x) (lift_to_both y)) (is_pure init) ;
    is_state :=
    foldi lo hi (fun x y => f (lift_to_both x) ((lift_to_both y))) init
  |}.
Next Obligation.
  intros.
  unfold foldi_pre.
  unfold Hacspec_Lib_Pre.foldi.

  (* set (b_lo := lo). *)
  (* set (b_hi := hi). *)
  (* destruct lo as [lo ? ?]. *)
  (* destruct hi as [hi ? ?]. *)

  simpl.

  destruct ((_ - unsigned lo)%Z) ; [ apply r_ret ; easy | | apply r_ret ; easy ].
  
  generalize dependent lo.
  clear.
  generalize dependent init.

  induction (Pos.to_nat p) ; intros.
  - cbn.
    apply r_ret ; easy.
  - rewrite <- foldi__move_S.
    rewrite <- Hacspec_Lib_Pre.foldi__move_S.

    set (b' := f _ _). (* TODO: This should not use lift_to_both !! *)

    pose @r_bind_trans_both.
    specialize r with (b := b').

    pattern_both_fresh.
    apply r.
    subst H H0 H1. hnf.

    rewrite bind_rewrite.

    apply IHn.
Qed.

(* Program Definition foldi_both' *)
(*              {acc: choice_type} *)
(*              {L1} {L2} {L3} {L} *)
(*              {I1} {I2} {I3} {I} *)
(*              (lo: both L1 I1 uint_size) *)
(*              (hi: both L2 I2 uint_size) (* {lo <= hi} *) *)
(*              (f: both L I (uint_size) -> both L I acc -> both L I acc) *)
(*              (init: both L3 I3 acc) *)
(*   : both L I acc := *)
(*   foldi_both lo hi (lift_to_both init) f. *)

(* Program Definition foldi_bind_both {A : choice_type} {L1 L2 L3 : {fset Location}} {I1 I2 I3}  `{H_bind_both : choice_typeMonad.BindBoth} (lo : both L1 I1 uint_size) (hi : both L2 I2 uint_size) (init : both L3 I3 (M A)) (f : uint_size -> A -> both (L1 :|: L2 :|: L3) (I1 :|: I2 :|: I3) (M A))  : both  (L1 :|: L2 :|: L3) (I1 :|: I2 :|: I3) (M A) := *)
(*   let_both init (fun init' => *)
(*   foldi_both' lo hi init' (fun x y => choice_typeMonad.bind_both (y) (f x))). *)

(* Theorem foldi_bind_both_proj_code' : forall {A : choice_type} {L1 L2 L : {fset Location}} {I1 I2 I}  `{H_bind_both : choice_typeMonad.BindBoth} (lo : both L1 I1 uint_size) (hi : both L2 I2 uint_size) (init : A) (f_both : uint_size -> A -> both L I (M A)) (a : uint_size) (b : uint_size) (f_code : uint_size -> A -> code (L) I ((M A))), *)
(*     (forall i x, is_state (f_both i x) = f_code i x) -> *)
(*     is_pure lo = a -> is_pure hi = b -> *)
(*     is_state (foldi_bind_both' lo hi init f_both) = foldi_bind_code' a b init f_code. *)
(* Proof. *)
(*   intros. *)
(*   unfold foldi_bind_both'. *)
(*   unfold foldi_bind_code'. *)

(*   apply code_ext. *)

(*   subst. *)

(*   unfold is_state. *)
(*   unfold foldi_both. *)
(*   unfold prog. *)

(*   set ((fun (x0 : uint_size) (y : M A) => _)). *)
(*   set ((fun (x0 : uint_size) (y : (M A)) => _)). *)

(*   enough (y0 = y). *)
(*   + now rewrite H0. subst y y0 ; hnf. *)
(*     apply functional_extensionality. intros. *)
(*     apply functional_extensionality. intros. *)
(*     cbn. *)
(*     f_equal. *)
(*     apply functional_extensionality. intros. *)
(*     now rewrite H. *)
(* Qed. *)

(* Theorem foldi_bind_both_proj_code : forall {A : choice_type} {L : {fset Location}} {I}  `{H_bind_both : choice_typeMonad.BindBoth} (lo : uint_size) (hi : uint_size) (init_both : both L I (M A)) (f_both : uint_size -> A -> both L I (M A)) (init_code : code (L) I (M A)) (f_code : uint_size -> A -> code (L) I ((M A))), *)
(*     is_state (init_both) = init_code -> *)
(*     (forall i x, is_state (f_both i x) = f_code i x) -> *)
(*     is_state (foldi_bind_both lo hi init_both f_both) = foldi_bind_code lo hi init_code f_code. *)
(* Proof. *)
(*   intros. *)
(*   unfold foldi_bind_both. *)
(*   unfold let_both. *)
(*   unfold is_state at 1. *)
(*   unfold foldi_bind_code. *)
(*   apply code_ext. *)
(*   unfold prog. *)
(*   f_equal. *)
(*   - now rewrite H. *)
(*   - apply functional_extensionality. intros. *)
(*     unfold is_state. *)
(*     unfold foldi_both. *)
(*     unfold prog. *)

(*     set ((fun (x0 : uint_size) (y : M A) => _)). *)
(*     set ((fun (x0 : uint_size) (y : M A) => _)). *)
(*     enough (y0 = y). *)
(*     + now rewrite H1. subst y y0 ; hnf. *)
(*       apply functional_extensionality. intros. *)
(*       apply functional_extensionality. intros. *)
(*       cbn. *)
(*       f_equal. *)
(*       apply functional_extensionality. intros. *)
(*       symmetry. *)
(*       apply H0. *)
(* Qed. *)

Section TodoSection3.
Definition nat_mod_from_byte_seq_be {A n} (x : seq A) : both0 (nat_mod n) := lift_to_both (nat_mod_from_byte_seq_be x).

End TodoSection3.

Definition neqb {A : choice_type} `{EqDec A} (x y : A) : both0 'bool := lift_to_both (negb (eqb x y) : 'bool).
Definition eqb {A : choice_type} `{EqDec A} (x y : A) : both0 'bool := lift_to_both (eqb x y : 'bool).

Definition ltb {A : choice_type} `{Comparable A} (x y : A) : both0 'bool := lift_to_both (ltb x y : 'bool).
Definition leb {A : choice_type} `{Comparable A} (x y : A) : both0 'bool := lift_to_both (leb x y : 'bool).
Definition gtb {A : choice_type} `{Comparable A} (x y : A) : both0 'bool := lift_to_both (gtb x y : 'bool).
Definition geb {A : choice_type} `{Comparable A} (x y : A) : both0 'bool := lift_to_both (geb x y : 'bool).

Infix "=.?" := eqb (at level 40) : hacspec_scope.
Infix "!=.?" := neqb (at level 40) : hacspec_scope.
Infix "<.?" := ltb (at level 42) : hacspec_scope.
Infix "<=.?" := leb (at level 42) : hacspec_scope.
Infix ">.?" := gtb (at level 42) : hacspec_scope.
Infix ">=.?" := geb (at level 42) : hacspec_scope.

Lemma foldi_nat_both :
  forall {A : choice_type} {L : {fset Location}} {I} (lo hi : nat)
    (b : nat -> A -> both L I A)
    (v : A),
  ⊢ ⦃ true_precond ⦄
      @foldi_nat _ lo hi b v
  ≈
  lift_to_both (Hacspec_Lib_Pre.foldi_nat lo hi b v) : both L I A
  ⦃ pre_to_post_ret true_precond ((Hacspec_Lib_Pre.foldi_nat lo hi b v)) ⦄.
Proof.
  intros.
  unfold prog, is_state at 2.
  unfold foldi_nat.
  unfold Hacspec_Lib_Pre.foldi_nat.

    destruct (_ - lo).
  { apply r_ret ; intros ; subst.
    split.
    - easy.
    - easy.
  }

  generalize dependent lo.
  clear.
  generalize dependent v.

  induction n ; intros.
  - cbn.
    (* unfold repr. *)

    (* replace (fun cur' : choice.Choice.sort (chElement (A)) => *)
    (*            ret (cur')) with (@ret (chElement (A))) by (apply functional_extensionality ; intros ; now rewrite T_ct_id). *)
    rewrite bind_ret.
    apply (@code_eq_proof_statement).

  - rewrite <- foldi__nat_move_S.
    rewrite <- Hacspec_Lib_Pre.foldi__nat_move_S.

    set (b' := b lo v).

    pose @r_bind_trans_both.
    specialize r with (b := b').

    specialize r with (g := fun temp => @ret (chElement (A))
       (
          (@Hacspec_Lib_Pre.foldi_nat_ ( A) (S n) (S lo)
             (fun (n0 : nat) (v0 : A) => @is_pure L I A (b n0 v0))
             temp))).
    apply r.
    intros.

    apply IHn.
Qed.

Lemma foldi_as_both :
  forall {A : choice_type} {L I} (lo hi : both L I uint_size)
    (state : uint_size -> A -> code L I (A))
    (pure : uint_size -> A -> A)
     v,
    (forall x y,
    ⊢ ⦃ true_precond ⦄
        state x y ≈ lift_to_code (L := L) (I := I) (pure x y)
    ⦃ pre_to_post_ret true_precond ((pure x y)) ⦄) ->
  ⊢ ⦃ true_precond ⦄
     @foldi _ lo hi L I state v
  ≈
     lift_to_both (Hacspec_Lib_Pre.foldi lo hi pure v) : both L I A
  ⦃ pre_to_post_ret true_precond ((Hacspec_Lib_Pre.foldi lo hi pure v)) ⦄.
Proof.
  intros.
  pose (fun x y => Build_both L I A (pure x y) (state x y) (H x y)).
  unfold is_state.
  unfold prog.

  pose (code_eq_proof_statement (foldi_both lo hi (lift_to_both v) (fun x y => b x (y)))).
  cbn in r.
  cbn.
  
  apply (code_eq_proof_statement (foldi_both lo hi (lift_to_both v) (fun x y => b x (y)))).
Qed.

(*** For loop again *)

(* SSProve for loop is inclusive upperbound, while hacspec is exclusive upperbound *)
Definition for_loop_range
  (lo: nat)
  (hi: nat)
  (f : nat -> raw_code 'unit) : raw_code 'unit :=
  match hi - lo with
  | O => @ret 'unit tt
  | S i => for_loop (fun n => f (n + lo)) i
  end.

Fixpoint list_types_ (l : list choice_type) (init : choice_type) : choice_type  :=
  match l with
  | (t :: ts) => list_types_ ts t × init
  | [] => init
  end.

Definition list_types (l : list choice_type) : choice_type :=
  match l with
  | [] => 'unit
  | (t :: ts) => list_types_ ts t
  end.

Program Fixpoint vars_to_tuple (vars : list (∑ (t : choice_type), t)) {measure (length vars)} : list_types (seq.map (fun '(x ; y) => x) vars)  :=
  match vars with
  | [] => tt
  | (x :: xs) =>
      match xs with
      | [] => _
      | (s :: xs) => (vars_to_tuple (s :: xs) , _)
      end
  end.

Fixpoint for_loop_return_ (ℓ : list Location) (vars : list (∑ (t : choice_type), t)) : raw_code (list_types (seq.cat (seq.map (fun '(x ; y) => x) vars) (seq.map (fun '(x ; y) => x) ℓ) )).

  destruct ℓ as [ | l ls ].
  - rewrite seq.cats0.
    pose (ret (vars_to_tuple vars)).
    replace (fun pat : ∑ t : choice_type, t => _) with
      (fun pat : @sigT choice_type
       (fun t : choice_type => t) =>
         match pat return choice_type with
         | @existT _ _ x _ => x
         end)
      in r by (apply functional_extensionality ; now intros []).
    apply r.
  - apply (getr (l)).
    intros x.
    destruct l.
    cbn in x.
    pose (for_loop_return_ ls (vars ++ [(x0 ; x)])).
    rewrite seq.map_cat in r.
    cbn in r.
    rewrite <- seq.catA in r.
    cbn in r.
    apply r.
Defined.

Definition for_loop_return (ℓ : list Location) : raw_code (list_types (seq.map (fun '(x ; y) => x) ℓ)) := for_loop_return_ ℓ [].

Definition for_loop_locations
           (lo: nat)
           (hi: nat)
           (ℓ : list Location)
           (f : nat -> raw_code 'unit) :=
  match hi - lo with
  | O => @ret 'unit tt
  | S i => for_loop (fun n => f (n + lo)) i
  end  ;; for_loop_return ℓ.

Theorem r_bind_trans_as_both : forall {B C : choice_type} {L I} (f : choice.Choice.sort B -> raw_code C) (g : B -> raw_code C) (state : code L I (B))
    (pure : B),
  forall (P : precond) (Q : postcond _ _),
    (⊢ ⦃ true_precond ⦄
        state ≈ lift_to_code (L := L) (I := I) (pure)
    ⦃ pre_to_post_ret true_precond (pure) ⦄) ->
    (⊢ ⦃ true_precond ⦄ f (pure)  ≈ g pure ⦃ Q ⦄) ->
    (⊢ ⦃ P ⦄ temp ← state ;; f temp ≈ g (pure) ⦃ Q ⦄).
Proof.
  intros.
  eapply r_bind_trans with (P_mid := true_precond).

  eapply rpre_weaken_rule.

  pose (Build_both L I B (pure) (state)).

  refine (code_eq_proof_statement (b _)). clear b.
  apply H.

  reflexivity.

  intros.
  apply H0.
Qed.

Ltac pattern_foldi_both Hx Hf Hg :=
  match goal with
    | [ |- context [ ⊢ ⦃ _ ⦄ bind _ (foldi _ _ _ ?fb) ≈ ?os ⦃ _ ⦄ ] ] =>
        let H := fresh in
        set (H := os)
        ; set (Hx := Hacspec_Lib_Pre.foldi _ _ _ _) in H
        ; pattern Hx in H
        ; subst H
        ; set (Hf := fb)
        ; match goal with
          | [ |- context [ ⊢ ⦃ _ ⦄ _ ≈ ?gb _ ⦃ _ ⦄ ] ] =>
              set (Hg := gb)
          end
  | [ |- context [ ⊢ ⦃ _ ⦄ prog (foldi _ _ _ ?fb) ≈ ?os ⦃ _ ⦄ ] ] =>
        let H := fresh in
        set (H := os)
        ; set (Hx := Hacspec_Lib_Pre.foldi _ _ _ _) in H
        ; pattern Hx in H
        ; subst H
        ; set (Hf := fb)
        ; match goal with
          | [ |- context [ ⊢ ⦃ _ ⦄ _ ≈ ?gb _ ⦃ _ ⦄ ] ] =>
              set (Hg := gb)
          end
    end.

Ltac pattern_foldi_both_fresh :=
  let Hx := fresh in
  let Hf := fresh in
  let Hg := fresh in
  pattern_foldi_both Hx Hf Hg.

Ltac progress_step_code :=
  match_foldi_both
  || (match_bind_trans_both)
  || match goal with
    | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; (getr ?l ?a)) ≈ _ ⦃ _ ⦄ ]] =>
        apply better_r_put_get_lhs
    end
  ||
  match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; (putr ?l ?y ?a)) ≈ _ ⦃ _ ⦄ ]] =>
      apply (r_transL (#put l := y ;; a )) ;
      [ apply contract_put | ]
  end
  ||
  match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; ?a) ≈ ?b ⦃ _ ⦄ ]] =>
      apply (better_r_put_lhs l x a b)
  end
  ||
  (unfold lift_to_code ; apply r_ret)
  ||
  (rewrite bind_assoc)
    with
    match_foldi_both :=
    let Hx := fresh in
    let Hf := fresh in
    let Hg := fresh in
    pattern_foldi_both Hx Hf Hg
    ; try (apply (@r_bind_trans_as_both) with (f := Hf) (g := Hg))
    ; intros ; subst Hf ; subst Hg ; subst Hx ; hnf
    ; [apply foldi_as_both ; [ try (cbn ; Lia.lia) | intros ; unfold lift_to_code ; unfold prog ] | step_code]
    with
    step_code :=
      repeat (clear_bind || progress_step_code) ; try easy
        with
        clear_bind :=
        (unfold lift_to_code ;
         match goal with
         | [ |- context [ bind ?y (fun x => ret (_)) ] ] =>
             let H := fresh in
             set (H := y)

             ; rewrite bind_ret
             ; subst H
         | [ |- context [ bind ?y (fun x => ret _) ] ] =>
             let H := fresh in
             set (H := y)

             ; rewrite bind_ret
             ; subst H
         end)
        ||
        (repeat (rewrite bind_assoc)
        ; match goal with
          | [ |- context [ bind (ret (?y)) (fun x => _) ] ] =>
              let H := fresh in
              set (H := y)

              ; rewrite bind_rewrite
              ; subst H
          | [ |- context [ bind (ret ?y) (fun x => _) ] ] =>
              let H := fresh in
              set (H := y)
              ; rewrite bind_rewrite
              ; subst H
          end).


Theorem empty_put {B} ℓ v (k h : raw_code B) :
  ⊢ ⦃ true_precond ⦄ k ≈ h ⦃ pre_to_post true_precond ⦄ ->
  ⊢ ⦃ true_precond ⦄ #put ℓ := v ;; k ≈ h ⦃ pre_to_post true_precond ⦄.
Proof.
  intros.
  apply better_r_put_lhs.
  eapply rpre_weaken_rule.
  apply H.
  intros.
  reflexivity.
Qed.


Ltac ssprove_valid_step :=
  (progress
     (
       cbv zeta
       || unfold prog
       || (match goal with | [ |- context[ @bind ?A ?B (ret ?x) ?f ]] => rewrite bind_rewrite end)
       || match goal with
         | [ |- context[match ?x with | true => _ | false => _ end] ] =>
             destruct x
         end
       || match goal with
         | [ |- context[match ?x with | tt => _ end] ] =>
             destruct x
         end
       || match goal with
         | [ |- context[match ?x with | inl _ => _ | inr _ => _ end] ] =>
             destruct x
         end
       || (match goal with | [ |- context[bind (bind ?v ?k1) ?k2] ] => rewrite bind_assoc end)
       || (apply valid_bind ; [apply valid_scheme ; try rewrite <- fset.fset0E ; apply prog_valid | intros])
       || (apply valid_bind ; [valid_program | intros])
       || (apply valid_bind ; [repeat ssprove_valid_step | intros])
       || (apply valid_opr ; [ ssprove_valid_opsig | intros ] )
       ||  match goal with
         | [ |- context [ putr _ _ _ ] ] => (apply valid_putr ; [ ssprove_valid_location | ])

         end

       || match goal with
         | [ |- context [ getr _ _ ] ] => (apply valid_getr ; [ ssprove_valid_location | intros])
         end
       || apply valid_ret
       || (match goal with
          | [ |- context [ValidCode (fset ?ys) _ (@prog _ _ _ (@foldi _ ?lo ?hi (fset ?xs) _ ?f ?v))] ] =>
              eapply (valid_subset_fset xs ys) ; [ | apply valid_foldi_pre ]
              ; loc_incl_compute
          end)
       || (hnf in * ; destruct_choice_type_prod)
  )).

Theorem length_merge_sort_pop : forall {A} leb (l1 : list (list A)) (l2 : list A),
    length (path.merge_sort_pop leb l2 l1) = length (seq.cat (seq.flatten l1) l2).
Proof.
  intros.
  generalize dependent l2.
  induction l1 ; intros.
  - cbn.
    reflexivity.
  - cbn.
    rewrite IHl1.
    rewrite seq.size_cat.
    rewrite seq.size_cat.
    rewrite seq.size_cat.
    rewrite path.size_merge.
    rewrite seq.size_cat.
    rewrite ssrnat.addnA.
    f_equal.
    rewrite ssrnat.addnC.
    reflexivity.
Qed.

Theorem length_sort_even : forall {A} leb a x (l1 : list (list A)) (l2 : list A),
    length (path.merge_sort_rec leb l1 (a :: x :: l2)) =
    length (path.merge_sort_rec leb
        (path.merge_sort_push leb (if leb a x then [a; x] else [x; a]) l1) l2).
Proof.
  reflexivity.
Qed.

Theorem length_sort_is_length' : forall {A} leb (l1 : list (list A)),
    length (path.merge_sort_rec leb l1 []) = length (seq.flatten l1).
Proof.
  destruct l1.
  + cbn.
    reflexivity.
  + cbn.
    rewrite length_merge_sort_pop.
    rewrite seq.size_cat.
    rewrite seq.size_cat.
    rewrite path.size_merge.
    rewrite seq.cats0.
    rewrite ssrnat.addnC.
    reflexivity.
Qed.

Ltac ssprove_valid'_2 :=
  repeat ssprove_valid_step
  ; ssprove_valid_program
  ; try ssprove_valid_location.

Ltac ssprove_valid_package :=
  (repeat apply valid_package_cons ; [ apply valid_empty_package | .. | try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity) ] ; intros ; progress unfold prog).

Ltac solve_zero :=
  match goal with
  | [ |- context [ (_ <= _)%Z ] ] =>
      cbn ;
      match goal with
      | [ |- context [ (0 <= toword ?x)%Z ] ] =>
          let H := fresh in
          let H_zero := fresh in
          let H_succ := fresh in
          set (H := x)
          ; destruct_uint_size_as_nat_named H H_zero H_succ
          ; [ reflexivity | cbn in H_succ ; cbn ; try rewrite H_succ ; Lia.lia ]
      end
  end.

Ltac ssprove_package_obligation :=
  setoid_rewrite (ssrbool.elimT (@fsetUidPl _ _ _)) ; [ reflexivity | ] ;
  repeat rewrite fsubUset ;
  repeat rewrite (ssrbool.introT (@ssrbool.andP _ _)) ;
  repeat split ;
  try reflexivity ;
  try apply -> loc_list_incl_remove_fset ;
  pose loc_list_incl_expand ;
  rewrite loc_list_incl_fsubset ;
  loc_incl_compute.

Ltac solve_ssprove_obligations :=
  intros ;
  try rewrite !fset1E ;
  try rewrite <- !fset0E ;
  try rewrite !fsetU0 ;
  try rewrite !fset0U ;
  try rewrite !fsetUid ;
  try rewrite <- !fset_cat ;
  try rewrite !fsetU0 ;
  try rewrite !fset0U ;
  try rewrite !fset0E ;
  try rewrite !fsetUid ;
  (ssprove_valid_location || loc_incl_compute || opsig_incl_compute || ssprove_package_obligation)
  || (match goal with
     | [ |- context [ pkg_composition.Parable _ _ ]] =>
         unfold pkg_composition.Parable, fdisjoint, fsetI, fset_filter,
                fmap.domm, fmap.FMap.fmval, fmap.mkfmap, fmap.setm, fmap.fmap, fset
         ; now rewrite ssreflect.locked_withE
     end)
  || now repeat rewrite <- fset_cat
  || (ssprove_valid_package ; ssprove_valid'_2)
  || ssprove_valid'_2
  || (try (Tactics.program_simpl; fail))
  .

Definition andb (x y : 'bool) : both0 'bool := lift_to_both (andb x y : 'bool).

Infix "&&" := andb : bool_scope.

Definition orb (x y : 'bool) : both0 'bool := lift_to_both (orb x y : 'bool).

Infix "||" := orb : bool_scope.

Definition negb (x : 'bool) : both0 'bool := lift_to_both (negb x : 'bool).

Program Definition ret_both  {L : {fset Location}} {I} `{choice_typeMonad.CEMonad} {A : choice_type} (x : A) : both L I (M A) := lift_to_both (choice_typeMonad.ret x).

Ltac init_both_proof b_state b_pure :=
  intros ;
  unfold lift_to_code ;
  cbv delta [b_state] ;
  cbn beta ;
  let H := fresh in
  match goal with
  | [ |- context [(prog {code ?x})] ] =>
      set (H := x)
  end ;
  unfold prog ;
  cbv delta [b_pure] ;
  subst H ;
  cbn beta.

(* Ltac foldi_state_eq_code := *)
(*   erewrite <- @foldi_bind_both_proj_code' ; [ reflexivity | intros ; hnf | reflexivity | reflexivity  ]. *)
Ltac bind_both_eq_code :=
  erewrite <- @choice_typeMonad.bind_both_proj_code ; [ reflexivity | hnf | reflexivity ].

(* Theorem letbm_proj_code : *)
(*   forall (L1 L2 : {fset Location}) `{H_loc_incl : List.incl L1 L2}, *)
(*   forall {I1 I2 : {fset opsig}} `{H_opsig_incl : List.incl I1 I2}, *)
(*   forall B (i : Location), *)
(*   forall `{H_in : is_true (ssrbool.in_mem (i) (ssrbool.mem L2))}, *)
(*   forall (x : both L1 I1 (i)) (f : (i) -> both (L1 :|: L2) (I1 :|: I2) B), *)
(*   forall (y : code L1 I1 (i)) (g : (i) -> code (L1 :|: L2) (I1 :|: I2) B), *)
(*     is_state x = y -> *)
(*     (forall x, is_state (f x) = (g x)) -> *)
(*     is_state ((let_mut_both i (H_in := H_in) x f)) = *)
(*     let_mut_code i (H_in := H_in) (lift_code_scope (H_loc_incl := H_loc_incl) (H_opsig_incl := H_opsig_incl) y) g *)
(*     . *)
(* Proof. *)
(*   intros L1 L2 H_loc_incl I1 I2 H_opsig_incl B [A n]. *)
(*   intros H_in x f y g H_var_eq H_fun_eq. *)
(*   apply code_ext. unfold prog. *)
(*   unfold let_mut_both, is_state at 1. *)
(*   unfold lift_scope. unfold is_state at 1. *)
(*   rewrite let_mut_code_equation_1. *)
(*   unfold prog. *)
(*   unfold lift_code_scope. *)
(*   rewrite H_var_eq. *)
(*   apply f_equal. *)
(*   apply functional_extensionality. intros. *)
(*   apply f_equal. *)
(*   apply f_equal. *)
(*   apply functional_extensionality. intros. *)
(*   now rewrite H_fun_eq. *)
(* Qed. *)

(* Ltac letbm_eq_code := *)
(*   match goal with *)
(*   | [ |- context [let_mut_both _ (lift_scope ?k) ?f] ] => *)
(*       erewrite letbm_proj_code with (g := f) (y := k) ; [ hnf | reflexivity | reflexivity ] *)
(*   end. *)
Ltac f_equal_fun_ext :=
  repeat (apply f_equal ; try (apply Coq.Logic.FunctionalExtensionality.functional_extensionality ; intros)).

Definition u32_word_t := nseq_ uint8 4.
Definition u128_word_t := nseq_ uint8 16.

(* Lemma letbm_ret_r : *)
(*   forall {A : choice.Choice.type} {B : choice_type} *)
(*     (r₁ : raw_code A) (pre : precond) *)
(*     (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)) *)
(*     (ℓ : Location) *)
(*     (L : {fset Location}) *)
(*     (I : Interface) *)
(*     v (f : _ -> both L I B) (H_in : is_true (ssrbool.in_mem (ℓ) (ssrbool.mem L))), *)
(*     ⊢ ⦃ (set_rhs (@existT choice_type (fun _ : choice_type => nat) ((projT1 ℓ)) (projT2 ℓ)) v pre) ⦄ r₁ ≈ f v ⦃ post ⦄ -> *)
(*     ⊢ ⦃ pre ⦄ r₁ ≈ let_mut_both ℓ (H_in := H_in) (lift_to_both (v)) f ⦃ post ⦄. *)
(* Proof. *)
(*   intros. *)
(*   cbn. *)
(*   unfold let_mut_code. *)
(*   unfold lift_to_code. *)
(*   (* unfold Hacspec_Lib.let_mut_both_obligation_1. *) *)
(*   cbn. *)
(*   destruct ℓ. *)
(*   cbn. *)
(*   apply better_r_put_get_rhs. *)
(*   apply better_r, r_put_rhs. *)
(*   apply H. *)
(* Qed. *)

(* Lemma letbm_ret_l : *)
(*   forall {A : choice_type} {B : choice.Choice.type} *)
(*     (r₀ : raw_code A) *)
(*     (r₁ : raw_code B) (pre : precond) *)
(*     (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)) *)
(*     (ℓ : Location) *)
(*     (L : {fset Location}) *)
(*     (I : Interface) *)
(*     v (f : _ -> both L I A) (H_in : is_true (ssrbool.in_mem (ℓ) (ssrbool.mem L))), *)
(*     ⊢ ⦃ (set_lhs (@existT choice_type (fun _ : choice_type => nat) ((projT1 ℓ)) (projT2 ℓ)) v pre) ⦄ f v ≈ r₁ ⦃ post ⦄ -> *)
(*     ⊢ ⦃ pre ⦄ let_mut_both ℓ (H_in := H_in) (lift_to_both (v)) f ≈ r₁ ⦃ post ⦄. *)
(* Proof. *)
(*   intros. *)
(*   cbn. *)
(*   unfold let_mut_code. *)
(*   unfold lift_to_code. *)
(*   (* unfold Hacspec_Lib.let_mut_both_obligation_1. *) *)
(*   cbn. *)
(*   destruct ℓ. *)
(*   apply better_r_put_get_lhs. *)
(*   apply better_r_put_lhs. *)
(*   apply H. *)
(* Qed. *)


Program Definition let_both_prod {L  : {fset Location}} {I} {A B C : choice_type}
        (x : both L I (A × B))
        (f : both L I A -> both L I B -> both L I C)
  : both L I C :=
  {|
    is_state := {code temp ← is_state x ;; is_state (f (lift_to_both (fst temp)) (lift_to_both (snd temp)))} ;
    is_pure := is_pure (f (lift_to_both (fst (is_pure x))) (lift_to_both (snd (is_pure x)))) ;
  |}.
Next Obligation.
  intros.
  cbn.
  replace (ret _) with (temp ← ret (is_pure x) ;; ret ((is_pure (f ((lift_to_both (fst temp))) ((lift_to_both (snd temp))))))) by reflexivity.

  eapply r_bind.
  apply x.

  intros.
  apply rpre_hypothesis_rule.
  intros ? ? [[] []]. subst.
  eapply rpre_weaken_rule.
  apply f.
  reflexivity.
Qed.

Definition both_LL_II_to_both_L_I {L I A} : both (L :|: L) (I :|: I) A -> both L I A.
Proof.
  now do 2 rewrite fsetUid.
Defined.

Definition both_L0_I0_to_both_L_I {L I A} : both (L :|: fset0) (I :|: fset []) A -> both L I A.
Proof.
  rewrite <- fset0E.
  now do 2 rewrite fsetU0.
Defined.

  (* takes two nseq's and joins them using a function op : a -> a -> a *)
  (* Definition array_join_map *)
  (*            {a: choice_type} *)
  (*            {len: uint_size} *)
  (*            {L1 L2 I1 I2} *)
  (*            (op: forall {L1 L2 I1 I2}, ( (both L1 I1 a)) -> (both L2 I2 a) -> ( (both (L1 :|: L2) (I1 :|: I2) a))) *)
  (*            (s1: (both L1 I1 (nseq a len))) *)
  (*            (s2 : (both L2 I2 (nseq a len))) : both (L1 :|: L2) (I1 :|: I2) ((nseq a len)) := @foldi_both' _ L1 L2 L1 (L1 :|: L2) I1 I2 I1 (I1 :|: I2) (lift_to_both (usize 0)) (lift_to_both len) *)
  (*  (fun x y => *)
  (*   let b1 := *)
  (*     eq_rect (L1 :|: (L1 :|: L2)) *)
  (*       (fun *)
  (*          f : {fset tag_ordType (I:=choice_type_ordType) *)
  (*                      (fun _ : choice_type => nat_ordType)} => *)
  (*        both f (I1 :|: (I1 :|: I2)) a) (array_index s1 x) (L1 :|: L1 :|: L2) *)
  (*       (fsetUA *)
  (*          (T:=tag_ordType (I:=choice_type_ordType) *)
  (*                (fun _ : choice_type => nat_ordType)) L1 L1 L2) in *)
  (*   let b2 := *)
  (*     eq_rect (I1 :|: (I1 :|: I2)) *)
  (*       (fun *)
  (*          f : {fset prod_ordType nat_ordType *)
  (*                      (prod_ordType choice_type_ordType *)
  (*                         choice_type_ordType)} => *)
  (*        both (L1 :|: L1 :|: L2) f a) b1 (I1 :|: I1 :|: I2) *)
  (*       (fsetUA *)
  (*          (T:=prod_ordType nat_ordType *)
  (*                (prod_ordType choice_type_ordType choice_type_ordType)) I1 *)
  (*          I1 I2) in *)
  (*   let b3 := *)
  (*     eq_rect (L1 :|: L1) *)
  (*       (fun *)
  (*          f : {fset tag_ordType (I:=choice_type_ordType) *)
  (*                      (fun _ : choice_type => nat_ordType)} => *)
  (*        both (f :|: L2) (I1 :|: I1 :|: I2) a) b2 L1 *)
  (*       (fsetUid *)
  (*          (T:=tag_ordType (I:=choice_type_ordType) *)
  (*                (fun _ : choice_type => nat_ordType)) L1) in *)
  (*   let b4 := *)
  (*     eq_rect (I1 :|: I1) *)
  (*       (fun *)
  (*          f : {fset prod_ordType nat_ordType *)
  (*                      (prod_ordType choice_type_ordType *)
  (*                         choice_type_ordType)} => *)
  (*        both (L1 :|: L2) (f :|: I2) a) b3 I1 *)
  (*       (fsetUid *)
  (*          (T:=prod_ordType nat_ordType *)
  (*                (prod_ordType choice_type_ordType choice_type_ordType)) I1) *)
  (*     in *)
  (*   let b5 := *)
  (*     eq_rect (L2 :|: (L1 :|: L2)) *)
  (*       (fun *)
  (*          f : {fset tag_ordType (I:=choice_type_ordType) *)
  (*                      (fun _ : choice_type => nat_ordType)} => *)
  (*        both f (I2 :|: (I1 :|: I2)) a) (array_index s2 x) (L1 :|: L2 :|: L2) *)
  (*       (fsetUC *)
  (*          (T:=tag_ordType (I:=choice_type_ordType) *)
  (*                (fun _ : choice_type => nat_ordType)) L2  *)
  (*          (L1 :|: L2)) in *)
  (*   let b6 := *)
  (*     eq_rect_r *)
  (*       (fun *)
  (*          f : {fset tag_ordType (I:=choice_type_ordType) *)
  (*                      (fun _ : choice_type => nat_ordType)} => *)
  (*        both f (I2 :|: (I1 :|: I2)) a) b5 *)
  (*       (fsetUA *)
  (*          (T:=tag_ordType (I:=choice_type_ordType) *)
  (*                (fun _ : choice_type => nat_ordType)) L1 L2 L2) in *)
  (*   let b7 := *)
  (*     eq_rect (L2 :|: L2) *)
  (*       (fun *)
  (*          f : {fset tag_ordType (I:=choice_type_ordType) *)
  (*                      (fun _ : choice_type => nat_ordType)} => *)
  (*        both (L1 :|: f) (I2 :|: (I1 :|: I2)) a) b6 L2 *)
  (*       (fsetUid *)
  (*          (T:=tag_ordType (I:=choice_type_ordType) *)
  (*                (fun _ : choice_type => nat_ordType)) L2) in *)
  (*   let b8 := *)
  (*     eq_rect (I2 :|: (I1 :|: I2)) *)
  (*       (fun *)
  (*          f : {fset prod_ordType nat_ordType *)
  (*                      (prod_ordType choice_type_ordType *)
  (*                         choice_type_ordType)} =>  *)
  (*        both (L1 :|: L2) f a) b7 (I1 :|: I2 :|: I2) *)
  (*       (fsetUC *)
  (*          (T:=prod_ordType nat_ordType *)
  (*                (prod_ordType choice_type_ordType choice_type_ordType)) I2 *)
  (*          (I1 :|: I2)) in *)
  (*   let b9 := *)
  (*     eq_rect_r *)
  (*       (fun *)
  (*          f : {fset prod_ordType nat_ordType *)
  (*                      (prod_ordType choice_type_ordType *)
  (*                         choice_type_ordType)} =>  *)
  (*        both (L1 :|: L2) f a) b8 *)
  (*       (fsetUA *)
  (*          (T:=prod_ordType nat_ordType *)
  (*                (prod_ordType choice_type_ordType choice_type_ordType)) I1 *)
  (*          I2 I2) in *)
  (*   let b10 := *)
  (*     eq_rect (I2 :|: I2) *)
  (*       (fun *)
  (*          f : {fset prod_ordType nat_ordType *)
  (*                      (prod_ordType choice_type_ordType *)
  (*                         choice_type_ordType)} => *)
  (*        both (L1 :|: L2) (I1 :|: f) a) b9 I2 *)
  (*       (fsetUid *)
  (*          (T:=prod_ordType nat_ordType *)
  (*                (prod_ordType choice_type_ordType choice_type_ordType)) I2) *)
  (*     in *)
  (*   let b11 := @op (L1 :|: L2) (L1 :|: L2) (I1 :|: I2) (I1 :|: I2) b4 b10 in *)
  (*   let b12 := *)
  (*     eq_rect (L1 :|: L2 :|: (L1 :|: L2)) *)
  (*       (fun *)
  (*          f : {fset tag_ordType (I:=choice_type_ordType) *)
  (*                      (fun _ : choice_type => nat_ordType)} => *)
  (*        both f (I1 :|: I2 :|: (I1 :|: I2)) a) b11  *)
  (*       (L1 :|: L2) *)
  (*       (fsetUid *)
  (*          (T:=tag_ordType (I:=choice_type_ordType) *)
  (*                (fun _ : choice_type => nat_ordType))  *)
  (*          (L1 :|: L2)) in *)
  (*   let b13 := *)
  (*     eq_rect (I1 :|: I2 :|: (I1 :|: I2)) *)
  (*       (fun *)
  (*          f : {fset prod_ordType nat_ordType *)
  (*                      (prod_ordType choice_type_ordType *)
  (*                         choice_type_ordType)} =>  *)
  (*        both (L1 :|: L2) f a) b12 (I1 :|: I2) *)
  (*       (fsetUid *)
  (*          (T:=prod_ordType nat_ordType *)
  (*                (prod_ordType choice_type_ordType choice_type_ordType)) *)
  (*          (I1 :|: I2)) in *)
  (*   let b14 := array_upd y x b13 in *)
  (*   let b15 := *)
  (*     eq_rect (L1 :|: L2 :|: (L1 :|: L2)) *)
  (*       (fun *)
  (*          f : {fset tag_ordType (I:=choice_type_ordType) *)
  (*                      (fun _ : choice_type => nat_ordType)} => *)
  (*        both (f :|: (L1 :|: L2)) *)
  (*          (I1 :|: I2 :|: (I1 :|: I2) :|: (I1 :|: I2)) *)
  (*          (nseq_ a (from_uint_size len))) b14 (L1 :|: L2) *)
  (*       (fsetUid *)
  (*          (T:=tag_ordType (I:=choice_type_ordType) *)
  (*                (fun _ : choice_type => nat_ordType))  *)
  (*          (L1 :|: L2)) in *)
  (*   let b16 := *)
  (*     eq_rect (L1 :|: L2 :|: (L1 :|: L2)) *)
  (*       (fun *)
  (*          f : {fset tag_ordType (I:=choice_type_ordType) *)
  (*                      (fun _ : choice_type => nat_ordType)} => *)
  (*        both f (I1 :|: I2 :|: (I1 :|: I2) :|: (I1 :|: I2)) *)
  (*          (nseq_ a (from_uint_size len))) b15 (L1 :|: L2) *)
  (*       (fsetUid *)
  (*          (T:=tag_ordType (I:=choice_type_ordType) *)
  (*                (fun _ : choice_type => nat_ordType))  *)
  (*          (L1 :|: L2)) in *)
  (*   let b17 := *)
  (*     eq_rect (I1 :|: I2 :|: (I1 :|: I2)) *)
  (*       (fun *)
  (*          f : {fset prod_ordType nat_ordType *)
  (*                      (prod_ordType choice_type_ordType *)
  (*                         choice_type_ordType)} => *)
  (*        both (L1 :|: L2) (f :|: (I1 :|: I2)) *)
  (*          (nseq_ a (from_uint_size len))) b16 (I1 :|: I2) *)
  (*       (fsetUid *)
  (*          (T:=prod_ordType nat_ordType *)
  (*                (prod_ordType choice_type_ordType choice_type_ordType)) *)
  (*          (I1 :|: I2)) in *)
  (*   let b18 := *)
  (*     eq_rect (I1 :|: I2 :|: (I1 :|: I2)) *)
  (*       (fun *)
  (*          f : {fset prod_ordType nat_ordType *)
  (*                      (prod_ordType choice_type_ordType *)
  (*                         choice_type_ordType)} => *)
  (*        both (L1 :|: L2) f (nseq_ a (from_uint_size len))) b17  *)
  (*       (I1 :|: I2) *)
  (*       (fsetUid *)
  (*          (T:=prod_ordType nat_ordType *)
  (*                (prod_ordType choice_type_ordType choice_type_ordType)) *)
  (*          (I1 :|: I2)) in *)
  (*   b18) s1. *)

  Fixpoint array_eq_
           {a: choice_type}
           {len: nat}
           (eq: ( (a)) -> ( (a)) -> bool)
           (s1: ( (nseq_ a len)))
           (s2 : ( (nseq_ a len)))
           {struct len}
    : bool.
  Proof.
    destruct len ; cbn in *.
    - exact  true.
    - destruct (getm s1 (fintype.Ordinal (m := len) (ssrnat.ltnSn _))) as [s | ].
      + destruct (getm s2 (fintype.Ordinal (m := len) (ssrnat.ltnSn _))) as [s0 | ].
        * exact (eq s s0).
        * exact false.
      + exact false.
  Defined.

Infix "array_xor" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_xor)) (at level 33) : hacspec_scope.
Infix "array_add" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_add)) (at level 33) : hacspec_scope.
Infix "array_minus" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_sub)) (at level 33) : hacspec_scope.
Infix "array_mul" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_mul)) (at level 33) : hacspec_scope.
Infix "array_div" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_div)) (at level 33) : hacspec_scope.
Infix "array_or" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_or)) (at level 33) : hacspec_scope.
Infix "array_and" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_and)) (at level 33) : hacspec_scope.

Infix "array_eq" := (array_eq_ eq) (at level 33) : hacspec_scope.
Infix "array_neq" := (fun s1 s2 => negb (array_eq_ eq s1 s2)) (at level 33) : hacspec_scope.


(* Handle products of size 1 - 4 for foldi_both' *)
Notation "'ssp(' 'fun' x => 'fun' a => f )" :=
  (((fun x a => f)) : both _ _ uint_size -> both _ _ _ -> both _ _ _) (at level 100, x at next level, f at next level, a at next level).

Notation "'ssp(' 'fun' x => 'fun' ' ( a , b ) => f )" :=
  (((fun x temp =>
       let '(a, b) := split_both temp in
       let '(a, b) := (unsplit_both a, unsplit_both b) in
       f)) : both _ _ uint_size -> both _ _ (_ × _) -> both _ _ _) (at level 100, x at next level, f at next level, a at next level, b at next level).

Notation "'ssp(' 'fun' x => 'fun' ' ( a , b , c ) => f )" :=
  (((fun x temp =>
       let '(a, b, c) := split_both temp in
       let '(a, b, c) := (unsplit_both a, unsplit_both b, unsplit_both c) in
     f)) : both _ _ uint_size -> both _ _ (_ × _ × _) -> both _ _ _) (at level 100, x at next level, f at next level, a at next level, b at next level, c at next level).

Notation "'ssp(' 'fun' x => 'fun' ' ( a , b , c , d ) => f )" :=
  (((fun x temp =>
       let '(a, b, c, d) := split_both temp in
       let '(a, b, c, d) := (unsplit_both a, unsplit_both b, unsplit_both c, unsplit_both d) in
     f)) : both _ _ uint_size -> both _ _ (_ × _ × _ × _) -> both _ _ _) (at level 100, x at next level, f at next level, a at next level, b at next level, c at next level, d at next level).

(* eq_fset *)
(* finmap.finSet *)
(* https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/aac-tactics.2C.20fset.20automation.2C.20universes *)
(* Display map / exponenetial maps *)
