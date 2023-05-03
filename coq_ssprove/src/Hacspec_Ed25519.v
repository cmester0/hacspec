(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519.


Notation "'scalar_from_hash_inp'" :=(
  sha512_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_hash_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Definition SCALAR_FROM_HASH : nat :=
  2463.
Program Definition scalar_from_hash (h_2461 : sha512_digest_t)
  : both (fset.fset0) [interface] (scalar_t) :=
  ((letb s_2462 : big_scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 h_2461)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (
              lift_to_both0 s_2462)) (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 32))))
      ) : both (fset.fset0) [interface] (scalar_t)).
Fail Next Obligation.


Notation "'sign_inp'" :=(
  secret_key_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" :=(
  signature_t : choice_type) (in custom pack_type at level 2).
Definition SIGN : nat :=
  2477.
Program Definition sign (sk_2464 : secret_key_t) (msg_2470 : byte_seq)
  : both (fset.fset0) [interface] (signature_t) :=
  ((letb '(a_2465, prefix_2466) : (serialized_scalar_t '× serialized_scalar_t
        ) :=
        secret_expand (lift_to_both0 sk_2464) in
      letb a_2467 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 a_2465)) in
      letb b_2468 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb a_p_2469 : compressed_ed_point_t :=
        compress (point_mul (lift_to_both0 a_2467) (lift_to_both0 b_2468)) in
      letb r_2471 : scalar_t :=
        scalar_from_hash (sha512 (array_concat (lift_to_both0 prefix_2466) (
              lift_to_both0 msg_2470))) in
      letb r_p_2472 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 r_2471) (lift_to_both0 b_2468) in
      letb r_s_2473 : compressed_ed_point_t :=
        compress (lift_to_both0 r_p_2472) in
      letb h_2474 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_s_2473) (
                array_to_seq (lift_to_both0 a_p_2469))) (
              lift_to_both0 msg_2470))) in
      letb s_2475 : scalar_t :=
        (lift_to_both0 r_2471) +% ((lift_to_both0 h_2474) *% (
            lift_to_both0 a_2467)) in
      letb s_bytes_2476 : seq uint8 :=
        seq_slice (nat_mod_to_byte_seq_le (lift_to_both0 s_2475)) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update (
          array_update (array_new_ (default : uint8) (64)) (lift_to_both0 (
              usize 0)) (array_to_seq (lift_to_both0 r_s_2473))) (
          lift_to_both0 (usize 32)) (lift_to_both0 s_bytes_2476))
      ) : both (fset.fset0) [interface] (signature_t)).
Fail Next Obligation.


Notation "'zcash_verify_inp'" :=(
  public_key_t × signature_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ZCASH_VERIFY : nat :=
  2491.
Program Definition zcash_verify (pk_2479 : public_key_t) (
    signature_2481 : signature_t) (msg_2486 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2478 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress_non_canonical (lift_to_both0 base_v)) in
      letbnd(_) a_2480 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (lift_to_both0 pk_2479)) (
          InvalidPublickey) in
      letb r_bytes_2482 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2481)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2483 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2481)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2483)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (InvalidS) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbnd(_) r_2484 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (lift_to_both0 r_bytes_2482)) (
          InvalidR) in
      letb s_2485 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2483)) in
      letb k_2487 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2482) (lift_to_both0 pk_2479)) (
              lift_to_both0 msg_2486))) in
      letb sb_2488 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2485) (
            lift_to_both0 b_2478)) in
      letb rc_2489 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2484) in
      letb ka_2490 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2487) (
            lift_to_both0 a_2480)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2488) (
            point_add (lift_to_both0 rc_2489) (lift_to_both0 ka_2490)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.


Notation "'ietf_cofactored_verify_inp'" :=(
  public_key_t × signature_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition IETF_COFACTORED_VERIFY : nat :=
  2505.
Program Definition ietf_cofactored_verify (pk_2493 : public_key_t) (
    signature_2495 : signature_t) (msg_2500 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2492 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2494 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2493)) (InvalidPublickey) in
      letb r_bytes_2496 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2495)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2497 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2495)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2497)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (InvalidS) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbnd(_) r_2498 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2496)) (InvalidR) in
      letb s_2499 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2497)) in
      letb k_2501 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2496) (lift_to_both0 pk_2493)) (
              lift_to_both0 msg_2500))) in
      letb sb_2502 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2499) (
            lift_to_both0 b_2492)) in
      letb rc_2503 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2498) in
      letb ka_2504 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2501) (
            lift_to_both0 a_2494)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2502) (
            point_add (lift_to_both0 rc_2503) (lift_to_both0 ka_2504)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.


Notation "'ietf_cofactorless_verify_inp'" :=(
  public_key_t × signature_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition IETF_COFACTORLESS_VERIFY : nat :=
  2518.
Program Definition ietf_cofactorless_verify (pk_2507 : public_key_t) (
    signature_2509 : signature_t) (msg_2514 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2506 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2508 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2507)) (InvalidPublickey) in
      letb r_bytes_2510 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2509)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2511 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2509)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2511)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (InvalidS) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbnd(_) r_2512 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2510)) (InvalidR) in
      letb s_2513 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2511)) in
      letb k_2515 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2510) (lift_to_both0 pk_2507)) (
              lift_to_both0 msg_2514))) in
      letb sb_2516 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_2513) (lift_to_both0 b_2506) in
      letb ka_2517 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 k_2515) (lift_to_both0 a_2508) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2516) (
            point_add (lift_to_both0 r_2512) (lift_to_both0 ka_2517)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.


Notation "'is_identity_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'is_identity_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition IS_IDENTITY : nat :=
  2520.
Program Definition is_identity (p_2519 : ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_eq (
          lift_to_both0 p_2519) (point_identity ))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'alg2_verify_inp'" :=(
  public_key_t × signature_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg2_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ALG2_VERIFY : nat :=
  2534.
Program Definition alg2_verify (pk_2522 : public_key_t) (
    signature_2524 : signature_t) (msg_2529 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2521 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2523 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2522)) (InvalidPublickey) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if is_identity (point_mul_by_cofactor (
            lift_to_both0 a_2523)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (SmallOrderPoint) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letb r_bytes_2525 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2524)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2526 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2524)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2526)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (InvalidS) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbnd(_) r_2527 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2525)) (InvalidR) in
      letb s_2528 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2526)) in
      letb k_2530 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2525) (lift_to_both0 pk_2522)) (
              lift_to_both0 msg_2529))) in
      letb sb_2531 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2528) (
            lift_to_both0 b_2521)) in
      letb rc_2532 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2527) in
      letb ka_2533 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2530) (
            lift_to_both0 a_2523)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2531) (
            point_add (lift_to_both0 rc_2532) (lift_to_both0 ka_2533)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.

Definition batch_entry_t : ChoiceEquality :=
  (public_key_t '× byte_seq '× signature_t).
Definition BatchEntry (x : (public_key_t '× byte_seq '× signature_t
    )) : batch_entry_t :=
   x.

Definition s_sum_2535_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2538%nat).
Definition r_sum_2536_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2539%nat).
Definition a_sum_2537_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2540%nat).
Notation "'zcash_batch_verify_inp'" :=(
  seq batch_entry_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ZCASH_BATCH_VERIFY : nat :=
  2558.
Program Definition zcash_batch_verify (entries_2542 : seq batch_entry_t) (
    entropy_2541 : byte_seq)
  : both (CEfset (
      [s_sum_2535_loc ; r_sum_2536_loc ; a_sum_2537_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2541)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2542))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2535_loc ; r_sum_2536_loc ; a_sum_2537_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (NotEnoughRandomness) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbm s_sum_2535 : scalar_t loc( s_sum_2535_loc ) := nat_mod_zero  in
      letbm r_sum_2536 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2536_loc ) :=
        point_identity  in
      letbm a_sum_2537 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2537_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2535,
          r_sum_2536,
          a_sum_2537
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2542)) prod_ce(
            s_sum_2535,
            r_sum_2536,
            a_sum_2537
          ) (L := (CEfset (
                [s_sum_2535_loc ; r_sum_2536_loc ; a_sum_2537_loc]))) (
            I := [interface]) (fun i_2543 '(s_sum_2535, r_sum_2536, a_sum_2537
            ) =>
            letb BatchEntry ((pk_2544, msg_2545, signature_2546
                )) : batch_entry_t :=
              (seq_index (entries_2542) (lift_to_both0 i_2543)) in
            letbnd(_) a_2547 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (lift_to_both0 pk_2544)) (
                InvalidPublickey) in
            letb r_bytes_2548 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2546)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2549 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2546)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2549)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2535_loc ; r_sum_2536_loc ; a_sum_2537_loc])) (
                L2 := CEfset (
                  [s_sum_2535_loc ; r_sum_2536_loc ; a_sum_2537_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (InvalidS) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letbnd(_) r_2550 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (
                  lift_to_both0 r_bytes_2548)) (InvalidR) in
            letb s_2551 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2549)) in
            letb c_2552 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2548) (
                      array_to_seq (lift_to_both0 pk_2544))) (
                    lift_to_both0 msg_2545))) in
            letb z_2553 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2541) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2543)) (lift_to_both0 (
                  usize 16)) in
            letb z_2554 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2553) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2535 loc( s_sum_2535_loc ) :=
              (lift_to_both0 s_sum_2535) +% ((lift_to_both0 s_2551) *% (
                  lift_to_both0 z_2554)) in
            letbm r_sum_2536 loc( r_sum_2536_loc ) :=
              point_add (lift_to_both0 r_sum_2536) (point_mul (
                  lift_to_both0 z_2554) (lift_to_both0 r_2550)) in
            letbm a_sum_2537 loc( a_sum_2537_loc ) :=
              point_add (lift_to_both0 a_sum_2537) (point_mul ((
                    lift_to_both0 z_2554) *% (lift_to_both0 c_2552)) (
                  lift_to_both0 a_2547)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                scalar_t '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                ) '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )
              ) error_t (prod_b(
                  lift_to_both0 s_sum_2535,
                  lift_to_both0 r_sum_2536,
                  lift_to_both0 a_sum_2537
                )))
            ) in
      letb b_2555 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2556 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2535) (lift_to_both0 b_2555) in
      letb check_2557 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2556)) (
            point_add (lift_to_both0 r_sum_2536) (lift_to_both0 a_sum_2537))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2557))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2535_loc ; r_sum_2536_loc ; a_sum_2537_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition r_sum_2560_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2562%nat).
Definition s_sum_2559_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2563%nat).
Definition a_sum_2561_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2564%nat).
Notation "'ietf_cofactored_batch_verify_inp'" :=(
  seq batch_entry_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition IETF_COFACTORED_BATCH_VERIFY : nat :=
  2582.
Program Definition ietf_cofactored_batch_verify (
    entries_2566 : seq batch_entry_t) (entropy_2565 : byte_seq)
  : both (CEfset (
      [s_sum_2559_loc ; r_sum_2560_loc ; a_sum_2561_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2565)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2566))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2559_loc ; r_sum_2560_loc ; a_sum_2561_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (NotEnoughRandomness) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbm s_sum_2559 : scalar_t loc( s_sum_2559_loc ) := nat_mod_zero  in
      letbm r_sum_2560 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2560_loc ) :=
        point_identity  in
      letbm a_sum_2561 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2561_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2559,
          r_sum_2560,
          a_sum_2561
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2566)) prod_ce(
            s_sum_2559,
            r_sum_2560,
            a_sum_2561
          ) (L := (CEfset (
                [s_sum_2559_loc ; r_sum_2560_loc ; a_sum_2561_loc]))) (
            I := [interface]) (fun i_2567 '(s_sum_2559, r_sum_2560, a_sum_2561
            ) =>
            letb BatchEntry ((pk_2568, msg_2569, signature_2570
                )) : batch_entry_t :=
              (seq_index (entries_2566) (lift_to_both0 i_2567)) in
            letbnd(_) a_2571 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2568)) (
                InvalidPublickey) in
            letb r_bytes_2572 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2570)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2573 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2570)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2573)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2559_loc ; r_sum_2560_loc ; a_sum_2561_loc])) (
                L2 := CEfset (
                  [s_sum_2559_loc ; r_sum_2560_loc ; a_sum_2561_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (InvalidS) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letbnd(_) r_2574 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2572)) (
                InvalidR) in
            letb s_2575 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2573)) in
            letb c_2576 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2572) (
                      array_to_seq (lift_to_both0 pk_2568))) (
                    lift_to_both0 msg_2569))) in
            letb z_2577 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2565) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2567)) (lift_to_both0 (
                  usize 16)) in
            letb z_2578 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2577) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2559 loc( s_sum_2559_loc ) :=
              (lift_to_both0 s_sum_2559) +% ((lift_to_both0 s_2575) *% (
                  lift_to_both0 z_2578)) in
            letbm r_sum_2560 loc( r_sum_2560_loc ) :=
              point_add (lift_to_both0 r_sum_2560) (point_mul (
                  lift_to_both0 z_2578) (lift_to_both0 r_2574)) in
            letbm a_sum_2561 loc( a_sum_2561_loc ) :=
              point_add (lift_to_both0 a_sum_2561) (point_mul ((
                    lift_to_both0 z_2578) *% (lift_to_both0 c_2576)) (
                  lift_to_both0 a_2571)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                scalar_t '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                ) '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )
              ) error_t (prod_b(
                  lift_to_both0 s_sum_2559,
                  lift_to_both0 r_sum_2560,
                  lift_to_both0 a_sum_2561
                )))
            ) in
      letb b_2579 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2580 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2559) (lift_to_both0 b_2579) in
      letb check_2581 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2580)) (
            point_add (lift_to_both0 r_sum_2560) (lift_to_both0 a_sum_2561))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2581))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2559_loc ; r_sum_2560_loc ; a_sum_2561_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition r_sum_2584_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2586%nat).
Definition a_sum_2585_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2587%nat).
Definition s_sum_2583_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2588%nat).
Notation "'ietf_cofactorless_batch_verify_inp'" :=(
  seq batch_entry_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition IETF_COFACTORLESS_BATCH_VERIFY : nat :=
  2606.
Program Definition ietf_cofactorless_batch_verify (
    entries_2590 : seq batch_entry_t) (entropy_2589 : byte_seq)
  : both (CEfset (
      [s_sum_2583_loc ; r_sum_2584_loc ; a_sum_2585_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2589)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2590))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2583_loc ; r_sum_2584_loc ; a_sum_2585_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (NotEnoughRandomness) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbm s_sum_2583 : scalar_t loc( s_sum_2583_loc ) := nat_mod_zero  in
      letbm r_sum_2584 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2584_loc ) :=
        point_identity  in
      letbm a_sum_2585 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2585_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2583,
          r_sum_2584,
          a_sum_2585
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2590)) prod_ce(
            s_sum_2583,
            r_sum_2584,
            a_sum_2585
          ) (L := (CEfset (
                [s_sum_2583_loc ; r_sum_2584_loc ; a_sum_2585_loc]))) (
            I := [interface]) (fun i_2591 '(s_sum_2583, r_sum_2584, a_sum_2585
            ) =>
            letb BatchEntry ((pk_2592, msg_2593, signature_2594
                )) : batch_entry_t :=
              (seq_index (entries_2590) (lift_to_both0 i_2591)) in
            letbnd(_) a_2595 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2592)) (
                InvalidPublickey) in
            letb r_bytes_2596 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2594)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2597 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2594)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2597)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2583_loc ; r_sum_2584_loc ; a_sum_2585_loc])) (
                L2 := CEfset (
                  [s_sum_2583_loc ; r_sum_2584_loc ; a_sum_2585_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (InvalidS) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letbnd(_) r_2598 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2596)) (
                InvalidR) in
            letb s_2599 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2597)) in
            letb c_2600 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2596) (
                      array_to_seq (lift_to_both0 pk_2592))) (
                    lift_to_both0 msg_2593))) in
            letb z_2601 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2589) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2591)) (lift_to_both0 (
                  usize 16)) in
            letb z_2602 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2601) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2583 loc( s_sum_2583_loc ) :=
              (lift_to_both0 s_sum_2583) +% ((lift_to_both0 s_2599) *% (
                  lift_to_both0 z_2602)) in
            letbm r_sum_2584 loc( r_sum_2584_loc ) :=
              point_add (lift_to_both0 r_sum_2584) (point_mul (
                  lift_to_both0 z_2602) (lift_to_both0 r_2598)) in
            letbm a_sum_2585 loc( a_sum_2585_loc ) :=
              point_add (lift_to_both0 a_sum_2585) (point_mul ((
                    lift_to_both0 z_2602) *% (lift_to_both0 c_2600)) (
                  lift_to_both0 a_2595)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                scalar_t '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                ) '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )
              ) error_t (prod_b(
                  lift_to_both0 s_sum_2583,
                  lift_to_both0 r_sum_2584,
                  lift_to_both0 a_sum_2585
                )))
            ) in
      letb b_2603 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2604 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2583) (lift_to_both0 b_2603) in
      letb check_2605 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (point_neg (lift_to_both0 sb_2604)) (point_add (
            lift_to_both0 r_sum_2584) (lift_to_both0 a_sum_2585)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2605))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2583_loc ; r_sum_2584_loc ; a_sum_2585_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition a_sum_2609_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2610%nat).
Definition s_sum_2607_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2611%nat).
Definition r_sum_2608_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2612%nat).
Notation "'alg3_batch_verify_inp'" :=(
  seq batch_entry_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ALG3_BATCH_VERIFY : nat :=
  2630.
Program Definition alg3_batch_verify (entries_2614 : seq batch_entry_t) (
    entropy_2613 : byte_seq)
  : both (CEfset (
      [s_sum_2607_loc ; r_sum_2608_loc ; a_sum_2609_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2613)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2614))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2607_loc ; r_sum_2608_loc ; a_sum_2609_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (NotEnoughRandomness) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbm s_sum_2607 : scalar_t loc( s_sum_2607_loc ) := nat_mod_zero  in
      letbm r_sum_2608 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2608_loc ) :=
        point_identity  in
      letbm a_sum_2609 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2609_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2607,
          r_sum_2608,
          a_sum_2609
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2614)) prod_ce(
            s_sum_2607,
            r_sum_2608,
            a_sum_2609
          ) (L := (CEfset (
                [s_sum_2607_loc ; r_sum_2608_loc ; a_sum_2609_loc]))) (
            I := [interface]) (fun i_2615 '(s_sum_2607, r_sum_2608, a_sum_2609
            ) =>
            letb BatchEntry ((pk_2616, msg_2617, signature_2618
                )) : batch_entry_t :=
              (seq_index (entries_2614) (lift_to_both0 i_2615)) in
            letbnd(_) a_2619 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2616)) (
                InvalidPublickey) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if is_identity (point_mul_by_cofactor (
                  lift_to_both0 a_2619)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2607_loc ; r_sum_2608_loc ; a_sum_2609_loc])) (
                L2 := CEfset (
                  [s_sum_2607_loc ; r_sum_2608_loc ; a_sum_2609_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (SmallOrderPoint) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letb r_bytes_2620 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2618)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2621 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2618)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2621)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2607_loc ; r_sum_2608_loc ; a_sum_2609_loc])) (
                L2 := CEfset (
                  [s_sum_2607_loc ; r_sum_2608_loc ; a_sum_2609_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (InvalidS) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letbnd(_) r_2622 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2620)) (
                InvalidR) in
            letb s_2623 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2621)) in
            letb c_2624 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2620) (
                      array_to_seq (lift_to_both0 pk_2616))) (
                    lift_to_both0 msg_2617))) in
            letb z_2625 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2613) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2615)) (lift_to_both0 (
                  usize 16)) in
            letb z_2626 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2625) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2607 loc( s_sum_2607_loc ) :=
              (lift_to_both0 s_sum_2607) +% ((lift_to_both0 s_2623) *% (
                  lift_to_both0 z_2626)) in
            letbm r_sum_2608 loc( r_sum_2608_loc ) :=
              point_add (lift_to_both0 r_sum_2608) (point_mul (
                  lift_to_both0 z_2626) (lift_to_both0 r_2622)) in
            letbm a_sum_2609 loc( a_sum_2609_loc ) :=
              point_add (lift_to_both0 a_sum_2609) (point_mul ((
                    lift_to_both0 z_2626) *% (lift_to_both0 c_2624)) (
                  lift_to_both0 a_2619)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                scalar_t '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                ) '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )
              ) error_t (prod_b(
                  lift_to_both0 s_sum_2607,
                  lift_to_both0 r_sum_2608,
                  lift_to_both0 a_sum_2609
                )))
            ) in
      letb b_2627 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2628 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2607) (lift_to_both0 b_2627) in
      letb check_2629 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2628)) (
            point_add (lift_to_both0 r_sum_2608) (lift_to_both0 a_sum_2609))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2629))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2607_loc ; r_sum_2608_loc ; a_sum_2609_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

