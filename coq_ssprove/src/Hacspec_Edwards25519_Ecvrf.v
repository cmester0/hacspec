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


Require Import Hacspec_Edwards25519.

Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519_Hash.

Definition errorec_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition FailedVerify : errorec_t :=
  inl (inl (inl (inl (inl tt)))).
Definition MessageTooLarge : errorec_t :=
  inl (inl (inl (inl (inr tt)))).
Definition InvalidProof : errorec_t :=
  inl (inl (inl (inr tt))).
Definition InvalidPublicKey : errorec_t :=
  inl (inl (inr tt)).
Definition FailedDecompression : errorec_t :=
  inl (inr tt).
Definition FailedE2C : errorec_t :=
  inr tt.

Notation "'byte_seq_result_t'" := ((result errorec_t byte_seq)) : hacspec_scope.

Notation "'proof_result_t'" := ((result errorec_t (
    ed_point_t ×
    scalar_t ×
    scalar_t
  ))) : hacspec_scope.

Notation "'ed_point_result_t'" := ((
  result errorec_t ed_point_t)) : hacspec_scope.

Definition large_mod_canvas_t := nseq (int8) (usize 32).
Definition large_mod_t :=
  nat_mod 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff.

Definition arr_large_mod_t := nseq (uint64) (usize 4).

Definition q_v : arr_large_mod_t :=
  @array_from_list uint64 [
    (secret (@repr U64 9223372036854775807)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551597)) : uint64
  ].

Definition c_len_v : uint_size :=
  usize 16.

Definition pt_len_v : uint_size :=
  usize 32.

Definition q_len_v : uint_size :=
  usize 32.

Definition int_byte_t := nseq (uint8) (usize 1).

Definition zero_v : int_byte_t :=
  @array_from_list uint8 [(secret (@repr U8 0)) : uint8].

Definition one_v : int_byte_t :=
  @array_from_list uint8 [(secret (@repr U8 1)) : uint8].

Definition two_v : int_byte_t :=
  @array_from_list uint8 [(secret (@repr U8 2)) : uint8].

Definition three_v : int_byte_t :=
  @array_from_list uint8 [(secret (@repr U8 3)) : uint8].

Definition four_v : int_byte_t :=
  @array_from_list uint8 [(secret (@repr U8 4)) : uint8].

Definition suite_string_v : int_byte_t :=
  four_v.

Definition dst_t := nseq (uint8) (usize 39).

Definition h2c_suite_id_string_v : dst_t :=
  @array_from_list uint8 [
    (secret (@repr U8 69)) : uint8;
    (secret (@repr U8 67)) : uint8;
    (secret (@repr U8 86)) : uint8;
    (secret (@repr U8 82)) : uint8;
    (secret (@repr U8 70)) : uint8;
    (secret (@repr U8 95)) : uint8;
    (secret (@repr U8 101)) : uint8;
    (secret (@repr U8 100)) : uint8;
    (secret (@repr U8 119)) : uint8;
    (secret (@repr U8 97)) : uint8;
    (secret (@repr U8 114)) : uint8;
    (secret (@repr U8 100)) : uint8;
    (secret (@repr U8 115)) : uint8;
    (secret (@repr U8 50)) : uint8;
    (secret (@repr U8 53)) : uint8;
    (secret (@repr U8 53)) : uint8;
    (secret (@repr U8 49)) : uint8;
    (secret (@repr U8 57)) : uint8;
    (secret (@repr U8 95)) : uint8;
    (secret (@repr U8 88)) : uint8;
    (secret (@repr U8 77)) : uint8;
    (secret (@repr U8 68)) : uint8;
    (secret (@repr U8 58)) : uint8;
    (secret (@repr U8 83)) : uint8;
    (secret (@repr U8 72)) : uint8;
    (secret (@repr U8 65)) : uint8;
    (secret (@repr U8 45)) : uint8;
    (secret (@repr U8 53)) : uint8;
    (secret (@repr U8 49)) : uint8;
    (secret (@repr U8 50)) : uint8;
    (secret (@repr U8 95)) : uint8;
    (secret (@repr U8 69)) : uint8;
    (secret (@repr U8 76)) : uint8;
    (secret (@repr U8 76)) : uint8;
    (secret (@repr U8 50)) : uint8;
    (secret (@repr U8 95)) : uint8;
    (secret (@repr U8 78)) : uint8;
    (secret (@repr U8 85)) : uint8;
    (secret (@repr U8 95)) : uint8
  ].

Definition h_3029_loc : ChoiceEqualityLocation :=
  ((option (ed_point_t)) ; 3031%nat).
Definition x_3030_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 3032%nat).
Notation "'ecvrf_encode_to_curve_try_and_increment_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ecvrf_encode_to_curve_try_and_increment_out'" :=(
  ed_point_result_t : choice_type) (in custom pack_type at level 2).
Definition ECVRF_ENCODE_TO_CURVE_TRY_AND_INCREMENT : nat :=
  3039.
Program Definition ecvrf_encode_to_curve_try_and_increment (
    encode_to_curve_salt_3035 : byte_seq) (alpha_3036 : byte_seq)
  : both (CEfset ([h_3029_loc ; x_3030_loc])) [interface] (ed_point_result_t) :=
  ((letbm h_3029 : (option (ed_point_t)) loc( h_3029_loc ) :=
        @None ed_point_t in
      letbm x_3030 : ed25519_field_element_t loc( x_3030_loc ) :=
        nat_mod_zero  in
      letb '(h_3029, x_3030) :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 256)) prod_ce(h_3029, x_3030) (L := (CEfset (
                [h_3029_loc ; x_3030_loc]))) (I := [interface]) (fun ctr_3033 '(
              h_3029,
              x_3030
            ) =>
            letb '(h_3029, x_3030) :=
              if ((lift_to_both0 h_3029)) =.? (
                @None ed_point_t) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([h_3029_loc ; x_3030_loc])) (
                L2 := CEfset ([h_3029_loc ; x_3030_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb ctr_string_3034 : seq uint8 :=
                  seq_slice (nat_mod_to_byte_seq_be (lift_to_both0 x_3030)) (
                    lift_to_both0 (usize 31)) (lift_to_both0 (usize 1)) in
                letb hash_string_3037 : sha512_digest_t :=
                  sha512 (seq_concat (seq_concat (seq_concat (seq_concat (
                            array_concat (lift_to_both0 suite_string_v) (
                              array_to_seq (lift_to_both0 one_v))) (
                            lift_to_both0 encode_to_curve_salt_3035)) (
                          lift_to_both0 alpha_3036)) (
                        lift_to_both0 ctr_string_3034)) (
                      array_to_seq (lift_to_both0 zero_v))) in
                letbm h_3029 loc( h_3029_loc ) :=
                  decompress (array_from_slice (default : uint8) (32) (
                      array_to_seq (lift_to_both0 hash_string_3037)) (
                      lift_to_both0 (usize 0)) (lift_to_both0 (usize 32))) in
                letbm x_3030 loc( x_3030_loc ) :=
                  (lift_to_both0 x_3030) +% (nat_mod_one ) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 h_3029,
                    lift_to_both0 x_3030
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 h_3029,
                  lift_to_both0 x_3030
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 h_3029,
                lift_to_both0 x_3030
              ))
            ) in
      letbnd(_) h_3038 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (lift_to_both0 h_3029) (FailedE2C) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok ed_point_t errorec_t (point_mul_by_cofactor (lift_to_both0 h_3038)))
      ) : both (CEfset ([h_3029_loc ; x_3030_loc])) [interface] (
      ed_point_result_t)).
Fail Next Obligation.


Notation "'ecvrf_encode_to_curve_h2c_suite_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ecvrf_encode_to_curve_h2c_suite_out'" :=(
  ed_point_result_t : choice_type) (in custom pack_type at level 2).
Definition ECVRF_ENCODE_TO_CURVE_H2C_SUITE : nat :=
  3046.
Program Definition ecvrf_encode_to_curve_h2c_suite (
    encode_to_curve_salt_3040 : byte_seq) (alpha_3041 : byte_seq)
  : both (fset.fset0) [interface] (ed_point_result_t) :=
  ((letb string_to_be_hashed_3042 : seq uint8 :=
        seq_concat (lift_to_both0 encode_to_curve_salt_3040) (
          lift_to_both0 alpha_3041) in
      letb dst_3043 : seq uint8 :=
        array_concat (lift_to_both0 h2c_suite_id_string_v) (
          array_to_seq (lift_to_both0 suite_string_v)) in
      letb h_3044 : (result (error_t) ((
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ))) :=
        ed_encode_to_curve (lift_to_both0 string_to_be_hashed_3042) (
          lift_to_both0 dst_3043) in
      letbnd(_) h_3045 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (result_ok (lift_to_both0 h_3044)) (FailedE2C) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok ed_point_t errorec_t (lift_to_both0 h_3045))
      ) : both (fset.fset0) [interface] (ed_point_result_t)).
Fail Next Obligation.


Notation "'ecvrf_nonce_generation_inp'" :=(
  secret_key_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ecvrf_nonce_generation_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Definition ECVRF_NONCE_GENERATION : nat :=
  3054.
Program Definition ecvrf_nonce_generation (sk_3047 : secret_key_t) (
    h_string_3050 : byte_seq)
  : both (fset.fset0) [interface] (scalar_t) :=
  ((letb hashed_sk_string_3048 : sha512_digest_t :=
        sha512 (array_to_le_bytes (lift_to_both0 sk_3047)) in
      letb truncated_hashed_sk_string_3049 : seq uint8 :=
        array_slice (lift_to_both0 hashed_sk_string_3048) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letb k_string_3051 : sha512_digest_t :=
        sha512 (seq_concat (lift_to_both0 truncated_hashed_sk_string_3049) (
            lift_to_both0 h_string_3050)) in
      letb nonce_3052 : big_scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 k_string_3051)) in
      letb nonceseq_3053 : seq uint8 :=
        seq_slice (nat_mod_to_byte_seq_le (lift_to_both0 nonce_3052)) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        nat_mod_from_byte_seq_le (lift_to_both0 nonceseq_3053))
      ) : both (fset.fset0) [interface] (scalar_t)).
Fail Next Obligation.


Notation "'ecvrf_challenge_generation_inp'" :=(
  ed_point_t × ed_point_t × ed_point_t × ed_point_t × ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ecvrf_challenge_generation_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Definition ECVRF_CHALLENGE_GENERATION : nat :=
  3063.
Program Definition ecvrf_challenge_generation (p1_3055 : ed_point_t) (
    p2_3056 : ed_point_t) (p3_3057 : ed_point_t) (p4_3058 : ed_point_t) (
    p5_3059 : ed_point_t)
  : both (fset.fset0) [interface] (scalar_t) :=
  ((letb string_3060 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (seq_concat (seq_concat (
                    array_concat (lift_to_both0 suite_string_v) (
                      array_to_seq (lift_to_both0 two_v))) (encode (
                      lift_to_both0 p1_3055))) (encode (
                    lift_to_both0 p2_3056))) (encode (lift_to_both0 p3_3057))) (
              encode (lift_to_both0 p4_3058))) (encode (
              lift_to_both0 p5_3059))) (array_to_seq (lift_to_both0 zero_v)) in
      letb c_string_3061 : sha512_digest_t :=
        sha512 (lift_to_both0 string_3060) in
      letb truncated_c_string_3062 : seq uint8 :=
        seq_concat (array_slice (lift_to_both0 c_string_3061) (lift_to_both0 (
              usize 0)) (lift_to_both0 c_len_v)) (seq_new_ (default : uint8) (
            lift_to_both0 (usize 16))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        nat_mod_from_byte_seq_le (lift_to_both0 truncated_c_string_3062))
      ) : both (fset.fset0) [interface] (scalar_t)).
Fail Next Obligation.


Notation "'ecvrf_decode_proof_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ecvrf_decode_proof_out'" :=(
  proof_result_t : choice_type) (in custom pack_type at level 2).
Definition ECVRF_DECODE_PROOF : nat :=
  3073.
Program Definition ecvrf_decode_proof (pi_3064 : byte_seq)
  : both (fset.fset0) [interface] (proof_result_t) :=
  ((letb gamma_string_3065 : seq uint8 :=
        seq_slice (lift_to_both0 pi_3064) (lift_to_both0 (usize 0)) (
          lift_to_both0 pt_len_v) in
      letb c_string_3066 : seq uint8 :=
        seq_slice (lift_to_both0 pi_3064) (lift_to_both0 pt_len_v) (
          lift_to_both0 c_len_v) in
      letb s_string_3067 : seq uint8 :=
        seq_slice (lift_to_both0 pi_3064) ((lift_to_both0 pt_len_v) .+ (
            lift_to_both0 c_len_v)) (lift_to_both0 q_len_v) in
      letbnd(_) gamma_3068 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (array_from_slice (default : uint8) (32) (
              lift_to_both0 gamma_string_3065) (lift_to_both0 (usize 0)) (
              lift_to_both0 (usize 32)))) (InvalidProof) in
      letb c_3069 : scalar_t :=
        nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 c_string_3066) (
            seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
      letb s_3070 : scalar_t :=
        nat_mod_from_byte_seq_le ((lift_to_both0 s_string_3067)) in
      letb s_test_3071 : large_mod_t :=
        nat_mod_from_byte_seq_le (lift_to_both0 s_string_3067) in
      letb q_3072 : large_mod_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 q_v)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 s_test_3071) >=.? (
            lift_to_both0 q_3072))
        then @Err (ed_point_t '× scalar_t '× scalar_t) errorec_t (
          InvalidProof)
        else @Ok (ed_point_t '× scalar_t '× scalar_t) errorec_t (prod_b(
            lift_to_both0 gamma_3068,
            lift_to_both0 c_3069,
            lift_to_both0 s_3070
          )))
      ) : both (fset.fset0) [interface] (proof_result_t)).
Fail Next Obligation.


Notation "'ecvrf_validate_key_inp'" :=(
  public_key_t : choice_type) (in custom pack_type at level 2).
Notation "'ecvrf_validate_key_out'" :=((result (errorec_t) (
      unit_ChoiceEquality)) : choice_type) (in custom pack_type at level 2).
Definition ECVRF_VALIDATE_KEY : nat :=
  3077.
Program Definition ecvrf_validate_key (y_3074 : public_key_t)
  : both (fset.fset0) [interface] ((result (errorec_t) (
        unit_ChoiceEquality))) :=
  ((letbnd(_) y_3075 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 y_3074)) (InvalidPublicKey) in
      letb y_prime_3076 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 y_3075) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 y_prime_3076) =.? (
            point_identity ))
        then @Err unit_ChoiceEquality errorec_t (InvalidPublicKey)
        else @Ok unit_ChoiceEquality errorec_t (tt))
      ) : both (fset.fset0) [interface] ((result (errorec_t) (
          unit_ChoiceEquality)))).
Fail Next Obligation.


Notation "'ecvrf_prove_inp'" :=(
  secret_key_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ecvrf_prove_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition ECVRF_PROVE : nat :=
  3094.
Program Definition ecvrf_prove (sk_3079 : secret_key_t) (alpha_3085 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letbnd(_) b_3078 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 base_v)) (
          FailedDecompression) in
      letb '(x_3080, _) : (serialized_scalar_t '× serialized_scalar_t) :=
        secret_expand (lift_to_both0 sk_3079) in
      letb x_3081 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 x_3080)) in
      letb y_3082 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 x_3081) (lift_to_both0 b_3078) in
      letb pk_3083 : compressed_ed_point_t := compress (lift_to_both0 y_3082) in
      letb encode_to_curve_salt_3084 : seq uint8 :=
        array_slice (lift_to_both0 pk_3083) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 32)) in
      letbnd(_) h_3086 : ed_point_t :=
        ecvrf_encode_to_curve_h2c_suite (
          lift_to_both0 encode_to_curve_salt_3084) (lift_to_both0 alpha_3085) in
      letb h_string_3087 : seq uint8 := encode (lift_to_both0 h_3086) in
      letb gamma_3088 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 x_3081) (lift_to_both0 h_3086) in
      letb k_3089 : scalar_t :=
        ecvrf_nonce_generation (lift_to_both0 sk_3079) (
          lift_to_both0 h_string_3087) in
      letb u_3090 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 k_3089) (lift_to_both0 b_3078) in
      letb v_3091 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 k_3089) (lift_to_both0 h_3086) in
      letb c_3092 : scalar_t :=
        ecvrf_challenge_generation (lift_to_both0 y_3082) (
          lift_to_both0 h_3086) (lift_to_both0 gamma_3088) (
          lift_to_both0 u_3090) (lift_to_both0 v_3091) in
      letb s_3093 : scalar_t :=
        (lift_to_both0 k_3089) +% ((lift_to_both0 c_3092) *% (
            lift_to_both0 x_3081)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok byte_seq errorec_t (
          seq_slice (seq_concat (seq_concat (encode (
                  lift_to_both0 gamma_3088)) (seq_slice (
                  nat_mod_to_byte_seq_le (lift_to_both0 c_3092)) (
                  lift_to_both0 (usize 0)) (lift_to_both0 c_len_v))) (
              seq_slice (nat_mod_to_byte_seq_le (lift_to_both0 s_3093)) (
                lift_to_both0 (usize 0)) (lift_to_both0 q_len_v))) (
            lift_to_both0 (usize 0)) (((lift_to_both0 c_len_v) .+ (
                lift_to_both0 q_len_v)) .+ (lift_to_both0 pt_len_v))))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.


Notation "'ecvrf_proof_to_hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ecvrf_proof_to_hash_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition ECVRF_PROOF_TO_HASH : nat :=
  3097.
Program Definition ecvrf_proof_to_hash (pi_3095 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letbnd(_) '(gamma_3096, _, _) : (ed_point_t '× scalar_t '× scalar_t) :=
        ecvrf_decode_proof (lift_to_both0 pi_3095) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok byte_seq errorec_t (
          array_slice (sha512 (seq_concat (seq_concat (array_concat (
                    lift_to_both0 suite_string_v) (
                    array_to_seq (lift_to_both0 three_v))) (encode (
                    point_mul_by_cofactor (lift_to_both0 gamma_3096)))) (
                array_to_seq (lift_to_both0 zero_v)))) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 64))))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.


Notation "'ecvrf_verify_inp'" :=(
  public_key_t × byte_seq × byte_seq × bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'ecvrf_verify_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition ECVRF_VERIFY : nat :=
  3112.
Program Definition ecvrf_verify (pk_3099 : public_key_t) (
    alpha_3107 : byte_seq) (pi_3102 : byte_seq) (
    validate_key_3101 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letbnd(_) b_3098 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 base_v)) (
          FailedDecompression) in
      letbnd(_) y_3100 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_3099)) (InvalidPublicKey) in
      letbnd(ChoiceEqualityMonad.result_bind_both errorec_t) 'tt :=
        if lift_to_both0 validate_key_3101 :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            ecvrf_validate_key (lift_to_both0 pk_3099) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality errorec_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality errorec_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbnd(_) '(gamma_3103, c_3104, s_3105) : (
          ed_point_t '×
          scalar_t '×
          scalar_t
        ) :=
        ecvrf_decode_proof (lift_to_both0 pi_3102) in
      letb encode_to_curve_salt_3106 : seq uint8 :=
        array_slice (lift_to_both0 pk_3099) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 32)) in
      letbnd(_) h_3108 : ed_point_t :=
        ecvrf_encode_to_curve_h2c_suite (
          lift_to_both0 encode_to_curve_salt_3106) (lift_to_both0 alpha_3107) in
      letb u_3109 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (point_mul (lift_to_both0 s_3105) (lift_to_both0 b_3098)) (
          point_neg (point_mul (lift_to_both0 c_3104) (
              lift_to_both0 y_3100))) in
      letb v_3110 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (point_mul (lift_to_both0 s_3105) (lift_to_both0 h_3108)) (
          point_neg (point_mul (lift_to_both0 c_3104) (
              lift_to_both0 gamma_3103))) in
      letb c_prime_3111 : scalar_t :=
        ecvrf_challenge_generation (lift_to_both0 y_3100) (
          lift_to_both0 h_3108) (lift_to_both0 gamma_3103) (
          lift_to_both0 u_3109) (lift_to_both0 v_3110) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 c_3104) =.? (
            lift_to_both0 c_prime_3111))
        then ecvrf_proof_to_hash (lift_to_both0 pi_3102)
        else @Err byte_seq errorec_t (FailedVerify))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.

