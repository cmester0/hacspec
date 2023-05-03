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

Definition b_in_bytes_v : uint_size :=
  usize 64.

Definition s_in_bytes_v : uint_size :=
  usize 128.

Definition l_v : uint_size :=
  usize 48.

Definition j_v : int128 :=
  @repr U128 486662.

Definition z_v : int128 :=
  @repr U128 2.

Definition arr_ed25519_field_element_t := nseq (uint64) (usize 4).

Definition ed_field_hash_canvas_t := nseq (int8) (usize 64).
Definition ed_field_hash_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality.
Definition ExpandMessageAbort : error_t :=
   tt.

Notation "'byte_seq_result_t'" := ((result error_t byte_seq)) : hacspec_scope.

Notation "'seq_ed_result_t'" := ((
  result error_t seq ed25519_field_element_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((result error_t ed_point_t)) : hacspec_scope.

Definition p_1_2_v : arr_ed25519_field_element_t :=
  @array_from_list uint64 [
    (secret (@repr U64 4611686018427387903)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551606)) : uint64
  ].

Definition p_3_8_v : arr_ed25519_field_element_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1152921504606846975)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551614)) : uint64
  ].

Definition p_5_8_v : arr_ed25519_field_element_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1152921504606846975)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551613)) : uint64
  ].

Definition b_i_2842_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2844%nat).
Definition uniform_bytes_2843_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2845%nat).
Definition result_2840_loc : ChoiceEqualityLocation :=
  ((result (error_t) (byte_seq)) ; 2846%nat).
Definition l_i_b_str_2841_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2847%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq × byte_seq × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  2858.
Program Definition expand_message_xmd (msg_2853 : byte_seq) (
    dst_2850 : byte_seq) (len_in_bytes_2848 : uint_size)
  : both (CEfset (
      [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc])) [interface] (
    byte_seq_result_t) :=
  ((letb ell_2849 : uint_size :=
        (((lift_to_both0 len_in_bytes_2848) .+ (
              lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
          lift_to_both0 b_in_bytes_v) in
      letbm result_2840 : (result (error_t) (
            byte_seq)) loc( result_2840_loc ) :=
        @Err byte_seq error_t (ExpandMessageAbort) in
      letb '(result_2840) :=
        if negb ((((lift_to_both0 ell_2849) >.? (lift_to_both0 (
                  usize 255))) || ((lift_to_both0 len_in_bytes_2848) >.? (
                lift_to_both0 (usize 65535)))) || ((seq_len (
                lift_to_both0 dst_2850)) >.? (lift_to_both0 (
                usize 255)))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc])) (
          L2 := CEfset (
            [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb dst_prime_2851 : seq uint8 :=
            seq_push (lift_to_both0 dst_2850) (uint8_from_usize (seq_len (
                  lift_to_both0 dst_2850))) in
          letb z_pad_2852 : seq uint8 :=
            seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
          letbm l_i_b_str_2841 : seq uint8 loc( l_i_b_str_2841_loc ) :=
            seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
          letb l_i_b_str_2841 : seq uint8 :=
            seq_upd l_i_b_str_2841 (lift_to_both0 (usize 0)) (is_pure (
                uint8_from_usize ((lift_to_both0 len_in_bytes_2848) ./ (
                    lift_to_both0 (usize 256))))) in
          letb l_i_b_str_2841 : seq uint8 :=
            seq_upd l_i_b_str_2841 (lift_to_both0 (usize 1)) (is_pure (
                uint8_from_usize (lift_to_both0 len_in_bytes_2848))) in
          letb msg_prime_2854 : seq uint8 :=
            seq_concat (seq_concat (seq_concat (seq_concat (
                    lift_to_both0 z_pad_2852) (lift_to_both0 msg_2853)) (
                  lift_to_both0 l_i_b_str_2841)) (seq_new_ (default : uint8) (
                  lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_2851) in
          letb b_0_2855 : seq uint8 :=
            seq_from_seq (array_to_seq (hash (lift_to_both0 msg_prime_2854))) in
          letbm b_i_2842 : seq uint8 loc( b_i_2842_loc ) :=
            seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                    lift_to_both0 b_0_2855) (secret (lift_to_both0 (
                        @repr U8 1)))) (lift_to_both0 dst_prime_2851)))) in
          letbm uniform_bytes_2843 : seq uint8 loc( uniform_bytes_2843_loc ) :=
            seq_from_seq (lift_to_both0 b_i_2842) in
          letb '(b_i_2842, uniform_bytes_2843) :=
            foldi_both' (lift_to_both0 (usize 2)) ((lift_to_both0 ell_2849) .+ (
                  lift_to_both0 (usize 1))) prod_ce(b_i_2842, uniform_bytes_2843
              ) (L := (CEfset (
                    [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc]))) (
                I := [interface]) (fun i_2856 '(b_i_2842, uniform_bytes_2843) =>
                letb t_2857 : seq uint8 :=
                  seq_from_seq (lift_to_both0 b_0_2855) in
                letbm b_i_2842 loc( b_i_2842_loc ) :=
                  seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                            lift_to_both0 t_2857) seq_xor (
                            lift_to_both0 b_i_2842)) (uint8_from_usize (
                            lift_to_both0 i_2856))) (
                        lift_to_both0 dst_prime_2851)))) in
                letbm uniform_bytes_2843 loc( uniform_bytes_2843_loc ) :=
                  seq_concat (lift_to_both0 uniform_bytes_2843) (
                    lift_to_both0 b_i_2842) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 b_i_2842,
                    lift_to_both0 uniform_bytes_2843
                  ))
                ) in
          letbm result_2840 loc( result_2840_loc ) :=
            @Ok byte_seq error_t (seq_truncate (
                lift_to_both0 uniform_bytes_2843) (
                lift_to_both0 len_in_bytes_2848)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2840)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2840)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_2840)
      ) : both (CEfset (
        [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc])) [interface] (
      byte_seq_result_t)).
Fail Next Obligation.

Definition output_2859_loc : ChoiceEqualityLocation :=
  (seq ed25519_field_element_t ; 2860%nat).
Notation "'ed_hash_to_field_inp'" :=(
  byte_seq × byte_seq × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_out'" :=(
  seq_ed_result_t : choice_type) (in custom pack_type at level 2).
Definition ED_HASH_TO_FIELD : nat :=
  2870.
Program Definition ed_hash_to_field (msg_2863 : byte_seq) (
    dst_2864 : byte_seq) (count_2861 : uint_size)
  : both (CEfset (
      [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc ; output_2859_loc])) [interface] (
    seq_ed_result_t) :=
  ((letb len_in_bytes_2862 : uint_size :=
        (lift_to_both0 count_2861) .* (lift_to_both0 l_v) in
      letbnd(_) uniform_bytes_2865 : byte_seq :=
        expand_message_xmd (lift_to_both0 msg_2863) (lift_to_both0 dst_2864) (
          lift_to_both0 len_in_bytes_2862) in
      letbm output_2859 : seq ed25519_field_element_t loc( output_2859_loc ) :=
        seq_new_ (default : ed25519_field_element_t) (
          lift_to_both0 count_2861) in
      letb output_2859 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2861) output_2859 (L := (CEfset (
                [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc ; output_2859_loc]))) (
            I := [interface]) (fun i_2866 output_2859 =>
            letb elm_offset_2867 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_2866) in
            letb tv_2868 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2865) (
                lift_to_both0 elm_offset_2867) (lift_to_both0 l_v) in
            letb u_i_2869 : ed25519_field_element_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2868))) (
                  lift_to_both0 (usize 32)) (lift_to_both0 (usize 32))) in
            letb output_2859 : seq ed25519_field_element_t :=
              seq_upd output_2859 (lift_to_both0 i_2866) (is_pure (
                  lift_to_both0 u_i_2869)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2859)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok seq ed25519_field_element_t error_t (lift_to_both0 output_2859))
      ) : both (CEfset (
        [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc ; output_2859_loc])) [interface] (
      seq_ed_result_t)).
Fail Next Obligation.


Notation "'ed_is_square_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_is_square_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition ED_IS_SQUARE : nat :=
  2874.
Program Definition ed_is_square (x_2872 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2871 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb tv_2873 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 x_2872) (lift_to_both0 c1_2871) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 tv_2873) =.? (nat_mod_zero )) || ((
            lift_to_both0 tv_2873) =.? (nat_mod_one )))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'sgn0_m_eq_1_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sgn0_m_eq_1_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition SGN0_M_EQ_1 : nat :=
  2876.
Program Definition sgn0_m_eq_1 (x_2875 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_2875) rem (nat_mod_two )) =.? (nat_mod_one ))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'ed_clear_cofactor_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition ED_CLEAR_COFACTOR : nat :=
  2878.
Program Definition ed_clear_cofactor (x_2877 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_mul_by_cofactor (
          lift_to_both0 x_2877))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'cmov_inp'" :=(
  ed25519_field_element_t × ed25519_field_element_t × bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'cmov_out'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Definition CMOV : nat :=
  2882.
Program Definition cmov (a_2881 : ed25519_field_element_t) (
    b_2880 : ed25519_field_element_t) (c_2879 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (ed25519_field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 c_2879)
        then lift_to_both0 b_2880
        else lift_to_both0 a_2881)
      ) : both (fset.fset0) [interface] (ed25519_field_element_t)).
Fail Next Obligation.


Notation "'xor_inp'" :=(
  bool_ChoiceEquality × bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition XOR : nat :=
  2885.
Program Definition xor (a_2883 : bool_ChoiceEquality) (
    b_2884 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 a_2883)
        then if is_pure (I := [interface]) (lift_to_both0 b_2884)
        then lift_to_both0 ((false : bool_ChoiceEquality))
        else lift_to_both0 ((true : bool_ChoiceEquality))
        else if is_pure (I := [interface]) (lift_to_both0 b_2884)
        then lift_to_both0 ((true : bool_ChoiceEquality))
        else lift_to_both0 ((false : bool_ChoiceEquality)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'curve25519_to_edwards25519_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'curve25519_to_edwards25519_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition CURVE25519_TO_EDWARDS25519 : nat :=
  2904.
Program Definition curve25519_to_edwards25519 (p_2886 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(s_2887, t_2888, _, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_normalize (lift_to_both0 p_2886) in
      letb one_2889 : ed25519_field_element_t := nat_mod_one  in
      letb zero_2890 : ed25519_field_element_t := nat_mod_zero  in
      letb tv1_2891 : ed25519_field_element_t :=
        (lift_to_both0 s_2887) +% (lift_to_both0 one_2889) in
      letb tv2_2892 : ed25519_field_element_t :=
        (lift_to_both0 tv1_2891) *% (lift_to_both0 t_2888) in
      letb tv2_2893 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 tv2_2892) in
      letb v_2894 : ed25519_field_element_t :=
        (lift_to_both0 tv2_2893) *% (lift_to_both0 tv1_2891) in
      letb v_2895 : ed25519_field_element_t :=
        (lift_to_both0 v_2894) *% (lift_to_both0 s_2887) in
      letb w_2896 : ed25519_field_element_t :=
        (lift_to_both0 tv2_2893) *% (lift_to_both0 t_2888) in
      letb tv1_2897 : ed25519_field_element_t :=
        (lift_to_both0 s_2887) -% (lift_to_both0 one_2889) in
      letb w_2898 : ed25519_field_element_t :=
        (lift_to_both0 w_2896) *% (lift_to_both0 tv1_2897) in
      letb e_2899 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_2893) =.? (lift_to_both0 zero_2890) in
      letb w_2900 : ed25519_field_element_t :=
        cmov (lift_to_both0 w_2898) (lift_to_both0 one_2889) (
          lift_to_both0 e_2899) in
      letb c_2901 : ed25519_field_element_t :=
        (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 486664))) in
      letb sq_2902 : (option (ed25519_field_element_t)) :=
        sqrt (lift_to_both0 c_2901) in
      letb v_2903 : ed25519_field_element_t :=
        (lift_to_both0 v_2895) *% (option_unwrap (lift_to_both0 sq_2902)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 v_2903,
          lift_to_both0 w_2900,
          lift_to_both0 one_2889,
          (lift_to_both0 v_2903) *% (lift_to_both0 w_2900)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition x_2906_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2908%nat).
Definition x1_2905_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2909%nat).
Definition y_2907_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2910%nat).
Notation "'map_to_curve_elligator2_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2 : nat :=
  2921.
Program Definition map_to_curve_elligator2 (u_2915 : ed25519_field_element_t)
  : both (CEfset ([x1_2905_loc ; x_2906_loc ; y_2907_loc])) [interface] (
    ed_point_t) :=
  ((letb j_2911 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb z_2912 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 z_v) in
      letb one_2913 : ed25519_field_element_t := nat_mod_one  in
      letb zero_2914 : ed25519_field_element_t := nat_mod_zero  in
      letbm x1_2905 : ed25519_field_element_t loc( x1_2905_loc ) :=
        ((lift_to_both0 zero_2914) -% (lift_to_both0 j_2911)) *% (nat_mod_inv ((
              lift_to_both0 one_2913) +% (((lift_to_both0 z_2912) *% (
                  lift_to_both0 u_2915)) *% (lift_to_both0 u_2915)))) in
      letb '(x1_2905) :=
        if (lift_to_both0 x1_2905) =.? (
          lift_to_both0 zero_2914) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2905_loc])) (L2 := CEfset (
            [x1_2905_loc ; x_2906_loc ; y_2907_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2905 loc( x1_2905_loc ) :=
            (lift_to_both0 zero_2914) -% (lift_to_both0 j_2911) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2905)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2905)
         in
      letb gx1_2916 : ed25519_field_element_t :=
        ((((lift_to_both0 x1_2905) *% (lift_to_both0 x1_2905)) *% (
              lift_to_both0 x1_2905)) +% (((lift_to_both0 j_2911) *% (
                lift_to_both0 x1_2905)) *% (lift_to_both0 x1_2905))) +% (
          lift_to_both0 x1_2905) in
      letb x2_2917 : ed25519_field_element_t :=
        ((lift_to_both0 zero_2914) -% (lift_to_both0 x1_2905)) -% (
          lift_to_both0 j_2911) in
      letb gx2_2918 : ed25519_field_element_t :=
        ((((lift_to_both0 x2_2917) *% (lift_to_both0 x2_2917)) *% (
              lift_to_both0 x2_2917)) +% ((lift_to_both0 j_2911) *% ((
                lift_to_both0 x2_2917) *% (lift_to_both0 x2_2917)))) +% (
          lift_to_both0 x2_2917) in
      letbm x_2906 : ed25519_field_element_t loc( x_2906_loc ) :=
        lift_to_both0 zero_2914 in
      letbm y_2907 : ed25519_field_element_t loc( y_2907_loc ) :=
        lift_to_both0 zero_2914 in
      letb '(x_2906, y_2907) :=
        if ed_is_square (lift_to_both0 gx1_2916) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [x1_2905_loc ; x_2906_loc ; y_2907_loc])) (L2 := CEfset (
            [x1_2905_loc ; x_2906_loc ; y_2907_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2906 loc( x_2906_loc ) := lift_to_both0 x1_2905 in
          letbm y_2907 loc( y_2907_loc ) :=
            option_unwrap (sqrt (lift_to_both0 gx1_2916)) in
          letb '(y_2907) :=
            if negb (sgn0_m_eq_1 (lift_to_both0 y_2907)) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [x1_2905_loc ; x_2906_loc ; y_2907_loc])) (L2 := CEfset (
                [x1_2905_loc ; x_2906_loc ; y_2907_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm y_2907 loc( y_2907_loc ) :=
                (lift_to_both0 zero_2914) -% (lift_to_both0 y_2907) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_2907)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_2907)
             in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 x_2906,
              lift_to_both0 y_2907
            ))
          )
        else  lift_scope (L1 := CEfset (
            [x1_2905_loc ; x_2906_loc ; y_2907_loc])) (L2 := CEfset (
            [x1_2905_loc ; x_2906_loc ; y_2907_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2906 loc( x_2906_loc ) := lift_to_both0 x2_2917 in
          letbm y_2907 loc( y_2907_loc ) :=
            option_unwrap (sqrt (lift_to_both0 gx2_2918)) in
          letb '(y_2907) :=
            if sgn0_m_eq_1 (lift_to_both0 y_2907) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [x1_2905_loc ; x_2906_loc ; y_2907_loc])) (L2 := CEfset (
                [x1_2905_loc ; x_2906_loc ; y_2907_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm y_2907 loc( y_2907_loc ) :=
                (lift_to_both0 zero_2914) -% (lift_to_both0 y_2907) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_2907)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_2907)
             in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 x_2906,
              lift_to_both0 y_2907
            ))
          ) in
      letb s_2919 : ed25519_field_element_t := lift_to_both0 x_2906 in
      letb t_2920 : ed25519_field_element_t := lift_to_both0 y_2907 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_2919,
          lift_to_both0 t_2920,
          lift_to_both0 one_2913,
          (lift_to_both0 s_2919) *% (lift_to_both0 t_2920)
        ))
      ) : both (CEfset ([x1_2905_loc ; x_2906_loc ; y_2907_loc])) [interface] (
      ed_point_t)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_straight_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_straight_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_STRAIGHT : nat :=
  2948.
Program Definition map_to_curve_elligator2_straight (
    u_2926 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_2922 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb z_2923 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 z_v) in
      letb one_2924 : ed25519_field_element_t := nat_mod_one  in
      letb zero_2925 : ed25519_field_element_t := nat_mod_zero  in
      letb tv1_2927 : ed25519_field_element_t :=
        (lift_to_both0 u_2926) *% (lift_to_both0 u_2926) in
      letb tv1_2928 : ed25519_field_element_t :=
        (lift_to_both0 z_2923) *% (lift_to_both0 tv1_2927) in
      letb e1_2929 : bool_ChoiceEquality :=
        (lift_to_both0 tv1_2928) =.? ((lift_to_both0 zero_2925) -% (
            lift_to_both0 one_2924)) in
      letb tv1_2930 : ed25519_field_element_t :=
        cmov (lift_to_both0 tv1_2928) (lift_to_both0 zero_2925) (
          lift_to_both0 e1_2929) in
      letb x1_2931 : ed25519_field_element_t :=
        (lift_to_both0 tv1_2930) +% (lift_to_both0 one_2924) in
      letb x1_2932 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 x1_2931) in
      letb x1_2933 : ed25519_field_element_t :=
        ((lift_to_both0 zero_2925) -% (lift_to_both0 j_2922)) *% (
          lift_to_both0 x1_2932) in
      letb gx1_2934 : ed25519_field_element_t :=
        (lift_to_both0 x1_2933) +% (lift_to_both0 j_2922) in
      letb gx1_2935 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2934) *% (lift_to_both0 x1_2933) in
      letb gx1_2936 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2935) +% (lift_to_both0 one_2924) in
      letb gx1_2937 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2936) *% (lift_to_both0 x1_2933) in
      letb x2_2938 : ed25519_field_element_t :=
        ((lift_to_both0 zero_2925) -% (lift_to_both0 x1_2933)) -% (
          lift_to_both0 j_2922) in
      letb gx2_2939 : ed25519_field_element_t :=
        (lift_to_both0 tv1_2930) *% (lift_to_both0 gx1_2937) in
      letb e2_2940 : bool_ChoiceEquality :=
        ed_is_square (lift_to_both0 gx1_2937) in
      letb x_2941 : ed25519_field_element_t :=
        cmov (lift_to_both0 x2_2938) (lift_to_both0 x1_2933) (
          lift_to_both0 e2_2940) in
      letb y2_2942 : ed25519_field_element_t :=
        cmov (lift_to_both0 gx2_2939) (lift_to_both0 gx1_2937) (
          lift_to_both0 e2_2940) in
      letb y_2943 : ed25519_field_element_t :=
        option_unwrap (sqrt (lift_to_both0 y2_2942)) in
      letb e3_2944 : bool_ChoiceEquality :=
        sgn0_m_eq_1 (lift_to_both0 y_2943) in
      letb y_2945 : ed25519_field_element_t :=
        cmov (lift_to_both0 y_2943) ((lift_to_both0 zero_2925) -% (
            lift_to_both0 y_2943)) (xor (lift_to_both0 e2_2940) (
            lift_to_both0 e3_2944)) in
      letb s_2946 : ed25519_field_element_t := lift_to_both0 x_2941 in
      letb t_2947 : ed25519_field_element_t := lift_to_both0 y_2945 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_2946,
          lift_to_both0 t_2947,
          lift_to_both0 one_2924,
          (lift_to_both0 s_2946) *% (lift_to_both0 t_2947)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_curve25519_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_curve25519_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_CURVE25519 : nat :=
  2996.
Program Definition map_to_curve_elligator2_curve25519 (
    u_2957 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_2949 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb zero_2950 : ed25519_field_element_t := nat_mod_zero  in
      letb one_2951 : ed25519_field_element_t := nat_mod_one  in
      letb two_2952 : ed25519_field_element_t := nat_mod_two  in
      letb c1_2953 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_3_8_v)) in
      letb c2_2954 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 two_2952) (lift_to_both0 c1_2953) in
      letb c3_2955 : ed25519_field_element_t :=
        option_unwrap (sqrt ((lift_to_both0 zero_2950) -% (
              lift_to_both0 one_2951))) in
      letb c4_2956 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_5_8_v)) in
      letb tv1_2958 : ed25519_field_element_t :=
        (lift_to_both0 u_2957) *% (lift_to_both0 u_2957) in
      letb tv1_2959 : ed25519_field_element_t :=
        (lift_to_both0 two_2952) *% (lift_to_both0 tv1_2958) in
      letb xd_2960 : ed25519_field_element_t :=
        (lift_to_both0 tv1_2959) +% (lift_to_both0 one_2951) in
      letb x1n_2961 : ed25519_field_element_t :=
        (lift_to_both0 zero_2950) -% (lift_to_both0 j_2949) in
      letb tv2_2962 : ed25519_field_element_t :=
        (lift_to_both0 xd_2960) *% (lift_to_both0 xd_2960) in
      letb gxd_2963 : ed25519_field_element_t :=
        (lift_to_both0 tv2_2962) *% (lift_to_both0 xd_2960) in
      letb gx1_2964 : ed25519_field_element_t :=
        (lift_to_both0 j_2949) *% (lift_to_both0 tv1_2959) in
      letb gx1_2965 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2964) *% (lift_to_both0 x1n_2961) in
      letb gx1_2966 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2965) +% (lift_to_both0 tv2_2962) in
      letb gx1_2967 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2966) *% (lift_to_both0 x1n_2961) in
      letb tv3_2968 : ed25519_field_element_t :=
        (lift_to_both0 gxd_2963) *% (lift_to_both0 gxd_2963) in
      letb tv2_2969 : ed25519_field_element_t :=
        (lift_to_both0 tv3_2968) *% (lift_to_both0 tv3_2968) in
      letb tv3_2970 : ed25519_field_element_t :=
        (lift_to_both0 tv3_2968) *% (lift_to_both0 gxd_2963) in
      letb tv3_2971 : ed25519_field_element_t :=
        (lift_to_both0 tv3_2970) *% (lift_to_both0 gx1_2967) in
      letb tv2_2972 : ed25519_field_element_t :=
        (lift_to_both0 tv2_2969) *% (lift_to_both0 tv3_2971) in
      letb y11_2973 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 tv2_2972) (lift_to_both0 c4_2956) in
      letb y11_2974 : ed25519_field_element_t :=
        (lift_to_both0 y11_2973) *% (lift_to_both0 tv3_2971) in
      letb y12_2975 : ed25519_field_element_t :=
        (lift_to_both0 y11_2974) *% (lift_to_both0 c3_2955) in
      letb tv2_2976 : ed25519_field_element_t :=
        (lift_to_both0 y11_2974) *% (lift_to_both0 y11_2974) in
      letb tv2_2977 : ed25519_field_element_t :=
        (lift_to_both0 tv2_2976) *% (lift_to_both0 gxd_2963) in
      letb e1_2978 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_2977) =.? (lift_to_both0 gx1_2967) in
      letb y1_2979 : ed25519_field_element_t :=
        cmov (lift_to_both0 y12_2975) (lift_to_both0 y11_2974) (
          lift_to_both0 e1_2978) in
      letb x2n_2980 : ed25519_field_element_t :=
        (lift_to_both0 x1n_2961) *% (lift_to_both0 tv1_2959) in
      letb y21_2981 : ed25519_field_element_t :=
        (lift_to_both0 y11_2974) *% (lift_to_both0 u_2957) in
      letb y21_2982 : ed25519_field_element_t :=
        (lift_to_both0 y21_2981) *% (lift_to_both0 c2_2954) in
      letb y22_2983 : ed25519_field_element_t :=
        (lift_to_both0 y21_2982) *% (lift_to_both0 c3_2955) in
      letb gx2_2984 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2967) *% (lift_to_both0 tv1_2959) in
      letb tv2_2985 : ed25519_field_element_t :=
        (lift_to_both0 y21_2982) *% (lift_to_both0 y21_2982) in
      letb tv2_2986 : ed25519_field_element_t :=
        (lift_to_both0 tv2_2985) *% (lift_to_both0 gxd_2963) in
      letb e2_2987 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_2986) =.? (lift_to_both0 gx2_2984) in
      letb y2_2988 : ed25519_field_element_t :=
        cmov (lift_to_both0 y22_2983) (lift_to_both0 y21_2982) (
          lift_to_both0 e2_2987) in
      letb tv2_2989 : ed25519_field_element_t :=
        (lift_to_both0 y1_2979) *% (lift_to_both0 y1_2979) in
      letb tv2_2990 : ed25519_field_element_t :=
        (lift_to_both0 tv2_2989) *% (lift_to_both0 gxd_2963) in
      letb e3_2991 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_2990) =.? (lift_to_both0 gx1_2967) in
      letb xn_2992 : ed25519_field_element_t :=
        cmov (lift_to_both0 x2n_2980) (lift_to_both0 x1n_2961) (
          lift_to_both0 e3_2991) in
      letb y_2993 : ed25519_field_element_t :=
        cmov (lift_to_both0 y2_2988) (lift_to_both0 y1_2979) (
          lift_to_both0 e3_2991) in
      letb e4_2994 : bool_ChoiceEquality :=
        sgn0_m_eq_1 (lift_to_both0 y_2993) in
      letb y_2995 : ed25519_field_element_t :=
        cmov (lift_to_both0 y_2993) ((lift_to_both0 zero_2950) -% (
            lift_to_both0 y_2993)) (xor (lift_to_both0 e3_2991) (
            lift_to_both0 e4_2994)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xn_2992,
          lift_to_both0 xd_2960,
          lift_to_both0 y_2995,
          lift_to_both0 one_2951
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_edwards25519_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards25519_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_EDWARDS25519 : nat :=
  3020.
Program Definition map_to_curve_elligator2_edwards25519 (
    u_3002 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_2997 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb zero_2998 : ed25519_field_element_t := nat_mod_zero  in
      letb one_2999 : ed25519_field_element_t := nat_mod_one  in
      letb two_3000 : ed25519_field_element_t := nat_mod_two  in
      letb c1_3001 : ed25519_field_element_t :=
        option_unwrap (sqrt ((lift_to_both0 zero_2998) -% ((
                lift_to_both0 j_2997) +% (lift_to_both0 two_3000)))) in
      letb '(xmn_3003, xmd_3004, ymn_3005, ymd_3006) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2_curve25519 (lift_to_both0 u_3002) in
      letb xn_3007 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3003) *% (lift_to_both0 ymd_3006) in
      letb xn_3008 : ed25519_field_element_t :=
        (lift_to_both0 xn_3007) *% (lift_to_both0 c1_3001) in
      letb xd_3009 : ed25519_field_element_t :=
        (lift_to_both0 xmd_3004) *% (lift_to_both0 ymn_3005) in
      letb yn_3010 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3003) -% (lift_to_both0 xmd_3004) in
      letb yd_3011 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3003) +% (lift_to_both0 xmd_3004) in
      letb tv1_3012 : ed25519_field_element_t :=
        (lift_to_both0 xd_3009) *% (lift_to_both0 yd_3011) in
      letb e_3013 : bool_ChoiceEquality :=
        (lift_to_both0 tv1_3012) =.? (lift_to_both0 zero_2998) in
      letb xn_3014 : ed25519_field_element_t :=
        cmov (lift_to_both0 xn_3008) (lift_to_both0 zero_2998) (
          lift_to_both0 e_3013) in
      letb xd_3015 : ed25519_field_element_t :=
        cmov (lift_to_both0 xd_3009) (lift_to_both0 one_2999) (
          lift_to_both0 e_3013) in
      letb yn_3016 : ed25519_field_element_t :=
        cmov (lift_to_both0 yn_3010) (lift_to_both0 one_2999) (
          lift_to_both0 e_3013) in
      letb yd_3017 : ed25519_field_element_t :=
        cmov (lift_to_both0 yd_3011) (lift_to_both0 one_2999) (
          lift_to_both0 e_3013) in
      letb x_3018 : ed25519_field_element_t :=
        (lift_to_both0 xn_3014) *% (nat_mod_inv (lift_to_both0 xd_3015)) in
      letb y_3019 : ed25519_field_element_t :=
        (lift_to_both0 yn_3016) *% (nat_mod_inv (lift_to_both0 yd_3017)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_3018,
          lift_to_both0 y_3019,
          lift_to_both0 one_2999,
          (lift_to_both0 x_3018) *% (lift_to_both0 y_3019)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_edwards_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_EDWARDS : nat :=
  3023.
Program Definition map_to_curve_elligator2_edwards (
    u_3021 : ed25519_field_element_t)
  : both (CEfset ([x1_2905_loc ; x_2906_loc ; y_2907_loc])) [interface] (
    ed_point_t) :=
  ((letb st_3022 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2 (lift_to_both0 u_3021) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        curve25519_to_edwards25519 (lift_to_both0 st_3022))
      ) : both (CEfset ([x1_2905_loc ; x_2906_loc ; y_2907_loc])) [interface] (
      ed_point_t)).
Fail Next Obligation.


Notation "'ed_encode_to_curve_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ed_encode_to_curve_out'" :=(
  ed_point_result_t : choice_type) (in custom pack_type at level 2).
Definition ED_ENCODE_TO_CURVE : nat :=
  3028.
Program Definition ed_encode_to_curve (msg_3024 : byte_seq) (
    dst_3025 : byte_seq)
  : both (CEfset (
      [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc ; output_2859_loc ; x1_2905_loc ; x_2906_loc ; y_2907_loc])) [interface] (
    ed_point_result_t) :=
  ((letbnd(_) u_3026 : seq ed25519_field_element_t :=
        ed_hash_to_field (lift_to_both0 msg_3024) (lift_to_both0 dst_3025) (
          lift_to_both0 (usize 1)) in
      letb q_3027 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2_edwards (seq_index (u_3026) (lift_to_both0 (
              usize 0))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok ed_point_t error_t (
          ed_clear_cofactor (lift_to_both0 q_3027)))
      ) : both (CEfset (
        [result_2840_loc ; l_i_b_str_2841_loc ; b_i_2842_loc ; uniform_bytes_2843_loc ; output_2859_loc ; x1_2905_loc ; x_2906_loc ; y_2907_loc])) [interface] (
      ed_point_result_t)).
Fail Next Obligation.

