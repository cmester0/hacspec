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
Require Import Hacspec_Bls12_381.



Require Import Hacspec_Sha256.

Definition fp_hash_canvas_t := nseq (int8) (usize 64).
Definition fp_hash_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition arr_fp_t := nseq (uint64) (usize 6).

Definition b_in_bytes_v : uint_size :=
  usize 32.

Definition s_in_bytes_v : uint_size :=
  usize 64.

Definition l_v : uint_size :=
  usize 64.

Definition p_1_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 936899308823769933)) : uint64;
    (secret (@repr U64 2706051889235351147)) : uint64;
    (secret (@repr U64 12843041017062132063)) : uint64;
    (secret (@repr U64 12941209323636816658)) : uint64;
    (secret (@repr U64 1105070755758604287)) : uint64;
    (secret (@repr U64 15924587544893707605)) : uint64
  ].

Definition p_1_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 468449654411884966)) : uint64;
    (secret (@repr U64 10576397981472451381)) : uint64;
    (secret (@repr U64 15644892545385841839)) : uint64;
    (secret (@repr U64 15693976698673184137)) : uint64;
    (secret (@repr U64 552535377879302143)) : uint64;
    (secret (@repr U64 17185665809301629611)) : uint64
  ].

Definition p_3_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 468449654411884966)) : uint64;
    (secret (@repr U64 10576397981472451381)) : uint64;
    (secret (@repr U64 15644892545385841839)) : uint64;
    (secret (@repr U64 15693976698673184137)) : uint64;
    (secret (@repr U64 552535377879302143)) : uint64;
    (secret (@repr U64 17185665809301629610)) : uint64
  ].

Definition uniform_bytes_2146_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2147%nat).
Definition l_i_b_str_2144_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2148%nat).
Definition b_i_2145_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2149%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq × byte_seq × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  2160.
Program Definition expand_message_xmd (msg_2155 : byte_seq) (
    dst_2152 : byte_seq) (len_in_bytes_2150 : uint_size)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc])) [interface] (
    byte_seq) :=
  ((letb ell_2151 : uint_size :=
        (((lift_to_both0 len_in_bytes_2150) .+ (
              lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
          lift_to_both0 b_in_bytes_v) in
      letb dst_prime_2153 : seq uint8 :=
        seq_push (lift_to_both0 dst_2152) (uint8_from_usize (seq_len (
              lift_to_both0 dst_2152))) in
      letb z_pad_2154 : seq uint8 :=
        seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
      letbm l_i_b_str_2144 : seq uint8 loc( l_i_b_str_2144_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
      letb l_i_b_str_2144 : seq uint8 :=
        seq_upd l_i_b_str_2144 (lift_to_both0 (usize 0)) (is_pure (
            uint8_from_usize ((lift_to_both0 len_in_bytes_2150) ./ (
                lift_to_both0 (usize 256))))) in
      letb l_i_b_str_2144 : seq uint8 :=
        seq_upd l_i_b_str_2144 (lift_to_both0 (usize 1)) (is_pure (
            uint8_from_usize (lift_to_both0 len_in_bytes_2150))) in
      letb msg_prime_2156 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (
                lift_to_both0 z_pad_2154) (lift_to_both0 msg_2155)) (
              lift_to_both0 l_i_b_str_2144)) (seq_new_ (default : uint8) (
              lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_2153) in
      letb b_0_2157 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (lift_to_both0 msg_prime_2156))) in
      letbm b_i_2145 : seq uint8 loc( b_i_2145_loc ) :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                lift_to_both0 b_0_2157) (secret (lift_to_both0 (@repr U8 1)))) (
              lift_to_both0 dst_prime_2153)))) in
      letbm uniform_bytes_2146 : seq uint8 loc( uniform_bytes_2146_loc ) :=
        seq_from_seq (lift_to_both0 b_i_2145) in
      letb '(b_i_2145, uniform_bytes_2146) :=
        foldi_both' (lift_to_both0 (usize 2)) ((lift_to_both0 ell_2151) .+ (
              lift_to_both0 (usize 1))) prod_ce(b_i_2145, uniform_bytes_2146) (
            L := (CEfset (
                [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc]))) (
            I := [interface]) (fun i_2158 '(b_i_2145, uniform_bytes_2146) =>
            letb t_2159 : seq uint8 := seq_from_seq (lift_to_both0 b_0_2157) in
            letbm b_i_2145 loc( b_i_2145_loc ) :=
              seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                        lift_to_both0 t_2159) seq_xor (
                        lift_to_both0 b_i_2145)) (uint8_from_usize (
                        lift_to_both0 i_2158))) (
                    lift_to_both0 dst_prime_2153)))) in
            letbm uniform_bytes_2146 loc( uniform_bytes_2146_loc ) :=
              seq_concat (lift_to_both0 uniform_bytes_2146) (
                lift_to_both0 b_i_2145) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 b_i_2145,
                lift_to_both0 uniform_bytes_2146
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_truncate (
          lift_to_both0 uniform_bytes_2146) (lift_to_both0 len_in_bytes_2150))
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

Definition output_2161_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2162%nat).
Notation "'fp_hash_to_field_inp'" :=(
  byte_seq × byte_seq × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_out'" :=(
  seq fp_t : choice_type) (in custom pack_type at level 2).
Definition FP_HASH_TO_FIELD : nat :=
  2172.
Program Definition fp_hash_to_field (msg_2165 : byte_seq) (
    dst_2166 : byte_seq) (count_2163 : uint_size)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc])) [interface] (
    seq fp_t) :=
  ((letb len_in_bytes_2164 : uint_size :=
        (lift_to_both0 count_2163) .* (lift_to_both0 l_v) in
      letb uniform_bytes_2167 : seq uint8 :=
        expand_message_xmd (lift_to_both0 msg_2165) (lift_to_both0 dst_2166) (
          lift_to_both0 len_in_bytes_2164) in
      letbm output_2161 : seq fp_t loc( output_2161_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 count_2163) in
      letb output_2161 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2163) output_2161 (L := (CEfset (
                [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc]))) (
            I := [interface]) (fun i_2168 output_2161 =>
            letb elm_offset_2169 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_2168) in
            letb tv_2170 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2167) (
                lift_to_both0 elm_offset_2169) (lift_to_both0 l_v) in
            letb u_i_2171 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2170))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2161 : seq fp_t :=
              seq_upd output_2161 (lift_to_both0 i_2168) (is_pure (
                  lift_to_both0 u_i_2171)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2161)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 output_2161)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc])) [interface] (
      seq fp_t)).
Fail Next Obligation.


Notation "'fp_sgn0_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP_SGN0 : nat :=
  2174.
Program Definition fp_sgn0 (x_2173 : fp_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_2173) rem (nat_mod_two )) =.? (nat_mod_one ))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'fp_is_square_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_is_square_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP_IS_SQUARE : nat :=
  2178.
Program Definition fp_is_square (x_2176 : fp_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2175 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb tv_2177 : fp_t :=
        nat_mod_pow_self (lift_to_both0 x_2176) (lift_to_both0 c1_2175) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 tv_2177) =.? (nat_mod_zero )) || ((
            lift_to_both0 tv_2177) =.? (nat_mod_one )))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'fp_sqrt_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Definition FP_SQRT : nat :=
  2181.
Program Definition fp_sqrt (x_2180 : fp_t)
  : both (fset.fset0) [interface] (fp_t) :=
  ((letb c1_2179 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_4_v)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_pow_self (
          lift_to_both0 x_2180) (lift_to_both0 c1_2179))
      ) : both (fset.fset0) [interface] (fp_t)).
Fail Next Obligation.


Notation "'g1_curve_func_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Definition G1_CURVE_FUNC : nat :=
  2183.
Program Definition g1_curve_func (x_2182 : fp_t)
  : both (fset.fset0) [interface] (fp_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x_2182) *% (lift_to_both0 x_2182)) *% (
            lift_to_both0 x_2182)) +% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 4))))
      ) : both (fset.fset0) [interface] (fp_t)).
Fail Next Obligation.

Definition tv4_2184_loc : ChoiceEqualityLocation :=
  (fp_t ; 2186%nat).
Definition y_2185_loc : ChoiceEqualityLocation :=
  (fp_t ; 2187%nat).
Notation "'g1_map_to_curve_svdw_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_MAP_TO_CURVE_SVDW : nat :=
  2201.
Program Definition g1_map_to_curve_svdw (u_2190 : fp_t)
  : both (CEfset ([tv4_2184_loc ; y_2185_loc])) [interface] (g1_t) :=
  ((letb z_2188 : fp_t :=
        (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 3))) in
      letb gz_2189 : fp_t := g1_curve_func (lift_to_both0 z_2188) in
      letb tv1_2191 : fp_t :=
        ((lift_to_both0 u_2190) *% (lift_to_both0 u_2190)) *% (
          lift_to_both0 gz_2189) in
      letb tv2_2192 : fp_t := (nat_mod_one ) +% (lift_to_both0 tv1_2191) in
      letb tv1_2193 : fp_t := (nat_mod_one ) -% (lift_to_both0 tv1_2191) in
      letb tv3_2194 : fp_t :=
        nat_mod_inv ((lift_to_both0 tv1_2193) *% (lift_to_both0 tv2_2192)) in
      letbm tv4_2184 : fp_t loc( tv4_2184_loc ) :=
        fp_sqrt (((nat_mod_zero ) -% (lift_to_both0 gz_2189)) *% (((
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3))) *% (
                lift_to_both0 z_2188)) *% (lift_to_both0 z_2188))) in
      letb '(tv4_2184) :=
        if fp_sgn0 (lift_to_both0 tv4_2184) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tv4_2184_loc])) (L2 := CEfset (
            [tv4_2184_loc ; y_2185_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tv4_2184 loc( tv4_2184_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 tv4_2184) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2184)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tv4_2184)
         in
      letb tv5_2195 : fp_t :=
        (((lift_to_both0 u_2190) *% (lift_to_both0 tv1_2193)) *% (
            lift_to_both0 tv3_2194)) *% (lift_to_both0 tv4_2184) in
      letb tv6_2196 : fp_t :=
        (((nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
                  @repr U128 4)))) *% (lift_to_both0 gz_2189)) *% (nat_mod_inv (
            ((nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3))) *% (
                lift_to_both0 z_2188)) *% (lift_to_both0 z_2188))) in
      letb x1_2197 : fp_t :=
        (((nat_mod_zero ) -% (lift_to_both0 z_2188)) *% (nat_mod_inv (
              nat_mod_two ))) -% (lift_to_both0 tv5_2195) in
      letb x2_2198 : fp_t :=
        (((nat_mod_zero ) -% (lift_to_both0 z_2188)) *% (nat_mod_inv (
              nat_mod_two ))) +% (lift_to_both0 tv5_2195) in
      letb x3_2199 : fp_t :=
        (lift_to_both0 z_2188) +% (((lift_to_both0 tv6_2196) *% (((
                  lift_to_both0 tv2_2192) *% (lift_to_both0 tv2_2192)) *% (
                lift_to_both0 tv3_2194))) *% (((lift_to_both0 tv2_2192) *% (
                lift_to_both0 tv2_2192)) *% (lift_to_both0 tv3_2194))) in
      letb x_2200 : fp_t :=
        if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
              lift_to_both0 x1_2197)))
        then lift_to_both0 x1_2197
        else if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
              lift_to_both0 x2_2198)))
        then lift_to_both0 x2_2198
        else lift_to_both0 x3_2199 in
      letbm y_2185 : fp_t loc( y_2185_loc ) :=
        fp_sqrt (g1_curve_func (lift_to_both0 x_2200)) in
      letb '(y_2185) :=
        if (fp_sgn0 (lift_to_both0 u_2190)) !=.? (fp_sgn0 (
            lift_to_both0 y_2185)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tv4_2184_loc ; y_2185_loc])) (
          L2 := CEfset ([tv4_2184_loc ; y_2185_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2185 loc( y_2185_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_2185) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2185)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2185)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2200,
          lift_to_both0 y_2185,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (CEfset ([tv4_2184_loc ; y_2185_loc])) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1_clear_cofactor_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_CLEAR_COFACTOR : nat :=
  2204.
Program Definition g1_clear_cofactor (x_2203 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb h_eff_2202 : scalar_t :=
        nat_mod_from_literal (_) (lift_to_both0 (
            @repr U128 15132376222941642753)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (g1mul (
          lift_to_both0 h_eff_2202) (lift_to_both0 x_2203))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1_hash_to_curve_svdw_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_HASH_TO_CURVE_SVDW : nat :=
  2212.
Program Definition g1_hash_to_curve_svdw (msg_2205 : byte_seq) (
    dst_2206 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc ; tv4_2184_loc ; y_2185_loc])) [interface] (
    g1_t) :=
  ((letb u_2207 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2205) (lift_to_both0 dst_2206) (
          lift_to_both0 (usize 2)) in
      letb q0_2208 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2207) (lift_to_both0 (usize 0))) in
      letb q1_2209 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2207) (lift_to_both0 (usize 1))) in
      letb r_2210 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1add (lift_to_both0 q0_2208) (lift_to_both0 q1_2209) in
      letb p_2211 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 r_2210) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2211)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc ; tv4_2184_loc ; y_2185_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_encode_to_curve_svdw_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_ENCODE_TO_CURVE_SVDW : nat :=
  2218.
Program Definition g1_encode_to_curve_svdw (msg_2213 : byte_seq) (
    dst_2214 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc ; tv4_2184_loc ; y_2185_loc])) [interface] (
    g1_t) :=
  ((letb u_2215 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2213) (lift_to_both0 dst_2214) (
          lift_to_both0 (usize 1)) in
      letb q_2216 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2215) (lift_to_both0 (usize 0))) in
      letb p_2217 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 q_2216) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2217)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc ; tv4_2184_loc ; y_2185_loc])) [interface] (
      g1_t)).
Fail Next Obligation.

Definition output_2219_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2220%nat).
Notation "'fp2_hash_to_field_inp'" :=(
  byte_seq × byte_seq × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_out'" :=(
  seq fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2_HASH_TO_FIELD : nat :=
  2233.
Program Definition fp2_hash_to_field (msg_2223 : byte_seq) (
    dst_2224 : byte_seq) (count_2221 : uint_size)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc])) [interface] (
    seq fp2_t) :=
  ((letb len_in_bytes_2222 : uint_size :=
        ((lift_to_both0 count_2221) .* (lift_to_both0 (usize 2))) .* (
          lift_to_both0 l_v) in
      letb uniform_bytes_2225 : seq uint8 :=
        expand_message_xmd (lift_to_both0 msg_2223) (lift_to_both0 dst_2224) (
          lift_to_both0 len_in_bytes_2222) in
      letbm output_2219 : seq (fp_t '× fp_t) loc( output_2219_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 count_2221) in
      letb output_2219 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2221) output_2219 (L := (CEfset (
                [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc]))) (
            I := [interface]) (fun i_2226 output_2219 =>
            letb elm_offset_2227 : uint_size :=
              ((lift_to_both0 l_v) .* (lift_to_both0 i_2226)) .* (
                lift_to_both0 (usize 2)) in
            letb tv_2228 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2225) (
                lift_to_both0 elm_offset_2227) (lift_to_both0 l_v) in
            letb e_1_2229 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2228))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb elm_offset_2230 : uint_size :=
              (lift_to_both0 l_v) .* ((lift_to_both0 (usize 1)) .+ ((
                    lift_to_both0 i_2226) .* (lift_to_both0 (usize 2)))) in
            letb tv_2231 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2225) (
                lift_to_both0 elm_offset_2230) (lift_to_both0 l_v) in
            letb e_2_2232 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2231))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2219 : seq (fp_t '× fp_t) :=
              seq_upd output_2219 (lift_to_both0 i_2226) (is_pure (prod_b(
                    lift_to_both0 e_1_2229,
                    lift_to_both0 e_2_2232
                  ))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2219)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 output_2219)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc])) [interface] (
      seq fp2_t)).
Fail Next Obligation.


Notation "'fp2_sgn0_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP2_SGN0 : nat :=
  2240.
Program Definition fp2_sgn0 (x_2234 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x0_2235, x1_2236) : (fp_t '× fp_t) := lift_to_both0 x_2234 in
      letb sign_0_2237 : bool_ChoiceEquality :=
        fp_sgn0 (lift_to_both0 x0_2235) in
      letb zero_0_2238 : bool_ChoiceEquality :=
        (lift_to_both0 x0_2235) =.? (nat_mod_zero ) in
      letb sign_1_2239 : bool_ChoiceEquality :=
        fp_sgn0 (lift_to_both0 x1_2236) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 sign_0_2237) || ((lift_to_both0 zero_0_2238) && (
            lift_to_both0 sign_1_2239)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'fp2_is_square_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_is_square_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP2_IS_SQUARE : nat :=
  2250.
Program Definition fp2_is_square (x_2242 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2241 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb '(x1_2243, x2_2244) : (fp_t '× fp_t) := lift_to_both0 x_2242 in
      letb tv1_2245 : fp_t :=
        (lift_to_both0 x1_2243) *% (lift_to_both0 x1_2243) in
      letb tv2_2246 : fp_t :=
        (lift_to_both0 x2_2244) *% (lift_to_both0 x2_2244) in
      letb tv1_2247 : fp_t :=
        (lift_to_both0 tv1_2245) +% (lift_to_both0 tv2_2246) in
      letb tv1_2248 : fp_t :=
        nat_mod_pow_self (lift_to_both0 tv1_2247) (lift_to_both0 c1_2241) in
      letb neg1_2249 : fp_t := (nat_mod_zero ) -% (nat_mod_one ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 tv1_2248) !=.? (lift_to_both0 neg1_2249))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition c_2251_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2252%nat).
Notation "'fp2exp_inp'" :=(
  fp2_t × fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2EXP : nat :=
  2256.
Program Definition fp2exp (n_2255 : fp2_t) (k_2254 : fp_t)
  : both (CEfset ([c_2251_loc])) [interface] (fp2_t) :=
  ((letbm c_2251 : (fp_t '× fp_t) loc( c_2251_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb c_2251 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 381)) c_2251 (L := (CEfset ([c_2251_loc]))) (
            I := [interface]) (fun i_2253 c_2251 =>
            letbm c_2251 loc( c_2251_loc ) :=
              fp2mul (lift_to_both0 c_2251) (lift_to_both0 c_2251) in
            letb '(c_2251) :=
              if nat_mod_bit (lift_to_both0 k_2254) ((lift_to_both0 (
                    usize 380)) .- (lift_to_both0 i_2253)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([c_2251_loc])) (L2 := CEfset (
                  [c_2251_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm c_2251 loc( c_2251_loc ) :=
                  fp2mul (lift_to_both0 c_2251) (lift_to_both0 n_2255) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 c_2251)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 c_2251)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 c_2251)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 c_2251)
      ) : both (CEfset ([c_2251_loc])) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2_sqrt_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2_SQRT : nat :=
  2265.
Program Definition fp2_sqrt (a_2259 : fp2_t)
  : both (CEfset ([c_2251_loc])) [interface] (fp2_t) :=
  ((letb c1_2257 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_3_4_v)) in
      letb c2_2258 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb a1_2260 : (fp_t '× fp_t) :=
        fp2exp (lift_to_both0 a_2259) (lift_to_both0 c1_2257) in
      letb alpha_2261 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a1_2260) (fp2mul (lift_to_both0 a1_2260) (
            lift_to_both0 a_2259)) in
      letb x0_2262 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a1_2260) (lift_to_both0 a_2259) in
      letb neg1_2263 : (fp_t '× fp_t) :=
        prod_b((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in
      letb b_2264 : (fp_t '× fp_t) :=
        fp2exp (fp2add (fp2fromfp (nat_mod_one )) (lift_to_both0 alpha_2261)) (
          lift_to_both0 c2_2258) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 alpha_2261) =.? (
            lift_to_both0 neg1_2263))
        then fp2mul (prod_b(nat_mod_zero , nat_mod_one )) (
          lift_to_both0 x0_2262)
        else fp2mul (lift_to_both0 b_2264) (lift_to_both0 x0_2262))
      ) : both (CEfset ([c_2251_loc])) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'g2_curve_func_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition G2_CURVE_FUNC : nat :=
  2267.
Program Definition g2_curve_func (x_2266 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2add (fp2mul (
            lift_to_both0 x_2266) (fp2mul (lift_to_both0 x_2266) (
              lift_to_both0 x_2266))) (prod_b(
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4)),
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4))
          )))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.

Definition y_2269_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2270%nat).
Definition tv4_2268_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2271%nat).
Notation "'g2_map_to_curve_svdw_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_MAP_TO_CURVE_SVDW : nat :=
  2286.
Program Definition g2_map_to_curve_svdw (u_2274 : fp2_t)
  : both (CEfset ([c_2251_loc ; tv4_2268_loc ; y_2269_loc])) [interface] (
    g2_t) :=
  ((letb z_2272 : (fp_t '× fp_t) := fp2neg (fp2fromfp (nat_mod_one )) in
      letb gz_2273 : (fp_t '× fp_t) := g2_curve_func (lift_to_both0 z_2272) in
      letb tv1_2275 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 u_2274) (lift_to_both0 u_2274)) (
          lift_to_both0 gz_2273) in
      letb tv2_2276 : (fp_t '× fp_t) :=
        fp2add (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2275) in
      letb tv1_2277 : (fp_t '× fp_t) :=
        fp2sub (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2275) in
      letb tv3_2278 : (fp_t '× fp_t) :=
        fp2inv (fp2mul (lift_to_both0 tv1_2277) (lift_to_both0 tv2_2276)) in
      letbm tv4_2268 : (fp_t '× fp_t) loc( tv4_2268_loc ) :=
        fp2_sqrt (fp2mul (fp2neg (lift_to_both0 gz_2273)) (fp2mul (fp2fromfp (
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))) (
              fp2mul (lift_to_both0 z_2272) (lift_to_both0 z_2272)))) in
      letb '(tv4_2268) :=
        if fp2_sgn0 (lift_to_both0 tv4_2268) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([c_2251_loc ; tv4_2268_loc])) (
          L2 := CEfset ([c_2251_loc ; tv4_2268_loc ; y_2269_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tv4_2268 loc( tv4_2268_loc ) :=
            fp2neg (lift_to_both0 tv4_2268) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2268)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tv4_2268)
         in
      letb tv5_2279 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (fp2mul (lift_to_both0 u_2274) (
              lift_to_both0 tv1_2277)) (lift_to_both0 tv3_2278)) (
          lift_to_both0 tv4_2268) in
      letb tv6_2280 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
                  lift_to_both0 (@repr U128 4))))) (lift_to_both0 gz_2273)) (
          fp2inv (fp2mul (fp2fromfp (nat_mod_from_literal (_) (lift_to_both0 (
                    @repr U128 3)))) (fp2mul (lift_to_both0 z_2272) (
                lift_to_both0 z_2272)))) in
      letb x1_2281 : (fp_t '× fp_t) :=
        fp2sub (fp2mul (fp2neg (lift_to_both0 z_2272)) (fp2inv (fp2fromfp (
                nat_mod_two )))) (lift_to_both0 tv5_2279) in
      letb x2_2282 : (fp_t '× fp_t) :=
        fp2add (fp2mul (fp2neg (lift_to_both0 z_2272)) (fp2inv (fp2fromfp (
                nat_mod_two )))) (lift_to_both0 tv5_2279) in
      letb tv7_2283 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 tv2_2276) (lift_to_both0 tv2_2276)) (
          lift_to_both0 tv3_2278) in
      letb x3_2284 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 z_2272) (fp2mul (lift_to_both0 tv6_2280) (fp2mul (
              lift_to_both0 tv7_2283) (lift_to_both0 tv7_2283))) in
      letb x_2285 : (fp_t '× fp_t) :=
        if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
              lift_to_both0 x1_2281)))
        then lift_to_both0 x1_2281
        else if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
              lift_to_both0 x2_2282)))
        then lift_to_both0 x2_2282
        else lift_to_both0 x3_2284 in
      letbm y_2269 : (fp_t '× fp_t) loc( y_2269_loc ) :=
        fp2_sqrt (g2_curve_func (lift_to_both0 x_2285)) in
      letb '(y_2269) :=
        if (fp2_sgn0 (lift_to_both0 u_2274)) !=.? (fp2_sgn0 (
            lift_to_both0 y_2269)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [c_2251_loc ; tv4_2268_loc ; y_2269_loc])) (L2 := CEfset (
            [c_2251_loc ; tv4_2268_loc ; y_2269_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2269 loc( y_2269_loc ) := fp2neg (lift_to_both0 y_2269) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2269)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2269)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2285,
          lift_to_both0 y_2269,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (CEfset ([c_2251_loc ; tv4_2268_loc ; y_2269_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'psi_inp'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Definition PSI : nat :=
  2295.
Program Definition psi (p_2289 : g2_t)
  : both (CEfset ([c_2251_loc])) [interface] (g2_t) :=
  ((letb c1_2287 : (fp_t '× fp_t) :=
        fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))))) in
      letb c2_2288 : (fp_t '× fp_t) :=
        fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                nat_mod_two )))) in
      letb '(x_2290, y_2291, inf_2292) : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 p_2289 in
      letb qx_2293 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 c1_2287) (fp2conjugate (lift_to_both0 x_2290)) in
      letb qy_2294 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 c2_2288) (fp2conjugate (lift_to_both0 y_2291)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 qx_2293,
          lift_to_both0 qy_2294,
          lift_to_both0 inf_2292
        ))
      ) : both (CEfset ([c_2251_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2_clear_cofactor_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_CLEAR_COFACTOR : nat :=
  2310.
Program Definition g2_clear_cofactor (p_2297 : g2_t)
  : both (CEfset ([c_2251_loc])) [interface] (g2_t) :=
  ((letb c1_2296 : scalar_t :=
        nat_mod_from_literal (_) (lift_to_both0 (
            @repr U128 15132376222941642752)) in
      letb t1_2298 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2mul (lift_to_both0 c1_2296) (lift_to_both0 p_2297) in
      letb t1_2299 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2neg (lift_to_both0 t1_2298) in
      letb t2_2300 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        psi (lift_to_both0 p_2297) in
      letb t3_2301 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2double (lift_to_both0 p_2297) in
      letb t3_2302 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        psi (psi (lift_to_both0 t3_2301)) in
      letb t3_2303 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2302) (g2neg (lift_to_both0 t2_2300)) in
      letb t2_2304 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t1_2299) (lift_to_both0 t2_2300) in
      letb t2_2305 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2mul (lift_to_both0 c1_2296) (lift_to_both0 t2_2304) in
      letb t2_2306 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2neg (lift_to_both0 t2_2305) in
      letb t3_2307 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2303) (lift_to_both0 t2_2306) in
      letb t3_2308 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2307) (g2neg (lift_to_both0 t1_2299)) in
      letb q_2309 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2308) (g2neg (lift_to_both0 p_2297)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2309)
      ) : both (CEfset ([c_2251_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2_hash_to_curve_svdw_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_HASH_TO_CURVE_SVDW : nat :=
  2318.
Program Definition g2_hash_to_curve_svdw (msg_2311 : byte_seq) (
    dst_2312 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc ; c_2251_loc ; tv4_2268_loc ; y_2269_loc])) [interface] (
    g2_t) :=
  ((letb u_2313 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2311) (lift_to_both0 dst_2312) (
          lift_to_both0 (usize 2)) in
      letb q0_2314 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2313) (lift_to_both0 (usize 0))) in
      letb q1_2315 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2313) (lift_to_both0 (usize 1))) in
      letb r_2316 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 q0_2314) (lift_to_both0 q1_2315) in
      letb p_2317 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 r_2316) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2317)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc ; c_2251_loc ; tv4_2268_loc ; y_2269_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_encode_to_curve_svdw_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_ENCODE_TO_CURVE_SVDW : nat :=
  2324.
Program Definition g2_encode_to_curve_svdw (msg_2319 : byte_seq) (
    dst_2320 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc ; c_2251_loc ; tv4_2268_loc ; y_2269_loc])) [interface] (
    g2_t) :=
  ((letb u_2321 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2319) (lift_to_both0 dst_2320) (
          lift_to_both0 (usize 1)) in
      letb q_2322 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2321) (lift_to_both0 (usize 0))) in
      letb p_2323 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 q_2322) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2323)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc ; c_2251_loc ; tv4_2268_loc ; y_2269_loc])) [interface] (
      g2_t)).
Fail Next Obligation.

Definition g1_iso_a_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 5707120929990979)) : uint64;
    (secret (@repr U64 4425131892511951234)) : uint64;
    (secret (@repr U64 12748169179688756904)) : uint64;
    (secret (@repr U64 15629909748249821612)) : uint64;
    (secret (@repr U64 10994253769421683071)) : uint64;
    (secret (@repr U64 6698022561392380957)) : uint64
  ].

Definition g1_iso_b_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1360808972976160816)) : uint64;
    (secret (@repr U64 111203405409480251)) : uint64;
    (secret (@repr U64 2312248699302920304)) : uint64;
    (secret (@repr U64 11581500465278574325)) : uint64;
    (secret (@repr U64 6495071758858381989)) : uint64;
    (secret (@repr U64 15117538217124375520)) : uint64
  ].

Definition g1_xnum_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1270119733718627136)) : uint64;
    (secret (@repr U64 13261148298159854981)) : uint64;
    (secret (@repr U64 7723742117508874335)) : uint64;
    (secret (@repr U64 17465657917644792520)) : uint64;
    (secret (@repr U64 6201670911048166766)) : uint64;
    (secret (@repr U64 12586459670690286007)) : uint64
  ].

Definition g1_xnum_k_1_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1668951808976071471)) : uint64;
    (secret (@repr U64 398773841247578140)) : uint64;
    (secret (@repr U64 8941869963990959127)) : uint64;
    (secret (@repr U64 17682789360670468203)) : uint64;
    (secret (@repr U64 5204176168283587414)) : uint64;
    (secret (@repr U64 16732261237459223483)) : uint64
  ].

Definition g1_xnum_k_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 960393023080265964)) : uint64;
    (secret (@repr U64 2094253841180170779)) : uint64;
    (secret (@repr U64 14844748873776858085)) : uint64;
    (secret (@repr U64 7528018573573808732)) : uint64;
    (secret (@repr U64 10776056440809943711)) : uint64;
    (secret (@repr U64 16147550488514976944)) : uint64
  ].

Definition g1_xnum_k_3_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1691355743628586423)) : uint64;
    (secret (@repr U64 5622191986793862162)) : uint64;
    (secret (@repr U64 15561595211679121189)) : uint64;
    (secret (@repr U64 17416319752018800771)) : uint64;
    (secret (@repr U64 5996228842464768403)) : uint64;
    (secret (@repr U64 14245880009877842017)) : uint64
  ].

Definition g1_xnum_k_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1051997788391994435)) : uint64;
    (secret (@repr U64 7368650625050054228)) : uint64;
    (secret (@repr U64 11086623519836470079)) : uint64;
    (secret (@repr U64 607681821319080984)) : uint64;
    (secret (@repr U64 10978131499682789316)) : uint64;
    (secret (@repr U64 5842660658088809945)) : uint64
  ].

Definition g1_xnum_k_5_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1598992431623377919)) : uint64;
    (secret (@repr U64 130921168661596853)) : uint64;
    (secret (@repr U64 15797696746983946651)) : uint64;
    (secret (@repr U64 11444679715590672272)) : uint64;
    (secret (@repr U64 11567228658253249817)) : uint64;
    (secret (@repr U64 14777367860349315459)) : uint64
  ].

Definition g1_xnum_k_6_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 967946631563726121)) : uint64;
    (secret (@repr U64 7653628713030275775)) : uint64;
    (secret (@repr U64 12760252618317466849)) : uint64;
    (secret (@repr U64 10378793938173061930)) : uint64;
    (secret (@repr U64 10205808941053849290)) : uint64;
    (secret (@repr U64 15985511645807504772)) : uint64
  ].

Definition g1_xnum_k_7_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1709149555065084898)) : uint64;
    (secret (@repr U64 16750075057192140371)) : uint64;
    (secret (@repr U64 3849985779734105521)) : uint64;
    (secret (@repr U64 11998370262181639475)) : uint64;
    (secret (@repr U64 4159013751748851119)) : uint64;
    (secret (@repr U64 11298218755092433038)) : uint64
  ].

Definition g1_xnum_k_8_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 580186936973955012)) : uint64;
    (secret (@repr U64 8903813505199544589)) : uint64;
    (secret (@repr U64 14140024565662700916)) : uint64;
    (secret (@repr U64 11728946595272970718)) : uint64;
    (secret (@repr U64 5738313744366653077)) : uint64;
    (secret (@repr U64 7886252005760951063)) : uint64
  ].

Definition g1_xnum_k_9_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1628930385436977092)) : uint64;
    (secret (@repr U64 3318087848058654498)) : uint64;
    (secret (@repr U64 15937899882900905113)) : uint64;
    (secret (@repr U64 7449821001803307903)) : uint64;
    (secret (@repr U64 11752436998487615353)) : uint64;
    (secret (@repr U64 9161465579737517214)) : uint64
  ].

Definition g1_xnum_k_10_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1167027828517898210)) : uint64;
    (secret (@repr U64 8275623842221021965)) : uint64;
    (secret (@repr U64 18049808134997311382)) : uint64;
    (secret (@repr U64 15351349873550116966)) : uint64;
    (secret (@repr U64 17769927732099571180)) : uint64;
    (secret (@repr U64 14584871380308065147)) : uint64
  ].

Definition g1_xnum_k_11_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 495550047642324592)) : uint64;
    (secret (@repr U64 13627494601717575229)) : uint64;
    (secret (@repr U64 3591512392926246844)) : uint64;
    (secret (@repr U64 2576269112800734056)) : uint64;
    (secret (@repr U64 14000314106239596831)) : uint64;
    (secret (@repr U64 12234233096825917993)) : uint64
  ].

Definition g1_xden_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 633474091881273774)) : uint64;
    (secret (@repr U64 1779737893574802031)) : uint64;
    (secret (@repr U64 132274872219551930)) : uint64;
    (secret (@repr U64 11283074393783708770)) : uint64;
    (secret (@repr U64 13067430171545714168)) : uint64;
    (secret (@repr U64 11041975239630265116)) : uint64
  ].

Definition g1_xden_k_1_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1321272531362356291)) : uint64;
    (secret (@repr U64 5238936591227237942)) : uint64;
    (secret (@repr U64 8089002360232247308)) : uint64;
    (secret (@repr U64 82967328719421271)) : uint64;
    (secret (@repr U64 1430641118356186857)) : uint64;
    (secret (@repr U64 16557527386785790975)) : uint64
  ].

Definition g1_xden_k_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 804282852993868382)) : uint64;
    (secret (@repr U64 9311163821600184607)) : uint64;
    (secret (@repr U64 8037026956533927121)) : uint64;
    (secret (@repr U64 18205324308570099372)) : uint64;
    (secret (@repr U64 15466434890074226396)) : uint64;
    (secret (@repr U64 18213183315621985817)) : uint64
  ].

Definition g1_xden_k_3_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 234844145893171966)) : uint64;
    (secret (@repr U64 14428037799351479124)) : uint64;
    (secret (@repr U64 6559532710647391569)) : uint64;
    (secret (@repr U64 6110444250091843536)) : uint64;
    (secret (@repr U64 5293652763671852484)) : uint64;
    (secret (@repr U64 1373009181854280920)) : uint64
  ].

Definition g1_xden_k_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1416629893867312296)) : uint64;
    (secret (@repr U64 751851957792514173)) : uint64;
    (secret (@repr U64 18437674587247370939)) : uint64;
    (secret (@repr U64 10190314345946351322)) : uint64;
    (secret (@repr U64 11228207967368476701)) : uint64;
    (secret (@repr U64 6025034940388909598)) : uint64
  ].

Definition g1_xden_k_5_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1041270466333271993)) : uint64;
    (secret (@repr U64 6140956605115975401)) : uint64;
    (secret (@repr U64 4131830461445745997)) : uint64;
    (secret (@repr U64 739642499118176303)) : uint64;
    (secret (@repr U64 8358912131254619921)) : uint64;
    (secret (@repr U64 13847998906088228005)) : uint64
  ].

Definition g1_xden_k_6_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 536714149743900185)) : uint64;
    (secret (@repr U64 1098328982230230817)) : uint64;
    (secret (@repr U64 6273329123533496713)) : uint64;
    (secret (@repr U64 5633448088282521244)) : uint64;
    (secret (@repr U64 16894043798660571244)) : uint64;
    (secret (@repr U64 17016134625831438906)) : uint64
  ].

Definition g1_xden_k_7_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1488347500898461874)) : uint64;
    (secret (@repr U64 3509418672874520985)) : uint64;
    (secret (@repr U64 7962192351555381416)) : uint64;
    (secret (@repr U64 1843909372225399896)) : uint64;
    (secret (@repr U64 1127511003250156243)) : uint64;
    (secret (@repr U64 1294742680819751518)) : uint64
  ].

Definition g1_xden_k_8_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 725340084226051970)) : uint64;
    (secret (@repr U64 6814521545734988748)) : uint64;
    (secret (@repr U64 16176803544133875307)) : uint64;
    (secret (@repr U64 8363199516777220149)) : uint64;
    (secret (@repr U64 252877309218538352)) : uint64;
    (secret (@repr U64 5149562959837648449)) : uint64
  ].

Definition g1_xden_k_9_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 675470927100193492)) : uint64;
    (secret (@repr U64 5146891164735334016)) : uint64;
    (secret (@repr U64 17762958817130696759)) : uint64;
    (secret (@repr U64 8565656522589412373)) : uint64;
    (secret (@repr U64 10599026333335446784)) : uint64;
    (secret (@repr U64 3270603789344496906)) : uint64
  ].

Definition g1_ynum_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 652344406751465184)) : uint64;
    (secret (@repr U64 2710356675495255290)) : uint64;
    (secret (@repr U64 1273695771440998738)) : uint64;
    (secret (@repr U64 3121750372618945491)) : uint64;
    (secret (@repr U64 14775319642720936898)) : uint64;
    (secret (@repr U64 13733803417833814835)) : uint64
  ].

Definition g1_ynum_k_1_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1389807578337138705)) : uint64;
    (secret (@repr U64 15352831428748068483)) : uint64;
    (secret (@repr U64 1307144967559264317)) : uint64;
    (secret (@repr U64 1121505450578652468)) : uint64;
    (secret (@repr U64 15475889019760388287)) : uint64;
    (secret (@repr U64 16183658160488302230)) : uint64
  ].

Definition g1_ynum_k_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 57553299067792998)) : uint64;
    (secret (@repr U64 17628079362768849300)) : uint64;
    (secret (@repr U64 2689461337731570914)) : uint64;
    (secret (@repr U64 14070580367580990887)) : uint64;
    (secret (@repr U64 15162865775551710499)) : uint64;
    (secret (@repr U64 13321614990632673782)) : uint64
  ].

Definition g1_ynum_k_3_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 141972750621744161)) : uint64;
    (secret (@repr U64 8689824239172478807)) : uint64;
    (secret (@repr U64 15288216298323671324)) : uint64;
    (secret (@repr U64 712874875091754233)) : uint64;
    (secret (@repr U64 16014900032503684588)) : uint64;
    (secret (@repr U64 11976580453200426187)) : uint64
  ].

Definition g1_ynum_k_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 633886036738506515)) : uint64;
    (secret (@repr U64 6678644607214234052)) : uint64;
    (secret (@repr U64 1825425679455244472)) : uint64;
    (secret (@repr U64 8755912272271186652)) : uint64;
    (secret (@repr U64 3379943669301788840)) : uint64;
    (secret (@repr U64 4735212769449148123)) : uint64
  ].

Definition g1_ynum_k_5_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1612358804494830442)) : uint64;
    (secret (@repr U64 2454990789666711200)) : uint64;
    (secret (@repr U64 8405916841409361853)) : uint64;
    (secret (@repr U64 8525415512662168654)) : uint64;
    (secret (@repr U64 2323684950984523890)) : uint64;
    (secret (@repr U64 11074978966450447856)) : uint64
  ].

Definition g1_ynum_k_6_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 336375361001233340)) : uint64;
    (secret (@repr U64 12882959944969186108)) : uint64;
    (secret (@repr U64 16671121624101127371)) : uint64;
    (secret (@repr U64 5922586712221110071)) : uint64;
    (secret (@repr U64 5163511947597922654)) : uint64;
    (secret (@repr U64 14511152726087948018)) : uint64
  ].

Definition g1_ynum_k_7_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 686738286210365551)) : uint64;
    (secret (@repr U64 16039894141796533876)) : uint64;
    (secret (@repr U64 1660145734357211167)) : uint64;
    (secret (@repr U64 18231571463891878950)) : uint64;
    (secret (@repr U64 4825120264949852469)) : uint64;
    (secret (@repr U64 11627815551290637097)) : uint64
  ].

Definition g1_ynum_k_8_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 719520515476580427)) : uint64;
    (secret (@repr U64 16756942182913253819)) : uint64;
    (secret (@repr U64 10320769399998235244)) : uint64;
    (secret (@repr U64 2200974244968450750)) : uint64;
    (secret (@repr U64 7626373186594408355)) : uint64;
    (secret (@repr U64 6933025920263103879)) : uint64
  ].

Definition g1_ynum_k_9_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1016611174344998325)) : uint64;
    (secret (@repr U64 2466492548686891555)) : uint64;
    (secret (@repr U64 14135124294293452542)) : uint64;
    (secret (@repr U64 475233659467912251)) : uint64;
    (secret (@repr U64 11186783513499056751)) : uint64;
    (secret (@repr U64 3147922594245844016)) : uint64
  ].

Definition g1_ynum_k_10_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1833315000454533566)) : uint64;
    (secret (@repr U64 1007974600900082579)) : uint64;
    (secret (@repr U64 14785260176242854207)) : uint64;
    (secret (@repr U64 15066861003931772432)) : uint64;
    (secret (@repr U64 3584647998681889532)) : uint64;
    (secret (@repr U64 16722834201330696498)) : uint64
  ].

Definition g1_ynum_k_11_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1780164921828767454)) : uint64;
    (secret (@repr U64 13337622794239929804)) : uint64;
    (secret (@repr U64 5923739534552515142)) : uint64;
    (secret (@repr U64 3345046972101780530)) : uint64;
    (secret (@repr U64 5321510883028162054)) : uint64;
    (secret (@repr U64 14846055306840460686)) : uint64
  ].

Definition g1_ynum_k_12_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 799438051374502809)) : uint64;
    (secret (@repr U64 15083972834952036164)) : uint64;
    (secret (@repr U64 8838227588559581326)) : uint64;
    (secret (@repr U64 13846054168121598783)) : uint64;
    (secret (@repr U64 488730451382505970)) : uint64;
    (secret (@repr U64 958146249756188408)) : uint64
  ].

Definition g1_ynum_k_13_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 163716820423854747)) : uint64;
    (secret (@repr U64 8285498163857659356)) : uint64;
    (secret (@repr U64 8465424830341846400)) : uint64;
    (secret (@repr U64 1433942577299613084)) : uint64;
    (secret (@repr U64 14325828012864645732)) : uint64;
    (secret (@repr U64 4817114329354076467)) : uint64
  ].

Definition g1_ynum_k_14_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 414658151749832465)) : uint64;
    (secret (@repr U64 189531577938912252)) : uint64;
    (secret (@repr U64 6802473390048830824)) : uint64;
    (secret (@repr U64 15684647020317539556)) : uint64;
    (secret (@repr U64 7755485098777620407)) : uint64;
    (secret (@repr U64 9685868895687483979)) : uint64
  ].

Definition g1_ynum_k_15_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1578157964224562126)) : uint64;
    (secret (@repr U64 5666948055268535989)) : uint64;
    (secret (@repr U64 14634479491382401593)) : uint64;
    (secret (@repr U64 6317940024988860850)) : uint64;
    (secret (@repr U64 13142913832013798519)) : uint64;
    (secret (@repr U64 338991247778166276)) : uint64
  ].

Definition g1_yden_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1590100849350973618)) : uint64;
    (secret (@repr U64 5915497081334721257)) : uint64;
    (secret (@repr U64 6924968209373727718)) : uint64;
    (secret (@repr U64 17204633670617869946)) : uint64;
    (secret (@repr U64 572916540828819565)) : uint64;
    (secret (@repr U64 92203205520679873)) : uint64
  ].

Definition g1_yden_k_1_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1829261189398470686)) : uint64;
    (secret (@repr U64 1877083417397643448)) : uint64;
    (secret (@repr U64 9640042925497046428)) : uint64;
    (secret (@repr U64 11862766565471805471)) : uint64;
    (secret (@repr U64 8693114993904885301)) : uint64;
    (secret (@repr U64 3672140328108400701)) : uint64
  ].

Definition g1_yden_k_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 400243331105348135)) : uint64;
    (secret (@repr U64 8046435537999802711)) : uint64;
    (secret (@repr U64 8702226981475745585)) : uint64;
    (secret (@repr U64 879791671491744492)) : uint64;
    (secret (@repr U64 11994630442058346377)) : uint64;
    (secret (@repr U64 2172204746352322546)) : uint64
  ].

Definition g1_yden_k_3_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1637008473169220501)) : uint64;
    (secret (@repr U64 17441636237435581649)) : uint64;
    (secret (@repr U64 15066165676546511630)) : uint64;
    (secret (@repr U64 1314387578457599809)) : uint64;
    (secret (@repr U64 8247046336453711789)) : uint64;
    (secret (@repr U64 12164906044230685718)) : uint64
  ].

Definition g1_yden_k_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 855930740911588324)) : uint64;
    (secret (@repr U64 12685735333705453020)) : uint64;
    (secret (@repr U64 14326404096614579120)) : uint64;
    (secret (@repr U64 6066025509460822294)) : uint64;
    (secret (@repr U64 11676450493790612973)) : uint64;
    (secret (@repr U64 15724621714793234461)) : uint64
  ].

Definition g1_yden_k_5_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 637792788410719021)) : uint64;
    (secret (@repr U64 11507373155986977154)) : uint64;
    (secret (@repr U64 13186912195705886849)) : uint64;
    (secret (@repr U64 14262012144631372388)) : uint64;
    (secret (@repr U64 5328758613570342114)) : uint64;
    (secret (@repr U64 199925847119476652)) : uint64
  ].

Definition g1_yden_k_6_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1612297190139091759)) : uint64;
    (secret (@repr U64 14103733843373163083)) : uint64;
    (secret (@repr U64 6840121186619029743)) : uint64;
    (secret (@repr U64 6760859324815900753)) : uint64;
    (secret (@repr U64 15418807805142572985)) : uint64;
    (secret (@repr U64 4402853133867972444)) : uint64
  ].

Definition g1_yden_k_7_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1631410310868805610)) : uint64;
    (secret (@repr U64 269334146695233390)) : uint64;
    (secret (@repr U64 16547411811928854487)) : uint64;
    (secret (@repr U64 18353100669930795314)) : uint64;
    (secret (@repr U64 13339932232668798692)) : uint64;
    (secret (@repr U64 6984591927261867737)) : uint64
  ].

Definition g1_yden_k_8_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1758313625630302499)) : uint64;
    (secret (@repr U64 1881349400343039172)) : uint64;
    (secret (@repr U64 18013005311323887904)) : uint64;
    (secret (@repr U64 12377427846571989832)) : uint64;
    (secret (@repr U64 5967237584920922243)) : uint64;
    (secret (@repr U64 7720081932193848650)) : uint64
  ].

Definition g1_yden_k_9_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1619701357752249884)) : uint64;
    (secret (@repr U64 16898074901591262352)) : uint64;
    (secret (@repr U64 3609344159736760251)) : uint64;
    (secret (@repr U64 5983130161189999867)) : uint64;
    (secret (@repr U64 14355327869992416094)) : uint64;
    (secret (@repr U64 3778226018344582997)) : uint64
  ].

Definition g1_yden_k_10_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 347606589330687421)) : uint64;
    (secret (@repr U64 5255719044972187933)) : uint64;
    (secret (@repr U64 11271894388753671721)) : uint64;
    (secret (@repr U64 1033887512062764488)) : uint64;
    (secret (@repr U64 8189165486932690436)) : uint64;
    (secret (@repr U64 70004379462101672)) : uint64
  ].

Definition g1_yden_k_11_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 778202887894139711)) : uint64;
    (secret (@repr U64 17691595219776375879)) : uint64;
    (secret (@repr U64 9193253711563866834)) : uint64;
    (secret (@repr U64 10092455202333888821)) : uint64;
    (secret (@repr U64 1655469341950262250)) : uint64;
    (secret (@repr U64 10845992994110574738)) : uint64
  ].

Definition g1_yden_k_12_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 781015344221683683)) : uint64;
    (secret (@repr U64 14078588081290548374)) : uint64;
    (secret (@repr U64 6067271023149908518)) : uint64;
    (secret (@repr U64 9033357708497886086)) : uint64;
    (secret (@repr U64 10592474449179118273)) : uint64;
    (secret (@repr U64 2204988348113831372)) : uint64
  ].

Definition g1_yden_k_13_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 172830037692534587)) : uint64;
    (secret (@repr U64 7101012286790006514)) : uint64;
    (secret (@repr U64 13787308004332873665)) : uint64;
    (secret (@repr U64 14660498759553796110)) : uint64;
    (secret (@repr U64 4757234684169342080)) : uint64;
    (secret (@repr U64 15130647872920159991)) : uint64
  ].

Definition g1_yden_k_14_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1013206390650290238)) : uint64;
    (secret (@repr U64 7720336747103001025)) : uint64;
    (secret (@repr U64 8197694151986493523)) : uint64;
    (secret (@repr U64 3625112747029342752)) : uint64;
    (secret (@repr U64 6675167463148394368)) : uint64;
    (secret (@repr U64 4905905684016745359)) : uint64
  ].

Definition x1_2325_loc : ChoiceEqualityLocation :=
  (fp_t ; 2327%nat).
Definition y_2326_loc : ChoiceEqualityLocation :=
  (fp_t ; 2328%nat).
Notation "'g1_simple_swu_iso_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_out'" :=((fp_t '× fp_t
  ) : choice_type) (in custom pack_type at level 2).
Definition G1_SIMPLE_SWU_ISO : nat :=
  2338.
Program Definition g1_simple_swu_iso (u_2332 : fp_t)
  : both (CEfset ([x1_2325_loc ; y_2326_loc])) [interface] ((fp_t '× fp_t)) :=
  ((letb z_2329 : fp_t :=
        nat_mod_from_literal (_) (lift_to_both0 (@repr U128 11)) in
      letb a_2330 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (
            lift_to_both0 g1_iso_a_v)) in
      letb b_2331 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (
            lift_to_both0 g1_iso_b_v)) in
      letb tv1_2333 : fp_t :=
        nat_mod_inv ((((lift_to_both0 z_2329) *% (lift_to_both0 z_2329)) *% (
              nat_mod_exp (lift_to_both0 u_2332) (lift_to_both0 (
                  @repr U32 4)))) +% (((lift_to_both0 z_2329) *% (
                lift_to_both0 u_2332)) *% (lift_to_both0 u_2332))) in
      letbm x1_2325 : fp_t loc( x1_2325_loc ) :=
        (((nat_mod_zero ) -% (lift_to_both0 b_2331)) *% (nat_mod_inv (
              lift_to_both0 a_2330))) *% ((nat_mod_one ) +% (
            lift_to_both0 tv1_2333)) in
      letb '(x1_2325) :=
        if (lift_to_both0 tv1_2333) =.? (nat_mod_zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2325_loc])) (L2 := CEfset (
            [x1_2325_loc ; y_2326_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2325 loc( x1_2325_loc ) :=
            (lift_to_both0 b_2331) *% (nat_mod_inv ((lift_to_both0 z_2329) *% (
                  lift_to_both0 a_2330))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2325)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2325)
         in
      letb gx1_2334 : fp_t :=
        ((nat_mod_exp (lift_to_both0 x1_2325) (lift_to_both0 (
                @repr U32 3))) +% ((lift_to_both0 a_2330) *% (
              lift_to_both0 x1_2325))) +% (lift_to_both0 b_2331) in
      letb x2_2335 : fp_t :=
        (((lift_to_both0 z_2329) *% (lift_to_both0 u_2332)) *% (
            lift_to_both0 u_2332)) *% (lift_to_both0 x1_2325) in
      letb gx2_2336 : fp_t :=
        ((nat_mod_exp (lift_to_both0 x2_2335) (lift_to_both0 (
                @repr U32 3))) +% ((lift_to_both0 a_2330) *% (
              lift_to_both0 x2_2335))) +% (lift_to_both0 b_2331) in
      letb '(x_2337, y_2326) : (fp_t '× fp_t) :=
        if is_pure (I := [interface]) (fp_is_square (lift_to_both0 gx1_2334))
        then prod_b(lift_to_both0 x1_2325, fp_sqrt (lift_to_both0 gx1_2334))
        else prod_b(lift_to_both0 x2_2335, fp_sqrt (lift_to_both0 gx2_2336)) in
      letb '(y_2326) :=
        if (fp_sgn0 (lift_to_both0 u_2332)) !=.? (fp_sgn0 (
            lift_to_both0 y_2326)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2325_loc ; y_2326_loc])) (
          L2 := CEfset ([x1_2325_loc ; y_2326_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2326 loc( y_2326_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_2326) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2326)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2326)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2337,
          lift_to_both0 y_2326
        ))
      ) : both (CEfset ([x1_2325_loc ; y_2326_loc])) [interface] ((fp_t '× fp_t
      ))).
Fail Next Obligation.

Definition xden_k_2340_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2352%nat).
Definition ynum_k_2341_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2353%nat).
Definition xx_2346_loc : ChoiceEqualityLocation :=
  (fp_t ; 2354%nat).
Definition xx_2344_loc : ChoiceEqualityLocation :=
  (fp_t ; 2355%nat).
Definition inf_2351_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2356%nat).
Definition xx_2348_loc : ChoiceEqualityLocation :=
  (fp_t ; 2357%nat).
Definition yden_k_2342_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2358%nat).
Definition xnum_2343_loc : ChoiceEqualityLocation :=
  (fp_t ; 2359%nat).
Definition ynum_2347_loc : ChoiceEqualityLocation :=
  (fp_t ; 2360%nat).
Definition xnum_k_2339_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2361%nat).
Definition yden_2349_loc : ChoiceEqualityLocation :=
  (fp_t ; 2362%nat).
Definition xden_2345_loc : ChoiceEqualityLocation :=
  (fp_t ; 2363%nat).
Definition xx_2350_loc : ChoiceEqualityLocation :=
  (fp_t ; 2364%nat).
Notation "'g1_isogeny_map_inp'" :=(
  fp_t × fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_ISOGENY_MAP : nat :=
  2373.
Program Definition g1_isogeny_map (x_2366 : fp_t) (y_2371 : fp_t)
  : both (CEfset (
      [xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) [interface] (
    g1_t) :=
  ((letbm xnum_k_2339 : seq fp_t loc( xnum_k_2339_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 12)) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_0_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_1_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_2_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_3_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_4_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_5_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_6_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_7_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_8_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_9_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_10_v)))) in
      letb xnum_k_2339 : seq fp_t :=
        seq_upd xnum_k_2339 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_11_v)))) in
      letbm xden_k_2340 : seq fp_t loc( xden_k_2340_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 10)) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_0_v)))) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_1_v)))) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_2_v)))) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_3_v)))) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_4_v)))) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_5_v)))) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_6_v)))) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_7_v)))) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_8_v)))) in
      letb xden_k_2340 : seq fp_t :=
        seq_upd xden_k_2340 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_9_v)))) in
      letbm ynum_k_2341 : seq fp_t loc( ynum_k_2341_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 16)) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_0_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_1_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_2_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_3_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_4_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_5_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_6_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_7_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_8_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_9_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_10_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_11_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 12)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_12_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 13)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_13_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 14)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_14_v)))) in
      letb ynum_k_2341 : seq fp_t :=
        seq_upd ynum_k_2341 (lift_to_both0 (usize 15)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_15_v)))) in
      letbm yden_k_2342 : seq fp_t loc( yden_k_2342_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 15)) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_0_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_1_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_2_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_3_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_4_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_5_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_6_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_7_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_8_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_9_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_10_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_11_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 12)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_12_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 13)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_13_v)))) in
      letb yden_k_2342 : seq fp_t :=
        seq_upd yden_k_2342 (lift_to_both0 (usize 14)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_14_v)))) in
      letbm xnum_2343 : fp_t loc( xnum_2343_loc ) := nat_mod_zero  in
      letbm xx_2344 : fp_t loc( xx_2344_loc ) := nat_mod_one  in
      letb '(xnum_2343, xx_2344) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xnum_k_2339)) prod_ce(xnum_2343, xx_2344) (L := (
              CEfset (
                [xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc]))) (
            I := [interface]) (fun i_2365 '(xnum_2343, xx_2344) =>
            letbm xnum_2343 loc( xnum_2343_loc ) :=
              (lift_to_both0 xnum_2343) +% ((lift_to_both0 xx_2344) *% (
                  seq_index (xnum_k_2339) (lift_to_both0 i_2365))) in
            letbm xx_2344 loc( xx_2344_loc ) :=
              (lift_to_both0 xx_2344) *% (lift_to_both0 x_2366) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2343,
                lift_to_both0 xx_2344
              ))
            ) in
      letbm xden_2345 : fp_t loc( xden_2345_loc ) := nat_mod_zero  in
      letbm xx_2346 : fp_t loc( xx_2346_loc ) := nat_mod_one  in
      letb '(xden_2345, xx_2346) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xden_k_2340)) prod_ce(xden_2345, xx_2346) (L := (
              CEfset (
                [xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc]))) (
            I := [interface]) (fun i_2367 '(xden_2345, xx_2346) =>
            letbm xden_2345 loc( xden_2345_loc ) :=
              (lift_to_both0 xden_2345) +% ((lift_to_both0 xx_2346) *% (
                  seq_index (xden_k_2340) (lift_to_both0 i_2367))) in
            letbm xx_2346 loc( xx_2346_loc ) :=
              (lift_to_both0 xx_2346) *% (lift_to_both0 x_2366) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2345,
                lift_to_both0 xx_2346
              ))
            ) in
      letbm xden_2345 loc( xden_2345_loc ) :=
        (lift_to_both0 xden_2345) +% (lift_to_both0 xx_2346) in
      letbm ynum_2347 : fp_t loc( ynum_2347_loc ) := nat_mod_zero  in
      letbm xx_2348 : fp_t loc( xx_2348_loc ) := nat_mod_one  in
      letb '(ynum_2347, xx_2348) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 ynum_k_2341)) prod_ce(ynum_2347, xx_2348) (L := (
              CEfset (
                [xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc]))) (
            I := [interface]) (fun i_2368 '(ynum_2347, xx_2348) =>
            letbm ynum_2347 loc( ynum_2347_loc ) :=
              (lift_to_both0 ynum_2347) +% ((lift_to_both0 xx_2348) *% (
                  seq_index (ynum_k_2341) (lift_to_both0 i_2368))) in
            letbm xx_2348 loc( xx_2348_loc ) :=
              (lift_to_both0 xx_2348) *% (lift_to_both0 x_2366) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2347,
                lift_to_both0 xx_2348
              ))
            ) in
      letbm yden_2349 : fp_t loc( yden_2349_loc ) := nat_mod_zero  in
      letbm xx_2350 : fp_t loc( xx_2350_loc ) := nat_mod_one  in
      letb '(yden_2349, xx_2350) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 yden_k_2342)) prod_ce(yden_2349, xx_2350) (L := (
              CEfset (
                [xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc]))) (
            I := [interface]) (fun i_2369 '(yden_2349, xx_2350) =>
            letbm yden_2349 loc( yden_2349_loc ) :=
              (lift_to_both0 yden_2349) +% ((lift_to_both0 xx_2350) *% (
                  seq_index (yden_k_2342) (lift_to_both0 i_2369))) in
            letbm xx_2350 loc( xx_2350_loc ) :=
              (lift_to_both0 xx_2350) *% (lift_to_both0 x_2366) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2349,
                lift_to_both0 xx_2350
              ))
            ) in
      letbm yden_2349 loc( yden_2349_loc ) :=
        (lift_to_both0 yden_2349) +% (lift_to_both0 xx_2350) in
      letb xr_2370 : fp_t :=
        (lift_to_both0 xnum_2343) *% (nat_mod_inv (lift_to_both0 xden_2345)) in
      letb yr_2372 : fp_t :=
        ((lift_to_both0 y_2371) *% (lift_to_both0 ynum_2347)) *% (nat_mod_inv (
            lift_to_both0 yden_2349)) in
      letbm inf_2351 : bool_ChoiceEquality loc( inf_2351_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(inf_2351) :=
        if ((lift_to_both0 xden_2345) =.? (nat_mod_zero )) || ((
            lift_to_both0 yden_2349) =.? (nat_mod_zero )) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) (
          L2 := CEfset (
            [xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm inf_2351 loc( inf_2351_loc ) :=
            lift_to_both0 ((true : bool_ChoiceEquality)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2351)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 inf_2351)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xr_2370,
          lift_to_both0 yr_2372,
          lift_to_both0 inf_2351
        ))
      ) : both (CEfset (
        [xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_map_to_curve_sswu_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_MAP_TO_CURVE_SSWU : nat :=
  2378.
Program Definition g1_map_to_curve_sswu (u_2374 : fp_t)
  : both (CEfset (
      [x1_2325_loc ; y_2326_loc ; xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) [interface] (
    g1_t) :=
  ((letb '(xp_2375, yp_2376) : (fp_t '× fp_t) :=
        g1_simple_swu_iso (lift_to_both0 u_2374) in
      letb p_2377 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_isogeny_map (lift_to_both0 xp_2375) (lift_to_both0 yp_2376) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2377)
      ) : both (CEfset (
        [x1_2325_loc ; y_2326_loc ; xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_hash_to_curve_sswu_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_HASH_TO_CURVE_SSWU : nat :=
  2386.
Program Definition g1_hash_to_curve_sswu (msg_2379 : byte_seq) (
    dst_2380 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc ; x1_2325_loc ; y_2326_loc ; xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) [interface] (
    g1_t) :=
  ((letb u_2381 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2379) (lift_to_both0 dst_2380) (
          lift_to_both0 (usize 2)) in
      letb q0_2382 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2381) (lift_to_both0 (usize 0))) in
      letb q1_2383 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2381) (lift_to_both0 (usize 1))) in
      letb r_2384 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1add (lift_to_both0 q0_2382) (lift_to_both0 q1_2383) in
      letb p_2385 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 r_2384) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2385)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc ; x1_2325_loc ; y_2326_loc ; xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_encode_to_curve_sswu_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_ENCODE_TO_CURVE_SSWU : nat :=
  2392.
Program Definition g1_encode_to_curve_sswu (msg_2387 : byte_seq) (
    dst_2388 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc ; x1_2325_loc ; y_2326_loc ; xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) [interface] (
    g1_t) :=
  ((letb u_2389 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2387) (lift_to_both0 dst_2388) (
          lift_to_both0 (usize 1)) in
      letb q_2390 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2389) (lift_to_both0 (usize 0))) in
      letb p_2391 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 q_2390) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2391)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2161_loc ; x1_2325_loc ; y_2326_loc ; xnum_k_2339_loc ; xden_k_2340_loc ; ynum_k_2341_loc ; yden_k_2342_loc ; xnum_2343_loc ; xx_2344_loc ; xden_2345_loc ; xx_2346_loc ; ynum_2347_loc ; xx_2348_loc ; yden_2349_loc ; xx_2350_loc ; inf_2351_loc])) [interface] (
      g1_t)).
Fail Next Obligation.

Definition g2_xnum_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 416399692810564414)) : uint64;
    (secret (@repr U64 13500519111022079365)) : uint64;
    (secret (@repr U64 3658379999393219626)) : uint64;
    (secret (@repr U64 9850925049107374429)) : uint64;
    (secret (@repr U64 6640057249351452444)) : uint64;
    (secret (@repr U64 7077594464397203414)) : uint64
  ].

Definition g2_xnum_k_1_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1249199078431693244)) : uint64;
    (secret (@repr U64 3608069185647134863)) : uint64;
    (secret (@repr U64 10975139998179658879)) : uint64;
    (secret (@repr U64 11106031073612571672)) : uint64;
    (secret (@repr U64 1473427674344805717)) : uint64;
    (secret (@repr U64 2786039319482058522)) : uint64
  ].

Definition g2_xnum_k_2_r_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1249199078431693244)) : uint64;
    (secret (@repr U64 3608069185647134863)) : uint64;
    (secret (@repr U64 10975139998179658879)) : uint64;
    (secret (@repr U64 11106031073612571672)) : uint64;
    (secret (@repr U64 1473427674344805717)) : uint64;
    (secret (@repr U64 2786039319482058526)) : uint64
  ].

Definition g2_xnum_k_2_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 624599539215846622)) : uint64;
    (secret (@repr U64 1804034592823567431)) : uint64;
    (secret (@repr U64 14710942035944605247)) : uint64;
    (secret (@repr U64 14776387573661061644)) : uint64;
    (secret (@repr U64 736713837172402858)) : uint64;
    (secret (@repr U64 10616391696595805069)) : uint64
  ].

Definition g2_xnum_k_3_r_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1665598771242257658)) : uint64;
    (secret (@repr U64 17108588296669214228)) : uint64;
    (secret (@repr U64 14633519997572878506)) : uint64;
    (secret (@repr U64 2510212049010394485)) : uint64;
    (secret (@repr U64 8113484923696258161)) : uint64;
    (secret (@repr U64 9863633783879261905)) : uint64
  ].

Definition g2_xden_k_0_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863523)) : uint64
  ].

Definition g2_xden_k_1_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863583)) : uint64
  ].

Definition g2_ynum_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1526798873638736187)) : uint64;
    (secret (@repr U64 6459500568425337235)) : uint64;
    (secret (@repr U64 1116230615302104219)) : uint64;
    (secret (@repr U64 17673314439684154624)) : uint64;
    (secret (@repr U64 18197961889718808424)) : uint64;
    (secret (@repr U64 1355520937843676934)) : uint64
  ].

Definition g2_ynum_k_1_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 416399692810564414)) : uint64;
    (secret (@repr U64 13500519111022079365)) : uint64;
    (secret (@repr U64 3658379999393219626)) : uint64;
    (secret (@repr U64 9850925049107374429)) : uint64;
    (secret (@repr U64 6640057249351452444)) : uint64;
    (secret (@repr U64 7077594464397203390)) : uint64
  ].

Definition g2_ynum_k_2_r_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1249199078431693244)) : uint64;
    (secret (@repr U64 3608069185647134863)) : uint64;
    (secret (@repr U64 10975139998179658879)) : uint64;
    (secret (@repr U64 11106031073612571672)) : uint64;
    (secret (@repr U64 1473427674344805717)) : uint64;
    (secret (@repr U64 2786039319482058524)) : uint64
  ].

Definition g2_ynum_k_2_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 624599539215846622)) : uint64;
    (secret (@repr U64 1804034592823567431)) : uint64;
    (secret (@repr U64 14710942035944605247)) : uint64;
    (secret (@repr U64 14776387573661061644)) : uint64;
    (secret (@repr U64 736713837172402858)) : uint64;
    (secret (@repr U64 10616391696595805071)) : uint64
  ].

Definition g2_ynum_k_3_r_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1318599027233453979)) : uint64;
    (secret (@repr U64 18155985086623849168)) : uint64;
    (secret (@repr U64 8510412652460270214)) : uint64;
    (secret (@repr U64 12747851915130467410)) : uint64;
    (secret (@repr U64 5654561228188306393)) : uint64;
    (secret (@repr U64 16263467779354626832)) : uint64
  ].

Definition g2_yden_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863163)) : uint64
  ].

Definition g2_yden_k_1_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863379)) : uint64
  ].

Definition g2_yden_k_2_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863577)) : uint64
  ].

Definition x1_2393_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2395%nat).
Definition y_2394_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2396%nat).
Notation "'g2_simple_swu_iso_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_out'" :=((fp2_t '× fp2_t
  ) : choice_type) (in custom pack_type at level 2).
Definition G2_SIMPLE_SWU_ISO : nat :=
  2406.
Program Definition g2_simple_swu_iso (u_2400 : fp2_t)
  : both (CEfset ([c_2251_loc ; x1_2393_loc ; y_2394_loc])) [interface] ((
      fp2_t '×
      fp2_t
    )) :=
  ((letb z_2397 : (fp_t '× fp_t) :=
        fp2neg (prod_b(nat_mod_two , nat_mod_one )) in
      letb a_2398 : (fp_t '× fp_t) :=
        prod_b(
          nat_mod_zero ,
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 240))
        ) in
      letb b_2399 : (fp_t '× fp_t) :=
        prod_b(
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012)),
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012))
        ) in
      letb tv1_2401 : (fp_t '× fp_t) :=
        fp2inv (fp2add (fp2mul (fp2mul (lift_to_both0 z_2397) (
                lift_to_both0 z_2397)) (fp2mul (fp2mul (lift_to_both0 u_2400) (
                  lift_to_both0 u_2400)) (fp2mul (lift_to_both0 u_2400) (
                  lift_to_both0 u_2400)))) (fp2mul (lift_to_both0 z_2397) (
              fp2mul (lift_to_both0 u_2400) (lift_to_both0 u_2400)))) in
      letbm x1_2393 : (fp_t '× fp_t) loc( x1_2393_loc ) :=
        fp2mul (fp2mul (fp2neg (lift_to_both0 b_2399)) (fp2inv (
              lift_to_both0 a_2398))) (fp2add (fp2fromfp (nat_mod_one )) (
            lift_to_both0 tv1_2401)) in
      letb '(x1_2393) :=
        if (lift_to_both0 tv1_2401) =.? (fp2zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2393_loc])) (L2 := CEfset (
            [c_2251_loc ; x1_2393_loc ; y_2394_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2393 loc( x1_2393_loc ) :=
            fp2mul (lift_to_both0 b_2399) (fp2inv (fp2mul (
                  lift_to_both0 z_2397) (lift_to_both0 a_2398))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2393)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2393)
         in
      letb gx1_2402 : (fp_t '× fp_t) :=
        fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x1_2393) (
                lift_to_both0 x1_2393)) (lift_to_both0 x1_2393)) (fp2mul (
              lift_to_both0 a_2398) (lift_to_both0 x1_2393))) (
          lift_to_both0 b_2399) in
      letb x2_2403 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 z_2397) (fp2mul (lift_to_both0 u_2400) (
              lift_to_both0 u_2400))) (lift_to_both0 x1_2393) in
      letb gx2_2404 : (fp_t '× fp_t) :=
        fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x2_2403) (
                lift_to_both0 x2_2403)) (lift_to_both0 x2_2403)) (fp2mul (
              lift_to_both0 a_2398) (lift_to_both0 x2_2403))) (
          lift_to_both0 b_2399) in
      letb '(x_2405, y_2394) : ((fp_t '× fp_t) '× fp2_t) :=
        if is_pure (I := [interface]) (fp2_is_square (lift_to_both0 gx1_2402))
        then prod_b(lift_to_both0 x1_2393, fp2_sqrt (lift_to_both0 gx1_2402))
        else prod_b(lift_to_both0 x2_2403, fp2_sqrt (lift_to_both0 gx2_2404)) in
      letb '(y_2394) :=
        if (fp2_sgn0 (lift_to_both0 u_2400)) !=.? (fp2_sgn0 (
            lift_to_both0 y_2394)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [c_2251_loc ; x1_2393_loc ; y_2394_loc])) (L2 := CEfset (
            [c_2251_loc ; x1_2393_loc ; y_2394_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2394 loc( y_2394_loc ) := fp2neg (lift_to_both0 y_2394) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2394)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2394)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2405,
          lift_to_both0 y_2394
        ))
      ) : both (CEfset ([c_2251_loc ; x1_2393_loc ; y_2394_loc])) [interface] ((
        fp2_t '×
        fp2_t
      ))).
Fail Next Obligation.

Definition xx_2414_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2420%nat).
Definition xden_2413_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2421%nat).
Definition ynum_k_2409_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2422%nat).
Definition yden_k_2410_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2423%nat).
Definition xx_2412_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2424%nat).
Definition xnum_k_2407_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2425%nat).
Definition yden_2417_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2426%nat).
Definition xden_k_2408_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2427%nat).
Definition ynum_2415_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2428%nat).
Definition xx_2418_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2429%nat).
Definition xnum_2411_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2430%nat).
Definition xx_2416_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2431%nat).
Definition inf_2419_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2432%nat).
Notation "'g2_isogeny_map_inp'" :=(
  fp2_t × fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_ISOGENY_MAP : nat :=
  2441.
Program Definition g2_isogeny_map (x_2434 : fp2_t) (y_2439 : fp2_t)
  : both (CEfset (
      [xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) [interface] (
    g2_t) :=
  ((letbm xnum_k_2407 : seq (fp_t '× fp_t) loc( xnum_k_2407_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
      letb xnum_k_2407 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2407 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_0_v))
            ))) in
      letb xnum_k_2407 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2407 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_1_i_v))
            ))) in
      letb xnum_k_2407 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2407 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_2_r_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_2_i_v))
            ))) in
      letb xnum_k_2407 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2407 (lift_to_both0 (usize 3)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_3_r_v)),
              nat_mod_zero 
            ))) in
      letbm xden_k_2408 : seq (fp_t '× fp_t) loc( xden_k_2408_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 2)) in
      letb xden_k_2408 : seq (fp_t '× fp_t) :=
        seq_upd xden_k_2408 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xden_k_0_i_v))
            ))) in
      letb xden_k_2408 : seq (fp_t '× fp_t) :=
        seq_upd xden_k_2408 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 12)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xden_k_1_i_v))
            ))) in
      letbm ynum_k_2409 : seq (fp_t '× fp_t) loc( ynum_k_2409_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
      letb ynum_k_2409 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2409 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_0_v))
            ))) in
      letb ynum_k_2409 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2409 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_1_i_v))
            ))) in
      letb ynum_k_2409 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2409 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_2_r_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_2_i_v))
            ))) in
      letb ynum_k_2409 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2409 (lift_to_both0 (usize 3)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_3_r_v)),
              nat_mod_zero 
            ))) in
      letbm yden_k_2410 : seq (fp_t '× fp_t) loc( yden_k_2410_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 3)) in
      letb yden_k_2410 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2410 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_0_v))
            ))) in
      letb yden_k_2410 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2410 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_1_i_v))
            ))) in
      letb yden_k_2410 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2410 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 18)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_2_i_v))
            ))) in
      letbm xnum_2411 : (fp_t '× fp_t) loc( xnum_2411_loc ) := fp2zero  in
      letbm xx_2412 : (fp_t '× fp_t) loc( xx_2412_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(xnum_2411, xx_2412) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xnum_k_2407)) prod_ce(xnum_2411, xx_2412) (L := (
              CEfset (
                [xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc]))) (
            I := [interface]) (fun i_2433 '(xnum_2411, xx_2412) =>
            letbm xnum_2411 loc( xnum_2411_loc ) :=
              fp2add (lift_to_both0 xnum_2411) (fp2mul (lift_to_both0 xx_2412) (
                  seq_index (xnum_k_2407) (lift_to_both0 i_2433))) in
            letbm xx_2412 loc( xx_2412_loc ) :=
              fp2mul (lift_to_both0 xx_2412) (lift_to_both0 x_2434) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2411,
                lift_to_both0 xx_2412
              ))
            ) in
      letbm xden_2413 : (fp_t '× fp_t) loc( xden_2413_loc ) := fp2zero  in
      letbm xx_2414 : (fp_t '× fp_t) loc( xx_2414_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(xden_2413, xx_2414) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xden_k_2408)) prod_ce(xden_2413, xx_2414) (L := (
              CEfset (
                [xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc]))) (
            I := [interface]) (fun i_2435 '(xden_2413, xx_2414) =>
            letbm xden_2413 loc( xden_2413_loc ) :=
              fp2add (lift_to_both0 xden_2413) (fp2mul (lift_to_both0 xx_2414) (
                  seq_index (xden_k_2408) (lift_to_both0 i_2435))) in
            letbm xx_2414 loc( xx_2414_loc ) :=
              fp2mul (lift_to_both0 xx_2414) (lift_to_both0 x_2434) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2413,
                lift_to_both0 xx_2414
              ))
            ) in
      letbm xden_2413 loc( xden_2413_loc ) :=
        fp2add (lift_to_both0 xden_2413) (lift_to_both0 xx_2414) in
      letbm ynum_2415 : (fp_t '× fp_t) loc( ynum_2415_loc ) := fp2zero  in
      letbm xx_2416 : (fp_t '× fp_t) loc( xx_2416_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(ynum_2415, xx_2416) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 ynum_k_2409)) prod_ce(ynum_2415, xx_2416) (L := (
              CEfset (
                [xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc]))) (
            I := [interface]) (fun i_2436 '(ynum_2415, xx_2416) =>
            letbm ynum_2415 loc( ynum_2415_loc ) :=
              fp2add (lift_to_both0 ynum_2415) (fp2mul (lift_to_both0 xx_2416) (
                  seq_index (ynum_k_2409) (lift_to_both0 i_2436))) in
            letbm xx_2416 loc( xx_2416_loc ) :=
              fp2mul (lift_to_both0 xx_2416) (lift_to_both0 x_2434) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2415,
                lift_to_both0 xx_2416
              ))
            ) in
      letbm yden_2417 : (fp_t '× fp_t) loc( yden_2417_loc ) := fp2zero  in
      letbm xx_2418 : (fp_t '× fp_t) loc( xx_2418_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(yden_2417, xx_2418) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 yden_k_2410)) prod_ce(yden_2417, xx_2418) (L := (
              CEfset (
                [xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc]))) (
            I := [interface]) (fun i_2437 '(yden_2417, xx_2418) =>
            letbm yden_2417 loc( yden_2417_loc ) :=
              fp2add (lift_to_both0 yden_2417) (fp2mul (lift_to_both0 xx_2418) (
                  seq_index (yden_k_2410) (lift_to_both0 i_2437))) in
            letbm xx_2418 loc( xx_2418_loc ) :=
              fp2mul (lift_to_both0 xx_2418) (lift_to_both0 x_2434) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2417,
                lift_to_both0 xx_2418
              ))
            ) in
      letbm yden_2417 loc( yden_2417_loc ) :=
        fp2add (lift_to_both0 yden_2417) (lift_to_both0 xx_2418) in
      letb xr_2438 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xnum_2411) (fp2inv (lift_to_both0 xden_2413)) in
      letb yr_2440 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 y_2439) (fp2mul (lift_to_both0 ynum_2415) (
            fp2inv (lift_to_both0 yden_2417))) in
      letbm inf_2419 : bool_ChoiceEquality loc( inf_2419_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(inf_2419) :=
        if ((lift_to_both0 xden_2413) =.? (fp2zero )) || ((
            lift_to_both0 yden_2417) =.? (fp2zero )) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) (
          L2 := CEfset (
            [xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm inf_2419 loc( inf_2419_loc ) :=
            lift_to_both0 ((true : bool_ChoiceEquality)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2419)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 inf_2419)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xr_2438,
          lift_to_both0 yr_2440,
          lift_to_both0 inf_2419
        ))
      ) : both (CEfset (
        [xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_map_to_curve_sswu_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_MAP_TO_CURVE_SSWU : nat :=
  2446.
Program Definition g2_map_to_curve_sswu (u_2442 : fp2_t)
  : both (CEfset (
      [c_2251_loc ; x1_2393_loc ; y_2394_loc ; xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) [interface] (
    g2_t) :=
  ((letb '(xp_2443, yp_2444) : (fp2_t '× fp2_t) :=
        g2_simple_swu_iso (lift_to_both0 u_2442) in
      letb p_2445 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_isogeny_map (lift_to_both0 xp_2443) (lift_to_both0 yp_2444) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2445)
      ) : both (CEfset (
        [c_2251_loc ; x1_2393_loc ; y_2394_loc ; xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_hash_to_curve_sswu_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_HASH_TO_CURVE_SSWU : nat :=
  2454.
Program Definition g2_hash_to_curve_sswu (msg_2447 : byte_seq) (
    dst_2448 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc ; c_2251_loc ; x1_2393_loc ; y_2394_loc ; xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) [interface] (
    g2_t) :=
  ((letb u_2449 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2447) (lift_to_both0 dst_2448) (
          lift_to_both0 (usize 2)) in
      letb q0_2450 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2449) (lift_to_both0 (usize 0))) in
      letb q1_2451 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2449) (lift_to_both0 (usize 1))) in
      letb r_2452 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 q0_2450) (lift_to_both0 q1_2451) in
      letb p_2453 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 r_2452) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2453)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc ; c_2251_loc ; x1_2393_loc ; y_2394_loc ; xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_encode_to_curve_sswu_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_ENCODE_TO_CURVE_SSWU : nat :=
  2460.
Program Definition g2_encode_to_curve_sswu (msg_2455 : byte_seq) (
    dst_2456 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc ; c_2251_loc ; x1_2393_loc ; y_2394_loc ; xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) [interface] (
    g2_t) :=
  ((letb u_2457 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2455) (lift_to_both0 dst_2456) (
          lift_to_both0 (usize 1)) in
      letb q_2458 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2457) (lift_to_both0 (usize 0))) in
      letb p_2459 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 q_2458) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2459)
      ) : both (CEfset (
        [l_i_b_str_2144_loc ; b_i_2145_loc ; uniform_bytes_2146_loc ; output_2219_loc ; c_2251_loc ; x1_2393_loc ; y_2394_loc ; xnum_k_2407_loc ; xden_k_2408_loc ; ynum_k_2409_loc ; yden_k_2410_loc ; xnum_2411_loc ; xx_2412_loc ; xden_2413_loc ; xx_2414_loc ; ynum_2415_loc ; xx_2416_loc ; yden_2417_loc ; xx_2418_loc ; inf_2419_loc])) [interface] (
      g2_t)).
Fail Next Obligation.

