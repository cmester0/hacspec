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


Definition rounds_v : uint_size :=
  usize 24.

Definition sha3224_rate_v : uint_size :=
  usize 144.

Definition sha3256_rate_v : uint_size :=
  usize 136.

Definition sha3384_rate_v : uint_size :=
  usize 104.

Definition sha3512_rate_v : uint_size :=
  usize 72.

Definition shake128_rate_v : uint_size :=
  usize 168.

Definition shake256_rate_v : uint_size :=
  usize 136.

Definition state_t := nseq (uint64) (usize 25).

Definition row_t := nseq (uint64) (usize 5).

Definition digest224_t := nseq (uint8) (usize 28).

Definition digest256_t := nseq (uint8) (usize 32).

Definition digest384_t := nseq (uint8) (usize 48).

Definition digest512_t := nseq (uint8) (usize 64).

Definition round_constants_t := nseq (int64) (rounds_v).

Definition rotation_constants_t := nseq (uint_size) (usize 25).

Definition roundconstants_v : round_constants_t :=
  @array_from_list int64 [
    (@repr U64 1) : int64;
    (@repr U64 32898) : int64;
    (@repr U64 9223372036854808714) : int64;
    (@repr U64 9223372039002292224) : int64;
    (@repr U64 32907) : int64;
    (@repr U64 2147483649) : int64;
    (@repr U64 9223372039002292353) : int64;
    (@repr U64 9223372036854808585) : int64;
    (@repr U64 138) : int64;
    (@repr U64 136) : int64;
    (@repr U64 2147516425) : int64;
    (@repr U64 2147483658) : int64;
    (@repr U64 2147516555) : int64;
    (@repr U64 9223372036854775947) : int64;
    (@repr U64 9223372036854808713) : int64;
    (@repr U64 9223372036854808579) : int64;
    (@repr U64 9223372036854808578) : int64;
    (@repr U64 9223372036854775936) : int64;
    (@repr U64 32778) : int64;
    (@repr U64 9223372039002259466) : int64;
    (@repr U64 9223372039002292353) : int64;
    (@repr U64 9223372036854808704) : int64;
    (@repr U64 2147483649) : int64;
    (@repr U64 9223372039002292232) : int64
  ].

Definition rotc_v : rotation_constants_t :=
  @array_from_list uint_size [
    (usize 0) : uint_size;
    (usize 1) : uint_size;
    (usize 62) : uint_size;
    (usize 28) : uint_size;
    (usize 27) : uint_size;
    (usize 36) : uint_size;
    (usize 44) : uint_size;
    (usize 6) : uint_size;
    (usize 55) : uint_size;
    (usize 20) : uint_size;
    (usize 3) : uint_size;
    (usize 10) : uint_size;
    (usize 43) : uint_size;
    (usize 25) : uint_size;
    (usize 39) : uint_size;
    (usize 41) : uint_size;
    (usize 45) : uint_size;
    (usize 15) : uint_size;
    (usize 21) : uint_size;
    (usize 8) : uint_size;
    (usize 18) : uint_size;
    (usize 2) : uint_size;
    (usize 61) : uint_size;
    (usize 56) : uint_size;
    (usize 14) : uint_size
  ].

Definition pi_v : rotation_constants_t :=
  @array_from_list uint_size [
    (usize 0) : uint_size;
    (usize 6) : uint_size;
    (usize 12) : uint_size;
    (usize 18) : uint_size;
    (usize 24) : uint_size;
    (usize 3) : uint_size;
    (usize 9) : uint_size;
    (usize 10) : uint_size;
    (usize 16) : uint_size;
    (usize 22) : uint_size;
    (usize 1) : uint_size;
    (usize 7) : uint_size;
    (usize 13) : uint_size;
    (usize 19) : uint_size;
    (usize 20) : uint_size;
    (usize 4) : uint_size;
    (usize 5) : uint_size;
    (usize 11) : uint_size;
    (usize 17) : uint_size;
    (usize 23) : uint_size;
    (usize 2) : uint_size;
    (usize 8) : uint_size;
    (usize 14) : uint_size;
    (usize 15) : uint_size;
    (usize 21) : uint_size
  ].

Definition b_1183_loc : ChoiceEqualityLocation :=
  (row_t ; 1184%nat).
Notation "'theta_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'theta_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition THETA : nat :=
  1191.
Program Definition theta (s_1186 : state_t)
  : both (CEfset ([b_1183_loc])) [interface] (state_t) :=
  ((letbm b_1183 : row_t loc( b_1183_loc ) :=
        array_new_ (default : uint64) (5) in
      letb b_1183 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 5)) b_1183 (
            L := (CEfset ([b_1183_loc]))) (I := [interface]) (
            fun i_1185 b_1183 =>
            letb b_1183 : row_t :=
              array_upd b_1183 (lift_to_both0 i_1185) (is_pure (((((
                          array_index (s_1186) (lift_to_both0 i_1185)) .^ (
                          array_index (s_1186) ((lift_to_both0 i_1185) .+ (
                              lift_to_both0 (usize 5))))) .^ (array_index (
                          s_1186) ((lift_to_both0 i_1185) .+ (lift_to_both0 (
                              usize 10))))) .^ (array_index (s_1186) ((
                          lift_to_both0 i_1185) .+ (lift_to_both0 (
                            usize 15))))) .^ (array_index (s_1186) ((
                        lift_to_both0 i_1185) .+ (lift_to_both0 (
                          usize 20)))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 b_1183)
            ) in
      letb s_1186 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 5)) s_1186 (
            L := (CEfset ([b_1183_loc]))) (I := [interface]) (
            fun i_1187 s_1186 =>
            letb u_1188 : uint64 :=
              array_index (b_1183) (((lift_to_both0 i_1187) .+ (lift_to_both0 (
                      usize 1))) .% (lift_to_both0 (usize 5))) in
            letb t_1189 : uint64 :=
              (array_index (b_1183) (((lift_to_both0 i_1187) .+ (lift_to_both0 (
                        usize 4))) .% (lift_to_both0 (usize 5)))) .^ (
                uint64_rotate_left (lift_to_both0 u_1188) (lift_to_both0 (
                    usize 1))) in
            letb s_1186 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 5)) s_1186 (L := (CEfset ([b_1183_loc]))) (
                  I := [interface]) (fun j_1190 s_1186 =>
                  letb s_1186 : state_t :=
                    array_upd s_1186 (((lift_to_both0 (usize 5)) .* (
                          lift_to_both0 j_1190)) .+ (lift_to_both0 i_1187)) (
                      is_pure ((array_index (s_1186) (((lift_to_both0 (
                                  usize 5)) .* (lift_to_both0 j_1190)) .+ (
                              lift_to_both0 i_1187))) .^ (
                          lift_to_both0 t_1189))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 s_1186)
                  ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1186)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1186)
      ) : both (CEfset ([b_1183_loc])) [interface] (state_t)).
Fail Next Obligation.


Notation "'rho_inp'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'rho_out'" :=(state_t : choice_type) (in custom pack_type at level 2).
Definition RHO : nat :=
  1195.
Program Definition rho (s_1192 : state_t)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb s_1192 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 25)) s_1192 (L := (fset.fset0)) (I := [interface]) (
            fun i_1193 s_1192 =>
            letb u_1194 : uint64 :=
              array_index (s_1192) (lift_to_both0 i_1193) in
            letb s_1192 : state_t :=
              array_upd s_1192 (lift_to_both0 i_1193) (is_pure (
                  uint64_rotate_left (lift_to_both0 u_1194) (array_index (
                      rotc_v) (lift_to_both0 i_1193)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1192)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1192)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.

Definition v_1196_loc : ChoiceEqualityLocation :=
  (state_t ; 1197%nat).
Notation "'pi_inp'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'pi_out'" :=(state_t : choice_type) (in custom pack_type at level 2).
Definition PI : nat :=
  1200.
Program Definition pi (s_1199 : state_t)
  : both (CEfset ([v_1196_loc])) [interface] (state_t) :=
  ((letbm v_1196 : state_t loc( v_1196_loc ) :=
        array_new_ (default : uint64) (25) in
      letb v_1196 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 25)) v_1196 (L := (CEfset ([v_1196_loc]))) (
            I := [interface]) (fun i_1198 v_1196 =>
            letb v_1196 : state_t :=
              array_upd v_1196 (lift_to_both0 i_1198) (is_pure (array_index (
                    s_1199) (array_index (pi_v) (lift_to_both0 i_1198)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 v_1196)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 v_1196)
      ) : both (CEfset ([v_1196_loc])) [interface] (state_t)).
Fail Next Obligation.

Definition b_1201_loc : ChoiceEqualityLocation :=
  (row_t ; 1202%nat).
Notation "'chi_inp'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'chi_out'" :=(state_t : choice_type) (in custom pack_type at level 2).
Definition CHI : nat :=
  1208.
Program Definition chi (s_1203 : state_t)
  : both (CEfset ([b_1201_loc])) [interface] (state_t) :=
  ((letbm b_1201 : row_t loc( b_1201_loc ) :=
        array_new_ (default : uint64) (5) in
      letb '(s_1203, b_1201) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 5)) prod_ce(
            s_1203,
            b_1201
          ) (L := (CEfset ([b_1201_loc]))) (I := [interface]) (fun i_1204 '(
              s_1203,
              b_1201
            ) =>
            letb b_1201 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 5)) b_1201 (L := (CEfset ([b_1201_loc]))) (
                  I := [interface]) (fun j_1205 b_1201 =>
                  letb b_1201 : row_t :=
                    array_upd b_1201 (lift_to_both0 j_1205) (is_pure (
                        array_index (s_1203) (((lift_to_both0 (usize 5)) .* (
                              lift_to_both0 i_1204)) .+ (
                            lift_to_both0 j_1205)))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 b_1201)
                  ) in
            letb s_1203 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 5)) s_1203 (L := (CEfset ([b_1201_loc]))) (
                  I := [interface]) (fun j_1206 s_1203 =>
                  letb u_1207 : uint64 :=
                    array_index (b_1201) (((lift_to_both0 j_1206) .+ (
                          lift_to_both0 (usize 1))) .% (lift_to_both0 (
                          usize 5))) in
                  letb s_1203 : state_t :=
                    array_upd s_1203 (((lift_to_both0 (usize 5)) .* (
                          lift_to_both0 i_1204)) .+ (lift_to_both0 j_1206)) (
                      is_pure ((array_index (s_1203) (((lift_to_both0 (
                                  usize 5)) .* (lift_to_both0 i_1204)) .+ (
                              lift_to_both0 j_1206))) .^ ((not (
                              lift_to_both0 u_1207)) .& (array_index (b_1201) ((
                                (lift_to_both0 j_1206) .+ (lift_to_both0 (
                                    usize 2))) .% (lift_to_both0 (
                                  usize 5))))))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 s_1203)
                  ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1203,
                lift_to_both0 b_1201
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1203)
      ) : both (CEfset ([b_1201_loc])) [interface] (state_t)).
Fail Next Obligation.


Notation "'iota_inp'" :=(
  state_t × int64 : choice_type) (in custom pack_type at level 2).
Notation "'iota_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition IOTA : nat :=
  1211.
Program Definition iota (s_1209 : state_t) (rndconst_1210 : int64)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb s_1209 : state_t :=
        array_upd s_1209 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                s_1209) (lift_to_both0 (usize 0))) .^ (uint64_classify (
                lift_to_both0 rndconst_1210)))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1209)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.


Notation "'keccakf1600_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'keccakf1600_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition KECCAKF1600 : nat :=
  1214.
Program Definition keccakf1600 (s_1212 : state_t)
  : both (CEfset ([b_1183_loc ; v_1196_loc ; b_1201_loc])) [interface] (
    state_t) :=
  ((letb s_1212 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 rounds_v) s_1212 (
            L := (CEfset ([b_1183_loc ; v_1196_loc ; b_1201_loc]))) (
            I := [interface]) (fun i_1213 s_1212 =>
            letbm s_1212 loc( s_1212_loc ) := theta (lift_to_both0 s_1212) in
            letbm s_1212 loc( s_1212_loc ) := rho (lift_to_both0 s_1212) in
            letbm s_1212 loc( s_1212_loc ) := pi (lift_to_both0 s_1212) in
            letbm s_1212 loc( s_1212_loc ) := chi (lift_to_both0 s_1212) in
            letbm s_1212 loc( s_1212_loc ) :=
              iota (lift_to_both0 s_1212) (array_index (roundconstants_v) (
                  lift_to_both0 i_1213)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1212)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1212)
      ) : both (CEfset ([b_1183_loc ; v_1196_loc ; b_1201_loc])) [interface] (
      state_t)).
Fail Next Obligation.


Notation "'absorb_block_inp'" :=(
  state_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition ABSORB_BLOCK : nat :=
  1220.
Program Definition absorb_block (s_1216 : state_t) (block_1215 : byte_seq)
  : both (CEfset ([b_1183_loc ; v_1196_loc ; b_1201_loc])) [interface] (
    state_t) :=
  ((letb s_1216 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 block_1215)) s_1216 (L := (CEfset (
                [b_1183_loc ; v_1196_loc ; b_1201_loc]))) (I := [interface]) (
            fun i_1217 s_1216 =>
            letb w_1218 : uint_size :=
              (lift_to_both0 i_1217) usize_shift_right (lift_to_both0 (
                  @repr U32 3)) in
            letb o_1219 : uint_size :=
              (lift_to_both0 (usize 8)) .* ((lift_to_both0 i_1217) .& (
                  lift_to_both0 (usize 7))) in
            letb s_1216 : state_t :=
              array_upd s_1216 (lift_to_both0 w_1218) (is_pure ((array_index (
                      s_1216) (lift_to_both0 w_1218)) .^ ((uint64_from_uint8 (
                        seq_index (block_1215) (
                          lift_to_both0 i_1217))) shift_left (
                      lift_to_both0 o_1219)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1216)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (keccakf1600 (
          lift_to_both0 s_1216))
      ) : both (CEfset ([b_1183_loc ; v_1196_loc ; b_1201_loc])) [interface] (
      state_t)).
Fail Next Obligation.

Definition out_1221_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1222%nat).
Notation "'squeeze_inp'" :=(
  state_t × uint_size × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition SQUEEZE : nat :=
  1231.
Program Definition squeeze (s_1224 : state_t) (nbytes_1223 : uint_size) (
    rate_1226 : uint_size)
  : both (CEfset (
      [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc])) [interface] (
    byte_seq) :=
  ((letbm out_1221 : seq uint8 loc( out_1221_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 nbytes_1223) in
      letb '(s_1224, out_1221) :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 nbytes_1223) prod_ce(s_1224, out_1221) (L := (CEfset (
                [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc]))) (
            I := [interface]) (fun i_1225 '(s_1224, out_1221) =>
            letb pos_1227 : uint_size :=
              (lift_to_both0 i_1225) .% (lift_to_both0 rate_1226) in
            letb w_1228 : uint_size :=
              (lift_to_both0 pos_1227) usize_shift_right (lift_to_both0 (
                  @repr U32 3)) in
            letb o_1229 : uint_size :=
              (lift_to_both0 (usize 8)) .* ((lift_to_both0 pos_1227) .& (
                  lift_to_both0 (usize 7))) in
            letb b_1230 : uint64 :=
              ((array_index (s_1224) (lift_to_both0 w_1228)) shift_right (
                  lift_to_both0 o_1229)) .& (uint64_classify (lift_to_both0 (
                    @repr U64 255))) in
            letb out_1221 : seq uint8 :=
              seq_upd out_1221 (lift_to_both0 i_1225) (is_pure (
                  uint8_from_uint64 (lift_to_both0 b_1230))) in
            letb '(s_1224) :=
              if (((lift_to_both0 i_1225) .+ (lift_to_both0 (usize 1))) .% (
                  lift_to_both0 rate_1226)) =.? (lift_to_both0 (
                  usize 0)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc])) (
                L2 := CEfset (
                  [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm s_1224 loc( s_1224_loc ) :=
                  keccakf1600 (lift_to_both0 s_1224) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_1224)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 s_1224)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1224,
                lift_to_both0 out_1221
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_1221)
      ) : both (CEfset (
        [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

Definition last_block_len_1233_loc : ChoiceEqualityLocation :=
  (uint_size ; 1235%nat).
Definition buf_1232_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1236%nat).
Definition s_1234_loc : ChoiceEqualityLocation :=
  (state_t ; 1237%nat).
Notation "'keccak_inp'" :=(
  uint_size × byte_seq × int8 × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'keccak_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition KECCAK : nat :=
  1245.
Program Definition keccak (rate_1238 : uint_size) (data_1239 : byte_seq) (
    p_1243 : int8) (outbytes_1244 : uint_size)
  : both (CEfset (
      [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
    byte_seq) :=
  ((letbm buf_1232 : seq uint8 loc( buf_1232_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 rate_1238) in
      letbm last_block_len_1233 : uint_size loc( last_block_len_1233_loc ) :=
        lift_to_both0 (usize 0) in
      letbm s_1234 : state_t loc( s_1234_loc ) :=
        array_new_ (default : uint64) (25) in
      letb '(buf_1232, last_block_len_1233, s_1234) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
              lift_to_both0 data_1239) (lift_to_both0 rate_1238)) prod_ce(
            buf_1232,
            last_block_len_1233,
            s_1234
          ) (L := (CEfset (
                [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc]))) (
            I := [interface]) (fun i_1240 '(
              buf_1232,
              last_block_len_1233,
              s_1234
            ) =>
            letb '(block_len_1241, block_1242) : (uint_size '× seq uint8) :=
              seq_get_chunk (lift_to_both0 data_1239) (
                lift_to_both0 rate_1238) (lift_to_both0 i_1240) in
            letb '(buf_1232, last_block_len_1233, s_1234) :=
              if (lift_to_both0 block_len_1241) =.? (
                lift_to_both0 rate_1238) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [b_1183_loc ; v_1196_loc ; b_1201_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) (
                L2 := CEfset (
                  [b_1183_loc ; v_1196_loc ; b_1201_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm s_1234 loc( s_1234_loc ) :=
                  absorb_block (lift_to_both0 s_1234) (
                    lift_to_both0 block_1242) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 buf_1232,
                    lift_to_both0 last_block_len_1233,
                    lift_to_both0 s_1234
                  ))
                )
              else  lift_scope (L1 := CEfset (
                  [buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) (
                L2 := CEfset (
                  [b_1183_loc ; v_1196_loc ; b_1201_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm buf_1232 loc( buf_1232_loc ) :=
                  seq_update_start (lift_to_both0 buf_1232) (
                    lift_to_both0 block_1242) in
                letbm last_block_len_1233 loc( last_block_len_1233_loc ) :=
                  lift_to_both0 block_len_1241 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 buf_1232,
                    lift_to_both0 last_block_len_1233,
                    lift_to_both0 s_1234
                  ))
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 buf_1232,
                lift_to_both0 last_block_len_1233,
                lift_to_both0 s_1234
              ))
            ) in
      letb buf_1232 : seq uint8 :=
        seq_upd buf_1232 (lift_to_both0 last_block_len_1233) (is_pure (secret (
              lift_to_both0 p_1243))) in
      letb buf_1232 : seq uint8 :=
        seq_upd buf_1232 ((lift_to_both0 rate_1238) .- (lift_to_both0 (
              usize 1))) (is_pure ((seq_index (buf_1232) ((
                  lift_to_both0 rate_1238) .- (lift_to_both0 (usize 1)))) .| (
              secret (lift_to_both0 (@repr U8 128))))) in
      letbm s_1234 loc( s_1234_loc ) :=
        absorb_block (lift_to_both0 s_1234) (lift_to_both0 buf_1232) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (squeeze (
          lift_to_both0 s_1234) (lift_to_both0 outbytes_1244) (
          lift_to_both0 rate_1238))
      ) : both (CEfset (
        [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.


Notation "'sha3224_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3224_out'" :=(
  digest224_t : choice_type) (in custom pack_type at level 2).
Definition SHA3224 : nat :=
  1248.
Program Definition sha3224 (data_1246 : byte_seq)
  : both (CEfset (
      [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
    digest224_t) :=
  ((letb t_1247 : seq uint8 :=
        keccak (lift_to_both0 sha3224_rate_v) (lift_to_both0 data_1246) (
          lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 28)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (28) (
          lift_to_both0 t_1247))
      ) : both (CEfset (
        [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
      digest224_t)).
Fail Next Obligation.


Notation "'sha3256_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3256_out'" :=(
  digest256_t : choice_type) (in custom pack_type at level 2).
Definition SHA3256 : nat :=
  1251.
Program Definition sha3256 (data_1249 : byte_seq)
  : both (CEfset (
      [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
    digest256_t) :=
  ((letb t_1250 : seq uint8 :=
        keccak (lift_to_both0 sha3256_rate_v) (lift_to_both0 data_1249) (
          lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          lift_to_both0 t_1250))
      ) : both (CEfset (
        [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
      digest256_t)).
Fail Next Obligation.


Notation "'sha3384_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3384_out'" :=(
  digest384_t : choice_type) (in custom pack_type at level 2).
Definition SHA3384 : nat :=
  1254.
Program Definition sha3384 (data_1252 : byte_seq)
  : both (CEfset (
      [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
    digest384_t) :=
  ((letb t_1253 : seq uint8 :=
        keccak (lift_to_both0 sha3384_rate_v) (lift_to_both0 data_1252) (
          lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 48)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (48) (
          lift_to_both0 t_1253))
      ) : both (CEfset (
        [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
      digest384_t)).
Fail Next Obligation.


Notation "'sha3512_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3512_out'" :=(
  digest512_t : choice_type) (in custom pack_type at level 2).
Definition SHA3512 : nat :=
  1257.
Program Definition sha3512 (data_1255 : byte_seq)
  : both (CEfset (
      [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
    digest512_t) :=
  ((letb t_1256 : seq uint8 :=
        keccak (lift_to_both0 sha3512_rate_v) (lift_to_both0 data_1255) (
          lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 64)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (64) (
          lift_to_both0 t_1256))
      ) : both (CEfset (
        [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
      digest512_t)).
Fail Next Obligation.


Notation "'shake128_inp'" :=(
  byte_seq × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'shake128_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition SHAKE128 : nat :=
  1260.
Program Definition shake128 (data_1258 : byte_seq) (outlen_1259 : uint_size)
  : both (CEfset (
      [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
    byte_seq) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (keccak (
          lift_to_both0 shake128_rate_v) (lift_to_both0 data_1258) (
          lift_to_both0 (@repr U8 31)) (lift_to_both0 outlen_1259))
      ) : both (CEfset (
        [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.


Notation "'shake256_inp'" :=(
  byte_seq × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'shake256_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition SHAKE256 : nat :=
  1263.
Program Definition shake256 (data_1261 : byte_seq) (outlen_1262 : uint_size)
  : both (CEfset (
      [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
    byte_seq) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (keccak (
          lift_to_both0 shake256_rate_v) (lift_to_both0 data_1261) (
          lift_to_both0 (@repr U8 31)) (lift_to_both0 outlen_1262))
      ) : both (CEfset (
        [b_1183_loc ; v_1196_loc ; b_1201_loc ; out_1221_loc ; buf_1232_loc ; last_block_len_1233_loc ; s_1234_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

