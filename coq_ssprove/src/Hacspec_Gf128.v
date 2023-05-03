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


Definition blocksize_v : uint_size :=
  usize 16.

Definition gf128_block_t := nseq (uint8) (blocksize_v).

Definition gf128_key_t := nseq (uint8) (blocksize_v).

Definition gf128_tag_t := nseq (uint8) (blocksize_v).

Notation "'element_t'" := (uint128) : hacspec_scope.

Definition irred_v : element_t :=
  secret (@repr U128 299076299051606071403356588563077529600).


Notation "'fadd_inp'" :=(
  element_t × element_t : choice_type) (in custom pack_type at level 2).
Notation "'fadd_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition FADD : nat :=
  211.
Program Definition fadd (x_209 : element_t) (y_210 : element_t)
  : both (fset.fset0) [interface] (element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((lift_to_both0 x_209) .^ (
          lift_to_both0 y_210))
      ) : both (fset.fset0) [interface] (element_t)).
Fail Next Obligation.

Definition res_212_loc : ChoiceEqualityLocation :=
  (element_t ; 214%nat).
Definition sh_213_loc : ChoiceEqualityLocation :=
  (uint128 ; 215%nat).
Notation "'fmul_inp'" :=(
  element_t × element_t : choice_type) (in custom pack_type at level 2).
Notation "'fmul_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition FMUL : nat :=
  219.
Program Definition fmul (x_216 : element_t) (y_218 : element_t)
  : both (CEfset ([res_212_loc ; sh_213_loc])) [interface] (element_t) :=
  ((letbm res_212 : element_t loc( res_212_loc ) :=
        secret (lift_to_both0 (@repr U128 0)) in
      letbm sh_213 : uint128 loc( sh_213_loc ) := lift_to_both0 x_216 in
      letb '(res_212, sh_213) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 128)) prod_ce(res_212, sh_213) (L := (CEfset (
                [res_212_loc ; sh_213_loc]))) (I := [interface]) (fun i_217 '(
              res_212,
              sh_213
            ) =>
            letb '(res_212) :=
              if (uint128_declassify ((lift_to_both0 y_218) .& ((secret (
                        lift_to_both0 (@repr U128 1))) shift_left ((
                        lift_to_both0 (usize 127)) .- (
                        lift_to_both0 i_217))))) !=.? (uint128_declassify (
                  secret (lift_to_both0 (@repr U128 0)))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([res_212_loc ; sh_213_loc])) (
                L2 := CEfset ([res_212_loc ; sh_213_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm res_212 loc( res_212_loc ) :=
                  (lift_to_both0 res_212) .^ (lift_to_both0 sh_213) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 res_212)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 res_212)
               in
            letb '(sh_213) :=
              if (uint128_declassify ((lift_to_both0 sh_213) .& (secret (
                      lift_to_both0 (@repr U128 1))))) !=.? (
                uint128_declassify (secret (lift_to_both0 (
                      @repr U128 0)))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([res_212_loc ; sh_213_loc])) (
                L2 := CEfset ([res_212_loc ; sh_213_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm sh_213 loc( sh_213_loc ) :=
                  ((lift_to_both0 sh_213) shift_right (lift_to_both0 (
                        usize 1))) .^ (lift_to_both0 irred_v) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 sh_213)
                )
              else  lift_scope (L1 := CEfset ([res_212_loc ; sh_213_loc])) (
                L2 := CEfset ([res_212_loc ; sh_213_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm sh_213 loc( sh_213_loc ) :=
                  (lift_to_both0 sh_213) shift_right (lift_to_both0 (
                      usize 1)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 sh_213)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 res_212,
                lift_to_both0 sh_213
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_212)
      ) : both (CEfset ([res_212_loc ; sh_213_loc])) [interface] (element_t)).
Fail Next Obligation.


Notation "'encode_inp'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE : nat :=
  221.
Program Definition encode (block_220 : gf128_block_t)
  : both (fset.fset0) [interface] (element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (uint128_from_be_bytes (
          array_from_seq (16) (array_to_seq (lift_to_both0 block_220))))
      ) : both (fset.fset0) [interface] (element_t)).
Fail Next Obligation.


Notation "'decode_inp'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Definition DECODE : nat :=
  223.
Program Definition decode (e_222 : element_t)
  : both (fset.fset0) [interface] (gf128_block_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          blocksize_v) (array_to_seq (uint128_to_be_bytes (
            lift_to_both0 e_222))))
      ) : both (fset.fset0) [interface] (gf128_block_t)).
Fail Next Obligation.


Notation "'update_inp'" :=(
  element_t × gf128_block_t × element_t : choice_type) (in custom pack_type at level 2).
Notation "'update_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition UPDATE : nat :=
  227.
Program Definition update (r_226 : element_t) (block_224 : gf128_block_t) (
    acc_225 : element_t)
  : both (CEfset ([res_212_loc ; sh_213_loc])) [interface] (element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fmul (fadd (encode (
              lift_to_both0 block_224)) (lift_to_both0 acc_225)) (
          lift_to_both0 r_226))
      ) : both (CEfset ([res_212_loc ; sh_213_loc])) [interface] (element_t)).
Fail Next Obligation.

Definition last_block_230_loc : ChoiceEqualityLocation :=
  (gf128_block_t ; 231%nat).
Definition block_229_loc : ChoiceEqualityLocation :=
  (gf128_block_t ; 232%nat).
Definition acc_228_loc : ChoiceEqualityLocation :=
  (uint128 ; 233%nat).
Notation "'poly_inp'" :=(
  byte_seq × element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition POLY : nat :=
  242.
Program Definition poly (msg_234 : byte_seq) (r_240 : element_t)
  : both (CEfset (
      [res_212_loc ; sh_213_loc ; acc_228_loc ; block_229_loc ; last_block_230_loc])) [interface] (
    element_t) :=
  ((letb l_235 : uint_size := seq_len (lift_to_both0 msg_234) in
      letb n_blocks_236 : uint_size :=
        (lift_to_both0 l_235) ./ (lift_to_both0 blocksize_v) in
      letb rem_237 : uint_size :=
        (lift_to_both0 l_235) .% (lift_to_both0 blocksize_v) in
      letbm acc_228 : uint128 loc( acc_228_loc ) :=
        secret (lift_to_both0 (@repr U128 0)) in
      letb acc_228 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 n_blocks_236) acc_228 (L := (CEfset (
                [res_212_loc ; sh_213_loc ; acc_228_loc ; block_229_loc ; last_block_230_loc]))) (
            I := [interface]) (fun i_238 acc_228 =>
            letb k_239 : uint_size :=
              (lift_to_both0 i_238) .* (lift_to_both0 blocksize_v) in
            letbm block_229 : gf128_block_t loc( block_229_loc ) :=
              array_new_ (default : uint8) (blocksize_v) in
            letbm block_229 loc( block_229_loc ) :=
              array_update_start (lift_to_both0 block_229) (seq_slice_range (
                  lift_to_both0 msg_234) (prod_b(
                    lift_to_both0 k_239,
                    (lift_to_both0 k_239) .+ (lift_to_both0 blocksize_v)
                  ))) in
            letbm acc_228 loc( acc_228_loc ) :=
              update (lift_to_both0 r_240) (lift_to_both0 block_229) (
                lift_to_both0 acc_228) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 acc_228)
            ) in
      letb '(acc_228) :=
        if (lift_to_both0 rem_237) !=.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [res_212_loc ; sh_213_loc ; acc_228_loc ; block_229_loc ; last_block_230_loc])) (
          L2 := CEfset (
            [res_212_loc ; sh_213_loc ; acc_228_loc ; block_229_loc ; last_block_230_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb k_241 : uint_size :=
            (lift_to_both0 n_blocks_236) .* (lift_to_both0 blocksize_v) in
          letbm last_block_230 : gf128_block_t loc( last_block_230_loc ) :=
            array_new_ (default : uint8) (blocksize_v) in
          letbm last_block_230 loc( last_block_230_loc ) :=
            array_update_slice (lift_to_both0 last_block_230) (lift_to_both0 (
                usize 0)) (lift_to_both0 msg_234) (lift_to_both0 k_241) (
              lift_to_both0 rem_237) in
          letbm acc_228 loc( acc_228_loc ) :=
            update (lift_to_both0 r_240) (lift_to_both0 last_block_230) (
              lift_to_both0 acc_228) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 acc_228)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 acc_228)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 acc_228)
      ) : both (CEfset (
        [res_212_loc ; sh_213_loc ; acc_228_loc ; block_229_loc ; last_block_230_loc])) [interface] (
      element_t)).
Fail Next Obligation.


Notation "'gmac_inp'" :=(
  byte_seq × gf128_key_t : choice_type) (in custom pack_type at level 2).
Notation "'gmac_out'" :=(
  gf128_tag_t : choice_type) (in custom pack_type at level 2).
Definition GMAC : nat :=
  248.
Program Definition gmac (text_246 : byte_seq) (k_244 : gf128_key_t)
  : both (CEfset (
      [res_212_loc ; sh_213_loc ; acc_228_loc ; block_229_loc ; last_block_230_loc])) [interface] (
    gf128_tag_t) :=
  ((letb s_243 : gf128_block_t := array_new_ (default : uint8) (blocksize_v) in
      letb r_245 : uint128 :=
        encode (array_from_seq (blocksize_v) (
            array_to_seq (lift_to_both0 k_244))) in
      letb a_247 : uint128 :=
        poly (lift_to_both0 text_246) (lift_to_both0 r_245) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          blocksize_v) (array_to_seq (decode (fadd (lift_to_both0 a_247) (
              encode (lift_to_both0 s_243))))))
      ) : both (CEfset (
        [res_212_loc ; sh_213_loc ; acc_228_loc ; block_229_loc ; last_block_230_loc])) [interface] (
      gf128_tag_t)).
Fail Next Obligation.

