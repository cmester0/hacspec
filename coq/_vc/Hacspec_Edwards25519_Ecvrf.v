(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.
Export Hacspec_Lib.

Require Import Hacspec_Edwards25519.
Export Hacspec_Edwards25519.

Require Import Hacspec_Sha512.
Export Hacspec_Sha512.

Require Import Hacspec_Edwards25519_Hash.
Export Hacspec_Edwards25519_Hash.

Inductive errorec_t :=
| FailedVerify : errorec_t
| MessageTooLarge : errorec_t
| InvalidProof : errorec_t
| InvalidPublicKey : errorec_t
| FailedDecompression : errorec_t
| FailedE2C : errorec_t.

Notation "'byte_seq_result_t'" := ((result byte_seq errorec_t)) : hacspec_scope.

Notation "'proof_result_t'" := ((result (ed_point_t '× scalar_t '× scalar_t
  ) errorec_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((
  result ed_point_t errorec_t)) : hacspec_scope.

Definition large_mod_canvas_t := nseq (int8) (32).
Definition large_mod_t :=
  nat_mod 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff.

Definition arr_large_mod_t := nseq (uint64) (usize 4).

Definition q_v : arr_large_mod_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 9223372036854775807) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551597) : int64
      ] in  l).

Definition c_len_v : uint_size :=
  usize 16.

Definition pt_len_v : uint_size :=
  usize 32.

Definition q_len_v : uint_size :=
  usize 32.

Definition int_byte_t := nseq (uint8) (usize 1).

Definition zero_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 0) : int8] in  l).

Definition one_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 1) : int8] in  l).

Definition two_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 2) : int8] in  l).

Definition three_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 3) : int8] in  l).

Definition four_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 4) : int8] in  l).

Definition suite_string_v : int_byte_t :=
  four_v.

Definition dst_t := nseq (uint8) (usize 39).

Definition h2c_suite_id_string_v : dst_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 69) : int8;
        secret (@repr WORDSIZE8 67) : int8;
        secret (@repr WORDSIZE8 86) : int8;
        secret (@repr WORDSIZE8 82) : int8;
        secret (@repr WORDSIZE8 70) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 100) : int8;
        secret (@repr WORDSIZE8 119) : int8;
        secret (@repr WORDSIZE8 97) : int8;
        secret (@repr WORDSIZE8 114) : int8;
        secret (@repr WORDSIZE8 100) : int8;
        secret (@repr WORDSIZE8 115) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 57) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 68) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 72) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 45) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 69) : int8;
        secret (@repr WORDSIZE8 76) : int8;
        secret (@repr WORDSIZE8 76) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 78) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 95) : int8
      ] in  l).

Definition ecvrf_encode_to_curve_try_and_increment
  (encode_to_curve_salt_2307 : byte_seq)
  (alpha_2308 : byte_seq)
  
  : ed_point_result_t :=
  let h_2309 : (option ed_point_t) :=
    @None ed_point_t in 
  let x_2310 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let '(h_2309, x_2310) :=
    foldi (usize 1) (usize 256) (fun ctr_2311 '(h_2309, x_2310) =>
      let '(h_2309, x_2310) :=
        if ((h_2309)) =.? (@None ed_point_t):bool then (
          let ctr_string_2312 : seq uint8 :=
            seq_slice (nat_mod_to_byte_seq_be (x_2310)) (usize 31) (usize 1) in 
          let hash_string_2313 : sha512_digest_t :=
            sha512 (seq_concat (seq_concat (seq_concat (seq_concat (
                      array_concat (suite_string_v) (array_to_seq (one_v))) (
                      encode_to_curve_salt_2307)) (alpha_2308)) (
                  ctr_string_2312)) (array_to_seq (zero_v))) in 
          let h_2309 :=
            decompress (array_from_slice (default : uint8) (32) (
                array_to_seq (hash_string_2313)) (usize 0) (usize 32)) in 
          let x_2310 :=
            (x_2310) +% (nat_mod_one ) in 
          (h_2309, x_2310)) else ((h_2309, x_2310)) in 
      (h_2309, x_2310))
    (h_2309, x_2310) in 
  bind (option_ok_or (h_2309) (FailedE2C)) (fun h_2314 =>
    @Ok ed_point_t errorec_t (point_mul_by_cofactor (h_2314))).


Definition ecvrf_encode_to_curve_h2c_suite
  (encode_to_curve_salt_2315 : byte_seq)
  (alpha_2316 : byte_seq)
  
  : ed_point_result_t :=
  let string_to_be_hashed_2317 : seq uint8 :=
    seq_concat (encode_to_curve_salt_2315) (alpha_2316) in 
  let dst_2318 : seq uint8 :=
    array_concat (h2c_suite_id_string_v) (array_to_seq (suite_string_v)) in 
  let h_2319 : (result (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) error_t) :=
    ed_encode_to_curve (string_to_be_hashed_2317) (dst_2318) in 
  bind (option_ok_or (result_ok (h_2319)) (FailedE2C)) (fun h_2320 =>
    @Ok ed_point_t errorec_t (h_2320)).


Definition ecvrf_nonce_generation
  (sk_2321 : secret_key_t)
  (h_string_2322 : byte_seq)
  
  : scalar_t :=
  let hashed_sk_string_2323 : sha512_digest_t :=
    sha512 (array_to_le_bytes (sk_2321)) in 
  let truncated_hashed_sk_string_2324 : seq uint8 :=
    array_slice (hashed_sk_string_2323) (usize 32) (usize 32) in 
  let k_string_2325 : sha512_digest_t :=
    sha512 (seq_concat (truncated_hashed_sk_string_2324) (h_string_2322)) in 
  let nonce_2326 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (k_string_2325)) : big_scalar_t in 
  let nonceseq_2327 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (nonce_2326)) (usize 0) (usize 32) in 
  nat_mod_from_byte_seq_le (nonceseq_2327) : scalar_t.


Definition ecvrf_challenge_generation
  (p1_2328 : ed_point_t)
  (p2_2329 : ed_point_t)
  (p3_2330 : ed_point_t)
  (p4_2331 : ed_point_t)
  (p5_2332 : ed_point_t)
  
  : scalar_t :=
  let string_2333 : seq uint8 :=
    seq_concat (seq_concat (seq_concat (seq_concat (seq_concat (seq_concat (
                array_concat (suite_string_v) (array_to_seq (two_v))) (encode (
                  p1_2328))) (encode (p2_2329))) (encode (p3_2330))) (encode (
            p4_2331))) (encode (p5_2332))) (array_to_seq (zero_v)) in 
  let c_string_2334 : sha512_digest_t :=
    sha512 (string_2333) in 
  let truncated_c_string_2335 : seq uint8 :=
    seq_concat (array_slice (c_string_2334) (usize 0) (c_len_v)) (seq_new_ (
        default : uint8) (usize 16)) in 
  nat_mod_from_byte_seq_le (truncated_c_string_2335) : scalar_t.


Definition ecvrf_decode_proof (pi_2336 : byte_seq)  : proof_result_t :=
  let gamma_string_2337 : seq uint8 :=
    seq_slice (pi_2336) (usize 0) (pt_len_v) in 
  let c_string_2338 : seq uint8 :=
    seq_slice (pi_2336) (pt_len_v) (c_len_v) in 
  let s_string_2339 : seq uint8 :=
    seq_slice (pi_2336) ((pt_len_v) + (c_len_v)) (q_len_v) in 
  bind (option_ok_or (decompress (array_from_slice (default : uint8) (32) (
          gamma_string_2337) (usize 0) (usize 32))) (InvalidProof)) (
    fun gamma_2340 => let c_2341 : scalar_t :=
      nat_mod_from_byte_seq_le (seq_concat (c_string_2338) (seq_new_ (
            default : uint8) (usize 16))) : scalar_t in 
    let s_2342 : scalar_t :=
      nat_mod_from_byte_seq_le ((s_string_2339)) : scalar_t in 
    let s_test_2343 : large_mod_t :=
      nat_mod_from_byte_seq_le (s_string_2339) : large_mod_t in 
    let q_2344 : large_mod_t :=
      nat_mod_from_byte_seq_be (array_to_be_bytes (q_v)) : large_mod_t in 
    (if ((s_test_2343) >=.? (q_2344)):bool then (@Err (
          ed_point_t '×
          scalar_t '×
          scalar_t
        ) errorec_t (InvalidProof)) else (@Ok (
          ed_point_t '×
          scalar_t '×
          scalar_t
        ) errorec_t ((gamma_2340, c_2341, s_2342))))).


Definition ecvrf_validate_key
  (y_2345 : public_key_t)
  
  : (result unit errorec_t) :=
  bind (option_ok_or (decompress (y_2345)) (InvalidPublicKey)) (fun y_2346 =>
    let y_prime_2347 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (y_2346) in 
    (if ((y_prime_2347) =.? (point_identity )):bool then (@Err unit errorec_t (
          InvalidPublicKey)) else (@Ok unit errorec_t (tt)))).


Definition ecvrf_prove
  (sk_2348 : secret_key_t)
  (alpha_2349 : byte_seq)
  
  : byte_seq_result_t :=
  bind (option_ok_or (decompress (base_v)) (FailedDecompression)) (fun b_2350 =>
    let '(x_2351, _) :=
      secret_expand (sk_2348) in 
    let x_2352 : scalar_t :=
      nat_mod_from_byte_seq_le (array_to_seq (x_2351)) : scalar_t in 
    let y_2353 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (x_2352) (b_2350) in 
    let pk_2354 : compressed_ed_point_t :=
      compress (y_2353) in 
    let encode_to_curve_salt_2355 : seq uint8 :=
      array_slice (pk_2354) (usize 0) (usize 32) in 
    bind (ecvrf_encode_to_curve_h2c_suite (encode_to_curve_salt_2355) (
        alpha_2349)) (fun h_2356 => let h_string_2357 : seq uint8 :=
        encode (h_2356) in 
      let gamma_2358 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (x_2352) (h_2356) in 
      let k_2359 : scalar_t :=
        ecvrf_nonce_generation (sk_2348) (h_string_2357) in 
      let u_2360 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (k_2359) (b_2350) in 
      let v_2361 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (k_2359) (h_2356) in 
      let c_2362 : scalar_t :=
        ecvrf_challenge_generation (y_2353) (h_2356) (gamma_2358) (u_2360) (
          v_2361) in 
      let s_2363 : scalar_t :=
        (k_2359) +% ((c_2362) *% (x_2352)) in 
      @Ok byte_seq errorec_t (seq_slice (seq_concat (seq_concat (encode (
                gamma_2358)) (seq_slice (nat_mod_to_byte_seq_le (c_2362)) (
                usize 0) (c_len_v))) (seq_slice (nat_mod_to_byte_seq_le (
                s_2363)) (usize 0) (q_len_v))) (usize 0) (((c_len_v) + (
              q_len_v)) + (pt_len_v))))).


Definition ecvrf_proof_to_hash (pi_2364 : byte_seq)  : byte_seq_result_t :=
  bind (ecvrf_decode_proof (pi_2364)) (fun '(gamma_2365, _, _) =>
    @Ok byte_seq errorec_t (array_slice (sha512 (seq_concat (seq_concat (
              array_concat (suite_string_v) (array_to_seq (three_v))) (encode (
                point_mul_by_cofactor (gamma_2365)))) (
            array_to_seq (zero_v)))) (usize 0) (usize 64))).


Definition ecvrf_verify
  (pk_2366 : public_key_t)
  (alpha_2367 : byte_seq)
  (pi_2368 : byte_seq)
  (validate_key_2369 : bool)
  
  : byte_seq_result_t :=
  bind (option_ok_or (decompress (base_v)) (FailedDecompression)) (fun b_2370 =>
    bind (option_ok_or (decompress (pk_2366)) (InvalidPublicKey)) (fun y_2371 =>
      ifbnd validate_key_2369 : bool
      thenbnd (bind (ecvrf_validate_key (pk_2366)) (fun _ =>
          @Ok unit errorec_t (tt)))
      else (tt) >> (fun 'tt =>
      bind (ecvrf_decode_proof (pi_2368)) (fun '(gamma_2372, c_2373, s_2374) =>
        let encode_to_curve_salt_2375 : seq uint8 :=
          array_slice (pk_2366) (usize 0) (usize 32) in 
        bind (ecvrf_encode_to_curve_h2c_suite (encode_to_curve_salt_2375) (
            alpha_2367)) (fun h_2376 => let u_2377 : (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ) :=
            point_add (point_mul (s_2374) (b_2370)) (point_neg (point_mul (
                  c_2373) (y_2371))) in 
          let v_2378 : (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ) :=
            point_add (point_mul (s_2374) (h_2376)) (point_neg (point_mul (
                  c_2373) (gamma_2372))) in 
          let c_prime_2379 : scalar_t :=
            ecvrf_challenge_generation (y_2371) (h_2376) (gamma_2372) (u_2377) (
              v_2378) in 
          (if ((c_2373) =.? (c_prime_2379)):bool then (ecvrf_proof_to_hash (
                pi_2368)) else (@Err byte_seq errorec_t (FailedVerify)))))))).


