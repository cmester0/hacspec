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
  array_from_list int64 (let l :=
      [
        @repr WORDSIZE64 1;
        @repr WORDSIZE64 32898;
        @repr WORDSIZE64 9223372036854808714;
        @repr WORDSIZE64 9223372039002292224;
        @repr WORDSIZE64 32907;
        @repr WORDSIZE64 2147483649;
        @repr WORDSIZE64 9223372039002292353;
        @repr WORDSIZE64 9223372036854808585;
        @repr WORDSIZE64 138;
        @repr WORDSIZE64 136;
        @repr WORDSIZE64 2147516425;
        @repr WORDSIZE64 2147483658;
        @repr WORDSIZE64 2147516555;
        @repr WORDSIZE64 9223372036854775947;
        @repr WORDSIZE64 9223372036854808713;
        @repr WORDSIZE64 9223372036854808579;
        @repr WORDSIZE64 9223372036854808578;
        @repr WORDSIZE64 9223372036854775936;
        @repr WORDSIZE64 32778;
        @repr WORDSIZE64 9223372039002259466;
        @repr WORDSIZE64 9223372039002292353;
        @repr WORDSIZE64 9223372036854808704;
        @repr WORDSIZE64 2147483649;
        @repr WORDSIZE64 9223372039002292232
      ] in  l).

Definition rotc_v : rotation_constants_t :=
  array_from_list uint_size (let l :=
      [
        usize 0;
        usize 1;
        usize 62;
        usize 28;
        usize 27;
        usize 36;
        usize 44;
        usize 6;
        usize 55;
        usize 20;
        usize 3;
        usize 10;
        usize 43;
        usize 25;
        usize 39;
        usize 41;
        usize 45;
        usize 15;
        usize 21;
        usize 8;
        usize 18;
        usize 2;
        usize 61;
        usize 56;
        usize 14
      ] in  l).

Definition pi_v : rotation_constants_t :=
  array_from_list uint_size (let l :=
      [
        usize 0;
        usize 6;
        usize 12;
        usize 18;
        usize 24;
        usize 3;
        usize 9;
        usize 10;
        usize 16;
        usize 22;
        usize 1;
        usize 7;
        usize 13;
        usize 19;
        usize 20;
        usize 4;
        usize 5;
        usize 11;
        usize 17;
        usize 23;
        usize 2;
        usize 8;
        usize 14;
        usize 15;
        usize 21
      ] in  l).

Definition theta (s_918 : state_t)  : state_t :=
  let b_919 : row_t :=
    array_new_ (default : uint64) (5) in 
  let b_919 :=
    foldi (usize 0) (usize 5) (fun i_920 b_919 =>
      let b_919 :=
        array_upd b_919 (i_920) (((((array_index (s_918) (i_920)) .^ (
                  array_index (s_918) ((i_920) + (usize 5)))) .^ (array_index (
                  s_918) ((i_920) + (usize 10)))) .^ (array_index (s_918) ((
                  i_920) + (usize 15)))) .^ (array_index (s_918) ((i_920) + (
                usize 20)))) in 
      (b_919))
    b_919 in 
  let s_918 :=
    foldi (usize 0) (usize 5) (fun i_921 s_918 =>
      let u_922 : uint64 :=
        array_index (b_919) (((i_921) + (usize 1)) %% (usize 5)) in 
      let t_923 : uint64 :=
        (array_index (b_919) (((i_921) + (usize 4)) %% (usize 5))) .^ (
          uint64_rotate_left (u_922) (usize 1)) in 
      let s_918 :=
        foldi (usize 0) (usize 5) (fun j_924 s_918 =>
          let s_918 :=
            array_upd s_918 (((usize 5) * (j_924)) + (i_921)) ((array_index (
                  s_918) (((usize 5) * (j_924)) + (i_921))) .^ (t_923)) in 
          (s_918))
        s_918 in 
      (s_918))
    s_918 in 
  s_918.


Definition rho (s_925 : state_t)  : state_t :=
  let s_925 :=
    foldi (usize 0) (usize 25) (fun i_926 s_925 =>
      let u_927 : uint64 :=
        array_index (s_925) (i_926) in 
      let s_925 :=
        array_upd s_925 (i_926) (uint64_rotate_left (u_927) (array_index (
              rotc_v) (i_926))) in 
      (s_925))
    s_925 in 
  s_925.


Definition pi (s_928 : state_t)  : state_t :=
  let v_929 : state_t :=
    array_new_ (default : uint64) (25) in 
  let v_929 :=
    foldi (usize 0) (usize 25) (fun i_930 v_929 =>
      let v_929 :=
        array_upd v_929 (i_930) (array_index (s_928) (array_index (pi_v) (
              i_930))) in 
      (v_929))
    v_929 in 
  v_929.


Definition chi (s_931 : state_t)  : state_t :=
  let b_932 : row_t :=
    array_new_ (default : uint64) (5) in 
  let '(s_931, b_932) :=
    foldi (usize 0) (usize 5) (fun i_933 '(s_931, b_932) =>
      let b_932 :=
        foldi (usize 0) (usize 5) (fun j_934 b_932 =>
          let b_932 :=
            array_upd b_932 (j_934) (array_index (s_931) (((usize 5) * (
                    i_933)) + (j_934))) in 
          (b_932))
        b_932 in 
      let s_931 :=
        foldi (usize 0) (usize 5) (fun j_935 s_931 =>
          let u_936 : uint64 :=
            array_index (b_932) (((j_935) + (usize 1)) %% (usize 5)) in 
          let s_931 :=
            array_upd s_931 (((usize 5) * (i_933)) + (j_935)) ((array_index (
                  s_931) (((usize 5) * (i_933)) + (j_935))) .^ ((not (
                    u_936)) .& (array_index (b_932) (((j_935) + (usize 2)) %% (
                      usize 5))))) in 
          (s_931))
        s_931 in 
      (s_931, b_932))
    (s_931, b_932) in 
  s_931.


Definition iota (s_937 : state_t) (rndconst_938 : int64)  : state_t :=
  let s_937 :=
    array_upd s_937 (usize 0) ((array_index (s_937) (usize 0)) .^ (
        uint64_classify (rndconst_938))) in 
  s_937.


Definition keccakf1600 (s_939 : state_t)  : state_t :=
  let s_939 :=
    foldi (usize 0) (rounds_v) (fun i_940 s_939 =>
      let s_939 :=
        theta (s_939) in 
      let s_939 :=
        rho (s_939) in 
      let s_939 :=
        pi (s_939) in 
      let s_939 :=
        chi (s_939) in 
      let s_939 :=
        iota (s_939) (array_index (roundconstants_v) (i_940)) in 
      (s_939))
    s_939 in 
  s_939.


Definition absorb_block (s_941 : state_t) (block_942 : byte_seq)  : state_t :=
  let s_941 :=
    foldi (usize 0) (seq_len (block_942)) (fun i_943 s_941 =>
      let w_944 : uint_size :=
        (i_943) usize_shift_right (@repr WORDSIZE32 (3)) in 
      let o_945 : uint_size :=
        (usize 8) * ((i_943) .& (usize 7)) in 
      let s_941 :=
        array_upd s_941 (w_944) ((array_index (s_941) (w_944)) .^ ((
              uint64_from_uint8 (seq_index (block_942) (i_943))) shift_left (
              o_945))) in 
      (s_941))
    s_941 in 
  keccakf1600 (s_941).


Definition squeeze
  (s_946 : state_t)
  (nbytes_947 : uint_size)
  (rate_948 : uint_size)
  
  : byte_seq :=
  let out_949 : seq uint8 :=
    seq_new_ (default : uint8) (nbytes_947) in 
  let '(s_946, out_949) :=
    foldi (usize 0) (nbytes_947) (fun i_950 '(s_946, out_949) =>
      let pos_951 : uint_size :=
        (i_950) %% (rate_948) in 
      let w_952 : uint_size :=
        (pos_951) usize_shift_right (@repr WORDSIZE32 (3)) in 
      let o_953 : uint_size :=
        (usize 8) * ((pos_951) .& (usize 7)) in 
      let b_954 : uint64 :=
        ((array_index (s_946) (w_952)) shift_right (o_953)) .& (
          uint64_classify (@repr WORDSIZE64 255)) in 
      let out_949 :=
        seq_upd out_949 (i_950) (uint8_from_uint64 (b_954)) in 
      let '(s_946) :=
        if (((i_950) + (usize 1)) %% (rate_948)) =.? (usize 0):bool then (
          let s_946 :=
            keccakf1600 (s_946) in 
          (s_946)) else ((s_946)) in 
      (s_946, out_949))
    (s_946, out_949) in 
  out_949.


Definition keccak
  (rate_955 : uint_size)
  (data_956 : byte_seq)
  (p_957 : int8)
  (outbytes_958 : uint_size)
  
  : byte_seq :=
  let buf_959 : seq uint8 :=
    seq_new_ (default : uint8) (rate_955) in 
  let last_block_len_960 : uint_size :=
    usize 0 in 
  let s_961 : state_t :=
    array_new_ (default : uint64) (25) in 
  let '(buf_959, last_block_len_960, s_961) :=
    foldi (usize 0) (seq_num_chunks (data_956) (rate_955)) (fun i_962 '(
        buf_959,
        last_block_len_960,
        s_961
      ) =>
      let '(block_len_963, block_964) :=
        seq_get_chunk (data_956) (rate_955) (i_962) in 
      let '(buf_959, last_block_len_960, s_961) :=
        if (block_len_963) =.? (rate_955):bool then (let s_961 :=
            absorb_block (s_961) (block_964) in 
          (buf_959, last_block_len_960, s_961)) else (let buf_959 :=
            seq_update_start (buf_959) (block_964) in 
          let last_block_len_960 :=
            block_len_963 in 
          (buf_959, last_block_len_960, s_961)) in 
      (buf_959, last_block_len_960, s_961))
    (buf_959, last_block_len_960, s_961) in 
  let buf_959 :=
    seq_upd buf_959 (last_block_len_960) (secret (p_957) : int8) in 
  let buf_959 :=
    seq_upd buf_959 ((rate_955) - (usize 1)) ((seq_index (buf_959) ((
            rate_955) - (usize 1))) .| (secret (
          @repr WORDSIZE8 128) : int8)) in 
  let s_961 :=
    absorb_block (s_961) (buf_959) in 
  squeeze (s_961) (outbytes_958) (rate_955).


Definition sha3224 (data_965 : byte_seq)  : digest224_t :=
  let t_966 : seq uint8 :=
    keccak (sha3224_rate_v) (data_965) (@repr WORDSIZE8 6) (usize 28) in 
  array_from_seq (28) (t_966).


Definition sha3256 (data_967 : byte_seq)  : digest256_t :=
  let t_968 : seq uint8 :=
    keccak (sha3256_rate_v) (data_967) (@repr WORDSIZE8 6) (usize 32) in 
  array_from_seq (32) (t_968).


Definition sha3384 (data_969 : byte_seq)  : digest384_t :=
  let t_970 : seq uint8 :=
    keccak (sha3384_rate_v) (data_969) (@repr WORDSIZE8 6) (usize 48) in 
  array_from_seq (48) (t_970).


Definition sha3512 (data_971 : byte_seq)  : digest512_t :=
  let t_972 : seq uint8 :=
    keccak (sha3512_rate_v) (data_971) (@repr WORDSIZE8 6) (usize 64) in 
  array_from_seq (64) (t_972).


Definition shake128
  (data_973 : byte_seq)
  (outlen_974 : uint_size)
  
  : byte_seq :=
  keccak (shake128_rate_v) (data_973) (@repr WORDSIZE8 31) (outlen_974).


Definition shake256
  (data_975 : byte_seq)
  (outlen_976 : uint_size)
  
  : byte_seq :=
  keccak (shake256_rate_v) (data_975) (@repr WORDSIZE8 31) (outlen_976).


