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

Definition block_size_v : uint_size :=
  usize 64.

Definition len_size_v : uint_size :=
  usize 8.

Definition k_size_v : uint_size :=
  usize 64.

Definition hash_size_v : uint_size :=
  (usize 256) / (usize 8).

Definition block_t := nseq (uint8) (block_size_v).

Definition op_table_type_t := nseq (uint_size) (usize 12).

Definition sha256_digest_t := nseq (uint8) (hash_size_v).

Definition round_constants_table_t := nseq (uint32) (k_size_v).

Definition hash_t := nseq (uint32) (usize 8).

Definition ch (x_513 : uint32) (y_514 : uint32) (z_515 : uint32)  : uint32 :=
  ((x_513) .& (y_514)) .^ ((not (x_513)) .& (z_515)).


Definition maj (x_516 : uint32) (y_517 : uint32) (z_518 : uint32)  : uint32 :=
  ((x_516) .& (y_517)) .^ (((x_516) .& (z_518)) .^ ((y_517) .& (z_518))).


Definition op_table_v : op_table_type_t :=
  array_from_list uint_size (let l :=
      [
        usize 2;
        usize 13;
        usize 22;
        usize 6;
        usize 11;
        usize 25;
        usize 7;
        usize 18;
        usize 3;
        usize 17;
        usize 19;
        usize 10
      ] in  l).

Definition k_table_v : round_constants_table_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 (1116352408)) : int32;
        secret (@repr WORDSIZE32 (1899447441)) : int32;
        secret (@repr WORDSIZE32 (3049323471)) : int32;
        secret (@repr WORDSIZE32 (3921009573)) : int32;
        secret (@repr WORDSIZE32 (961987163)) : int32;
        secret (@repr WORDSIZE32 (1508970993)) : int32;
        secret (@repr WORDSIZE32 (2453635748)) : int32;
        secret (@repr WORDSIZE32 (2870763221)) : int32;
        secret (@repr WORDSIZE32 (3624381080)) : int32;
        secret (@repr WORDSIZE32 (310598401)) : int32;
        secret (@repr WORDSIZE32 (607225278)) : int32;
        secret (@repr WORDSIZE32 (1426881987)) : int32;
        secret (@repr WORDSIZE32 (1925078388)) : int32;
        secret (@repr WORDSIZE32 (2162078206)) : int32;
        secret (@repr WORDSIZE32 (2614888103)) : int32;
        secret (@repr WORDSIZE32 (3248222580)) : int32;
        secret (@repr WORDSIZE32 (3835390401)) : int32;
        secret (@repr WORDSIZE32 (4022224774)) : int32;
        secret (@repr WORDSIZE32 (264347078)) : int32;
        secret (@repr WORDSIZE32 (604807628)) : int32;
        secret (@repr WORDSIZE32 (770255983)) : int32;
        secret (@repr WORDSIZE32 (1249150122)) : int32;
        secret (@repr WORDSIZE32 (1555081692)) : int32;
        secret (@repr WORDSIZE32 (1996064986)) : int32;
        secret (@repr WORDSIZE32 (2554220882)) : int32;
        secret (@repr WORDSIZE32 (2821834349)) : int32;
        secret (@repr WORDSIZE32 (2952996808)) : int32;
        secret (@repr WORDSIZE32 (3210313671)) : int32;
        secret (@repr WORDSIZE32 (3336571891)) : int32;
        secret (@repr WORDSIZE32 (3584528711)) : int32;
        secret (@repr WORDSIZE32 (113926993)) : int32;
        secret (@repr WORDSIZE32 (338241895)) : int32;
        secret (@repr WORDSIZE32 (666307205)) : int32;
        secret (@repr WORDSIZE32 (773529912)) : int32;
        secret (@repr WORDSIZE32 (1294757372)) : int32;
        secret (@repr WORDSIZE32 (1396182291)) : int32;
        secret (@repr WORDSIZE32 (1695183700)) : int32;
        secret (@repr WORDSIZE32 (1986661051)) : int32;
        secret (@repr WORDSIZE32 (2177026350)) : int32;
        secret (@repr WORDSIZE32 (2456956037)) : int32;
        secret (@repr WORDSIZE32 (2730485921)) : int32;
        secret (@repr WORDSIZE32 (2820302411)) : int32;
        secret (@repr WORDSIZE32 (3259730800)) : int32;
        secret (@repr WORDSIZE32 (3345764771)) : int32;
        secret (@repr WORDSIZE32 (3516065817)) : int32;
        secret (@repr WORDSIZE32 (3600352804)) : int32;
        secret (@repr WORDSIZE32 (4094571909)) : int32;
        secret (@repr WORDSIZE32 (275423344)) : int32;
        secret (@repr WORDSIZE32 (430227734)) : int32;
        secret (@repr WORDSIZE32 (506948616)) : int32;
        secret (@repr WORDSIZE32 (659060556)) : int32;
        secret (@repr WORDSIZE32 (883997877)) : int32;
        secret (@repr WORDSIZE32 (958139571)) : int32;
        secret (@repr WORDSIZE32 (1322822218)) : int32;
        secret (@repr WORDSIZE32 (1537002063)) : int32;
        secret (@repr WORDSIZE32 (1747873779)) : int32;
        secret (@repr WORDSIZE32 (1955562222)) : int32;
        secret (@repr WORDSIZE32 (2024104815)) : int32;
        secret (@repr WORDSIZE32 (2227730452)) : int32;
        secret (@repr WORDSIZE32 (2361852424)) : int32;
        secret (@repr WORDSIZE32 (2428436474)) : int32;
        secret (@repr WORDSIZE32 (2756734187)) : int32;
        secret (@repr WORDSIZE32 (3204031479)) : int32;
        secret (@repr WORDSIZE32 (3329325298)) : int32
      ] in  l).

Definition hash_init_v : hash_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 (1779033703)) : int32;
        secret (@repr WORDSIZE32 (3144134277)) : int32;
        secret (@repr WORDSIZE32 (1013904242)) : int32;
        secret (@repr WORDSIZE32 (2773480762)) : int32;
        secret (@repr WORDSIZE32 (1359893119)) : int32;
        secret (@repr WORDSIZE32 (2600822924)) : int32;
        secret (@repr WORDSIZE32 (528734635)) : int32;
        secret (@repr WORDSIZE32 (1541459225)) : int32
      ] in  l).

Definition sigma
  (x_519 : uint32)
  (i_520 : uint_size)
  (op_521 : uint_size)
  
  : uint32 :=
  let tmp_522 : uint32 :=
    uint32_rotate_right (x_519) (array_index (op_table_v) (((usize 3) * (
            i_520)) + (usize 2))) in 
  let '(tmp_522) :=
    if (op_521) =.? (usize 0):bool then (let tmp_522 :=
        (x_519) shift_right (array_index (op_table_v) (((usize 3) * (i_520)) + (
              usize 2))) in 
      (tmp_522)) else ((tmp_522)) in 
  ((uint32_rotate_right (x_519) (array_index (op_table_v) ((usize 3) * (
            i_520)))) .^ (uint32_rotate_right (x_519) (array_index (
          op_table_v) (((usize 3) * (i_520)) + (usize 1))))) .^ (tmp_522).


Definition schedule (block_523 : block_t)  : round_constants_table_t :=
  let b_524 : seq uint32 :=
    array_to_be_uint32s (block_523) in 
  let s_525 : round_constants_table_t :=
    array_new_ (default : uint32) (k_size_v) in 
  let s_525 :=
    foldi (usize 0) (k_size_v) (fun i_526 s_525 =>
      let '(s_525) :=
        if (i_526) <.? (usize 16):bool then (let s_525 :=
            array_upd s_525 (i_526) (seq_index (b_524) (i_526)) in 
          (s_525)) else (let t16_527 : uint32 :=
            array_index (s_525) ((i_526) - (usize 16)) in 
          let t15_528 : uint32 :=
            array_index (s_525) ((i_526) - (usize 15)) in 
          let t7_529 : uint32 :=
            array_index (s_525) ((i_526) - (usize 7)) in 
          let t2_530 : uint32 :=
            array_index (s_525) ((i_526) - (usize 2)) in 
          let s1_531 : uint32 :=
            sigma (t2_530) (usize 3) (usize 0) in 
          let s0_532 : uint32 :=
            sigma (t15_528) (usize 2) (usize 0) in 
          let s_525 :=
            array_upd s_525 (i_526) ((((s1_531) .+ (t7_529)) .+ (s0_532)) .+ (
                t16_527)) in 
          (s_525)) in 
      (s_525))
    s_525 in 
  s_525.


Definition shuffle
  (ws_533 : round_constants_table_t)
  (hashi_534 : hash_t)
  
  : hash_t :=
  let h_535 : hash_t :=
    hashi_534 in 
  let h_535 :=
    foldi (usize 0) (k_size_v) (fun i_536 h_535 =>
      let a0_537 : uint32 :=
        array_index (h_535) (usize 0) in 
      let b0_538 : uint32 :=
        array_index (h_535) (usize 1) in 
      let c0_539 : uint32 :=
        array_index (h_535) (usize 2) in 
      let d0_540 : uint32 :=
        array_index (h_535) (usize 3) in 
      let e0_541 : uint32 :=
        array_index (h_535) (usize 4) in 
      let f0_542 : uint32 :=
        array_index (h_535) (usize 5) in 
      let g0_543 : uint32 :=
        array_index (h_535) (usize 6) in 
      let h0_544 : uint32 :=
        array_index (h_535) (usize 7) in 
      let t1_545 : uint32 :=
        ((((h0_544) .+ (sigma (e0_541) (usize 1) (usize 1))) .+ (ch (e0_541) (
                f0_542) (g0_543))) .+ (array_index (k_table_v) (i_536))) .+ (
          array_index (ws_533) (i_536)) in 
      let t2_546 : uint32 :=
        (sigma (a0_537) (usize 0) (usize 1)) .+ (maj (a0_537) (b0_538) (
            c0_539)) in 
      let h_535 :=
        array_upd h_535 (usize 0) ((t1_545) .+ (t2_546)) in 
      let h_535 :=
        array_upd h_535 (usize 1) (a0_537) in 
      let h_535 :=
        array_upd h_535 (usize 2) (b0_538) in 
      let h_535 :=
        array_upd h_535 (usize 3) (c0_539) in 
      let h_535 :=
        array_upd h_535 (usize 4) ((d0_540) .+ (t1_545)) in 
      let h_535 :=
        array_upd h_535 (usize 5) (e0_541) in 
      let h_535 :=
        array_upd h_535 (usize 6) (f0_542) in 
      let h_535 :=
        array_upd h_535 (usize 7) (g0_543) in 
      (h_535))
    h_535 in 
  h_535.


Definition compress (block_547 : block_t) (h_in_548 : hash_t)  : hash_t :=
  let s_549 : round_constants_table_t :=
    schedule (block_547) in 
  let h_550 : hash_t :=
    shuffle (s_549) (h_in_548) in 
  let h_550 :=
    foldi (usize 0) (usize 8) (fun i_551 h_550 =>
      let h_550 :=
        array_upd h_550 (i_551) ((array_index (h_550) (i_551)) .+ (array_index (
              h_in_548) (i_551))) in 
      (h_550))
    h_550 in 
  h_550.


Definition hash (msg_552 : byte_seq)  : sha256_digest_t :=
  let h_553 : hash_t :=
    hash_init_v in 
  let last_block_554 : block_t :=
    array_new_ (default : uint8) (block_size_v) in 
  let last_block_len_555 : uint_size :=
    usize 0 in 
  let '(h_553, last_block_554, last_block_len_555) :=
    foldi (usize 0) (seq_num_chunks (msg_552) (block_size_v)) (fun i_556 '(
        h_553,
        last_block_554,
        last_block_len_555
      ) =>
      let '(block_len_557, block_558) :=
        seq_get_chunk (msg_552) (block_size_v) (i_556) in 
      let '(h_553, last_block_554, last_block_len_555) :=
        if (block_len_557) <.? (block_size_v):bool then (let last_block_554 :=
            array_update_start (array_new_ (default : uint8) (block_size_v)) (
              block_558) in 
          let last_block_len_555 :=
            block_len_557 in 
          (h_553, last_block_554, last_block_len_555)) else (
          let compress_input_559 : block_t :=
            array_from_seq (block_size_v) (block_558) in 
          let h_553 :=
            compress (compress_input_559) (h_553) in 
          (h_553, last_block_554, last_block_len_555)) in 
      (h_553, last_block_554, last_block_len_555))
    (h_553, last_block_554, last_block_len_555) in 
  let last_block_554 :=
    array_upd last_block_554 (last_block_len_555) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let len_bist_560 : uint64 :=
    secret (pub_u64 ((seq_len (msg_552)) * (usize 8))) : int64 in 
  let '(h_553, last_block_554) :=
    if (last_block_len_555) <.? ((block_size_v) - (len_size_v)):bool then (
      let last_block_554 :=
        array_update (last_block_554) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint64_to_be_bytes (len_bist_560))) in 
      let h_553 :=
        compress (last_block_554) (h_553) in 
      (h_553, last_block_554)) else (let pad_block_561 : block_t :=
        array_new_ (default : uint8) (block_size_v) in 
      let pad_block_561 :=
        array_update (pad_block_561) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint64_to_be_bytes (len_bist_560))) in 
      let h_553 :=
        compress (last_block_554) (h_553) in 
      let h_553 :=
        compress (pad_block_561) (h_553) in 
      (h_553, last_block_554)) in 
  array_from_seq (hash_size_v) (array_to_be_bytes (h_553)).


Definition sha256 (msg_562 : byte_seq)  : sha256_digest_t :=
  hash (msg_562).


