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

Definition state_t := nseq (uint32) (usize 16).

Definition state_idx_t :=
  nat_mod (usize 16).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition constants_t := nseq (uint32) (usize 4).

Definition constants_idx_t :=
  nat_mod (usize 4).
Definition uint_size_in_constants_idx_t(n : uint_size) : constants_idx_t := int_in_nat_mod n.
Coercion uint_size_in_constants_idx_t : uint_size >-> constants_idx_t.

Definition block_t := nseq (uint8) (usize 64).

Definition cha_cha_iv_t := nseq (uint8) (usize 12).

Definition cha_cha_key_t := nseq (uint8) (usize 32).

Definition chacha20_line
  (a_195 : state_idx_t)
  (b_196 : state_idx_t)
  (d_197 : state_idx_t)
  (s_198 : uint_size)
  (m_199 : state_t)
  
  : state_t :=
  let state_200 : state_t :=
    m_199 in 
  let state_200 :=
    array_upd state_200 (a_195) ((array_index (state_200) (a_195)) .+ (
        array_index (state_200) (b_196))) in 
  let state_200 :=
    array_upd state_200 (d_197) ((array_index (state_200) (d_197)) .^ (
        array_index (state_200) (a_195))) in 
  let state_200 :=
    array_upd state_200 (d_197) (uint32_rotate_left (array_index (state_200) (
          d_197)) (s_198)) in 
  state_200.


Definition chacha20_quarter_round
  (a_201 : state_idx_t)
  (b_202 : state_idx_t)
  (c_203 : state_idx_t)
  (d_204 : state_idx_t)
  (state_205 : state_t)
  
  : state_t :=
  let state_206 : state_t :=
    chacha20_line (a_201) (b_202) (d_204) (usize 16) (state_205) in 
  let state_207 : state_t :=
    chacha20_line (c_203) (d_204) (b_202) (usize 12) (state_206) in 
  let state_208 : state_t :=
    chacha20_line (a_201) (b_202) (d_204) (usize 8) (state_207) in 
  chacha20_line (c_203) (d_204) (b_202) (usize 7) (state_208).


Definition chacha20_double_round (state_209 : state_t)  : state_t :=
  let state_210 : state_t :=
    chacha20_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (
      state_209) in 
  let state_211 : state_t :=
    chacha20_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (
      state_210) in 
  let state_212 : state_t :=
    chacha20_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (
      state_211) in 
  let state_213 : state_t :=
    chacha20_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (
      state_212) in 
  let state_214 : state_t :=
    chacha20_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (
      state_213) in 
  let state_215 : state_t :=
    chacha20_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (
      state_214) in 
  let state_216 : state_t :=
    chacha20_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (
      state_215) in 
  chacha20_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (state_216).


Definition chacha20_rounds (state_217 : state_t)  : state_t :=
  let st_218 : state_t :=
    state_217 in 
  let st_218 :=
    foldi (usize 0) (usize 10) (fun i_219 st_218 =>
      let st_218 :=
        chacha20_double_round (st_218) in 
      (st_218))
    st_218 in 
  st_218.


Definition chacha20_core (ctr_220 : uint32) (st0_221 : state_t)  : state_t :=
  let state_222 : state_t :=
    st0_221 in 
  let state_222 :=
    array_upd state_222 (usize 12) ((array_index (state_222) (usize 12)) .+ (
        ctr_220)) in 
  let k_223 : state_t :=
    chacha20_rounds (state_222) in 
  (k_223) array_add (state_222).


Definition chacha20_constants_init   : constants_t :=
  let constants_224 : constants_t :=
    array_new_ (default : uint32) (4) in 
  let constants_224 :=
    array_upd constants_224 (usize 0) (secret (
        @repr WORDSIZE32 (1634760805)) : int32) in 
  let constants_224 :=
    array_upd constants_224 (usize 1) (secret (
        @repr WORDSIZE32 (857760878)) : int32) in 
  let constants_224 :=
    array_upd constants_224 (usize 2) (secret (
        @repr WORDSIZE32 (2036477234)) : int32) in 
  let constants_224 :=
    array_upd constants_224 (usize 3) (secret (
        @repr WORDSIZE32 (1797285236)) : int32) in 
  constants_224.


Definition chacha20_init
  (key_225 : cha_cha_key_t)
  (iv_226 : cha_cha_iv_t)
  (ctr_227 : uint32)
  
  : state_t :=
  let st_228 : state_t :=
    array_new_ (default : uint32) (16) in 
  let st_228 :=
    array_update (st_228) (usize 0) (
      array_to_seq (chacha20_constants_init )) in 
  let st_228 :=
    array_update (st_228) (usize 4) (array_to_le_uint32s (key_225)) in 
  let st_228 :=
    array_upd st_228 (usize 12) (ctr_227) in 
  let st_228 :=
    array_update (st_228) (usize 13) (array_to_le_uint32s (iv_226)) in 
  st_228.


Definition chacha20_key_block (state_229 : state_t)  : block_t :=
  let state_230 : state_t :=
    chacha20_core (secret (@repr WORDSIZE32 (0)) : int32) (state_229) in 
  array_from_seq (64) (array_to_le_bytes (state_230)).


Definition chacha20_key_block0
  (key_231 : cha_cha_key_t)
  (iv_232 : cha_cha_iv_t)
  
  : block_t :=
  let state_233 : state_t :=
    chacha20_init (key_231) (iv_232) (secret (@repr WORDSIZE32 (0)) : int32) in 
  chacha20_key_block (state_233).


Definition chacha20_encrypt_block
  (st0_234 : state_t)
  (ctr_235 : uint32)
  (plain_236 : block_t)
  
  : block_t :=
  let st_237 : state_t :=
    chacha20_core (ctr_235) (st0_234) in 
  let pl_238 : state_t :=
    array_from_seq (16) (array_to_le_uint32s (plain_236)) in 
  let st_239 : state_t :=
    (pl_238) array_xor (st_237) in 
  array_from_seq (64) (array_to_le_bytes (st_239)).


Definition chacha20_encrypt_last
  (st0_240 : state_t)
  (ctr_241 : uint32)
  (plain_242 : byte_seq)
  
  : byte_seq :=
  let b_243 : block_t :=
    array_new_ (default : uint8) (64) in 
  let b_243 :=
    array_update (b_243) (usize 0) (plain_242) in 
  let b_243 :=
    chacha20_encrypt_block (st0_240) (ctr_241) (b_243) in 
  array_slice (b_243) (usize 0) (seq_len (plain_242)).


Definition chacha20_update (st0_244 : state_t) (m_245 : byte_seq)  : byte_seq :=
  let blocks_out_246 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (m_245)) in 
  let n_blocks_247 : uint_size :=
    seq_num_exact_chunks (m_245) (usize 64) in 
  let blocks_out_246 :=
    foldi (usize 0) (n_blocks_247) (fun i_248 blocks_out_246 =>
      let msg_block_249 : seq uint8 :=
        seq_get_exact_chunk (m_245) (usize 64) (i_248) in 
      let b_250 : block_t :=
        chacha20_encrypt_block (st0_244) (secret (pub_u32 (i_248)) : int32) (
          array_from_seq (64) (msg_block_249)) in 
      let blocks_out_246 :=
        seq_set_exact_chunk (blocks_out_246) (usize 64) (i_248) (
          array_to_seq (b_250)) in 
      (blocks_out_246))
    blocks_out_246 in 
  let last_block_251 : seq uint8 :=
    seq_get_remainder_chunk (m_245) (usize 64) in 
  let '(blocks_out_246) :=
    if (seq_len (last_block_251)) !=.? (usize 0):bool then (
      let b_252 : seq uint8 :=
        chacha20_encrypt_last (st0_244) (secret (pub_u32 (
              n_blocks_247)) : int32) (last_block_251) in 
      let blocks_out_246 :=
        seq_set_chunk (blocks_out_246) (usize 64) (n_blocks_247) (b_252) in 
      (blocks_out_246)) else ((blocks_out_246)) in 
  blocks_out_246.


Definition chacha20
  (key_253 : cha_cha_key_t)
  (iv_254 : cha_cha_iv_t)
  (ctr_255 : int32)
  (m_256 : byte_seq)
  
  : byte_seq :=
  let state_257 : state_t :=
    chacha20_init (key_253) (iv_254) (secret (ctr_255) : int32) in 
  chacha20_update (state_257) (m_256).


