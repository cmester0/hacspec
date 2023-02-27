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

Require Import Hacspec_Aes.
Export Hacspec_Aes.

Require Import Hacspec_Gf128.
Export Hacspec_Gf128.

Notation "'aes_gcm_byte_seq_result_t'" := ((
  result byte_seq int8)) : hacspec_scope.

Definition invalid_tag_v : int8 :=
  @repr WORDSIZE8 1.

Definition pad_aad_msg (aad_128 : byte_seq) (msg_129 : byte_seq)  : byte_seq :=
  let laad_130 : uint_size :=
    seq_len (aad_128) in 
  let lmsg_131 : uint_size :=
    seq_len (msg_129) in 
  let pad_aad_132 : uint_size :=
    (if (((laad_130) %% (usize 16)) =.? (usize 0)):bool then (laad_130) else ((
          laad_130) + ((usize 16) - ((laad_130) %% (usize 16))))) in 
  let pad_msg_133 : uint_size :=
    (if (((lmsg_131) %% (usize 16)) =.? (usize 0)):bool then (lmsg_131) else ((
          lmsg_131) + ((usize 16) - ((lmsg_131) %% (usize 16))))) in 
  let padded_msg_134 : seq uint8 :=
    seq_new_ (default : uint8) (((pad_aad_132) + (pad_msg_133)) + (
        usize 16)) in 
  let padded_msg_134 :=
    seq_update (padded_msg_134) (usize 0) (aad_128) in 
  let padded_msg_134 :=
    seq_update (padded_msg_134) (pad_aad_132) (msg_129) in 
  let padded_msg_134 :=
    seq_update (padded_msg_134) ((pad_aad_132) + (pad_msg_133)) (
      array_to_seq (uint64_to_be_bytes ((secret (pub_u64 (
              laad_130)) : int64) .* (secret (
            @repr WORDSIZE64 8) : int64)))) in 
  let padded_msg_134 :=
    seq_update (padded_msg_134) (((pad_aad_132) + (pad_msg_133)) + (usize 8)) (
      array_to_seq (uint64_to_be_bytes ((secret (pub_u64 (
              lmsg_131)) : int64) .* (secret (
            @repr WORDSIZE64 8) : int64)))) in 
  padded_msg_134.


Definition encrypt_aes
  (key_135 : byte_seq)
  (iv_136 : aes_nonce_t)
  (aad_137 : byte_seq)
  (msg_138 : byte_seq)
  
  : (byte_seq '× gf128_tag_t) :=
  let iv0_139 : aes_nonce_t :=
    array_new_ (default : uint8) (_) in 
  let mac_key_140 : block_t :=
    result_unwrap (aes_ctr_key_block (key_135) (iv0_139) (secret (
          @repr WORDSIZE32 (0)) : int32) (key_length_v) (rounds_v) (
        key_schedule_length_v) (key_length_v) (iterations_v)) in 
  let tag_mix_141 : block_t :=
    result_unwrap (aes_ctr_key_block (key_135) ((iv_136)) (secret (
          @repr WORDSIZE32 (1)) : int32) (key_length_v) (rounds_v) (
        key_schedule_length_v) (key_length_v) (iterations_v)) in 
  let cipher_text_142 : seq uint8 :=
    aes128_encrypt (array_from_seq (_) (key_135)) (iv_136) (secret (
        @repr WORDSIZE32 (2)) : int32) (msg_138) in 
  let padded_msg_143 : seq uint8 :=
    pad_aad_msg (aad_137) (cipher_text_142) in 
  let tag_144 : gf128_tag_t :=
    gmac (padded_msg_143) (array_from_seq (_) (array_to_seq (mac_key_140))) in 
  let tag_145 : block_t :=
    xor_block (array_from_seq (_) (array_to_seq (tag_144))) (tag_mix_141) in 
  (cipher_text_142, array_from_seq (_) (array_to_seq (tag_145))).


Definition encrypt_aes128
  (key_146 : key128_t)
  (iv_147 : aes_nonce_t)
  (aad_148 : byte_seq)
  (msg_149 : byte_seq)
  
  : (byte_seq '× gf128_tag_t) :=
  encrypt_aes (seq_from_seq (array_to_seq (key_146))) (iv_147) (aad_148) (
    msg_149).


Definition decrypt_aes
  (key_150 : byte_seq)
  (iv_151 : aes_nonce_t)
  (aad_152 : byte_seq)
  (cipher_text_153 : byte_seq)
  (tag_154 : gf128_tag_t)
  
  : aes_gcm_byte_seq_result_t :=
  let iv0_155 : aes_nonce_t :=
    array_new_ (default : uint8) (_) in 
  bind (aes_ctr_key_block (key_150) (iv0_155) (secret (
        @repr WORDSIZE32 (0)) : int32) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)) (fun mac_key_156 =>
    bind (aes_ctr_key_block (key_150) ((iv_151)) (secret (
          @repr WORDSIZE32 (1)) : int32) (key_length_v) (rounds_v) (
        key_schedule_length_v) (key_length_v) (iterations_v)) (
      fun tag_mix_157 => let padded_msg_158 : seq uint8 :=
        pad_aad_msg (aad_152) (cipher_text_153) in 
      let my_tag_159 : gf128_tag_t :=
        gmac (padded_msg_158) (array_from_seq (_) (
            array_to_seq (mac_key_156))) in 
      let my_tag_160 : block_t :=
        xor_block (array_from_seq (_) (array_to_seq (my_tag_159))) (
          tag_mix_157) in 
      let ptxt_161 : seq uint8 :=
        aes128_decrypt (array_from_seq (_) (key_150)) (iv_151) (secret (
            @repr WORDSIZE32 (2)) : int32) (cipher_text_153) in 
      (if (array_declassify_eq (my_tag_160) (array_from_seq (_) (
              array_to_seq (tag_154)))):bool then (@Ok byte_seq int8 (
            ptxt_161)) else (@Err byte_seq int8 (invalid_tag_v))))).


Definition decrypt_aes128
  (key_162 : key128_t)
  (iv_163 : aes_nonce_t)
  (aad_164 : byte_seq)
  (cipher_text_165 : byte_seq)
  (tag_166 : gf128_tag_t)
  
  : aes_gcm_byte_seq_result_t :=
  decrypt_aes (seq_from_seq (array_to_seq (key_162))) (iv_163) (aad_164) (
    cipher_text_165) (tag_166).


