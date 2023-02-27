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

Require Import Strobe.
Export Strobe.

Notation "'transcript_t'" := (strobe_t) : hacspec_scope.

Definition merlin_protocol_label   : seq uint8 :=
  [
    secret (@repr WORDSIZE8 77) : int8;
    secret (@repr WORDSIZE8 101) : int8;
    secret (@repr WORDSIZE8 114) : int8;
    secret (@repr WORDSIZE8 108) : int8;
    secret (@repr WORDSIZE8 105) : int8;
    secret (@repr WORDSIZE8 110) : int8;
    secret (@repr WORDSIZE8 32) : int8;
    secret (@repr WORDSIZE8 118) : int8;
    secret (@repr WORDSIZE8 49) : int8;
    secret (@repr WORDSIZE8 46) : int8;
    secret (@repr WORDSIZE8 48) : int8
  ].


Definition encode_uint64 (x_901 : uint64)  : seq uint8 :=
  array_to_le_bytes (uint64_to_le_bytes (x_901)).


Definition encode_usize_as_u32 (x_902 : uint_size)  : seq uint8 :=
  let x_uint32_903 : uint32 :=
    uint32_classify (pub_u32 (x_902)) in 
  array_to_le_bytes (uint32_to_le_bytes (x_uint32_903)).


Definition new_ (label_904 : seq uint8)  : transcript_t :=
  let transcript_905 : (state_uint8_t '× int8 '× int8 '× int8) :=
    new_strobe (merlin_protocol_label ) in 
  let dom_sep_906 : seq uint8 :=
    [
      secret (@repr WORDSIZE8 100) : int8;
      secret (@repr WORDSIZE8 111) : int8;
      secret (@repr WORDSIZE8 109) : int8;
      secret (@repr WORDSIZE8 45) : int8;
      secret (@repr WORDSIZE8 115) : int8;
      secret (@repr WORDSIZE8 101) : int8;
      secret (@repr WORDSIZE8 112) : int8
    ] in 
  append_message (transcript_905) (dom_sep_906) (label_904).


Definition append_message
  (transcript_907 : transcript_t)
  (label_908 : seq uint8)
  (message_909 : seq uint8)
  
  : transcript_t :=
  let data_len_910 : seq uint8 :=
    array_to_be_bytes (uint32_to_le_bytes (uint32_classify (pub_u32 (seq_len (
              message_909))))) in 
  let transcript_907 :=
    meta_ad (transcript_907) (label_908) (false) in 
  let transcript_907 :=
    meta_ad (transcript_907) (data_len_910) (true) in 
  let transcript_907 :=
    ad (transcript_907) (message_909) (false) in 
  transcript_907.


Definition challenge_bytes
  (transcript_911 : transcript_t)
  (label_912 : seq uint8)
  (dest_913 : seq uint8)
  
  : (transcript_t '× seq uint8) :=
  let data_len_914 : seq uint8 :=
    encode_usize_as_u32 (seq_len (dest_913)) in 
  let transcript_911 :=
    meta_ad (transcript_911) (label_912) (false) in 
  let transcript_911 :=
    meta_ad (transcript_911) (data_len_914) (true) in 
  prf (transcript_911) (dest_913) (false).


Definition append_uint64
  (transcript_915 : transcript_t)
  (label_916 : seq uint8)
  (x_917 : uint64)
  
  : transcript_t :=
  append_message (transcript_915) (label_916) (encode_uint64 (x_917)).


