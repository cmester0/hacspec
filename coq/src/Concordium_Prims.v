(** This file was automatically generated using Hacspec **)

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

Require Import Hacspec_Lib.

Definition accept_hacspec  : int32 :=
  @repr WORDSIZE32 1.

Definition simple_transfer_hacspec
  (buf_0 : public_byte_seq)
  (amount_1 : int64)
  : int32 :=
  @repr WORDSIZE32 1.

Definition send_hacspec
  (addr_index_2 : int64)
  (addr_subindex_3 : int64)
  (receive_name_4 : public_byte_seq)
  (amount_5 : int64)
  (parameter_6 : public_byte_seq)
  : int32 :=
  @repr WORDSIZE32 1.

Definition combine_and_hacspec (l_7 : int32) (r_8 : int32) : int32 :=
  @repr WORDSIZE32 1.

Definition combine_or_hacspec (l_9 : int32) (r_10 : int32) : int32 :=
  @repr WORDSIZE32 1.

Definition get_parameter_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.

Definition get_parameter_section_hacspec
  (buf_11 : public_byte_seq)
  (offset_12 : int32)
  : (public_byte_seq ∏ int32) :=
  (buf_11, @repr WORDSIZE32 1).

Definition get_policy_section_hacspec
  (policy_bytes_13 : public_byte_seq)
  (offset_14 : int32)
  : (public_byte_seq ∏ int32) :=
  (policy_bytes_13, @repr WORDSIZE32 1).

Definition log_event_hacspec
  (start_15 : public_byte_seq)
  : (public_byte_seq ∏ int32) :=
  (start_15, @repr WORDSIZE32 1).

Definition load_state_hacspec
  (buf_16 : public_byte_seq)
  (offset_17 : int32)
  : (public_byte_seq ∏ int32) :=
  (buf_16, @repr WORDSIZE32 1).

Definition write_state_hacspec
  (buf_18 : public_byte_seq)
  (offset_19 : int32)
  : (public_byte_seq ∏ int32) :=
  (buf_18, @repr WORDSIZE32 1).

Definition resize_state_hacspec (new_size_20 : int32) : int32 :=
  @repr WORDSIZE32 1.

Definition state_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.

Definition get_init_origin_hacspec
  (start_21 : public_byte_seq)
  : public_byte_seq :=
  start_21.

Definition get_receive_invoker_hacspec
  (start_22 : public_byte_seq)
  : public_byte_seq :=
  start_22.

Definition get_receive_self_address_hacspec
  (start_23 : public_byte_seq)
  : public_byte_seq :=
  start_23.

Definition get_receive_self_balance_hacspec  : int64 :=
  @repr WORDSIZE64 1.

Definition get_receive_sender_hacspec
  (start_24 : public_byte_seq)
  : public_byte_seq :=
  start_24.

Definition get_slot_time_hacspec  : int64 :=
  @repr WORDSIZE64 1.

