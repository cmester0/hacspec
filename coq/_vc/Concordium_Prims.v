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

Definition accept_hacspec   : int32 :=
  @repr WORDSIZE32 (1).


Definition simple_transfer_hacspec
  (buf_2525 : public_byte_seq)
  (amount_2526 : int64)
  
  : int32 :=
  @repr WORDSIZE32 (1).


Definition send_hacspec
  (addr_index_2527 : int64)
  (addr_subindex_2528 : int64)
  (receive_name_2529 : public_byte_seq)
  (amount_2530 : int64)
  (parameter_2531 : public_byte_seq)
  
  : int32 :=
  @repr WORDSIZE32 (1).


Definition combine_and_hacspec (l_2532 : int32) (r_2533 : int32)  : int32 :=
  @repr WORDSIZE32 (1).


Definition combine_or_hacspec (l_2534 : int32) (r_2535 : int32)  : int32 :=
  @repr WORDSIZE32 (1).


Definition get_parameter_size_hacspec   : int32 :=
  @repr WORDSIZE32 (1).


Definition get_parameter_section_hacspec
  (buf_2536 : public_byte_seq)
  (offset_2537 : int32)
  
  : (public_byte_seq '× int32) :=
  (buf_2536, @repr WORDSIZE32 (1)).


Definition get_policy_section_hacspec
  (policy_bytes_2538 : public_byte_seq)
  (offset_2539 : int32)
  
  : (public_byte_seq '× int32) :=
  (policy_bytes_2538, @repr WORDSIZE32 (1)).


Definition log_event_hacspec
  (start_2540 : public_byte_seq)
  
  : (public_byte_seq '× int32) :=
  (start_2540, @repr WORDSIZE32 (1)).


Definition load_state_hacspec
  (buf_2541 : public_byte_seq)
  (offset_2542 : int32)
  
  : (public_byte_seq '× int32) :=
  (buf_2541, @repr WORDSIZE32 (1)).


Definition write_state_hacspec
  (buf_2543 : public_byte_seq)
  (offset_2544 : int32)
  
  : (public_byte_seq '× int32) :=
  (buf_2543, @repr WORDSIZE32 (1)).


Definition resize_state_hacspec (new_size_2545 : int32)  : int32 :=
  @repr WORDSIZE32 (1).


Definition state_size_hacspec   : int32 :=
  @repr WORDSIZE32 (1).


Definition get_init_origin_hacspec
  (start_2546 : public_byte_seq)
  
  : public_byte_seq :=
  start_2546.


Definition get_receive_invoker_hacspec
  (start_2547 : public_byte_seq)
  
  : public_byte_seq :=
  start_2547.


Definition get_receive_self_address_hacspec
  (start_2548 : public_byte_seq)
  
  : public_byte_seq :=
  start_2548.


Definition get_receive_self_balance_hacspec   : int64 :=
  @repr WORDSIZE64 1.


Definition get_receive_sender_hacspec
  (start_2549 : public_byte_seq)
  
  : public_byte_seq :=
  start_2549.


Definition get_receive_owner_hacspec
  (start_2550 : public_byte_seq)
  
  : public_byte_seq :=
  start_2550.


Definition get_slot_time_hacspec   : int64 :=
  @repr WORDSIZE64 1.


