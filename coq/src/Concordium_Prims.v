(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:1]] *)
(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
(* hacspec_concordium_prims - Coq code:1 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:2]] *)
Definition load_state_hacspec
  (buf_0 : public_byte_seq)
  (offset_1 : int32)
  : (public_byte_seq × int32) :=
  (buf_0, @repr WORDSIZE32 1).
(* hacspec_concordium_prims - Coq code:2 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:3]] *)
Definition write_state_hacspec
  (buf_2 : public_byte_seq)
  (offset_3 : int32)
  : (public_byte_seq × int32) :=
  (buf_2, @repr WORDSIZE32 1).
(* hacspec_concordium_prims - Coq code:3 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:4]] *)
Definition state_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.
(* hacspec_concordium_prims - Coq code:4 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:5]] *)
Definition resize_state_hacspec (new_size_4 : int32) : int32 :=
  @repr WORDSIZE32 1.
(* hacspec_concordium_prims - Coq code:5 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:6]] *)
Definition get_parameter_section_hacspec
  (buf_5 : public_byte_seq)
  (offset_6 : int32)
  : (public_byte_seq × int32) :=
  (buf_5, @repr WORDSIZE32 1).
(* hacspec_concordium_prims - Coq code:6 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:7]] *)
Definition get_parameter_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.
(* hacspec_concordium_prims - Coq code:7 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:8]] *)
Definition get_slot_time_hacspec  : int64 :=
  @repr WORDSIZE64 1.
(* hacspec_concordium_prims - Coq code:8 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:9]] *)
Definition get_policy_section_hacspec
  (policy_bytes_7 : public_byte_seq)
  (offset_8 : int32)
  : (public_byte_seq × int32) :=
  (policy_bytes_7, @repr WORDSIZE32 1).
(* hacspec_concordium_prims - Coq code:9 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:10]] *)
Definition get_init_origin_hacspec
  (start_9 : public_byte_seq)
  : public_byte_seq :=
  start_9.
(* hacspec_concordium_prims - Coq code:10 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:11]] *)
Definition get_receive_invoker_hacspec
  (start_10 : public_byte_seq)
  : public_byte_seq :=
  start_10.
(* hacspec_concordium_prims - Coq code:11 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:12]] *)
Definition get_receive_self_address_hacspec
  (start_11 : public_byte_seq)
  : public_byte_seq :=
  start_11.
(* hacspec_concordium_prims - Coq code:12 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:13]] *)
Definition get_receive_self_balance_hacspec  : int64 :=
  @repr WORDSIZE64 1.
(* hacspec_concordium_prims - Coq code:13 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:14]] *)
Definition get_receive_sender_hacspec
  (start_12 : public_byte_seq)
  : public_byte_seq :=
  start_12.
(* hacspec_concordium_prims - Coq code:14 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:15]] *)
Definition log_event_hacspec
  (start_13 : public_byte_seq)
  : (public_byte_seq × int32) :=
  (start_13, @repr WORDSIZE32 1).
(* hacspec_concordium_prims - Coq code:15 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:16]] *)
Definition accept_hacspec  : int32 :=
  @repr WORDSIZE32 1.
(* hacspec_concordium_prims - Coq code:16 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:17]] *)
Definition simple_transfer_hacspec
  (buf_14 : public_byte_seq)
  (amount_15 : int64)
  : int32 :=
  @repr WORDSIZE32 1.
(* hacspec_concordium_prims - Coq code:17 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:18]] *)
Definition send_hacspec
  (addr_index_16 : int64)
  (addr_subindex_17 : int64)
  (receive_name_18 : public_byte_seq)
  (amount_19 : int64)
  (parameter_20 : public_byte_seq)
  : int32 :=
  @repr WORDSIZE32 1.
(* hacspec_concordium_prims - Coq code:18 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:19]] *)
Definition combine_and_hacspec (l_21 : int32) (r_22 : int32) : int32 :=
  @repr WORDSIZE32 1.
(* hacspec_concordium_prims - Coq code:19 ends here *)

(* [[file:concordium.org::*hacspec_concordium_prims - Coq code][hacspec_concordium_prims - Coq code:20]] *)
Definition combine_or_hacspec (l_23 : int32) (r_24 : int32) : int32 :=
  @repr WORDSIZE32 1.
(* hacspec_concordium_prims - Coq code:20 ends here *)
