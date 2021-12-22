(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition test_casting  : unit :=
  let uint8v_0 : uint8 :=
    secret (@repr WORDSIZE8 5) in 
  let uint16v_1 : uint16 :=
    secret (@repr WORDSIZE16 5) in 
  let uint32v_2 : uint32 :=
    secret (@repr WORDSIZE32 5) in 
  let uint64v_3 : uint64 :=
    secret (@repr WORDSIZE64 5) in 
  let uint128v_4 : uint128 :=
    secret (@repr WORDSIZE128 5) in 
  let iint8v_5 : iint8 :=
    secret (@repr WORDSIZE8 5) in 
  let iint16v_6 : iint16 :=
    secret (@repr WORDSIZE16 5) in 
  let iint32v_7 : iint32 :=
    secret (@repr WORDSIZE32 5) in 
  let iint64v_8 : iint64 :=
    secret (@repr WORDSIZE64 5) in 
  let iint128v_9 : iint128 :=
    secret (@repr WORDSIZE128 5) in 
  let usizev_10 : uint_size :=
    usize 5 in 
  let u8v_11 : int8 :=
    @repr WORDSIZE8 5 in 
  let u16v_12 : int16 :=
    @repr WORDSIZE16 5 in 
  let u32v_13 : int32 :=
    @repr WORDSIZE32 5 in 
  let u64v_14 : int64 :=
    @repr WORDSIZE64 5 in 
  let u128v_15 : int128 :=
    @repr WORDSIZE128 5 in 
  let i8v_16 : int8 :=
    @repr WORDSIZE8 5 in 
  let i16v_17 : int16 :=
    @repr WORDSIZE16 5 in 
  let i32v_18 : int32 :=
    @repr WORDSIZE32 5 in 
  let i64v_19 : int64 :=
    @repr WORDSIZE64 5 in 
  let i128v_20 : int128 :=
    @repr WORDSIZE128 5 in 
  let _ : uint128 :=
    uint128_from_uint8 (uint8v_0) in 
  let _ : uint8 :=
    uint8_from_uint128 (uint128v_4) in 
  let _ : uint128 :=
    uint128_from_uint16 (uint16v_1) in 
  let _ : uint16 :=
    uint16_from_uint128 (uint128v_4) in 
  let _ : uint128 :=
    uint128_from_uint32 (uint32v_2) in 
  let _ : uint32 :=
    uint32_from_uint128 (uint128v_4) in 
  let _ : uint128 :=
    uint128_from_uint64 (uint64v_3) in 
  let _ : uint64 :=
    uint64_from_uint128 (uint128v_4) in 
  let _ : uint64 :=
    uint64_from_uint8 (uint8v_0) in 
  let _ : uint8 :=
    uint8_from_uint64 (uint64v_3) in 
  let _ : uint64 :=
    uint64_from_uint16 (uint16v_1) in 
  let _ : uint16 :=
    uint16_from_uint64 (uint64v_3) in 
  let _ : uint64 :=
    uint64_from_uint32 (uint32v_2) in 
  let _ : uint32 :=
    uint32_from_uint64 (uint64v_3) in 
  let _ : uint32 :=
    uint32_from_uint8 (uint8v_0) in 
  let _ : uint8 :=
    uint8_from_uint32 (uint32v_2) in 
  let _ : uint32 :=
    uint32_from_uint16 (uint16v_1) in 
  let _ : uint16 :=
    uint16_from_uint32 (uint32v_2) in 
  let _ : uint16 :=
    uint16_from_uint8 (uint8v_0) in 
  let _ : uint8 :=
    uint8_from_uint16 (uint16v_1) in 
  let _ : int8 :=
    declassify_u8_from_uint8 (uint8v_0) in 
  let _ : int16 :=
    declassify_u16_from_uint8 (uint8v_0) in 
  let _ : int32 :=
    declassify_u32_from_uint8 (uint8v_0) in 
  let _ : int64 :=
    declassify_u64_from_uint8 (uint8v_0) in 
  let _ : int128 :=
    declassify_u128_from_uint8 (uint8v_0) in 
  let _ : uint_size :=
    declassify_usize_from_uint8 (uint8v_0) in 
  let _ : uint8 :=
    uint8_from_usize (usizev_10) in 
  let _ : int16 :=
    declassify_u16_from_uint16 (uint16v_1) in 
  let _ : int32 :=
    declassify_u32_from_uint16 (uint16v_1) in 
  let _ : int64 :=
    declassify_u64_from_uint16 (uint16v_1) in 
  let _ : int128 :=
    u128_from_uint16 (uint16v_1) in 
  let _ : int32 :=
    declassify_u32_from_uint32 (uint32v_2) in 
  let _ : int64 :=
    declassify_u64_from_uint32 (uint32v_2) in 
  let _ : int128 :=
    declassify_u128_from_uint32 (uint32v_2) in 
  let _ : int64 :=
    declassify_u64_from_uint64 (uint64v_3) in 
  let _ : int128 :=
    declassify_u128_from_uint64 (uint64v_3) in 
  let _ : int128 :=
    declassify_u128_from_uint128 (uint128v_4) in 
  let _ : uint64 :=
    uint64_from_usize (usizev_10) in 
  let _ : uint128 :=
    uint128_from_usize (usizev_10) in 
  let _ : iint128 :=
    iint128_from_iint8 (iint8v_5) in 
  let _ : iint8 :=
    iint8_from_iint128 (iint128v_9) in 
  let _ : iint128 :=
    iint128_from_iint16 (iint16v_6) in 
  let _ : iint16 :=
    iint16_from_iint128 (iint128v_9) in 
  let _ : iint128 :=
    iint128_from_iint32 (iint32v_7) in 
  let _ : iint32 :=
    iint32_from_iint128 (iint128v_9) in 
  let _ : iint128 :=
    iint128_from_iint64 (iint64v_8) in 
  let _ : iint64 :=
    iint64_from_iint128 (iint128v_9) in 
  let _ : iint64 :=
    iint64_from_iint8 (iint8v_5) in 
  let _ : iint8 :=
    iint8_from_iint64 (iint64v_8) in 
  let _ : iint64 :=
    iint64_from_iint16 (iint16v_6) in 
  let _ : iint16 :=
    iint16_from_iint64 (iint64v_8) in 
  let _ : iint64 :=
    iint64_from_iint32 (iint32v_7) in 
  let _ : iint32 :=
    iint32_from_iint64 (iint64v_8) in 
  let _ : iint32 :=
    iint32_from_iint8 (iint8v_5) in 
  let _ : iint8 :=
    iint8_from_iint32 (iint32v_7) in 
  let _ : iint32 :=
    iint32_from_iint16 (iint16v_6) in 
  let _ : iint16 :=
    iint16_from_iint32 (iint32v_7) in 
  let _ : iint16 :=
    iint16_from_iint8 (iint8v_5) in 
  let _ : iint8 :=
    iint8_from_iint16 (iint16v_6) in 
  tt.

