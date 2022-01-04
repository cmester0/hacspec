(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition build_irreducible (p_0 : uint_size) : seq int128 :=
  let irr_1 : seq int128 :=
    seq_new_ (default) ((p_0) + (usize 1)) in 
  let irr_1 :=
    seq_upd irr_1 (usize 0) (- (@repr WORDSIZE128 1)) in 
  let irr_1 :=
    seq_upd irr_1 (usize 1) (- (@repr WORDSIZE128 1)) in 
  let irr_1 :=
    seq_upd irr_1 (p_0) (@repr WORDSIZE128 1) in 
  irr_1.

Definition round_to_3 (poly_2 : seq int128) (q_3 : int128) : seq int128 :=
  let result_4 : seq int128 :=
    (poly_2) in 
  let q_12_5 : int128 :=
    ((q_3) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let result_4 :=
    foldi (usize 0) (seq_len (poly_2)) (fun i_6 result_4 =>
      let '(result_4) :=
        if (seq_index (poly_2) (i_6)) >.? (q_12_5):bool then (let result_4 :=
            seq_upd result_4 (i_6) ((seq_index (poly_2) (i_6)) .- (q_3)) in 
          (result_4)) else ((result_4)) in 
      (result_4))
    result_4 in 
  let result_4 :=
    foldi (usize 0) (seq_len (result_4)) (fun i_7 result_4 =>
      let '(result_4) :=
        if ((seq_index (result_4) (i_7)) .% (@repr WORDSIZE128 3)) !=.? (
          @repr WORDSIZE128 0):bool then (let result_4 :=
            seq_upd result_4 (i_7) ((seq_index (result_4) (i_7)) .- (
                @repr WORDSIZE128 1)) in 
          let '(result_4) :=
            if ((seq_index (result_4) (i_7)) .% (@repr WORDSIZE128 3)) !=.? (
              @repr WORDSIZE128 0):bool then (let result_4 :=
                seq_upd result_4 (i_7) ((seq_index (result_4) (i_7)) .+ (
                    @repr WORDSIZE128 2)) in 
              (result_4)) else ((result_4)) in 
          (result_4)) else ((result_4)) in 
      (result_4))
    result_4 in 
  result_4.

Definition encrypt
  (r_8 : seq int128)
  (h_9 : seq int128)
  (q_10 : int128)
  (irreducible_11 : seq int128)
  : seq int128 :=
  let pre_12 : seq int128 :=
    mul_poly_irr (r_8) (h_9) (irreducible_11) (q_10) in 
  round_to_3 (pre_12) (q_10).

Definition ntru_prime_653_encrypt
  (r_13 : seq int128)
  (h_14 : seq int128)
  : seq int128 :=
  let p_15 : uint_size :=
    usize 653 in 
  let q_16 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_17 : uint_size :=
    usize 288 in 
  let irreducible_18 : seq int128 :=
    build_irreducible (p_15) in 
  encrypt (r_13) (h_14) (q_16) (irreducible_18).

Definition ntru_prime_653_decrypt
  (c_19 : seq int128)
  (key_f_20 : seq int128)
  (key_v_21 : seq int128)
  : (seq int128 × bool) :=
  let p_22 : uint_size :=
    usize 653 in 
  let q_23 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_24 : uint_size :=
    usize 288 in 
  let irreducible_25 : seq int128 :=
    build_irreducible (p_22) in 
  let f_c_26 : seq int128 :=
    mul_poly_irr (key_f_20) (c_19) (irreducible_25) (q_23) in 
  let f_3_c_and_decryption_ok_27 : (seq int128 × bool) :=
    poly_to_ring (irreducible_25) (add_poly (f_c_26) (add_poly (f_c_26) (
          f_c_26) (q_23)) (q_23)) (q_23) in 
  let '(f_3_c_28, ok_decrypt_29) :=
    f_3_c_and_decryption_ok_27 in 
  let f_3_c_30 : seq int128 :=
    f_3_c_28 in 
  let q_12_31 : int128 :=
    ((q_23) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let f_3_c_30 :=
    foldi (usize 0) (seq_len (f_3_c_30)) (fun i_32 f_3_c_30 =>
      let '(f_3_c_30) :=
        if (seq_index (f_3_c_30) (i_32)) >.? (q_12_31):bool then (
          let f_3_c_30 :=
            seq_upd f_3_c_30 (i_32) ((seq_index (f_3_c_30) (i_32)) .- (
                q_23)) in 
          (f_3_c_30)) else ((f_3_c_30)) in 
      (f_3_c_30))
    f_3_c_30 in 
  let e_33 : seq int128 :=
    seq_new_ (default) (seq_len (f_3_c_30)) in 
  let e_33 :=
    foldi (usize 0) (seq_len (e_33)) (fun i_34 e_33 =>
      let e_33 :=
        seq_upd e_33 (i_34) ((seq_index (f_3_c_30) (i_34)) .% (
            @repr WORDSIZE128 3)) in 
      (e_33))
    e_33 in 
  let e_33 :=
    make_positive (e_33) (@repr WORDSIZE128 3) in 
  let r_35 : seq int128 :=
    mul_poly_irr (e_33) (key_v_21) (irreducible_25) (@repr WORDSIZE128 3) in 
  let r_35 :=
    foldi (usize 0) (seq_len (r_35)) (fun i_36 r_35 =>
      let '(r_35) :=
        if (seq_index (r_35) (i_36)) =.? (@repr WORDSIZE128 2):bool then (
          let r_35 :=
            seq_upd r_35 (i_36) (- (@repr WORDSIZE128 1)) in 
          (r_35)) else ((r_35)) in 
      (r_35))
    r_35 in 
  (r_35, ok_decrypt_29).

