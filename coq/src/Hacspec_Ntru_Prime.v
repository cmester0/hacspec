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

Definition build_irreducible (p_1106 : uint_size)  : seq int128 :=
  let irr_1107 : seq int128 :=
    seq_new_ (default : int128) ((p_1106) + (usize 1)) in 
  let irr_1107 :=
    seq_upd irr_1107 (usize 0) (- (@repr WORDSIZE128 (1))) in 
  let irr_1107 :=
    seq_upd irr_1107 (usize 1) (- (@repr WORDSIZE128 (1))) in 
  let irr_1107 :=
    seq_upd irr_1107 (p_1106) (@repr WORDSIZE128 (1)) in 
  irr_1107.


Definition round_to_3
  (poly_1108 : seq int128)
  (q_1109 : int128)
  
  : seq int128 :=
  let result_1110 : seq int128 :=
    (poly_1108) in 
  let q_12_1111 : int128 :=
    ((q_1109) .- (@repr WORDSIZE128 (1))) ./ (@repr WORDSIZE128 (2)) in 
  let result_1110 :=
    foldi (usize 0) (seq_len (poly_1108)) (fun i_1112 result_1110 =>
      let '(result_1110) :=
        if (seq_index (poly_1108) (i_1112)) >.? (q_12_1111):bool then (
          let result_1110 :=
            seq_upd result_1110 (i_1112) ((seq_index (poly_1108) (i_1112)) .- (
                q_1109)) in 
          (result_1110)) else ((result_1110)) in 
      (result_1110))
    result_1110 in 
  let result_1110 :=
    foldi (usize 0) (seq_len (result_1110)) (fun i_1113 result_1110 =>
      let '(result_1110) :=
        if ((seq_index (result_1110) (i_1113)) .% (
            @repr WORDSIZE128 (3))) !=.? (@repr WORDSIZE128 (0)):bool then (
          let result_1110 :=
            seq_upd result_1110 (i_1113) ((seq_index (result_1110) (
                  i_1113)) .- (@repr WORDSIZE128 (1))) in 
          let '(result_1110) :=
            if ((seq_index (result_1110) (i_1113)) .% (
                @repr WORDSIZE128 (3))) !=.? (@repr WORDSIZE128 (0)):bool then (
              let result_1110 :=
                seq_upd result_1110 (i_1113) ((seq_index (result_1110) (
                      i_1113)) .+ (@repr WORDSIZE128 (2))) in 
              (result_1110)) else ((result_1110)) in 
          (result_1110)) else ((result_1110)) in 
      (result_1110))
    result_1110 in 
  result_1110.


Definition encrypt
  (r_1114 : seq int128)
  (h_1115 : seq int128)
  (q_1116 : int128)
  (irreducible_1117 : seq int128)
  
  : seq int128 :=
  let pre_1118 : seq int128 :=
    mul_poly_irr (r_1114) (h_1115) (irreducible_1117) (q_1116) in 
  round_to_3 (pre_1118) (q_1116).


Definition ntru_prime_653_encrypt
  (r_1119 : seq int128)
  (h_1120 : seq int128)
  
  : seq int128 :=
  let p_1121 : uint_size :=
    usize 653 in 
  let q_1122 : int128 :=
    @repr WORDSIZE128 (4621) in 
  let w_1123 : uint_size :=
    usize 288 in 
  let irreducible_1124 : seq int128 :=
    build_irreducible (p_1121) in 
  encrypt (r_1119) (h_1120) (q_1122) (irreducible_1124).


Definition ntru_prime_653_decrypt
  (c_1125 : seq int128)
  (key_f_1126 : seq int128)
  (key_v_1127 : seq int128)
  
  : (seq int128 '× bool) :=
  let p_1128 : uint_size :=
    usize 653 in 
  let q_1129 : int128 :=
    @repr WORDSIZE128 (4621) in 
  let w_1130 : uint_size :=
    usize 288 in 
  let irreducible_1131 : seq int128 :=
    build_irreducible (p_1128) in 
  let f_c_1132 : seq int128 :=
    mul_poly_irr (key_f_1126) (c_1125) (irreducible_1131) (q_1129) in 
  let f_3_c_and_decryption_ok_1133 : (seq int128 '× bool) :=
    poly_to_ring (irreducible_1131) (add_poly (f_c_1132) (add_poly (f_c_1132) (
          f_c_1132) (q_1129)) (q_1129)) (q_1129) in 
  let '(f_3_c_1134, ok_decrypt_1135) :=
    f_3_c_and_decryption_ok_1133 in 
  let f_3_c_1136 : seq int128 :=
    f_3_c_1134 in 
  let q_12_1137 : int128 :=
    ((q_1129) .- (@repr WORDSIZE128 (1))) ./ (@repr WORDSIZE128 (2)) in 
  let f_3_c_1136 :=
    foldi (usize 0) (seq_len (f_3_c_1136)) (fun i_1138 f_3_c_1136 =>
      let '(f_3_c_1136) :=
        if (seq_index (f_3_c_1136) (i_1138)) >.? (q_12_1137):bool then (
          let f_3_c_1136 :=
            seq_upd f_3_c_1136 (i_1138) ((seq_index (f_3_c_1136) (i_1138)) .- (
                q_1129)) in 
          (f_3_c_1136)) else ((f_3_c_1136)) in 
      (f_3_c_1136))
    f_3_c_1136 in 
  let e_1139 : seq int128 :=
    seq_new_ (default : int128) (seq_len (f_3_c_1136)) in 
  let e_1139 :=
    foldi (usize 0) (seq_len (e_1139)) (fun i_1140 e_1139 =>
      let e_1139 :=
        seq_upd e_1139 (i_1140) ((seq_index (f_3_c_1136) (i_1140)) .% (
            @repr WORDSIZE128 (3))) in 
      (e_1139))
    e_1139 in 
  let e_1139 :=
    make_positive (e_1139) (@repr WORDSIZE128 (3)) in 
  let r_1141 : seq int128 :=
    mul_poly_irr (e_1139) (key_v_1127) (irreducible_1131) (
      @repr WORDSIZE128 (3)) in 
  let r_1141 :=
    foldi (usize 0) (seq_len (r_1141)) (fun i_1142 r_1141 =>
      let '(r_1141) :=
        if (seq_index (r_1141) (i_1142)) =.? (@repr WORDSIZE128 (2)):bool then (
          let r_1141 :=
            seq_upd r_1141 (i_1142) (- (@repr WORDSIZE128 (1))) in 
          (r_1141)) else ((r_1141)) in 
      (r_1141))
    r_1141 in 
  (r_1141, ok_decrypt_1135).


