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

Require Import Hacspec_Edwards25519.
Export Hacspec_Edwards25519.

Require Import Hacspec_Sha512.
Export Hacspec_Sha512.

Definition b_in_bytes_v : uint_size :=
  usize 64.

Definition s_in_bytes_v : uint_size :=
  usize 128.

Definition l_v : uint_size :=
  usize 48.

Definition j_v : int128 :=
  @repr WORDSIZE128 486662.

Definition z_v : int128 :=
  @repr WORDSIZE128 2.

Definition arr_ed25519_field_element_t := nseq (uint64) (usize 4).

Definition ed_field_hash_canvas_t := nseq (int8) (64).
Definition ed_field_hash_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Inductive error_t :=
| ExpandMessageAbort : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | ExpandMessageAbort => match y with | ExpandMessageAbort=> true end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Notation "'seq_ed_result_t'" := ((
  result seq ed25519_field_element_t error_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((result ed_point_t error_t)) : hacspec_scope.

Definition p_1_2_v : arr_ed25519_field_element_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 4611686018427387903) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551606) : int64
      ] in  l).

Definition p_3_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1152921504606846975) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551614) : int64
      ] in  l).

Definition p_5_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1152921504606846975) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551613) : int64
      ] in  l).

Definition expand_message_xmd
  (msg_2140 : byte_seq)
  (dst_2141 : byte_seq)
  (len_in_bytes_2142 : uint_size)
  
  : byte_seq_result_t :=
  let ell_2143 : uint_size :=
    (((len_in_bytes_2142) + (b_in_bytes_v)) - (usize 1)) / (b_in_bytes_v) in 
  let result_2144 : (result byte_seq error_t) :=
    @Err byte_seq error_t (ExpandMessageAbort) in 
  let '(result_2144) :=
    if negb ((((ell_2143) >.? (usize 255)) || ((len_in_bytes_2142) >.? (
            usize 65535))) || ((seq_len (dst_2141)) >.? (
          usize 255))):bool then (let dst_prime_2145 : seq uint8 :=
        seq_push (dst_2141) (uint8_from_usize (seq_len (dst_2141))) in 
      let z_pad_2146 : seq uint8 :=
        seq_new_ (default : uint8) (s_in_bytes_v) in 
      let l_i_b_str_2147 : seq uint8 :=
        seq_new_ (default : uint8) (usize 2) in 
      let l_i_b_str_2147 :=
        seq_upd l_i_b_str_2147 (usize 0) (uint8_from_usize ((
              len_in_bytes_2142) / (usize 256))) in 
      let l_i_b_str_2147 :=
        seq_upd l_i_b_str_2147 (usize 1) (uint8_from_usize (
            len_in_bytes_2142)) in 
      let msg_prime_2148 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (z_pad_2146) (
                msg_2140)) (l_i_b_str_2147)) (seq_new_ (default : uint8) (
              usize 1))) (dst_prime_2145) in 
      let b_0_2149 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (msg_prime_2148))) in 
      let b_i_2150 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push (b_0_2149) (
                secret (@repr WORDSIZE8 1) : int8)) (dst_prime_2145)))) in 
      let uniform_bytes_2151 : seq uint8 :=
        seq_from_seq (b_i_2150) in 
      let '(b_i_2150, uniform_bytes_2151) :=
        foldi (usize 2) ((ell_2143) + (usize 1)) (fun i_2152 '(
            b_i_2150,
            uniform_bytes_2151
          ) =>
          let t_2153 : seq uint8 :=
            seq_from_seq (b_0_2149) in 
          let b_i_2150 :=
            seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                      t_2153) seq_xor (b_i_2150)) (uint8_from_usize (i_2152))) (
                  dst_prime_2145)))) in 
          let uniform_bytes_2151 :=
            seq_concat (uniform_bytes_2151) (b_i_2150) in 
          (b_i_2150, uniform_bytes_2151))
        (b_i_2150, uniform_bytes_2151) in 
      let result_2144 :=
        @Ok byte_seq error_t (seq_truncate (uniform_bytes_2151) (
            len_in_bytes_2142)) in 
      (result_2144)) else ((result_2144)) in 
  result_2144.


Definition ed_hash_to_field
  (msg_2154 : byte_seq)
  (dst_2155 : byte_seq)
  (count_2156 : uint_size)
  
  : seq_ed_result_t :=
  let len_in_bytes_2157 : uint_size :=
    (count_2156) * (l_v) in 
  bind (expand_message_xmd (msg_2154) (dst_2155) (len_in_bytes_2157)) (
    fun uniform_bytes_2158 => let output_2159 : seq ed25519_field_element_t :=
      seq_new_ (default : ed25519_field_element_t) (count_2156) in 
    let output_2159 :=
      foldi (usize 0) (count_2156) (fun i_2160 output_2159 =>
        let elm_offset_2161 : uint_size :=
          (l_v) * (i_2160) in 
        let tv_2162 : seq uint8 :=
          seq_slice (uniform_bytes_2158) (elm_offset_2161) (l_v) in 
        let u_i_2163 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                nat_mod_from_byte_seq_be (tv_2162) : ed_field_hash_t)) (
              usize 32) (usize 32)) : ed25519_field_element_t in 
        let output_2159 :=
          seq_upd output_2159 (i_2160) (u_i_2163) in 
        (output_2159))
      output_2159 in 
    @Ok seq ed25519_field_element_t error_t (output_2159)).


Definition ed_is_square (x_2164 : ed25519_field_element_t)  : bool :=
  let c1_2165 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_1_2_v)) : ed25519_field_element_t in 
  let tv_2166 : ed25519_field_element_t :=
    nat_mod_pow_self (x_2164) (c1_2165) in 
  ((tv_2166) =.? (nat_mod_zero )) || ((tv_2166) =.? (nat_mod_one )).


Definition sgn0_m_eq_1 (x_2167 : ed25519_field_element_t)  : bool :=
  ((x_2167) rem (nat_mod_two )) =.? (nat_mod_one ).


Definition ed_clear_cofactor (x_2168 : ed_point_t)  : ed_point_t :=
  point_mul_by_cofactor (x_2168).


Definition cmov
  (a_2169 : ed25519_field_element_t)
  (b_2170 : ed25519_field_element_t)
  (c_2171 : bool)
  
  : ed25519_field_element_t :=
  (if (c_2171):bool then (b_2170) else (a_2169)).


Definition xor (a_2172 : bool) (b_2173 : bool)  : bool :=
  (if (a_2172):bool then ((if (b_2173):bool then (false) else (true))) else ((
        if (b_2173):bool then (true) else (false)))).


Definition curve25519_to_edwards25519 (p_2174 : ed_point_t)  : ed_point_t :=
  let '(s_2175, t_2176, _, _) :=
    point_normalize (p_2174) in 
  let one_2177 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2178 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2179 : ed25519_field_element_t :=
    (s_2175) +% (one_2177) in 
  let tv2_2180 : ed25519_field_element_t :=
    (tv1_2179) *% (t_2176) in 
  let tv2_2181 : ed25519_field_element_t :=
    nat_mod_inv (tv2_2180) in 
  let v_2182 : ed25519_field_element_t :=
    (tv2_2181) *% (tv1_2179) in 
  let v_2183 : ed25519_field_element_t :=
    (v_2182) *% (s_2175) in 
  let w_2184 : ed25519_field_element_t :=
    (tv2_2181) *% (t_2176) in 
  let tv1_2185 : ed25519_field_element_t :=
    (s_2175) -% (one_2177) in 
  let w_2186 : ed25519_field_element_t :=
    (w_2184) *% (tv1_2185) in 
  let e_2187 : bool :=
    (tv2_2181) =.? (zero_2178) in 
  let w_2188 : ed25519_field_element_t :=
    cmov (w_2186) (one_2177) (e_2187) in 
  let c_2189 : ed25519_field_element_t :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (
        @repr WORDSIZE128 486664) : ed25519_field_element_t) in 
  let sq_2190 : (option ed25519_field_element_t) :=
    sqrt (c_2189) in 
  let v_2191 : ed25519_field_element_t :=
    (v_2183) *% (option_unwrap (sq_2190)) in 
  (v_2191, w_2188, one_2177, (v_2191) *% (w_2188)).


Definition map_to_curve_elligator2
  (u_2192 : ed25519_field_element_t)
  
  : ed_point_t :=
  let j_2193 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2194 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2195 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2196 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let x1_2197 : ed25519_field_element_t :=
    ((zero_2196) -% (j_2193)) *% (nat_mod_inv ((one_2195) +% (((z_2194) *% (
              u_2192)) *% (u_2192)))) in 
  let '(x1_2197) :=
    if (x1_2197) =.? (zero_2196):bool then (let x1_2197 :=
        (zero_2196) -% (j_2193) in 
      (x1_2197)) else ((x1_2197)) in 
  let gx1_2198 : ed25519_field_element_t :=
    ((((x1_2197) *% (x1_2197)) *% (x1_2197)) +% (((j_2193) *% (x1_2197)) *% (
          x1_2197))) +% (x1_2197) in 
  let x2_2199 : ed25519_field_element_t :=
    ((zero_2196) -% (x1_2197)) -% (j_2193) in 
  let gx2_2200 : ed25519_field_element_t :=
    ((((x2_2199) *% (x2_2199)) *% (x2_2199)) +% ((j_2193) *% ((x2_2199) *% (
            x2_2199)))) +% (x2_2199) in 
  let x_2201 : ed25519_field_element_t :=
    zero_2196 in 
  let y_2202 : ed25519_field_element_t :=
    zero_2196 in 
  let '(x_2201, y_2202) :=
    if ed_is_square (gx1_2198):bool then (let x_2201 :=
        x1_2197 in 
      let y_2202 :=
        option_unwrap (sqrt (gx1_2198)) in 
      let '(y_2202) :=
        if negb (sgn0_m_eq_1 (y_2202)):bool then (let y_2202 :=
            (zero_2196) -% (y_2202) in 
          (y_2202)) else ((y_2202)) in 
      (x_2201, y_2202)) else (let x_2201 :=
        x2_2199 in 
      let y_2202 :=
        option_unwrap (sqrt (gx2_2200)) in 
      let '(y_2202) :=
        if sgn0_m_eq_1 (y_2202):bool then (let y_2202 :=
            (zero_2196) -% (y_2202) in 
          (y_2202)) else ((y_2202)) in 
      (x_2201, y_2202)) in 
  let s_2203 : ed25519_field_element_t :=
    x_2201 in 
  let t_2204 : ed25519_field_element_t :=
    y_2202 in 
  (s_2203, t_2204, one_2195, (s_2203) *% (t_2204)).


Definition map_to_curve_elligator2_straight
  (u_2205 : ed25519_field_element_t)
  
  : ed_point_t :=
  let j_2206 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2207 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2208 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2209 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2210 : ed25519_field_element_t :=
    (u_2205) *% (u_2205) in 
  let tv1_2211 : ed25519_field_element_t :=
    (z_2207) *% (tv1_2210) in 
  let e1_2212 : bool :=
    (tv1_2211) =.? ((zero_2209) -% (one_2208)) in 
  let tv1_2213 : ed25519_field_element_t :=
    cmov (tv1_2211) (zero_2209) (e1_2212) in 
  let x1_2214 : ed25519_field_element_t :=
    (tv1_2213) +% (one_2208) in 
  let x1_2215 : ed25519_field_element_t :=
    nat_mod_inv (x1_2214) in 
  let x1_2216 : ed25519_field_element_t :=
    ((zero_2209) -% (j_2206)) *% (x1_2215) in 
  let gx1_2217 : ed25519_field_element_t :=
    (x1_2216) +% (j_2206) in 
  let gx1_2218 : ed25519_field_element_t :=
    (gx1_2217) *% (x1_2216) in 
  let gx1_2219 : ed25519_field_element_t :=
    (gx1_2218) +% (one_2208) in 
  let gx1_2220 : ed25519_field_element_t :=
    (gx1_2219) *% (x1_2216) in 
  let x2_2221 : ed25519_field_element_t :=
    ((zero_2209) -% (x1_2216)) -% (j_2206) in 
  let gx2_2222 : ed25519_field_element_t :=
    (tv1_2213) *% (gx1_2220) in 
  let e2_2223 : bool :=
    ed_is_square (gx1_2220) in 
  let x_2224 : ed25519_field_element_t :=
    cmov (x2_2221) (x1_2216) (e2_2223) in 
  let y2_2225 : ed25519_field_element_t :=
    cmov (gx2_2222) (gx1_2220) (e2_2223) in 
  let y_2226 : ed25519_field_element_t :=
    option_unwrap (sqrt (y2_2225)) in 
  let e3_2227 : bool :=
    sgn0_m_eq_1 (y_2226) in 
  let y_2228 : ed25519_field_element_t :=
    cmov (y_2226) ((zero_2209) -% (y_2226)) (xor (e2_2223) (e3_2227)) in 
  let s_2229 : ed25519_field_element_t :=
    x_2224 in 
  let t_2230 : ed25519_field_element_t :=
    y_2228 in 
  (s_2229, t_2230, one_2208, (s_2229) *% (t_2230)).


Definition map_to_curve_elligator2_curve25519
  (u_2231 : ed25519_field_element_t)
  
  : ed_point_t :=
  let j_2232 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2233 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2234 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2235 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2236 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_3_8_v)) : ed25519_field_element_t in 
  let c2_2237 : ed25519_field_element_t :=
    nat_mod_pow_self (two_2235) (c1_2236) in 
  let c3_2238 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2233) -% (one_2234))) in 
  let c4_2239 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_5_8_v)) : ed25519_field_element_t in 
  let tv1_2240 : ed25519_field_element_t :=
    (u_2231) *% (u_2231) in 
  let tv1_2241 : ed25519_field_element_t :=
    (two_2235) *% (tv1_2240) in 
  let xd_2242 : ed25519_field_element_t :=
    (tv1_2241) +% (one_2234) in 
  let x1n_2243 : ed25519_field_element_t :=
    (zero_2233) -% (j_2232) in 
  let tv2_2244 : ed25519_field_element_t :=
    (xd_2242) *% (xd_2242) in 
  let gxd_2245 : ed25519_field_element_t :=
    (tv2_2244) *% (xd_2242) in 
  let gx1_2246 : ed25519_field_element_t :=
    (j_2232) *% (tv1_2241) in 
  let gx1_2247 : ed25519_field_element_t :=
    (gx1_2246) *% (x1n_2243) in 
  let gx1_2248 : ed25519_field_element_t :=
    (gx1_2247) +% (tv2_2244) in 
  let gx1_2249 : ed25519_field_element_t :=
    (gx1_2248) *% (x1n_2243) in 
  let tv3_2250 : ed25519_field_element_t :=
    (gxd_2245) *% (gxd_2245) in 
  let tv2_2251 : ed25519_field_element_t :=
    (tv3_2250) *% (tv3_2250) in 
  let tv3_2252 : ed25519_field_element_t :=
    (tv3_2250) *% (gxd_2245) in 
  let tv3_2253 : ed25519_field_element_t :=
    (tv3_2252) *% (gx1_2249) in 
  let tv2_2254 : ed25519_field_element_t :=
    (tv2_2251) *% (tv3_2253) in 
  let y11_2255 : ed25519_field_element_t :=
    nat_mod_pow_self (tv2_2254) (c4_2239) in 
  let y11_2256 : ed25519_field_element_t :=
    (y11_2255) *% (tv3_2253) in 
  let y12_2257 : ed25519_field_element_t :=
    (y11_2256) *% (c3_2238) in 
  let tv2_2258 : ed25519_field_element_t :=
    (y11_2256) *% (y11_2256) in 
  let tv2_2259 : ed25519_field_element_t :=
    (tv2_2258) *% (gxd_2245) in 
  let e1_2260 : bool :=
    (tv2_2259) =.? (gx1_2249) in 
  let y1_2261 : ed25519_field_element_t :=
    cmov (y12_2257) (y11_2256) (e1_2260) in 
  let x2n_2262 : ed25519_field_element_t :=
    (x1n_2243) *% (tv1_2241) in 
  let y21_2263 : ed25519_field_element_t :=
    (y11_2256) *% (u_2231) in 
  let y21_2264 : ed25519_field_element_t :=
    (y21_2263) *% (c2_2237) in 
  let y22_2265 : ed25519_field_element_t :=
    (y21_2264) *% (c3_2238) in 
  let gx2_2266 : ed25519_field_element_t :=
    (gx1_2249) *% (tv1_2241) in 
  let tv2_2267 : ed25519_field_element_t :=
    (y21_2264) *% (y21_2264) in 
  let tv2_2268 : ed25519_field_element_t :=
    (tv2_2267) *% (gxd_2245) in 
  let e2_2269 : bool :=
    (tv2_2268) =.? (gx2_2266) in 
  let y2_2270 : ed25519_field_element_t :=
    cmov (y22_2265) (y21_2264) (e2_2269) in 
  let tv2_2271 : ed25519_field_element_t :=
    (y1_2261) *% (y1_2261) in 
  let tv2_2272 : ed25519_field_element_t :=
    (tv2_2271) *% (gxd_2245) in 
  let e3_2273 : bool :=
    (tv2_2272) =.? (gx1_2249) in 
  let xn_2274 : ed25519_field_element_t :=
    cmov (x2n_2262) (x1n_2243) (e3_2273) in 
  let y_2275 : ed25519_field_element_t :=
    cmov (y2_2270) (y1_2261) (e3_2273) in 
  let e4_2276 : bool :=
    sgn0_m_eq_1 (y_2275) in 
  let y_2277 : ed25519_field_element_t :=
    cmov (y_2275) ((zero_2233) -% (y_2275)) (xor (e3_2273) (e4_2276)) in 
  (xn_2274, xd_2242, y_2277, one_2234).


Definition map_to_curve_elligator2_edwards25519
  (u_2278 : ed25519_field_element_t)
  
  : ed_point_t :=
  let j_2279 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2280 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2281 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2282 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2283 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2280) -% ((j_2279) +% (two_2282)))) in 
  let '(xmn_2284, xmd_2285, ymn_2286, ymd_2287) :=
    map_to_curve_elligator2_curve25519 (u_2278) in 
  let xn_2288 : ed25519_field_element_t :=
    (xmn_2284) *% (ymd_2287) in 
  let xn_2289 : ed25519_field_element_t :=
    (xn_2288) *% (c1_2283) in 
  let xd_2290 : ed25519_field_element_t :=
    (xmd_2285) *% (ymn_2286) in 
  let yn_2291 : ed25519_field_element_t :=
    (xmn_2284) -% (xmd_2285) in 
  let yd_2292 : ed25519_field_element_t :=
    (xmn_2284) +% (xmd_2285) in 
  let tv1_2293 : ed25519_field_element_t :=
    (xd_2290) *% (yd_2292) in 
  let e_2294 : bool :=
    (tv1_2293) =.? (zero_2280) in 
  let xn_2295 : ed25519_field_element_t :=
    cmov (xn_2289) (zero_2280) (e_2294) in 
  let xd_2296 : ed25519_field_element_t :=
    cmov (xd_2290) (one_2281) (e_2294) in 
  let yn_2297 : ed25519_field_element_t :=
    cmov (yn_2291) (one_2281) (e_2294) in 
  let yd_2298 : ed25519_field_element_t :=
    cmov (yd_2292) (one_2281) (e_2294) in 
  let x_2299 : ed25519_field_element_t :=
    (xn_2295) *% (nat_mod_inv (xd_2296)) in 
  let y_2300 : ed25519_field_element_t :=
    (yn_2297) *% (nat_mod_inv (yd_2298)) in 
  (x_2299, y_2300, one_2281, (x_2299) *% (y_2300)).


Definition map_to_curve_elligator2_edwards
  (u_2301 : ed25519_field_element_t)
  
  : ed_point_t :=
  let st_2302 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    map_to_curve_elligator2 (u_2301) in 
  curve25519_to_edwards25519 (st_2302).


Definition ed_encode_to_curve
  (msg_2303 : byte_seq)
  (dst_2304 : byte_seq)
  
  : ed_point_result_t :=
  bind (ed_hash_to_field (msg_2303) (dst_2304) (usize 1)) (fun u_2305 =>
    let q_2306 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      map_to_curve_elligator2_edwards (seq_index (u_2305) (usize 0)) in 
    @Ok ed_point_t error_t (ed_clear_cofactor (q_2306))).


