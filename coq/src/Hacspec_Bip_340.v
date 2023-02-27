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

Require Import Hacspec_Sha256.
Export Hacspec_Sha256.

Inductive error_t :=
| InvalidSecretKey : error_t
| InvalidNonceGenerated : error_t
| InvalidPublicKey : error_t
| InvalidXCoordinate : error_t
| InvalidSignature : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | InvalidSecretKey => match y with | InvalidSecretKey=> true | _ => false end
   | InvalidNonceGenerated =>
       match y with
       | InvalidNonceGenerated=> true
       | _ => false
       end
   | InvalidPublicKey => match y with | InvalidPublicKey=> true | _ => false end
   | InvalidXCoordinate =>
       match y with
       | InvalidXCoordinate=> true
       | _ => false
       end
   | InvalidSignature => match y with | InvalidSignature=> true | _ => false end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Definition field_canvas_t := nseq (int8) (32).
Definition field_element_t :=
  nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141.

Definition big_integer_t := nat_mod pow2 256.

Notation "'affine_point_t'" := ((field_element_t '× field_element_t
)) : hacspec_scope.

Definition p_bytes32_t := nseq (int8) (usize 32).

Inductive point_t :=
| Affine : affine_point_t -> point_t
| AtInfinity : point_t.

Definition finite (p_2405 : point_t)  : (option affine_point_t) :=
  match p_2405 with
  | Affine (p_2406) => some (p_2406)
  | AtInfinity => @None affine_point_t
  end.


Definition x (p_2407 : affine_point_t)  : field_element_t :=
  let '(x_2408, _) :=
    p_2407 in 
  x_2408.


Definition y (p_2409 : affine_point_t)  : field_element_t :=
  let '(_, y_2410) :=
    p_2409 in 
  y_2410.


Definition has_even_y (p_2411 : affine_point_t)  : bool :=
  ((y (p_2411)) rem (nat_mod_two )) =.? (nat_mod_zero ).


Definition sqrt (y_2412 : field_element_t)  : (option field_element_t) :=
  let p1_4_2413 : field_element_t :=
    nat_mod_from_public_byte_seq_be (array_from_list int8 (let l :=
          [
            @repr WORDSIZE8 63;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 191;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 12
          ] in  l)) in 
  let x_2414 : field_element_t :=
    nat_mod_pow_self (y_2412) (p1_4_2413) in 
  (if ((nat_mod_pow_self (x_2414) (nat_mod_two )) =.? (y_2412)):bool then (
      some (x_2414)) else (@None field_element_t)).


Definition lift_x
  (x_2415 : field_element_t)
  
  : (result affine_point_t error_t) :=
  let one_2416 : field_element_t :=
    nat_mod_one  in 
  let two_2417 : field_element_t :=
    nat_mod_two  in 
  let three_2418 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  let seven_2419 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 7) : field_element_t in 
  let y_sq_2420 : field_element_t :=
    (nat_mod_pow_self (x_2415) (three_2418)) +% (seven_2419) in 
  bind (option_ok_or (sqrt (y_sq_2420)) (InvalidXCoordinate)) (fun y_2421 =>
    let '(y_2421) :=
      if ((y_2421) rem (two_2417)) =.? (one_2416):bool then (let y_2421 :=
          (nat_mod_zero ) -% (y_2421) in 
        (y_2421)) else ((y_2421)) in 
    @Ok affine_point_t error_t ((x_2415, y_2421))).


Definition compute_lam
  (p1_2422 : affine_point_t)
  (p2_2423 : affine_point_t)
  
  : field_element_t :=
  let three_2424 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  (if ((p1_2422) !=.? (p2_2423)):bool then (((y (p2_2423)) -% (y (
            p1_2422))) *% (nat_mod_pow_self ((x (p2_2423)) -% (x (p1_2422))) ((
            nat_mod_zero ) -% (nat_mod_two )))) else ((((three_2424) *% (x (
              p1_2422))) *% (x (p1_2422))) *% (nat_mod_pow_self ((
            nat_mod_two ) *% (y (p1_2422))) ((nat_mod_zero ) -% (
            nat_mod_two ))))).


Definition point_add (p1_2425 : point_t) (p2_2426 : point_t)  : point_t :=
  let result_2427 : point_t :=
    AtInfinity in 
  let '(result_2427) :=
    if option_is_none (finite (p1_2425)):bool then (let result_2427 :=
        p2_2426 in 
      (result_2427)) else (let '(result_2427) :=
        if option_is_none (finite (p2_2426)):bool then (let result_2427 :=
            p1_2425 in 
          (result_2427)) else (let p1_2428 : (
              field_element_t '×
              field_element_t
            ) :=
            option_unwrap (finite (p1_2425)) in 
          let p2_2429 : (field_element_t '× field_element_t) :=
            option_unwrap (finite (p2_2426)) in 
          let '(result_2427) :=
            if negb (((x (p1_2428)) =.? (x (p2_2429))) && ((y (p1_2428)) !=.? (
                  y (p2_2429)))):bool then (let lam_2430 : field_element_t :=
                compute_lam (p1_2428) (p2_2429) in 
              let x3_2431 : field_element_t :=
                (((lam_2430) *% (lam_2430)) -% (x (p1_2428))) -% (x (
                    p2_2429)) in 
              let result_2427 :=
                Affine ((
                    x3_2431,
                    ((lam_2430) *% ((x (p1_2428)) -% (x3_2431))) -% (y (
                        p1_2428))
                  )) in 
              (result_2427)) else ((result_2427)) in 
          (result_2427)) in 
      (result_2427)) in 
  result_2427.


Definition point_mul (s_2432 : scalar_t) (p_2433 : point_t)  : point_t :=
  let p_2434 : point_t :=
    p_2433 in 
  let q_2435 : point_t :=
    AtInfinity in 
  let '(p_2434, q_2435) :=
    foldi (usize 0) (usize 256) (fun i_2436 '(p_2434, q_2435) =>
      let '(q_2435) :=
        if nat_mod_bit (s_2432) (i_2436):bool then (let q_2435 :=
            point_add (q_2435) (p_2434) in 
          (q_2435)) else ((q_2435)) in 
      let p_2434 :=
        point_add (p_2434) (p_2434) in 
      (p_2434, q_2435))
    (p_2434, q_2435) in 
  q_2435.


Definition point_mul_base (s_2437 : scalar_t)  : point_t :=
  let gx_2438 : p_bytes32_t :=
    array_from_list int8 (let l :=
        [
          @repr WORDSIZE8 121;
          @repr WORDSIZE8 190;
          @repr WORDSIZE8 102;
          @repr WORDSIZE8 126;
          @repr WORDSIZE8 249;
          @repr WORDSIZE8 220;
          @repr WORDSIZE8 187;
          @repr WORDSIZE8 172;
          @repr WORDSIZE8 85;
          @repr WORDSIZE8 160;
          @repr WORDSIZE8 98;
          @repr WORDSIZE8 149;
          @repr WORDSIZE8 206;
          @repr WORDSIZE8 135;
          @repr WORDSIZE8 11;
          @repr WORDSIZE8 7;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 155;
          @repr WORDSIZE8 252;
          @repr WORDSIZE8 219;
          @repr WORDSIZE8 45;
          @repr WORDSIZE8 206;
          @repr WORDSIZE8 40;
          @repr WORDSIZE8 217;
          @repr WORDSIZE8 89;
          @repr WORDSIZE8 242;
          @repr WORDSIZE8 129;
          @repr WORDSIZE8 91;
          @repr WORDSIZE8 22;
          @repr WORDSIZE8 248;
          @repr WORDSIZE8 23;
          @repr WORDSIZE8 152
        ] in  l) in 
  let gy_2439 : p_bytes32_t :=
    array_from_list int8 (let l :=
        [
          @repr WORDSIZE8 72;
          @repr WORDSIZE8 58;
          @repr WORDSIZE8 218;
          @repr WORDSIZE8 119;
          @repr WORDSIZE8 38;
          @repr WORDSIZE8 163;
          @repr WORDSIZE8 196;
          @repr WORDSIZE8 101;
          @repr WORDSIZE8 93;
          @repr WORDSIZE8 164;
          @repr WORDSIZE8 251;
          @repr WORDSIZE8 252;
          @repr WORDSIZE8 14;
          @repr WORDSIZE8 17;
          @repr WORDSIZE8 8;
          @repr WORDSIZE8 168;
          @repr WORDSIZE8 253;
          @repr WORDSIZE8 23;
          @repr WORDSIZE8 180;
          @repr WORDSIZE8 72;
          @repr WORDSIZE8 166;
          @repr WORDSIZE8 133;
          @repr WORDSIZE8 84;
          @repr WORDSIZE8 25;
          @repr WORDSIZE8 156;
          @repr WORDSIZE8 71;
          @repr WORDSIZE8 208;
          @repr WORDSIZE8 143;
          @repr WORDSIZE8 251;
          @repr WORDSIZE8 16;
          @repr WORDSIZE8 212;
          @repr WORDSIZE8 184
        ] in  l) in 
  let g_2440 : point_t :=
    Affine ((
        nat_mod_from_public_byte_seq_be (gx_2438),
        nat_mod_from_public_byte_seq_be (gy_2439)
      )) in 
  point_mul (s_2437) (g_2440).


Definition bytes32_t := nseq (uint8) (usize 32).

Notation "'secret_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'public_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'message_t'" := (bytes32_t) : hacspec_scope.

Notation "'aux_rand_t'" := (bytes32_t) : hacspec_scope.

Definition signature_t := nseq (uint8) (usize 64).

Definition tagged_hash
  (tag_2441 : public_byte_seq)
  (msg_2442 : byte_seq)
  
  : bytes32_t :=
  let tag_hash_2443 : seq uint8 :=
    array_to_be_bytes (sha256 (seq_from_public_seq (tag_2441))) in 
  let hash_2444 : sha256_digest_t :=
    sha256 (seq_concat (seq_concat (tag_hash_2443) (tag_hash_2443)) (
        msg_2442)) in 
  array_from_seq (32) (array_to_seq (hash_2444)).


Definition tagged_hash_aux_prefix_t := nseq (int8) (usize 11).

Definition bip0340_aux_v : tagged_hash_aux_prefix_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 97;
        @repr WORDSIZE8 117;
        @repr WORDSIZE8 120
      ] in  l).

Definition hash_aux (aux_rand_2445 : aux_rand_t)  : bytes32_t :=
  tagged_hash (seq_from_seq (array_to_seq (bip0340_aux_v))) (seq_from_seq (
      aux_rand_2445)).


Definition tagged_hash_nonce_prefix_t := nseq (int8) (usize 13).

Definition bip0340_nonce_v : tagged_hash_nonce_prefix_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 111;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 99;
        @repr WORDSIZE8 101
      ] in  l).

Definition hash_nonce
  (rand_2446 : bytes32_t)
  (pubkey_2447 : bytes32_t)
  (msg_2448 : message_t)
  
  : bytes32_t :=
  let c_2449 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rand_2446))) (
        array_to_seq (pubkey_2447))) (msg_2448) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_nonce_v))) (c_2449).


Definition tagged_hash_challenge_prefix_t := nseq (int8) (usize 17).

Definition bip0340_challenge_v : tagged_hash_challenge_prefix_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 99;
        @repr WORDSIZE8 104;
        @repr WORDSIZE8 97;
        @repr WORDSIZE8 108;
        @repr WORDSIZE8 108;
        @repr WORDSIZE8 101;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 103;
        @repr WORDSIZE8 101
      ] in  l).

Definition hash_challenge
  (rx_2450 : bytes32_t)
  (pubkey_2451 : bytes32_t)
  (msg_2452 : bytes32_t)
  
  : bytes32_t :=
  let c_2453 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rx_2450))) (
        array_to_seq (pubkey_2451))) (array_to_seq (msg_2452)) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_challenge_v))) (c_2453).


Definition bytes_from_point (p_2454 : affine_point_t)  : bytes32_t :=
  let '(x_2455, _) :=
    p_2454 in 
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2455)).


Definition bytes_from_scalar (x_2456 : scalar_t)  : bytes32_t :=
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2456)).


Definition scalar_from_bytes (b_2457 : bytes32_t)  : scalar_t :=
  nat_mod_from_byte_seq_be (array_to_seq (b_2457)) : scalar_t.


Definition scalar_from_bytes_strict (b_2458 : bytes32_t)  : (option scalar_t) :=
  let s_2459 : big_integer_t :=
    nat_mod_from_byte_seq_be (array_to_seq (b_2458)) : big_integer_t in 
  let max_scalar_2460 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2459) >.? (max_scalar_2460)):bool then (@None scalar_t) else (
      @Some scalar_t (nat_mod_from_byte_seq_be (
          array_to_seq (b_2458)) : scalar_t))).


Definition seckey_scalar_from_bytes (b_2461 : bytes32_t)  : (option scalar_t) :=
  bind (scalar_from_bytes_strict (b_2461)) (fun s_2462 => (if ((s_2462) =.? (
          nat_mod_zero )):bool then (@None scalar_t) else (@Some scalar_t (
          s_2462)))).


Definition fieldelem_from_bytes
  (b_2463 : public_key_t)
  
  : (option field_element_t) :=
  let s_2464 : big_integer_t :=
    nat_mod_from_byte_seq_be (b_2463) : big_integer_t in 
  let max_fe_2465 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2464) >.? (max_fe_2465)):bool then (@None field_element_t) else (
      @Some field_element_t (nat_mod_from_byte_seq_be (
          b_2463) : field_element_t))).


Definition xor_bytes (b0_2466 : bytes32_t) (b1_2467 : bytes32_t)  : bytes32_t :=
  let b_2468 : seq uint8 :=
    seq_new_ (default : uint8) (array_len (b0_2466)) in 
  let b_2468 :=
    foldi (usize 0) (array_len (b0_2466)) (fun i_2469 b_2468 =>
      let b_2468 :=
        seq_upd b_2468 (i_2469) ((array_index (b0_2466) (i_2469)) .^ (
            array_index (b1_2467) (i_2469))) in 
      (b_2468))
    b_2468 in 
  array_from_seq (32) (b_2468).


Notation "'pubkey_gen_result_t'" := ((
  result public_key_t error_t)) : hacspec_scope.

Definition pubkey_gen (seckey_2470 : secret_key_t)  : pubkey_gen_result_t :=
  bind (option_ok_or (seckey_scalar_from_bytes (seckey_2470)) (
      InvalidSecretKey)) (fun d0_2471 => let p_2472 : (
        field_element_t '×
        field_element_t
      ) :=
      option_unwrap (finite (point_mul_base (d0_2471))) in 
    @Ok public_key_t error_t (bytes_from_point (p_2472))).


Notation "'sign_result_t'" := ((result signature_t error_t)) : hacspec_scope.

Definition sign
  (msg_2473 : message_t)
  (seckey_2474 : secret_key_t)
  (aux_rand_2475 : aux_rand_t)
  
  : sign_result_t :=
  bind (option_ok_or (seckey_scalar_from_bytes (seckey_2474)) (
      InvalidSecretKey)) (fun d0_2476 => let p_2477 : (
        field_element_t '×
        field_element_t
      ) :=
      option_unwrap (finite (point_mul_base (d0_2476))) in 
    let d_2478 : scalar_t :=
      (if (has_even_y (p_2477)):bool then (d0_2476) else ((nat_mod_zero ) -% (
            d0_2476))) in 
    let t_2479 : bytes32_t :=
      xor_bytes (bytes_from_scalar (d_2478)) (hash_aux (aux_rand_2475)) in 
    let k0_2480 : scalar_t :=
      scalar_from_bytes (hash_nonce (t_2479) (bytes_from_point (p_2477)) (
          msg_2473)) in 
    ifbnd (k0_2480) =.? (nat_mod_zero ) : bool
    thenbnd (bind (@Err signature_t error_t (InvalidNonceGenerated)) (fun _ =>
        @Ok unit error_t (tt)))
    else (tt) >> (fun 'tt =>
    let r_2481 : (field_element_t '× field_element_t) :=
      option_unwrap (finite (point_mul_base (k0_2480))) in 
    let k_2482 : scalar_t :=
      (if (has_even_y (r_2481)):bool then (k0_2480) else ((nat_mod_zero ) -% (
            k0_2480))) in 
    let e_2483 : scalar_t :=
      scalar_from_bytes (hash_challenge (bytes_from_point (r_2481)) (
          bytes_from_point (p_2477)) (msg_2473)) in 
    let sig_2484 : signature_t :=
      array_update (array_update (array_new_ (default : uint8) (64)) (usize 0) (
          array_to_seq (bytes_from_point (r_2481)))) (usize 32) (
        array_to_seq (bytes_from_scalar ((k_2482) +% ((e_2483) *% (
              d_2478))))) in 
    bind (verify (msg_2473) (bytes_from_point (p_2477)) (sig_2484)) (fun _ =>
      @Ok signature_t error_t (sig_2484)))).


Notation "'verification_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition verify
  (msg_2485 : message_t)
  (pubkey_2486 : public_key_t)
  (sig_2487 : signature_t)
  
  : verification_result_t :=
  bind (option_ok_or (fieldelem_from_bytes (pubkey_2486)) (InvalidPublicKey)) (
    fun p_x_2488 => bind (lift_x (p_x_2488)) (fun p_2489 => bind (option_ok_or (
          fieldelem_from_bytes (array_from_slice (default : uint8) (32) (
              array_to_seq (sig_2487)) (usize 0) (usize 32))) (
          InvalidSignature)) (fun r_2490 => bind (option_ok_or (
            scalar_from_bytes_strict (array_from_slice (default : uint8) (32) (
                array_to_seq (sig_2487)) (usize 32) (usize 32))) (
            InvalidSignature)) (fun s_2491 => let e_2492 : scalar_t :=
            scalar_from_bytes (hash_challenge (array_from_slice (
                  default : uint8) (32) (array_to_seq (sig_2487)) (usize 0) (
                  usize 32)) (bytes_from_point (p_2489)) (msg_2485)) in 
          bind (option_ok_or (finite (point_add (point_mul_base (s_2491)) (
                  point_mul ((nat_mod_zero ) -% (e_2492)) (Affine (p_2489))))) (
              InvalidSignature)) (fun r_p_2493 => (if ((negb (has_even_y (
                      r_p_2493))) || ((x (r_p_2493)) !=.? (r_2490))):bool then (
                @Err unit error_t (InvalidSignature)) else (@Ok unit error_t (
                  tt)))))))).


