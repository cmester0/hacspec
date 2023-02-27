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

Definition bit_size_v : int32 :=
  @repr WORDSIZE32 (2048).

Definition byte_size_v : int32 :=
  (@repr WORDSIZE32 (2048)) ./ (@repr WORDSIZE32 (8)).

Definition hlen_v : uint_size :=
  usize 32.

Definition rsa_int_t := nat_mod pow2 2048.

Inductive error_t :=
| InvalidLength : error_t
| MessageTooLarge : error_t
| DecryptionFailed : error_t
| VerificationFailed : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | InvalidLength => match y with | InvalidLength=> true | _ => false end
   | MessageTooLarge => match y with | MessageTooLarge=> true | _ => false end
   | DecryptionFailed => match y with | DecryptionFailed=> true | _ => false end
   | VerificationFailed =>
       match y with
       | VerificationFailed=> true
       | _ => false
       end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Notation "'pk_t'" := ((rsa_int_t '× rsa_int_t)) : hacspec_scope.

Notation "'sk_t'" := ((rsa_int_t '× rsa_int_t)) : hacspec_scope.

Notation "'key_pair_t'" := ((pk_t '× sk_t)) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Notation "'rsa_int_result_t'" := ((result rsa_int_t error_t)) : hacspec_scope.

Definition rsaep (pk_2380 : pk_t) (m_2381 : rsa_int_t)  : rsa_int_result_t :=
  let '(n_2382, e_2383) :=
    pk_2380 in 
  (if ((m_2381) >.? ((n_2382) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_2381) (e_2383) (n_2382)))).


Definition rsadp (sk_2384 : sk_t) (c_2385 : rsa_int_t)  : rsa_int_result_t :=
  let '(n_2386, d_2387) :=
    sk_2384 in 
  (if ((c_2385) >.? ((n_2386) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (c_2385) (d_2387) (n_2386)))).


Definition rsasp1 (sk_2388 : sk_t) (m_2389 : rsa_int_t)  : rsa_int_result_t :=
  let '(n_2390, d_2391) :=
    sk_2388 in 
  (if ((m_2389) >.? ((n_2390) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_2389) (d_2391) (n_2390)))).


Definition rsavp1 (pk_2392 : pk_t) (s_2393 : rsa_int_t)  : rsa_int_result_t :=
  let '(n_2394, e_2395) :=
    pk_2392 in 
  (if ((s_2393) >.? ((n_2394) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (s_2393) (e_2395) (n_2394)))).


Definition i2osp
  (x_2396 : rsa_int_t)
  (x_len_2397 : int32)
  
  : byte_seq_result_t :=
  (if (((x_2396) >=.? (nat_mod_exp (nat_mod_from_literal (0x) (
              @repr WORDSIZE128 256) : rsa_int_t) (x_len_2397))) && ((
          x_len_2397) !=.? (byte_size_v))):bool then (@Err byte_seq error_t (
        InvalidLength)) else (@Ok byte_seq error_t (seq_slice (
          nat_mod_to_byte_seq_be (x_2396)) (@cast _ uint32 _ ((byte_size_v) .- (
              x_len_2397))) (@cast _ uint32 _ (x_len_2397))))).


Definition os2ip (x_2398 : byte_seq)  : rsa_int_t :=
  nat_mod_from_byte_seq_be (x_2398) : rsa_int_t.


Definition mgf1
  (mgf_seed_2399 : byte_seq)
  (mask_len_2400 : uint_size)
  
  : byte_seq_result_t :=
  let result_2401 : (result byte_seq error_t) :=
    @Err byte_seq error_t (InvalidLength) in 
  ifbnd (mask_len_2400) <.? ((usize 2) .^ ((usize 32) * (hlen_v))) : bool
  thenbnd (let t_2402 : seq uint8 :=
      seq_new_ (default : uint8) (usize 0) in 
    bind (foldibnd (usize 0) to (((mask_len_2400) + (usize 32)) / (
          usize 32)) for t_2402 >> (fun i_2403 t_2402 =>
      bind (i2osp (nat_mod_from_literal (0x) (pub_u128 (i_2403)) : rsa_int_t) (
          @repr WORDSIZE32 (4))) (fun x_2404 => let t_2402 :=
          seq_concat (t_2402) (array_to_seq (sha256 (seq_concat (
                mgf_seed_2399) (x_2404)))) in 
        @Ok (seq uint8) error_t ((t_2402))))) (fun t_2402 => let result_2401 :=
        @Ok byte_seq error_t (seq_slice (t_2402) (usize 0) (mask_len_2400)) in 
      @Ok ((result byte_seq error_t)) error_t ((result_2401))))
  else ((result_2401)) >> (fun '(result_2401) =>
  result_2401).


