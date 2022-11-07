(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519.

Definition scalar_from_hash (h_1635 : sha512_digest_t) : scalar_t :=
  let s_1636 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (h_1635)) : big_scalar_t in 
  nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (s_1636)) (
      usize 0) (usize 32)) : scalar_t.

Definition sign (sk_1637 : secret_key_t) (msg_1638 : byte_seq) : signature_t :=
  let '(a_1639, prefix_1640) :=
    secret_expand (sk_1637) in 
  let a_1641 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (a_1639)) : scalar_t in 
  let b_1642 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_p_1643 : compressed_ed_point_t :=
    compress (point_mul (a_1641) (b_1642)) in 
  let r_1644 : scalar_t :=
    scalar_from_hash (sha512 (array_concat (prefix_1640) (msg_1638))) in 
  let r_p_1645 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (r_1644) (b_1642) in 
  let r_s_1646 : compressed_ed_point_t :=
    compress (r_p_1645) in 
  let h_1647 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_s_1646) (
            array_to_seq (a_p_1643))) (msg_1638))) in 
  let s_1648 : scalar_t :=
    (r_1644) +% ((h_1647) *% (a_1641)) in 
  let s_bytes_1649 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (s_1648)) (usize 0) (usize 32) in 
  array_update (array_update (array_new_ (default) (64)) (usize 0) (
      array_to_seq (r_s_1646))) (usize 32) (s_bytes_1649).

Definition zcash_verify
  (pk_1650 : public_key_t)
  (signature_1651 : signature_t)
  (msg_1652 : byte_seq)
  : verify_result_t :=
  let b_1653 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress_non_canonical (base_v)) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  bind (option_ok_or (decompress_non_canonical (pk_1650)) (InvalidPublickey)) (
    fun a_1654 => let r_bytes_1655 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1651)) (
        usize 0) (usize 32) in 
    let s_bytes_1656 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1651)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1656)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress_non_canonical (r_bytes_1655)) (InvalidR)) (
      fun r_1657 => let s_1658 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1656)) : scalar_t in 
      let k_1659 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1655) (
                pk_1650)) (msg_1652))) in 
      let sb_1660 : (
=======
  bind (option_ok_or (decompress_non_canonical (pk_1911)) (InvalidPublickey)) (
    fun a_1915 => let r_bytes_1916 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1912)) (
        usize 0) (usize 32) in 
    let s_bytes_1917 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1912)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1917)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress_non_canonical (r_bytes_1916)) (InvalidR)) (
      fun r_1918 => let s_1919 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1917)) : scalar_t in 
      let k_1920 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1916) (
                pk_1911)) (msg_1913))) in 
      let sb_1921 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul_by_cofactor (point_mul (s_1658) (b_1653)) in 
      let rc_1661 : (
=======
        point_mul_by_cofactor (point_mul (s_1919) (b_1914)) in 
      let rc_1922 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul_by_cofactor (r_1657) in 
      let ka_1662 : (
=======
        point_mul_by_cofactor (r_1918) in 
      let ka_1923 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul_by_cofactor (point_mul (k_1659) (a_1654)) in 
      (if (point_eq (sb_1660) (point_add (rc_1661) (ka_1662))):bool then (
=======
        point_mul_by_cofactor (point_mul (k_1920) (a_1915)) in 
      (if (point_eq (sb_1921) (point_add (rc_1922) (ka_1923))):bool then (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactored_verify
  (pk_1663 : public_key_t)
  (signature_1664 : signature_t)
  (msg_1665 : byte_seq)
  : verify_result_t :=
  let b_1666 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  bind (option_ok_or (decompress (pk_1663)) (InvalidPublickey)) (fun a_1667 =>
    let r_bytes_1668 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1664)) (
        usize 0) (usize 32) in 
    let s_bytes_1669 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1664)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1669)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1668)) (InvalidR)) (fun r_1670 =>
      let s_1671 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1669)) : scalar_t in 
      let k_1672 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1668) (
                pk_1663)) (msg_1665))) in 
      let sb_1673 : (
=======
  bind (option_ok_or (decompress (pk_1924)) (InvalidPublickey)) (fun a_1928 =>
    let r_bytes_1929 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1925)) (
        usize 0) (usize 32) in 
    let s_bytes_1930 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1925)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1930)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1929)) (InvalidR)) (fun r_1931 =>
      let s_1932 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1930)) : scalar_t in 
      let k_1933 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1929) (
                pk_1924)) (msg_1926))) in 
      let sb_1934 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul_by_cofactor (point_mul (s_1671) (b_1666)) in 
      let rc_1674 : (
=======
        point_mul_by_cofactor (point_mul (s_1932) (b_1927)) in 
      let rc_1935 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul_by_cofactor (r_1670) in 
      let ka_1675 : (
=======
        point_mul_by_cofactor (r_1931) in 
      let ka_1936 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul_by_cofactor (point_mul (k_1672) (a_1667)) in 
      (if (point_eq (sb_1673) (point_add (rc_1674) (ka_1675))):bool then (
=======
        point_mul_by_cofactor (point_mul (k_1933) (a_1928)) in 
      (if (point_eq (sb_1934) (point_add (rc_1935) (ka_1936))):bool then (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactorless_verify
  (pk_1676 : public_key_t)
  (signature_1677 : signature_t)
  (msg_1678 : byte_seq)
  : verify_result_t :=
  let b_1679 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  bind (option_ok_or (decompress (pk_1676)) (InvalidPublickey)) (fun a_1680 =>
    let r_bytes_1681 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1677)) (
        usize 0) (usize 32) in 
    let s_bytes_1682 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1677)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1682)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1681)) (InvalidR)) (fun r_1683 =>
      let s_1684 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1682)) : scalar_t in 
      let k_1685 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1681) (
                pk_1676)) (msg_1678))) in 
      let sb_1686 : (
=======
  bind (option_ok_or (decompress (pk_1937)) (InvalidPublickey)) (fun a_1941 =>
    let r_bytes_1942 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1938)) (
        usize 0) (usize 32) in 
    let s_bytes_1943 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1938)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1943)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1942)) (InvalidR)) (fun r_1944 =>
      let s_1945 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1943)) : scalar_t in 
      let k_1946 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1942) (
                pk_1937)) (msg_1939))) in 
      let sb_1947 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul (s_1684) (b_1679) in 
      let ka_1687 : (
=======
        point_mul (s_1945) (b_1940) in 
      let ka_1948 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul (k_1685) (a_1680) in 
      (if (point_eq (sb_1686) (point_add (r_1683) (ka_1687))):bool then (
=======
        point_mul (k_1946) (a_1941) in 
      (if (point_eq (sb_1947) (point_add (r_1944) (ka_1948))):bool then (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition is_identity (p_1688 : ed_point_t) : bool :=
  point_eq (p_1688) (point_identity ).

Definition alg2_verify
  (pk_1689 : public_key_t)
  (signature_1690 : signature_t)
  (msg_1691 : byte_seq)
  : verify_result_t :=
  let b_1692 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  bind (option_ok_or (decompress (pk_1689)) (InvalidPublickey)) (fun a_1693 =>
    ifbnd is_identity (point_mul_by_cofactor (a_1693)) : bool
    thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    let r_bytes_1694 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1690)) (
        usize 0) (usize 32) in 
    let s_bytes_1695 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1690)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1695)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1694)) (InvalidR)) (fun r_1696 =>
      let s_1697 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1695)) : scalar_t in 
      let k_1698 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1694) (
                pk_1689)) (msg_1691))) in 
      let sb_1699 : (
=======
  bind (option_ok_or (decompress (pk_1950)) (InvalidPublickey)) (fun a_1954 =>
    ifbnd is_identity (point_mul_by_cofactor (a_1954)) : bool
    thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    let r_bytes_1955 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1951)) (
        usize 0) (usize 32) in 
    let s_bytes_1956 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1951)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1956)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1955)) (InvalidR)) (fun r_1957 =>
      let s_1958 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1956)) : scalar_t in 
      let k_1959 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1955) (
                pk_1950)) (msg_1952))) in 
      let sb_1960 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul_by_cofactor (point_mul (s_1697) (b_1692)) in 
      let rc_1700 : (
=======
        point_mul_by_cofactor (point_mul (s_1958) (b_1953)) in 
      let rc_1961 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul_by_cofactor (r_1696) in 
      let ka_1701 : (
=======
        point_mul_by_cofactor (r_1957) in 
      let ka_1962 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
        point_mul_by_cofactor (point_mul (k_1698) (a_1693)) in 
      (if (point_eq (sb_1699) (point_add (rc_1700) (ka_1701))):bool then (
=======
        point_mul_by_cofactor (point_mul (k_1959) (a_1954)) in 
      (if (point_eq (sb_1960) (point_add (rc_1961) (ka_1962))):bool then (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature))))))).

Inductive batch_entry_t :=
| BatchEntry : (public_key_t × byte_seq × signature_t) -> batch_entry_t.

Definition zcash_batch_verify
  (entries_1702 : seq batch_entry_t)
  (entropy_1703 : byte_seq)
  : verify_result_t :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  ifbnd (seq_len (entropy_1703)) <.? ((usize 16) * (seq_len (
        entries_1702))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1704 : scalar_t :=
=======
  ifbnd (seq_len (entropy_1964)) <.? ((usize 16) * (seq_len (
        entries_1963))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1965 : scalar_t :=
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
    nat_mod_zero  in 
  let r_sum_1705 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1706 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  bind (foldibnd (usize 0) to (seq_len (entries_1702)) for (
      s_sum_1704,
      r_sum_1705,
      a_sum_1706
    ) >> (fun i_1707 '(s_sum_1704, r_sum_1705, a_sum_1706) =>
    let 'BatchEntry ((pk_1708, msg_1709, signature_1710)) :=
      (seq_index (entries_1702) (i_1707)) in 
    bind (option_ok_or (decompress_non_canonical (pk_1708)) (
        InvalidPublickey)) (fun a_1711 =>
      let r_bytes_1712 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1710)) (
=======
  bind (foldibnd (usize 0) to (seq_len (entries_1963)) for (
      s_sum_1965,
      r_sum_1966,
      a_sum_1967
    ) >> (fun i_1968 '(s_sum_1965, r_sum_1966, a_sum_1967) =>
    let 'BatchEntry ((pk_1969, msg_1970, signature_1971)) :=
      (seq_index (entries_1963) (i_1968)) in 
    bind (option_ok_or (decompress_non_canonical (pk_1969)) (
        InvalidPublickey)) (fun a_1972 =>
      let r_bytes_1973 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1971)) (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          usize 0) (usize 32) in 
      let s_bytes_1713 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1710)) (
          usize 32) (usize 32) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      ifbnd negb (check_canonical_scalar (s_bytes_1713)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress_non_canonical (r_bytes_1712)) (InvalidR)) (
        fun r_1714 => let s_1715 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1713)) : scalar_t in 
        let c_1716 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1712) (
                  array_to_seq (pk_1708))) (msg_1709))) in 
        let z_1717 : seq uint8 :=
          seq_slice (entropy_1703) ((usize 16) * (i_1707)) (usize 16) in 
        let z_1718 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1717) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1704 :=
          (s_sum_1704) +% ((s_1715) *% (z_1718)) in 
        let r_sum_1705 :=
          point_add (r_sum_1705) (point_mul (z_1718) (r_1714)) in 
        let a_sum_1706 :=
          point_add (a_sum_1706) (point_mul ((z_1718) *% (c_1716)) (a_1711)) in 
        Ok ((s_sum_1704, r_sum_1705, a_sum_1706))))))) (fun '(
      s_sum_1704,
      r_sum_1705,
      a_sum_1706
    ) => let b_1719 : (
=======
      ifbnd negb (check_canonical_scalar (s_bytes_1974)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress_non_canonical (r_bytes_1973)) (InvalidR)) (
        fun r_1975 => let s_1976 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1974)) : scalar_t in 
        let c_1977 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1973) (
                  array_to_seq (pk_1969))) (msg_1970))) in 
        let z_1978 : seq uint8 :=
          seq_slice (entropy_1964) ((usize 16) * (i_1968)) (usize 16) in 
        let z_1979 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1978) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1965 :=
          (s_sum_1965) +% ((s_1976) *% (z_1979)) in 
        let r_sum_1966 :=
          point_add (r_sum_1966) (point_mul (z_1979) (r_1975)) in 
        let a_sum_1967 :=
          point_add (a_sum_1967) (point_mul ((z_1979) *% (c_1977)) (a_1972)) in 
        Ok ((s_sum_1965, r_sum_1966, a_sum_1967))))))) (fun '(
      s_sum_1965,
      r_sum_1966,
      a_sum_1967
    ) => let b_1980 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
    let sb_1720 : (
=======
    let sb_1981 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      point_mul (s_sum_1704) (b_1719) in 
    let check_1721 : (
=======
      point_mul (s_sum_1965) (b_1980) in 
    let check_1982 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      point_mul_by_cofactor (point_add (point_neg (sb_1720)) (point_add (
            r_sum_1705) (a_sum_1706))) in 
    (if (is_identity (check_1721)):bool then (@Ok unit error_t (tt)) else (
=======
      point_mul_by_cofactor (point_add (point_neg (sb_1981)) (point_add (
            r_sum_1966) (a_sum_1967))) in 
    (if (is_identity (check_1982)):bool then (@Ok unit error_t (tt)) else (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactored_batch_verify
  (entries_1722 : seq batch_entry_t)
  (entropy_1723 : byte_seq)
  : verify_result_t :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  ifbnd (seq_len (entropy_1723)) <.? ((usize 16) * (seq_len (
        entries_1722))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1724 : scalar_t :=
=======
  ifbnd (seq_len (entropy_1984)) <.? ((usize 16) * (seq_len (
        entries_1983))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1985 : scalar_t :=
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
    nat_mod_zero  in 
  let r_sum_1725 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1726 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  bind (foldibnd (usize 0) to (seq_len (entries_1722)) for (
      s_sum_1724,
      r_sum_1725,
      a_sum_1726
    ) >> (fun i_1727 '(s_sum_1724, r_sum_1725, a_sum_1726) =>
    let 'BatchEntry ((pk_1728, msg_1729, signature_1730)) :=
      (seq_index (entries_1722) (i_1727)) in 
    bind (option_ok_or (decompress (pk_1728)) (InvalidPublickey)) (fun a_1731 =>
      let r_bytes_1732 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1730)) (
=======
  bind (foldibnd (usize 0) to (seq_len (entries_1983)) for (
      s_sum_1985,
      r_sum_1986,
      a_sum_1987
    ) >> (fun i_1988 '(s_sum_1985, r_sum_1986, a_sum_1987) =>
    let 'BatchEntry ((pk_1989, msg_1990, signature_1991)) :=
      (seq_index (entries_1983) (i_1988)) in 
    bind (option_ok_or (decompress (pk_1989)) (InvalidPublickey)) (fun a_1992 =>
      let r_bytes_1993 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1991)) (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          usize 0) (usize 32) in 
      let s_bytes_1733 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1730)) (
          usize 32) (usize 32) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      ifbnd negb (check_canonical_scalar (s_bytes_1733)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1732)) (InvalidR)) (fun r_1734 =>
        let s_1735 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1733)) : scalar_t in 
        let c_1736 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1732) (
                  array_to_seq (pk_1728))) (msg_1729))) in 
        let z_1737 : seq uint8 :=
          seq_slice (entropy_1723) ((usize 16) * (i_1727)) (usize 16) in 
        let z_1738 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1737) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1724 :=
          (s_sum_1724) +% ((s_1735) *% (z_1738)) in 
        let r_sum_1725 :=
          point_add (r_sum_1725) (point_mul (z_1738) (r_1734)) in 
        let a_sum_1726 :=
          point_add (a_sum_1726) (point_mul ((z_1738) *% (c_1736)) (a_1731)) in 
        Ok ((s_sum_1724, r_sum_1725, a_sum_1726))))))) (fun '(
      s_sum_1724,
      r_sum_1725,
      a_sum_1726
    ) => let b_1739 : (
=======
      ifbnd negb (check_canonical_scalar (s_bytes_1994)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1993)) (InvalidR)) (fun r_1995 =>
        let s_1996 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1994)) : scalar_t in 
        let c_1997 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1993) (
                  array_to_seq (pk_1989))) (msg_1990))) in 
        let z_1998 : seq uint8 :=
          seq_slice (entropy_1984) ((usize 16) * (i_1988)) (usize 16) in 
        let z_1999 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1998) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1985 :=
          (s_sum_1985) +% ((s_1996) *% (z_1999)) in 
        let r_sum_1986 :=
          point_add (r_sum_1986) (point_mul (z_1999) (r_1995)) in 
        let a_sum_1987 :=
          point_add (a_sum_1987) (point_mul ((z_1999) *% (c_1997)) (a_1992)) in 
        Ok ((s_sum_1985, r_sum_1986, a_sum_1987))))))) (fun '(
      s_sum_1985,
      r_sum_1986,
      a_sum_1987
    ) => let b_2000 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
    let sb_1740 : (
=======
    let sb_2001 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      point_mul (s_sum_1724) (b_1739) in 
    let check_1741 : (
=======
      point_mul (s_sum_1985) (b_2000) in 
    let check_2002 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      point_mul_by_cofactor (point_add (point_neg (sb_1740)) (point_add (
            r_sum_1725) (a_sum_1726))) in 
    (if (is_identity (check_1741)):bool then (@Ok unit error_t (tt)) else (
=======
      point_mul_by_cofactor (point_add (point_neg (sb_2001)) (point_add (
            r_sum_1986) (a_sum_1987))) in 
    (if (is_identity (check_2002)):bool then (@Ok unit error_t (tt)) else (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactorless_batch_verify
  (entries_1742 : seq batch_entry_t)
  (entropy_1743 : byte_seq)
  : verify_result_t :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  ifbnd (seq_len (entropy_1743)) <.? ((usize 16) * (seq_len (
        entries_1742))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1744 : scalar_t :=
=======
  ifbnd (seq_len (entropy_2004)) <.? ((usize 16) * (seq_len (
        entries_2003))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2005 : scalar_t :=
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
    nat_mod_zero  in 
  let r_sum_1745 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1746 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  bind (foldibnd (usize 0) to (seq_len (entries_1742)) for (
      s_sum_1744,
      r_sum_1745,
      a_sum_1746
    ) >> (fun i_1747 '(s_sum_1744, r_sum_1745, a_sum_1746) =>
    let 'BatchEntry ((pk_1748, msg_1749, signature_1750)) :=
      (seq_index (entries_1742) (i_1747)) in 
    bind (option_ok_or (decompress (pk_1748)) (InvalidPublickey)) (fun a_1751 =>
      let r_bytes_1752 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1750)) (
=======
  bind (foldibnd (usize 0) to (seq_len (entries_2003)) for (
      s_sum_2005,
      r_sum_2006,
      a_sum_2007
    ) >> (fun i_2008 '(s_sum_2005, r_sum_2006, a_sum_2007) =>
    let 'BatchEntry ((pk_2009, msg_2010, signature_2011)) :=
      (seq_index (entries_2003) (i_2008)) in 
    bind (option_ok_or (decompress (pk_2009)) (InvalidPublickey)) (fun a_2012 =>
      let r_bytes_2013 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_2011)) (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          usize 0) (usize 32) in 
      let s_bytes_1753 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1750)) (
          usize 32) (usize 32) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      ifbnd negb (check_canonical_scalar (s_bytes_1753)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1752)) (InvalidR)) (fun r_1754 =>
        let s_1755 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1753)) : scalar_t in 
        let c_1756 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1752) (
                  array_to_seq (pk_1748))) (msg_1749))) in 
        let z_1757 : seq uint8 :=
          seq_slice (entropy_1743) ((usize 16) * (i_1747)) (usize 16) in 
        let z_1758 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1757) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1744 :=
          (s_sum_1744) +% ((s_1755) *% (z_1758)) in 
        let r_sum_1745 :=
          point_add (r_sum_1745) (point_mul (z_1758) (r_1754)) in 
        let a_sum_1746 :=
          point_add (a_sum_1746) (point_mul ((z_1758) *% (c_1756)) (a_1751)) in 
        Ok ((s_sum_1744, r_sum_1745, a_sum_1746))))))) (fun '(
      s_sum_1744,
      r_sum_1745,
      a_sum_1746
    ) => let b_1759 : (
=======
      ifbnd negb (check_canonical_scalar (s_bytes_2014)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_2013)) (InvalidR)) (fun r_2015 =>
        let s_2016 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2014)) : scalar_t in 
        let c_2017 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2013) (
                  array_to_seq (pk_2009))) (msg_2010))) in 
        let z_2018 : seq uint8 :=
          seq_slice (entropy_2004) ((usize 16) * (i_2008)) (usize 16) in 
        let z_2019 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2018) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_2005 :=
          (s_sum_2005) +% ((s_2016) *% (z_2019)) in 
        let r_sum_2006 :=
          point_add (r_sum_2006) (point_mul (z_2019) (r_2015)) in 
        let a_sum_2007 :=
          point_add (a_sum_2007) (point_mul ((z_2019) *% (c_2017)) (a_2012)) in 
        Ok ((s_sum_2005, r_sum_2006, a_sum_2007))))))) (fun '(
      s_sum_2005,
      r_sum_2006,
      a_sum_2007
    ) => let b_2020 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
    let sb_1760 : (
=======
    let sb_2021 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      point_mul (s_sum_1744) (b_1759) in 
    let check_1761 : (
=======
      point_mul (s_sum_2005) (b_2020) in 
    let check_2022 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      point_add (point_neg (sb_1760)) (point_add (r_sum_1745) (a_sum_1746)) in 
    (if (is_identity (check_1761)):bool then (@Ok unit error_t (tt)) else (
=======
      point_add (point_neg (sb_2021)) (point_add (r_sum_2006) (a_sum_2007)) in 
    (if (is_identity (check_2022)):bool then (@Ok unit error_t (tt)) else (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        @Err unit error_t (InvalidSignature))))).

Definition alg3_batch_verify
  (entries_1762 : seq batch_entry_t)
  (entropy_1763 : byte_seq)
  : verify_result_t :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  ifbnd (seq_len (entropy_1763)) <.? ((usize 16) * (seq_len (
        entries_1762))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1764 : scalar_t :=
=======
  ifbnd (seq_len (entropy_2024)) <.? ((usize 16) * (seq_len (
        entries_2023))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2025 : scalar_t :=
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
    nat_mod_zero  in 
  let r_sum_1765 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1766 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
  bind (foldibnd (usize 0) to (seq_len (entries_1762)) for (
      s_sum_1764,
      r_sum_1765,
      a_sum_1766
    ) >> (fun i_1767 '(s_sum_1764, r_sum_1765, a_sum_1766) =>
    let 'BatchEntry ((pk_1768, msg_1769, signature_1770)) :=
      (seq_index (entries_1762) (i_1767)) in 
    bind (option_ok_or (decompress (pk_1768)) (InvalidPublickey)) (fun a_1771 =>
      ifbnd is_identity (point_mul_by_cofactor (a_1771)) : bool
      thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      let r_bytes_1772 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1770)) (
=======
  bind (foldibnd (usize 0) to (seq_len (entries_2023)) for (
      s_sum_2025,
      r_sum_2026,
      a_sum_2027
    ) >> (fun i_2028 '(s_sum_2025, r_sum_2026, a_sum_2027) =>
    let 'BatchEntry ((pk_2029, msg_2030, signature_2031)) :=
      (seq_index (entries_2023) (i_2028)) in 
    bind (option_ok_or (decompress (pk_2029)) (InvalidPublickey)) (fun a_2032 =>
      ifbnd is_identity (point_mul_by_cofactor (a_2032)) : bool
      thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      let r_bytes_2033 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_2031)) (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
          usize 0) (usize 32) in 
      let s_bytes_1773 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1770)) (
          usize 32) (usize 32) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      ifbnd negb (check_canonical_scalar (s_bytes_1773)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1772)) (InvalidR)) (fun r_1774 =>
        let s_1775 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1773)) : scalar_t in 
        let c_1776 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1772) (
                  array_to_seq (pk_1768))) (msg_1769))) in 
        let z_1777 : seq uint8 :=
          seq_slice (entropy_1763) ((usize 16) * (i_1767)) (usize 16) in 
        let z_1778 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1777) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1764 :=
          (s_sum_1764) +% ((s_1775) *% (z_1778)) in 
        let r_sum_1765 :=
          point_add (r_sum_1765) (point_mul (z_1778) (r_1774)) in 
        let a_sum_1766 :=
          point_add (a_sum_1766) (point_mul ((z_1778) *% (c_1776)) (a_1771)) in 
        Ok ((s_sum_1764, r_sum_1765, a_sum_1766)))))))) (fun '(
      s_sum_1764,
      r_sum_1765,
      a_sum_1766
    ) => let b_1779 : (
=======
      ifbnd negb (check_canonical_scalar (s_bytes_2034)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_2033)) (InvalidR)) (fun r_2035 =>
        let s_2036 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2034)) : scalar_t in 
        let c_2037 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2033) (
                  array_to_seq (pk_2029))) (msg_2030))) in 
        let z_2038 : seq uint8 :=
          seq_slice (entropy_2024) ((usize 16) * (i_2028)) (usize 16) in 
        let z_2039 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2038) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_2025 :=
          (s_sum_2025) +% ((s_2036) *% (z_2039)) in 
        let r_sum_2026 :=
          point_add (r_sum_2026) (point_mul (z_2039) (r_2035)) in 
        let a_sum_2027 :=
          point_add (a_sum_2027) (point_mul ((z_2039) *% (c_2037)) (a_2032)) in 
        Ok ((s_sum_2025, r_sum_2026, a_sum_2027)))))))) (fun '(
      s_sum_2025,
      r_sum_2026,
      a_sum_2027
    ) => let b_2040 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
<<<<<<< ../coq/src/Hacspec_Ed25519.v
    let sb_1780 : (
=======
    let sb_2041 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      point_mul (s_sum_1764) (b_1779) in 
    let check_1781 : (
=======
      point_mul (s_sum_2025) (b_2040) in 
    let check_2042 : (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
<<<<<<< ../coq/src/Hacspec_Ed25519.v
      point_mul_by_cofactor (point_add (point_neg (sb_1780)) (point_add (
            r_sum_1765) (a_sum_1766))) in 
    (if (is_identity (check_1781)):bool then (@Ok unit error_t (tt)) else (
=======
      point_mul_by_cofactor (point_add (point_neg (sb_2041)) (point_add (
            r_sum_2026) (a_sum_2027))) in 
    (if (is_identity (check_2042)):bool then (@Ok unit error_t (tt)) else (
>>>>>>> ../coq/_vc/Hacspec_Ed25519.v
        @Err unit error_t (InvalidSignature))))).

