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

Require Import Hacspec_Sha512.
Export Hacspec_Sha512.

Require Import Hacspec_Edwards25519.
Export Hacspec_Edwards25519.

Definition scalar_from_hash (h_1828 : sha512_digest_t)  : scalar_t :=
  let s_1829 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (h_1828)) : big_scalar_t in 
  nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (s_1829)) (
      usize 0) (usize 32)) : scalar_t.


Definition sign (sk_1830 : secret_key_t) (msg_1831 : byte_seq)  : signature_t :=
  let '(a_1832, prefix_1833) :=
    secret_expand (sk_1830) in 
  let a_1834 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (a_1832)) : scalar_t in 
  let b_1835 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_p_1836 : compressed_ed_point_t :=
    compress (point_mul (a_1834) (b_1835)) in 
  let r_1837 : scalar_t :=
    scalar_from_hash (sha512 (array_concat (prefix_1833) (msg_1831))) in 
  let r_p_1838 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_mul (r_1837) (b_1835) in 
  let r_s_1839 : compressed_ed_point_t :=
    compress (r_p_1838) in 
  let h_1840 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_s_1839) (
            array_to_seq (a_p_1836))) (msg_1831))) in 
  let s_1841 : scalar_t :=
    (r_1837) +% ((h_1840) *% (a_1834)) in 
  let s_bytes_1842 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (s_1841)) (usize 0) (usize 32) in 
  array_update (array_update (array_new_ (default : uint8) (64)) (usize 0) (
      array_to_seq (r_s_1839))) (usize 32) (s_bytes_1842).


Definition zcash_verify
  (pk_1843 : public_key_t)
  (signature_1844 : signature_t)
  (msg_1845 : byte_seq)
  
  : verify_result_t :=
  let b_1846 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress_non_canonical (base_v)) in 
  bind (option_ok_or (decompress_non_canonical (pk_1843)) (InvalidPublickey)) (
    fun a_1847 => let r_bytes_1848 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1844)) (
        usize 0) (usize 32) in 
    let s_bytes_1849 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1844)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1849)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress_non_canonical (r_bytes_1848)) (InvalidR)) (
      fun r_1850 => let s_1851 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1849)) : scalar_t in 
      let k_1852 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1848) (
                pk_1843)) (msg_1845))) in 
      let sb_1853 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_1851) (b_1846)) in 
      let rc_1854 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_1850) in 
      let ka_1855 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_1852) (a_1847)) in 
      (if (point_eq (sb_1853) (point_add (rc_1854) (ka_1855))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).


Definition ietf_cofactored_verify
  (pk_1856 : public_key_t)
  (signature_1857 : signature_t)
  (msg_1858 : byte_seq)
  
  : verify_result_t :=
  let b_1859 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_1856)) (InvalidPublickey)) (fun a_1860 =>
    let r_bytes_1861 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1857)) (
        usize 0) (usize 32) in 
    let s_bytes_1862 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1857)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1862)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1861)) (InvalidR)) (fun r_1863 =>
      let s_1864 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1862)) : scalar_t in 
      let k_1865 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1861) (
                pk_1856)) (msg_1858))) in 
      let sb_1866 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_1864) (b_1859)) in 
      let rc_1867 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_1863) in 
      let ka_1868 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_1865) (a_1860)) in 
      (if (point_eq (sb_1866) (point_add (rc_1867) (ka_1868))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).


Definition ietf_cofactorless_verify
  (pk_1869 : public_key_t)
  (signature_1870 : signature_t)
  (msg_1871 : byte_seq)
  
  : verify_result_t :=
  let b_1872 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_1869)) (InvalidPublickey)) (fun a_1873 =>
    let r_bytes_1874 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1870)) (
        usize 0) (usize 32) in 
    let s_bytes_1875 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1870)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1875)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1874)) (InvalidR)) (fun r_1876 =>
      let s_1877 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1875)) : scalar_t in 
      let k_1878 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1874) (
                pk_1869)) (msg_1871))) in 
      let sb_1879 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (s_1877) (b_1872) in 
      let ka_1880 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (k_1878) (a_1873) in 
      (if (point_eq (sb_1879) (point_add (r_1876) (ka_1880))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).


Definition is_identity (p_1881 : ed_point_t)  : bool :=
  point_eq (p_1881) (point_identity ).


Definition alg2_verify
  (pk_1882 : public_key_t)
  (signature_1883 : signature_t)
  (msg_1884 : byte_seq)
  
  : verify_result_t :=
  let b_1885 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_1882)) (InvalidPublickey)) (fun a_1886 =>
    ifbnd is_identity (point_mul_by_cofactor (a_1886)) : bool
    thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ =>
        @Ok unit error_t (tt)))
    else (tt) >> (fun 'tt =>
    let r_bytes_1887 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1883)) (
        usize 0) (usize 32) in 
    let s_bytes_1888 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1883)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1888)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1887)) (InvalidR)) (fun r_1889 =>
      let s_1890 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1888)) : scalar_t in 
      let k_1891 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1887) (
                pk_1882)) (msg_1884))) in 
      let sb_1892 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_1890) (b_1885)) in 
      let rc_1893 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_1889) in 
      let ka_1894 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_1891) (a_1886)) in 
      (if (point_eq (sb_1892) (point_add (rc_1893) (ka_1894))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature))))))).


Inductive batch_entry_t :=
| BatchEntry : (public_key_t '× byte_seq '× signature_t) -> batch_entry_t.

Definition zcash_batch_verify
  (entries_1895 : seq batch_entry_t)
  (entropy_1896 : byte_seq)
  
  : verify_result_t :=
  ifbnd (seq_len (entropy_1896)) <.? ((usize 16) * (seq_len (
        entries_1895))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1897 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1898 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1899 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1895)) for (
      s_sum_1897,
      r_sum_1898,
      a_sum_1899
    ) >> (fun i_1900 '(s_sum_1897, r_sum_1898, a_sum_1899) =>
    let 'BatchEntry ((pk_1901, msg_1902, signature_1903)) :=
      (seq_index (entries_1895) (i_1900)) in 
    bind (option_ok_or (decompress_non_canonical (pk_1901)) (
        InvalidPublickey)) (fun a_1904 =>
      let r_bytes_1905 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_1903)) (usize 0) (usize 32) in 
      let s_bytes_1906 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_1903)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1906)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress_non_canonical (r_bytes_1905)) (InvalidR)) (
        fun r_1907 => let s_1908 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1906)) : scalar_t in 
        let c_1909 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1905) (
                  array_to_seq (pk_1901))) (msg_1902))) in 
        let z_1910 : seq uint8 :=
          seq_slice (entropy_1896) ((usize 16) * (i_1900)) (usize 16) in 
        let z_1911 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1910) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_1897 :=
          (s_sum_1897) +% ((s_1908) *% (z_1911)) in 
        let r_sum_1898 :=
          point_add (r_sum_1898) (point_mul (z_1911) (r_1907)) in 
        let a_sum_1899 :=
          point_add (a_sum_1899) (point_mul ((z_1911) *% (c_1909)) (a_1904)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_1897, r_sum_1898, a_sum_1899))))))) (fun '(
      s_sum_1897,
      r_sum_1898,
      a_sum_1899
    ) => let b_1912 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1913 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1897) (b_1912) in 
    let check_1914 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_1913)) (point_add (
            r_sum_1898) (a_sum_1899))) in 
    (if (is_identity (check_1914)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).


Definition ietf_cofactored_batch_verify
  (entries_1915 : seq batch_entry_t)
  (entropy_1916 : byte_seq)
  
  : verify_result_t :=
  ifbnd (seq_len (entropy_1916)) <.? ((usize 16) * (seq_len (
        entries_1915))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1917 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1918 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1919 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1915)) for (
      s_sum_1917,
      r_sum_1918,
      a_sum_1919
    ) >> (fun i_1920 '(s_sum_1917, r_sum_1918, a_sum_1919) =>
    let 'BatchEntry ((pk_1921, msg_1922, signature_1923)) :=
      (seq_index (entries_1915) (i_1920)) in 
    bind (option_ok_or (decompress (pk_1921)) (InvalidPublickey)) (fun a_1924 =>
      let r_bytes_1925 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_1923)) (usize 0) (usize 32) in 
      let s_bytes_1926 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_1923)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1926)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1925)) (InvalidR)) (fun r_1927 =>
        let s_1928 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1926)) : scalar_t in 
        let c_1929 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1925) (
                  array_to_seq (pk_1921))) (msg_1922))) in 
        let z_1930 : seq uint8 :=
          seq_slice (entropy_1916) ((usize 16) * (i_1920)) (usize 16) in 
        let z_1931 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1930) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_1917 :=
          (s_sum_1917) +% ((s_1928) *% (z_1931)) in 
        let r_sum_1918 :=
          point_add (r_sum_1918) (point_mul (z_1931) (r_1927)) in 
        let a_sum_1919 :=
          point_add (a_sum_1919) (point_mul ((z_1931) *% (c_1929)) (a_1924)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_1917, r_sum_1918, a_sum_1919))))))) (fun '(
      s_sum_1917,
      r_sum_1918,
      a_sum_1919
    ) => let b_1932 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1933 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1917) (b_1932) in 
    let check_1934 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_1933)) (point_add (
            r_sum_1918) (a_sum_1919))) in 
    (if (is_identity (check_1934)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).


Definition ietf_cofactorless_batch_verify
  (entries_1935 : seq batch_entry_t)
  (entropy_1936 : byte_seq)
  
  : verify_result_t :=
  ifbnd (seq_len (entropy_1936)) <.? ((usize 16) * (seq_len (
        entries_1935))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1937 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1938 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1939 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1935)) for (
      s_sum_1937,
      r_sum_1938,
      a_sum_1939
    ) >> (fun i_1940 '(s_sum_1937, r_sum_1938, a_sum_1939) =>
    let 'BatchEntry ((pk_1941, msg_1942, signature_1943)) :=
      (seq_index (entries_1935) (i_1940)) in 
    bind (option_ok_or (decompress (pk_1941)) (InvalidPublickey)) (fun a_1944 =>
      let r_bytes_1945 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_1943)) (usize 0) (usize 32) in 
      let s_bytes_1946 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_1943)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1946)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1945)) (InvalidR)) (fun r_1947 =>
        let s_1948 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1946)) : scalar_t in 
        let c_1949 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1945) (
                  array_to_seq (pk_1941))) (msg_1942))) in 
        let z_1950 : seq uint8 :=
          seq_slice (entropy_1936) ((usize 16) * (i_1940)) (usize 16) in 
        let z_1951 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1950) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_1937 :=
          (s_sum_1937) +% ((s_1948) *% (z_1951)) in 
        let r_sum_1938 :=
          point_add (r_sum_1938) (point_mul (z_1951) (r_1947)) in 
        let a_sum_1939 :=
          point_add (a_sum_1939) (point_mul ((z_1951) *% (c_1949)) (a_1944)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_1937, r_sum_1938, a_sum_1939))))))) (fun '(
      s_sum_1937,
      r_sum_1938,
      a_sum_1939
    ) => let b_1952 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1953 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1937) (b_1952) in 
    let check_1954 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_add (point_neg (sb_1953)) (point_add (r_sum_1938) (a_sum_1939)) in 
    (if (is_identity (check_1954)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).


Definition alg3_batch_verify
  (entries_1955 : seq batch_entry_t)
  (entropy_1956 : byte_seq)
  
  : verify_result_t :=
  ifbnd (seq_len (entropy_1956)) <.? ((usize 16) * (seq_len (
        entries_1955))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1957 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1958 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1959 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1955)) for (
      s_sum_1957,
      r_sum_1958,
      a_sum_1959
    ) >> (fun i_1960 '(s_sum_1957, r_sum_1958, a_sum_1959) =>
    let 'BatchEntry ((pk_1961, msg_1962, signature_1963)) :=
      (seq_index (entries_1955) (i_1960)) in 
    bind (option_ok_or (decompress (pk_1961)) (InvalidPublickey)) (fun a_1964 =>
      ifbnd is_identity (point_mul_by_cofactor (a_1964)) : bool
      thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ =>
          @Ok unit error_t (tt)))
      else (tt) >> (fun 'tt =>
      let r_bytes_1965 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_1963)) (usize 0) (usize 32) in 
      let s_bytes_1966 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_1963)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1966)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1965)) (InvalidR)) (fun r_1967 =>
        let s_1968 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1966)) : scalar_t in 
        let c_1969 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1965) (
                  array_to_seq (pk_1961))) (msg_1962))) in 
        let z_1970 : seq uint8 :=
          seq_slice (entropy_1956) ((usize 16) * (i_1960)) (usize 16) in 
        let z_1971 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1970) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_1957 :=
          (s_sum_1957) +% ((s_1968) *% (z_1971)) in 
        let r_sum_1958 :=
          point_add (r_sum_1958) (point_mul (z_1971) (r_1967)) in 
        let a_sum_1959 :=
          point_add (a_sum_1959) (point_mul ((z_1971) *% (c_1969)) (a_1964)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_1957, r_sum_1958, a_sum_1959)))))))) (fun '(
      s_sum_1957,
      r_sum_1958,
      a_sum_1959
    ) => let b_1972 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1973 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1957) (b_1972) in 
    let check_1974 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_1973)) (point_add (
            r_sum_1958) (a_sum_1959))) in 
    (if (is_identity (check_1974)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).


