(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Definition fp_canvas_t := nseq (int8) (usize 48).
Definition fp_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition serialized_fp_t := nseq (uint8) (usize 48).

Definition array_fp_t := nseq (uint64) (usize 6).

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Notation "'g1_t'" := ((fp_t × fp_t × bool_ChoiceEquality)) : hacspec_scope.

Notation "'fp2_t'" := ((fp_t × fp_t)) : hacspec_scope.

Notation "'g2_t'" := ((fp2_t × fp2_t × bool_ChoiceEquality)) : hacspec_scope.

Notation "'fp6_t'" := ((fp2_t × fp2_t × fp2_t)) : hacspec_scope.

Notation "'fp12_t'" := ((fp6_t × fp6_t)) : hacspec_scope.


Notation "'fp2fromfp_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2fromfp_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2FROMFP : nat :=
  1634.
Program Definition fp2fromfp (n_1633 : fp_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n_1633,
          nat_mod_zero 
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2zero_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2zero_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2ZERO : nat :=
  1635.
Program Definition fp2zero  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2fromfp (nat_mod_zero ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2neg_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2neg_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2NEG : nat :=
  1639.
Program Definition fp2neg (n_1636 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1637, n2_1638) : (fp_t '× fp_t) := lift_to_both0 n_1636 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          (nat_mod_zero ) -% (lift_to_both0 n1_1637),
          (nat_mod_zero ) -% (lift_to_both0 n2_1638)
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2add_inp'" :=(
  fp2_t × fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2add_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2ADD : nat :=
  1646.
Program Definition fp2add (n_1640 : fp2_t) (m_1643 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1641, n2_1642) : (fp_t '× fp_t) := lift_to_both0 n_1640 in
      letb '(m1_1644, m2_1645) : (fp_t '× fp_t) := lift_to_both0 m_1643 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          (lift_to_both0 n1_1641) +% (lift_to_both0 m1_1644),
          (lift_to_both0 n2_1642) +% (lift_to_both0 m2_1645)
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2sub_inp'" :=(
  fp2_t × fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2sub_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2SUB : nat :=
  1649.
Program Definition fp2sub (n_1647 : fp2_t) (m_1648 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2add (
          lift_to_both0 n_1647) (fp2neg (lift_to_both0 m_1648)))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2mul_inp'" :=(
  fp2_t × fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2mul_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2MUL : nat :=
  1658.
Program Definition fp2mul (n_1650 : fp2_t) (m_1653 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1651, n2_1652) : (fp_t '× fp_t) := lift_to_both0 n_1650 in
      letb '(m1_1654, m2_1655) : (fp_t '× fp_t) := lift_to_both0 m_1653 in
      letb x1_1656 : fp_t :=
        ((lift_to_both0 n1_1651) *% (lift_to_both0 m1_1654)) -% ((
            lift_to_both0 n2_1652) *% (lift_to_both0 m2_1655)) in
      letb x2_1657 : fp_t :=
        ((lift_to_both0 n1_1651) *% (lift_to_both0 m2_1655)) +% ((
            lift_to_both0 n2_1652) *% (lift_to_both0 m1_1654)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x1_1656,
          lift_to_both0 x2_1657
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2inv_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2inv_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2INV : nat :=
  1666.
Program Definition fp2inv (n_1659 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1660, n2_1661) : (fp_t '× fp_t) := lift_to_both0 n_1659 in
      letb t0_1662 : fp_t :=
        ((lift_to_both0 n1_1660) *% (lift_to_both0 n1_1660)) +% ((
            lift_to_both0 n2_1661) *% (lift_to_both0 n2_1661)) in
      letb t1_1663 : fp_t := nat_mod_inv (lift_to_both0 t0_1662) in
      letb x1_1664 : fp_t :=
        (lift_to_both0 n1_1660) *% (lift_to_both0 t1_1663) in
      letb x2_1665 : fp_t :=
        (nat_mod_zero ) -% ((lift_to_both0 n2_1661) *% (
            lift_to_both0 t1_1663)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x1_1664,
          lift_to_both0 x2_1665
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2conjugate_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2conjugate_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2CONJUGATE : nat :=
  1670.
Program Definition fp2conjugate (n_1667 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1668, n2_1669) : (fp_t '× fp_t) := lift_to_both0 n_1667 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n1_1668,
          (nat_mod_zero ) -% (lift_to_both0 n2_1669)
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp6fromfp2_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6fromfp2_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6FROMFP2 : nat :=
  1672.
Program Definition fp6fromfp2 (n_1671 : fp2_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n_1671,
          fp2zero ,
          fp2zero 
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6zero_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp6zero_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6ZERO : nat :=
  1673.
Program Definition fp6zero  : both (fset.fset0) [interface] (fp6_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp6fromfp2 (fp2zero ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6neg_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6neg_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6NEG : nat :=
  1678.
Program Definition fp6neg (n_1674 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((letb '(n1_1675, n2_1676, n3_1677) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 n_1674 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          fp2sub (fp2zero ) (lift_to_both0 n1_1675),
          fp2sub (fp2zero ) (lift_to_both0 n2_1676),
          fp2sub (fp2zero ) (lift_to_both0 n3_1677)
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6add_inp'" :=(
  fp6_t × fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6add_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6ADD : nat :=
  1687.
Program Definition fp6add (n_1679 : fp6_t) (m_1683 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((letb '(n1_1680, n2_1681, n3_1682) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 n_1679 in
      letb '(m1_1684, m2_1685, m3_1686) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 m_1683 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          fp2add (lift_to_both0 n1_1680) (lift_to_both0 m1_1684),
          fp2add (lift_to_both0 n2_1681) (lift_to_both0 m2_1685),
          fp2add (lift_to_both0 n3_1682) (lift_to_both0 m3_1686)
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6sub_inp'" :=(
  fp6_t × fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6sub_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6SUB : nat :=
  1690.
Program Definition fp6sub (n_1688 : fp6_t) (m_1689 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp6add (
          lift_to_both0 n_1688) (fp6neg (lift_to_both0 m_1689)))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6mul_inp'" :=(
  fp6_t × fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6mul_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6MUL : nat :=
  1712.
Program Definition fp6mul (n_1691 : fp6_t) (m_1695 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((letb '(n1_1692, n2_1693, n3_1694) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 n_1691 in
      letb '(m1_1696, m2_1697, m3_1698) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 m_1695 in
      letb eps_1699 : (fp_t '× fp_t) := prod_b(nat_mod_one , nat_mod_one ) in
      letb t1_1700 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1692) (lift_to_both0 m1_1696) in
      letb t2_1701 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n2_1693) (lift_to_both0 m2_1697) in
      letb t3_1702 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n3_1694) (lift_to_both0 m3_1698) in
      letb t4_1703 : (fp_t '× fp_t) :=
        fp2mul (fp2add (lift_to_both0 n2_1693) (lift_to_both0 n3_1694)) (
          fp2add (lift_to_both0 m2_1697) (lift_to_both0 m3_1698)) in
      letb t5_1704 : (fp_t '× fp_t) :=
        fp2sub (fp2sub (lift_to_both0 t4_1703) (lift_to_both0 t2_1701)) (
          lift_to_both0 t3_1702) in
      letb x_1705 : (fp_t '× fp_t) :=
        fp2add (fp2mul (lift_to_both0 t5_1704) (lift_to_both0 eps_1699)) (
          lift_to_both0 t1_1700) in
      letb t4_1706 : (fp_t '× fp_t) :=
        fp2mul (fp2add (lift_to_both0 n1_1692) (lift_to_both0 n2_1693)) (
          fp2add (lift_to_both0 m1_1696) (lift_to_both0 m2_1697)) in
      letb t5_1707 : (fp_t '× fp_t) :=
        fp2sub (fp2sub (lift_to_both0 t4_1706) (lift_to_both0 t1_1700)) (
          lift_to_both0 t2_1701) in
      letb y_1708 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 t5_1707) (fp2mul (lift_to_both0 eps_1699) (
            lift_to_both0 t3_1702)) in
      letb t4_1709 : (fp_t '× fp_t) :=
        fp2mul (fp2add (lift_to_both0 n1_1692) (lift_to_both0 n3_1694)) (
          fp2add (lift_to_both0 m1_1696) (lift_to_both0 m3_1698)) in
      letb t5_1710 : (fp_t '× fp_t) :=
        fp2sub (fp2sub (lift_to_both0 t4_1709) (lift_to_both0 t1_1700)) (
          lift_to_both0 t3_1702) in
      letb z_1711 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 t5_1710) (lift_to_both0 t2_1701) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1705,
          lift_to_both0 y_1708,
          lift_to_both0 z_1711
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6inv_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6inv_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6INV : nat :=
  1734.
Program Definition fp6inv (n_1713 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((letb '(n1_1714, n2_1715, n3_1716) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 n_1713 in
      letb eps_1717 : (fp_t '× fp_t) := prod_b(nat_mod_one , nat_mod_one ) in
      letb t1_1718 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1714) (lift_to_both0 n1_1714) in
      letb t2_1719 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n2_1715) (lift_to_both0 n2_1715) in
      letb t3_1720 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n3_1716) (lift_to_both0 n3_1716) in
      letb t4_1721 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1714) (lift_to_both0 n2_1715) in
      letb t5_1722 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1714) (lift_to_both0 n3_1716) in
      letb t6_1723 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n2_1715) (lift_to_both0 n3_1716) in
      letb x0_1724 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t1_1718) (fp2mul (lift_to_both0 eps_1717) (
            lift_to_both0 t6_1723)) in
      letb y0_1725 : (fp_t '× fp_t) :=
        fp2sub (fp2mul (lift_to_both0 eps_1717) (lift_to_both0 t3_1720)) (
          lift_to_both0 t4_1721) in
      letb z0_1726 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t2_1719) (lift_to_both0 t5_1722) in
      letb t0_1727 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1714) (lift_to_both0 x0_1724) in
      letb t0_1728 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 t0_1727) (fp2mul (lift_to_both0 eps_1717) (
            fp2mul (lift_to_both0 n3_1716) (lift_to_both0 y0_1725))) in
      letb t0_1729 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 t0_1728) (fp2mul (lift_to_both0 eps_1717) (
            fp2mul (lift_to_both0 n2_1715) (lift_to_both0 z0_1726))) in
      letb t0_1730 : (fp_t '× fp_t) := fp2inv (lift_to_both0 t0_1729) in
      letb x_1731 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 x0_1724) (lift_to_both0 t0_1730) in
      letb y_1732 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 y0_1725) (lift_to_both0 t0_1730) in
      letb z_1733 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 z0_1726) (lift_to_both0 t0_1730) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1731,
          lift_to_both0 y_1732,
          lift_to_both0 z_1733
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp12fromfp6_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12fromfp6_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12FROMFP6 : nat :=
  1736.
Program Definition fp12fromfp6 (n_1735 : fp6_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n_1735,
          fp6zero 
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12neg_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12neg_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12NEG : nat :=
  1740.
Program Definition fp12neg (n_1737 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1738, n2_1739) : (fp6_t '× fp6_t) := lift_to_both0 n_1737 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          fp6sub (fp6zero ) (lift_to_both0 n1_1738),
          fp6sub (fp6zero ) (lift_to_both0 n2_1739)
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12add_inp'" :=(
  fp12_t × fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12add_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12ADD : nat :=
  1747.
Program Definition fp12add (n_1741 : fp12_t) (m_1744 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1742, n2_1743) : (fp6_t '× fp6_t) := lift_to_both0 n_1741 in
      letb '(m1_1745, m2_1746) : (fp6_t '× fp6_t) := lift_to_both0 m_1744 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          fp6add (lift_to_both0 n1_1742) (lift_to_both0 m1_1745),
          fp6add (lift_to_both0 n2_1743) (lift_to_both0 m2_1746)
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12sub_inp'" :=(
  fp12_t × fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12sub_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12SUB : nat :=
  1750.
Program Definition fp12sub (n_1748 : fp12_t) (m_1749 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12add (
          lift_to_both0 n_1748) (fp12neg (lift_to_both0 m_1749)))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12mul_inp'" :=(
  fp12_t × fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12mul_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12MUL : nat :=
  1763.
Program Definition fp12mul (n_1751 : fp12_t) (m_1754 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1752, n2_1753) : (fp6_t '× fp6_t) := lift_to_both0 n_1751 in
      letb '(m1_1755, m2_1756) : (fp6_t '× fp6_t) := lift_to_both0 m_1754 in
      letb gamma_1757 : (fp2_t '× fp2_t '× fp2_t) :=
        prod_b(fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in
      letb t1_1758 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n1_1752) (lift_to_both0 m1_1755) in
      letb t2_1759 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n2_1753) (lift_to_both0 m2_1756) in
      letb x_1760 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6add (lift_to_both0 t1_1758) (fp6mul (lift_to_both0 t2_1759) (
            lift_to_both0 gamma_1757)) in
      letb y_1761 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (fp6add (lift_to_both0 n1_1752) (lift_to_both0 n2_1753)) (
          fp6add (lift_to_both0 m1_1755) (lift_to_both0 m2_1756)) in
      letb y_1762 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6sub (fp6sub (lift_to_both0 y_1761) (lift_to_both0 t1_1758)) (
          lift_to_both0 t2_1759) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1760,
          lift_to_both0 y_1762
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12inv_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12inv_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12INV : nat :=
  1774.
Program Definition fp12inv (n_1764 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1765, n2_1766) : (fp6_t '× fp6_t) := lift_to_both0 n_1764 in
      letb gamma_1767 : (fp2_t '× fp2_t '× fp2_t) :=
        prod_b(fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in
      letb t1_1768 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n1_1765) (lift_to_both0 n1_1765) in
      letb t2_1769 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n2_1766) (lift_to_both0 n2_1766) in
      letb t1_1770 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6sub (lift_to_both0 t1_1768) (fp6mul (lift_to_both0 gamma_1767) (
            lift_to_both0 t2_1769)) in
      letb t2_1771 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6inv (lift_to_both0 t1_1770) in
      letb x_1772 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n1_1765) (lift_to_both0 t2_1771) in
      letb y_1773 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6neg (fp6mul (lift_to_both0 n2_1766) (lift_to_both0 t2_1771)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1772,
          lift_to_both0 y_1773
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.

Definition c_1775_loc : ChoiceEqualityLocation :=
  ((fp6_t '× fp6_t) ; 1776%nat).
Notation "'fp12exp_inp'" :=(
  fp12_t × scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12exp_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12EXP : nat :=
  1780.
Program Definition fp12exp (n_1779 : fp12_t) (k_1778 : scalar_t)
  : both (CEfset ([c_1775_loc])) [interface] (fp12_t) :=
  ((letbm c_1775 : (fp6_t '× fp6_t) loc( c_1775_loc ) :=
        fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in
      letb c_1775 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) c_1775 (L := (CEfset ([c_1775_loc]))) (
            I := [interface]) (fun i_1777 c_1775 =>
            letbm c_1775 loc( c_1775_loc ) :=
              fp12mul (lift_to_both0 c_1775) (lift_to_both0 c_1775) in
            letb '(c_1775) :=
              if nat_mod_bit (lift_to_both0 k_1778) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_1777)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([c_1775_loc])) (L2 := CEfset (
                  [c_1775_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm c_1775 loc( c_1775_loc ) :=
                  fp12mul (lift_to_both0 c_1775) (lift_to_both0 n_1779) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 c_1775)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 c_1775)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 c_1775)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 c_1775)
      ) : both (CEfset ([c_1775_loc])) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12conjugate_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12conjugate_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12CONJUGATE : nat :=
  1784.
Program Definition fp12conjugate (n_1781 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1782, n2_1783) : (fp6_t '× fp6_t) := lift_to_both0 n_1781 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n1_1782,
          fp6neg (lift_to_both0 n2_1783)
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12zero_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp12zero_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12ZERO : nat :=
  1785.
Program Definition fp12zero  : both (fset.fset0) [interface] (fp12_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12fromfp6 (fp6zero ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'g1add_a_inp'" :=(
  g1_t × g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_a_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1ADD_A : nat :=
  1797.
Program Definition g1add_a (p_1786 : g1_t) (q_1789 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x1_1787, y1_1788, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_1786 in
      letb '(x2_1790, y2_1791, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        lift_to_both0 q_1789 in
      letb x_diff_1792 : fp_t :=
        (lift_to_both0 x2_1790) -% (lift_to_both0 x1_1787) in
      letb y_diff_1793 : fp_t :=
        (lift_to_both0 y2_1791) -% (lift_to_both0 y1_1788) in
      letb xovery_1794 : fp_t :=
        (lift_to_both0 y_diff_1793) *% (nat_mod_inv (
            lift_to_both0 x_diff_1792)) in
      letb x3_1795 : fp_t :=
        ((nat_mod_exp (lift_to_both0 xovery_1794) (lift_to_both0 (
                @repr U32 2))) -% (lift_to_both0 x1_1787)) -% (
          lift_to_both0 x2_1790) in
      letb y3_1796 : fp_t :=
        ((lift_to_both0 xovery_1794) *% ((lift_to_both0 x1_1787) -% (
              lift_to_both0 x3_1795))) -% (lift_to_both0 y1_1788) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_1795,
          lift_to_both0 y3_1796,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1double_a_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_a_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1DOUBLE_A : nat :=
  1805.
Program Definition g1double_a (p_1798 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x1_1799, y1_1800, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_1798 in
      letb x12_1801 : fp_t :=
        nat_mod_exp (lift_to_both0 x1_1799) (lift_to_both0 (@repr U32 2)) in
      letb xovery_1802 : fp_t :=
        ((nat_mod_from_literal (
              0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
              lift_to_both0 (@repr U128 3))) *% (lift_to_both0 x12_1801)) *% (
          nat_mod_inv ((nat_mod_two ) *% (lift_to_both0 y1_1800))) in
      letb x3_1803 : fp_t :=
        (nat_mod_exp (lift_to_both0 xovery_1802) (lift_to_both0 (
              @repr U32 2))) -% ((nat_mod_two ) *% (lift_to_both0 x1_1799)) in
      letb y3_1804 : fp_t :=
        ((lift_to_both0 xovery_1802) *% ((lift_to_both0 x1_1799) -% (
              lift_to_both0 x3_1803))) -% (lift_to_both0 y1_1800) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_1803,
          lift_to_both0 y3_1804,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1double_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1DOUBLE : nat :=
  1810.
Program Definition g1double (p_1806 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x1_1807, y1_1808, inf1_1809) : (fp_t '× fp_t '× bool_ChoiceEquality
        ) :=
        lift_to_both0 p_1806 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (((lift_to_both0 y1_1808) !=.? (
              nat_mod_zero )) && (negb (lift_to_both0 inf1_1809)))
        then g1double_a (lift_to_both0 p_1806)
        else prod_b(
          nat_mod_zero ,
          nat_mod_zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1add_inp'" :=(
  g1_t × g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_out'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Definition G1ADD : nat :=
  1819.
Program Definition g1add (p_1811 : g1_t) (q_1815 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x1_1812, y1_1813, inf1_1814) : (fp_t '× fp_t '× bool_ChoiceEquality
        ) :=
        lift_to_both0 p_1811 in
      letb '(x2_1816, y2_1817, inf2_1818) : (
          fp_t '×
          fp_t '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 q_1815 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 inf1_1814)
        then lift_to_both0 q_1815
        else if is_pure (I := [interface]) (lift_to_both0 inf2_1818)
        then lift_to_both0 p_1811
        else if is_pure (I := [interface]) ((lift_to_both0 p_1811) =.? (
            lift_to_both0 q_1815))
        then g1double (lift_to_both0 p_1811)
        else if is_pure (I := [interface]) (negb (((lift_to_both0 x1_1812) =.? (
                lift_to_both0 x2_1816)) && ((lift_to_both0 y1_1813) =.? ((
                  nat_mod_zero ) -% (lift_to_both0 y2_1817)))))
        then g1add_a (lift_to_both0 p_1811) (lift_to_both0 q_1815)
        else prod_b(
          nat_mod_zero ,
          nat_mod_zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.

Definition t_1820_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t '× bool_ChoiceEquality) ; 1821%nat).
Notation "'g1mul_inp'" :=(
  scalar_t × g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1mul_out'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Definition G1MUL : nat :=
  1825.
Program Definition g1mul (m_1823 : scalar_t) (p_1824 : g1_t)
  : both (CEfset ([t_1820_loc])) [interface] (g1_t) :=
  ((letbm t_1820 : (fp_t '× fp_t '× bool_ChoiceEquality) loc( t_1820_loc ) :=
        prod_b(
          nat_mod_zero ,
          nat_mod_zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ) in
      letb t_1820 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) t_1820 (L := (CEfset ([t_1820_loc]))) (
            I := [interface]) (fun i_1822 t_1820 =>
            letbm t_1820 loc( t_1820_loc ) := g1double (lift_to_both0 t_1820) in
            letb '(t_1820) :=
              if nat_mod_bit (lift_to_both0 m_1823) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_1822)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([t_1820_loc])) (L2 := CEfset (
                  [t_1820_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1820 loc( t_1820_loc ) :=
                  g1add (lift_to_both0 t_1820) (lift_to_both0 p_1824) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1820)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1820)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 t_1820)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 t_1820)
      ) : both (CEfset ([t_1820_loc])) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1neg_inp'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1neg_out'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Definition G1NEG : nat :=
  1830.
Program Definition g1neg (p_1826 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x_1827, y_1828, inf_1829) : (fp_t '× fp_t '× bool_ChoiceEquality
        ) :=
        lift_to_both0 p_1826 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1827,
          (nat_mod_zero ) -% (lift_to_both0 y_1828),
          lift_to_both0 inf_1829
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g2add_a_inp'" :=(
  g2_t × g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_a_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2ADD_A : nat :=
  1846.
Program Definition g2add_a (p_1831 : g2_t) (q_1834 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x1_1832, y1_1833, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_1831 in
      letb '(x2_1835, y2_1836, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 q_1834 in
      letb x_diff_1837 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 x2_1835) (lift_to_both0 x1_1832) in
      letb y_diff_1838 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 y2_1836) (lift_to_both0 y1_1833) in
      letb xovery_1839 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 y_diff_1838) (fp2inv (
            lift_to_both0 x_diff_1837)) in
      letb t1_1840 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xovery_1839) (lift_to_both0 xovery_1839) in
      letb t2_1841 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t1_1840) (lift_to_both0 x1_1832) in
      letb x3_1842 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t2_1841) (lift_to_both0 x2_1835) in
      letb t1_1843 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 x1_1832) (lift_to_both0 x3_1842) in
      letb t2_1844 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xovery_1839) (lift_to_both0 t1_1843) in
      letb y3_1845 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t2_1844) (lift_to_both0 y1_1833) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_1842,
          lift_to_both0 y3_1845,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2double_a_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_a_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2DOUBLE_A : nat :=
  1860.
Program Definition g2double_a (p_1847 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x1_1848, y1_1849, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_1847 in
      letb x12_1850 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 x1_1848) (lift_to_both0 x1_1848) in
      letb t1_1851 : (fp_t '× fp_t) :=
        fp2mul (fp2fromfp (nat_mod_from_literal (
              0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
              lift_to_both0 (@repr U128 3)))) (lift_to_both0 x12_1850) in
      letb t2_1852 : (fp_t '× fp_t) :=
        fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (lift_to_both0 y1_1849)) in
      letb xovery_1853 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t1_1851) (lift_to_both0 t2_1852) in
      letb t1_1854 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xovery_1853) (lift_to_both0 xovery_1853) in
      letb t2_1855 : (fp_t '× fp_t) :=
        fp2mul (fp2fromfp (nat_mod_two )) (lift_to_both0 x1_1848) in
      letb x3_1856 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t1_1854) (lift_to_both0 t2_1855) in
      letb t1_1857 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 x1_1848) (lift_to_both0 x3_1856) in
      letb t2_1858 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xovery_1853) (lift_to_both0 t1_1857) in
      letb y3_1859 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t2_1858) (lift_to_both0 y1_1849) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_1856,
          lift_to_both0 y3_1859,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2double_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2DOUBLE : nat :=
  1865.
Program Definition g2double (p_1861 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x1_1862, y1_1863, inf1_1864) : (
          fp2_t '×
          fp2_t '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 p_1861 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (((lift_to_both0 y1_1863) !=.? (
              fp2zero )) && (negb (lift_to_both0 inf1_1864)))
        then g2double_a (lift_to_both0 p_1861)
        else prod_b(
          fp2zero ,
          fp2zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2add_inp'" :=(
  g2_t × g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Definition G2ADD : nat :=
  1874.
Program Definition g2add (p_1866 : g2_t) (q_1870 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x1_1867, y1_1868, inf1_1869) : (
          fp2_t '×
          fp2_t '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 p_1866 in
      letb '(x2_1871, y2_1872, inf2_1873) : (
          fp2_t '×
          fp2_t '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 q_1870 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 inf1_1869)
        then lift_to_both0 q_1870
        else if is_pure (I := [interface]) (lift_to_both0 inf2_1873)
        then lift_to_both0 p_1866
        else if is_pure (I := [interface]) ((lift_to_both0 p_1866) =.? (
            lift_to_both0 q_1870))
        then g2double (lift_to_both0 p_1866)
        else if is_pure (I := [interface]) (negb (((lift_to_both0 x1_1867) =.? (
                lift_to_both0 x2_1871)) && ((lift_to_both0 y1_1868) =.? (
                fp2neg (lift_to_both0 y2_1872)))))
        then g2add_a (lift_to_both0 p_1866) (lift_to_both0 q_1870)
        else prod_b(
          fp2zero ,
          fp2zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.

Definition t_1875_loc : ChoiceEqualityLocation :=
  ((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 1876%nat).
Notation "'g2mul_inp'" :=(
  scalar_t × g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2mul_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Definition G2MUL : nat :=
  1880.
Program Definition g2mul (m_1878 : scalar_t) (p_1879 : g2_t)
  : both (CEfset ([t_1875_loc])) [interface] (g2_t) :=
  ((letbm t_1875 : (fp2_t '× fp2_t '× bool_ChoiceEquality
        ) loc( t_1875_loc ) :=
        prod_b(fp2zero , fp2zero , lift_to_both0 ((true : bool_ChoiceEquality))
        ) in
      letb t_1875 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) t_1875 (L := (CEfset ([t_1875_loc]))) (
            I := [interface]) (fun i_1877 t_1875 =>
            letbm t_1875 loc( t_1875_loc ) := g2double (lift_to_both0 t_1875) in
            letb '(t_1875) :=
              if nat_mod_bit (lift_to_both0 m_1878) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_1877)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([t_1875_loc])) (L2 := CEfset (
                  [t_1875_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1875 loc( t_1875_loc ) :=
                  g2add (lift_to_both0 t_1875) (lift_to_both0 p_1879) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1875)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1875)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 t_1875)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 t_1875)
      ) : both (CEfset ([t_1875_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2neg_inp'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2neg_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Definition G2NEG : nat :=
  1885.
Program Definition g2neg (p_1881 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x_1882, y_1883, inf_1884) : (fp2_t '× fp2_t '× bool_ChoiceEquality
        ) :=
        lift_to_both0 p_1881 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1882,
          fp2neg (lift_to_both0 y_1883),
          lift_to_both0 inf_1884
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.


Notation "'twist_inp'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'twist_out'" :=((fp12_t '× fp12_t
  ) : choice_type) (in custom pack_type at level 2).
Definition TWIST : nat :=
  1891.
Program Definition twist (p_1886 : g1_t)
  : both (fset.fset0) [interface] ((fp12_t '× fp12_t)) :=
  ((letb '(p0_1887, p1_1888, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_1886 in
      letb x_1889 : ((fp2_t '× fp2_t '× fp2_t) '× fp6_t) :=
        prod_b(
          prod_b(fp2zero , fp2fromfp (lift_to_both0 p0_1887), fp2zero ),
          fp6zero 
        ) in
      letb y_1890 : (fp6_t '× (fp2_t '× fp2_t '× fp2_t)) :=
        prod_b(
          fp6zero ,
          prod_b(fp2zero , fp2fromfp (lift_to_both0 p1_1888), fp2zero )
        ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1889,
          lift_to_both0 y_1890
        ))
      ) : both (fset.fset0) [interface] ((fp12_t '× fp12_t))).
Fail Next Obligation.


Notation "'line_double_p_inp'" :=(
  g2_t × g1_t : choice_type) (in custom pack_type at level 2).
Notation "'line_double_p_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition LINE_DOUBLE_P : nat :=
  1903.
Program Definition line_double_p (r_1892 : g2_t) (p_1900 : g1_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(r0_1893, r1_1894, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 r_1892 in
      letb a_1895 : (fp_t '× fp_t) :=
        fp2mul (fp2fromfp (nat_mod_from_literal (
              0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
              lift_to_both0 (@repr U128 3)))) (fp2mul (lift_to_both0 r0_1893) (
            lift_to_both0 r0_1893)) in
      letb a_1896 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a_1895) (fp2inv (fp2mul (fp2fromfp (
                nat_mod_two )) (lift_to_both0 r1_1894))) in
      letb b_1897 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 r1_1894) (fp2mul (lift_to_both0 a_1896) (
            lift_to_both0 r0_1893)) in
      letb a_1898 : (fp6_t '× fp6_t) :=
        fp12fromfp6 (fp6fromfp2 (lift_to_both0 a_1896)) in
      letb b_1899 : (fp6_t '× fp6_t) :=
        fp12fromfp6 (fp6fromfp2 (lift_to_both0 b_1897)) in
      letb '(x_1901, y_1902) : (fp12_t '× fp12_t) :=
        twist (lift_to_both0 p_1900) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12neg (fp12sub (
            fp12sub (lift_to_both0 y_1902) (fp12mul (lift_to_both0 a_1898) (
                lift_to_both0 x_1901))) (lift_to_both0 b_1899)))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'line_add_p_inp'" :=(
  g2_t × g2_t × g1_t : choice_type) (in custom pack_type at level 2).
Notation "'line_add_p_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition LINE_ADD_P : nat :=
  1917.
Program Definition line_add_p (r_1904 : g2_t) (q_1907 : g2_t) (p_1914 : g1_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(r0_1905, r1_1906, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 r_1904 in
      letb '(q0_1908, q1_1909, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 q_1907 in
      letb a_1910 : (fp_t '× fp_t) :=
        fp2mul (fp2sub (lift_to_both0 q1_1909) (lift_to_both0 r1_1906)) (
          fp2inv (fp2sub (lift_to_both0 q0_1908) (lift_to_both0 r0_1905))) in
      letb b_1911 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 r1_1906) (fp2mul (lift_to_both0 a_1910) (
            lift_to_both0 r0_1905)) in
      letb a_1912 : (fp6_t '× fp6_t) :=
        fp12fromfp6 (fp6fromfp2 (lift_to_both0 a_1910)) in
      letb b_1913 : (fp6_t '× fp6_t) :=
        fp12fromfp6 (fp6fromfp2 (lift_to_both0 b_1911)) in
      letb '(x_1915, y_1916) : (fp12_t '× fp12_t) :=
        twist (lift_to_both0 p_1914) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12neg (fp12sub (
            fp12sub (lift_to_both0 y_1916) (fp12mul (lift_to_both0 a_1912) (
                lift_to_both0 x_1915))) (lift_to_both0 b_1913)))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'frobenius_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'frobenius_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FROBENIUS : nat :=
  1947.
Program Definition frobenius (f_1918 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '((g0_1919, g1_1920, g2_1921), (h0_1922, h1_1923, h2_1924)) : (
          fp6_t '×
          fp6_t
        ) :=
        lift_to_both0 f_1918 in
      letb t1_1925 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 g0_1919) in
      letb t2_1926 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 h0_1922) in
      letb t3_1927 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 g1_1920) in
      letb t4_1928 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 h1_1923) in
      letb t5_1929 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 g2_1921) in
      letb t6_1930 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 h2_1924) in
      letb c1_1931 : array_fp_t :=
        @array_from_list uint64 ([
            (secret (lift_to_both0 (@repr U64 10162220747404304312))) : uint64;
            (secret (lift_to_both0 (@repr U64 17761815663483519293))) : uint64;
            (secret (lift_to_both0 (@repr U64 8873291758750579140))) : uint64;
            (secret (lift_to_both0 (@repr U64 1141103941765652303))) : uint64;
            (secret (lift_to_both0 (@repr U64 13993175198059990303))) : uint64;
            (secret (lift_to_both0 (@repr U64 1802798568193066599))) : uint64
          ]) in
      letb c1_1932 : seq uint8 := array_to_le_bytes (lift_to_both0 c1_1931) in
      letb c1_1933 : fp_t := nat_mod_from_byte_seq_le (lift_to_both0 c1_1932) in
      letb c2_1934 : array_fp_t :=
        @array_from_list uint64 ([
            (secret (lift_to_both0 (@repr U64 3240210268673559283))) : uint64;
            (secret (lift_to_both0 (@repr U64 2895069921743240898))) : uint64;
            (secret (lift_to_both0 (@repr U64 17009126888523054175))) : uint64;
            (secret (lift_to_both0 (@repr U64 6098234018649060207))) : uint64;
            (secret (lift_to_both0 (@repr U64 9865672654120263608))) : uint64;
            (secret (lift_to_both0 (@repr U64 71000049454473266))) : uint64
          ]) in
      letb c2_1935 : seq uint8 := array_to_le_bytes (lift_to_both0 c2_1934) in
      letb c2_1936 : fp_t := nat_mod_from_byte_seq_le (lift_to_both0 c2_1935) in
      letb gamma11_1937 : (fp_t '× fp_t) :=
        prod_b(lift_to_both0 c1_1933, lift_to_both0 c2_1936) in
      letb gamma12_1938 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 gamma11_1937) (lift_to_both0 gamma11_1937) in
      letb gamma13_1939 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 gamma12_1938) (lift_to_both0 gamma11_1937) in
      letb gamma14_1940 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 gamma13_1939) (lift_to_both0 gamma11_1937) in
      letb gamma15_1941 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 gamma14_1940) (lift_to_both0 gamma11_1937) in
      letb t2_1942 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t2_1926) (lift_to_both0 gamma11_1937) in
      letb t3_1943 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t3_1927) (lift_to_both0 gamma12_1938) in
      letb t4_1944 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t4_1928) (lift_to_both0 gamma13_1939) in
      letb t5_1945 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t5_1929) (lift_to_both0 gamma14_1940) in
      letb t6_1946 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t6_1930) (lift_to_both0 gamma15_1941) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          prod_b(
            lift_to_both0 t1_1925,
            lift_to_both0 t3_1943,
            lift_to_both0 t5_1945
          ),
          prod_b(
            lift_to_both0 t2_1942,
            lift_to_both0 t4_1944,
            lift_to_both0 t6_1946
          )
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'final_exponentiation_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'final_exponentiation_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FINAL_EXPONENTIATION : nat :=
  1982.
Program Definition final_exponentiation (f_1948 : fp12_t)
  : both (CEfset ([c_1775_loc])) [interface] (fp12_t) :=
  ((letb fp6_1949 : (fp6_t '× fp6_t) := fp12conjugate (lift_to_both0 f_1948) in
      letb finv_1950 : (fp6_t '× fp6_t) := fp12inv (lift_to_both0 f_1948) in
      letb fp6_1_1951 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 fp6_1949) (lift_to_both0 finv_1950) in
      letb fp8_1952 : (fp6_t '× fp6_t) :=
        frobenius (frobenius (lift_to_both0 fp6_1_1951)) in
      letb f_1953 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 fp8_1952) (lift_to_both0 fp6_1_1951) in
      letb u_1954 : scalar_t :=
        nat_mod_from_literal (
          0x8000000000000000000000000000000000000000000000000000000000000000) (
          lift_to_both0 (@repr U128 15132376222941642752)) in
      letb u_half_1955 : scalar_t :=
        nat_mod_from_literal (
          0x8000000000000000000000000000000000000000000000000000000000000000) (
          lift_to_both0 (@repr U128 7566188111470821376)) in
      letb t0_1956 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 f_1953) (lift_to_both0 f_1953) in
      letb t1_1957 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t0_1956) (lift_to_both0 u_1954) in
      letb t1_1958 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t1_1957) in
      letb t2_1959 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t1_1958) (lift_to_both0 u_half_1955) in
      letb t2_1960 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t2_1959) in
      letb t3_1961 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 f_1953) in
      letb t1_1962 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t3_1961) (lift_to_both0 t1_1958) in
      letb t1_1963 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t1_1962) in
      letb t1_1964 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_1963) (lift_to_both0 t2_1960) in
      letb t2_1965 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t1_1964) (lift_to_both0 u_1954) in
      letb t2_1966 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t2_1965) in
      letb t3_1967 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t2_1966) (lift_to_both0 u_1954) in
      letb t3_1968 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t3_1967) in
      letb t1_1969 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t1_1964) in
      letb t3_1970 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_1969) (lift_to_both0 t3_1968) in
      letb t1_1971 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t1_1969) in
      letb t1_1972 : (fp6_t '× fp6_t) :=
        frobenius (frobenius (frobenius (lift_to_both0 t1_1971))) in
      letb t2_1973 : (fp6_t '× fp6_t) :=
        frobenius (frobenius (lift_to_both0 t2_1966)) in
      letb t1_1974 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_1972) (lift_to_both0 t2_1973) in
      letb t2_1975 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t3_1970) (lift_to_both0 u_1954) in
      letb t2_1976 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t2_1975) in
      letb t2_1977 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t2_1976) (lift_to_both0 t0_1956) in
      letb t2_1978 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t2_1977) (lift_to_both0 f_1953) in
      letb t1_1979 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_1974) (lift_to_both0 t2_1978) in
      letb t2_1980 : (fp6_t '× fp6_t) := frobenius (lift_to_both0 t3_1970) in
      letb t1_1981 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_1979) (lift_to_both0 t2_1980) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 t1_1981)
      ) : both (CEfset ([c_1775_loc])) [interface] (fp12_t)).
Fail Next Obligation.

Definition f_1984_loc : ChoiceEqualityLocation :=
  ((fp6_t '× fp6_t) ; 1985%nat).
Definition r_1983_loc : ChoiceEqualityLocation :=
  ((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 1986%nat).
Notation "'pairing_inp'" :=(
  g1_t × g2_t : choice_type) (in custom pack_type at level 2).
Notation "'pairing_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition PAIRING : nat :=
  1993.
Program Definition pairing (p_1990 : g1_t) (q_1988 : g2_t)
  : both (CEfset ([c_1775_loc ; r_1983_loc ; f_1984_loc])) [interface] (
    fp12_t) :=
  ((letb t_1987 : scalar_t :=
        nat_mod_from_literal (
          0x8000000000000000000000000000000000000000000000000000000000000000) (
          lift_to_both0 (@repr U128 15132376222941642752)) in
      letbm r_1983 : (fp2_t '× fp2_t '× bool_ChoiceEquality
        ) loc( r_1983_loc ) :=
        lift_to_both0 q_1988 in
      letbm f_1984 : (fp6_t '× fp6_t) loc( f_1984_loc ) :=
        fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in
      letb '(r_1983, f_1984) :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 64)) prod_ce(r_1983, f_1984) (L := (CEfset (
                [c_1775_loc ; r_1983_loc ; f_1984_loc]))) (I := [interface]) (
            fun i_1989 '(r_1983, f_1984) =>
            letb lrr_1991 : (fp6_t '× fp6_t) :=
              line_double_p (lift_to_both0 r_1983) (lift_to_both0 p_1990) in
            letbm r_1983 loc( r_1983_loc ) := g2double (lift_to_both0 r_1983) in
            letbm f_1984 loc( f_1984_loc ) :=
              fp12mul (fp12mul (lift_to_both0 f_1984) (lift_to_both0 f_1984)) (
                lift_to_both0 lrr_1991) in
            letb '(r_1983, f_1984) :=
              if nat_mod_bit (lift_to_both0 t_1987) (((lift_to_both0 (
                      usize 64)) .- (lift_to_both0 i_1989)) .- (lift_to_both0 (
                    usize 1))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([r_1983_loc ; f_1984_loc])) (
                L2 := CEfset ([r_1983_loc ; f_1984_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb lrq_1992 : (fp6_t '× fp6_t) :=
                  line_add_p (lift_to_both0 r_1983) (lift_to_both0 q_1988) (
                    lift_to_both0 p_1990) in
                letbm r_1983 loc( r_1983_loc ) :=
                  g2add (lift_to_both0 r_1983) (lift_to_both0 q_1988) in
                letbm f_1984 loc( f_1984_loc ) :=
                  fp12mul (lift_to_both0 f_1984) (lift_to_both0 lrq_1992) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 r_1983,
                    lift_to_both0 f_1984
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 r_1983,
                  lift_to_both0 f_1984
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 r_1983,
                lift_to_both0 f_1984
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (final_exponentiation (
          fp12conjugate (lift_to_both0 f_1984)))
      ) : both (CEfset ([c_1775_loc ; r_1983_loc ; f_1984_loc])) [interface] (
      fp12_t)).
Fail Next Obligation.


Notation "'test_fp2_prop_add_neg_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_add_neg_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP2_PROP_ADD_NEG : nat :=
  1996.
Program Definition test_fp2_prop_add_neg (a_1994 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_1995 : (fp_t '× fp_t) := fp2neg (lift_to_both0 a_1994) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp2fromfp (
            nat_mod_zero )) =.? (fp2add (lift_to_both0 a_1994) (
            lift_to_both0 b_1995)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp2_prop_mul_inv_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP2_PROP_MUL_INV : nat :=
  1999.
Program Definition test_fp2_prop_mul_inv (a_1997 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_1998 : (fp_t '× fp_t) := fp2inv (lift_to_both0 a_1997) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp2fromfp (
            nat_mod_one )) =.? (fp2mul (lift_to_both0 a_1997) (
            lift_to_both0 b_1998)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_extraction_issue_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_extraction_issue_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_EXTRACTION_ISSUE : nat :=
  2001.
Program Definition test_extraction_issue 
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2000 : (fp_t '× fp_t) :=
        fp2inv (prod_b(nat_mod_one , nat_mod_one )) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp2fromfp (
            nat_mod_one )) =.? (fp2mul (prod_b(nat_mod_one , nat_mod_one )) (
            lift_to_both0 b_2000)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp6_prop_mul_inv_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP6_PROP_MUL_INV : nat :=
  2004.
Program Definition test_fp6_prop_mul_inv (a_2002 : fp6_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2003 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6inv (lift_to_both0 a_2002) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp6fromfp2 (fp2fromfp (
              nat_mod_one ))) =.? (fp6mul (lift_to_both0 a_2002) (
            lift_to_both0 b_2003)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp6_prop_add_neg_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_add_neg_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP6_PROP_ADD_NEG : nat :=
  2007.
Program Definition test_fp6_prop_add_neg (a_2005 : fp6_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2006 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6neg (lift_to_both0 a_2005) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp6fromfp2 (fp2fromfp (
              nat_mod_zero ))) =.? (fp6add (lift_to_both0 a_2005) (
            lift_to_both0 b_2006)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp12_prop_add_neg_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp12_prop_add_neg_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP12_PROP_ADD_NEG : nat :=
  2010.
Program Definition test_fp12_prop_add_neg (a_2008 : fp12_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2009 : (fp6_t '× fp6_t) := fp12neg (lift_to_both0 a_2008) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp12fromfp6 (
            fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (
            lift_to_both0 a_2008) (lift_to_both0 b_2009)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp12_prop_mul_inv_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp12_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP12_PROP_MUL_INV : nat :=
  2013.
Program Definition test_fp12_prop_mul_inv (a_2011 : fp12_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2012 : (fp6_t '× fp6_t) := fp12inv (lift_to_both0 a_2011) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp12fromfp6 (
            fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (
            lift_to_both0 a_2011) (lift_to_both0 b_2012)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

