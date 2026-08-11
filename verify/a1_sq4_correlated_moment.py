#!/usr/bin/env python3
"""Exact Fraction audit for correlated transforms of the SQ4 nonzero family."""

from fractions import Fraction as F


U = F(43, 200)
SMOOTH = F(2, 5)
P = 2 * U + SMOOTH
V = 2 * U
R = F(33, 50)
K = P - SMOOTH
PHYSICAL_X = -F(23, 100)
COMPLETION = SMOOTH - P
SQ4_HB = F(149, 100)
BUDGET = F(83, 50)
INTEGRATED_BUDGET = F(143, 100)

# Exact multiplicative-Fourier moment followed by one coefficient-blind
# all-modulus character Cauchy/large-sieve step.
CHARACTER_FAMILY = 2 * P
V_PAIR_ENERGY = V
KR_LENGTH = K + R
CHAR_V_NORM = (CHARACTER_FAMILY + V_PAIR_ENERGY) / 2
CHAR_KR_NORM = (max(CHARACTER_FAMILY, KR_LENGTH) + KR_LENGTH) / 2
CHAR_FIXED = COMPLETION + CHAR_V_NORM + CHAR_KR_NORM

# Freeze p and v, triangle both outer families, and grant ideal square-root
# cancellation in the k,r pair together with Weil size for each complete sum.
FIXED_PV_SQRT = COMPLETION + P + V + (K + R) / 2 + P / 2

# Blomer--Pascadi, arXiv:2607.24311, Theorem 5.5, applied only to the
# fixed-(p,v) bilinear (k,r) block.  These are the five summands in H(M,N,c)
# with theorem variables M=K, N=R, c=P.  A sum of positive powers has the
# largest exponent; all transitions below are exact Fraction arithmetic.
BP_H1 = (
    K / 8
    + (max(P, K + R) + max(P, 2 * R)) / 16
    - P / 4
    + min(P - K, P / 2) / 16
)
BP_H2 = max(
    2 * R - 2 * P,
    R / 2 + K + max(P, 2 * R) - 5 * P / 2,
) / 16
BP_H3 = max(K, R) / 3 - P / 5
BP_H4 = max(K / 2 + R / 6, K / 6 + R / 2) - 7 * P / 18
BP_H5 = max(K, R) / 15 - P / 15
BP_H = max(BP_H1, BP_H2, BP_H3, BP_H4, BP_H5)
BP_FIXED_PV_INNER = (K + R) / 2 + P + BP_H
BP_FIXED_PV_OUTER = COMPLETION + P + V + BP_FIXED_PV_INNER

# Kerr--Shparlinski--Wu--Xi, JLMS 108 (2023), Theorem 2.1, in a
# favourable Type-I class.  Fix p, the source frequency ell, and the Fourier
# parameter; collapse (k,v) into an arbitrary coefficient on a full residue
# interval of length p, grant its L2 exponent V, and take h of length V.
ELL = R - V
KSWX_A1 = -P / 4 - V + P / 2
KSWX_A2 = P / 2 - V - P / 2
KSWX_A3 = -V / 2
KSWX_DELTA_A = max(KSWX_A1, KSWX_A2, KSWX_A3)
KSWX_B1 = -P / 2 + max(-3 * V / 4 + P / 2, F(0))
KSWX_B2 = -V / 2
KSWX_DELTA_B = max(KSWX_B1, KSWX_B2)
KSWX_C1 = -P / 2 + max(-V + P / 2, P / 4)
KSWX_C2 = -V / 2
KSWX_DELTA_C = max(KSWX_C1, KSWX_C2)
KSWX_BEST_DELTA = min(KSWX_DELTA_A, KSWX_DELTA_B, KSWX_DELTA_C)
KSWX_PER_P_ELL = V + P / 2 + V + P / 2 + KSWX_BEST_DELTA
KSWX_FIXED = COMPLETION + P + ELL + KSWX_PER_P_ELL
# The exact reciprocity phase removed in this class differs from 1 by T^-1.
# The already-audited direct Weil/triangle output is 467/200+eta+epsilon.
KSWX_RECIPROCITY_ERROR = F(467, 200) - 1
KSWX_RECIPROCITY_ETA = F(1, 20)
KSWX_RECIPROCITY_EPSILON = F(1, 20)
KSWX_RECIPROCITY_ERROR_ALLOCATED = (
    KSWX_RECIPROCITY_ERROR
    + KSWX_RECIPROCITY_ETA
    + KSWX_RECIPROCITY_EPSILON
)

# Ramanujan lift on the squarefree-v stratum, then Pascadi 2026,
# Corollary 5.11 (arXiv Corollary 17) / equation (5.32), with theorem
# parameters.  PASCADI_FIXED is
# only the favourable arithmetic under the explicitly granted unstated
# general-first-sequence variant.  The literal stated-corollary route pays
# the separate-(d,a) recombination exponent V/2.
# The source convention is R_thm < r_thm <= 2*R_thm.  Take r_thm=1 and
# R_thm=1/2; this fixed factor has exponent zero.  The other parameters are
# S_thm=(u1*u2)*v, M_thm=K, N_thm=v*r, C_thm=M.
LEVEL = 2 * V
SECOND_INDEX = V + R
PASCADI_ROOT_PREF = (LEVEL + K) / 2
PASCADI_COEFFICIENT_NORM = (LEVEL + R) / 2
PASCADI_A = LEVEL + SMOOTH
PASCADI_B = (K + SECOND_INDEX) / 2
PASCADI_C = (LEVEL + K) / 2 + SMOOTH
PASCADI_D = (LEVEL + SECOND_INDEX) / 2 + SMOOTH
PASCADI_GEOMETRY = (
    max(PASCADI_A, PASCADI_B, PASCADI_C)
    + max(PASCADI_A, PASCADI_B, PASCADI_D)
    - max(PASCADI_A, PASCADI_B)
)
PASCADI_BEFORE_COMPLETION = (
    PASCADI_ROOT_PREF + PASCADI_COEFFICIENT_NORM + PASCADI_GEOMETRY
)
PASCADI_FIXED = COMPLETION + PASCADI_BEFORE_COMPLETION
LITERAL_COR511_RECOMBINATION = V / 2
LITERAL_COR511_BEFORE_COMPLETION = (
    PASCADI_BEFORE_COMPLETION + LITERAL_COR511_RECOMBINATION
)
LITERAL_COR511_FIXED = COMPLETION + LITERAL_COR511_BEFORE_COMPLETION

NORMALIZED_OPTIMISTIC_LOG = F(0)
RAW_LONG_LOG = F(2)
LITERAL_COR511_DUAL_DYADIC_LOG = F(1)
LITERAL_COR511_RAW_LOG = RAW_LONG_LOG + LITERAL_COR511_DUAL_DYADIC_LOG
GRANTED_GENERAL_B_DIVISOR_LOG = F(1)
GRANTED_GENERAL_B_NORMALIZED_LOG = (
    LITERAL_COR511_DUAL_DYADIC_LOG + GRANTED_GENERAL_B_DIVISOR_LOG
)
GRANTED_GENERAL_B_RAW_LOG = RAW_LONG_LOG + GRANTED_GENERAL_B_NORMALIZED_LOG

assert U == F(43, 200)
assert P == F(83, 100)
assert V == K == F(43, 100)
assert R == F(33, 50)
assert COMPLETION == -F(43, 100)
assert KR_LENGTH == F(109, 100)
assert CHARACTER_FAMILY == F(83, 50)
assert CHAR_V_NORM == F(209, 200)
assert CHAR_KR_NORM == F(11, 8)
assert CHAR_FIXED == F(199, 100)
assert CHAR_FIXED - BUDGET == F(33, 100)
assert CHAR_FIXED - SQ4_HB == F(1, 2)
assert CHAR_FIXED + PHYSICAL_X == F(44, 25)
assert CHAR_FIXED + PHYSICAL_X - INTEGRATED_BUDGET == F(33, 100)
assert FIXED_PV_SQRT == F(179, 100)
assert FIXED_PV_SQRT - BUDGET == F(13, 100)
assert FIXED_PV_SQRT - SQ4_HB == F(3, 10)
assert FIXED_PV_SQRT + PHYSICAL_X == F(39, 25)
assert BP_H1 == F(7, 320)
assert BP_H2 == F(1, 3200)
assert BP_H3 == F(27, 500)
assert BP_H4 == F(71, 900)
assert BP_H5 == -F(17, 1500)
assert BP_H == F(71, 900)
assert BP_FIXED_PV_INNER == F(2617, 1800)
assert BP_FIXED_PV_OUTER == F(4111, 1800)
assert BP_FIXED_PV_OUTER - BUDGET == F(1123, 1800)
assert BP_FIXED_PV_OUTER - SQ4_HB == F(1429, 1800)
assert BP_FIXED_PV_OUTER + PHYSICAL_X == F(3697, 1800)
assert ELL == F(23, 100)
assert KSWX_A1 == -F(89, 400)
assert KSWX_A2 == -F(43, 100)
assert KSWX_A3 == -F(43, 200)
assert KSWX_DELTA_A == -F(43, 200)
assert KSWX_B1 == -F(129, 400)
assert KSWX_B2 == -F(43, 200)
assert KSWX_DELTA_B == -F(43, 200)
assert KSWX_C1 == -F(83, 400)
assert KSWX_C2 == -F(43, 200)
assert KSWX_DELTA_C == -F(83, 400)
assert KSWX_BEST_DELTA == -F(43, 200)
assert KSWX_PER_P_ELL == F(59, 40)
assert KSWX_FIXED == F(421, 200)
assert KSWX_FIXED - BUDGET == F(89, 200)
assert KSWX_FIXED - SQ4_HB == F(123, 200)
assert KSWX_FIXED + PHYSICAL_X == F(15, 8)
assert KSWX_RECIPROCITY_ERROR == F(267, 200)
assert KSWX_RECIPROCITY_ETA == KSWX_RECIPROCITY_EPSILON == F(1, 20)
assert KSWX_RECIPROCITY_ERROR_ALLOCATED == F(287, 200)
assert SQ4_HB - KSWX_RECIPROCITY_ERROR_ALLOCATED == F(11, 200)

assert LEVEL == F(43, 50)
assert SECOND_INDEX == F(109, 100)
assert PASCADI_ROOT_PREF == F(129, 200)
assert PASCADI_COEFFICIENT_NORM == F(19, 25)
assert PASCADI_A == F(63, 50)
assert PASCADI_B == F(19, 25)
assert PASCADI_C == F(209, 200)
assert PASCADI_D == F(11, 8)
assert PASCADI_GEOMETRY == F(11, 8)
assert PASCADI_BEFORE_COMPLETION == F(139, 50)
assert PASCADI_FIXED == F(47, 20)
assert PASCADI_FIXED - BUDGET == F(69, 100)
assert PASCADI_FIXED - SQ4_HB == F(43, 50)
assert PASCADI_FIXED + PHYSICAL_X == F(53, 25)
assert PASCADI_FIXED + PHYSICAL_X - INTEGRATED_BUDGET == F(69, 100)
assert LITERAL_COR511_RECOMBINATION == F(43, 200)
assert LITERAL_COR511_BEFORE_COMPLETION == F(599, 200)
assert LITERAL_COR511_FIXED == F(513, 200)
assert LITERAL_COR511_FIXED - BUDGET == F(181, 200)
assert LITERAL_COR511_FIXED - SQ4_HB == F(43, 40)
assert LITERAL_COR511_FIXED + PHYSICAL_X == F(467, 200)
assert NORMALIZED_OPTIMISTIC_LOG == 0
assert RAW_LONG_LOG == 2
assert LITERAL_COR511_DUAL_DYADIC_LOG == 1
assert LITERAL_COR511_RAW_LOG == 3
assert GRANTED_GENERAL_B_DIVISOR_LOG == 1
assert GRANTED_GENERAL_B_NORMALIZED_LOG == 2
assert GRANTED_GENERAL_B_RAW_LOG == 4


def row(label: str, value: F) -> None:
    print(f"{label} = {value} ({float(value):.12f})")


print("A1 SQ4 correlated-moment exact exponent audit")
row("one short Mobius slot U", U)
row("product modulus side P", P)
row("two-slot product V", V)
row("Poisson dual length K", K)
row("source numerator R", R)
row("completion prefactor", COMPLETION)
row("SQ4-HB target", SQ4_HB)
row("literal fixed-x budget", BUDGET)
print()
print("generalized-Gauss-product character moment + one coefficient-blind Cauchy")
row("modulus-character family exponent", CHARACTER_FAMILY)
row("v-pair character norm", CHAR_V_NORM)
row("k*r character norm", CHAR_KR_NORM)
row("fixed-x output", CHAR_FIXED)
row("excess above literal budget", CHAR_FIXED - BUDGET)
row("excess above SQ4-HB", CHAR_FIXED - SQ4_HB)
row("integrated output", CHAR_FIXED + PHYSICAL_X)
row("integrated budget excess", CHAR_FIXED + PHYSICAL_X - INTEGRATED_BUDGET)
print()
print("fixed-(p,v) ideal k,r square-root class")
row("fixed-x output", FIXED_PV_SQRT)
row("excess above literal budget", FIXED_PV_SQRT - BUDGET)
row("excess above SQ4-HB", FIXED_PV_SQRT - SQ4_HB)
row("integrated output", FIXED_PV_SQRT + PHYSICAL_X)
print()
print("Blomer--Pascadi Theorem 5.5 on a fixed-(p,v) k,r block")
row("H first summand", BP_H1)
row("H second summand", BP_H2)
row("H third summand", BP_H3)
row("H fourth summand", BP_H4)
row("H fifth summand", BP_H5)
row("dominant H exponent", BP_H)
row("fixed-(p,v) inner bilinear output", BP_FIXED_PV_INNER)
row("outer-triangled fixed-x output", BP_FIXED_PV_OUTER)
row("excess above literal budget", BP_FIXED_PV_OUTER - BUDGET)
row("excess above SQ4-HB", BP_FIXED_PV_OUTER - SQ4_HB)
row("integrated output", BP_FIXED_PV_OUTER + PHYSICAL_X)
print("status = LITERAL FIXED-BLOCK APPLICATION; OUTER CORRELATION DISCARDED")
print()
print("Kerr--Shparlinski--Wu--Xi favourable Type-I class")
row("source ell exponent", ELL)
row("Delta1 first candidate", KSWX_DELTA_A)
row("Delta1 second candidate", KSWX_DELTA_B)
row("Delta1 third candidate", KSWX_DELTA_C)
row("best Delta1 exponent", KSWX_BEST_DELTA)
row("per-(p,ell) output", KSWX_PER_P_ELL)
row("fixed-x output", KSWX_FIXED)
row("excess above literal budget", KSWX_FIXED - BUDGET)
row("excess above SQ4-HB", KSWX_FIXED - SQ4_HB)
row("integrated output", KSWX_FIXED + PHYSICAL_X)
row("reciprocity-phase base error", KSWX_RECIPROCITY_ERROR)
row("Poisson eta allocation", KSWX_RECIPROCITY_ETA)
row("aggregate epsilon allocation", KSWX_RECIPROCITY_EPSILON)
row("allocated reciprocity-phase error", KSWX_RECIPROCITY_ERROR_ALLOCATED)
row("allocated reciprocity-error margin below SQ4-HB", SQ4_HB - KSWX_RECIPROCITY_ERROR_ALLOCATED)
print("status = FAVOURABLE COEFFICIENT-NORM/COPRIME GRANTS; POWER-KILLED")
print()
print("squarefree-v Ramanujan lift + Pascadi geometry")
row("lifted level q=(u1*u2)*v", LEVEL)
row("lifted first index k", K)
row("lifted second index v*r", SECOND_INDEX)
row("lifted quotient modulus", SMOOTH)
row("sqrt(q*k) prefactor", PASCADI_ROOT_PREF)
row("level/second-index coefficient norm", PASCADI_COEFFICIENT_NORM)
row("Pascadi A=S*sqrt(R)*C", PASCADI_A)
row("Pascadi B=sqrt(M*N)", PASCADI_B)
row("Pascadi C=sqrt(S*M)*C", PASCADI_C)
row("Pascadi D=sqrt(S*N)*C", PASCADI_D)
row("Pascadi rational geometry factor", PASCADI_GEOMETRY)
row("output before Poisson prefactor", PASCADI_BEFORE_COMPLETION)
row("fixed-x output", PASCADI_FIXED)
row("excess above literal budget", PASCADI_FIXED - BUDGET)
row("excess above SQ4-HB", PASCADI_FIXED - SQ4_HB)
row("integrated output", PASCADI_FIXED + PHYSICAL_X)
row("integrated budget excess", PASCADI_FIXED + PHYSICAL_X - INTEGRATED_BUDGET)
print("status = CONDITIONAL ARITHMETIC UNDER UNSTATED GENERAL-b VARIANT")
print()
print("literal stated Corollary 5.11 via separate (d,a) applications")
row("additive recombination power", LITERAL_COR511_RECOMBINATION)
row("output before Poisson prefactor", LITERAL_COR511_BEFORE_COMPLETION)
row("fixed-x output", LITERAL_COR511_FIXED)
row("excess above literal budget", LITERAL_COR511_FIXED - BUDGET)
row("excess above SQ4-HB", LITERAL_COR511_FIXED - SQ4_HB)
row("integrated output", LITERAL_COR511_FIXED + PHYSICAL_X)
print()
row("optimistic normalized auxiliary log exponent", NORMALIZED_OPTIMISTIC_LOG)
row("raw long-slot log exponent", RAW_LONG_LOG)
row("literal Cor5.11 k-dyadic scale log exponent", LITERAL_COR511_DUAL_DYADIC_LOG)
row("literal Cor5.11 raw fixed log exponent", LITERAL_COR511_RAW_LOG)
row("granted general-b divisor log exponent", GRANTED_GENERAL_B_DIVISOR_LOG)
row("granted general-b normalized fixed log exponent", GRANTED_GENERAL_B_NORMALIZED_LOG)
row("granted general-b raw fixed log exponent", GRANTED_GENERAL_B_RAW_LOG)
print("all divisor, Mellin, and theorem losses are displayed as T^epsilon")
print("verdict coefficient-blind generalized-Gauss-product moment = POWER-KILLED")
print("verdict fixed-(p,v) square-root-only chain = POWER-KILLED")
print("verdict fixed-(p,v) Blomer--Pascadi chain = APPLICABLE LOCALLY AND POWER-KILLED")
print("verdict favourable Kerr--Shparlinski--Wu--Xi Type-I chain = POWER-KILLED")
print("verdict literal squarefree-v Cor5.11 additive chain = POWER-KILLED")
print("verdict favourable general-b geometry = CONDITIONAL AND POWER-KILLED")
print("non-squarefree v with gcd(v1,v2) not dividing k = STRUCTURALLY OUTSIDE THE LIFT")
print("survivor = signed generalized-Gauss-product level moment before Cauchy")
