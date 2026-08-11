#!/usr/bin/env python3
"""Exact Fraction replay for the published-theorem SQ4 literature audit.

This script checks only rational power and fixed-log bookkeeping.  It does
not assert any cited analytic theorem or any applicability statement.
"""

from fractions import Fraction as F


# Source scales.
U = F(43, 200)
SMOOTH = F(2, 5)
P = 2 * U + SMOOTH
V = 2 * U
K = P - SMOOTH
R = F(33, 50)
ELL = R - V
COMPLETION = SMOOTH - P

# The target in the exact pre-completion normalization M4=(P/M) Z_nz.
PRECOMPLETION_TARGET = F(48, 25)
COMPLETED_TARGET = PRECOMPLETION_TARGET + COMPLETION


def precompletion(completed: F) -> F:
    """Remove the Poisson completion prefactor from a completed exponent."""

    return completed - COMPLETION


# Existing coefficient-blind and locally square-root method classes.
CHARACTER_FAMILY = 2 * P
KR_LENGTH = K + R
CHAR_V_NORM = (CHARACTER_FAMILY + V) / 2
CHAR_KR_NORM = (max(CHARACTER_FAMILY, KR_LENGTH) + KR_LENGTH) / 2
CHARACTER_COMPLETED = COMPLETION + CHAR_V_NORM + CHAR_KR_NORM
CHARACTER_PRECOMPLETION = precompletion(CHARACTER_COMPLETED)

FIXED_PV_SQRT_COMPLETED = COMPLETION + P + V + (K + R) / 2 + P / 2
FIXED_PV_SQRT_PRECOMPLETION = precompletion(FIXED_PV_SQRT_COMPLETED)

WEIL_TRIANGLE_COMPLETED = COMPLETION + P + V + R + K + P / 2
WEIL_TRIANGLE_PRECOMPLETION = precompletion(WEIL_TRIANGLE_COMPLETED)

# Shparlinski, Trans. AMS 371 (2019), Theorem 2.1, in the explicitly
# favourable fixed-(p,ell,t) unit/coprime class.  The granted collapsed
# coefficient norms are ||alpha||_1 <= T^(2V+eps) and
# ||alpha||_2 <= T^(V+eps); the theorem interval is h of length T^V.
SHP19_ALPHA_L1 = 2 * V
SHP19_ALPHA_L2 = V
SHP19_NORM_FACTOR = (SHP19_ALPHA_L1 + SHP19_ALPHA_L2) / 2
SHP19_KERNEL_1 = V / 8 + P
SHP19_KERNEL_2 = V / 2 + 3 * P / 4
SHP19_KERNEL = max(SHP19_KERNEL_1, SHP19_KERNEL_2)
SHP19_LOCAL = SHP19_NORM_FACTOR + SHP19_KERNEL
SHP19_PRECOMPLETION = P + ELL + SHP19_LOCAL

# Theorem 2.2's good-modulus base power at moment parameter s=2, under the
# same favourable coefficient grants.  Its exceptional moduli remain
# uncontrolled by that theorem, so this is not a full-family route.
SHP19_ALMOST_ALL_S = F(2)
SHP19_AA_NORM = (
    SHP19_ALPHA_L1 * (1 - 1 / SHP19_ALMOST_ALL_S)
    + SHP19_ALPHA_L2 / SHP19_ALMOST_ALL_S
)
SHP19_AA_KERNEL_1 = P
SHP19_AA_KERNEL_2 = (
    V / 2 + P * (F(1, 2) + 1 / (2 * SHP19_ALMOST_ALL_S))
)
SHP19_AA_KERNEL = max(SHP19_AA_KERNEL_1, SHP19_AA_KERNEL_2)
SHP19_AA_PRECOMPLETION = P + ELL + SHP19_AA_NORM + SHP19_AA_KERNEL

# Blomer--Pascadi arXiv:2607.24311v1, Theorem 5.5 (preprint), included only
# to distinguish the closest locally applicable preprint from published
# inputs.  This repeats the exact five H-powers already audited elsewhere.
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
BP_INNER = (K + R) / 2 + P + BP_H
BP_COMPLETED = COMPLETION + P + V + BP_INNER
BP_PRECOMPLETION = precompletion(BP_COMPLETED)

# Kerr--Shparlinski--Wu--Xi, JLMS 108 (2023), Theorem 2.1, under the
# favourable coprimality and collapsed-L2 grants of the existing audit.
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
KSWX_COMPLETED = COMPLETION + P + ELL + KSWX_PER_P_ELL
KSWX_PRECOMPLETION = precompletion(KSWX_COMPLETED)

# Pascadi, Forum Math. Pi 14 (2026), Corollary 5.11.  The favourable
# general-first-sequence value is conditional; the larger value is the
# literal separate-(d,a) recombination on the squarefree-v lift.
LEVEL = 2 * V
SECOND_INDEX = V + R
PASCADI_ROOT = (LEVEL + K) / 2
PASCADI_COEFF = (LEVEL + R) / 2
PASCADI_A = LEVEL + SMOOTH
PASCADI_B = (K + SECOND_INDEX) / 2
PASCADI_C = (LEVEL + K) / 2 + SMOOTH
PASCADI_D = (LEVEL + SECOND_INDEX) / 2 + SMOOTH
PASCADI_GEOMETRY = (
    max(PASCADI_A, PASCADI_B, PASCADI_C)
    + max(PASCADI_A, PASCADI_B, PASCADI_D)
    - max(PASCADI_A, PASCADI_B)
)
PASCADI_CONDITIONAL_PRECOMPLETION = PASCADI_ROOT + PASCADI_COEFF + PASCADI_GEOMETRY
PASCADI_LITERAL_RECOMBINATION = V / 2
PASCADI_LITERAL_PRECOMPLETION = (
    PASCADI_CONDITIONAL_PRECOMPLETION + PASCADI_LITERAL_RECOMBINATION
)

# Fixed logarithmic exponents, reconstructed from their primitive sources.
# Every q^o or theorem loss is recorded as T^epsilon rather than assigned an
# unsupported fixed logarithmic power.
STANDARD_NORMALIZED_LOG = F(0)
RAW_LONG_SLOT_LOG = F(2)
PASCADI_LITERAL_DUAL_DYADIC_LOG = F(1)
PASCADI_CONDITIONAL_DIVISOR_LOG = F(1)

STANDARD_RAW_LOG = RAW_LONG_SLOT_LOG + STANDARD_NORMALIZED_LOG
PASCADI_LITERAL_NORMALIZED_LOG = PASCADI_LITERAL_DUAL_DYADIC_LOG
PASCADI_LITERAL_RAW_LOG = RAW_LONG_SLOT_LOG + PASCADI_LITERAL_NORMALIZED_LOG
PASCADI_CONDITIONAL_NORMALIZED_LOG = (
    PASCADI_LITERAL_DUAL_DYADIC_LOG + PASCADI_CONDITIONAL_DIVISOR_LOG
)
PASCADI_CONDITIONAL_RAW_LOG = (
    RAW_LONG_SLOT_LOG + PASCADI_CONDITIONAL_NORMALIZED_LOG
)


assert U == F(43, 200)
assert P == F(83, 100)
assert V == K == F(43, 100)
assert R == F(33, 50)
assert ELL == F(23, 100)
assert COMPLETION == -F(43, 100)
assert PRECOMPLETION_TARGET == F(48, 25)
assert COMPLETED_TARGET == F(149, 100)

assert CHARACTER_PRECOMPLETION == F(121, 50)
assert CHARACTER_PRECOMPLETION - PRECOMPLETION_TARGET == F(1, 2)
assert FIXED_PV_SQRT_PRECOMPLETION == F(111, 50)
assert FIXED_PV_SQRT_PRECOMPLETION - PRECOMPLETION_TARGET == F(3, 10)
assert WEIL_TRIANGLE_PRECOMPLETION == F(553, 200)
assert WEIL_TRIANGLE_PRECOMPLETION - PRECOMPLETION_TARGET == F(169, 200)

assert SHP19_ALPHA_L1 == F(43, 50)
assert SHP19_ALPHA_L2 == F(43, 100)
assert SHP19_NORM_FACTOR == F(129, 200)
assert SHP19_KERNEL_1 == F(707, 800)
assert SHP19_KERNEL_2 == F(67, 80)
assert SHP19_KERNEL == F(707, 800)
assert SHP19_LOCAL == F(1223, 800)
assert SHP19_PRECOMPLETION == F(2071, 800)
assert SHP19_PRECOMPLETION - PRECOMPLETION_TARGET == F(107, 160)

assert SHP19_AA_NORM == F(129, 200)
assert SHP19_AA_KERNEL_1 == F(83, 100)
assert SHP19_AA_KERNEL_2 == F(67, 80)
assert SHP19_AA_KERNEL == F(67, 80)
assert SHP19_AA_PRECOMPLETION == F(1017, 400)
assert SHP19_AA_PRECOMPLETION - PRECOMPLETION_TARGET == F(249, 400)

assert BP_H == F(71, 900)
assert BP_PRECOMPLETION == F(977, 360)
assert BP_PRECOMPLETION - PRECOMPLETION_TARGET == F(1429, 1800)
assert KSWX_PRECOMPLETION == F(507, 200)
assert KSWX_PRECOMPLETION - PRECOMPLETION_TARGET == F(123, 200)
assert PASCADI_CONDITIONAL_PRECOMPLETION == F(139, 50)
assert PASCADI_CONDITIONAL_PRECOMPLETION - PRECOMPLETION_TARGET == F(43, 50)
assert PASCADI_LITERAL_PRECOMPLETION == F(599, 200)
assert PASCADI_LITERAL_PRECOMPLETION - PRECOMPLETION_TARGET == F(43, 40)

assert STANDARD_NORMALIZED_LOG == 0
assert RAW_LONG_SLOT_LOG == 2
assert PASCADI_LITERAL_DUAL_DYADIC_LOG == 1
assert PASCADI_CONDITIONAL_DIVISOR_LOG == 1
assert STANDARD_RAW_LOG == 2
assert PASCADI_LITERAL_NORMALIZED_LOG == 1
assert PASCADI_LITERAL_RAW_LOG == 3
assert PASCADI_CONDITIONAL_NORMALIZED_LOG == 2
assert PASCADI_CONDITIONAL_RAW_LOG == 4


def row(label: str, value: F) -> None:
    print(f"{label} = {value} ({float(value):.12f})")


print("A1 SQ4 published-literature exact exponent audit")
row("pre-completion target", PRECOMPLETION_TARGET)
row("completion prefactor", COMPLETION)
row("completed SQ4-HB target", COMPLETED_TARGET)
print()
print("existing benchmark classes, replayed in pre-completion normalization")
row("coefficient-blind character output", CHARACTER_PRECOMPLETION)
row("coefficient-blind target excess", CHARACTER_PRECOMPLETION - PRECOMPLETION_TARGET)
row("fixed-(p,v) ideal joint-square-root output", FIXED_PV_SQRT_PRECOMPLETION)
row("fixed-(p,v) target excess", FIXED_PV_SQRT_PRECOMPLETION - PRECOMPLETION_TARGET)
row("direct Weil-triangle base output", WEIL_TRIANGLE_PRECOMPLETION)
row("direct Weil-triangle base target excess", WEIL_TRIANGLE_PRECOMPLETION - PRECOMPLETION_TARGET)
print("direct Weil-triangle also carries the explicit positive loss eta+epsilon")
print()
print("Shparlinski 2019 Theorem 2.1 favourable fixed-(p,ell,t) unit class")
row("granted alpha L1 exponent", SHP19_ALPHA_L1)
row("granted alpha L2 exponent", SHP19_ALPHA_L2)
row("sqrt(L1*L2) exponent", SHP19_NORM_FACTOR)
row("kernel term N^(1/8)*q", SHP19_KERNEL_1)
row("kernel term N^(1/2)*q^(3/4)", SHP19_KERNEL_2)
row("dominant kernel exponent", SHP19_KERNEL)
row("local fixed-(p,ell,t) output", SHP19_LOCAL)
row("outer-triangled pre-completion output", SHP19_PRECOMPLETION)
row("target excess", SHP19_PRECOMPLETION - PRECOMPLETION_TARGET)
print("status = FAVOURABLE UNIT/COPRIME AND COEFFICIENT-NORM GRANTS; POWER-KILLED")
print()
print("Shparlinski 2019 Theorem 2.2 good-modulus part at s=2")
row("mixed coefficient norm exponent", SHP19_AA_NORM)
row("kernel term q", SHP19_AA_KERNEL_1)
row("kernel term N^(1/2)*q^(3/4)", SHP19_AA_KERNEL_2)
row("good-modulus pre-completion base output", SHP19_AA_PRECOMPLETION)
row("good-modulus target excess", SHP19_AA_PRECOMPLETION - PRECOMPLETION_TARGET)
print("status = GOOD PART POWER-KILLED; THEOREM DOES NOT BOUND EXCEPTIONAL SOURCE MASS")
print()
print("other audited theorem classes in pre-completion normalization")
row("Blomer--Pascadi preprint fixed-(p,v) outer-triangle output", BP_PRECOMPLETION)
row("Blomer--Pascadi target excess", BP_PRECOMPLETION - PRECOMPLETION_TARGET)
row("KSWX favourable Type-I output", KSWX_PRECOMPLETION)
row("KSWX target excess", KSWX_PRECOMPLETION - PRECOMPLETION_TARGET)
row("Pascadi unstated-general-sequence conditional output", PASCADI_CONDITIONAL_PRECOMPLETION)
row("Pascadi conditional target excess", PASCADI_CONDITIONAL_PRECOMPLETION - PRECOMPLETION_TARGET)
row("Pascadi literal separate-(d,a) output", PASCADI_LITERAL_PRECOMPLETION)
row("Pascadi literal target excess", PASCADI_LITERAL_PRECOMPLETION - PRECOMPLETION_TARGET)
print()
row("standard normalized fixed log exponent", STANDARD_NORMALIZED_LOG)
row("standard raw fixed log exponent", STANDARD_RAW_LOG)
row("Pascadi literal normalized fixed log exponent", PASCADI_LITERAL_NORMALIZED_LOG)
row("Pascadi literal raw fixed log exponent", PASCADI_LITERAL_RAW_LOG)
row("Pascadi conditional normalized fixed log exponent", PASCADI_CONDITIONAL_NORMALIZED_LOG)
row("Pascadi conditional raw fixed log exponent", PASCADI_CONDITIONAL_RAW_LOG)
print("unspecified q^o, Mellin, truncation, and theorem losses are recorded as T^epsilon")
print("explicit Pascadi divisor/dyadic losses are the fixed log powers printed above")
print("headline = NO PUBLISHED THEOREM FOUND IN THE AUDITED CLASSES")
print("survivor = full signed conductor-stratified generalized-Gauss-product level moment")
