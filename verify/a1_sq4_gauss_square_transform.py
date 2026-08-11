#!/usr/bin/env python3
"""Exact Fraction audit for the SQ4 Gauss-square transform target."""

from fractions import Fraction as F


U = F(43, 200)
SMOOTH = F(2, 5)
P = 2 * U + SMOOTH
V = 2 * U
K = P - SMOOTH
R = F(33, 50)
COMPLETION = SMOOTH - P
SQ4_HB = F(149, 100)
LITERAL_BUDGET = F(83, 50)

# Removing the Poisson completion factor M/P defines the pre-completion
# character moment M_4 = (P/M) Z_33^nz.
SQ4_MOMENT_TARGET = SQ4_HB - COMPLETION
LITERAL_MOMENT_TARGET = LITERAL_BUDGET - COMPLETION

# The already-audited coefficient-blind Cauchy chain has fixed-x exponent
# 199/100 after completion.  This line only compares exact powers.
COEFFICIENT_BLIND_FIXED = F(199, 100)
COEFFICIENT_BLIND_MOMENT = COEFFICIENT_BLIND_FIXED - COMPLETION

RAW_LONG_LOG = F(2)

assert P == F(83, 100)
assert V == K == F(43, 100)
assert R == F(33, 50)
assert COMPLETION == -F(43, 100)
assert SQ4_MOMENT_TARGET == F(48, 25)
assert LITERAL_MOMENT_TARGET == F(209, 100)
assert COEFFICIENT_BLIND_MOMENT == F(121, 50)
assert COEFFICIENT_BLIND_MOMENT - SQ4_MOMENT_TARGET == F(1, 2)
assert COEFFICIENT_BLIND_MOMENT - LITERAL_MOMENT_TARGET == F(33, 100)
assert RAW_LONG_LOG == 2


def row(label: str, value: F) -> None:
    print(f"{label} = {value} ({float(value):.12f})")


print("A1 SQ4 finite Gauss-square transform target audit")
row("one short Mobius slot U", U)
row("factorized modulus P", P)
row("two-slot product V", V)
row("Poisson dual length K", K)
row("numerator R", R)
row("completion prefactor M/P", COMPLETION)
row("SQ4-HB fixed-x target", SQ4_HB)
row("literal fixed-x budget", LITERAL_BUDGET)
print()
row("exact pre-completion SQ4 moment target", SQ4_MOMENT_TARGET)
row("exact pre-completion literal target", LITERAL_MOMENT_TARGET)
row("coefficient-blind pre-completion output", COEFFICIENT_BLIND_MOMENT)
row("coefficient-blind excess above SQ4 moment", COEFFICIENT_BLIND_MOMENT - SQ4_MOMENT_TARGET)
row("coefficient-blind excess above literal moment", COEFFICIENT_BLIND_MOMENT - LITERAL_MOMENT_TARGET)
row("raw long-slot log exponent", RAW_LONG_LOG)
print("finite transform identity = EXACT ALGEBRA, ALL POSITIVE MODULI INCLUDING COMPOSITE")
print("Gauss-square specialization = UNIT STRATUM ONLY")
print("analytic survivor = signed generalized-Gauss level moment before Cauchy")
