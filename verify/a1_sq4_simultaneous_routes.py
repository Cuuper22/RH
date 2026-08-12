#!/usr/bin/env python3
"""Exact Fraction audit for six simultaneous SQ4 method classes."""

from fractions import Fraction as F


P = F(83, 100)
Q = F(83, 100)
R = F(33, 50)
SMOOTH = F(2, 5)
MU_PAIR = F(43, 100)
PHYSICAL_X = -F(23, 100)
FIXED_TARGET = F(83, 50)
INTEGRATED_TARGET = F(143, 100)
NORMALIZED_AUX_LOG = F(0)
RAW_LONG_LOG = F(2)

CHAR_CONDUCTOR = max(2 * Q, P) / 2
CHAR_FIXED = P / 2 + Q / 2 + CHAR_CONDUCTOR + R

NORM_ONLY_OPERATOR = max(P, Q) / 2
NORM_ONLY_FIXED = P / 2 + Q / 2 + NORM_ONLY_OPERATOR + R

ADDITIVE_FACTOR = max(R, 2 * Q) / 2
ADDITIVE_FIXED = P / 2 + Q / 2 + R / 2 + ADDITIVE_FACTOR

DUAL = P - SMOOTH
COMPLETION_PREFACTOR = SMOOTH - P
NORMALIZED_LONG_ARGUMENT = MU_PAIR + SMOOTH + PHYSICAL_X - F(3, 5)
RECIPROCITY_PROFILE_PARAMETER = R - P - MU_PAIR - SMOOTH
TRUNCATION_RATIO = DUAL - P
ZERO_MODE_FIXED = COMPLETION_PREFACTOR + P + MU_PAIR + R
WEIL_TRIANGLE_FIXED = (
    COMPLETION_PREFACTOR + P + MU_PAIR + R + DUAL + P / 2
)

assert P == Q == F(83, 100)
assert DUAL == MU_PAIR == F(43, 100)
assert MU_PAIR + SMOOTH == P
assert CHAR_CONDUCTOR == F(83, 100)
assert CHAR_FIXED == F(58, 25)
assert CHAR_FIXED - FIXED_TARGET == F(33, 50)
assert CHAR_FIXED + PHYSICAL_X == F(209, 100)
assert CHAR_FIXED + PHYSICAL_X - INTEGRATED_TARGET == F(33, 50)
assert NORM_ONLY_OPERATOR == F(83, 200)
assert NORM_ONLY_FIXED == F(381, 200)
assert NORM_ONLY_FIXED - FIXED_TARGET == F(49, 200)
assert NORM_ONLY_FIXED + PHYSICAL_X == F(67, 40)
assert NORM_ONLY_FIXED + PHYSICAL_X - INTEGRATED_TARGET == F(49, 200)
assert ADDITIVE_FACTOR == F(83, 100)
assert ADDITIVE_FIXED == F(199, 100)
assert ADDITIVE_FIXED - FIXED_TARGET == F(33, 100)
assert ADDITIVE_FIXED + PHYSICAL_X == F(44, 25)
assert ADDITIVE_FIXED + PHYSICAL_X - INTEGRATED_TARGET == F(33, 100)
assert COMPLETION_PREFACTOR == -F(43, 100)
assert NORMALIZED_LONG_ARGUMENT == 0
assert RECIPROCITY_PROFILE_PARAMETER == -1
assert TRUNCATION_RATIO == -F(2, 5)
assert ZERO_MODE_FIXED == F(149, 100)
assert FIXED_TARGET - ZERO_MODE_FIXED == F(17, 100)
assert ZERO_MODE_FIXED + PHYSICAL_X == F(63, 50)
assert INTEGRATED_TARGET - (ZERO_MODE_FIXED + PHYSICAL_X) == F(17, 100)
assert WEIL_TRIANGLE_FIXED == F(467, 200)
assert WEIL_TRIANGLE_FIXED - FIXED_TARGET == F(27, 40)
assert WEIL_TRIANGLE_FIXED + PHYSICAL_X == F(421, 200)
assert WEIL_TRIANGLE_FIXED + PHYSICAL_X - INTEGRATED_TARGET == F(27, 40)
assert NORMALIZED_AUX_LOG == 0
assert RAW_LONG_LOG == 2


def row(label: str, value: F) -> None:
    print(f"{label} = {value} ({float(value):.12f})")


print("A1 SQ4 simultaneous-route exact exponent audit")
row("product side P", P)
row("product side Q", Q)
row("numerator R", R)
row("physical x", PHYSICAL_X)
row("fixed target", FIXED_TARGET)
row("integrated target", INTEGRATED_TARGET)
print()
print("multiplicative Fourier + one all-modulus character large sieve")
row("conductor factor sqrt(Q^2+P)", CHAR_CONDUCTOR)
row("fixed-x output after triangle in r", CHAR_FIXED)
row("fixed-x excess", CHAR_FIXED - FIXED_TARGET)
row("integrated output", CHAR_FIXED + PHYSICAL_X)
row("integrated excess", CHAR_FIXED + PHYSICAL_X - INTEGRATED_TARGET)
row("normalized extra log exponent granted", NORMALIZED_AUX_LOG)
row("raw long-slot log exponent", RAW_LONG_LOG)
print()
print("coefficient-uniform two-sided norm-only operator")
row("unavoidable single-column operator exponent", NORM_ONLY_OPERATOR)
row("fixed-x output after triangle in r", NORM_ONLY_FIXED)
row("fixed-x excess", NORM_ONLY_FIXED - FIXED_TARGET)
row("integrated output", NORM_ONLY_FIXED + PHYSICAL_X)
row("integrated excess", NORM_ONLY_FIXED + PHYSICAL_X - INTEGRATED_TARGET)
row("normalized extra log exponent granted", NORMALIZED_AUX_LOG)
row("raw long-slot log exponent", RAW_LONG_LOG)
print()
print("one additive large sieve in r on reciprocal Farey points")
row("factor sqrt(R+Q^2)", ADDITIVE_FACTOR)
row("fixed-x output", ADDITIVE_FIXED)
row("fixed-x excess", ADDITIVE_FIXED - FIXED_TARGET)
row("integrated output", ADDITIVE_FIXED + PHYSICAL_X)
row("integrated excess", ADDITIVE_FIXED + PHYSICAL_X - INTEGRATED_TARGET)
row("normalized extra log exponent granted", NORMALIZED_AUX_LOG)
row("raw long-slot log exponent", RAW_LONG_LOG)
print()
print("reciprocity + Poisson in one smooth slot")
row("dual frequency K=P-M", DUAL)
row("completion prefactor M-P", COMPLETION_PREFACTOR)
row("normalized long-profile argument", NORMALIZED_LONG_ARGUMENT)
row("reciprocity profile parameter", RECIPROCITY_PROFILE_PARAMETER)
row("truncation ratio K/P before eta", TRUNCATION_RATIO)
row("zero-mode fixed-x power", ZERO_MODE_FIXED)
row("zero-mode margin", FIXED_TARGET - ZERO_MODE_FIXED)
row("zero-mode integrated power", ZERO_MODE_FIXED + PHYSICAL_X)
row("zero-mode integrated margin", INTEGRATED_TARGET - (ZERO_MODE_FIXED + PHYSICAL_X))
row("nonzero Weil-triangle fixed-x output", WEIL_TRIANGLE_FIXED)
row("nonzero Weil-triangle excess", WEIL_TRIANGLE_FIXED - FIXED_TARGET)
row("nonzero Weil-triangle integrated output", WEIL_TRIANGLE_FIXED + PHYSICAL_X)
row("nonzero Weil-triangle integrated excess", WEIL_TRIANGLE_FIXED + PHYSICAL_X - INTEGRATED_TARGET)
print("zero-mode divisor losses recorded as T^epsilon, log exponent = 0")
print("nonzero truncation/divisor power loss = eta + epsilon")
row("nonzero truncation/divisor log exponent", NORMALIZED_AUX_LOG)
row("raw long-slot log exponent", RAW_LONG_LOG)
print()
print("verdict char-single-large-sieve = POWER-KILLED")
print("verdict prescribed-crude-norm-two-sided = POWER-KILLED")
print("verdict additive-r-large-sieve = POWER-KILLED")
print("verdict literal reciprocal-completed classical Kuznetsov = STRUCTURALLY INAPPLICABLE")
print("verdict direct moving-index divisor-switch = STRUCTURALLY INAPPLICABLE")
print("verdict reciprocal-Poisson-Weil-triangle = POWER-KILLED")
print("survivor = correlated four-slot moment or geometry-changing trace formula")
