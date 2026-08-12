#!/usr/bin/env python3
"""Exact integer/Fraction audit of the eta=3/4 support-model obstruction."""

from fractions import Fraction


def ordered_factor_pairs(n: int) -> list[tuple[int, int]]:
    """Enumerate exact ordered positive factor pairs, without floating point."""
    return [(d, n // d) for d in range(1, n + 1) if n % d == 0]


eta = Fraction(3, 4)
trace = 1 + eta
balanced_atom = Fraction(1, 2)
short = 1 - eta
long = eta
p_exp = eta + balanced_atom
q_exp = eta + balanced_atom
h_exp = eta
pq_exp = p_exp + q_exp
ph_exp = p_exp + h_exp

base = 5
T = base**4
short_box = range(base, 2 * base + 1)
balanced_box = range(base**2, 2 * base**2 + 1)
long_box = range(base**3, 2 * base**3 + 1)
witness = 29 * 31
witness_pairs = ordered_factor_pairs(witness)
balanced_pairs = [
    (left, right)
    for left, right in witness_pairs
    if left in balanced_box and right in balanced_box
]
short_long_pairs = [
    (left, right)
    for left, right in witness_pairs
    if left in short_box and right in long_box
]

print("B4 eta-superposition support-model exact audit")
print(f"eta = {eta}")
print(f"trace exponent = {trace}")
print(f"balanced atom exponent = {balanced_atom}")
print(f"short/long exponents = {short}, {long}")
assert short == Fraction(1, 4)
assert short + long == 1

print(f"base scale T = {T}")
print(f"short box = [{short_box.start},{short_box.stop - 1}]")
print(f"balanced box = [{balanced_box.start},{balanced_box.stop - 1}]")
print(f"long box = [{long_box.start},{long_box.stop - 1}]")
assert T == 625
assert base**1 == 5
assert base**2 == 25
assert base**3 == 125

print(f"witness ordered products = 29*31, 31*29 = {witness}")
print(f"ordered factor pairs = {witness_pairs}")
print(f"balanced supported pairs = {balanced_pairs}")
print(f"short-long supported pairs = {short_long_pairs}")
assert witness == 899
assert balanced_pairs == [(29, 31), (31, 29)]
assert short_long_pairs == []
assert all(witness % r != 0 for r in short_box)
print("common-short-support finite support model = POINTWISE IMPOSSIBLE")

print(f"P exponent = {p_exp}")
print(f"Q exponent = {q_exp}")
print(f"H exponent = {h_exp}")
print(f"PQ exponent/excess = {pq_exp}, {pq_exp - trace}")
print(f"PH exponent/excess = {ph_exp}, {ph_exp - trace}")
assert pq_exp - trace == eta
assert ph_exp - trace == eta - Fraction(1, 2)
assert pq_exp > trace
assert ph_exp > trace
print("positive P(Q+H) majorant = POWER-INCOMPATIBLE")
print("survivor = piece leaving excluded box, retained variables, or non-pointwise identity")
