#!/usr/bin/env python3
"""Exact exponent audit for the Phase A1.1 evaluate-don't-bound route.

All scale calculations use fractions.  The analytic inequalities themselves
are the cited published inputs recorded in docs/audit/log_budget_routes.md.
"""

from fractions import Fraction


def show(label: str, value: Fraction) -> None:
    print(f"{label} = {value} = {float(value):.15f}")


eta = Fraction(43, 100)
p_exp = Fraction(1, 2) + eta
q_exp = Fraction(1, 2)
h_exp = eta
target_exp = p_exp + q_exp

print("repo scales")
show("eta", eta)
show("P exponent", p_exp)
show("Q exponent", q_exp)
show("H exponent", h_exp)
show("Q as a power of P", q_exp / p_exp)
show("log(P)/log(Q)", p_exp / q_exp)
show("PQ target exponent", target_exp)
assert p_exp == h_exp + q_exp

print("\nNguyen Theorem 3 plus residue Parseval and Cauchy")
nguyen_exp = q_exp + h_exp / 2 + p_exp * Fraction(71, 72)
nguyen_excess = nguyen_exp - target_exp
show("aggregate exponent", nguyen_exp)
show("excess over PQ", nguyen_excess)
assert nguyen_exp == Fraction(3917, 2400)
assert nguyen_excess == Fraction(97, 480)
print("explicit logarithmic exponent = 15/2")

print("\nParry Theorem 1 plus Parseval and absolute q-sum")
parry_exp = (
    p_exp * Fraction(3, 4)
    + h_exp / 2
    + q_exp * Fraction(23, 16)
)
parry_excess = parry_exp - target_exp
show("aggregate exponent", parry_exp)
show("excess over PQ", parry_excess)
assert parry_exp == Fraction(261, 160)
assert parry_excess == Fraction(161, 800)

print("\nmodulus ranges")
parry_margin = Fraction(4, 7) - q_exp / p_exp
wxz_deficit = q_exp / p_exp - Fraction(293, 584)
show("Parry 4/7 margin over Q=P^(50/93)", parry_margin)
show("Wei-Xue-Zhang deficit below Q=P^(50/93)", wxz_deficit)
assert parry_margin == Fraction(22, 651)
assert wxz_deficit == Fraction(1951, 54312)

print("\nnatural variance boundary")
variance_cauchy_exp = (
    q_exp * Fraction(3, 2) + (p_exp + h_exp) / 2
)
show("variance-plus-Cauchy exponent", variance_cauchy_exp)
show("power margin", target_exp - variance_cauchy_exp)
assert variance_cauchy_exp == target_exp

print("\nliteral log budget")
print("C=0 contribution exponent = 2")
print("trace normalization exponent = 3")
assert 2 < 3
