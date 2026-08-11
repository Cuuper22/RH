#!/usr/bin/env python3
"""Exact rational audit of the proposed eta > 1/2 terminal factorization.

All decisions use fractions.Fraction.  The rational value eta = 3/4 is a
single legal member of the claimed uniform range and therefore suffices as a
counterexample to a universal relabel-only construction.
"""

from fractions import Fraction


def show(label: str, value: Fraction) -> None:
    print(f"{label} = {value} = {float(value):.15f}")


eta = Fraction(3, 4)
one = Fraction(1)
half = Fraction(1, 2)
delta = (one - eta) / 2
x_exp = one + eta
hb_cutoff = x_exp / 3
mu_exp = eta / 2
smooth_exp = half

print("B4 eta-closure exact rational audit")
show("eta", eta)
show("delta = (1-eta)/2", delta)
assert 0 < delta < half

print("\nlegal K=3, j=2 balanced Heath--Brown block")
show("X exponent", x_exp)
show("K=3 truncated cutoff exponent", hb_cutoff)
show("each of two truncated exponents", mu_exp)
show("each of two unrestricted exponents", smooth_exp)
assert mu_exp <= hb_cutoff
assert 2 * mu_exp + 2 * smooth_exp == x_exp
print("cutoff and product checks = PASS")

print("\nliteral relabel-only split")
available_after_A = {Fraction(0), half, one}
target_m1 = one - eta
show("target M1 exponent", target_m1)
print("available subproduct exponents = " + ", ".join(str(x) for x in sorted(available_after_A)))
assert target_m1 not in available_after_A

# Check that, among whole-variable groupings of two mu atoms and two smooth
# atoms, the only group of exponent eta is the two-mu group.
groups_at_A = []
for mu_count in range(3):
    for smooth_count in range(3):
        exponent = mu_count * mu_exp + smooth_count * smooth_exp
        if exponent == eta:
            groups_at_A.append((mu_count, smooth_count))
assert groups_at_A == [(2, 0)]
print(f"whole-variable groups having exponent A=eta = {groups_at_A}")
print("requested M1 split is unavailable = PASS")

print("\nconditional asymmetric single-block algebra")
p_asym = eta + (one - eta)
q_asym = eta
h_exp = eta
trace = one + eta
show("P exponent", p_asym)
show("Q exponent", q_asym)
show("H exponent", h_exp)
show("P Q exponent", p_asym + q_asym)
show("trace exponent", trace)
assert p_asym + q_asym == trace
assert p_asym + h_exp == trace

print("\nbalanced block obstruction")
p_bal = eta + half
q_bal = eta + half
pq_bal = p_bal + q_bal
ph_bal = p_bal + eta
show("balanced P exponent", p_bal)
show("balanced Q exponent", q_bal)
show("balanced P Q exponent", pq_bal)
show("P Q excess over trace", pq_bal - trace)
show("balanced P H exponent", ph_bal)
show("P H excess over trace", ph_bal - trace)
assert pq_bal - trace == eta
assert ph_bal - trace == eta - half

print("\npreliminary zero-shift replacement")
eps = Fraction(1, 14)
eps_threshold = (one - eta) / (one + eta)
preliminary = 2 * eta + (one + eta) * eps
show("epsilon", eps)
show("epsilon threshold", eps_threshold)
show("H^2 (AM)^epsilon exponent", preliminary)
show("power saving against trace", trace - preliminary)
assert eps < eps_threshold
assert preliminary < trace
assert trace - preliminary == Fraction(1, 8)

print("\nliteral prime-dyadic logarithmic threshold")
print("contribution exponent in log T = C + 2")
print("budget exponent in log T = 3")
print("closure requires C < 1; every C >= 1 fails")
print("all exact checks = PASS")
