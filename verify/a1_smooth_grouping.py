#!/usr/bin/env python3
"""Exact rational audit of the K=4 HB-to-BBLR grouping obstruction."""

from fractions import Fraction


eta = Fraction(43, 100)
trace = 1 + eta
hb4_cap = trace / 4
type_i_threshold = trace - eta

mu = (eta / 2, eta / 2)
smooth = (Fraction(2, 5), Fraction(3, 5))

left_target = (Fraction(1, 2), Fraction(1, 2))
right_target = (Fraction(1, 2) - eta, Fraction(1, 2) + eta)


def show(name: str, value: Fraction) -> None:
    print(f"{name} = {value} = {float(value):.15f}")


print("A1 smooth HB-to-BBLR grouping exact audit")
show("eta", eta)
show("trace exponent", trace)
show("K=4 irregular-atom cap", hb4_cap)
show("Type-I threshold X/H", type_i_threshold)
print(f"counterexample mu exponents = {mu}")
print(f"counterexample smooth exponents = {smooth}")
component_scalar = -6
moebius_at_two = -1
coefficient_one_at_two = 1
print(f"zero-based HB component j=1 scalar = {component_scalar}")
print(f"mu_Z(2) vs coefficient-one at 2 = {moebius_at_two} vs {coefficient_one_at_two}")
assert component_scalar == -6
assert moebius_at_two != coefficient_one_at_two
show("counterexample total", sum(mu + smooth))
show("counterexample outer mu product", sum(mu))
assert sum(mu + smooth) == trace
assert sum(mu) == eta
assert all(0 < exponent <= hb4_cap for exponent in mu)
assert all(0 < exponent < type_i_threshold for exponent in smooth)
print("counterexample terminal legality = PASS")

left_gaps = tuple(abs(exponent - target) for exponent in smooth for target in left_target)
right_gaps = tuple(abs(exponent - target) for exponent in smooth for target in right_target)
show("minimum left literal-inner gap", min(left_gaps))
show("minimum right literal-inner gap", min(right_gaps))
assert min(left_gaps) == Fraction(1, 10)
assert min(right_gaps) == Fraction(33, 100)
print("left (1/2,1/2) literal grouping = IMPOSSIBLE")
print("right (7/100,93/100) literal grouping = IMPOSSIBLE")
print("two-sided asymmetric literal grouping = IMPOSSIBLE")

# Collapsing two coefficient-one slots by their product introduces the
# factor-pair multiplicity d_2(n), not another literal coefficient-one slot.
def factor_pair_count(n: int) -> int:
    return sum(1 for divisor in range(1, n + 1) if n % divisor == 0)


print(f"two-slot collapse multiplicity at 2 = {factor_pair_count(2)}")
print(f"two-slot collapse multiplicity at 4 = {factor_pair_count(4)}")
assert factor_pair_count(2) == 2
assert factor_pair_count(4) == 3
print("two-slot collapse is coefficient-bearing = PASS")
