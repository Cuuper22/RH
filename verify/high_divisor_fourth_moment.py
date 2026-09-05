#!/usr/bin/env python3
"""Exact exponent checks for mobius_energy_20260905.md, Section 30."""

from fractions import Fraction


eta = Fraction(47343, 100000)

# Section 24 at D=R.
old_exponent = (7 * eta - 1) / 2
old_excess = old_exponent - 1

# Section 30: R^2 (C/R)^(1/2), C=T^((1+eta)/2).
new_exponent = 2 * eta + (1 - eta) / 4
new_excess = new_exponent - 1
crossover = (3 + eta) / 8

assert old_exponent == Fraction(231401, 200000)       # 1.157005
assert old_excess == Fraction(31401, 200000)          # 0.157005
assert new_exponent == Fraction(431401, 400000)       # 1.0785025
assert new_excess == Fraction(31401, 400000)          # 0.0785025
assert old_excess == 2 * new_excess
assert old_exponent - new_exponent == new_excess
assert crossover == Fraction(347343, 800000)         # 0.43417875

# Endpoint determinant geometry in the literature audit.
x = eta
y = (3 * eta - 1) / 2
bc_first = Fraction(39, 20) * x + Fraction(17, 20) * y
bc_second = Fraction(15, 8) * x + y
absolute_count = 2 * x + 2 * y - eta

assert y == Fraction(42029, 200000)                   # 0.210145
assert bc_first == Fraction(4407247, 4000000)         # 1.10181175
assert bc_second == Fraction(4391305, 4000000)        # 1.09782625
assert absolute_count == Fraction(22343, 25000)       # 0.89372
assert bc_first > absolute_count
assert bc_second > absolute_count

# Section 31 moment ladder.
s4_exponent = 2 * eta + (1 - eta) / 8
s5_exponent = 2 * eta + (1 - eta) / 10
s5_margin = 1 - s5_exponent
assert s4_exponent == Fraction(4050725, 4000000)     # 1.01268125
assert s5_exponent == Fraction(999517, 1000000)      # 0.999517
assert s5_margin == Fraction(483, 1000000)           # 0.000483

print("eta =", float(eta))
print("old packet exponent =", float(old_exponent))
print("new packet exponent =", float(new_exponent))
print("remaining excess =", float(new_excess))
print("old/new crossover =", float(crossover))
print("BC errors =", float(bc_first), float(bc_second))
print("absolute determinant exponent =", float(absolute_count))
print("s=4 ladder exponent =", float(s4_exponent))
print("s=5 ladder exponent =", float(s5_exponent))
print("s=5 margin below one =", float(s5_margin))
