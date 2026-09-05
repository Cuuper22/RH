#!/usr/bin/env python3
"""Check the exact exponent arithmetic and displayed constants in §§18--20."""

from decimal import Decimal, getcontext
from fractions import Fraction


getcontext().prec = 60

eta = Fraction(49, 100)
theta = Fraction(1, 5)

# Section 18: beta_PV=(3/2)kappa+.745-rho/2 and beta_PV<1.
rho = Fraction(1, 1)
kappa_endpoint = (rho + Fraction(51, 100)) / 3
assert kappa_endpoint == Fraction(151, 300)
assert kappa_endpoint - Fraction(1, 2) == Fraction(1, 300)

# If the same epsilon is used at kappa=1/2+eps and
# kappa=151/300-eps, the interval is nonempty exactly for eps<1/600.
assert (kappa_endpoint - Fraction(1, 2)) / 2 == Fraction(1, 600)

# Section 19: fixed-power Farey separation and the positive packet constant.
assert eta + 2 * theta - 1 == Fraction(-11, 100)
u = (eta + theta) / eta
assert u == Fraction(69, 49)

d69 = Decimal(69)
d49 = Decimal(49)
j = (Decimal(69) / Decimal(100)) * (d69 / d49).ln() - Decimal(1) / Decimal(5)
dickman = Decimal(1) - (d69 / d49).ln()

assert abs(j - Decimal("0.03617748247577661267")) < Decimal("1e-20")
assert abs(dickman - Decimal("0.65771379351336722801")) < Decimal("1e-20")
assert j > 0

# Section 20: Pólya--Vinogradov closes .725+delta<1, and Burgess gives
# R^(19/8)=T^(931/800)=T^1.16375 at eta=49/100.
pv_base = 3 * eta - Fraction(149, 200)  # R^3/Q, Q=T^(149/200)
assert pv_base == Fraction(29, 40)  # .725
assert 1 - pv_base == Fraction(11, 40)  # .275

# Section 21: R^2(D/M)=T^(.235+2 delta), so the packet projection
# remains below T exactly for delta<.3825.
projected_acz_endpoint = (1 - Fraction(47, 200)) / 2
assert projected_acz_endpoint == Fraction(153, 400)

burgess_exponent = eta * Fraction(19, 8)
assert burgess_exponent == Fraction(931, 800)
assert float(burgess_exponent) == 1.16375

print(f"high-K endpoint = {float(kappa_endpoint):.15f}")
print(f"J_0.49(0.20) = {j}")
print(f"Dickman complement = {dickman}")
print(f"PV divisor endpoint = {float(1 - pv_base):.15f}")
print(f"Poisson-ACZ projected endpoint = {float(projected_acz_endpoint):.15f}")
print(f"Burgess projected exponent = {float(burgess_exponent):.15f}")
