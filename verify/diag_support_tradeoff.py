"""Exact rational checks for the one-sided D_diag support tradeoff."""

from fractions import Fraction as F
from math import factorial, prod

import sympy as sp


x, v = sp.symbols("x v")
s = sp.Rational(147343, 100000)
p = sum(
    (-1) ** j * sp.Rational(2**j, factorial(2 * j)) * x ** (2 * j)
    for j in range(7)
)

# Positivity on |x|<=s/2: discard positive nonconstant terms and maximize
# the magnitude of every negative monomial at the endpoint.
endpoint = s / 2
lower = 1 - sum(
    sp.Rational(2**j, factorial(2 * j)) * endpoint ** (2 * j)
    for j in (1, 3, 5)
)
assert lower > 0
mass = sp.integrate(p, (x, -s / 2, s / 2))
u = sp.cancel(p / mass)


def simplex_integral(poly, variables):
    terms = sp.Poly(sp.expand(poly), *variables).terms()
    return sum(
        coefficient
        * sp.Rational(
            prod(factorial(k) for k in powers),
            factorial(sum(powers) + len(variables)),
        )
        for powers, coefficient in terms
    )


lo = u.subs({x: -s / 2 + s * x})
up = u.subs({x: -s / 2 + s * (x + v)})
d_cost = sp.cancel(
    sp.integrate(u**2, (x, -s / 2, s / 2))
    + 2 * s**3 * simplex_integral(v * lo * up, (x, v))
)
assert d_cost < sp.Rational(23, 20)
margin = sp.Rational(23, 20) - d_cost


def cs_bounds(q, terms=12):
    """Alternating bounds for cos(q/sqrt2) and sinc(q/sqrt2)."""
    q = F(q)
    z = q * q / F(2)
    cos_hi = sum((-1) ** j * z**j / F(factorial(2 * j))
                 for j in range(terms + 1))
    cos_lo = sum((-1) ** j * z**j / F(factorial(2 * j))
                 for j in range(terms))
    sinc_hi = sum((-1) ** j * z**j / F(factorial(2 * j + 1))
                  for j in range(terms + 1))
    sinc_lo = sum((-1) ** j * z**j / F(factorial(2 * j + 1))
                  for j in range(terms))
    return cos_lo, cos_hi, sinc_lo, sinc_hi


def d_lower(q):
    cos_lo, _, _, sinc_hi = cs_bounds(q)
    return q / F(2) + cos_lo / (q * sinc_hi)


def d_upper(q):
    _, cos_hi, sinc_lo, _ = cs_bounds(q)
    return q / F(2) + cos_hi / (q * sinc_lo)


s_lo = F(147342692508524, 10**14)
s_hi = F(147342692508525, 10**14)
assert d_lower(s_lo) > F(23, 20)
assert d_upper(s_hi) < F(23, 20)

# theta=2eta/(1+eta)<=5/8 implies eta<=5/11 and s<=16/11.
s_625 = F(16, 11)
assert d_lower(s_625) > F(23, 20)

eta = F(s) - 1
theta = 2 * eta / (1 + eta)
assert eta == F(47343, 100000)
assert theta == F(94686, 147343)
assert theta > F(5, 8)

print("Exact support-tradeoff checks passed")
print("eta:", eta, float(eta))
print("D_diag:", float(d_cost))
print("margin 23/20-D:", float(margin))
print("eta infimum bracket:", s_lo - 1, s_hi - 1)
print("balanced exponent:", theta, float(theta))
print("D_min(16/11) lower bound:", float(d_lower(s_625)))
