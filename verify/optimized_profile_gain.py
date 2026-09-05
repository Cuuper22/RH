"""Exact certificate for the optimized ordered-cubic profile.

This checks the profile integrals and final scalar implication.  It does not
formalize the zero-moment theorem or the finite operator inequality.
"""

from fractions import Fraction as F
from math import factorial, isqrt, prod

import sympy as sp


x, v, w = sp.symbols("x v w")
coeff = [
    1091974251780,
    -1092598710370,
    183563572147,
    -13799851355,
    11008450474,
    -46499927506,
    75463768564,
]
p = sum(sp.Rational(c, 10**12) * x ** (2 * j)
        for j, c in enumerate(coeff))

# On x^2 <= 1/4, discard positive nonconstant terms and maximize the
# magnitude of every negative term.  This deliberately crude rational
# lower bound certifies positivity on the whole support.
assert all(coeff[j] > 0 for j in (0, 2, 4, 6))
assert all(coeff[j] < 0 for j in (1, 3, 5))
positive_lower = sp.Rational(coeff[0], 10**12) + sum(
    sp.Rational(coeff[j], 10**12) * sp.Rational(1, 4) ** j
    for j in (1, 3, 5)
)
assert positive_lower > 0

mass = sp.integrate(p, (x, -sp.Rational(1, 2), sp.Rational(1, 2)))
u = sp.cancel(p / mass)


def simplex_integral(poly, variables):
    """Integrate a polynomial over nonnegative coordinates of sum <= 1."""
    terms = sp.Poly(sp.expand(poly), *variables).terms()
    return sum(
        coefficient
        * sp.Rational(
            prod(factorial(k) for k in powers),
            factorial(sum(powers) + len(variables)),
        )
        for powers, coefficient in terms
    )


lo = u.subs({x: x - sp.Rational(1, 2)})
up = u.subs({x: x + v - sp.Rational(1, 2)})
i2 = sp.integrate(u**2, (x, -sp.Rational(1, 2), sp.Rational(1, 2)))
d_cost = sp.cancel(i2 + 2 * simplex_integral(v * lo * up, (x, v)))

i3 = sp.integrate(u**3, (x, -sp.Rational(1, 2), sp.Rational(1, 2)))
m3 = sp.cancel(
    i3 + 3 * simplex_integral(v * (lo**2 * up + lo * up**2), (x, v))
)
kappa = sp.cancel(3 * d_cost - 2 - m3)

q0 = sp.integrate(u**4, (x, -sp.Rational(1, 2), sp.Rational(1, 2))) / 6
q1 = simplex_integral(v * lo * up * (lo + up) ** 2, (x, v)) / 3
base = lo
first = u.subs({x: x + v - sp.Rational(1, 2)})
second = u.subs({x: x + w - sp.Rational(1, 2)})
last = u.subs({x: x + v + w - sp.Rational(1, 2)})
q2 = simplex_integral(
    v * w * (last * second**2 * base + last * second * first * base),
    (x, v, w),
)
q_energy = sp.cancel(q0 + q1 + q2)


def ceil_sqrt_rat(q, decimals):
    """Return a decimal rational strictly above sqrt(q), using integers."""
    q = F(q)
    scale = 10**decimals
    n = (q.numerator * scale * scale + q.denominator - 1) // q.denominator
    a = isqrt(n)
    while a * a < n:
        a += 1
    while (a - 1) * (a - 1) >= n:
        a -= 1
    return F(a, scale)


d_cost = F(d_cost)
m3 = F(m3)
kappa = F(kappa)
q_energy = F(q_energy)
sqrt_q = ceil_sqrt_rat(q_energy, 12)
sqrt_d = ceil_sqrt_rat(d_cost - F(2, 3), 12)
assert sqrt_q * sqrt_q > q_energy
assert sqrt_d * sqrt_d > d_cost - F(2, 3)

gain = F(1, 271803)
assert kappa > 6 * gain
margin = (kappa - 6 * gain) ** 2 - 18 * gain * (sqrt_q + sqrt_d) ** 2
assert margin > 0
result = 2 - d_cost + gain
assert result > F(336252191, 500000000)  # 0.672504382

print("Exact optimized-profile scalar checks passed")
print("D:", float(d_cost))
print("M3:", float(m3))
print("kappa:", float(kappa))
print("Q:", float(q_energy))
print("Certified gain:", gain, float(gain))
print("Squared scalar margin:", float(margin))
print("Certified proportion:", float(result), "> 0.672504382")
