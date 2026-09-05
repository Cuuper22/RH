"""Exact rational certificate for the sharpened ordered cubic gain.

This checks scalar Taylor bounds and polynomial integrations. It does not
formalize the analytic zero-moment theorem or the operator inequalities.
"""
from fractions import Fraction as F
from math import factorial, prod
import sympy as sp

Slo = sum((-1)**j * F(1, 2)**j / factorial(2*j + 1)
          for j in range(16))
Clo = sum((-1)**j * F(1, 2)**j / factorial(2*j)
          for j in range(16))
Shi = Slo + F(1, 2)**16 / factorial(33)
Chi = Clo + F(1, 2)**16 / factorial(32)
Dlo = F(1, 2) + Clo / Shi
Dhi = F(1, 2) + Chi / Slo
u2hi = (1 + Shi*Chi) / (2*Slo**2)
M3hi = 3*Dhi*u2hi - 2/Shi**2 + F(1, 3)
defect_hi = M3hi - 3*Dlo + 2
assert Dhi < F(531, 400)
assert defect_hi < -F(471, 40000)

# sin(t)/t >= 1-1/12+1/480-1/40320 at t=1/sqrt(2).
# cos(sqrt(2)x) <= 1-x^2+x^4/6 for |x|<=1/2.
envelope_scale = sp.Rational(40320, 37043)
x, v, w = sp.symbols("x v w")
p = lambda q: 1-q**2+q**4/sp.Integer(6)

def simplex_integral(poly, variables):
    terms = sp.Poly(sp.expand(poly), *variables).terms()
    return sum(coefficient * sp.Rational(
        prod(factorial(k) for k in powers),
        factorial(sum(powers)+len(variables)))
        for powers, coefficient in terms)

base = p(x-sp.Rational(1, 2))
first = p(x+v-sp.Rational(1, 2))
second = p(x+w-sp.Rational(1, 2))
last = p(x+v+w-sp.Rational(1, 2))
zero = sp.integrate(p(x)**4, (x, -sp.Rational(1,2), sp.Rational(1,2)))/6
one = simplex_integral(v*base*first*(base+first)**2, (x,v))/3
two = simplex_integral(v*w*(last*second**2*base
                           +last*second*first*base), (x,v,w))
q_upper = F(envelope_scale**4 * (zero+one+two))
assert q_upper == F(3154631940664954715840,7906248876401653709399)

sqrt_q_bound = F(63167,100000)
sqrt_h_bound = F(81292,100000)
assert sqrt_q_bound**2 > q_upper
assert sqrt_h_bound**2 > F(531,400)-F(2,3)
sum_bound = sqrt_q_bound+sqrt_h_bound
assert sum_bound == F(144459,100000)
kappa = F(471,40000)
gain = F(1,272000)
assert kappa > 6*gain
margin = (kappa-6*gain)**2 - 18*gain*sum_bound**2
assert margin == F(737589807,23120000000000000)
assert margin > 0
assert 2-Dhi+gain > F(33625219,50000000)

print("Exact sharpened cubic scalar checks passed")
print("Ordered fourth upper bound:",q_upper)
print("Cubic defect upper bound:",float(defect_hi))
print("Certified gain:",gain)
print("Gain ratio over previous certificate:",gain*35280000)
print("Result exceeds:",F(33625219,50000000))
