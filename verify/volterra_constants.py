"""Exact scalar checks for the ordered-moment research derivation.

These checks do not verify the analytic complex-zero moment transfer.
Only Python rational arithmetic is used; printed decimals are illustrative.
"""
from fractions import Fraction as Q
from math import factorial

# At t=1/sqrt(2), sin(t)/t and cos(t) have rational alternating series.
# The odd final index gives lower endpoints; the next term bounds the error.
Slo = sum((-1)**j * Q(1, 2)**j / factorial(2*j + 1)
          for j in range(16))
Clo = sum((-1)**j * Q(1, 2)**j / factorial(2*j)
          for j in range(16))
Shi = Slo + Q(1, 2)**16 / factorial(33)
Chi = Clo + Q(1, 2)**16 / factorial(32)
assert 0 < Slo < Shi < 1
assert 0 < Clo < Chi < 1

# u=cos(sqrt(2)x)/S on [-1/2,1/2].
# D=1/2+C/S; integral u^2=(1+SC)/(2S^2);
# integral u^3=1/S^2-1/6; M3=3D integral u^2-2 integral u^3.
Dlo = Q(1, 2) + Clo / Shi
Dhi = Q(1, 2) + Chi / Slo
Bhi = (1 + Shi*Chi) / (2*Slo**2)
M3hi = 3*Dhi*Bhi - 2/Shi**2 + Q(1, 3)
defect_hi = M3hi - 3*Dlo + 2
assert Dhi < Q(4, 3)
assert 1/Slo < Q(6, 5)
assert defect_hi < -Q(1, 100)

# Positive ordered domains, with profile height <=6/5 and width <=1.
ordered_bound = Q(6, 5)**4 * (Q(1, 6) + Q(2, 9) + Q(1, 60))
assert ordered_bound == Q(2628, 3125)
assert ordered_bound < 1

# Bound 3sqrt(2Q)+12(sqrt(D)+sqrt(3))+2 by 42.
assert Q(3, 2)**2 > 2
assert Q(7, 6)**2 > Q(4, 3)
assert Q(7, 4)**2 > 3
assert 3*Q(3, 2) + 12*(Q(7, 6)+Q(7, 4)) + 2 < 42
gain = Q(1, 100)**2 / (2*42**2)
assert gain == Q(1, 35280000)
assert 2-Dhi+gain > Q(672500732, 10**9)

print('Exact scalar checks passed')
print('Cubic defect upper bound:', float(defect_hi))
print('Ordered moment upper bound:', ordered_bound)
print('Scalar gain, if analytic inputs hold:', gain)
print('Resulting rational threshold:', Q(672500732, 10**9))
