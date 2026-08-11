#!/usr/bin/env python3
"""Exact Fraction audit of the direct kill and unresolved Pascadi candidate."""

from fractions import Fraction


trace = Fraction(143, 100)
outer = Fraction(43, 100)
inner_short = Fraction(2, 5)
inner_long = Fraction(3, 5)
shift = Fraction(43, 100)
frequency = Fraction(23, 100)
physical_x = -Fraction(23, 100)
numerator = frequency + shift
one_outer_coefficient_l2 = outer / 2
numerator_coefficient_l2 = numerator / 2
coefficient_l2 = numerator_coefficient_l2 + 2 * one_outer_coefficient_l2


def show(name: str, value: Fraction) -> None:
    print(f"{name} = {value} = {float(value):.15f}")


print("A1 pre-majorant one-shot DI exact exponent audit")
show("trace exponent", trace)
show("outer exponents R=S", outer)
show("short smooth exponents C=D", inner_short)
show("long smooth exponents", inner_long)
show("shift exponent H", shift)
show("frequency exponent L", frequency)
show("collapsed numerator exponent N=LH", numerator)
show("physical x exponent", physical_x)
show("one outer mu-pair L2 power exponent", one_outer_coefficient_l2)
show("ell*h numerator L2 power exponent", numerator_coefficient_l2)
show("collapsed coefficient L2 power exponent", coefficient_l2)
assert numerator == Fraction(33, 50)
assert one_outer_coefficient_l2 == Fraction(43, 200)
assert numerator_coefficient_l2 == Fraction(33, 100)
assert coefficient_l2 == Fraction(19, 25)
print("source scale and collapsed L2 power = PASS")

# Drappeau 2017, Theorem 2.1, with q0=1.
C = inner_short
D = inner_short
N = numerator
R = outer
S = outer
drappeau_k2_1 = C + S + max(R + S, N) + max(C, R + D)
drappeau_k2_2 = 2 * C + D + S + (max(R + S, N) + R) / 2
drappeau_k2_3 = 2 * D + N + R - S
drappeau_k = max(drappeau_k2_1, drappeau_k2_2, drappeau_k2_3) / 2
drappeau_fixed_x = drappeau_k + coefficient_l2
drappeau_integrated = drappeau_fixed_x + physical_x

show("Drappeau K^2 term 1 exponent", drappeau_k2_1)
show("Drappeau K^2 term 2 exponent", drappeau_k2_2)
show("Drappeau K^2 term 3 exponent", drappeau_k2_3)
show("Drappeau K exponent", drappeau_k)
show("Drappeau fixed-x exponent", drappeau_fixed_x)
show("Drappeau integrated exponent", drappeau_integrated)
show("Drappeau excess over trace", drappeau_integrated - trace)
assert drappeau_k2_1 == Fraction(63, 25)
assert drappeau_k2_2 == Fraction(91, 40)
assert drappeau_k2_3 == Fraction(73, 50)
assert drappeau_k == Fraction(63, 50)
assert drappeau_fixed_x == Fraction(101, 50)
assert drappeau_integrated == Fraction(179, 100)
assert drappeau_integrated - trace == Fraction(9, 25)
print("Drappeau direct one-shot route = POWER-INCOMPATIBLE")

# Pascadi 2025, Theorem 10.3: arithmetic substitution only.  Literal Poisson
# completion has not been put in the theorem's required Kloosterman form.
pC = inner_short
pM = S + C - D
pN = numerator
pR = outer
pS = outer
completion_prefactor = D - pS - pC
cs_sqrt_r = pC + pS + pR / 2
sqrt_mn = (pM + pN) / 2
c_sqrt_sm = pC + (pS + pM) / 2
c_sqrt_sn = pC + (pS + pN) / 2
theta_denominator = max(pM, pR + pS) + max(pN, pR + pS) / 2
theta_ratio = cs_sqrt_r - theta_denominator
theta_max = Fraction(7, 32)
theta_power = theta_max * max(Fraction(0), theta_ratio)
rational_factor = (
    max(cs_sqrt_r, sqrt_mn, c_sqrt_sm)
    + max(cs_sqrt_r, sqrt_mn, c_sqrt_sn)
    - max(cs_sqrt_r, sqrt_mn)
)
sqrt_mrs = (pM + pR + pS) / 2
pascadi_complete = theta_power + sqrt_mrs + coefficient_l2 + rational_factor
pascadi_fixed_x = completion_prefactor + pascadi_complete
pascadi_integrated = pascadi_fixed_x + physical_x
lower_dual_fixed_x_intercept = (
    completion_prefactor + (pR + pS) / 2
    + coefficient_l2 + rational_factor
)

show("Pascadi candidate completed M exponent", pM)
show("completion prefactor exponent", completion_prefactor)
show("Pascadi candidate CS*sqrt(R) exponent", cs_sqrt_r)
show("Pascadi candidate sqrt(MN) exponent", sqrt_mn)
show("Pascadi candidate C*sqrt(SM) exponent", c_sqrt_sm)
show("Pascadi candidate C*sqrt(SN) exponent", c_sqrt_sn)
show("Pascadi candidate theta denominator exponent", theta_denominator)
show("Pascadi candidate theta ratio exponent", theta_ratio)
show("Pascadi candidate theta power contribution", theta_power)
show("Pascadi candidate rational-factor exponent", rational_factor)
show("Pascadi candidate sqrt(MRS) exponent", sqrt_mrs)
show("Pascadi candidate complete-sum exponent", pascadi_complete)
show("Pascadi candidate fixed-x exponent", pascadi_fixed_x)
show("Pascadi candidate integrated exponent", pascadi_integrated)
show("Pascadi candidate excess over trace", pascadi_integrated - trace)
show("Pascadi candidate lower-dual fixed-x intercept", lower_dual_fixed_x_intercept)
assert pM == Fraction(43, 100)
assert completion_prefactor == -Fraction(43, 100)
assert cs_sqrt_r == Fraction(209, 200)
assert sqrt_mn == Fraction(109, 200)
assert c_sqrt_sm == Fraction(83, 100)
assert c_sqrt_sn == Fraction(189, 200)
assert theta_denominator == Fraction(129, 100)
assert theta_ratio == -Fraction(49, 200)
assert theta_power == 0
assert rational_factor == Fraction(209, 200)
assert sqrt_mrs == Fraction(129, 200)
assert pascadi_complete == Fraction(49, 20)
assert pascadi_fixed_x == Fraction(101, 50)
assert pascadi_integrated == Fraction(179, 100)
assert pascadi_integrated - trace == Fraction(9, 25)
assert lower_dual_fixed_x_intercept == Fraction(361, 200)
print("literal completion phase = S(k, signed-n*a^{-1}; q)")
print("equivalent completion phase = S(k*a^{-1}, signed-n; q)")
print("Pascadi required phase = S(m*a, signed-n; q)")
zmod_q = 5
zmod_a = 2
zmod_a_inv = pow(zmod_a, -1, zmod_q)
print(f"ZMod 5 regression: a=2, a^(-1)={zmod_a_inv}, a^(-1)!=a")
assert zmod_a_inv == 3
assert zmod_a_inv != zmod_a
print("support-preserving k-to-m reindex = NOT PROVED")
print("k=0 Ramanujan term outside m~M theorem sum = NOT TREATED")
print("Pascadi completed one-shot candidate = UNRESOLVED-APPLICABILITY")

normalized_log_exponent = Fraction(3, 2)
unnormalized_log_exponent = normalized_log_exponent + 2
show("one multiplicative-energy L2 log exponent", Fraction(1, 2))
show("normalized coefficient log exponent", normalized_log_exponent)
show("unnormalized coefficient log exponent", unnormalized_log_exponent)
assert normalized_log_exponent == Fraction(3, 2)
assert unnormalized_log_exponent == Fraction(7, 2)
print("theorem loss = an additional explicit positive T^epsilon power")
print("direct Drappeau finish/kill exponent = 179/100 with excess 9/25")
print("Pascadi 179/100 arithmetic is excluded from the finish/kill claim")
print("survivor = four Moebius slots, cross-HB cancellation, or exact completion reindex")
