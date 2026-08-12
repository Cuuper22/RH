#!/usr/bin/env python3
"""Exact Fraction audit of the retained four-Moebius-slot route."""

from fractions import Fraction


def show(name: str, value: Fraction) -> None:
    print(f"{name} = {value} = {float(value):.15f}")


mu = Fraction(43, 200)
smooth = Fraction(2, 5)
frequency = Fraction(23, 100)
shift = Fraction(43, 100)
numerator = Fraction(33, 50)
side = 2 * mu + smooth
physical_x = -Fraction(23, 100)
fixed_x_target = Fraction(83, 50)
integrated_target = Fraction(143, 100)
volume = 4 * mu + 2 * smooth + numerator

print("A1 retained four-Moebius-slot exact exponent audit")
show("each Moebius slot U", mu)
show("each smooth slot M", smooth)
show("frequency L", frequency)
show("shift H", shift)
show("collapsed numerator r=|ell|h", numerator)
show("each product side u1*u2*m or v1*v2*n", side)
show("seven-variable tuple volume", volume)
show("physical x exponent", physical_x)
show("fixed-x target", fixed_x_target)
show("integrated target", integrated_target)
assert frequency + shift == numerator
assert side == Fraction(83, 100)
assert volume == Fraction(58, 25)
assert fixed_x_target + physical_x == integrated_target
print("seven literal scales and target normalization = PASS")

mu_relative_q = mu / side
show("one Moebius slot relative to q", mu_relative_q)
show("prime-modulus square-root threshold", Fraction(1, 2))
show("one-slot threshold deficit", Fraction(1, 2) - mu_relative_q)
assert mu_relative_q == Fraction(43, 166)
assert Fraction(1, 2) - mu_relative_q == Fraction(20, 83)
print("single-slot arbitrary-modulus multiplicative range = FAILS")

# Prescribed architecture: freeze q-side and numerator; grant square-root
# size for the entire p-side; sum the frozen variables by triangle.
one_sided = side / 2 + side + numerator
one_sided_integrated = one_sided + physical_x
one_sided_fixed_excess = one_sided - fixed_x_target
one_sided_integrated_excess = one_sided_integrated - integrated_target
show("one-sided ideal square-root fixed-x output", one_sided)
show("one-sided ideal square-root integrated output", one_sided_integrated)
show("one-sided fixed-x excess", one_sided_fixed_excess)
show("one-sided integrated excess", one_sided_integrated_excess)
assert one_sided == Fraction(381, 200)
assert one_sided_integrated == Fraction(67, 40)
assert one_sided_fixed_excess == Fraction(49, 200)
assert one_sided_integrated_excess == Fraction(49, 200)
print("prescribed one-sided fixed-modulus/triangle class = POWER-INCOMPATIBLE")
print("this is an upper-bound-chain output, not a lower bound for the source sum")

# Candidate only: square-root size in both product-side volumes, with the
# numerator counted trivially.
simultaneous = side / 2 + side / 2 + numerator
simultaneous_margin = fixed_x_target - simultaneous
simultaneous_integrated = simultaneous + physical_x
simultaneous_integrated_margin = integrated_target - simultaneous_integrated
extra_gain = one_sided - simultaneous
show("simultaneous both-side candidate fixed-x exponent", simultaneous)
show("simultaneous candidate margin", simultaneous_margin)
show("simultaneous both-side candidate integrated exponent", simultaneous_integrated)
show("simultaneous integrated margin", simultaneous_integrated_margin)
show("gain over one-sided chain", extra_gain)
show("gain needed to repair one-sided chain", one_sided_fixed_excess)
show("surplus after repair", extra_gain - one_sided_fixed_excess)
assert simultaneous == Fraction(149, 100)
assert simultaneous_margin == Fraction(17, 100)
assert simultaneous_integrated == Fraction(63, 50)
assert simultaneous_integrated_margin == Fraction(17, 100)
assert extra_gain == Fraction(83, 200)
assert extra_gain - one_sided_fixed_excess == Fraction(17, 100)
print("simultaneous exponent is a CANDIDATE, not a proved analytic estimate")

# One concrete strict allocation: half of the intrinsic margin goes to the
# analytic epsilon and half to dominating the two explicit long logarithms.
analytic_epsilon = Fraction(17, 400)
two_log_power = Fraction(17, 400)
allocated_raw = simultaneous + analytic_epsilon + two_log_power
allocated_integrated = allocated_raw + physical_x
allocated_fixed_margin = fixed_x_target - allocated_raw
allocated_integrated_margin = integrated_target - allocated_integrated
show("concrete analytic epsilon allocation", analytic_epsilon)
show("concrete two-log power allocation", two_log_power)
show("allocated raw fixed-x exponent", allocated_raw)
show("allocated raw integrated exponent", allocated_integrated)
show("allocated fixed-x margin", allocated_fixed_margin)
show("allocated integrated margin", allocated_integrated_margin)
assert allocated_raw == Fraction(63, 40)
assert allocated_integrated == Fraction(269, 200)
assert allocated_fixed_margin == Fraction(17, 200)
assert allocated_integrated_margin == Fraction(17, 200)
print("concrete epsilon/log allocation remains STRICTLY BELOW both targets")

normalized_long_log_exponent = Fraction(0)
raw_long_log_exponent = Fraction(2)
show("normalized long-log exponent", normalized_long_log_exponent)
show("raw two-long-slot log exponent", raw_long_log_exponent)
assert raw_long_log_exponent - normalized_long_log_exponent == 2
print("single dyadic numerator L1 count adds log exponent 0")
print("a proved T^(149/100+epsilon)*(log T)^2 bound with epsilon<17/100")
print("would imply the fixed-x target with C=0; no such bound is asserted")
print("published direct theorem found retaining all four Moebius slots = NO")
