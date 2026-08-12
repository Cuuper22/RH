#!/usr/bin/env python3
"""Exact scale audit for Phase A1.2 cross-Y recombination.

The arithmetic uses fractions only.  The finite aligned-block example is the
countermodel formalized by LogBudget.blockwise_triangle_sharp.
"""

from fractions import Fraction


def show(label: str, value: Fraction) -> None:
    print(f"{label} = {value} = {float(value):.15f}")


theta = Fraction(43, 100)
y_exp = 1 + theta
h_exp = theta
p_exp = Fraction(1, 2) + theta
q_exp = Fraction(1, 2)

print("local cycle-5 scales at theta=43/100")
show("Y exponent", y_exp)
show("H exponent", h_exp)
show("P exponent", p_exp)
show("Q exponent", q_exp)
show("P*Q exponent", p_exp + q_exp)
show("P*H exponent", p_exp + h_exp)
show("secondary power saving", y_exp - (p_exp + h_exp))
assert p_exp + q_exp == y_exp
assert y_exp - (p_exp + h_exp) == Fraction(7, 100)

print("\nlogarithmic budget at the forced minimum C=3")
c_min = Fraction(3)
budget_log_exp = Fraction(3)
literal_log_exp = c_min + 2
cross_y_log_exp = c_min + 1
show("literal Y-dyadic contribution exponent", literal_log_exp)
show("cross-Y recombined contribution exponent", cross_y_log_exp)
show("trace budget exponent", budget_log_exp)
show("cross-Y excess", cross_y_log_exp - budget_log_exp)
assert literal_log_exp == 5
assert cross_y_log_exp == 4
assert cross_y_log_exp - budget_log_exp == 1
print("cross-Y closure condition = C < 2")

print("\naligned five-block countermodel")
bounds = [Fraction(1) for _ in range(5)]
errors = bounds.copy()
print(f"individual bounds = {bounds}")
print(f"aligned weighted sum = {sum(errors)}")
print(f"sum of blockwise bounds = {sum(bounds)}")
assert sum(errors) == sum(bounds) == 5
