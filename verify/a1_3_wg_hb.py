#!/usr/bin/env python3
"""Exact exponent audit for the A1.3 Weil-grade HB route."""

from fractions import Fraction


def show(label: str, value: Fraction) -> None:
    print(f"{label} = {value} = {float(value):.15f}")


eta = Fraction(43, 100)
c_exp = Fraction(1, 2)
h_exp = eta
q_exp = c_exp
p_exp = h_exp + q_exp
y_exp = h_exp + 2 * q_exp

print("endpoint scales")
show("H exponent", h_exp)
show("Q=c exponent", q_exp)
show("P=H*Q exponent", p_exp)
show("Y=H*Q^2 exponent", y_exp)
assert y_exp == Fraction(143, 100)

print("\nsufficient simultaneous-cancellation benchmark")
csqd_1 = Fraction(1, 2) + 2 * eta
csqd_2 = Fraction(3, 4) + Fraction(3, 2) * eta
show("CSQD first exponent", csqd_1)
show("CSQD second exponent", csqd_2)
show("minimum power saving", y_exp - max(csqd_1, csqd_2))
show("saving after epsilon=7/400", y_exp - csqd_2 - Fraction(7, 400))
assert csqd_1 == Fraction(34, 25)
assert csqd_2 == Fraction(279, 200)
assert y_exp - csqd_2 == Fraction(7, 200)
assert y_exp - csqd_2 - Fraction(7, 400) == Fraction(7, 400)

print("\none-shot method-class losses")
fixed_weil = 2 * eta + Fraction(3, 4)
bc_norms = p_exp
bc_amn = h_exp + p_exp + q_exp
bc_1 = bc_norms + Fraction(7, 20) * bc_amn + Fraction(1, 4) * max(p_exp, q_exp)
bc_2 = bc_norms + Fraction(3, 8) * bc_amn + Fraction(1, 8) * max(
    h_exp + q_exp, h_exp + p_exp
)
bblr_1 = Fraction(1, 2) + 3 * eta
bblr_2 = fixed_weil
for name, exponent in (
    ("fixed-modulus Weil", fixed_weil),
    ("Bettin-Chandee term 1", bc_1),
    ("Bettin-Chandee term 2", bc_2),
    ("BBLR term 1", bblr_1),
    ("BBLR term 2", bblr_2),
):
    show(f"{name} exponent", exponent)
    show(f"{name} deficit", exponent - y_exp)
    assert exponent > y_exp
assert fixed_weil - y_exp == Fraction(9, 50)
assert bc_1 - y_exp == Fraction(767, 2000)
assert bc_2 - y_exp == Fraction(147, 400)

print("\nnew bilinear Kloosterman range checks, with H=c^(43/50)")
h_in_c = h_exp / c_exp
bp_low = Fraction(13, 28)
bp_high = Fraction(7, 12)
show("H exponent in c", h_in_c)
show("Blomer-Pascadi upper endpoint", bp_high)
show("amount above BP range", h_in_c - bp_high)
assert h_in_c == Fraction(43, 50)
assert h_in_c - bp_high == Fraction(83, 300)

mqw_cond_1 = Fraction(12, 5) * h_in_c
mqw_cond_2 = 2 * h_in_c
show("MQW M^(7/5)N exponent in c", mqw_cond_1)
show("MQW condition-1 excess", mqw_cond_1 - Fraction(3, 2))
show("MQW MN exponent in c", mqw_cond_2)
show("MQW condition-2 excess", mqw_cond_2 - Fraction(5, 4))
assert mqw_cond_1 == Fraction(258, 125)
assert mqw_cond_1 - Fraction(3, 2) == Fraction(141, 250)
assert mqw_cond_2 == Fraction(43, 25)
assert mqw_cond_2 - Fraction(5, 4) == Fraction(47, 100)
