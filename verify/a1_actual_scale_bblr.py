#!/usr/bin/env python3
"""Exact Fraction audit of the actual-scale BBLR block."""

from fractions import Fraction


eta = Fraction(43, 100)
trace = 1 + eta
outer = eta
inner_short = Fraction(2, 5)
inner_long = Fraction(3, 5)
shift = eta

product = 2 * outer + 2 * (inner_short + inner_long)
outside = (product + 2 * shift) / 4
ab_error = outside + 2 * outer
watt_parenthesis = shift / 4 + outer / 2 + product / 8
watt_error = outside + watt_parenthesis

fourier_physical = inner_long - outer - inner_short
frequency_cutoff = (
    outer + inner_short + inner_long - inner_long - inner_long
)
p = outer + inner_short
q = outer + inner_short
pq = p + q
ph = p + shift
progression_majorant = max(pq, ph)
taylor_h_sq = 2 * shift


def show(name: str, value: Fraction) -> None:
    print(f"{name} = {value} = {float(value):.15f}")


print("A1 actual-scale BBLR exact exponent audit")
show("eta", eta)
show("trace exponent", trace)
show("outer exponent A=B", outer)
show("inner short exponent M1=N1", inner_short)
show("inner long exponent M2=N2", inner_long)
show("shift exponent H", shift)
show("one-side product exponent", outer + inner_short + inner_long)
show("ABMN exponent", product)
assert outer + inner_short + inner_long == trace
assert inner_short <= inner_long
assert shift == (outer + outer) / 2
print("block geometry and BBLR range boundary = PASS")

show("BBLR outside exponent", outside)
show("BBLR AB-error exponent", ab_error)
show("BBLR Watt-parenthesis exponent", watt_parenthesis)
show("BBLR Watt-error exponent", watt_error)
show("BBLR AB-error excess", ab_error - trace)
show("BBLR Watt-error excess", watt_error - trace)
assert outside == Fraction(93, 100)
assert ab_error == Fraction(179, 100)
assert watt_parenthesis == Fraction(17, 25)
assert watt_error == Fraction(161, 100)
assert ab_error - trace == Fraction(9, 25)
assert watt_error - trace == Fraction(9, 50)
print("BBLR Proposition 3.1 black-box class = POWER-INCOMPATIBLE")

show("source Fourier physical exponent", fourier_physical)
show("source nonzero-frequency cutoff exponent", frequency_cutoff)
show("source summed-Fourier net exponent", fourier_physical + frequency_cutoff)
assert fourier_physical == -Fraction(23, 100)
assert frequency_cutoff == Fraction(23, 100)
assert fourier_physical + frequency_cutoff == 0
print("Fourier-size/frequency-count cancellation = PASS")
show("source d=1 P exponent", p)
show("source d=1 Q exponent", q)
show("source d=1 PQ exponent", pq)
show("source d=1 PH exponent", ph)
show("source P(Q+H) exponent", progression_majorant)
show("source PQ excess", pq - trace)
show("source PH saving", trace - ph)
show("Taylor H^2 saving", trace - taylor_h_sq)
assert p == q == Fraction(83, 100)
assert pq == Fraction(83, 50)
assert ph == Fraction(63, 50)
assert progression_majorant == pq
assert pq - trace == Fraction(23, 100)
assert trace - ph == Fraction(17, 100)
assert trace - taylor_h_sq == Fraction(57, 100)
print("source d=1 P(Q+H) progression-majorant class = POWER-INCOMPATIBLE")
print("survivor = cancellation before the residue/progression majorant")
