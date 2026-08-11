#!/usr/bin/env python3
"""Exact audit for the quartic finite-to-asymptotic transfer.

Only ``fractions.Fraction`` arithmetic is used.  The audit checks

* the exact coefficient ``3`` of the enlarged-window edge count;
* the fixed-point quotient identity for the R-8686 and R-9506 terminals;
* the strict frozen-target margins used by the transfer; and
* the two weakening inequalities used for R-8657 and R-9383.
"""

from fractions import Fraction as Q


def qstr(value: Q) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def fixed_point(mu: Q, AP: Q, cap: Q, cost: Q) -> Q:
    return (mu * AP - cap * (cost - 1) / 2) / (1 - cap / 2)


def transfer_quotient(mu: Q, AP: Q, cap: Q, cost: Q) -> Q:
    return (mu * AP + 2 - cost - cap / 2) / (1 - cap / 2)


# Affine expressions in ``cap`` are represented by exact pairs
# ``(constant, cap_coefficient)``.  Robust stability contributes ``2``;
# replacing s1 by N0s+edge contributes ``1-cap/2``; and the trim-count
# comparison contributes ``cap/2``.  The cap coefficient cancels exactly.
robust_edge = (Q(2), Q(0))
s1_edge = (Q(1), Q(-1, 2))
trim_edge = (Q(0), Q(1, 2))
edge_affine = tuple(sum(parts, Q(0)) for parts in zip(robust_edge, s1_edge, trim_edge))
assert edge_affine == (Q(3), Q(0))


cases = (
    (
        "R-8686",
        Q(4999, 10000),
        Q(29882276809014040891941502329751, 1560455496913214458368000000000000),
        Q(204953852069001839, 2018328905500000000),
        Q(113434643, 100000000),
        Q(86855250, 100000000),
    ),
    (
        "R-9506",
        Q(4999, 10000),
        Q(2656428028876877176306155297737641, 48586574957743442014570566600000000),
        Q(34684079711986262847393, 95458352130098292500000),
        Q(106772567, 100000000),
        Q(95063832187565, 100000000000000),
    ),
)


print("QUARTIC FINITE-TO-ASYMPTOTIC TRANSFER")
print(
    f"edge affine coefficient = {qstr(edge_affine[0])} + "
    f"{qstr(edge_affine[1])}*cap = PASS"
)

for name, mu, AP, cap, cost, frozen in cases:
    fp = fixed_point(mu, AP, cap, cost)
    quotient = transfer_quotient(mu, AP, cap, cost)
    assert 2 - cost + fp == quotient
    assert frozen < quotient
    print(f"\n[{name}]")
    print("fixed-point quotient identity = PASS")
    print(f"transfer quotient = {qstr(quotient)}")
    print(f"strict frozen margin = {qstr(quotient - frozen)}")


c8657 = Q(865674254456636, 10**15)
c8686 = Q(86855250, 10**8)
c9383 = Q(938313327050949, 10**15)
c9506 = Q(95063832187565, 10**14)

assert c8657 < c8686
assert c9383 < c9506

print("\nFROZEN-RUNG MONOTONICITY")
print(f"R-8686 minus R-8657 = {qstr(c8686 - c8657)} = PASS")
print(f"R-9506 minus R-9383 = {qstr(c9506 - c9383)} = PASS")
print("\nall exact checks = PASS")
