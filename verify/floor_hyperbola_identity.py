#!/usr/bin/env python3
"""Exact finite check of the lcm/hyperbola regrouping in §23."""

from fractions import Fraction
from math import gcd, lcm


def divisors(n: int) -> list[int]:
    small, large = [], []
    d = 1
    while d * d <= n:
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
        d += 1
    return small + large[::-1]


def mobius(n: int) -> int:
    value = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
        p += 1
    return -value if n > 1 else value


def original_coefficients(R: int, r: int) -> dict[int, Fraction]:
    """Coefficient of epsilon(Yv/n) in the original floor remainder."""
    out: dict[int, Fraction] = {}
    for d in range(1, R):
        mu_d = mobius(d)
        if not mu_d:
            continue
        for s in divisors(r):
            n = lcm(s, d)
            value = Fraction(mu_d * gcd(s, d) * mobius(r // s), d)
            out[n] = out.get(n, Fraction()) + value
    return {n: value for n, value in out.items() if value}


def hyperbola_coefficients(R: int, r: int) -> dict[int, Fraction]:
    """Coefficient after d=t*a, a|rad(s), t squarefree and (s,t)=1."""
    out: dict[int, Fraction] = {}
    for s in divisors(r):
        mu_rs = mobius(r // s)
        if not mu_rs:
            continue
        squarefree_divisors = [a for a in divisors(s) if mobius(a)]
        for t in range(1, R):
            mu_t = mobius(t)
            if not mu_t or gcd(t, s) != 1:
                continue
            delta = sum(mobius(a) for a in squarefree_divisors if a * t < R)
            n = s * t
            value = Fraction(mu_rs * mu_t * delta, t)
            out[n] = out.get(n, Fraction()) + value
            if s > 1 and n < R:
                assert delta == 0
    return {n: value for n, value in out.items() if value}


for R in range(3, 25):
    for r in range(R, 3 * R + 1):
        assert original_coefficients(R, r) == hyperbola_coefficients(R, r)

print("Exact floor-hyperbola regrouping checks passed")
