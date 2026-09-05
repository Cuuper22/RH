#!/usr/bin/env python3
"""Exact finite check of the reduced reciprocal-frequency grouping in §27."""

from fractions import Fraction
from math import gcd


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


def core_coefficients(R: int, r: int, Y: int) -> dict[int, Fraction]:
    """B_r(n), before the Fourier coefficient 1/h."""
    out: dict[int, Fraction] = {}
    for s in divisors(r):
        mu_rs = mobius(r // s)
        if not mu_rs:
            continue
        sf_divs = [a for a in divisors(s) if mobius(a)]
        for t in range(1, R):
            mu_t = mobius(t)
            n = s * t
            if not mu_t or gcd(s, t) != 1 or not (R <= n <= Y):
                continue
            delta = sum(mobius(a) for a in sf_divs if a * t < R)
            value = mu_rs * mu_t * s * delta
            if value:
                out[n] = out.get(n, Fraction()) + value
    return {n: value for n, value in out.items() if value}


def grouped(coeffs: dict[int, Fraction], Y: int) -> dict[int, Fraction]:
    """Gamma_r(k)=sum_m B_r(km)/m."""
    return {
        k: sum((coeffs.get(k * m, Fraction()) / m for m in range(1, Y // k + 1)), Fraction())
        for k in range(1, Y + 1)
    }


for R in range(3, 15):
    Y = R * R
    for r in range(R, 3 * R + 1):
        coeffs = core_coefficients(R, r, Y)
        gamma = grouped(coeffs, Y)
        for k in range(1, Y + 1):
            for a in range(-5, 6):
                if not a or gcd(abs(a), k) != 1:
                    continue
                # The coefficient of the reduced frequency a/k in the
                # ungrouped h/n expansion has h=a(n/k).
                direct = sum(
                    (value / (a * (n // k)) for n, value in coeffs.items() if n % k == 0),
                    Fraction(),
                )
                assert direct == gamma[k] / a

print("Exact reduced-frequency grouping checks passed")
