#!/usr/bin/env python3
"""Certified arithmetic for the A2.1 common-lattice TDAC obstruction.

The rank argument itself is exact and is written in
``docs/audit/r1a_power_complementary_partition.md``.  This script checks the
only transcendental inputs to its terminal-profile applications: the
residual-symbol edge margins and positivity at the full-support endpoint.

Every reported enclosure is built from ``fractions.Fraction`` interval
arithmetic.  Square roots are enclosed by integer square root at 90 decimal
places; sine and cosine use Taylor polynomials with a rational remainder
bound.  Independent mpmath evaluations at 60 and 100 decimal places are
included as a calibration, not as the proof of the signs.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import factorial, isqrt

import mpmath as mp


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @staticmethod
    def point(value: Fraction | int) -> "Interval":
        value = Fraction(value)
        return Interval(value, value)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(min(products), max(products))

    def reciprocal(self) -> "Interval":
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError("interval contains zero")
        return Interval(min(1 / self.lo, 1 / self.hi), max(1 / self.lo, 1 / self.hi))

    def __truediv__(self, other: "Interval") -> "Interval":
        return self * other.reciprocal()

    def scale(self, value: Fraction | int) -> "Interval":
        return self * Interval.point(Fraction(value))

    def pow(self, exponent: int) -> "Interval":
        if exponent < 0:
            return self.pow(-exponent).reciprocal()
        result = Interval.point(1)
        base = self
        power = exponent
        while power:
            if power & 1:
                result = result * base
            base = base * base
            power >>= 1
        return result

    def max_abs(self) -> Fraction:
        return max(abs(self.lo), abs(self.hi))


def sqrt_interval(value: Fraction, decimal_places: int = 90) -> Interval:
    """Exact rational enclosure of the positive square root."""
    if value <= 0:
        raise ValueError("sqrt_interval expects a positive rational")
    scale = 10**decimal_places
    floor_scaled = isqrt(value.numerator * scale * scale // value.denominator)
    lo = Fraction(floor_scaled, scale)
    hi = Fraction(floor_scaled + 1, scale)
    assert lo * lo <= value <= hi * hi
    return Interval(lo, hi)


def sin_interval(value: Interval, terms: int = 28) -> Interval:
    """Taylor enclosure valid for the arguments (all of modulus < 1) here."""
    assert value.max_abs() < 1
    total = Interval.point(0)
    for k in range(terms):
        term = value.pow(2 * k + 1).scale(Fraction(1, factorial(2 * k + 1)))
        total = total + term if k % 2 == 0 else total - term
    remainder = value.max_abs() ** (2 * terms + 1) / factorial(2 * terms + 1)
    return Interval(total.lo - remainder, total.hi + remainder)


def cos_interval(value: Interval, terms: int = 28) -> Interval:
    """Taylor enclosure valid for the arguments (all of modulus < 1) here."""
    assert value.max_abs() < 1
    total = Interval.point(0)
    for k in range(terms):
        term = value.pow(2 * k).scale(Fraction(1, factorial(2 * k)))
        total = total + term if k % 2 == 0 else total - term
    remainder = value.max_abs() ** (2 * terms) / factorial(2 * terms)
    return Interval(total.lo - remainder, total.hi + remainder)


SQRT2 = sqrt_interval(Fraction(2))
SQRT3 = sqrt_interval(Fraction(3))


def euler_intervals(sigma: Fraction, edge: Fraction) -> dict[str, Interval]:
    """Reconstruct A, B, M, V(edge), and u(sigma/2) by rational intervals."""
    one = Interval.point(1)
    half = Fraction(1, 2)
    sigma_i = Interval.point(sigma)
    b = Fraction(2 - sigma, 2)
    d = b - half
    b_i = Interval.point(b)
    d_i = Interval.point(d)

    sqrt2_b = SQRT2 * b_i
    sqrt3_d = SQRT3 * d_i
    sin_d = sin_interval(d_i)
    cos_d = cos_interval(d_i)
    sin_sqrt3_d = sin_interval(sqrt3_d)
    cos_sqrt3_d = cos_interval(sqrt3_d)
    sin_sqrt2_b = sin_interval(sqrt2_b)
    cos_sqrt2_b = cos_interval(sqrt2_b)

    determinant = (
        SQRT3 * cos_d * cos_sqrt3_d + sin_d * sin_sqrt3_d
    )
    a_const = (
        SQRT3 * cos_sqrt2_b * cos_sqrt3_d
        + SQRT2 * sin_sqrt2_b * sin_sqrt3_d
    ) / determinant
    b_const = (
        cos_sqrt2_b * sin_d - SQRT2 * cos_d * sin_sqrt2_b
    ) / determinant

    outer = Fraction(sigma - 1, 2)
    outer_i = Interval.point(outer)
    normalization_half = (
        sin_sqrt2_b / SQRT2
        + a_const * (sin_interval(outer_i) - sin_d)
        - (b_const / SQRT3)
        * (cos_interval(SQRT3 * outer_i) - cos_sqrt3_d)
    )
    normalization = normalization_half.scale(2)

    edge_i = Interval.point(edge)
    if edge <= b:
        u_edge = cos_interval(SQRT2 * edge_i)
    else:
        edge_shift = edge_i - Interval.point(half)
        u_edge = a_const * cos_interval(edge_shift) + b_const * sin_interval(
            SQRT3 * edge_shift
        )

    endpoint_shift = outer_i
    u_endpoint = a_const * cos_interval(endpoint_shift) + b_const * sin_interval(
        SQRT3 * endpoint_shift
    )
    v_edge = sigma_i * u_edge / normalization
    return {
        "A": a_const,
        "B": b_const,
        "M": normalization,
        "u_endpoint": u_endpoint,
        "V_edge": v_edge,
        "one": one,
    }


def mp_euler_margin(sigma_q: Fraction, mu_q: Fraction, p_q: Fraction, dps: int) -> mp.mpf:
    """Independent floating evaluation, reconstructed from the matching system."""
    mp.mp.dps = dps
    sigma = mp.mpf(sigma_q.numerator) / sigma_q.denominator
    mu = mp.mpf(mu_q.numerator) / mu_q.denominator
    p = mp.mpf(p_q.numerator) / p_q.denominator
    b = (2 - sigma) / 2
    d = b - mp.mpf("0.5")
    matrix = mp.matrix(
        [
            [mp.cos(d), mp.sin(mp.sqrt(3) * d)],
            [-mp.sin(d), mp.sqrt(3) * mp.cos(mp.sqrt(3) * d)],
        ]
    )
    target = mp.matrix(
        [mp.cos(mp.sqrt(2) * b), -mp.sqrt(2) * mp.sin(mp.sqrt(2) * b)]
    )
    a_const, b_const = mp.lu_solve(matrix, target)

    def u(x: mp.mpf) -> mp.mpf:
        x = abs(x)
        if x <= b:
            return mp.cos(mp.sqrt(2) * x)
        return a_const * mp.cos(x - mp.mpf("0.5")) + b_const * mp.sin(
            mp.sqrt(3) * (x - mp.mpf("0.5"))
        )

    normalization = 2 * (mp.quad(u, [0, b]) + mp.quad(u, [b, sigma / 2]))
    return sigma * u(mu * p / 2) / normalization - 1 / p


def decimal(value: Fraction, digits: int = 24) -> str:
    mp.mp.dps = digits + 10
    return mp.nstr(mp.mpf(value.numerator) / value.denominator, digits)


def show_interval(label: str, value: Interval) -> None:
    print(f"{label} in [{decimal(value.lo)}, {decimal(value.hi)}]")


def audit_case(
    name: str,
    sigma: Fraction,
    mu: Fraction,
    p: Fraction,
    rational_margin: Fraction,
) -> None:
    edge = mu * p / 2
    values = euler_intervals(sigma, edge)
    margin = values["V_edge"] - Interval.point(1 / p)
    low_mp = mp_euler_margin(sigma, mu, p, 60)
    high_mp = mp_euler_margin(sigma, mu, p, 100)

    print(f"\n{name}")
    print(f"sigma = {sigma}; mu = {mu}; p = {p}; edge = {edge}")
    show_interval("A", values["A"])
    show_interval("B", values["B"])
    show_interval("M", values["M"])
    show_interval("u(sigma/2)", values["u_endpoint"])
    show_interval("V(edge)-1/p", margin)
    print(f"certified rational comparison: V(edge)-1/p > {rational_margin}")
    print(f"mpmath 100-dps margin = {mp.nstr(high_mp, 30)}")
    print(f"60-vs-100-dps difference = {mp.nstr(abs(low_mp - high_mp), 8)}")

    assert values["A"].lo > 0
    assert values["B"].hi < 0
    assert values["M"].lo > 0
    assert values["u_endpoint"].lo > 0
    assert margin.lo > rational_margin
    assert abs(low_mp - high_mp) < mp.mpf("1e-55")


def main() -> None:
    print("CERTIFIED TERMINAL-PROFILE SIGNS")
    audit_case(
        "R-9506 top-hat",
        Fraction(19999, 10000),
        Fraction(4999, 10000),
        Fraction(83, 100),
        Fraction(1, 1000),
    )
    audit_case(
        "R-8686 top-hat",
        Fraction(14999, 10000),
        Fraction(4999, 10000),
        Fraction(89, 100),
        Fraction(1, 1000),
    )
    audit_case(
        "file-15 flat block",
        Fraction(1499999, 1000000),
        Fraction(499, 1000),
        Fraction(1),
        Fraction(1, 10),
    )

    mu = Fraction(499, 1000)
    profile_mass = Fraction(1031, 1200)
    quadratic_edge_residual = (
        1 - Fraction(169, 100) * (mu / 2) ** 2
    ) / profile_mass - 1
    quadratic_average = (
        1 - Fraction(169, 1200) * mu * mu
    ) / profile_mass
    print("\nNORMALIZED CYCLE-3 QUADRATIC PROFILE")
    print(f"profile mass = {profile_mass}")
    print(f"central flat-block edge residual = {quadratic_edge_residual}")
    print(
        "central flat-block edge residual decimal = "
        f"{decimal(quadratic_edge_residual)}"
    )
    print(f"central width-mu average = {quadratic_average}")
    print(f"central width-mu average decimal = {decimal(quadratic_average)}")
    print(f"average excess above one = {quadratic_average - 1}")
    assert quadratic_edge_residual == Fraction(42756493, 1031000000)
    assert quadratic_edge_residual > 0
    assert quadratic_average == Fraction(1157918831, 1031000000)
    assert quadratic_average > 1

    print("\nEXACT FIBER COUNTS")
    for name, total, distinguished in (
        ("R-9506", 19999, 4999),
        ("R-8686", 14999, 4999),
        ("file-15", 1499999, 499000),
    ):
        complement = total - distinguished
        print(
            f"{name}: required residual rank = {total}; "
            f"available complement rank <= {complement}; deficit = {distinguished}"
        )
        assert complement < total


if __name__ == "__main__":
    main()
