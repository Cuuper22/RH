#!/usr/bin/env python3
"""Exact rational replay for the R1a allocation-capacity obstruction."""

from fractions import Fraction as Q
from math import comb


def even_integral(coeffs: tuple[Q, ...]) -> Q:
    """Integral of sum_i coeffs[i] x^(2i) over [-1/2,1/2]."""
    return sum(c / ((2 * i + 1) * 2 ** (2 * i)) for i, c in enumerate(coeffs))


def bernstein_coeffs_on_square_interval(
    coeffs: tuple[Q, ...], edge: Q
) -> tuple[Q, ...]:
    """Bernstein coefficients of -v'(s)/s on 0 <= s^2 <= edge^2.

    For v(s)=sum_i c_i s^(2i), put y=s^2 and
    q(y)=-v'(s)/s=sum_{i>=1} -2*i*c_i*y^(i-1).  Substitute
    y=edge^2*t and convert the power basis on t in [0,1] to the
    Bernstein basis of the same degree.
    """
    power = tuple(-2 * i * coeffs[i] * edge ** (2 * (i - 1))
                  for i in range(1, len(coeffs)))
    degree = len(power) - 1
    return tuple(
        sum(
            power[k] * Q(comb(j, k), comb(degree, k))
            for k in range(j + 1)
        )
        for j in range(degree + 1)
    )


CASES = (
    {
        "name": "Family14999",
        "sigma": Q(14999, 10000),
        "mu": Q(4999, 10000),
        "p": Q(89, 100),
        "coeffs": (
            Q(1189, 1000), Q(-2611, 1000), Q(-1293, 200),
            Q(270061, 1000), Q(-1766327, 500), Q(12751103, 500),
            Q(-106684243, 1000), Q(123437043, 500),
            Q(-26547161, 100), Q(13324801, 200),
        ),
        "expected_area": Q(3815170470337249, 3814073303040000),
        "expected_edge": Q(444911, 2999800),
    },
    {
        "name": "Family19999",
        "sigma": Q(19999, 10000),
        "mu": Q(4999, 10000),
        "p": Q(83, 100),
        "coeffs": (
            Q(2509, 2000), Q(-4689, 1250), Q(17669, 2500),
            Q(-238517, 10000), Q(362157, 5000), Q(-476329, 5000),
        ),
        "expected_area": Q(5913507107, 5913600000),
        "expected_edge": Q(414917, 3999800),
    },
)

Q_ENERGY = Q(2, 5)
EPSILON = Q(1, 100)


def main() -> None:
    print("R1a allocation no-go exact rational replay")
    print(f"energy_ratio_floor={Q_ENERGY}")
    print(f"l1_error={EPSILON}")
    for case in CASES:
        sigma = case["sigma"]
        mu = case["mu"]
        p = case["p"]
        coeffs = case["coeffs"]
        area = even_integral(coeffs)
        edge = mu * p / (2 * sigma)
        v0 = coeffs[0]
        bernstein = bernstein_coeffs_on_square_interval(coeffs, edge)
        lhs = mu * p * v0
        rhs = (1 - EPSILON) * Q_ENERGY * sigma * area
        gap = rhs - lhs

        assert area == case["expected_area"]
        assert edge == case["expected_edge"]
        assert all(b > 0 for b in bernstein)
        assert Q_ENERGY < mu
        assert mu * p < sigma
        assert gap > 0

        print(case["name"])
        print(f"  area={area}")
        print(f"  active_edge={edge}")
        print(f"  profile_center_cap={v0}")
        print(f"  bernstein_degree={len(bernstein) - 1}")
        print(f"  min_bernstein_coefficient={min(bernstein)}")
        print(f"  capacity_lhs={lhs}")
        print(f"  capacity_rhs={rhs}")
        print(f"  strict_gap={gap}")
    print("PASS")


if __name__ == "__main__":
    main()
