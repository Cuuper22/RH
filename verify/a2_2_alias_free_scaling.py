#!/usr/bin/env python3
"""Exact A2.2 normalization and corrected quartic-tail audit.

The proof in ``docs/audit/r1a_alias_free_fallback.md`` is algebraic.  This
script independently recomputes every rational used there:

* the normalized quadratic-profile cap and the saturated pair costs;
* the first four intrinsic moments of the forced interval restriction;
* a common five-atom probability law with those moments and no mass above
  the *correct* threshold ``Y = sigma - 1``; and
* direct high-precision Gauss--Legendre evaluations of formula (18),
  including the three-dimensional crossing contraction.

All proof decisions use ``fractions.Fraction``.  The mpmath calculation is a
separate calibration of the closed moment formulas, not a source of signs.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q

import mpmath as mp


A = Q(1031, 1200)
B = Q(1809683, 2400000)
VMAX = 1 / A

# Coefficients of the exact autocorrelation polynomial g(u), low degree first.
G = (
    Q(1809683, 2400000),
    -Q(53361, 160000),
    -Q(174239, 120000),
    Q(169, 150),
    Q(0),
    -Q(28561, 300000),
)

# A rational support which works simultaneously in every case below.
ATOMS = (Q(-7, 10), Q(-1, 5), Q(-1, 10), Q(3, 10), Q(2, 5))

# Exact inverse of V[k,i] = ATOMS[i]^k, 0 <= k,i <= 4.
VANDERMONDE_INV = (
    (Q(2, 275), Q(1, 15), -Q(7, 33), -Q(40, 33), Q(100, 33)),
    (-Q(14, 25), -Q(47, 15), Q(74, 3), -Q(20, 3), -Q(200, 3)),
    (Q(7, 5), Q(5, 6), -Q(185, 6), Q(50, 3), Q(250, 3)),
    (Q(7, 25), Q(39, 10), Q(17, 2), -Q(30), -Q(50)),
    (-Q(7, 55), -Q(5, 3), -Q(70, 33), Q(700, 33), Q(1000, 33)),
)


@dataclass(frozen=True)
class Case:
    name: str
    sigma: Q
    mu: Q
    expected_cost: Q
    strict_rs: bool = True


CASES = (
    Case("R-850 support", Q(143, 100), Q(499, 1000),
         Q(2561811364469143, 2227707598259143)),
    Case("file-15 strict support", Q(1499999, 1000000), Q(499, 1000),
         Q(96150315442952061415650847745050283464440727,
           84754191966816092204313678624469283464440727)),
    Case("R-8686 support", Q(14999, 10000), Q(4999, 10000),
         Q(96113968095064133944342067010727,
           84720634821781091664283967010727)),
    Case("R-9506 support", Q(19999, 10000), Q(4999, 10000),
         Q(509004667099686324441527220200727,
           476063683898154328323469120200727)),
    Case("endpoint calibration", Q(2), Q(1, 2),
         Q(318220981, 297629080), strict_rs=False),
)


def dot(left: tuple[Q, ...], right: tuple[Q, ...]) -> Q:
    return sum((x * y for x, y in zip(left, right)), Q(0))


def vandermonde_determinant() -> Q:
    ans = Q(1)
    for i, x in enumerate(ATOMS):
        for y in ATOMS[i + 1 :]:
            ans *= y - x
    return ans


def check_inverse() -> None:
    for i, row in enumerate(VANDERMONDE_INV):
        for j, atom in enumerate(ATOMS):
            assert dot(row, tuple(atom**k for k in range(5))) == (1 if i == j else 0)


def intrinsic_moments(sigma: Q, mu: Q) -> tuple[Q, Q, Q, Q, Q]:
    """Closed rational evaluation of terminal formula (18).

    The forced restriction is

        r(t) = 1 + b*t + c*(t^2 - 1/12),

    where b contains one square root.  Every final moment contains b only
    through b^2, so all arithmetic below is rational.
    """
    delta = mu / sigma
    b2 = Q(4056, 1031) ** 2 * delta**2 * (1 - delta**2) / 12
    c = -Q(2028, 1031) * delta**2

    q2 = b2 / 12 + c**2 / 180
    q3 = b2 * c / 60 + c**3 / 3780
    q4 = b2**2 / 80 + Q(11) * b2 * c**2 / 2520 + c**4 / 15120

    h0 = Q(1, 3) + c / 90 - b2 / 60 - c**2 / 3780
    h1 = c / 180 + b2 / 60 + c**2 / 540 - b2 * c / 560 + c**3 / 45360
    h2 = (
        b2 / 30 + 2 * c**2 / 945 + b2 * c / 168 + c**3 / 5670
        - b2**2 / 420 - b2 * c**2 / 2520 - c**4 / 748440
    )
    double_cross = (
        -b2 / 60 - c**2 / 3780 - b2 * c / 280 + c**3 / 22680
        + b2**2 / 336 + b2 * c**2 / 7560 + 19 * c**4 / 1496880
    )
    r2h2 = (
        Q(7, 60) + c / 90 - 23 * b2 / 2520 + 29 * c**2 / 45360
        - b2 * c / 648 + c**3 / 149688 + 83 * b2**2 / 181440
        + 31 * b2 * c**2 / 1197504 + 23 * c**4 / 116756640
    )
    crossing = (
        Q(1, 30) - b2 / 420 - c**2 / 7560 + c**3 / 311850
        + b2**2 / 10080 - b2 * c**2 / 332640 + c**4 / 2432430
    )

    m2 = q2 + mu**2 * h0
    m3 = q3 + 3 * mu**2 * h1
    m4 = (
        q4 + 4 * mu**2 * h2 + 2 * mu**2 * double_cross
        + 2 * mu**4 * r2h2 + mu**4 * crossing
    )
    return Q(1), Q(0), m2, m3, m4


def witness_weights(moments: tuple[Q, ...]) -> tuple[Q, ...]:
    return tuple(dot(row, moments) for row in VANDERMONDE_INV)


def integrate_poly(coefficients: tuple[Q, ...], lo: Q, hi: Q) -> Q:
    return sum(
        (coefficient * (hi ** (degree + 1) - lo ** (degree + 1)) / (degree + 1)
         for degree, coefficient in enumerate(coefficients)),
        Q(0),
    )


def saturated_cost(sigma: Q) -> Q:
    split = 1 / sigma
    ug = (Q(0),) + G
    j_sigma = 2 * (
        sigma * integrate_poly(ug, Q(0), split)
        + integrate_poly(G, split, Q(1))
    )
    return (B + sigma * j_sigma) / (sigma * A**2)


def mpq(value: Q) -> mp.mpf:
    return mp.mpf(value.numerator) / value.denominator


def direct_quadrature(sigma_q: Q, mu_q: Q) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """Direct numerical integration of (18), independent of its closed form."""
    mp.mp.dps = 55
    nodes, gauss_weights = mp.gauss_quadrature(12, "legendre")

    def integrate(function, lo: mp.mpf, hi: mp.mpf) -> mp.mpf:
        center = (lo + hi) / 2
        radius = (hi - lo) / 2
        return radius * sum(
            gauss_weights[i] * function(center + radius * nodes[i])
            for i in range(len(nodes))
        )

    unit = tuple(((1 + nodes[i]) / 2, gauss_weights[i] / 2) for i in range(len(nodes)))
    sigma = mpq(sigma_q)
    mu = mpq(mu_q)
    delta = mu / sigma
    b = -mp.mpf(4056) / 1031 * delta * mp.sqrt((1 - delta**2) / 12)
    c = -mp.mpf(2028) / 1031 * delta**2

    def r(t: mp.mpf) -> mp.mpf:
        return 1 + b * t + c * (t**2 - mp.mpf(1) / 12)

    def q(t: mp.mpf) -> mp.mpf:
        return r(t) - 1

    half = mp.mpf(1) / 2

    def h(x: mp.mpf) -> mp.mpf:
        return (
            integrate(lambda y: (x - y) * r(y), -half, x)
            + integrate(lambda y: (y - x) * r(y), x, half)
        )

    m2 = integrate(lambda x: q(x) ** 2, -half, half)
    m2 += mu**2 * integrate(lambda x: r(x) * h(x), -half, half)

    m3 = integrate(lambda x: q(x) ** 3, -half, half)
    m3 += 3 * mu**2 * integrate(lambda x: q(x) * r(x) * h(x), -half, half)

    double_cross = 2 * integrate(
        lambda x: integrate(
            lambda y: q(x) * r(x) * q(y) * r(y) * (x - y), -half, x
        ),
        -half,
        half,
    )
    m4 = integrate(lambda x: q(x) ** 4, -half, half)
    m4 += 4 * mu**2 * integrate(lambda x: q(x) ** 2 * r(x) * h(x), -half, half)
    m4 += 2 * mu**2 * double_cross
    m4 += 2 * mu**4 * integrate(lambda x: r(x) ** 2 * h(x) ** 2, -half, half)

    # Put a=x-y and z-y=+/- b.  In each of the four sign quadrants the
    # (a,b)-domain is the simplex a,b>=0, a+b<=1.  Map it and the remaining
    # y-interval to a unit cube before applying tensor Gauss--Legendre.
    def crossing_quadrant(sign_a: int, sign_b: int) -> mp.mpf:
        total = mp.mpf(0)
        for s, ws in unit:
            for t, wt in unit:
                aa = s
                bb = (1 - s) * t
                simplex_jacobian = 1 - s
                if sign_a == 1 and sign_b == 1:
                    lo, hi = -half, half - aa - bb
                    shifts = (aa, bb, aa + bb)
                elif sign_a == -1 and sign_b == -1:
                    lo, hi = -half + aa + bb, half
                    shifts = (-aa, -bb, -aa - bb)
                elif sign_a == 1 and sign_b == -1:
                    lo, hi = -half + bb, half - aa
                    shifts = (aa, -bb, aa - bb)
                else:
                    lo, hi = -half + aa, half - bb
                    shifts = (-aa, bb, -aa + bb)
                for u, wu in unit:
                    y = lo + (hi - lo) * u
                    total += (
                        ws * wt * wu * simplex_jacobian * (hi - lo) * aa * bb
                        * r(y + shifts[0]) * r(y) * r(y + shifts[1]) * r(y + shifts[2])
                    )
        return total

    crossing = sum(
        (crossing_quadrant(sa, sb) for sa in (1, -1) for sb in (1, -1)),
        mp.mpf(0),
    )
    m4 += mu**4 * crossing
    return m2, m3, m4


def decimal(value: Q, digits: int = 13) -> str:
    mp.mp.dps = digits + 8
    return mp.nstr(mpq(value), digits)


def main() -> None:
    print("A2.2 alias-free normalization and corrected-tail audit")
    print(f"A = {A}")
    print(f"sup V = 1/A = {VMAX} = {decimal(VMAX)}")
    assert vandermonde_determinant() == Q(99, 500000)
    check_inverse()
    print(f"Vandermonde determinant = {vandermonde_determinant()} > 0")
    print("atoms = " + str(ATOMS))
    assert min(1 + atom for atom in ATOMS) == Q(3, 10) > 0
    print("min(1 + atom) = 3/10 > 0")

    for case in CASES:
        assert 1 < case.sigma
        assert 2 * case.mu < case.sigma
        assert VMAX < case.sigma
        moments = intrinsic_moments(case.sigma, case.mu)
        weights = witness_weights(moments)
        assert all(weight > Q(1, 25) for weight in weights)
        assert sum(weights, Q(0)) == 1
        for degree in range(5):
            assert sum(
                (weight * atom**degree for atom, weight in zip(ATOMS, weights)), Q(0)
            ) == moments[degree]
        threshold_gap = case.sigma - 1 - max(ATOMS)
        assert threshold_gap > 0
        cost = saturated_cost(case.sigma)
        assert cost == case.expected_cost

        numerical = direct_quadrature(case.sigma, case.mu)
        exact_numerical = tuple(mpq(value) for value in moments[2:])
        errors = tuple(abs(x - y) for x, y in zip(numerical, exact_numerical))
        assert max(errors) < mp.mpf("1e-45")

        print()
        print(f"[{case.name}] sigma={case.sigma}, mu={case.mu}, strict_RS={case.strict_rs}")
        print("moments M2,M3,M4 = " + ", ".join(decimal(value) for value in moments[2:]))
        print("weights = " + ", ".join(decimal(value) for value in weights))
        print("all weights > 1/25: PASS")
        print("exact moment reconstruction through degree 4: PASS")
        print(f"threshold gap sigma-1-max(atom) = {threshold_gap} > 0")
        print("corrected positive tail before trimming = 0")
        print(f"D_sigma = {cost}")
        print(f"2-D_sigma = {2 - cost}")
        print("direct-quadrature max error = " + mp.nstr(max(errors), 5))

    print()
    print("RESULT: A2.2 mean-one cap fails and the honest degree-four tail optimum is 0.")


if __name__ == "__main__":
    main()
