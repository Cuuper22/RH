#!/usr/bin/env python3
"""Independent arithmetic audit for the three source-only quartic rungs.

This verifier deliberately separates four questions which the run documents
had mixed together:

* exact top-hat moments and fixed-point arithmetic for R-8686/R-9506;
* exact global sign checks for their two rational contact duals;
* explicit positive *rational-polynomial* windows whose exact saturated
  costs beat the directed bounds used by those certificates; and
* a calibrated high-precision recomputation of the flat endpoint branch for
  R-9383.

Every proof decision for R-8686/R-9506 uses ``fractions.Fraction``.  Window
positivity is certified by an exact positive Bernstein expansion, rather
than by sampling.  The R-9383 Euler cost is transcendental, so that section
is a two-precision mpmath calibration.  It exposes a genuine directed-
rounding obstruction: the frozen decimal is the nearest 15-place rounding,
but is strictly *above* the recomputed endpoint branch.

This script audits certificate arithmetic only.  It does not reinstate the
mean-one principal-compression construction killed by Phase A2.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import comb

import mpmath as mp


# Keep decimal-string constants exact well beyond every reported digit even
# outside the explicit work-precision blocks below.
mp.mp.dps = 100


def qstr(value: Q) -> str:
    return f"{value.numerator}/{value.denominator}" if value.denominator != 1 else str(value.numerator)


def qdecimal(value: Q, places: int = 24) -> str:
    with localcontext() as context:
        context.prec = places + 20
        number = Decimal(value.numerator) / Decimal(value.denominator)
        return format(number, f".{places}f")


def mpq(value: Q) -> mp.mpf:
    return mp.mpf(value.numerator) / value.denominator


def print_rationals(label: str, values: tuple[Q, ...] | list[Q]) -> None:
    print(f"{label} = [{', '.join(qstr(value) for value in values)}]")


# ---------------------------------------------------------------------------
# Exact polynomial integration and rational saturated-window witnesses.


def poly_add(left: list[Q], right: list[Q]) -> list[Q]:
    result = [Q(0)] * max(len(left), len(right))
    for index, value in enumerate(left):
        result[index] += value
    for index, value in enumerate(right):
        result[index] += value
    while result and result[-1] == 0:
        result.pop()
    return result


def poly_scale(poly: list[Q], scalar: Q) -> list[Q]:
    return [scalar * value for value in poly]


def linear_power(constant: Q, linear: Q, exponent: int) -> list[Q]:
    return [
        Q(comb(exponent, degree)) * constant ** (exponent - degree) * linear**degree
        for degree in range(exponent + 1)
    ]


def integrate_poly(poly: list[Q], lower: Q, upper: Q) -> Q:
    return sum(
        (
            coefficient * (upper ** (degree + 1) - lower ** (degree + 1))
            / (degree + 1)
            for degree, coefficient in enumerate(poly)
        ),
        Q(0),
    )


def autocorrelation_basis(left_index: int, right_index: int) -> list[Q]:
    """Return g_ij(u)=int s^(2i)(s+u)^(2j) ds on [-1/2,1/2-u]."""
    result: list[Q] = []
    for shift_degree in range(2 * right_index + 1):
        antiderivative_degree = 2 * left_index + shift_degree + 1
        boundary = linear_power(Q(1, 2), Q(-1), antiderivative_degree)
        boundary[0] -= Q(-1, 2) ** antiderivative_degree
        scalar = Q(comb(2 * right_index, shift_degree), antiderivative_degree)
        term = [Q(0)] * (2 * right_index - shift_degree)
        term += poly_scale(boundary, scalar)
        result = poly_add(result, term)
    return result


def cost_entry(sigma: Q, left_index: int, right_index: int) -> Q:
    """Entry of B + sigma*J for the even monomial basis."""
    square_integral = Q(
        1,
        (2 * (left_index + right_index) + 1) * 2 ** (2 * (left_index + right_index)),
    )
    autocorrelation = autocorrelation_basis(left_index, right_index)
    split = 1 / sigma
    saturated_j = 2 * (
        sigma * integrate_poly([Q(0)] + autocorrelation, Q(0), split)
        + integrate_poly(autocorrelation, split, Q(1))
    )
    return square_integral + sigma * saturated_j


def symmetric_cost_matrix(sigma: Q, size: int) -> list[list[Q]]:
    raw = [[cost_entry(sigma, i, j) for j in range(size)] for i in range(size)]
    return [[(raw[i][j] + raw[j][i]) / 2 for j in range(size)] for i in range(size)]


def window_cost(sigma: Q, coefficients: tuple[Q, ...]) -> tuple[Q, Q]:
    matrix = symmetric_cost_matrix(sigma, len(coefficients))
    area = sum(
        (
            coefficient / ((2 * index + 1) * 2 ** (2 * index))
            for index, coefficient in enumerate(coefficients)
        ),
        Q(0),
    )
    numerator = sum(
        (
            coefficients[i] * matrix[i][j] * coefficients[j]
            for i in range(len(coefficients))
            for j in range(len(coefficients))
        ),
        Q(0),
    )
    return area, numerator / (sigma * area**2)


def even_poly_bernstein(coefficients: tuple[Q, ...]) -> tuple[Q, ...]:
    """Bernstein coefficients of v(x-1/2), 0<=x<=1."""
    degree = 2 * (len(coefficients) - 1)
    power = [Q(0)] * (degree + 1)
    for index, coefficient in enumerate(coefficients):
        shifted = poly_scale(linear_power(Q(-1, 2), Q(1), 2 * index), coefficient)
        for power_index, value in enumerate(shifted):
            power[power_index] += value
    return tuple(
        sum(
            (
                power[k] * Q(comb(j, k), comb(degree, k))
                for k in range(j + 1)
            ),
            Q(0),
        )
        for j in range(degree + 1)
    )


@dataclass(frozen=True)
class WindowWitness:
    name: str
    sigma: Q
    coefficients: tuple[Q, ...]
    directed_bound: Q


WINDOWS = (
    WindowWitness(
        "R-8686 window",
        Q(14999, 10000),
        (
            Q(1189, 1000),
            -Q(2611, 1000),
            -Q(1293, 200),
            Q(270061, 1000),
            -Q(1766327, 500),
            Q(12751103, 500),
            -Q(106684243, 1000),
            Q(123437043, 500),
            -Q(26547161, 100),
            Q(13324801, 200),
        ),
        Q(113434643, 100000000),
    ),
    WindowWitness(
        "R-9506 window",
        Q(19999, 10000),
        (
            Q(2509, 2000),
            -Q(4689, 1250),
            Q(17669, 2500),
            -Q(238517, 10000),
            Q(362157, 5000),
            -Q(476329, 5000),
        ),
        Q(106772567, 100000000),
    ),
)


def audit_windows() -> None:
    print("RATIONAL SATURATED-WINDOW WITNESSES")
    # Independent self-test against the already formalized support-143/100 window.
    _, known_cost = window_cost(Q(143, 100), (Q(1), -Q(169, 100)))
    assert known_cost == Q(2561811364469143, 2227707598259143)
    print(f"support-143/100 integration self-test = {qstr(known_cost)}")

    for witness in WINDOWS:
        area, cost = window_cost(witness.sigma, witness.coefficients)
        bernstein = even_poly_bernstein(witness.coefficients)
        minimum = min(bernstein)
        minimum_index = bernstein.index(minimum)
        margin = witness.directed_bound - cost
        assert area > 0
        assert all(coefficient > 0 for coefficient in bernstein)
        assert margin > 0
        print()
        print(f"[{witness.name}] sigma={qstr(witness.sigma)}")
        print(f"degree = {2 * (len(witness.coefficients) - 1)}")
        print_rationals("even monomial coefficients", witness.coefficients)
        print(f"integral = {qstr(area)}")
        print(f"minimum Bernstein coefficient = {qstr(minimum)} (index {minimum_index})")
        print(f"exact cost = {qstr(cost)}")
        print(f"exact cost decimal = {qdecimal(cost)}")
        print(f"directed bound = {qstr(witness.directed_bound)}")
        print(f"bound minus cost = {qstr(margin)}")
        print(f"bound minus cost decimal = {qdecimal(margin, 30)}")
        print("pointwise positivity = PASS (all exact Bernstein coefficients positive)")


# ---------------------------------------------------------------------------
# Exact moments, contact duals, global factor signs, and fixed points.


def solve_linear(matrix: list[list[Q]], right_hand_side: list[Q]) -> list[Q]:
    augmented = [list(map(Q, row)) + [Q(value)] for row, value in zip(matrix, right_hand_side)]
    size = len(augmented)
    for column in range(size):
        pivot = next(row for row in range(column, size) if augmented[row][column])
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        scale = augmented[column][column]
        augmented[column] = [value / scale for value in augmented[column]]
        for row in range(size):
            if row != column and augmented[row][column]:
                scale = augmented[row][column]
                augmented[row] = [
                    value - scale * pivot_value
                    for value, pivot_value in zip(augmented[row], augmented[column])
                ]
    return [augmented[row][-1] for row in range(size)]


def contact_dual(a: Q, c: Q, t: Q) -> tuple[Q, ...]:
    def value_row(x: Q) -> list[Q]:
        return [x**degree for degree in range(5)] + [Q(0)]

    def derivative_row(x: Q) -> list[Q]:
        return [Q(0)] + [Q(degree) * x ** (degree - 1) for degree in range(1, 5)] + [Q(0)]

    row_at_t = value_row(t)
    row_at_t[-1] = -1
    matrix = [value_row(a), derivative_row(a), value_row(c), derivative_row(c), row_at_t,
              derivative_row(t)]
    rhs = [Q(0), Q(0), c**2, 2 * c, Q(0), Q(0)]
    return tuple(solve_linear(matrix, rhs))


def polynomial_value(coefficients: tuple[Q, ...] | list[Q], x: Q) -> Q:
    return sum((coefficient * x**degree for degree, coefficient in enumerate(coefficients)), Q(0))


def polynomial_derivative_value(coefficients: tuple[Q, ...] | list[Q], x: Q) -> Q:
    return sum(
        (degree * coefficient * x ** (degree - 1) for degree, coefficient in enumerate(coefficients[1:], 1)),
        Q(0),
    )


def divide_exact(numerator: list[Q], denominator: list[Q]) -> tuple[Q, ...]:
    work = list(numerator)
    quotient = [Q(0)] * (len(work) - len(denominator) + 1)
    while len(work) >= len(denominator):
        offset = len(work) - len(denominator)
        coefficient = work[-1] / denominator[-1]
        quotient[offset] = coefficient
        for index, value in enumerate(denominator):
            work[offset + index] -= coefficient * value
        while work and work[-1] == 0:
            work.pop()
    assert not work
    return tuple(quotient)


def top_hat_moments(mu: Q, p: Q) -> tuple[Q, ...]:
    q0 = 1 - p
    return (
        Q(1),
        Q(0),
        q0 / p + mu**2 * p / 3,
        q0**3 / p**2 - q0 + mu**2 * q0,
        q0**4 / p**3 + q0 + 2 * mu**2 * q0**2 / p + 4 * mu**4 * p / 15,
    )


@dataclass(frozen=True)
class RationalCertificate:
    name: str
    mu: Q
    p: Q
    directed_cost: Q
    contacts: tuple[Q, Q, Q]
    frozen_target: Q
    source_epsilon_truncation: Q
    expected_moments: tuple[Q, Q, Q]


CERTIFICATES = (
    RationalCertificate(
        "R-8686",
        Q(4999, 10000),
        Q(89, 100),
        Q(113434643, 100000000),
        (Q(-8905, 10000), Q(911, 10000), Q(6623, 10000)),
        Q(86855250, 100000000),
        Q(28989382854, 10000000000000),
        (
            Q(527945797921, 2670000000000),
            -Q(6402596222869, 79210000000000),
            Q(348494870075912117922241, 2643633750000000000000000),
        ),
    ),
    RationalCertificate(
        "R-9506",
        Q(4999, 10000),
        Q(83, 100),
        Q(106772567, 100000000),
        (Q(-9081, 10000), Q(113, 500), Q(4839, 5000)),
        Q(95063832187565, 100000000000000),
        Q(1836399187565, 100000000000000),
        (
            Q(682156116889, 2490000000000),
            -Q(8293346012887, 68890000000000),
            Q(434598816917989781038321, 2144201250000000000000000),
        ),
    ),
)


def certificate_exact_data(certificate: RationalCertificate) -> dict[str, object]:
    moments = top_hat_moments(certificate.mu, certificate.p)
    assert moments[2:] == certificate.expected_moments
    dual = contact_dual(*certificate.contacts)
    polynomial = dual[:5]
    cap = dual[5]
    a, c, t = certificate.contacts

    assert polynomial_value(polynomial, a) == 0
    assert polynomial_derivative_value(polynomial, a) == 0
    assert polynomial_value(polynomial, c) == c**2
    assert polynomial_derivative_value(polynomial, c) == 2 * c
    assert polynomial_value(polynomial, t) == cap
    assert polynomial_derivative_value(polynomial, t) == 0

    factor_p = divide_exact(list(polynomial), [a**2, -2 * a, Q(1)])
    factor_square = divide_exact(
        [-polynomial[0], -polynomial[1], 1 - polynomial[2], -polynomial[3], -polynomial[4]],
        [c**2, -2 * c, Q(1)],
    )
    factor_cap = divide_exact(
        [cap - polynomial[0], -polynomial[1], -polynomial[2], -polynomial[3], -polynomial[4]],
        [t**2, -2 * t, Q(1)],
    )
    discriminant_square = factor_square[1] ** 2 - 4 * factor_square[0] * factor_square[2]
    discriminant_cap = factor_cap[1] ** 2 - 4 * factor_cap[0] * factor_cap[2]

    # For z<=0 every term of factor_p is strictly negative/nonpositive.
    assert factor_p[0] < 0 and factor_p[1] > 0 and factor_p[2] < 0
    # The other factors are globally positive quadratics.
    assert factor_square[2] > 0 and discriminant_square < 0
    assert factor_cap[2] > 0 and discriminant_cap < 0
    assert 0 < cap < 2

    moment_score = sum((polynomial[index] * moments[index] for index in range(5)), Q(0))
    epsilon = (
        certificate.mu * moment_score - cap * (certificate.directed_cost - 1) / 2
    ) / (1 - cap / 2)
    rung = 2 - certificate.directed_cost + epsilon
    assert epsilon > certificate.source_epsilon_truncation
    assert rung > certificate.frozen_target

    return {
        "moments": moments,
        "dual": dual,
        "factor_p": factor_p,
        "factor_square": factor_square,
        "factor_cap": factor_cap,
        "discriminant_square": discriminant_square,
        "discriminant_cap": discriminant_cap,
        "moment_score": moment_score,
        "epsilon": epsilon,
        "rung": rung,
    }


def audit_rational_certificates() -> None:
    print("\nEXACT R-8686 / R-9506 CERTIFICATE ARITHMETIC")
    for certificate in CERTIFICATES:
        data = certificate_exact_data(certificate)
        moments = data["moments"]
        dual = data["dual"]
        rung = data["rung"]
        assert isinstance(moments, tuple) and isinstance(dual, tuple) and isinstance(rung, Q)
        print()
        print(f"[{certificate.name}] mu={qstr(certificate.mu)}, p={qstr(certificate.p)}")
        print(f"directed D = {qstr(certificate.directed_cost)}")
        print_rationals("moments M0..M4", moments)
        print_rationals("dual p0..p4,L", dual)
        print_rationals("P/(y-a)^2", data["factor_p"])
        print_rationals("(y^2-P)/(y-c)^2", data["factor_square"])
        print_rationals("(L-P)/(y-t)^2", data["factor_cap"])
        print(f"disc square factor = {qstr(data['discriminant_square'])}")
        print(f"disc cap factor = {qstr(data['discriminant_cap'])}")
        print("global dual inequalities = PASS (exact coefficient/discriminant signs)")
        print(f"A_P = {qstr(data['moment_score'])}")
        print(f"epsilon = {qstr(data['epsilon'])}")
        print(f"epsilon decimal = {qdecimal(data['epsilon'])}")
        print(f"rung = {qstr(rung)}")
        print(f"rung decimal = {qdecimal(rung)}")
        margin = rung - certificate.frozen_target
        print(f"margin over frozen target = {qstr(margin)}")
        print(f"margin decimal = {qdecimal(margin, 30)}")


# ---------------------------------------------------------------------------
# Numerical primal calibration for the rational duals.


def optimal_top_hat_branch(certificate: RationalCertificate) -> dict[str, mp.mpf]:
    with mp.workdps(90):
        mu = mpq(certificate.mu)
        p = mpq(certificate.p)
        cost = mpq(certificate.directed_cost)
        moments_q = top_hat_moments(certificate.mu, certificate.p)
        moments = tuple(mpq(value) for value in moments_q)

        def equations(trim_mass: mp.mpf, high_atom: mp.mpf):
            mass = 1 - trim_mass
            first = moments[1] - trim_mass * high_atom
            second = moments[2] - trim_mass * high_atom**2
            third = moments[3] - trim_mass * high_atom**3
            fourth = moments[4] - trim_mass * high_atom**4
            hankel = mass * second - first**2
            atom_sum = (mass * third - first * second) / hankel
            atom_product = (first * third - second**2) / hankel
            discriminant = atom_sum**2 - 4 * atom_product
            negative_atom = (atom_sum - mp.sqrt(discriminant)) / 2
            positive_atom = (atom_sum + mp.sqrt(discriminant)) / 2
            negative_mass = (positive_atom * mass - first) / (positive_atom - negative_atom)
            positive_mass = mass - negative_mass
            epsilon = mu * positive_mass * positive_atom**2
            moment_residual = fourth * hankel - (
                mass * third**2 - 2 * first * second * third + second**3
            )
            fixed_residual = cost - 1 - epsilon - 2 * mu * trim_mass
            return (
                moment_residual,
                fixed_residual,
                negative_atom,
                positive_atom,
                negative_mass,
                positive_mass,
                epsilon,
            )

        a0, _, t0 = certificate.contacts
        initial_trim = (certificate.directed_cost - 1) / (2 * certificate.mu)
        trim_mass, high_atom = mp.findroot(
            lambda trim, high: equations(trim, high)[:2],
            (mpq(initial_trim), mpq(t0)),
            tol=mp.mpf("1e-75"),
            maxsteps=100,
        )
        values = equations(trim_mass, high_atom)
        assert abs(values[0]) < mp.mpf("1e-70")
        assert abs(values[1]) < mp.mpf("1e-70")
        return {
            "trim": +trim_mass,
            "high": +high_atom,
            "negative": +values[2],
            "positive": +values[3],
            "negative_mass": +values[4],
            "positive_mass": +values[5],
            "epsilon": +values[6],
            "rung": +(2 - cost + values[6]),
            "moment_residual": +values[0],
            "fixed_residual": +values[1],
        }


def audit_primal_calibration() -> None:
    print("\nTHREE-ATOM PRIMAL CALIBRATION (NON-PROOF NUMERICAL CROSS-CHECK)")
    for certificate in CERTIFICATES:
        exact = certificate_exact_data(certificate)
        primal = optimal_top_hat_branch(certificate)
        dual_rung = mpq(exact["rung"])
        gap = primal["rung"] - dual_rung
        assert gap > 0
        assert gap < mp.mpf("1e-8")
        print()
        print(f"[{certificate.name}]")
        print(f"atoms = ({mp.nstr(primal['negative'], 28)}, {mp.nstr(primal['positive'], 28)}, "
              f"{mp.nstr(primal['high'], 28)})")
        print(f"masses = ({mp.nstr(primal['negative_mass'], 28)}, "
              f"{mp.nstr(primal['positive_mass'], 28)}, {mp.nstr(primal['trim'], 28)})")
        print(f"primal equality rung = {mp.nstr(primal['rung'], 35)}")
        print(f"primal minus rational-dual rung = {mp.nstr(gap, 20)}")
        print(f"moment residual = {mp.nstr(primal['moment_residual'], 5)}")
        print(f"fixed-point residual = {mp.nstr(primal['fixed_residual'], 5)}")


# ---------------------------------------------------------------------------
# R-9383 endpoint branch and the upward-rounding obstruction.


def r9383_endpoint(precision: int) -> dict[str, mp.mpf]:
    with mp.workdps(precision):
        root_three = mp.sqrt(3)
        cos_half = mp.cos(mp.mpf(1) / 2)
        sin_half = mp.sin(mp.mpf(1) / 2)
        cos_three_half = mp.cos(root_three / 2)
        sin_three_half = mp.sin(root_three / 2)
        determinant = cos_half * root_three * cos_three_half + sin_three_half * sin_half
        coefficient_a = root_three * cos_three_half / determinant
        coefficient_b = -sin_half / determinant

        # Closed elementary integrals of
        # A cos(x-1/2)+B sin(sqrt(3)(x-1/2)), 0<=x<=1.
        half_mass = 2 * coefficient_a * sin_half
        mass = 2 * half_mass
        first_weighted = coefficient_a * sin_half + coefficient_b * (
            -cos_three_half / root_three + 2 * sin_three_half / 3
        )
        cost = (1 + 2 * first_weighted) / mass
        mu = mp.mpf(1) / 2

        def equations(trim_mass: mp.mpf, high_atom: mp.mpf):
            mass_left = 1 - trim_mass
            first = -trim_mass * high_atom
            second = mp.mpf(1) / 3 - trim_mass * high_atom**2
            third = -trim_mass * high_atom**3
            fourth = mp.mpf(4) / 15 - trim_mass * high_atom**4
            hankel = mass_left * second - first**2
            atom_sum = (mass_left * third - first * second) / hankel
            atom_product = (first * third - second**2) / hankel
            discriminant = atom_sum**2 - 4 * atom_product
            negative_atom = (atom_sum - mp.sqrt(discriminant)) / 2
            positive_atom = (atom_sum + mp.sqrt(discriminant)) / 2
            negative_mass = (
                positive_atom * mass_left - first
            ) / (positive_atom - negative_atom)
            positive_mass = mass_left - negative_mass
            epsilon = mu**3 * positive_mass * positive_atom**2
            moment_residual = fourth * hankel - (
                mass_left * third**2 - 2 * first * second * third + second**3
            )
            fixed_residual = cost - 1 - 2 * mu * trim_mass - epsilon
            return (
                moment_residual,
                fixed_residual,
                negative_atom,
                positive_atom,
                negative_mass,
                positive_mass,
                epsilon,
            )

        trim_mass, high_atom = mp.findroot(
            lambda trim, high: equations(trim, high)[:2],
            (mp.mpf("0.0617"), mp.mpf("1.2669")),
            tol=mp.mpf(10) ** (-(precision - 15)),
            maxsteps=100,
        )
        values = equations(trim_mass, high_atom)

        # A nonzero local Jacobian makes the precision calibration meaningful.
        first_first = mp.diff(lambda value: equations(value, high_atom)[0], trim_mass)
        first_second = mp.diff(lambda value: equations(trim_mass, value)[0], high_atom)
        second_first = mp.diff(lambda value: equations(value, high_atom)[1], trim_mass)
        second_second = mp.diff(lambda value: equations(trim_mass, value)[1], high_atom)
        jacobian_determinant = first_first * second_second - first_second * second_first

        return {
            "A": +coefficient_a,
            "B": +coefficient_b,
            "mass": +mass,
            "cost": +cost,
            "trim": +trim_mass,
            "high": +high_atom,
            "negative": +values[2],
            "positive": +values[3],
            "negative_mass": +values[4],
            "positive_mass": +values[5],
            "epsilon": +values[6],
            "rung": +(2 - cost + values[6]),
            "moment_residual": +values[0],
            "fixed_residual": +values[1],
            "jacobian": +jacobian_determinant,
        }


def audit_r9383() -> None:
    print("\nR-9383 ENDPOINT CALIBRATION AND DIRECTED-ROUNDING CHECK")
    low_precision = r9383_endpoint(90)
    high_precision = r9383_endpoint(140)
    for key in ("cost", "trim", "high", "negative", "positive", "epsilon", "rung"):
        assert abs(low_precision[key] - high_precision[key]) < mp.mpf("1e-75")
    assert abs(high_precision["moment_residual"]) < mp.mpf("1e-120")
    assert abs(high_precision["fixed_residual"]) < mp.mpf("1e-120")
    assert abs(high_precision["jacobian"]) > mp.mpf("0.1")

    target = mp.mpf("0.938313327050949")
    gap = target - high_precision["rung"]
    assert mp.mpf("1e-16") < gap < mp.mpf("2e-16")
    scale = mp.mpf(10) ** 15
    downward = mp.floor(high_precision["rung"] * scale) / scale
    nearest = mp.nint(high_precision["rung"] * scale) / scale
    assert nearest == target
    assert downward == mp.mpf("0.938313327050948")

    print(f"Euler A = {mp.nstr(high_precision['A'], 70)}")
    print(f"Euler B = {mp.nstr(high_precision['B'], 70)}")
    print(f"Euler mass = {mp.nstr(high_precision['mass'], 70)}")
    print(f"D_2 = {mp.nstr(high_precision['cost'], 70)}")
    print(f"trim mass q = {mp.nstr(high_precision['trim'], 70)}")
    print(f"atoms = ({mp.nstr(high_precision['negative'], 55)}, "
          f"{mp.nstr(high_precision['positive'], 55)}, {mp.nstr(high_precision['high'], 55)})")
    print(f"masses = ({mp.nstr(high_precision['negative_mass'], 55)}, "
          f"{mp.nstr(high_precision['positive_mass'], 55)}, {mp.nstr(high_precision['trim'], 55)})")
    print(f"epsilon_2 = {mp.nstr(high_precision['epsilon'], 70)}")
    print(f"endpoint rung = {mp.nstr(high_precision['rung'], 70)}")
    print(f"frozen R-9383 target = {mp.nstr(target, 70)}")
    print(f"target minus endpoint = {mp.nstr(gap, 70)}")
    print(f"15-place downward rounding = {mp.nstr(downward, 20)}")
    print(f"15-place nearest rounding = {mp.nstr(nearest, 20)}")
    print(f"moment residual = {mp.nstr(high_precision['moment_residual'], 8)}")
    print(f"fixed-point residual = {mp.nstr(high_precision['fixed_residual'], 8)}")
    print(f"local Jacobian determinant = {mp.nstr(high_precision['jacobian'], 55)}")
    print("R-9383 frozen inequality = OBSTRUCTED (nearest rounding is upward, not a lower bound)")


def main() -> None:
    audit_windows()
    audit_rational_certificates()
    audit_primal_calibration()
    audit_r9383()
    print("\nSUMMARY")
    print("R-8686 exact conditional certificate arithmetic = PASS")
    print("R-9506 exact conditional certificate arithmetic = PASS")
    print("R-9383 frozen 15-place lower bound = FAIL (upward-rounding obstruction)")
    print("All expected audit assertions passed.")


if __name__ == "__main__":
    main()
