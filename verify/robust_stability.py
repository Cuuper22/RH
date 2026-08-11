#!/usr/bin/env python3
"""Independent exact audit of the finite robust-stability accounting.

The verifier uses only integer arithmetic and ``fractions.Fraction``.  A
small multivariate-polynomial implementation expands the substituted finite
prebound

    F - 4 T + s + 2 traceCap + 4 b

with ``F = D N + e_F``, ``T = N - e_T``, and
``traceCap = s + e_P``.  It checks the robust error coefficients and the
remaining count slack symbolically, then replays exact rational samples and
the finite sorted-head trimming construction used in Lean.
"""

from __future__ import annotations

from fractions import Fraction as Q
from typing import Iterable


VARIABLES = (
    "D",
    "zeroScale",
    "s",
    "b",
    "pTraceErr",
    "traceErr",
    "frobErr",
)
INDEX = {name: position for position, name in enumerate(VARIABLES)}
Monomial = tuple[int, ...]
Polynomial = dict[Monomial, Q]
ZERO_MONOMIAL: Monomial = (0,) * len(VARIABLES)


def clean(poly: Polynomial) -> Polynomial:
    return {monomial: coefficient for monomial, coefficient in poly.items() if coefficient}


def constant(value: int | Q) -> Polynomial:
    coefficient = value if isinstance(value, Q) else Q(value)
    return {} if coefficient == 0 else {ZERO_MONOMIAL: coefficient}


def variable(name: str) -> Polynomial:
    exponents = [0] * len(VARIABLES)
    exponents[INDEX[name]] = 1
    return {tuple(exponents): Q(1)}


def add(left: Polynomial, right: Polynomial) -> Polynomial:
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, Q(0)) + coefficient
    return clean(result)


def neg(poly: Polynomial) -> Polynomial:
    return {monomial: -coefficient for monomial, coefficient in poly.items()}


def sub(left: Polynomial, right: Polynomial) -> Polynomial:
    return add(left, neg(right))


def mul(left: Polynomial, right: Polynomial) -> Polynomial:
    result: Polynomial = {}
    for left_monomial, left_coefficient in left.items():
        for right_monomial, right_coefficient in right.items():
            monomial = tuple(
                left_exponent + right_exponent
                for left_exponent, right_exponent in zip(left_monomial, right_monomial)
            )
            result[monomial] = result.get(monomial, Q(0)) + left_coefficient * right_coefficient
    return clean(result)


def scale(value: int | Q, poly: Polynomial) -> Polynomial:
    return mul(constant(value), poly)


def linear_coefficient(poly: Polynomial, name: str) -> Q:
    return poly.get(next(iter(variable(name))), Q(0))


def evaluate(poly: Polynomial, values: dict[str, Q]) -> Q:
    total = Q(0)
    for monomial, coefficient in poly.items():
        term = coefficient
        for name, exponent in zip(VARIABLES, monomial):
            term *= values[name] ** exponent
        total += term
    return total


def show_q(value: Q) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def sample_values(
    D: Q,
    zero_scale: Q,
    s: int,
    b: int,
    p_trace_error: Q,
    trace_error: Q,
    frob_error: Q,
) -> dict[str, Q]:
    return {
        "D": D,
        "zeroScale": zero_scale,
        "s": Q(s),
        "b": Q(b),
        "pTraceErr": p_trace_error,
        "traceErr": trace_error,
        "frobErr": frob_error,
    }


D = variable("D")
N = variable("zeroScale")
s = variable("s")
b = variable("b")
e_p = variable("pTraceErr")
e_t = variable("traceErr")
e_f = variable("frobErr")

frob_upper = add(mul(D, N), e_f)
trace_lower = sub(N, e_t)
p_trace_cap = add(s, e_p)

substituted_prebound = add(
    sub(frob_upper, scale(4, trace_lower)),
    add(s, add(scale(2, p_trace_cap), scale(4, b))),
)
robust_target = add(
    add(s, mul(sub(D, constant(2)), N)),
    add(scale(2, e_p), add(scale(4, e_t), e_f)),
)
count_slack = scale(2, sub(add(s, scale(2, b)), N))

assert sub(substituted_prebound, robust_target) == count_slack
coefficient_vector = (
    linear_coefficient(robust_target, "pTraceErr"),
    linear_coefficient(robust_target, "traceErr"),
    linear_coefficient(robust_target, "frobErr"),
)
assert coefficient_vector == (Q(2), Q(4), Q(1))

print("Robust stability exact symbolic audit")
print("finite prebound substitution = PASS")
print("prebound - robust target = 2 * (s + 2*b - zeroScale)")
print("error coefficient vector (pTraceErr, traceErr, frobErr) = (2, 4, 1)")


samples = (
    sample_values(Q(7, 5), Q(12), 5, 3, Q(2, 7), Q(1, 11), Q(3, 13)),
    sample_values(Q(11, 8), Q(5), 0, 2, Q(1, 9), Q(2, 15), Q(4, 17)),
    sample_values(Q(3, 2), Q(13), 7, 3, Q(0), Q(0), Q(0)),
)

print("\nexact rational substitutions")
for index, values in enumerate(samples, start=1):
    prebound_value = evaluate(substituted_prebound, values)
    target_value = evaluate(robust_target, values)
    slack_value = evaluate(count_slack, values)
    assert prebound_value - target_value == slack_value
    assert values["s"] + 2 * values["b"] <= values["zeroScale"]
    assert slack_value <= 0
    print(
        f"sample {index}: prebound={show_q(prebound_value)}, "
        f"target={show_q(target_value)}, count_slack={show_q(slack_value)} = PASS"
    )


def sorted_trim(dimension: int, budget: int) -> tuple[set[int], set[int]]:
    retained = {budget + offset for offset in range(max(dimension - budget, 0))}
    removed = set(range(dimension)) - retained
    return retained, removed


print("\nfinite sorted-head cardinality and mass checks")
for dimension, budget in ((7, 3), (5, 9), (1, 0), (12, 4)):
    retained, removed = sorted_trim(dimension, budget)
    expected_retained = set(range(min(budget, dimension), dimension))
    assert retained == expected_retained
    assert len(retained) == max(dimension - budget, 0)
    assert len(removed) == min(dimension, budget)
    assert len(removed) <= budget
    removed_mass = Q(len(removed), dimension)
    declared_budget = Q(budget, dimension)
    assert removed_mass <= declared_budget
    print(
        f"d={dimension}, b={budget}: retained={len(retained)}, removed={len(removed)}, "
        f"mass={show_q(removed_mass)} <= {show_q(declared_budget)} = PASS"
    )


def positive_square(value: Q) -> Q:
    return max(value, Q(0)) ** 2


def spectral_residual(eigenvalues: Iterable[Q], budget: int) -> tuple[Q, Q]:
    spectrum = tuple(eigenvalues)
    dimension = len(spectrum)
    assert all(left >= right for left, right in zip(spectrum, spectrum[1:]))
    centered = tuple(value - 1 for value in spectrum)
    retained, removed = sorted_trim(dimension, budget)
    residual = sum(
        (Q(0) if index in removed else Q(1, dimension)) * positive_square(value)
        for index, value in enumerate(centered)
    )
    tail = sum(positive_square(centered[index]) for index in sorted(retained)) / dimension
    return residual, tail


print("\nexact spectral residual identities")
spectrum = (Q(5, 2), Q(7, 4), Q(1), Q(1, 2), Q(-1, 3))
for budget in (1, 2, 8):
    residual, normalized_tail = spectral_residual(spectrum, budget)
    assert residual == normalized_tail
    print(
        f"d=5, b={budget}: residual=tail/d={show_q(residual)} = PASS"
    )

print("\nall exact checks = PASS")
