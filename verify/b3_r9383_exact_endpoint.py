#!/usr/bin/env python3
"""Exact enclosure certificate for the flat R-9383 endpoint branch.

The older certificate audit used ``mpmath`` to observe that the frozen
15-place decimal was rounded upward.  This verifier proves the direction.
It uses only Python's integer arithmetic and ``fractions.Fraction``:

* square roots are enclosed by integer-square-root inequalities;
* sine and cosine are enclosed by rational Taylor polynomials with a
  rational Lagrange remainder;
* the fourth-moment equation is reduced by an exact bivariate-polynomial
  identity and its relevant root is enclosed by nested rational square-root
  intervals; and
* interval automatic differentiation proves that the fixed residual is
  strictly increasing throughout the isolating interval.

The scope is the exact flat three-atom contact branch in run file 17,
equations (26)--(32), at ``mu = 1/2`` and the Euler saturated cost at
``sigma = 2``.  It does not prove the analytic inputs or the block
construction on which that source-only certificate depends.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from math import factorial, isqrt


def as_q(value: int | Q) -> Q:
    return value if isinstance(value, Q) else Q(value)


@dataclass(frozen=True)
class Interval:
    """Closed rational interval with outward operations."""

    lo: Q
    hi: Q

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @staticmethod
    def point(value: int | Q) -> "Interval":
        rational = as_q(value)
        return Interval(rational, rational)

    @staticmethod
    def coerce(value: int | Q | "Interval") -> "Interval":
        return value if isinstance(value, Interval) else Interval.point(value)

    def __add__(self, other: int | Q | "Interval") -> "Interval":
        rhs = Interval.coerce(other)
        return Interval(self.lo + rhs.lo, self.hi + rhs.hi)

    __radd__ = __add__

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: int | Q | "Interval") -> "Interval":
        return self + (-Interval.coerce(other))

    def __rsub__(self, other: int | Q | "Interval") -> "Interval":
        return Interval.coerce(other) - self

    def __mul__(self, other: int | Q | "Interval") -> "Interval":
        rhs = Interval.coerce(other)
        products = (
            self.lo * rhs.lo,
            self.lo * rhs.hi,
            self.hi * rhs.lo,
            self.hi * rhs.hi,
        )
        return Interval(min(products), max(products))

    __rmul__ = __mul__

    def reciprocal(self) -> "Interval":
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError("interval contains zero")
        return Interval(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other: int | Q | "Interval") -> "Interval":
        return self * Interval.coerce(other).reciprocal()

    def __rtruediv__(self, other: int | Q | "Interval") -> "Interval":
        return Interval.coerce(other) / self

    def __pow__(self, exponent: int) -> "Interval":
        if exponent < 0:
            return (self ** (-exponent)).reciprocal()
        if exponent == 0:
            return Interval.point(1)
        if self.lo >= 0:
            return Interval(self.lo**exponent, self.hi**exponent)
        if self.hi <= 0:
            if exponent % 2:
                return Interval(self.lo**exponent, self.hi**exponent)
            return Interval(self.hi**exponent, self.lo**exponent)
        if exponent % 2:
            return Interval(self.lo**exponent, self.hi**exponent)
        return Interval(0, max((-self.lo) ** exponent, self.hi**exponent))


def floor_q(value: Q) -> int:
    return value.numerator // value.denominator


def ceil_q(value: Q) -> int:
    return -floor_q(-value)


def sqrt_rational_interval(value: Q, decimal_places: int = 150) -> Interval:
    """Enclose sqrt(value); the two endpoint inequalities are exact."""
    if value < 0:
        raise ValueError("negative square root")
    scale = 10**decimal_places
    scaled_floor = value.numerator * scale * scale // value.denominator
    lower_integer = isqrt(scaled_floor)
    while Q(lower_integer * lower_integer, scale * scale) > value:
        lower_integer -= 1
    while Q((lower_integer + 1) ** 2, scale * scale) <= value:
        lower_integer += 1
    lower = Q(lower_integer, scale)
    if lower * lower == value:
        return Interval(lower, lower)
    upper = Q(lower_integer + 1, scale)
    assert lower * lower < value < upper * upper
    return Interval(lower, upper)


def sqrt_interval(value: Interval, decimal_places: int = 150) -> Interval:
    if value.lo < 0:
        raise ValueError("interval square root has negative lower endpoint")
    lower = sqrt_rational_interval(value.lo, decimal_places).lo
    upper = sqrt_rational_interval(value.hi, decimal_places).hi
    result = Interval(lower, upper)
    assert result.lo * result.lo <= value.lo
    assert result.hi * result.hi >= value.hi
    return result


def taylor_sin(value: Interval, terms: int = 72) -> Interval:
    """Rational Taylor enclosure; valid here because |value| < 1."""
    assert -1 < value.lo <= value.hi < 1
    total = Interval.point(0)
    for index in range(terms):
        term = value ** (2 * index + 1) / factorial(2 * index + 1)
        total = total + (term if index % 2 == 0 else -term)
    degree = 2 * terms - 1
    radius = max(abs(value.lo), abs(value.hi)) ** (degree + 1) / factorial(degree + 1)
    return total + Interval(-radius, radius)


def taylor_cos(value: Interval, terms: int = 72) -> Interval:
    """Rational Taylor enclosure; valid here because |value| < 1."""
    assert -1 < value.lo <= value.hi < 1
    total = Interval.point(0)
    for index in range(terms):
        term = value ** (2 * index) / factorial(2 * index)
        total = total + (term if index % 2 == 0 else -term)
    degree = 2 * terms - 2
    radius = max(abs(value.lo), abs(value.hi)) ** (degree + 1) / factorial(degree + 1)
    return total + Interval(-radius, radius)


def euler_cost_interval() -> Interval:
    """Enclose D_2 = 2/3 + cot(1/2)/4 - tan(sqrt(3)/2)/(12sqrt(3))."""
    root_three = sqrt_interval(Interval.point(3))
    half = Interval.point(Q(1, 2))
    root_three_half = root_three / 2
    sin_half = taylor_sin(half)
    cos_half = taylor_cos(half)
    sin_three_half = taylor_sin(root_three_half)
    cos_three_half = taylor_cos(root_three_half)
    assert sin_half.lo > 0 and cos_three_half.lo > 0 and root_three.lo > 0
    cot_half = cos_half / sin_half
    tan_three_half = sin_three_half / cos_three_half
    return Q(2, 3) + cot_half / 4 - tan_three_half / (12 * root_three)


# A minimal exact bivariate polynomial checker.  Exponents are (q_degree,
# t_degree); it prevents the key fourth-moment reduction from being accepted
# merely because it agrees numerically at the final root.
Poly = dict[tuple[int, int], Q]


def poly_clean(poly: Poly) -> Poly:
    return {monomial: coefficient for monomial, coefficient in poly.items() if coefficient}


def poly_add(left: Poly, right: Poly) -> Poly:
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, Q(0)) + coefficient
    return poly_clean(result)


def poly_neg(poly: Poly) -> Poly:
    return {monomial: -coefficient for monomial, coefficient in poly.items()}


def poly_sub(left: Poly, right: Poly) -> Poly:
    return poly_add(left, poly_neg(right))


def poly_mul(left: Poly, right: Poly) -> Poly:
    result: Poly = {}
    for (q_left, t_left), left_coefficient in left.items():
        for (q_right, t_right), right_coefficient in right.items():
            monomial = (q_left + q_right, t_left + t_right)
            result[monomial] = result.get(monomial, Q(0)) + left_coefficient * right_coefficient
    return poly_clean(result)


def poly_pow(poly: Poly, exponent: int) -> Poly:
    result: Poly = {(0, 0): Q(1)}
    for _ in range(exponent):
        result = poly_mul(result, poly)
    return result


def poly_scale(poly: Poly, scalar: Q) -> Poly:
    return poly_clean({monomial: scalar * coefficient for monomial, coefficient in poly.items()})


def verify_moment_identity() -> None:
    one: Poly = {(0, 0): Q(1)}
    q: Poly = {(1, 0): Q(1)}
    t: Poly = {(0, 1): Q(1)}
    qt = poly_mul(q, t)
    a_mass = poly_sub(one, q)
    first = poly_neg(qt)
    second = poly_sub({(0, 0): Q(1, 3)}, poly_mul(q, poly_pow(t, 2)))
    third = poly_neg(poly_mul(q, poly_pow(t, 3)))
    fourth = poly_sub({(0, 0): Q(4, 15)}, poly_mul(q, poly_pow(t, 4)))
    hankel = poly_sub(poly_mul(a_mass, second), poly_pow(first, 2))
    residual = poly_sub(
        poly_mul(fourth, hankel),
        poly_add(
            poly_sub(poly_mul(a_mass, poly_pow(third, 2)),
                     poly_scale(poly_mul(poly_mul(first, second), third), Q(2))),
            poly_pow(second, 3),
        ),
    )
    expected: Poly = {
        (0, 0): Q(7, 135),
        (1, 0): -Q(4, 45),
        (1, 2): Q(1, 15),
        (1, 4): -Q(1, 3),
    }
    assert residual == expected


def solve_linear(matrix: list[list[Q]], rhs: list[Q]) -> tuple[Q, ...]:
    """Exact Gauss--Jordan elimination over the rationals."""
    augmented = [list(row) + [value] for row, value in zip(matrix, rhs)]
    size = len(augmented)
    for column in range(size):
        pivot = next(row for row in range(column, size) if augmented[row][column])
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        pivot_value = augmented[column][column]
        augmented[column] = [value / pivot_value for value in augmented[column]]
        for row in range(size):
            if row != column and augmented[row][column]:
                multiplier = augmented[row][column]
                augmented[row] = [
                    value - multiplier * pivot_entry
                    for value, pivot_entry in zip(augmented[row], augmented[column])
                ]
    return tuple(row[-1] for row in augmented)


def rational_law_witness(cost: Interval, frozen: Q) -> tuple[tuple[Q, ...], Q, Q, Q]:
    """A second, wholly rational, non-sharp comparison at the frozen target.

    The five close rational atoms make the five moment equations square.
    Their exact Vandermonde solution is positive.  Removing the fifth atom
    uses less than q=1-frozen mass; the remaining scaled positive-square
    tail is strictly below ``frozen + D_lower - 2``.
    """
    atoms = (
        -Q(37364054801253, 50000000000000),
        -Q(747281096025059, 1000000000000000),
        Q(282369757316461, 1000000000000000),
        Q(141184878658231, 500000000000000),
        Q(1266887617549373, 1000000000000000),
    )
    matrix = [[atom**degree for atom in atoms] for degree in range(5)]
    target_moments = [Q(1), Q(0), Q(1, 3), Q(0), Q(4, 15)]
    weights = solve_linear(matrix, target_moments)
    for degree, target in enumerate(target_moments):
        assert sum((weight * atom**degree for weight, atom in zip(weights, atoms)), Q(0)) == target
    assert all(weight > 0 for weight in weights)

    trim_budget = 1 - frozen
    trim_mass = weights[4]
    assert trim_mass <= trim_budget
    scaled_tail = (weights[2] * atoms[2] ** 2 + weights[3] * atoms[3] ** 2) / 8

    # This terminating decimal is strictly below the Taylor lower endpoint.
    cost_lower = Q(10677173760647041522687642216851958360927, 10**40)
    assert cost_lower < cost.lo
    comparison_level = frozen + cost_lower - 2
    assert scaled_tail < comparison_level
    return weights, trim_budget - trim_mass, scaled_tail, comparison_level - scaled_tail


@dataclass(frozen=True)
class DualInterval:
    value: Interval
    derivative: Interval

    @staticmethod
    def constant(value: int | Q | Interval) -> "DualInterval":
        return DualInterval(Interval.coerce(value), Interval.point(0))

    @staticmethod
    def coerce(value: int | Q | Interval | "DualInterval") -> "DualInterval":
        return value if isinstance(value, DualInterval) else DualInterval.constant(value)

    def __add__(self, other: int | Q | Interval | "DualInterval") -> "DualInterval":
        rhs = DualInterval.coerce(other)
        return DualInterval(self.value + rhs.value, self.derivative + rhs.derivative)

    __radd__ = __add__

    def __neg__(self) -> "DualInterval":
        return DualInterval(-self.value, -self.derivative)

    def __sub__(self, other: int | Q | Interval | "DualInterval") -> "DualInterval":
        return self + (-DualInterval.coerce(other))

    def __rsub__(self, other: int | Q | Interval | "DualInterval") -> "DualInterval":
        return DualInterval.coerce(other) - self

    def __mul__(self, other: int | Q | Interval | "DualInterval") -> "DualInterval":
        rhs = DualInterval.coerce(other)
        return DualInterval(
            self.value * rhs.value,
            self.derivative * rhs.value + self.value * rhs.derivative,
        )

    __rmul__ = __mul__

    def reciprocal(self) -> "DualInterval":
        return DualInterval(self.value.reciprocal(), -self.derivative / (self.value**2))

    def __truediv__(self, other: int | Q | Interval | "DualInterval") -> "DualInterval":
        return self * DualInterval.coerce(other).reciprocal()

    def __rtruediv__(self, other: int | Q | Interval | "DualInterval") -> "DualInterval":
        return DualInterval.coerce(other) / self

    def __pow__(self, exponent: int) -> "DualInterval":
        if exponent == 0:
            return DualInterval.constant(1)
        if exponent < 0:
            return (self ** (-exponent)).reciprocal()
        return DualInterval(
            self.value**exponent,
            exponent * (self.value ** (exponent - 1)) * self.derivative,
        )


def dual_sqrt(value: DualInterval) -> DualInterval:
    root = sqrt_interval(value.value)
    assert root.lo > 0
    return DualInterval(root, value.derivative / (2 * root))


@dataclass(frozen=True)
class BranchData:
    q: DualInterval
    t: DualInterval
    negative_atom: DualInterval
    positive_atom: DualInterval
    negative_mass: DualInterval
    positive_mass: DualInterval
    epsilon: DualInterval
    residual: DualInterval


def three_atom_branch(q: DualInterval, cost: Interval) -> BranchData:
    # The plus root is the high-atom branch t > 1 used in file 17.
    t_squared = (9 + dual_sqrt(1260 / q - 2079)) / 90
    t = dual_sqrt(t_squared)

    mass = 1 - q
    first = -q * t
    second = Q(1, 3) - q * t**2
    third = -q * t**3
    hankel = mass * second - first**2
    assert hankel.value.lo > 0
    atom_sum = (mass * third - first * second) / hankel
    atom_product = (first * third - second**2) / hankel
    discriminant = atom_sum**2 - 4 * atom_product
    assert discriminant.value.lo > 0
    root_discriminant = dual_sqrt(discriminant)
    negative_atom = (atom_sum - root_discriminant) / 2
    positive_atom = (atom_sum + root_discriminant) / 2
    atom_gap = positive_atom - negative_atom
    assert atom_gap.value.lo > 0
    negative_mass = (positive_atom * mass + q * t) / atom_gap
    positive_mass = mass - negative_mass
    epsilon = positive_mass * positive_atom**2 / 8
    residual = q + epsilon - (cost - 1)

    assert t.value.lo > 1
    assert negative_atom.value.hi < 0 < positive_atom.value.lo
    assert positive_atom.value.hi < t.value.lo
    assert q.value.lo > 0
    assert negative_mass.value.lo > 0 and positive_mass.value.lo > 0
    return BranchData(
        q=q,
        t=t,
        negative_atom=negative_atom,
        positive_atom=positive_atom,
        negative_mass=negative_mass,
        positive_mass=positive_mass,
        epsilon=epsilon,
        residual=residual,
    )


def decimal_bound(value: Q, places: int, upper: bool) -> str:
    scale = 10**places
    integer = ceil_q(value * scale) if upper else floor_q(value * scale)
    sign = "-" if integer < 0 else ""
    digits = str(abs(integer)).rjust(places + 1, "0")
    return f"{sign}{digits[:-places]}.{digits[-places:]}" if places else f"{sign}{digits}"


def decimal_interval(value: Interval, places: int) -> str:
    return f"[{decimal_bound(value.lo, places, False)}, {decimal_bound(value.hi, places, True)}]"


def exact_decimal(value: Q, places: int) -> str:
    scale = 10**places
    scaled = value * scale
    assert scaled.denominator == 1
    integer = scaled.numerator
    digits = str(abs(integer)).rjust(places + 1, "0")
    sign = "-" if integer < 0 else ""
    return f"{sign}{digits[:-places]}.{digits[-places:]}"


def main() -> None:
    verify_moment_identity()
    cost = euler_cost_interval()

    q_lower = Q(616866729490511152, 10**19)
    q_upper = Q(616866729490511153, 10**19)
    frozen = Q(938313327050949, 10**15)
    q_frozen = 1 - frozen
    assert q_frozen < q_lower < q_upper

    lower_data = three_atom_branch(
        DualInterval(Interval.point(q_lower), Interval.point(1)), cost
    )
    upper_data = three_atom_branch(
        DualInterval(Interval.point(q_upper), Interval.point(1)), cost
    )
    assert lower_data.residual.value.hi < 0
    assert upper_data.residual.value.lo > 0

    box_data = three_atom_branch(
        DualInterval(Interval(q_lower, q_upper), Interval.point(1)), cost
    )
    assert box_data.residual.derivative.lo > 0

    endpoint = Interval(1 - q_upper, 1 - q_lower)
    assert endpoint.hi < frozen
    gap = frozen - endpoint.hi
    rational_weights, trim_slack, rational_tail, rational_margin = rational_law_witness(cost, frozen)

    print("R-9383 EXACT FLAT THREE-ATOM ENDPOINT CERTIFICATE")
    print("arithmetic backend = Fraction/integer only (no floating-point decisions)")
    print("fourth-moment polynomial identity = PASS")
    print("135 F(q,t) = 7 - 12q + 9q t^2 - 45q t^4")
    print("selected root: t^2 = (9 + sqrt(1260/q - 2079))/90")
    print(f"Euler D_2 enclosure = {decimal_interval(cost, 70)}")
    print(f"q isolating interval = [{exact_decimal(q_lower, 19)}, {exact_decimal(q_upper, 19)}]")
    print(f"residual at q_lower = {decimal_interval(lower_data.residual.value, 45)}")
    print(f"residual at q_upper = {decimal_interval(upper_data.residual.value, 45)}")
    print(f"residual derivative on box = {decimal_interval(box_data.residual.derivative, 40)}")
    print("endpoint existence = PASS (opposite endpoint signs and continuity)")
    print("endpoint uniqueness in isolating interval = PASS (strictly positive derivative)")
    print(f"high atom box = {decimal_interval(box_data.t.value, 40)}")
    print(f"negative atom box = {decimal_interval(box_data.negative_atom.value, 40)}")
    print(f"positive atom box = {decimal_interval(box_data.positive_atom.value, 40)}")
    print(f"negative mass box = {decimal_interval(box_data.negative_mass.value, 40)}")
    print(f"positive mass box = {decimal_interval(box_data.positive_mass.value, 40)}")
    print("branch admissibility = PASS (q,u,v>0; a<0<c<t; moment identity exact)")
    print(f"endpoint = 1-q in {decimal_interval(endpoint, 19)}")
    print(f"frozen target = {exact_decimal(frozen, 15)}")
    print(f"strict target gap >= {exact_decimal(gap, 19)}")
    print("independent rational five-atom comparison = PASS")
    print(f"rational-law minimum weight > 0 = {decimal_bound(min(rational_weights), 30, False)}")
    print(f"rational-law trim slack = {decimal_bound(trim_slack, 35, False)}")
    print(f"rational-law scaled tail = {decimal_bound(rational_tail, 40, True)}")
    print(f"rational-law strict comparison margin = {decimal_bound(rational_margin, 40, False)}")
    print("frozen R-9383 claim from this flat endpoint branch = FAIL (strict exact enclosure)")


if __name__ == "__main__":
    main()
