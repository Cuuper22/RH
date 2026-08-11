#!/usr/bin/env python3
"""Exact finite calibration for SQ4 CRT and conductor stratification.

Only integer polynomial arithmetic and fractions.Fraction are used.  Roots
of unity are compared in Q[x]/Phi_q(x), never by floating point.  The Gauss
tests below use real quadratic characters; the general complex conjugation
phase is proved in Lean, not inferred from this finite calibration.
"""

from fractions import Fraction
from functools import lru_cache
from math import gcd, isqrt


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def moebius(n: int) -> int:
    value = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        value = -value
    return value


def trim(poly: list[Fraction]) -> list[Fraction]:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def exact_div(num: list[Fraction], den: list[Fraction]) -> list[Fraction]:
    num = trim(num[:])
    den = trim(den[:])
    out = [Fraction(0)] * max(1, len(num) - len(den) + 1)
    while len(num) >= len(den) and num != [0]:
        shift = len(num) - len(den)
        coeff = num[-1] / den[-1]
        out[shift] += coeff
        for i, c in enumerate(den):
            num[i + shift] -= coeff * c
        trim(num)
    assert num == [0]
    return trim(out)


@lru_cache(maxsize=None)
def cyclotomic(n: int) -> tuple[Fraction, ...]:
    poly = [Fraction(-1)] + [Fraction(0)] * (n - 1) + [Fraction(1)]
    for d in divisors(n):
        if d < n:
            poly = exact_div(poly, list(cyclotomic(d)))
    return tuple(poly)


def reduce_root_poly(poly: list[Fraction], q: int) -> tuple[Fraction, ...]:
    poly = trim(poly[:])
    phi = list(cyclotomic(q))
    while len(poly) >= len(phi):
        shift = len(poly) - len(phi)
        coeff = poly[-1] / phi[-1]
        for i, c in enumerate(phi):
            poly[i + shift] -= coeff * c
        trim(poly)
    return tuple(poly)


def primitive_quadratic(f: int, a: int) -> int:
    """Selected primitive real characters of conductors 1,3,4,5,8."""
    a %= f
    if f == 1:
        return 1
    if gcd(a, f) != 1:
        return 0
    if f == 3:
        return 1 if a == 1 else -1
    if f == 4:
        return 1 if a == 1 else -1
    if f == 5:
        return 1 if a in (1, 4) else -1
    if f == 8:
        return 1 if a in (1, 7) else -1
    raise ValueError(f"unsupported conductor {f}")


def direct_gauss_poly(f: int, m: int, t: int) -> list[Fraction]:
    q = f * m
    out = [Fraction(0)] * q
    for z in range(q):
        if gcd(z, q) == 1:
            out[(t * z) % q] += primitive_quadratic(f, z)
    return out


def primitive_tau_poly(f: int, m: int) -> list[Fraction]:
    """tau(chi*) in powers of zeta_(f*m), with zeta_f=zeta_(f*m)^m."""
    q = f * m
    out = [Fraction(0)] * q
    for a in range(f):
        out[(m * a) % q] += primitive_quadratic(f, a)
    return out


def conductor_formula_poly(f: int, m: int, t: int) -> list[Fraction]:
    q = f * m
    scalar = 0
    for s in divisors(gcd(m, t)):
        d = m // s
        if gcd(d, f) == 1:
            scalar += (
                moebius(d)
                * primitive_quadratic(f, d)
                * s
                * primitive_quadratic(f, t // s)
            )
    return [Fraction(scalar) * c for c in primitive_tau_poly(f, m)]


def is_squarefree(n: int) -> bool:
    return all(n % (p * p) for p in range(2, isqrt(n) + 1))


def check_conductor_formula() -> tuple[int, int]:
    identities = 0
    support_checks = 0
    for f in (1, 3, 4, 5, 8):
        for m in range(1, 13):
            q = f * m
            for t in range(0, 2 * q + 1):
                lhs = reduce_root_poly(direct_gauss_poly(f, m, t), q)
                rhs = reduce_root_poly(conductor_formula_poly(f, m, t), q)
                assert lhs == rhs, (f, m, t, lhs, rhs)
                identities += 1
                if any(lhs):
                    assert (q // gcd(t, q)) % f == 0
                    support_checks += 1
    return identities, support_checks


def check_shared_gcd_strata() -> int:
    checks = 0
    for u1 in range(1, 101):
        for u2 in range(1, 101):
            if not (is_squarefree(u1) and is_squarefree(u2)):
                continue
            g = gcd(u1, u2)
            a, b = u1 // g, u2 // g
            assert u1 == g * a and u2 == g * b
            assert gcd(g, a) == gcd(g, b) == gcd(a, b) == 1
            assert u1 * u2 == g * g * a * b
            checks += 1
    return checks


def check_exact_exponents() -> None:
    sq4_hb = Fraction(149, 100)
    completion = Fraction(43, 100)
    precompletion = Fraction(48, 25)
    assert precompletion - completion == sq4_hb
    assert Fraction(121, 50) - precompletion == Fraction(1, 2)


def main() -> None:
    identities, support = check_conductor_formula()
    strata = check_shared_gcd_strata()
    check_exact_exponents()

    assert moebius(2) == -1
    assert gcd(2, 2) == 2
    assert 2 % 4 != 0 and (2 * 2) % 4 == 0
    assert all((x * x) % 2 == x for x in range(2))

    print("A1 SQ4 CRT/conductor exact finite calibration")
    print(f"imprimitive Gauss identities checked = {identities}")
    print(f"nonzero conductor-support checks = {support}")
    print(f"squarefree shared-gcd strata checked = {strata}")
    print("smallest shared slot = u1=u2=2, mu(2)=-1, gcd=2")
    print("ring obstruction = 2 mod 4 is nonzero square-zero")
    print("real-character conductor calibration = PASS")
    print("general complex phase = Lean theorem (outside Python scope)")
    print("48/25 - 43/100 = 149/100")
    print("121/50 - 48/25 = 1/2")


if __name__ == "__main__":
    main()
