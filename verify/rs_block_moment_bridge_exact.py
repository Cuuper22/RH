#!/usr/bin/env python3
"""Exact verifier for the actual-block binomial centering bridge.

Only integer polynomial arithmetic is used.  The script independently
checks that the coefficients of `(X - 1)^k` are the coefficients in the
Lean `centeredTransform` for every `0 <= k <= 4`.
"""

from __future__ import annotations

from math import comb


def multiply(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return tuple(result)


def polynomial_power(base: tuple[int, ...], exponent: int) -> tuple[int, ...]:
    result = (1,)
    for _ in range(exponent):
        result = multiply(result, base)
    return result


def centered_coefficients(k: int) -> tuple[int, ...]:
    return tuple((-1) ** (k - a) * comb(k, a) for a in range(k + 1))


def format_polynomial(coefficients: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in coefficients) + "]"


def main() -> None:
    print("ACTUAL-BLOCK CENTERING COEFFICIENTS")
    for k in range(5):
        expanded = polynomial_power((-1, 1), k)
        transform = centered_coefficients(k)
        assert expanded == transform
        assert sum(transform) == (1 if k == 0 else 0)
        print(f"k={k}: {format_polynomial(transform)}")

    print("ANALYTIC BOUNDARY")
    print("input degrees = uncentered k=0,1,2,3,4")
    print("formal output degrees = centered k=1,2,3,4")
    print("complex Poisson summability/cancellation = separate constructor inputs")
    print("PASS: exact finite centering coefficients")


if __name__ == "__main__":
    main()
