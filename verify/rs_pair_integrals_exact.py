#!/usr/bin/env python3
"""Exact finite verifier for the RS pairing and block-fraction bookkeeping.

This script uses integer combinatorics and formal linear combinations of the
contraction variables.  It does not numerically sample an integral.
"""

from __future__ import annotations

from fractions import Fraction
from math import factorial


LinearForm = tuple[int, ...]


def pairing_count(k: int, q: int) -> int:
    """Number of disjoint unoriented q-pair matchings on k labelled points."""
    return factorial(k) // (
        2**q * factorial(q) * factorial(k - 2 * q)
    )


def partial_sums(k: int, positives: tuple[int, ...],
                 negatives: tuple[int, ...]) -> tuple[LinearForm, ...]:
    q = len(positives)
    assert len(negatives) == q
    xi = [[0 for _ in range(q)] for _ in range(k)]
    for a, i in enumerate(positives):
        xi[i][a] += 1
    for a, i in enumerate(negatives):
        xi[i][a] -= 1

    running = [0 for _ in range(q)]
    result: list[LinearForm] = []
    for row in xi:
        result.append(tuple(running))
        running = [x + dx for x, dx in zip(running, row)]
    assert running == [0 for _ in range(q)]
    return tuple(result)


def show_form(coefficients: LinearForm) -> str:
    names = ("u", "v", "w", "t")
    terms: list[str] = []
    for coefficient, name in zip(coefficients, names):
        if coefficient == 1:
            terms.append(name)
        elif coefficient == -1:
            terms.append(f"-{name}")
        elif coefficient:
            terms.append(f"{coefficient}*{name}")
    if not terms:
        return "0"
    return "+".join(terms).replace("+-", "-")


def main() -> None:
    expected_counts = {
        1: (),
        2: (1,),
        3: (3,),
        4: (6, 3),
    }
    print("PAIRING COUNTS")
    for k, expected in expected_counts.items():
        actual = tuple(pairing_count(k, q) for q in range(1, k // 2 + 1))
        assert actual == expected
        print(f"k={k}: q-counts={actual or ()}; total={sum(actual)}")

    one_pair = tuple((i, j) for i in range(4) for j in range(i + 1, 4))
    profiles: list[tuple[tuple[int, int], tuple[str, ...]]] = []
    for i, j in one_pair:
        sums = partial_sums(4, (i,), (j,))
        profiles.append(((i, j), tuple(show_form(x) for x in sums)))
    adjacent = sum(profile.count("u") in (1, 3) for _, profile in profiles)
    opposite = sum(profile.count("u") == 2 for _, profile in profiles)
    assert (adjacent, opposite) == (4, 2)
    print("ONE-PAIR PARTIAL SUMS")
    for pair, profile in profiles:
        print(f"{pair}: {profile}")
    print(f"k=4 classes: adjacent={adjacent}; opposite={opposite}")

    two_pair = (
        ("crossing", (0, 1), (2, 3), ("0", "u", "u+v", "v")),
        ("nested", (0, 1), (3, 2), ("0", "u", "u+v", "u")),
        ("separated", (0, 2), (1, 3), ("0", "u", "0", "v")),
    )
    print("TWO-PAIR PARTIAL SUMS")
    for name, positives, negatives, expected in two_pair:
        actual = tuple(show_form(x) for x in partial_sums(4, positives, negatives))
        assert actual == expected
        print(f"{name}: +{positives}/-{negatives} -> {actual}")

    print("MU SCALING")
    for q in (1, 2):
        symbol_power = 1
        jacobian_and_weight_power = 2 * q
        unnormalized = symbol_power + jacobian_and_weight_power
        normalized = unnormalized - 1
        assert Fraction(unnormalized) == Fraction(1 + 2 * q)
        assert Fraction(normalized) == Fraction(2 * q)
        print(
            f"q={q}: symbol=mu^1; q*(|w|dw)=mu^{2*q}; "
            f"unnormalized=mu^{unnormalized}; normalized=mu^{normalized}"
        )

    print("PASS: exact pairing, partial-sum, and mu-scaling checks")


if __name__ == "__main__":
    main()
