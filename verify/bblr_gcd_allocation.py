#!/usr/bin/env python3
"""Independent integer check for the BBLR gcd-allocation regression."""

from math import gcd


def ordered_factor_pairs(n: int) -> list[tuple[int, int]]:
    return [(a, n // a) for a in range(1, n + 1) if n % a == 0]


def main() -> None:
    d = 2
    p = 2
    raw = [
        (d1, d2, a, m)
        for d1, d2 in ordered_factor_pairs(d)
        for a, m in ordered_factor_pairs(p)
    ]
    canonical = [entry for entry in raw if gcd(entry[2], entry[1]) == 1]
    merged_raw = [(d1 * a, d2 * m) for d1, d2, a, m in raw]
    merged_canonical = [(d1 * a, d2 * m) for d1, d2, a, m in canonical]
    original = ordered_factor_pairs(d * p)

    assert len(raw) == 4
    assert len(canonical) == 3
    assert sorted(merged_canonical) == sorted(original)
    assert len(set(merged_raw)) == 3

    print(f"d={d} p={p}")
    print(f"raw_count={len(raw)}")
    print(f"canonical_count={len(canonical)}")
    print(f"original_count={len(original)}")
    print(f"raw_merged={merged_raw}")
    print(f"canonical_merged={merged_canonical}")
    print("status=PASS")


if __name__ == "__main__":
    main()
