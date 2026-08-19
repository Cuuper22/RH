"""Deterministic Sobol evaluator for the strict-support sixth-moment block.

The block model is Y = (r-1) + mu X_r.  For each even number of X edges,
the trace-cycle contraction is enumerated over all Gaussian difference-mode
pairings.  The script is intentionally small and specialized to degrees <= 6.
"""

from __future__ import annotations

import itertools
import math
from functools import lru_cache

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.stats import qmc


SIGMA = 1.9999
MU = 0.3333
B = (2.0 - SIGMA) / 2.0
A_EULER = 0.8312126609842
B_EULER = -0.3551542095561
M_EULER = 1.5939724172081


def cap(x: np.ndarray | float) -> np.ndarray:
    """Accepted normalized Euler cap W(t)=V_sigma(mu*t)."""
    z = np.abs(np.asarray(x, dtype=float))
    outer = SIGMA / M_EULER * (
        A_EULER * np.cos(MU * z - 0.5)
        + B_EULER * np.sin(math.sqrt(3.0) * (MU * z - 0.5))
    )
    inner = SIGMA / M_EULER * np.cos(math.sqrt(2.0) * MU * z)
    return np.where(MU * z <= B, inner, outer)


def cap_scalar(x: float) -> float:
    return float(cap(x))


def pairings(items: tuple[int, ...]):
    if not items:
        yield ()
        return
    first = items[0]
    for j in range(1, len(items)):
        second = items[j]
        for rest in pairings(items[1:j] + items[j + 1 :]):
            yield ((first, second),) + rest


@lru_cache(None)
def parameterization(m: int, pairing: tuple[tuple[int, int], ...]) -> np.ndarray:
    if m == 2:
        return np.eye(2)
    rows = []
    for i, j in pairing[:-1]:
        row = np.zeros(m)
        row[i] += 1
        row[(i + 1) % m] -= 1
        row[j] += 1
        row[(j + 1) % m] -= 1
        rows.append(row)
    constraint = np.asarray(rows)
    rank = m // 2 - 1
    for pivots in itertools.combinations(range(m), rank):
        pivot = constraint[:, pivots]
        if abs(round(np.linalg.det(pivot))) != 1:
            continue
        free = [j for j in range(m) if j not in pivots]
        transform = np.zeros((m, len(free)))
        transform[free, np.arange(len(free))] = 1
        transform[list(pivots)] = -np.linalg.solve(pivot, constraint[:, free])
        return transform
    raise RuntimeError(f"no unimodular parameterization for {pairing}")


@lru_cache(None)
def compositions(k: int, m: int) -> tuple[tuple[int, ...], ...]:
    """Q-run exponents at the m cyclic X vertices, with word multiplicity."""
    result = []
    for word in itertools.product((0, 1), repeat=k):
        if sum(word) != m:
            continue
        positions = [j for j, value in enumerate(word) if value]
        exponents = [0] * m
        for j, position in enumerate(positions):
            following = positions[(j + 1) % m]
            exponents[(j + 1) % m] = (following - position - 1) % k
        result.append(tuple(exponents))
    return tuple(result)


def outer_profile(gap: float):
    """Return r=W on |t|>=gap/2 and its centered q."""
    def evaluate(z: np.ndarray):
        r = np.where(np.abs(z) >= gap / 2.0, cap(z), 0.0)
        return r, r - 1.0
    return evaluate


def mass_gap() -> float:
    return brentq(
        lambda gap: 2.0 * quad(cap_scalar, gap / 2.0, 0.5, epsabs=2e-13)[0] - 1.0,
        0.18,
        0.22,
    )


def moments(gap: float, seed: int = 10, sobol_power: int = 19) -> np.ndarray:
    profile = outer_profile(gap)
    result = np.zeros(7)
    for k in range(2, 7):
        result[k] = gap * ((-1) ** k) + 2.0 * quad(
            lambda x: (cap_scalar(x) - 1.0) ** k,
            gap / 2.0,
            0.5,
            epsabs=3e-13,
        )[0]

    for m in (2, 4, 6):
        for pairing_index, pairing in enumerate(pairings(tuple(range(m)))):
            transform = parameterization(m, pairing)
            sampler = qmc.Sobol(
                transform.shape[1], scramble=True, seed=seed + 100 * m + pairing_index
            )
            free = sampler.random_base2(sobol_power) - 0.5
            vertices = free @ transform.T
            admissible = np.max(np.abs(vertices), axis=1) <= 0.5
            r, q = profile(vertices)
            base = admissible.astype(float) * np.prod(r, axis=1)
            for i, _ in pairing:
                base *= np.abs(vertices[:, i] - vertices[:, (i + 1) % m])
            for k in range(m, 7):
                word_sum = np.zeros(len(vertices))
                for exponents in compositions(k, m):
                    term = np.ones(len(vertices))
                    for j, exponent in enumerate(exponents):
                        if exponent:
                            term *= q[:, j] ** exponent
                    word_sum += term
                result[k] += MU**m * np.mean(base * word_sum)
    return result


if __name__ == "__main__":
    gap = mass_gap()
    print(f"mass gap = {gap:.15f}")
    for scramble in (10, 20, 30):
        value = moments(gap, seed=scramble)
        print(scramble, " ".join(f"{x:.12f}" for x in value[2:]))
