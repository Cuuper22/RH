#!/usr/bin/env python3
"""Independent audit of the withdrawn density-one source claim.

Run with mpmath 1.3.0 or later.  The exact endpoint calculation uses only
``fractions.Fraction``.  The numerical calculation reconstructs, rather than
hard-codes, the Euler cap and outer-gap profile stated in
``docs/run/100/certificate100_cycle4_cubic_96p518798.md``.
"""

from fractions import Fraction

import mpmath as mp


def exact_endpoint_audit() -> dict[str, Fraction]:
    """Return exact consequences of the source's own endpoint premises."""
    mu = Fraction(333333, 500000)
    delta = Fraction(3385873, 50000000)  # 1.06771746 - 1
    claimed_m2 = Fraction(18717, 50000)

    # At s/N = 1, epsilon = delta and b = 0.  Applying the two quadratic
    # trace scores displayed in FINAL_100_RESULT.md gives these M2 ceilings.
    cap_c_7_over_20 = (49 + 729 * delta / mu) / 329
    cap_c_3_over_8 = (9 + 121 * delta / mu) / 57

    return {
        "mu": mu,
        "delta": delta,
        "claimed_m2": claimed_m2,
        "cap_c_7_over_20": cap_c_7_over_20,
        "gap_c_7_over_20": claimed_m2 - cap_c_7_over_20,
        "score_gap_c_7_over_20": mu * (-49 + 329 * claimed_m2) / 729 - delta,
        "cap_c_3_over_8": cap_c_3_over_8,
        "gap_c_3_over_8": claimed_m2 - cap_c_3_over_8,
        "score_gap_c_3_over_8": mu * (-9 + 57 * claimed_m2) / 121 - delta,
    }


def euler_cap(sigma: mp.mpf):
    """Reconstruct V_sigma and its matching constants from the source."""
    half = mp.mpf("0.5")
    b = (2 - sigma) / 2
    d = b - half
    matrix = mp.matrix(
        [
            [mp.cos(d), mp.sin(mp.sqrt(3) * d)],
            [-mp.sin(d), mp.sqrt(3) * mp.cos(mp.sqrt(3) * d)],
        ]
    )
    target = mp.matrix(
        [mp.cos(mp.sqrt(2) * b), -mp.sqrt(2) * mp.sin(mp.sqrt(2) * b)]
    )
    a_const, b_const = mp.lu_solve(matrix, target)

    def u(x: mp.mpf) -> mp.mpf:
        x = abs(x)
        if x <= b:
            return mp.cos(mp.sqrt(2) * x)
        return a_const * mp.cos(x - half) + b_const * mp.sin(
            mp.sqrt(3) * (x - half)
        )

    normalization = 2 * (
        mp.quad(u, [0, b]) + mp.quad(u, [b, sigma / 2])
    )

    def v(x: mp.mpf) -> mp.mpf:
        return sigma * u(x) / normalization

    return a_const, b_const, normalization, v


def written_cone_profile(dps: int) -> dict[str, mp.mpf]:
    """Evaluate the explicit profile under the pointwise cone as written."""
    mp.mp.dps = dps
    sigma = mp.mpf(19999) / 10000
    mu = mp.mpf(333333) / 500000
    half = mp.mpf("0.5")
    a_const, b_const, normalization, v = euler_cap(sigma)

    def w(t: mp.mpf) -> mp.mpf:
        return v(mu * t)

    def mass(gap: mp.mpf) -> mp.mpf:
        return 2 * mp.quad(w, [gap / 2, half])

    gap = mp.findroot(lambda value: mass(value) - 1, (mp.mpf("0.17"), mp.mpf("0.18")))
    q_squared = gap + 2 * mp.quad(
        lambda t: (w(t) - 1) ** 2, [gap / 2, half]
    )

    # For the symmetric probability density r, F(t)=1/2+E(t) on the
    # positive outer interval.  E|X-Y| = 2 int F(1-F), reduced by symmetry.
    def positive_excess(t: mp.mpf) -> mp.mpf:
        return mp.quad(w, [gap / 2, t])

    absolute_distance = 4 * mp.quad(
        lambda t: mp.mpf("0.25") - positive_excess(t) ** 2,
        [gap / 2, half],
    ) + gap / 2
    m2 = q_squared + mu**2 * absolute_distance

    return {
        "A": a_const,
        "B": b_const,
        "normalization": normalization,
        "total_cap_mass": 2 * mp.quad(w, [0, half]),
        "gap": gap,
        "profile_mass": mass(gap),
        "q_squared": q_squared,
        "absolute_distance": absolute_distance,
        "m2": m2,
    }


def decimal(value: Fraction, digits: int = 18) -> str:
    mp.mp.dps = digits + 10
    return mp.nstr(mp.mpf(value.numerator) / value.denominator, digits)


def main() -> None:
    exact = exact_endpoint_audit()
    print("EXACT ENDPOINT AUDIT")
    for key in (
        "mu",
        "delta",
        "claimed_m2",
        "cap_c_7_over_20",
        "gap_c_7_over_20",
        "score_gap_c_7_over_20",
        "cap_c_3_over_8",
        "gap_c_3_over_8",
        "score_gap_c_3_over_8",
    ):
        value = exact[key]
        print(f"{key} = {value} = {decimal(value)}")

    assert exact["claimed_m2"] > exact["cap_c_7_over_20"]
    assert exact["claimed_m2"] > exact["cap_c_3_over_8"]
    assert exact["score_gap_c_7_over_20"] > 0
    assert exact["score_gap_c_3_over_8"] > 0

    print("\nWRITTEN POINTWISE-CONE REPRODUCTION")
    low = written_cone_profile(50)
    high = written_cone_profile(80)
    for key in high:
        print(f"{key} = {mp.nstr(high[key], 24)}")

    calibration_gap = abs(low["m2"] - high["m2"])
    print(f"50-vs-80-dps M2 difference = {mp.nstr(calibration_gap, 8)}")
    print("pointwise check: r(t)=0 on the central gap and r(t)=V_sigma(mu*t) outside")
    print("therefore 0 <= r(t) <= V_sigma(mu*t) identically by construction")
    print(f"M2 - 0.3144 = {mp.nstr(high['m2'] - mp.mpf('0.3144'), 24)}")

    assert abs(high["profile_mass"] - 1) < mp.mpf("1e-60")
    assert calibration_gap < mp.mpf("1e-40")
    assert high["m2"] > mp.mpf("0.3144")
    assert high["m2"] > mp.mpf(exact["claimed_m2"].numerator) / exact[
        "claimed_m2"
    ].denominator

    print("\nVERDICT")
    print("density-one premise package: INCONSISTENT AT s/N = 1")
    print("claimed pointwise maximum M2 <= 0.3144: NOT REPRODUCED")
    print("an additional admissibility condition is required to obtain that bound")


if __name__ == "__main__":
    main()
