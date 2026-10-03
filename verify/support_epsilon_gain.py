"""Gain function g(eps) for a hypothetical pair-correlation support 1+eps.

Certificate shape (repo, Theorem D / Zeta85 ladder):  simple-on-line fraction
>= 2 - D(u), with

    D(u) = int u^2 + iint K(x-y) u(x) u(y),     u >= 0, int u = 1,
    supp u in an interval of width s = 1+eps,

K(t) = |t| on |t| <= 1 (unconditional, Montgomery range) and K(t) = 1 on
1 < |t| <= 1+eps (the hypothetical one-sided form-factor input F <= 1 there).
g(eps) := 2 - D*(eps),  D*(eps) := inf D.

Part A (CHECKED, interval arithmetic): closed form of D*(eps) from the
Euler--Lagrange delay equation, evaluated with mpmath.iv.
Part B (CHECKED, exact rationals): for each table eps, an explicit
nonnegative piecewise-polynomial rational profile u0 gives D* <= D(u0)
exactly, and the dual residual bound D* >= D(u0) - ||r||^2/m with the
convexity constant m = 1 - 2 s^2/pi^2 - 2 eps^2 (proved in the memo).
Part C (NUMERICAL): floating QP cross-check, and the dependence on a weaker
one-sided bound F <= C on the strip.
"""

from fractions import Fraction as Fr
from math import factorial

import mpmath
import numpy as np
import sympy as sp
from mpmath import iv, mp

mp.dps = 40
iv.dps = 40

EPS_TABLE = [Fr(1, 1000), Fr(1, 100), Fr(1, 20), Fr(1, 10), Fr(1, 4)]
CUBIC_GAIN = Fr(1, 271803)          # sharpened_cubic_gain_20260905.md (8)

# ---------------------------------------------------------------------------
# Part A: closed form, interval certified
# ---------------------------------------------------------------------------


def closed_form_iv(eps):
    """Interval enclosure of D*(eps) and of the collar minimum.

    Profile (A=1 before normalisation):
      middle |x| <= x0 = (1-eps)/2 :  cos(sqrt2 x)
      right collar x = 1/2 + y, |y| <= eps/2 :  f(y) = a cos y + b sin(sqrt3 y)
    with (a,b) fixed by C^1 matching at x0.  D* = lambda/mass.
    """
    eps = Fr(eps)
    e = iv.mpf(eps.numerator) / eps.denominator
    x0 = (1 - e) / 2
    r2, r3 = iv.sqrt(2), iv.sqrt(3)
    # 2x2 system  [cos(e/2), -sin(r3 e/2); sin(e/2), r3 cos(r3 e/2)] (a,b)^T
    #           = (cos(r2 x0), -r2 sin(r2 x0))^T
    m11, m12 = iv.cos(e / 2), -iv.sin(r3 * e / 2)
    m21, m22 = iv.sin(e / 2), r3 * iv.cos(r3 * e / 2)
    b1, b2 = iv.cos(r2 * x0), -r2 * iv.sin(r2 * x0)
    det = m11 * m22 - m12 * m21
    a = (b1 * m22 - m12 * b2) / det
    b = (m11 * b2 - m21 * b1) / det
    mass = 2 * (iv.sin(r2 * x0) / r2 + 2 * a * iv.sin(e / 2))
    lam = 1 + 2 * (
        x0 * iv.sin(r2 * x0) / r2 + (iv.cos(r2 * x0) - 1) / 2
        + a * iv.sin(e / 2)
        + 2 * b * (-(e / 2) * iv.cos(r3 * e / 2) / r3 + iv.sin(r3 * e / 2) / 3)
    )
    D = lam / mass
    # positivity of the collar: f on a grid plus Lipschitz bound
    n = 64
    ys = [-e / 2 + e * k / n for k in range(n + 1)]
    fmin = min((a * iv.cos(y) + b * iv.sin(r3 * y)).a for y in ys)
    lip = abs(a) + r3 * abs(b)
    fmin_cert = fmin - (lip * e / (2 * n)).b
    return D, a / mass, b / mass, fmin_cert / mass.a


def g_prime_zero():
    """g'(0+) = csc^2(1/sqrt2)/2 - 1/2, as an interval."""
    t = 1 / iv.sqrt(2)
    return 1 / (2 * iv.sin(t) ** 2) - iv.mpf(1) / 2


# ---------------------------------------------------------------------------
# Part B: exact rational piecewise-polynomial certificate
# ---------------------------------------------------------------------------
X, Y = sp.symbols("x y")


def taylor_cos_sqrt2(J):
    return sum(sp.Rational((-1) ** j * 2 ** j, factorial(2 * j)) * X ** (2 * j)
               for j in range(J + 1))


def taylor_cos(z, J):
    return sum(sp.Rational((-1) ** j, factorial(2 * j)) * z ** (2 * j)
               for j in range(J + 1))


def taylor_sin_sqrt3_over_sqrt3(z, J):
    # sin(sqrt3 z)/sqrt3 = sum (-1)^j 3^j z^(2j+1)/(2j+1)!
    return sum(sp.Rational((-1) ** j * 3 ** j, factorial(2 * j + 1)) * z ** (2 * j + 1)
               for j in range(J + 1))


def rational_profile(eps, a_num, bp_num, J=14):
    """Piecewise polynomial pieces [(interval, poly)] for width 1+eps.

    a_num, bp_num: rational approximations of a and b' = b*sqrt3 (A = 1).
    """
    eps = sp.Rational(eps)
    s = 1 + eps
    x0 = (1 - eps) / 2
    pm = sp.expand(taylor_cos_sqrt2(J))
    z = X - sp.Rational(1, 2)
    pr = sp.expand(a_num * taylor_cos(z, J) + bp_num * taylor_sin_sqrt3_over_sqrt3(z, J))
    pl = sp.expand(pr.subs(X, -X))
    return [((-s / 2, -x0), pl), ((-x0, x0), pm), ((x0, s / 2), pr)]


def check_positive(pieces):
    for (lo, hi), p in pieces:
        poly = sp.Poly(p, X)
        assert poly.count_roots(lo, hi) == 0, "root inside piece"
        assert p.subs(X, (lo + hi) / 2) > 0


def integrate_piece(p, lo, hi):
    return sp.integrate(p, (X, lo, hi))


def cost_exact(pieces, eps):
    """Exact D(u) for u = P/mass with K = min(|t|,1); also returns pieces of u."""
    eps = sp.Rational(eps)
    s = 1 + eps
    mass = sum(integrate_piece(p, lo, hi) for (lo, hi), p in pieces)
    u_pieces = [((lo, hi), sp.expand(p / mass)) for (lo, hi), p in pieces]
    i2 = sum(integrate_piece(p ** 2, lo, hi) for (lo, hi), p in u_pieces)
    # iint |x-y| u u = 2 * sum over ordered pairs x>y
    abs_part = 0
    for i, ((lo_i, hi_i), p_i) in enumerate(u_pieces):
        # same piece: x in [lo_i,hi_i], y in [lo_i, x]
        inner = sp.integrate((X - Y) * p_i * p_i.subs(X, Y), (Y, lo_i, X))
        abs_part += sp.integrate(inner, (X, lo_i, hi_i))
        for j in range(i):
            (lo_j, hi_j), p_j = u_pieces[j]
            inner = sp.integrate((X - Y) * p_i * p_j.subs(X, Y), (Y, lo_j, hi_j))
            abs_part += sp.integrate(inner, (X, lo_i, hi_i))
    abs_part = 2 * abs_part
    # saturation: subtract 2 * int_{x in R} int_{y in L, y < x-1} (x-y-1) u u
    (lo_l, hi_l), p_l = u_pieces[0]
    (lo_r, hi_r), p_r = u_pieces[2]
    inner = sp.integrate((X - Y - 1) * p_r * p_l.subs(X, Y), (Y, lo_l, X - 1))
    sat = 2 * sp.integrate(inner, (X, lo_r, hi_r))
    D = sp.nsimplify(i2 + abs_part - sat)
    return sp.Rational(D), u_pieces


def residual_norm_sq(u_pieces, eps):
    """Exact ||u + K*u - c||_2^2 with c the mean of u + K*u on the window."""
    eps = sp.Rational(eps)
    s = 1 + eps
    (lo_l, hi_l), p_l = u_pieces[0]
    (lo_r, hi_r), p_r = u_pieces[2]
    ku = []
    for i, ((lo_i, hi_i), p_i) in enumerate(u_pieces):
        val = 0
        for j, ((lo_j, hi_j), p_j) in enumerate(u_pieces):
            if j < i:
                val += sp.integrate((X - Y) * p_j.subs(X, Y), (Y, lo_j, hi_j))
            elif j > i:
                val += sp.integrate((Y - X) * p_j.subs(X, Y), (Y, lo_j, hi_j))
            else:
                val += sp.integrate((X - Y) * p_i.subs(X, Y), (Y, lo_i, X))
                val += sp.integrate((Y - X) * p_i.subs(X, Y), (Y, X, hi_i))
        if i == 2:   # right collar: y < x-1 lies in the left collar
            val -= sp.integrate((X - Y - 1) * p_l.subs(X, Y), (Y, lo_l, X - 1))
        if i == 0:   # left collar: y > x+1 lies in the right collar
            val -= sp.integrate((Y - X - 1) * p_r.subs(X, Y), (Y, X + 1, hi_r))
        ku.append(sp.expand(p_i + val))
    c = sum(integrate_piece(q, lo, hi) for ((lo, hi), _), q in zip(u_pieces, ku)) / s
    rr = sum(integrate_piece(sp.expand((q - c) ** 2), lo, hi)
             for ((lo, hi), _), q in zip(u_pieces, ku))
    return sp.Rational(sp.nsimplify(rr)), sp.Rational(sp.nsimplify(c))


def convexity_constant(eps):
    """m = 1 - 2 s^2/pi^2 - 2 eps^2 with pi > 314159/100000 (lower bound on m)."""
    eps = Fr(eps)
    s = 1 + eps
    pi_lo = Fr(314159, 100000)
    return 1 - 2 * s * s / (pi_lo * pi_lo) - 2 * eps * eps


def fit_rational_params(eps):
    """Rational a, b' from the high-precision closed form (A = 1)."""
    eps = Fr(eps)
    e = mp.mpf(eps.numerator) / eps.denominator
    x0 = (1 - e) / 2
    r2, r3 = mp.sqrt(2), mp.sqrt(3)
    M = mp.matrix([[mp.cos(e / 2), -mp.sin(r3 * e / 2)], [mp.sin(e / 2), r3 * mp.cos(r3 * e / 2)]])
    rhs = mp.matrix([mp.cos(r2 * x0), -r2 * mp.sin(r2 * x0)])
    a, b = mp.lu_solve(M, rhs)
    scale = 10 ** 18
    return (sp.Rational(int(mp.nint(a * scale)), scale),
            sp.Rational(int(mp.nint(b * r3 * scale)), scale))


# ---------------------------------------------------------------------------
# Part C: floating QP (NUMERICAL)
# ---------------------------------------------------------------------------


def qp(eps, C=1.0, n=900):
    """Piecewise-constant discretisation of inf D with K=C on 1<|t|<=1+eps."""
    s = 1 + eps
    h = s / n
    x = -s / 2 + h * (np.arange(n) + 0.5)
    T = np.abs(x[:, None] - x[None, :])
    K = np.where(T <= 1, T, C)
    K[np.arange(n), np.arange(n)] = h / 3
    Q = h * np.eye(n) + h * h * K
    active = np.ones(n, bool)
    u = None
    for _ in range(60):
        idx = np.where(active)[0]
        v = np.linalg.solve(Q[np.ix_(idx, idx)], np.ones(len(idx)))
        u = np.zeros(n)
        u[idx] = v / (h * v.sum())
        if (u[idx] >= -1e-12).all():
            break
        active[idx[u[idx] < 0]] = False
    return float(u @ Q @ u), u, x


# ---------------------------------------------------------------------------
def main():
    D1 = iv.mpf(1) / 2 + iv.cos(1 / iv.sqrt(2)) / (iv.sqrt(2) * iv.sin(1 / iv.sqrt(2)))
    g0 = 2 - D1
    gp = g_prime_zero()
    print("== Part A: closed form (interval arithmetic, 40 digits) ==")
    print("g(0) = 2 - D_1 in", mpmath.nstr(g0, 20))
    print("g'(0+) = csc^2(1/sqrt2)/2 - 1/2 in", mpmath.nstr(gp, 20))
    print("eps equivalent to the cubic gain 1/271803:",
          mpmath.nstr(iv.mpf(1) / 271803 / gp, 10))
    rows = {}
    for eps in EPS_TABLE + [Fr(1, 2)]:
        D, a, b, fmin = closed_form_iv(eps)
        g = 2 - D
        assert fmin > 0, "collar positivity failed"
        rows[eps] = (D, g)
        print(f"eps={float(eps):<6} D*(eps) in {mpmath.nstr(D, 18)}   g(eps) in {mpmath.nstr(g, 18)}"
              f"   collar min >= {mpmath.nstr(fmin, 6)}   (g-g0)/eps in {mpmath.nstr((g - g0) * eps.denominator / eps.numerator, 12)}"
              f"   gain/cubic_gain in {mpmath.nstr((g - g0) * 271803, 10)}")
    # second-order coefficient (NUMERICAL, high precision floats)
    for ef in [Fr(1, 1000), Fr(1, 10000), Fr(1, 100000)]:
        D, _, _, _ = closed_form_iv(ef)
        e = mp.mpf(ef.numerator) / ef.denominator
        c2 = ((2 - D.mid) - g0.mid - gp.mid * e) / e ** 2
        print(f"  second-order coefficient estimate at eps={float(ef)}: {mpmath.nstr(c2, 10)}")

    print("\n== Part B: exact rational piecewise-polynomial certificates ==")
    print("(upper bound D(u0) exact; lower bound D(u0) - ||r||^2/m with m = 1-2s^2/pi^2-2eps^2)")
    for eps in EPS_TABLE:
        a_num, bp_num = fit_rational_params(eps)
        pieces = rational_profile(eps, a_num, bp_num, J=14)
        check_positive(pieces)
        D_up, u_pieces = cost_exact(pieces, eps)
        rr, c = residual_norm_sq(u_pieces, eps)
        m = convexity_constant(eps)
        assert m > 0
        D_lo = D_up - Fr(rr) / m
        g_lo, g_hi = 2 - D_up, 2 - D_lo
        Dcf, _ = rows[eps][0], None
        # consistency with Part A
        assert float(D_lo) <= float(Dcf.b) and float(D_up) >= float(Dcf.a), "enclosures disagree"
        D1_lo = Fr(13274992963, 10 ** 10)          # rational lower bound of D_1
        assert D1.a > mp.mpf(D1_lo.numerator) / D1_lo.denominator
        gain_lo = g_lo - (2 - D1_lo)              # rigorous strict gain over g(0)
        assert gain_lo > 0
        print(f"eps={float(eps):<6} D(u0)={float(D_up):.18f}  ||r||^2={float(rr):.3e}  m>={float(m):.4f}"
              f"  => D* in [{float(D_lo):.18f}, {float(D_up):.18f}]")
        print(f"          g(eps) in [{float(g_lo):.16f}, {float(g_hi):.16f}];  rigorous gain over g(0) >= "
              f"{float(gain_lo):.12e}  = {float(gain_lo * 271803):.1f} x (1/271803)")

    print("\n== Part C: floating diagnostics (NUMERICAL) ==")
    g0f = float(g0.mid)
    for eps in [0.001, 0.01, 0.05, 0.1, 0.25]:
        Dq, _, _ = qp(eps, 1.0, 900)
        print(f"eps={eps:<6} QP D={Dq:.9f}  (closed form {mpmath.nstr(rows[Fr(str(eps))][0].mid, 10)})")
    print("gain g_C(eps)-g(0) when only F <= C is known on 1<|alpha|<=1+eps:")
    for eps in [0.01, 0.05, 0.1, 0.25]:
        row = []
        for C in [1, 2, 5, 10, 30, 100]:
            Dq, _, _ = qp(eps, C, 700)
            row.append((C, round(2 - Dq - g0f, 7)))
        print(f"  eps={eps}: {row}")
    print("best gain over eps for fixed C (law ~ const/C):")
    for C in [5, 10, 30, 100]:
        best = (0, 0)
        for eps in np.concatenate([np.linspace(0.004, 0.1, 13), np.linspace(0.15, 0.6, 10)]):
            Dq, _, _ = qp(eps, C, 500)
            if 2 - Dq - g0f > best[1]:
                best = (eps, 2 - Dq - g0f)
        print(f"  C={C}: eps_opt~{best[0]:.3f}  gain~{best[1]:.5f}  gain*C~{best[1] * C:.3f}")


if __name__ == "__main__":
    main()
