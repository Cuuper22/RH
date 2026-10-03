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

X = sp.symbols("x")

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
# Part B: exact rational piecewise-polynomial certificate (Fraction arithmetic)
# ---------------------------------------------------------------------------
# A polynomial is a list of Fractions, index = power.


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pscale(p, c):
    return [c * a for a in p]


def pmul(p, q):
    out = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return out


def pint(p):
    """Antiderivative with zero constant term."""
    return [Fr(0)] + [a / (i + 1) for i, a in enumerate(p)]


def peval(p, x):
    v = Fr(0)
    for a in reversed(p):
        v = v * x + a
    return v


def pdef(p, lo, hi):
    P = pint(p)
    return peval(P, hi) - peval(P, lo)


def pshift(p, c):
    """p(x + c) as a polynomial in x."""
    out = [Fr(0)] * len(p)
    for i, a in enumerate(p):
        if a:
            for k in range(i + 1):
                out[k] += a * Fr(factorial(i), factorial(k) * factorial(i - k)) * c ** (i - k)
    return out


def pxmul(p):
    return [Fr(0)] + list(p)


def taylor_cos_sqrt2(J):
    p = [Fr(0)] * (2 * J + 1)
    for j in range(J + 1):
        p[2 * j] = Fr((-1) ** j * 2 ** j, factorial(2 * j))
    return p


def taylor_cos(J):
    p = [Fr(0)] * (2 * J + 1)
    for j in range(J + 1):
        p[2 * j] = Fr((-1) ** j, factorial(2 * j))
    return p


def taylor_sin_sqrt3_over_sqrt3(J):
    p = [Fr(0)] * (2 * J + 2)
    for j in range(J + 1):
        p[2 * j + 1] = Fr((-1) ** j * 3 ** j, factorial(2 * j + 1))
    return p


def rational_profile(eps, a_num, bp_num, J=10):
    """Pieces [(lo, hi, poly)] on L, M, R for width 1+eps (A = 1).

    a_num, bp_num: rational approximations of a and b' = b*sqrt3.
    """
    eps = Fr(eps)
    s = 1 + eps
    x0 = (1 - eps) / 2
    pm = taylor_cos_sqrt2(J)
    f = padd(pscale(taylor_cos(J), a_num), pscale(taylor_sin_sqrt3_over_sqrt3(J), bp_num))
    pr = pshift(f, -Fr(1, 2))                       # f(x - 1/2)
    pl = [a * (-1) ** i for i, a in enumerate(pr)]  # pr(-x)
    return [(-s / 2, -x0, pl), (-x0, x0, pm), (x0, s / 2, pr)]


def check_positive(pieces):
    for lo, hi, p in pieces:
        poly = sp.Poly([sp.Rational(a.numerator, a.denominator) for a in reversed(p)], X)
        assert poly.count_roots(sp.Rational(lo.numerator, lo.denominator),
                                sp.Rational(hi.numerator, hi.denominator)) == 0
        assert peval(p, (lo + hi) / 2) > 0


def left_abs_integral(p, lo, x_poly_shift=None):
    """Polynomial in x equal to int_lo^x (x - y) p(y) dy."""
    Q, R = pint(p), pint(pxmul(p))
    # x*(Q(x)-Q(lo)) - (R(x)-R(lo))
    term = padd(pxmul(padd(Q, [-peval(Q, lo)])), pscale(padd(R, [-peval(R, lo)]), Fr(-1)))
    return term


def right_abs_integral(p, hi):
    """Polynomial in x equal to int_x^hi (y - x) p(y) dy."""
    Q, R = pint(p), pint(pxmul(p))
    return padd(padd([peval(R, hi)], pscale(R, Fr(-1))),
                pscale(pxmul(padd([peval(Q, hi)], pscale(Q, Fr(-1)))), Fr(-1)))


def ku_pieces(u_pieces, eps):
    """(K*u) on each piece as a polynomial, K = min(|t|,1)."""
    lo_l, hi_l, p_l = u_pieces[0]
    lo_r, hi_r, p_r = u_pieces[2]
    out = []
    for i, (lo_i, hi_i, p_i) in enumerate(u_pieces):
        val = [Fr(0)]
        for j, (lo_j, hi_j, p_j) in enumerate(u_pieces):
            m0, m1 = pdef(p_j, lo_j, hi_j), pdef(pxmul(p_j), lo_j, hi_j)
            if j < i:      # int (x - y) p_j = x m0 - m1
                val = padd(val, [-m1, m0])
            elif j > i:    # int (y - x) p_j = m1 - x m0
                val = padd(val, [m1, -m0])
            else:
                val = padd(val, left_abs_integral(p_i, lo_i))
                val = padd(val, right_abs_integral(p_i, hi_i))
        if i == 2:
            # subtract int_{lo_l}^{x-1} (x-1-y) p_l(y) dy  =  G(x-1), G(z)=int_{lo_l}^{z}(z-y)p_l
            G = left_abs_integral(p_l, lo_l)
            val = padd(val, pscale(pshift(G, Fr(-1)), Fr(-1)))
        if i == 0:
            # subtract int_{x+1}^{hi_r} (y-x-1) p_r(y) dy = H(x+1), H(z)=int_z^{hi_r}(y-z)p_r
            H = right_abs_integral(p_r, hi_r)
            val = padd(val, pscale(pshift(H, Fr(1)), Fr(-1)))
        out.append(val)
    return out


def cost_and_residual(pieces, eps):
    """Exact D(u) for u = P/mass, and exact ||u + K*u - c||^2."""
    eps = Fr(eps)
    s = 1 + eps
    mass = sum(pdef(p, lo, hi) for lo, hi, p in pieces)
    u_pieces = [(lo, hi, pscale(p, 1 / mass)) for lo, hi, p in pieces]
    ku = ku_pieces(u_pieces, eps)
    # D = int u (u + K*u)
    D = sum(pdef(pmul(p, padd(p, k)), lo, hi) for (lo, hi, p), k in zip(u_pieces, ku))
    c = sum(pdef(padd(p, k), lo, hi) for (lo, hi, p), k in zip(u_pieces, ku)) / s
    rr = Fr(0)
    for (lo, hi, p), k in zip(u_pieces, ku):
        r = padd(padd(p, k), [-c])
        rr += pdef(pmul(r, r), lo, hi)
    return D, rr, c


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
    return Fr(int(mp.nint(a * scale)), scale), Fr(int(mp.nint(b * r3 * scale)), scale)


# ---------------------------------------------------------------------------
# Part C: floating QP (NUMERICAL)
# ---------------------------------------------------------------------------


def qp(eps, C=1.0, n=900, iters=4000):
    """Piecewise-constant discretisation of inf D with K=C on 1<|t|<=1+eps.

    Monotone projected-gradient descent on the simplex, started from the
    (admissible) width-one Montgomery--Taylor cosine, so the returned value is
    always the cost of a feasible profile (an upper bound on inf D, hence the
    reported gain is a valid lower bound and is >= 0 up to discretisation).
    """
    s = 1 + eps
    h = s / n
    x = -s / 2 + h * (np.arange(n) + 0.5)
    T = np.abs(x[:, None] - x[None, :])
    K = np.where(T <= 1, T, C)
    K[np.arange(n), np.arange(n)] = h / 3
    Q = h * np.eye(n) + h * h * K
    # start: cosine on |x|<=1/2
    u = np.where(np.abs(x) <= 0.5, np.cos(np.sqrt(2) * x), 0.0)
    u /= h * u.sum()
    L = np.linalg.norm(Q, 2) * 2
    step = 1.0 / L

    def project(v):
        # Euclidean projection onto {v >= 0, h*sum v = 1}
        target = 1.0 / h
        w = np.sort(v)[::-1]
        css = np.cumsum(w)
        k = np.arange(1, n + 1)
        cond = w - (css - target) / k > 0
        rho = k[cond][-1]
        theta = (css[rho - 1] - target) / rho
        return np.maximum(v - theta, 0.0)

    f = u @ Q @ u
    y, t = u.copy(), 1.0
    for _ in range(iters):
        g = 2 * Q @ y
        u_new = project(y - step * g)
        f_new = u_new @ Q @ u_new
        if f_new > f:                      # monotone safeguard: restart momentum
            y, t = u.copy(), 1.0
            u_new = project(u - step * (2 * Q @ u))
            f_new = u_new @ Q @ u_new
            if f_new > f:
                break
        t_new = (1 + np.sqrt(1 + 4 * t * t)) / 2
        y = u_new + ((t - 1) / t_new) * (u_new - u)
        u, f, t = u_new, f_new, t_new
    return float(f), u, x


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
        pieces = rational_profile(eps, a_num, bp_num, J=10)
        check_positive(pieces)
        D_up, rr, c = cost_and_residual(pieces, eps)
        m = convexity_constant(eps)
        assert m > 0
        D_lo = D_up - rr / m
        g_lo, g_hi = 2 - D_up, 2 - D_lo
        Dcf = rows[eps][0]
        # consistency with Part A (interval endpoints are mpf; compare through decimal strings)
        cf_lo, cf_hi = (Fr(t.strip()) for t in mpmath.nstr(Dcf, 40).strip('[]').split(','))
        assert D_lo <= cf_hi + Fr(1, 10 ** 30) and D_up >= cf_lo - Fr(1, 10 ** 30), "enclosures disagree"
        D1_lo = Fr(13274992963, 10 ** 10)          # rational lower bound of D_1
        assert D1.a > mp.mpf(D1_lo.numerator) / D1_lo.denominator
        gain_lo = g_lo - (2 - D1_lo)              # rigorous strict gain over g(0)
        assert gain_lo > 0
        print(f"eps={float(eps):<6} D(u0)={float(D_up):.18f}  ||r||^2={float(rr):.3e}  m>={float(m):.4f}"
              f"  => D* in [{float(D_lo):.18f}, {float(D_up):.18f}]")
        print(f"          g(eps) in [{float(g_lo):.16f}, {float(g_hi):.16f}];  rigorous gain over g(0) >= "
              f"{float(gain_lo):.12e}  = {float(gain_lo * 271803):.1f} x (1/271803)")
        print(f"          profile: a={a_num}, b'={bp_num} (A=1, Taylor order 20)")

    print("\n== Part C: floating diagnostics (NUMERICAL) ==")
    g0f = float(g0.mid)
    for eps in [0.001, 0.01, 0.05, 0.1, 0.25]:
        Dq, _, _ = qp(eps, 1.0, 600)
        print(f"eps={eps:<6} QP D={Dq:.9f}  (closed form {mpmath.nstr(rows[Fr(str(eps))][0].mid, 10)})")
    print("gain g_C(eps)-g(0) when only F <= C is known on 1<|alpha|<=1+eps:")
    for eps in [0.01, 0.05, 0.1, 0.25]:
        row = []
        for C in [1, 2, 5, 10, 30, 100]:
            Dq, _, _ = qp(eps, C, 500)
            row.append((C, round(2 - Dq - g0f, 7)))
        print(f"  eps={eps}: {row}")
    print("best gain over eps for fixed C (law ~ const/C):")
    for C in [5, 10, 30, 100]:
        best = (0, 0)
        for eps in np.concatenate([np.linspace(0.004, 0.1, 13), np.linspace(0.15, 0.6, 10)]):
            Dq, _, _ = qp(eps, C, 400)
            if 2 - Dq - g0f > best[1]:
                best = (eps, 2 - Dq - g0f)
        print(f"  C={C}: eps_opt~{best[0]:.3f}  gain~{best[1]:.5f}  gain*C~{best[1] * C:.3f}")


if __name__ == "__main__":
    main()
