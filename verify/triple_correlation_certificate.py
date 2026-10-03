"""Triple-correlation certificates: support geometry, obstructions, and a marked cubic gain.

Companion to docs/research/triple_correlation_20261003.md.  Sections:
  [1] exact support geometry of the translation-invariant 3- and 4-level regions;
  [2] exact cancellation behind the vanishing third cumulant on the hexagon;
  [3] interval-arithmetic two-off-line-pair obstruction to cubic spectral certificates;
  [4] the cubic-moment-only adversary (abstract tight block + literal clusters);
  [5] numerical checks of the marked operator identity and linear-term inequality;
  [6] EXACT rational certificate for the marked ordered-cubic gain;
  [7] optional numerical QP over polynomial marks (needs cvxpy) and a CUE sanity check.
Exact sections use Fractions/sympy; [3],[4] use mpmath interval arithmetic.
The analytic transfers (marked 3-level and marked ordered 4-level limits) are NOT
checked here; see the memo for their status.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction as F
from math import factorial, isqrt, lcm, comb
import random, sys, time
import numpy as np
import sympy as sp
from mpmath import iv, mpf, pi as mpi, sqrt as msqrt

# ---------------------------------------------------------------- [1]
def section1():
    print("[1] support geometry (exact rational tests)")
    rnd = random.Random(1)
    for _ in range(20000):
        a = F(rnd.randint(-999, 999), 1000); b = F(rnd.randint(-999, 999), 1000)
        xi = (a, b, -a - b)
        assert sum(abs(t) for t in xi) == 2 * max(abs(t) for t in xi)
        # realise as a triangle cycle (x-y, y-z, z-x) in an interval of length max|xi|
        y = F(0); x = y + a; z = y - b
        assert (x - y, y - z, z - x) == xi
        assert max(x, y, z) - min(x, y, z) == max(abs(t) for t in xi)
    for _ in range(20000):
        xs = [F(rnd.randint(-999, 999), 1000) for _ in range(3)]
        xi = xs + [-sum(xs)]
        pos = sum(t for t in xi if t > 0)
        assert sum(abs(t) for t in xi) == 2 * pos
        assert max(abs(t) for t in xi) <= pos
    print("    sum-zero triples: sum|xi| = 2 max|xi| (hexagon = triangle-cycle range < 1): OK")
    print("    sum-zero n-tuples: sum|xi| = 2 sum(xi)_+ >= 2 max|xi|; no |xi_i| >= 1 inside sum|xi| < 2: OK")

# ---------------------------------------------------------------- [2]
def section2():
    print("[2] sine-kernel 3-level structure factor on the hexagon")
    rnd = random.Random(2)
    for _ in range(20000):
        a = F(rnd.randint(-999, 999), 1000); b = F(rnd.randint(-999, 999), 1000)
        xi = (a, b, -a - b)
        if max(abs(t) for t in xi) >= 1:
            continue
        # i=j=k: 1 ; three i=j!=k lines: -(1-|xi_c|) off the delta ; 2K12K23K31: 2(1-max|xi|)
        cont = 1 - sum(1 - abs(t) for t in xi) + 2 * (1 - max(abs(t) for t in xi))
        assert cont == 0
    print("    continuous part 1 - sum(1-|xi_c|) + 2(1-max|xi|) = 0 on the hexagon: OK")
    print("    => S3 = delta delta + sum_c delta(xi_c)|xi_a| there; third cumulant vanishes")

# ---------------------------------------------------------------- [3]
iv.dps = 60
class C:
    def __init__(s, re, im=None): s.re = re; s.im = im if im is not None else iv.mpf(0)
    def __add__(s, o): return C(s.re + o.re, s.im + o.im)
    def __mul__(s, o): return C(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
    def __truediv__(s, o):
        den = o.re * o.re + o.im * o.im
        return C((s.re * o.re + s.im * o.im) / den, (s.im * o.re - s.re * o.im) / den)
def Iw(d, c):
    """int_{-1/2}^{1/2} exp(i w x) dx = 2 sin(w/2)/w for w = d + i c != 0."""
    ch = (iv.exp(c / 2) + iv.exp(-c / 2)) / 2; sh = (iv.exp(c / 2) - iv.exp(-c / 2)) / 2
    sn = C(iv.sin(d / 2) * ch, iv.cos(d / 2) * sh)
    return C(2 * sn.re, 2 * sn.im) / C(d, c)
def Iu_cos(d, c):
    """int u(x) exp(i w x) dx for the normalised Montgomery-Taylor cosine u, w = d + i c."""
    r2 = iv.sqrt(2); cn = r2 / (2 * iv.sin(1 / r2))
    t = Iw(d + r2, c) + Iw(d - r2, c)
    return C(cn * t.re / 2, cn * t.im / 2)
def two_pair_traces(B, delta, profile="flat"):
    """Exact trace formulas for two off-line pairs, ordinates 0, delta (zeta-units L*gamma)."""
    z = iv.mpf(0); w = [z, delta]
    M = lambda f: [[f(w[j] - w[i], i == j) for j in range(2)] for i in range(2)]
    if profile == "flat":
        Kaa = M(lambda d, e: Iw(z if e else d, -2 * B))
        Kbb = M(lambda d, e: Iw(z if e else d, 2 * B))
        Sg = M(lambda d, e: C(iv.mpf(1)) if e else Iw(d, z))
    else:
        Kaa = M(lambda d, e: Iu_cos(z if e else d, -2 * B))
        Kbb = M(lambda d, e: Iu_cos(z if e else d, 2 * B))
        Sg = M(lambda d, e: Iu_cos(z if e else d, z))
    mul = lambda A, Bm: [[A[i][0] * Bm[0][j] + A[i][1] * Bm[1][j] for j in range(2)] for i in range(2)]
    tr = lambda A: A[0][0] + A[1][1]
    two, three = C(iv.mpf(2)), C(iv.mpf(3))
    t1 = tr(Sg) * two
    t2 = tr(mul(Sg, Sg)) * two + tr(mul(Kbb, Kaa)) * two
    t3 = tr(mul(mul(Sg, Sg), Sg)) * two + (tr(mul(mul(Sg, Kbb), Kaa)) + tr(mul(mul(Sg, Kaa), Kbb))) * three
    return t1.re, t2.re, t3.re
def section3():
    print("[3] two shallow off-line pairs vs cubic spectral certificates (interval arithmetic)")
    out = {}
    for Bv in (12, 48, 192, 1024, 4096):
        B = iv.mpf(Bv); dl = iv.mpf(str(mpi + mpi * (1 + 1 / msqrt(2)) / Bv))
        t1, t2, t3 = two_pair_traces(B, dl)
        Qd = t2 - 2 * t1                # S - (2trG - trG^2) with S = 0
        P = t3 - 3 * t2 + 2 * t1        # tr p(G), p = t(t-1)(t-2)
        assert t1.a == 4 and t1.b == 4 and Qd.a > 0 and P.b < 0
        r = Qd / (-P)
        out[Bv] = r.b
        print(f"    B={Bv:5d}: trG=4, slack>0, tr p(G)<0, ratio slack/|tr p| <= {float(r.b):.6e}, B*ratio <= {float((B*r).b):.6f}")
    print(f"    predicted limit B*ratio -> pi^2/(6 sqrt 2) = {float(mpi**2/(6*msqrt(2))):.6f}")
    for Bv, cc in ((192, '5.5'), (4096, '5.25')):
        B = iv.mpf(Bv); dl = iv.mpf(str(mpi + mpf(cc) / Bv))
        t1, t2, t3 = two_pair_traces(B, dl, "cosine")
        Qd = t2 - 2 * t1; P = t3 - 3 * t2 + 2 * t1
        assert abs(float(t1.mid) - 4) < 1e-12 and Qd.a > 0 and P.b < 0
        print(f"    cosine profile B={Bv:5d}: ratio <= {float((Qd/(-P)).b):.6e}, B*ratio <= {float((B*Qd/(-P)).b):.6f}")
    print("    => S >= trG*(..) + c*tr p(G) fails for every c<0 with |c| > ratio; with coalescing simple zeros (c<=0) only c=0 survives")
    return out

# ---------------------------------------------------------------- [4]
def section4(D, kappa, ratio4096):
    print("[4] cubic-moment-only adversary (abstract tight block + literal two-pair clusters)")
    excess = kappa * ratio4096
    print(f"    exact moments (1, D, 3D-2-kappa) attained with S/N = 2 - D + kappa*ratio; at B=4096:")
    print(f"    kappa*ratio <= {excess:.6e}  <  1/271803 = {1/271803:.6e} (the inherited ordered-quartic increment)")
    assert excess < 1 / 271803

# ---------------------------------------------------------------- [5]
def section5():
    print("[5] marked operator algebra (floating-point checks, not proofs)")
    rng = np.random.default_rng(3)
    def herm(n):
        M = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)); M = (M + M.conj().T) / 2
        np.fill_diagonal(M, 0); return M
    Sig = lambda A, V: A @ V @ V + V @ A @ V + V @ V @ A
    worst = 0
    for _ in range(300):
        n = 9; G = herm(n); H = herm(n); A = np.diag(rng.uniform(-1, 1, n)); I = np.eye(n)
        V = np.tril(G, -1); W = np.tril(H, -1); Z = V - W; X = G - H
        lhs = np.trace(A @ G @ G @ G) - np.trace(A @ H @ H @ H)
        rhs = (np.trace(A @ (H @ H @ X + H @ X @ H + X @ H @ H))
               + 2 * np.real(np.trace((Sig(A, V) - Sig(A, W)) @ Z.conj().T))
               + 2 * np.real(np.trace(Sig(A, Z) @ (H - I))))
        Bm = np.diag(rng.uniform(0, 2, n)); K = -1j * (W - W.conj().T); Y = W @ Bm @ W
        worst = max(worst, abs(lhs - rhs),
                    abs(np.linalg.norm(Y)**2 - np.linalg.norm(H @ Bm @ K + K @ Bm @ H)**2 / 8),
                    abs(np.linalg.norm(K)**2 - np.linalg.norm(H)**2))
    print(f"    marked cubic expansion identity / WBW identity / ||K||=||H||: max residual {worst:.2e}")
    assert worst < 1e-9
    def unit(n):
        v = rng.normal(size=n) + 1j * rng.normal(size=n); return v / np.linalg.norm(v)
    def proj(M):
        w, U = np.linalg.eigh(M); idx = w > 1e-10; return U[:, idx] @ U[:, idx].conj().T
    worst = -1e9
    for _ in range(3000):
        n = int(rng.integers(4, 14)); S = int(rng.integers(0, 5)); nd = int(rng.integers(0, 3)); npair = int(rng.integers(0, 3))
        P = np.zeros((n, n), complex); Q = np.zeros((n, n), complex)
        for _ in range(S): v = unit(n); P += np.outer(v, v.conj())
        for _ in range(nd): f = unit(n); Q += 2 * np.outer(f, f.conj())
        for _ in range(npair):
            a = unit(n) * rng.uniform(1, 3); b = unit(n); b = b / np.vdot(a, b).conjugate()
            Q += np.outer(a, b.conj()) + np.outer(b, a.conj())
        N = S + 2 * nd + 2 * npair; G = P + Q
        if abs(np.trace(G).real - N) > 1e-8: continue
        w, U = np.linalg.eigh(Q); Bq = (U * np.maximum(w, 0)) @ U.conj().T; Cq = (U * np.maximum(-w, 0)) @ U.conj().T
        Fp = proj(Bq); J = np.eye(n) - Fp; E = proj(J @ (P - Cq) @ J); H = E + 2 * Fp; X = G - H
        d2 = np.linalg.norm(X)**2; Delta = np.trace(G @ G).real - 4 * np.trace(G).real + 2 * N + S
        J0 = np.eye(n) - E - Fp; Dp = 2 * J0 @ X @ J0 - E @ X @ E + 2 * Fp @ X @ Fp
        assert np.linalg.norm(Dp - (H @ H @ X + H @ X @ H + X @ H @ H - 3 * (H @ X + X @ H) + 2 * X)) < 1e-8
        bvec = rng.uniform(0, rng.choice([0.5, 1, 2, 3]), n); A = np.eye(n) - np.diag(bvec)
        lhs = -np.trace(A @ Dp).real
        rhs = Delta - d2 + bvec.max() * np.sqrt(2 * N - S) * np.sqrt(d2)
        worst = max(worst, lhs - rhs)
    print(f"    linear term  -tr(A Dp(H)[X]) <= Delta - d^2 + beta sqrt(2N-S) d : max(lhs-rhs) = {worst:.2e}")
    assert worst < 1e-9

# ---------------------------------------------------------------- [6]
x = sp.symbols('x'); h = sp.Rational(1, 2)
COEFF = [1091974251780, -1092598710370, 183563572147, -13799851355, 11008450474, -46499927506, 75463768564]
ALPHA = [F(n, 10**12) for n in (472828210507, -1129673802345, 389359086226, 386110142863, -458489619579,
                                 22317526742, 282317470468, -176140789998, -68490929761, 138998680169,
                                 -35983150606, -43743837471, 33967978797)]
EPS = F(1, 250000); BETA = F(6001, 5000); DELTA0 = F(1, 216600)
def compositions(total, parts):
    if parts == 1: yield (total,); return
    for i in range(total + 1):
        for rest in compositions(total - i, parts - 1): yield (i,) + rest
def gm_levels(n, s):
    """Grundmann-Moller rule on the standard n-simplex, exact for degree 2s+1."""
    d = 2 * s + 1
    for i in range(s + 1):
        m = d + n - 2 * i
        yield F((-1)**i * m**d, 2**(2 * s) * factorial(i) * factorial(d + n - i)), m, compositions(s - i, n + 1)
def int_form(coeffs):
    den = 1
    for c in coeffs: den = lcm(den, c.denominator)
    return [int(c * den) for c in coeffs], den
def ev(nums, r, q):
    deg = len(nums) - 1; acc = 0
    for j in range(deg, -1, -1): acc = acc * r + nums[j] * q**(deg - j)
    return acc
def T1_exact(uc, ac, s):
    un, ud = int_form(uc); an, ad = int_form(ac); du = len(un) - 1; da = len(an) - 1; tot = F(0)
    for wi, m, comps in gm_levels(2, s):
        q = 2 * m; acc = 0; cache = {}
        def UA(r):
            if r not in cache: cache[r] = (ev(un, r, q), ev(an, r, q))
            return cache[r]
        for beta in comps:
            k1, k2 = (2 * b + 1 for b in beta[1:])
            lo, alo = UA(2 * k1 - m); up, aup = UA(2 * (k1 + k2) - m)
            acc += k2 * lo * up * (2 * lo * up * (aup + 2 * alo) * (2 * aup + alo)
                                   + lo * lo * (aup + 2 * alo)**2 + up * up * (2 * aup + alo)**2)
        tot += wi * F(acc, m * (ud * q**du)**4 * (ad * q**da)**2)
    return tot / 3
def T2_exact(uc, ac, s):
    un, ud = int_form(uc); an, ad = int_form(ac); du = len(un) - 1; da = len(an) - 1; tot = F(0)
    for wi, m, comps in gm_levels(3, s):
        q = 2 * m; acc = 0; cu = {}; ca = {}
        U = lambda r: cu[r] if r in cu else cu.setdefault(r, ev(un, r, q))
        A = lambda r: ca[r] if r in ca else ca.setdefault(r, ev(an, r, q))
        for beta in comps:
            k1, k2, k3 = (2 * b + 1 for b in beta[1:])
            r0 = 2 * k1 - m; r1 = 2 * (k1 + k2) - m; r2 = 2 * (k1 + k3) - m; r3 = 2 * (k1 + k2 + k3) - m
            u0, u1, u2, u3 = U(r0), U(r1), U(r2), U(r3); a0, a1, a2, a3 = A(r0), A(r1), A(r2), A(r3)
            S1 = a3 + a2 + a0; S2 = a3 + a1 + a0
            acc += k2 * k3 * u3 * u0 * u2 * (u1 * S1 * S2 + u2 * S1 * S1)
        tot += wi * F(acc, m * m * (ud * q**du)**4 * (ad * q**da)**2)
    return tot
def ceil_sqrt(q, dec=12):
    q = F(q); s = 10**dec; n = -(-q.numerator * s * s // q.denominator); r = isqrt(n)
    while r * r < n: r += 1
    return F(r, s)
def section6():
    print("[6] EXACT marked ordered-cubic certificate (repository profile + degree-24 mark)")
    R = lambda f: sp.Rational(f.numerator, f.denominator)
    p = sum(sp.Rational(c, 10**12) * x**(2 * j) for j, c in enumerate(COEFF))
    u = sp.expand(p / sp.integrate(p, (x, -h, h)))
    a = sp.expand(sum(R(al) * sp.legendre(2 * j, 2 * x) for j, al in enumerate(ALPHA)) - R(EPS))
    b = sp.expand(1 - a)
    assert sp.Poly(u, x).count_roots(-h, h) == 0 and u.subs(x, 0) > 0
    assert sp.Poly(b, x).count_roots(-h, h) == 0 and b.subs(x, 0) > 0
    assert sp.Poly(R(BETA) - b, x).count_roots(-h, h) == 0 and R(BETA) - b.subs(x, 0) > 0
    print(f"    profile u>0; mark a=1-b with 0<b<beta={BETA} on [-1/2,1/2] (Sturm counts), hence |a|<=1")
    I = lambda f: F(str(sp.integrate(sp.expand(f), (x, -h, h))))
    y = sp.symbols('y')
    K = lambda f: sp.expand(sp.integrate((x - y) * f.subs(x, y), (y, -h, x)) + sp.integrate((y - x) * f.subs(x, y), (y, x, h)))
    Ku = K(u); Ku2 = K(u * u)
    D = I(u * u + u * Ku); M3 = I(u**3 + 3 * u * u * Ku)
    dens = sp.expand(-(u**3 + 2 * u * u * Ku + u * Ku2 - 3 * u * u - 3 * u * Ku + 2 * u))
    kappa = I(dens); kappa_a = I(a * dens)
    assert kappa == 3 * D - 2 - M3
    T0 = F(3, 2) * I(a * a * u**4)
    cf = lambda e: [F(str(c)) for c in reversed(sp.Poly(e, x).all_coeffs())]
    uc, ac = cf(u), cf(a)
    t = time.time()
    T1 = T1_exact(uc, ac, 49); T2 = T2_exact(uc, ac, 49)
    assert T1 == T1_exact(uc, ac, 50) and T2 == T2_exact(uc, ac, 50)   # two exact rules agree
    QA = T0 + T1 + T2
    Q1 = F(3, 2) * I(u**4) + T1_exact(uc, [F(1)], 26) + T2_exact(uc, [F(1)], 26)
    print(f"    exact Grundmann-Moller integration ({time.time()-t:.1f}s); unmarked Q = {float(Q1/9):.16f}")
    print(f"    D = {float(D):.16f}  kappa = {float(kappa):.16f}")
    print(f"    marked defect kappa_a = {float(kappa_a):.16f}   marked ordered energy Q_A = {float(QA):.16f}")
    sD, sQ, sD23, s2 = ceil_sqrt(D), ceil_sqrt(QA), ceil_sqrt(D - F(2, 3)), ceil_sqrt(2)
    Cup = 3 * BETA * sD + s2 * sQ + 3 * s2 * sD23
    assert kappa_a > 6 * DELTA0
    margin = (kappa_a - 6 * DELTA0)**2 - DELTA0 * Cup * Cup
    assert margin > 0
    bound = 2 - D + DELTA0
    assert bound > F(672505319, 10**9)
    # the unmarked inequality with the same exact data, for comparison
    Cun = 3 * s2 * (ceil_sqrt(Q1 / 9) + sD23)
    dl_un = F(1, 271803)
    assert (kappa - 6 * dl_un)**2 - dl_un * Cun * Cun > 0
    print(f"    C <= {float(Cup):.10f};  (kappa_a - 6 d0)^2 - d0 C^2 = {float(margin):.4e} > 0 with d0 = 1/216600")
    print(f"    => liminf N0s/N >= 2 - D + 1/216600 = {float(bound):.13f} > 0.672505319")
    print(f"    (inherited frontier 2 - D + 1/271803 = {float(2 - D + dl_un):.13f})")
    return D, kappa

# ---------------------------------------------------------------- [7]
def section7():
    print("[7] optional numerics: mark QP sweep and CUE sanity check (NUMERICAL)")
    try:
        import cvxpy as cp
    except ImportError:
        print("    cvxpy not installed; QP sweep skipped"); return
    from numpy.polynomial.legendre import leggauss, legval
    def gl(n, lo, hi):
        t, w = leggauss(n); return (hi - lo) / 2 * t + (lo + hi) / 2, (hi - lo) / 2 * w
    up = lambda t: sum(c * 1e-12 * t**(2 * j) for j, c in enumerate(COEFF))
    Kd = 12; basis = [(lambda j: (lambda t: legval(2 * t, [0] * (2 * j) + [1])))(j) for j in range(Kd + 1)]
    evb = lambda t: np.array([f(t) for f in basis])
    n2, m = 64, 56
    X, WX = gl(n2, -.5, .5); mass = np.sum(WX * up(X)); U = lambda t: up(t) / mass; ux = U(X)
    V, WV = gl(n2, 0, 1)
    Y = np.concatenate([gl(n2, -.5, .5 - v)[0] for v in V]); WY = np.concatenate([gl(n2, -.5, .5 - v)[1] * wv * v for v, wv in zip(V, WV)])
    Xu = Y + np.repeat(V, n2); uy, uxx = U(Y), U(Xu); py, px = evb(Y), evb(Xu); ph = evb(X)
    I2 = lambda f: np.sum(WY * f)
    D = np.sum(WX * ux * ux) + 2 * I2(uxx * uy)
    k = -(ph @ (WX * ux**3) + 2 * (px @ (WY * uxx**2 * uy) + py @ (WY * uy**2 * uxx)) + (px @ (WY * uxx * uy**2) + py @ (WY * uy * uxx**2))
          - 3 * ph @ (WX * ux**2) - 3 * (px @ (WY * uxx * uy) + py @ (WY * uy * uxx)) + 2 * ph @ (WX * ux))
    Bm = (ph * (WX * 1.5 * ux**4)) @ ph.T
    A1 = px + 2 * py; A2 = 2 * px + py; T = (A1 * (WY * uxx**2 * uy**2 / 3)) @ A2.T; Bm += T + T.T
    Bm += (A1 * (WY * uxx * uy**3 / 3)) @ A1.T + (A2 * (WY * uxx**3 * uy / 3)) @ A2.T
    S, WS = gl(m, 0, 1); Tt, WT = gl(m, 0, 1); Zs, Ws, Vs, Wws = [], [], [], []
    for s_, ws in zip(S, WS):
        z, wz = gl(m, -.5, .5 - s_)
        for t_, wt in zip(Tt, WT):
            v_ = s_ * t_; w_ = s_ * (1 - t_)
            Zs.append(z); Ws.append(wz * ws * wt * s_ * v_ * w_); Vs.append(np.full(m, v_)); Wws.append(np.full(m, w_))
    z = np.concatenate(Zs); W3 = np.concatenate(Ws); vv = np.concatenate(Vs); ww = np.concatenate(Wws); top = z + vv + ww
    u0, ut, uf, us = U(z), U(top), U(z + vv), U(z + ww); p0, pt, pf, ps = evb(z), evb(top), evb(z + vv), evb(z + ww)
    L1 = pt + ps + p0; L2 = pt + pf + p0
    T = (L1 * (W3 * ut * us * uf * u0)) @ L2.T; Bm += (T + T.T) / 2; Bm += (L1 * (W3 * ut * us**2 * u0)) @ L1.T
    Bm = (Bm + Bm.T) / 2
    from scipy.optimize import brentq
    def cert(kap, QA, beta):
        Cc = 3 * beta * np.sqrt(D) + np.sqrt(2) * np.sqrt(QA) + 3 * np.sqrt(2) * np.sqrt(D - 2 / 3)
        return brentq(lambda d: 6 * d + np.sqrt(d) * Cc - kap, 1e-18, .1)
    e1 = np.eye(Kd + 1)[0]; d0 = cert(k @ e1, e1 @ Bm @ e1, 0.0)
    w_, Ev = np.linalg.eigh(Bm); Lh = Ev * np.sqrt(np.maximum(w_, 0))
    grid = np.linspace(0, .5, 801); Phi = evb(grid).T; best = (d0, None)
    for beta in (1.1, 1.2, 1.3):
        for mu in np.geomspace(1e-3, 3e-2, 12):
            al = cp.Variable(Kd + 1)
            cp.Problem(cp.Maximize(k @ al - mu * cp.sum_squares(Lh.T @ al)), [Phi @ al <= 1, Phi @ al >= 1 - beta]).solve(solver="CLARABEL")
            if al.value is None: continue
            av = Phi @ al.value
            dl = cert(k @ al.value, al.value @ Bm @ al.value, 1 - av.min())
            if dl > best[0]: best = (dl, beta)
    print(f"    unmarked delta = {d0:.6e} (1/{1/d0:.0f});  best degree-24 mark delta = {best[0]:.6e}  (x{best[0]/d0:.4f})")
    # CUE: exact 'Gaussian' range for triangle cycles; marked triple traces vs formula
    rng = np.random.default_rng(0); N = 160; M = N; xg = -0.5 + (np.arange(M) + 0.5) / M
    uc = np.cos(np.sqrt(2) * xg); uc = uc / np.sum(uc) * M; am = np.where(np.abs(xg) < 0.283, 1.0, -0.23)
    Kmat = np.abs(xg[:, None] - xg[None, :]) / M; Ku = Kmat @ uc; Ku2 = Kmat @ (uc * uc)
    form = np.sum(am * (uc**3 + 2 * uc * uc * Ku + uc * Ku2)) / M
    vals = []
    for _ in range(80):
        Zm = (rng.normal(size=(N, N)) + 1j * rng.normal(size=(N, N))) / np.sqrt(2)
        Qm, Rm = np.linalg.qr(Zm); Qm = Qm * (np.diag(Rm) / np.abs(np.diag(Rm)))
        th = np.angle(np.linalg.eigvals(Qm)); E = np.exp(1j * np.outer(np.arange(M), th))
        G = np.sqrt(np.outer(uc, uc)) * (E @ E.conj().T) / M
        vals.append(np.sum(am * np.diag(G @ G @ G)).real / N)
    vals = np.array(vals)
    print(f"    CUE N={N}: marked triple trace {vals.mean():.5f} +- {vals.std()/np.sqrt(len(vals)):.5f}; formula {form:.5f}")

if __name__ == "__main__":
    t0 = time.time()
    section1(); section2(); r = section3()
    D, kappa = section6()
    section4(D, float(kappa), float(r[4096]))
    section5()
    if "--no-numerics" not in sys.argv:
        section7()
    print(f"all assertions passed ({time.time()-t0:.0f}s)")
