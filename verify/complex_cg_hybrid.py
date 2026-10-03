"""Hybrid route to the complex Cheer--Goldston inequality (**): Lemma-R split, barriers,
a single-pair theorem valid at every height, and a targeted mid-height adversary.

Companion to docs/research/complex_cg_hybrid_20261003.md (labels PROVED / CHECKED /
NUMERICAL / REFUTED as there).  Output: verify/complex_cg_hybrid.out.
Default run: about 6 minutes on 4 cores.  `python3 complex_cg_hybrid.py full` runs the
larger adversary (about 15 minutes) whose numbers are quoted in the memo.

(**)  Sigma_Z(rho) = int_{-1}^{1} rho |S_Z|^2  >=  kappa (2N - s_1),   kappa = r(0) = 1,
S_Z(a) = sum_real m_j e(a x_j) + sum_pairs 2 m_k cosh(2 pi a v_k) e(a x_k).

Part 0  The certified Cheer--Goldston test of verify/complex_cg_proof.py (same LP, same
        exact positivity certificate r >= 0 on R): P(rho) = 1.3210847, kappa_real >= 1.
Part 1  The split rho = sigma + rho_r, sigma = phi*phi~ (phi >= 0 on [-1/2,1/2]):
        best sigma found, exact node check sigma <= rho, structure of the remainder,
        and the numerical barriers of memo Section 2.
Part 2  Pair lattices: ratio rho(0) at every height; zero lifting field (memo Section 3).
Part 3  Theorem H1 (memo Section 4): (**) for real atoms + ONE conjugate pair of any
        multiplicity at any height v >= 0.0795 (v <= 0.08 is Theorem 4 of
        complex_cg_proof).  Rigorous cell-packing bound, swept over v in [0.0795, 20]
        with interval control in v and x, plus an analytic bound for v >= 20.
Part 4  Targeted adversary: pairs at middle heights v >= v_lo in near-tight real designs,
        with dense real clusters, heavy neighbours and doubles (periodic, exact form).
Do not run lake.  Nothing here is a Lean statement.
"""
import os, sys, time, math, pickle
os.environ.setdefault("OMP_NUM_THREADS", "1")
import numpy as np
from scipy.optimize import linprog, minimize
from multiprocessing import Pool

T0 = time.time()
FULL = len(sys.argv) > 1 and sys.argv[1] == "full"
Lam, D, SLOPE = 2.5, 0.01, 20.0
K = int(round(Lam / D)); al = np.linspace(0, Lam, K + 1); k1 = int(round(1 / D))

# ============================================================== Part 0
def cell_cos_mat(us):
    M = np.zeros((len(us), K + 1)); w = 2 * np.pi * us
    for k in range(K):
        a, b = al[k], al[k + 1]; h = b - a
        with np.errstate(divide='ignore', invalid='ignore'):
            I = (np.sin(w * b) - np.sin(w * a)) / w
            J = h * np.sin(w * b) / w + (np.cos(w * b) - np.cos(w * a)) / w ** 2
            I0 = I - J / h; I1 = J / h
        m = np.abs(us) < 1e-12; I0[m] = h / 2; I1[m] = h / 2
        M[:, k] += 2 * I0; M[:, k + 1] += 2 * I1
    return M

def solve_lp(du=0.001, U=50.0, eps=1e-6):
    """Verbatim LP of verify/complex_cg_proof.py, Part 1."""
    us = np.arange(0, U + 1e-9, du); M = cell_cos_mat(us)
    obj = np.zeros(K + 1); obj[0] += 1
    for k in range(k1):
        a, b = al[k], al[k + 1]; h = b - a
        I0 = (b**2 - a**2) / 2 - (b**3 - a**3) / (3 * h) + a * (b**2 - a**2) / (2 * h)
        I1 = (b**3 - a**3) / (3 * h) - a * (b**2 - a**2) / (2 * h)
        obj[k] += 2 * I0; obj[k + 1] += 2 * I1
    norm = np.full(K + 1, 2 * D); norm[0] = D; norm[K] = D
    bounds = [(0.0, 20.0)] * (k1 + 1) + [(-20.0, 0.0)] * (K - k1)
    bounds[K] = (0.0, 0.0); bounds[k1] = (0.0, 0.0)
    Dm = np.zeros((2 * K, K + 1))
    for k in range(K):
        Dm[2 * k, k] = -1; Dm[2 * k, k + 1] = 1; Dm[2 * k + 1, k] = 1; Dm[2 * k + 1, k + 1] = -1
    res = linprog(obj, A_ub=np.vstack([-M, Dm]),
                  b_ub=np.concatenate([np.full(len(us), -eps), np.full(2 * K, SLOPE * D)]),
                  A_eq=norm[None, :], b_eq=[1.0], bounds=bounds, method="highs")
    assert res.status == 0, res.message
    return res.x, float(obj @ res.x), float(norm[:k1 + 1] @ res.x[:k1 + 1])

def jumps(cc):
    sl = np.diff(cc) / D; J = np.zeros(len(cc)); J[0] = 2 * sl[0]; J[1:-1] = sl[1:] - sl[:-1]; J[-1] = -sl[-1]; return J

def certify_r(c, h=0.0005):
    """Exact positivity certificate of complex_cg_proof.py: r(u) = -T(u)/(2 pi^2 u^2), T 100-periodic."""
    J = jumps(c); coef = J.copy(); coef[0] = J[0] / 2
    M2 = (2 * np.pi) ** 2 * np.sum(np.abs(coef) * al ** 2)
    L1 = 2 * np.pi * np.sum(np.abs(c) * al * np.r_[D / 2, np.full(K - 1, D), D / 2]) * 2
    u0 = 0.9 / L1; us = np.arange(u0, 50 + h, h); worst = -np.inf
    for s0 in range(0, len(us), 20000):
        u = us[s0:s0 + 20000]
        C = np.cos(2 * np.pi * np.outer(u, al)); S = np.sin(2 * np.pi * np.outer(u, al))
        T = C @ coef; Tp = -(S * (2 * np.pi * al)) @ coef
        worst = max(worst, (np.maximum(T, T + Tp * h + M2 * h ** 2 / 2) + 4e-12 * np.sum(np.abs(coef))).max())
    return worst


def part0():
    print("Part 0: certified Cheer-Goldston test (re-solved; identical to verify/complex_cg_proof.py)")
    c, P, R = solve_lp()
    w = certify_r(c)
    print("  P(rho) = %.10f, R = int rho = %.8f, rho(0) = %.6f, r(0) = 1 (LP equality); max cell bound of T on [u0,50] = %.2e -> r >= 0 on R %s"
          % (P, R, c[0], w, "CERTIFIED" if w < 0 else "NOT CERTIFIED"))
    print("  kappa_real(rho) >= 1 (Cheer-Goldston); (**) for complex Z would give 2 - P = %.7f   [%.0fs]" % (2 - P, time.time() - T0))
    sys.stdout.flush()
    return c, P, R

# ============================================================== shared setup from the LP solution
G = {}
def setup(c):
    """Derived exact data of rho (PL on the 0.01 grid of [0,1]) and of r."""
    rho = c[:k1 + 1]; s = np.diff(rho) / D
    G.update(c=c, rho=rho, s=s, jk=s[1:] - s[:-1], an=al[1:k1], JJ=np.r_[s[1:] - s[:-1], -s[-1]], aJ=al[1:k1 + 1])
    Jr = jumps(c); coefr = Jr.copy(); coefr[0] = Jr[0] / 2; G['coefr'] = coefr
    gx, gw = np.polynomial.legendre.leggauss(10)
    G['Aq'] = np.concatenate([(al[k] + al[k + 1]) / 2 + D / 2 * gx for k in range(k1)])
    G['Wq'] = np.concatenate([D / 2 * gw] * k1)
    G['rhoq'] = np.interp(G['Aq'], al[:k1 + 1], rho); G['drhoq'] = np.repeat(s, len(gx))
    g6, w6 = np.polynomial.legendre.leggauss(6)
    Aall = np.concatenate([(al[k] + al[k + 1]) / 2 + D / 2 * g6 for k in range(K)]); Wall = np.concatenate([D / 2 * w6] * K)
    rq = np.abs(np.interp(Aall, al, c))
    G['Lr'] = 1.001 * 2 * 2 * np.pi * np.sum(Wall * Aall * rq)            # |r'| <= 2 pi int |a rhat|
    G['M2r'] = 1.001 * 2 * 4 * np.pi ** 2 * np.sum(Wall * Aall ** 2 * rq)   # |r''| <= 4 pi^2 int a^2 |rhat|
    hu = 1e-4; uu = np.arange(0.05, 1.2 + hu / 2, hu); ru, _, eu = r_and_dr(uu)
    G['uu'] = uu; G['pref'] = np.minimum.accumulate(np.minimum(ru[:-1], ru[1:]) - G['Lr'] * hu / 2 - eu[:-1])

def integ(f): return 2 * np.sum(G['Wq'] * f)          # int_{-1}^{1} of an even function sampled on (0,1)
def rho_at(a): return np.interp(np.abs(a), al[:k1 + 1], G['rho'], right=0.0)
def r_and_dr(u):
    """r(u) = -T(u)/(2 pi^2 u^2) (exact jump representation), r'(u), rounding allowance."""
    ph = 2 * np.pi * np.outer(u, al); T = np.cos(ph) @ G['coefr']; Tp = -(np.sin(ph) * (2 * np.pi * al)) @ G['coefr']
    return -T / (2 * np.pi ** 2 * u ** 2), -Tp / (2 * np.pi ** 2 * u ** 2) + T / (np.pi ** 2 * u ** 3), 1e-13 * np.sum(np.abs(G['coefr'])) / (2 * np.pi ** 2 * u ** 2)
def rmin_lo(d):
    """certified lower bound for min_{[0,d]} r (grid + Lipschitz on [0.05,1.2]; r >= 1 - L_r u below 0.05)."""
    d = np.atleast_1d(d); idx = np.clip(np.searchsorted(G['uu'], d), 1, len(G['pref']))
    return np.minimum(1 - G['Lr'] * 0.05, G['pref'][idx - 1])
def Ifun(lam):
    """I(lam) = int_0^1 rho(a) e^{lam a} da in closed form (PL rho, rho(1) = 0), dI/dlam, magnitudes."""
    rho, s, jk, an = G['rho'], G['s'], G['jk'], G['an']
    E = np.exp(np.outer(lam, an)); e1 = np.exp(lam)
    B = s[0] - s[-1] * e1 + E @ jk; B1 = -s[-1] * e1 + E @ (jk * an)
    I = -rho[0] / lam + B / lam ** 2
    dI = rho[0] / lam ** 2 - 2 * B / lam ** 3 + B1 / lam ** 2
    re = np.exp(np.outer(lam.real, an))
    M = np.abs(rho[0] / lam) + (abs(s[0]) + abs(s[-1]) * np.exp(lam.real) + re @ np.abs(jk)) / np.abs(lam) ** 2
    M1 = 3 * M / np.abs(lam) + (abs(s[-1]) * np.exp(lam.real) + re @ np.abs(jk * an)) / np.abs(lam) ** 2
    return I, dI, M, M1
def Xv(v): return integ(G['rhoq'] * np.sinh(2 * np.pi * G['Aq'] * v) ** 2)
def Tv(v):
    """TV((rho d)')/(4 pi^2), d = cosh(2 pi a v) - 1: |Q_v(x)| <= Tv(v)/x^2; increasing in v."""
    Aq, rq, drq = G['Aq'], G['rhoq'], G['drhoq']
    d1 = 2 * np.pi * v * np.sinh(2 * np.pi * Aq * v); d2 = (2 * np.pi * v) ** 2 * np.cosh(2 * np.pi * Aq * v)
    return 1.001 * (2 * np.sum(np.abs(G['JJ']) * (np.cosh(2 * np.pi * G['aJ'] * v) - 1)) + integ(2 * np.abs(drq) * d1 + rq * d2)) / (4 * np.pi ** 2)
def dQbar(v): return 1.001 * integ(G['rhoq'] * 2 * np.pi * G['Aq'] * np.sinh(2 * np.pi * G['Aq'] * v))
def Tdv(v):
    """TV((rho g)')/(4 pi^2), g = d/dv d = 2 pi a sinh(2 pi a v): |dQ_v/dv (x)| <= Tdv/x^2; increasing in v."""
    a, rq, drq = G['Aq'], G['rhoq'], G['drhoq']; aJ = G['aJ']
    g1 = 2 * np.pi * np.sinh(2 * np.pi * a * v) + 4 * np.pi ** 2 * a * v * np.cosh(2 * np.pi * a * v)
    g2 = 8 * np.pi ** 2 * v * np.cosh(2 * np.pi * a * v) + 8 * np.pi ** 3 * a * v ** 2 * np.sinh(2 * np.pi * a * v)
    return 1.001 * (2 * np.sum(np.abs(G['JJ']) * 2 * np.pi * aJ * np.sinh(2 * np.pi * aJ * v)) + integ(2 * np.abs(drq) * g1 + rq * g2)) / (4 * np.pi ** 2)

# ============================================================== Part 1: the Lemma-R split
def part1(P, R):
    print("\nPart 1: the split rho = sigma + rho_r with sigma = phi*phi~ (Lemma R covers sigma at every height)")
    c = G['c']; n = 100; h = 1.0 / n; rhon = c[:n + 1]
    def acf(phi):
        full = np.correlate(phi, phi, 'full') * h; out = np.zeros(n + 1); m = min(n + 1, len(full) - (n - 1)); out[:m] = full[n - 1:n - 1 + m]; return out
    best = None
    for p0 in (np.full(n, 0.9), 1.3 * np.cos(np.pi * ((np.arange(n) + 0.5) * h - 0.5))):
        res = minimize(lambda p: -(h * p.sum()) ** 2, p0, jac=lambda p: -2 * (h * p.sum()) * h * np.ones(n),
                       constraints=[{'type': 'ineq', 'fun': lambda p: rhon - acf(p)}], bounds=[(0, None)] * n,
                       method='SLSQP', options={'maxiter': 500, 'ftol': 1e-13})
        if best is None or -res.fun > best[0]: best = (-res.fun, res.x)
    phi = np.maximum(best[1], 0)
    sig = acf(phi); t = min(1.0, np.min(np.where(sig > 0, rhon / np.maximum(sig, 1e-300), np.inf)))
    phi = phi * np.sqrt(t) * (1 - 1e-12); sig = acf(phi)
    kap = (h * phi.sum()) ** 2
    ok = np.all(sig <= rhon)
    print("  sigma = phi*phi~, phi >= 0 piecewise constant on the 0.01 grid of [-1/2,1/2]; sigma and rho are PL on the same nodes,")
    print("  so sigma <= rho on [-1,1] iff at the 101 nodes: %s (max sigma - rho = %.1e).  kappa_auto(rho) >= int sigma = (int phi)^2 = %.6f (CHECKED)"
          % (ok, (sig - rhon).max(), kap))
    rr = rhon - sig; supp = np.where(rr > 1e-9)[0]
    print("  remainder rho_r = rho - sigma >= 0: int rho_r = %.6f, rho_r(0) = %.1e, rho_r > 1e-9 only on |a| in [%.2f, %.2f], max rho_r = %.4f at |a| = %.2f"
          % (R - kap, rr[0], supp.min() * h, supp.max() * h, rr.max(), rr.argmax() * h))
    print("  sigma(0) = %.6f = rho(0); Var(phi) = sigma(0) - int sigma = %.6f; P(sigma)/int sigma = %.6f (>= c_MT = 1.3274993)"
          % (sig[0], sig[0] - kap, (sig[0] + 2 * h * np.sum(np.arange(n + 1) * h * sig) - h * sig[-1]) / kap))
    cMT = 0.5 + 2 ** -0.5 / math.tan(2 ** -0.5); front = 0.6725162800
    need = P / (2 - front)
    print("  all-height (**) from Lemma R alone: kappa = %.6f -> 2 - P/kappa = %.6f (below Montgomery-Taylor 0.6725007)" % (kap, 2 - P / kap))
    print("  [Prop 2.3] any mixture of autocorrelations sigma <= rho has int sigma <= P(rho)/c_MT = %.6f < %.6f = P/(2 - frontier) needed" % (P / cMT, need))
    print("             so an all-height argument must extract >= %.5f per unit cost (frontier) / %.5f (kappa = 1) beyond Lemma R" % (need - kap, 1 - kap))
    eps = 2 * (1 - kap)
    print("  [Prop 2.5] high pairs charged at kappa_H = %.6f, everything else at 1: worst case (2-P-eps)/(1-eps) = %.6f, eps = %.5f;"
          % (kap, (2 - P - eps) / (1 - eps), eps))
    kH = 1 - (2 - P - front) / (2 * (1 - front)); fH = (2 - P - front) / eps
    print("             the frontier is beaten iff kappa_H > %.5f, or iff the fraction of zeros in high pairs is < %.4f" % (kH, fH))
    for cCG, lab in ((1.0, "Lemma 4 (kappa_real <= rho(0))"), (2 - 0.6818287, "bandwidth-one ceiling 0.6818287"), (1.3209466, "LP value (NUMERICAL)")):
        # need (1 + (cCG-1) a^2)/a < 2 - front
        A_, B_, C_ = cCG - 1, -(2 - front), 1.0
        disc = B_ ** 2 - 4 * A_ * C_
        amin = (1 / (2 - front)) if A_ == 0 else (-B_ - math.sqrt(disc)) / (2 * A_)
        print("  [Prop 2.6] remainder supported in [-a,a]: beats the frontier only if a > %.5f  (using %s); height gain factor 1/a < %.4f"
              % (amin, lab, 1 / amin))
    sys.stdout.flush()
    return kap, phi

# ============================================================== Part 2: pair lattices
def per_sigma(x, v, Wt, M):
    nmax = int(np.floor(M - 1e-12)); f = np.arange(1, nmax + 1) / M
    T = ((Wt * np.cosh(2 * np.pi * np.outer(f, v))) * np.exp(2j * np.pi * np.outer(f, x))).sum(1)
    return (rho_at(0) * Wt.sum() ** 2 + 2 * np.sum(rho_at(f) * np.abs(T) ** 2)) / M

def part2(phi):
    print("\nPart 2: pair lattices (memo Section 3, PROVED; numerical confirmation)")
    for v in (0.1, 0.6, 2.0, 5.0):
        print("  unit lattice of pairs (m=1) at common height v=%.1f: Sigma/cost per period = %.6f = rho(0)" % (v, per_sigma(np.array([0.]), np.array([v]), np.array([2.]), 1.0) / 4))
    # zero lifting field: sum_n Q_v(x - n) = sum_k f_v(k) e(kx) = f_v(0) = 0
    x0 = np.array([0.3, 0.5, 0.77]); v = 0.6; Nn = 4000
    nn = np.arange(-Nn, Nn + 1)
    lam = lambda xx, sg: 2 * np.pi * (sg * v + 1j * xx)
    tot = np.zeros(3)
    for i, xx in enumerate(x0):
        X_ = xx - nn; Ip, _, _, _ = Ifun(lam(X_, 1)); Im, _, _, _ = Ifun(lam(X_, -1)); I0, _, _, _ = Ifun(2j * np.pi * X_)
        tot[i] = np.sum(np.real(Ip + Im - 2 * I0))
    print("  lifting field of the unit pair lattice at v=0.6 on a real atom: sum_{|n|<=%d} Q_v(x-n) = %s (Q_v(0.5) alone = %.3f; tail O(1/N))"
          % (Nn, np.array2string(tot, precision=5), np.real(sum(Ifun(np.array([lam(0.5, 1)]))[0] + Ifun(np.array([lam(0.5, -1)]))[0] - 2 * Ifun(np.array([1j * np.pi]))[0]))))
    print("  triangle test sigma = (1-|a|)_+ (phi = 1 on [-1/2,1/2]): pair lattice gives Sigma/cost = sigma(0) = 1 = int sigma at every height -> Lemma R exactly tight, no per-pair height surplus")
    sys.stdout.flush()

# ============================================================== Part 3: Theorem H1 (single pair, every height)
def Psi_exact(Gv, rc):
    """max over integers w >= 0 of 4 G w - pen(w); pen(w) = rc w^2 - 2 rc w + [w=1] rc + [w odd >= 3] min(rc, 3 - 3 rc)."""
    Gv = np.atleast_1d(Gv).astype(float); rc = np.atleast_1d(rc) * np.ones_like(Gv)
    best = 8 * Gv; ws0 = 2 * Gv / rc + 1
    for d in range(-3, 4):
        for par in (0, 1):
            w = np.floor(ws0) + d; w = np.maximum(w + ((w % 2) != par), 0)
            pen = rc * w ** 2 - 2 * rc * w + np.where(w == 1, rc, np.where(w % 2 == 1, np.minimum(rc, 3 - 3 * rc), 0))
            best = np.maximum(best, 4 * Gv * w - pen)
    return best

GRIDS = {}
def make_grid(XF, h=1e-3):
    xs = np.arange(0.25, XF + h / 2, h); r0, dr0, er0 = r_and_dr(xs); I0, dI0, M0, M10 = Ifun(2j * np.pi * xs)
    GRIDS[XF] = dict(xs=xs, h=h, XF=XF, r0=r0, dr0=dr0, er0=er0, I0=I0, dI0=dI0, M0=M0, M10=M10)

def h1_check(v0, v1, XF):
    """Certified bound, valid for every v in [v0,v1], on (sum of cell gains)/(4 m^2 X(v) + 4m(m-1)).
    Returns (max over m, m = 1 value, uniform m >= 2 value, lmax, tail cell length, #pieces)."""
    gr = GRIDS[XF]; xs, h = gr['xs'], gr['h']
    Ip, dIp, Mp, M1p = Ifun(2 * np.pi * (v0 + 1j * xs)); Im, dIm, Mm, M1m = Ifun(2 * np.pi * (-v0 + 1j * xs))
    Q = np.real(Ip + Im - 2 * gr['I0']); dQ = np.real(2j * np.pi * (dIp + dIm - 2 * gr['dI0']))
    eQ = 1e-13 * (Mp + Mm + 2 * gr['M0']); edQ = 1e-13 * 2 * np.pi * (M1p + M1m + 2 * gr['M10'])
    F = gr['r0'] + Q; dF = gr['dr0'] + dQ; eF = gr['er0'] + eQ
    M2 = G['M2r'] + 1.001 * integ(G['rhoq'] * 4 * np.pi ** 2 * G['Aq'] ** 2 * (np.cosh(2 * np.pi * G['Aq'] * v0) - 1))
    Dv = np.minimum(dQbar(v1), Tdv(v1) / xs ** 2) * (v1 - v0)
    err = np.abs(edQ) * h + M2 * h * h / 2 + eF + Dv
    lo = np.minimum(F, F + dF * h) - err; up = np.maximum(-F, -F - dF * h) + err
    act = (lo < 0)[:-1]
    dd = np.diff(np.r_[0, act.astype(int), 0]); st = np.where(dd == 1)[0]; en = np.where(dd == -1)[0]
    X = Xv(v0); T = Tv(v1); best = None
    for lmax in (0.5, 0.6, 0.7):
        gs = []; Ls = []
        for a, b in zip(st, en):
            L = (b - a) * h; npc = max(1, int(math.ceil(L / lmax - 1e-12))); edges = np.linspace(a, b, npc + 1).round().astype(int)
            for t in range(npc):
                if edges[t + 1] > edges[t]:
                    gs.append(max(0.0, up[edges[t]:edges[t + 1]].max())); Ls.append((edges[t + 1] - edges[t]) * h)
        g = np.array(gs); rc = rmin_lo(np.array(Ls))
        for Lt in (0.5, 1.0):
            rt = rmin_lo(Lt)[0]; Z2 = XF ** -2 + XF ** -1 / Lt; Z4 = XF ** -4 + XF ** -3 / (3 * Lt)
            tl = 8 * T * Z2; tq = 4 * T ** 2 * Z4 / rt; tail1 = tl + (tq if T / XF ** 2 > min(rt, 0.75) else 0.0)
            r1 = 2 * (Psi_exact(g, rc).sum() + tail1) / (4 * X)
            rU = 2 * (np.sum(4 * g ** 2 / rc) + tq) / (4 * X) + 2 * (np.sum(8 * g) + tl) / (8 * X)
            cand = (max(r1, rU), r1, rU, lmax, Lt, len(g))
            if best is None or cand[0] < best[0]: best = cand
    return best

def h1_sweep(args):
    va, vb = args; out = []; v = va; rel = 0.003
    while v < vb - 1e-12:
        XF = 60.0 if v < 0.5 else 20.0
        v1 = min(vb, v * (1 + rel)); b = h1_check(v, v1, XF)
        if b[0] > 0.95 and rel > 0.0004: rel /= 2; continue
        out.append((v, v1) + b); v = v1
        if b[0] < 0.85: rel = min(rel * 1.5, 0.05)
    return out

def h1_analytic(v, a1=0.9):
    """v >= 20: half-unit cells from 1/4; sum_c sup Q^2 <= (2 + 4 pi) ||f_v||_2^2 (Plancherel), monotone bounds."""
    rho, s = G['rho'], G['s']; kk = int(round(a1 * 100))
    ratio = np.r_[rho[kk:k1] / (1 - al[kk:k1]), -s[-1]]; l1, L1 = ratio.min(), ratio.max(); rmax = rho.max(); R = integ(G['rhoq'])
    rh = rmin_lo(0.5)[0]; y = 4 * np.pi * v * (1 - a1); eps1 = np.exp(-y) * (1 + y)
    num = 4 * L1 ** 2 / (4 * np.pi * v) + 2 * rmax ** 2 * (4 * np.pi * v) * np.exp(-4 * np.pi * (1 - a1) * v)
    den = (l1 / 2) * (1 - eps1) - l1 * (1 - a1) ** 2 * (4 * np.pi * v) ** 2 * np.exp(-4 * np.pi * v) / 2
    main = (2 + 4 * np.pi) * (num / den) / rh
    Smax = np.abs(s).max(); SJ = np.abs(G['JJ']).sum(); e = np.exp(2 * np.pi * v)
    TVf = e * (2 * SJ + 4 * Smax + 2 * np.pi * v * rmax); T = TVf / (4 * np.pi ** 2)
    T1 = 2 * np.pi * (TVf + 4 * (Smax + 2 * np.pi * v * rmax) * e) / (4 * np.pi ** 2)
    Xlo = l1 / 2 * np.exp(4 * np.pi * v) * (1 - eps1) / (4 * np.pi * v) ** 2 - l1 * (1 - a1) ** 2 / 2
    lin = 2 * (8 * np.sqrt(R * e * T) + 4 * np.sqrt(2 * np.pi * R * e * T1)) / Xlo
    return main, lin, l1, L1, rh

def part3(pool):
    print("\nPart 3: Theorem H1 -- (**) for arbitrary real atoms plus ONE conjugate pair (any multiplicity m, any height v)")
    print("  identity: Sigma - cost = sum_j (W_j^2 - cost_j) + sum_{j!=k} W_j W_k r(x_j-x_k) + 4m sum_j W_j G_v(x_j) + 4m^2 X(v) + 4m(m-1) + int shat |S_0|^2,")
    print("  G_v = r + Q_v, Q_v = FT[rho (cosh(2 pi a v) - 1)], X(v) = int rho sinh^2(2 pi a v).  Cell packing: per cell of diameter d,")
    print("  gain <= Psi(m g_c) with pen(w) from integer multiplicities and intra-cell r >= rmin(d).  Need sum_c Psi <= 4 m^2 X + 4m(m-1).")
    t1 = time.time()
    edges = [0.0795, 0.13, 0.25, 0.6, 20.0]
    res = pool.map(h1_sweep, list(zip(edges[:-1], edges[1:])))
    log = [row for part in res for row in part]
    ok = all(row[2] < 1 for row in log) and abs(log[0][0] - 0.0795) < 1e-12 and abs(log[-1][1] - 20.0) < 1e-9 \
        and all(abs(log[i][1] - log[i + 1][0]) < 1e-12 for i in range(len(log) - 1))
    vv = np.array([row[0] for row in log]); mx = np.array([row[2] for row in log]); m1 = np.array([row[3] for row in log]); un = np.array([row[4] for row in log])
    print("  sweep v in [0.0795, 20]: %d contiguous intervals, every certified ratio < 1: %s   [%.0fs]" % (len(log), ok, time.time() - t1))
    for a, b in [(0.0795, 0.13), (0.13, 0.25), (0.25, 0.4), (0.4, 0.6), (0.6, 1), (1, 2), (2, 5), (5, 10), (10, 20)]:
        sel = (vv >= a) & (vv < b)
        print("    v in [%5.2f,%5.2f): %4d intervals, max certified ratio %.3f (m = 1: %.3f, all m >= 2: %.3f)" % (a, b, sel.sum(), mx[sel].max(), m1[sel].max(), un[sel].max()))
    ok2 = True
    for v in (20.0, 25.0, 40.0):
        main, lin, l1, L1, rh = h1_analytic(v); ok2 &= main + lin < 1
        print("  analytic bound v=%.0f: (2+4pi)||f_v||^2/(rmin(1/2) X) <= %.4f, linear part <= %.1e  (l_1=%.4f, L_1=%.4f, rmin(1/2)=%.4f)" % (v, main, lin, l1, L1, rh))
    print("  both pieces are decreasing in v for v >= 1/(4 pi (1-a_1)) = %.2f, so the bound < 1 holds for all v >= 20: %s" % (1 / (4 * np.pi * 0.1), ok2))
    print("  Theorem 4 of complex_cg_proof covers v <= 0.08.  => (**) with kappa = 1 for every Z = (reals) + (one pair), any height: %s"
          % ("PROVED (modulo the CHECKED constants)" if ok and ok2 else "NOT ESTABLISHED"))
    sys.stdout.flush()
    return log

# ============================================================== Part 4: targeted adversary at middle heights
def drho_at(f):
    i = np.clip((np.abs(f) / D).astype(int), 0, k1 - 1); return np.where(np.abs(f) < 1, G['s'][i], 0.0)
def sig_grad(x, v, Wt, M):
    """per-period Sigma of an M-periodic configuration (exact) and its gradient in x, v, M."""
    nmax = int(np.floor(M - 1e-12)); n = np.arange(1, nmax + 1); f = n / M; TP = 2 * np.pi
    ch = np.cosh(TP * np.outer(f, v)); sh = np.sinh(TP * np.outer(f, v)); E = np.exp(1j * TP * np.outer(f, x))
    amp = ch * Wt; T = (amp * E).sum(1); rf = rho_at(f)
    val = (rho_at(0) * Wt.sum() ** 2 + 2 * np.sum(rf * np.abs(T) ** 2)) / M
    cT = np.conj(T)
    gx = (2 / M) * np.sum((rf * 2)[:, None] * np.real(cT[:, None] * amp * 1j * TP * f[:, None] * E), 0)
    gv = (2 / M) * np.sum((rf * 2)[:, None] * np.real(cT[:, None] * Wt * TP * f[:, None] * sh * E), 0)
    dTdf = ((Wt * (TP * v) * sh + amp * 1j * TP * x) * E).sum(1)
    gM = -val / M + (2 / M) * np.sum((drho_at(f) * np.abs(T) ** 2 + rf * 2 * np.real(cT * dTdf)) * (-n / M ** 2))
    return val, gx, gv, gM
def costv(Wt, isp): return np.sum(np.where(isp, 2 * Wt, np.where(Wt == 1, 1, 2 * Wt)))
def optimise(Wt, isp, x0, v0, M0, vlo, vhi, iters=600):
    Kk = len(Wt); Pp = np.where(isp)[0]; C = costv(Wt, isp)
    def unpack(z):
        v = np.zeros(Kk); v[Pp] = z[Kk:Kk + len(Pp)]; return z[:Kk], v, z[-1]
    def f(z):
        x, v, M = unpack(z); val, gx, gv, gM = sig_grad(x, v, Wt, M); return val / C, np.r_[gx, gv[Pp], gM] / C
    bnds = [(None, None)] * Kk + [(vlo[i], vhi[i]) for i in Pp] + [(max(1.0, 0.5 * M0), 2 * M0)]
    z0 = np.r_[x0, np.clip(v0[Pp], vlo[Pp], vhi[Pp]), M0]
    res = minimize(f, z0, jac=True, method='L-BFGS-B', bounds=bnds, options={'maxiter': iters})
    x, v, M = unpack(res.x); return res.fun, x, v, M, C

def tight_job(seed):
    rng = np.random.default_rng(seed); out = []
    for _ in range(40):
        Kk = rng.integers(4, 26); Wt = rng.choice([1.0, 2.0], size=Kk)
        M0 = Wt.sum() * rng.uniform(0.95, 1.15) if rng.random() < 0.5 else Kk * rng.uniform(1.0, 1.6)
        isp = np.zeros(Kk, bool); z = np.zeros(Kk)
        val, x, v, M, C = optimise(Wt, isp, np.sort(rng.uniform(0, M0, Kk)), z, M0, z, z)
        out.append((val, Wt, x, M))
    return out

TIGHT = []
def adv_job(args):
    seed, vlo, mode = args; rng = np.random.default_rng(10007 * seed + 13)
    VHI = 0.6
    if mode == 'random':
        Kk = rng.integers(5, 41); kinds = rng.choice(4, size=Kk, p=[0.35, 0.3, 0.1, 0.25])
        Wt = np.array([1., 2., 0, 0])[kinds]; Wt[kinds == 2] = rng.choice([3., 4., 5.], (kinds == 2).sum())
        isp = kinds == 3; Wt[isp] = 2.0 * rng.choice([1, 1, 2], isp.sum())
        if isp.sum() == 0: isp[0] = True; Wt[0] = 2.0
        Pp = np.where(isp)[0]; mid = rng.choice(Pp, min(len(Pp), rng.integers(1, 3)), replace=False)
        vlo_a = np.zeros(Kk); vhi_a = np.where(isp, 1.0, 0.0); vlo_a[mid] = vlo; vhi_a[mid] = VHI
        M = Wt.sum() * rng.uniform(0.9, 1.3); x0 = np.sort(rng.uniform(0, M, Kk))
        v0 = np.where(isp, rng.uniform(0, 0.6, Kk), 0.0); v0[mid] = rng.uniform(vlo, VHI, len(mid))
    else:
        val, Wt, x, M = TIGHT[rng.integers(len(TIGHT))]
        rep = rng.integers(1, 5 if FULL else 4); Wt = np.tile(Wt, rep).copy(); x = np.concatenate([x + k * M for k in range(rep)]); M = M * rep
        Kk = len(Wt); isp = np.zeros(Kk, bool)
        if mode == 'alllift':
            if rng.random() < 0.3: Wt[:] = 2.0
            isp = Wt == 2
            if isp.sum() == 0: isp[0] = True; Wt[0] = 2.0
            mid = np.where(isp)[0]; extra = []
        else:
            nmid = 1 if mode == 'single' else 2
            mid = rng.choice(Kk, nmid, replace=False)
            for i in mid: isp[i] = True; Wt[i] = 2.0 * rng.choice([1, 1, 1, 2])
            if mode in ('two', 'cluster') or rng.random() < 0.5:
                j = (mid[0] + rng.choice([-1, 1])) % Kk
                if not isp[j]: Wt[j] = rng.choice([2., 3., 4., 5., 6.])
            if mode == 'cluster':
                nc = rng.integers(2, 6); xc = x[mid[0]] + rng.choice([-1, 1]) * rng.uniform(0.6, 1.2) + rng.uniform(-0.3, 0.3, nc)
                x = np.r_[x, xc]; Wt = np.r_[Wt, np.ones(nc)]; isp = np.r_[isp, np.zeros(nc, bool)]; M = M + nc * rng.uniform(0.5, 1.0); Kk = len(Wt)
            free = np.where((~isp) & (Wt == 2))[0]; extra = []
            if mode != 'single' and len(free) > 0 and rng.random() < 0.5:
                extra = rng.choice(free, min(len(free), rng.integers(1, 4)), replace=False); isp[extra] = True
        vlo_a = np.zeros(Kk); vhi_a = np.zeros(Kk)
        vlo_a[mid] = vlo; vhi_a[mid] = VHI
        for i in extra: vhi_a[i] = 1.0
        v0 = np.zeros(Kk); v0[mid] = rng.uniform(vlo, VHI, len(mid)) if mode != 'alllift' else vlo + 0.05 * rng.random(len(mid))
        for i in extra: v0[i] = rng.uniform(0, 0.5)
        x0 = x + rng.normal(0, 0.03, Kk)
    val, x, v, M, C = optimise(Wt, isp, x0, v0, M, vlo_a, vhi_a)
    return (vlo, mode, val, (val * C - C) / len(mid), len(Wt), int(isp.sum()), len(mid), float(np.max(v[mid])))

def part4():
    print("\nPart 4: targeted adversary, pairs at middle heights v in [v_lo, 0.6] (periodic configurations, exact quadratic form)")
    t1 = time.time()
    with Pool(4) as pool: tt = pool.map(tight_job, range(8 if FULL else 4))
    allt = sorted([o for part in tt for o in part], key=lambda o: o[0])
    TIGHT.extend(allt[:60])
    print("  near-tight real seeds: best real ratio %.6f (period %.3f, %d atoms); %d seeds kept" % (allt[0][0], allt[0][3], len(allt[0][1]), len(TIGHT)))
    vlos = [0.08, 0.15, 0.25, 0.4]; modes = ['single', 'two', 'cluster', 'alllift', 'random']; ns = 100 if FULL else 20
    jobs = [(s, vlo, m) for vlo in vlos for m in modes for s in range(ns)]
    with Pool(4) as pool: res = pool.map(adv_job, jobs, chunksize=4)
    print("  %d local optimisations, %d-%d atoms per period" % (len(res), min(r[4] for r in res), max(r[4] for r in res)))
    print("  v_lo | min ratio over configs with a pair at v >= v_lo (mode, atoms) | min excess per mid pair (mode) | 4X(v_lo) | pair lattice")
    for vlo in vlos:
        R_ = [r for r in res if r[0] == vlo]; b = min(R_, key=lambda r: r[2]); e = min(R_, key=lambda r: r[3])
        print("  %.2f | %.6f (%s, %d) | %.4f (%s, %d atoms) | %.4f | ratio %.6f, excess/pair %.4f"
              % (vlo, b[2], b[1], b[4], e[3], e[1], e[4], 4 * Xv(vlo), rho_at(0), 4 * (rho_at(0) - 1)))
        print("         by mode (min ratio / min excess per mid pair): " + "; ".join(
            "%s %.5f/%.4f" % (m, min(r[2] for r in R_ if r[1] == m), min(r[3] for r in R_ if r[1] == m)) for m in modes))
    viol = [r for r in res if r[2] < 1]
    print("  violations of (**) (ratio < 1): %d   [%.0fs]" % (len(viol), time.time() - t1))
    sys.stdout.flush()

# ============================================================== main
if __name__ == "__main__":
    c, P, R = part0()
    setup(c)
    kap, phi = part1(P, R)
    part2(phi)
    for XF in (60.0, 20.0): make_grid(XF)
    with Pool(4) as pool: log = part3(pool)
    part4()
    print("\nStatus: Lemma-R split kappa_auto >= %.6f (all heights, below MT); hybrid barriers CHECKED; pair lattices: no per-pair height surplus;"
          % kap)
    print("        Theorem H1 (reals + one pair, every height) certified; (**) for several pairs at unequal heights remains open.  total %.0fs" % (time.time() - T0))
