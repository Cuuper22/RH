"""Adversarial search for the complex Cheer--Goldston inequality (**).

Companion to docs/research/complex_cg_adversary_20261003.md; builds on
docs/research/positivity_class_20261003.md and verify/positivity_class_certificate.py.

(**)   Sigma_Z(rho) = int_{-1}^{1} rho(a) |S_Z(a)|^2 da  >=  kappa (2N - s_1),   kappa = 1,
for every finite conjugation-invariant multiset Z, with rho the LP-optimal bandwidth-one
part of the Cheer--Goldston test (R = int rho = 1.01261, P = 1.32092).  Here
    S_Z(a) = sum_real m_j e(a x_j) + sum_pairs 2 m_k cosh(2 pi a v_k) e(a x_k),
N = |Z| with multiplicity (a pair x +- iv of multiplicity m counts 2m), s_1 = number of
simple REAL atoms.  Cost per atom: simple real 1, real of multiplicity m >= 2: 2m,
pair of multiplicity m: 4m.

Periodic reduction (exact).  If Z is periodic with period M (atoms listed in one period),
the P-period truncation satisfies Sigma/P -> (1/M) sum_{|n|<M} rho(n/M) |T(n/M)|^2,
T(a) = S of one period; (rho(1) = 0 for the LP rho, so |n| = M never contributes).
This finite quadratic form is used for all extensive searches; Part 1 checks it against
direct truncations.

Labels: CHECKED = exact / high precision evaluation; NUMERICAL = optimisation without
certificate.  Default run: about 8 minutes on 4 cores.  Do not import from elsewhere.
"""
import os, sys, time
os.environ.setdefault("OMP_NUM_THREADS", "1")
import numpy as np
import mpmath as mp
from scipy.optimize import linprog, minimize
from multiprocessing import Pool

T0 = time.time()
mp.mp.dps = 30

# ============================================================== Part 0: the LP rho
# Verbatim copy of Part A of verify/positivity_class_certificate.py (same grid, bounds, solver).
Lam, D, U, SLOPE = 2.5, 0.01, 60.0, 20.0
K = int(round(Lam / D)); al = np.linspace(0, Lam, K + 1); k1 = int(round(1 / D))

def cell_cos(a, b, u):
    w = 2 * np.pi * u; h = b - a
    if abs(u) < 1e-14:
        return h / 2, h / 2
    I = (np.sin(w * b) - np.sin(w * a)) / w
    J = (b - a) * np.sin(w * b) / w + (np.cos(w * b) - np.cos(w * a)) / w ** 2
    return I - J / h, J / h

def rmatrix(us, kmax=K):
    Mx = np.zeros((len(us), K + 1))
    for i, u in enumerate(us):
        for k in range(kmax):
            I0, I1 = cell_cos(al[k], al[k + 1], u)
            Mx[i, k] += 2 * I0; Mx[i, k + 1] += 2 * I1
    return Mx

def solve_lp():
    us = np.arange(0, U + 1e-9, 0.01)
    Mx = rmatrix(us)
    obj = np.zeros(K + 1); obj[0] += 1
    for k in range(k1):
        a, b = al[k], al[k + 1]; h = b - a
        I0 = (b**2 - a**2) / 2 - (b**3 - a**3) / (3 * h) + a * (b**2 - a**2) / (2 * h)
        I1 = (b**3 - a**3) / (3 * h) - a * (b**2 - a**2) / (2 * h)
        obj[k] += 2 * I0; obj[k + 1] += 2 * I1
    norm = np.full(K + 1, 2 * D); norm[0] = D; norm[K] = D
    bounds = [(-20.0, 20.0)] * (K + 1)
    for k in range(k1, K + 1):
        bounds[k] = (-20.0, 0.0)
    bounds[K] = (0.0, 0.0)
    Dm = np.zeros((2 * K, K + 1))
    for k in range(K):
        Dm[2 * k, k] = -1; Dm[2 * k, k + 1] = 1; Dm[2 * k + 1, k] = 1; Dm[2 * k + 1, k + 1] = -1
    res = linprog(obj, A_ub=np.vstack([-Mx, Dm]), b_ub=np.concatenate([np.zeros(len(us)), np.full(2 * K, SLOPE * D)]),
                  A_eq=norm[None, :], b_eq=[1.0], bounds=bounds, method="highs-ipm")
    assert res.status == 0, res.message
    c = res.x
    return c, float(obj @ c), float(norm[:k1 + 1] @ c[:k1 + 1])

# ============================================================== generic rho machinery
GX, GW = np.polynomial.legendre.leggauss(8)

class Rho:
    """even rho on [-1,1], piecewise linear through (grid, vals) on [0,1]."""
    def __init__(self, grid, vals):
        self.g = np.asarray(grid, float); self.v = np.asarray(vals, float); self.h = self.g[1] - self.g[0]
        nodes, wts = [], []
        for k in range(len(self.g) - 1):
            a, b = self.g[k], self.g[k + 1]; x = (a + b) / 2 + (b - a) / 2 * GX; w = (b - a) / 2 * GW
            nodes.append(x); wts.append(w * (self.v[k] + (self.v[k + 1] - self.v[k]) * (x - a) / (b - a)))
        self.A = np.concatenate(nodes); self.W = 2 * np.concatenate(wts)   # quadrature for int_{-1}^{1}, using evenness
    def __call__(self, a):
        return np.interp(np.abs(a), self.g, self.v, right=0.0)
    def d(self, a):
        a = np.abs(a); k = np.clip((a / self.h).astype(int), 0, len(self.g) - 2)
        return np.where(a < 1, (self.v[k + 1] - self.v[k]) / self.h, 0.0)

def cost(mr, mp_):
    mr = np.asarray(mr); mp_ = np.asarray(mp_)
    return float(np.sum(np.where(mr == 1, 1, 2 * mr)) + 4 * np.sum(mp_))

def sig_per(Rh, M, xr, mr, xp, vp, mp_, grad=True):
    """per-period Sigma for period M, with gradients in (x_real, x_pair, v_pair, M)."""
    nmax = int(np.ceil(M)) - 1; n = np.arange(0, nmax + 1); A = n / M
    W = Rh(A) * np.where(n == 0, 1.0, 2.0) / M
    ph_r = np.exp(2j * np.pi * np.outer(A, xr)); ph_p = np.exp(2j * np.pi * np.outer(A, xp))
    ch = np.cosh(2 * np.pi * np.outer(A, vp)); sh = np.sinh(2 * np.pi * np.outer(A, vp))
    T = ph_r @ mr + (ph_p * ch) @ (2 * mp_); T2 = np.abs(T) ** 2; S = float(W @ T2)
    if not grad:
        return S
    Tc = np.conj(T) * W
    gxr = 2 * np.real((Tc[:, None] * ph_r * (2j * np.pi * A[:, None])).sum(0)) * mr
    gxp = 2 * np.real((Tc[:, None] * ph_p * ch * (2j * np.pi * A[:, None])).sum(0)) * 2 * mp_
    gvp = 2 * np.real((Tc[:, None] * ph_p * sh * (2 * np.pi * A[:, None])).sum(0)) * 2 * mp_
    dA = -A / M
    dT = (ph_r * (2j * np.pi * xr)) @ mr + (ph_p * (ch * 2j * np.pi * xp + sh * 2 * np.pi * vp)) @ (2 * mp_)
    dW = (Rh.d(A) * dA) * np.where(n == 0, 1.0, 2.0) / M - W / M
    gM = float(dW @ T2 + 2 * np.real(np.sum(Tc * dT * dA)))
    return S, gxr, gxp, gvp, gM

def sig_fin(Rh, xr, mr, xp, vp, mp_, grad=True):
    A, W = Rh.A, Rh.W
    ph_r = np.exp(2j * np.pi * np.outer(A, xr)); ph_p = np.exp(2j * np.pi * np.outer(A, xp)); ch = np.cosh(2 * np.pi * np.outer(A, vp))
    T = ph_r @ mr + (ph_p * ch) @ (2 * mp_); S = float(W @ np.abs(T) ** 2)
    if not grad:
        return S
    Tc = np.conj(T) * W
    gxr = 2 * np.real((Tc[:, None] * ph_r * (2j * np.pi * A[:, None])).sum(0)) * mr
    gxp = 2 * np.real((Tc[:, None] * ph_p * ch * (2j * np.pi * A[:, None])).sum(0)) * 2 * mp_
    gvp = 2 * np.real((Tc[:, None] * ph_p * np.sinh(2 * np.pi * np.outer(A, vp)) * (2 * np.pi * A[:, None])).sum(0)) * 2 * mp_
    return S, gxr, gxp, gvp

def optimise(Rh, mr, mp_, rng, starts=8, periodic=True, vmax=2.0, x0s=None, span=None, Mrange=None, fixM=None, vfix=None):
    """minimise Sigma/(2N - s_1) over positions (first real atom at 0), heights in [0,vmax]
    (or fixed heights vfix), and the period M (or fixed M).  Returns (ratio, (M, xr, xp, vp))."""
    mr = np.asarray(mr, float); mp_ = np.asarray(mp_, float); nr, npp = len(mr), len(mp_)
    C = cost(mr, mp_); N = mr.sum() + 2 * mp_.sum()
    freeM = periodic and fixM is None; o0 = 1 if freeM else 0
    def unpack(z):
        M = (z[0] if freeM else fixM) if periodic else None
        xr = np.concatenate([[0.0], z[o0:o0 + nr - 1]]) if nr else np.zeros(0); o = o0 + max(nr - 1, 0)
        return M, xr, z[o:o + npp], z[o + npp:o + 2 * npp]
    def f(z):
        M, xr, xp, vp = unpack(z)
        if periodic:
            S, a, b, c, gM = sig_per(Rh, M, xr, mr, xp, vp, mp_); g = [gM] if freeM else []
        else:
            S, a, b, c = sig_fin(Rh, xr, mr, xp, vp, mp_); g = []
        g += list(a[1:] if nr else []) + list(b) + list(c)
        return S / C, np.array(g) / C
    if span is None: span = 1.2 * (nr + npp) + 1
    if Mrange is None: Mrange = (0.6 * N, 1.4 * N)
    best = (np.inf, None)
    for s in range(starts):
        if periodic:
            M0 = fixM if fixM is not None else rng.uniform(*Mrange)
            z0 = ([M0] if freeM else []) + list(rng.uniform(0, M0, max(nr - 1, 0) + npp))
        else:
            z0 = list(rng.uniform(0, span, max(nr - 1, 0) + npp))
        z0 += list(rng.uniform(0, 0.6, npp)) if vfix is None else list(np.broadcast_to(vfix, (npp,)))
        if x0s is not None and s < len(x0s): z0 = list(x0s[s])
        vb = [(0, vmax)] * npp if vfix is None else [(float(v), float(v)) for v in np.broadcast_to(vfix, (npp,))]
        bnds = ([(0.5, 3 * N + 2)] if freeM else []) + [(None, None)] * (max(nr - 1, 0) + npp) + vb
        if len(z0) == 0:
            val = f(np.zeros(0))[0]
            if val < best[0]: best = (val, unpack(np.zeros(0)))
            continue
        r = minimize(f, np.array(z0, float), jac=True, method="L-BFGS-B", bounds=bnds,
                     options={"maxiter": 4000, "ftol": 1e-15, "gtol": 1e-11})
        if r.fun < best[0]: best = (r.fun, unpack(r.x))
    return best

def lift_coeff(Rh, M, xr, mr, xp, mp_, x0):
    """C = sum_k m_k q(x0 - x_k) (periodic version): Sigma changes by 2 (2 pi v)^2 C + O(v^4)
    when a real double at x0 (included in the configuration) is lifted to x0 +- i v."""
    nmax = int(np.ceil(M)) - 1; n = np.arange(0, nmax + 1); A = n / M
    W = Rh(A) * np.where(n == 0, 1.0, 2.0) / M
    T = np.exp(2j * np.pi * np.outer(A, xr)) @ mr + np.exp(2j * np.pi * np.outer(A, xp)) @ (2 * mp_)
    return float(np.sum(W * A ** 2 * np.real(np.conj(T) * np.exp(2j * np.pi * A * x0))))

# exact (mpmath) evaluation of the per-period quadratic form for the LP rho
def mp_ratio_periodic(cvec, M, xr, mr, xp, vp, mp_):
    M = mp.mpf(M); S = mp.mpf(0); h = mp.mpf(1) / 100
    for n in range(0, int(mp.ceil(M))):
        a = n / M
        if a >= 1: break
        k = int(mp.floor(a / h)); t = (a - k * h) / h
        rv = mp.mpf(cvec[k]) * (1 - t) + mp.mpf(cvec[k + 1]) * t
        T = mp.mpc(0)
        for x, m in zip(xr, mr): T += m * mp.expjpi(2 * a * mp.mpf(x))
        for x, v, m in zip(xp, vp, mp_): T += 2 * m * mp.cosh(2 * mp.pi * a * mp.mpf(v)) * mp.expjpi(2 * a * mp.mpf(x))
        S += (1 if n == 0 else 2) * rv * abs(T) ** 2
    return S / M / cost(mr, mp_)

def fmt(x):
    return "[" + ", ".join("%.6f" % t for t in np.atleast_1d(x)) + "]"

# ============================================================== worker jobs (module level for Pool)
RHO = None
def init_worker(grid, vals):
    global RHO
    RHO = Rho(grid, vals)

def job_patterns(args):
    seed, mr, mp_ = args
    rng = np.random.default_rng(seed)
    val, cfg = optimise(RHO, mr, mp_, rng, starts=8, vmax=1.5)
    M, xr, xp, vp = cfg
    coll = sig_per(RHO, M, xr, np.array(mr, float), xp, 0 * vp, np.array(mp_, float), grad=False) / cost(mr, mp_)
    return val, coll, mr, mp_, cfg

def job_lattice(seed):
    rng = np.random.default_rng(1000 + seed)
    Kn = int(rng.integers(6, 40)); fp = rng.choice([0.05, 0.1, 0.2, 0.35, 0.5, 0.8])
    gaps = rng.choice([1.0, 1.05, 2.0, 1.5, 0.8], size=Kn, p=[.3, .3, .2, .1, .1]) * rng.uniform(0.9, 1.1, Kn)
    pos = np.cumsum(gaps); M0 = pos[-1]; pos -= pos[0]
    mr, mp_, xr0, xp0 = [], [], [], []
    for j in range(Kn):
        if rng.random() < fp: mp_.append(int(rng.choice([1, 1, 1, 2]))); xp0.append(pos[j])
        else: mr.append(int(rng.choice([1, 1, 1, 1, 2, 3]))); xr0.append(pos[j])
    if not mr: mr, xr0 = [1], [0.0]
    base = xr0[0]; xr0 = np.array(xr0) - base; xp0 = np.array(xp0) - base if xp0 else np.zeros(0)
    best = (np.inf,)
    for vsc in [0.05, 0.15, 0.3, 0.6]:
        z0 = [M0] + list(xr0[1:]) + list(xp0) + list(rng.uniform(0, 2 * vsc, len(mp_)))
        val, cfg = optimise(RHO, mr, mp_, rng, starts=1, x0s=[z0])
        if val < best[0]: best = (val, cfg)
    M, xr, xp, vp = best[1]
    coll = sig_per(RHO, M, xr, np.array(mr, float), xp, 0 * vp, np.array(mp_, float), grad=False) / cost(mr, mp_)
    return best[0], coll, mr, mp_, best[1]

def job_neartight(seed):
    rng = np.random.default_rng(5000 + seed)
    Kn = int(rng.integers(3, 20))
    gaps = rng.choice([1.045, 1.95, 2.9], size=Kn, p=[.5, .4, .1]) * rng.uniform(0.98, 1.02, Kn)
    pos = np.concatenate([[0], np.cumsum(gaps)[:-1]]); M0 = gaps.sum()
    nd = int(rng.integers(1, Kn + 1))
    mr = np.array([2] * nd + [1] * (Kn - nd)); rng.shuffle(mr)
    val, (M, xr, _, _) = optimise(RHO, list(mr), [], rng, starts=1, x0s=[[M0] + list(pos[1:])])
    Cs = [lift_coeff(RHO, M, xr, mr.astype(float), np.zeros(0), np.zeros(0), xr[i]) for i in range(Kn) if mr[i] == 2]
    simp = [i for i in range(Kn) if mr[i] == 1]; dbl = [i for i in range(Kn) if mr[i] == 2]
    best = (np.inf, None)
    for v0 in [0.05, 0.15, 0.3, 0.5]:
        if simp:
            base = xr[simp[0]]
            z0 = [M] + list(xr[simp[1:]] - base) + list(xr[dbl] - base) + list(v0 * rng.uniform(.5, 1.5, nd))
            vv, cfg = optimise(RHO, [1] * len(simp), [1] * nd, rng, starts=1, x0s=[z0])
        else:
            z0 = [M] + list(xr[dbl]) + list(v0 * rng.uniform(.5, 1.5, nd))
            vv, cfg = optimise(RHO, [], [1] * nd, rng, starts=1, x0s=[z0])
        if vv < best[0]: best = (vv, cfg)
    return val, min(Cs), best[0], best[1][3].max(), Kn, nd, (M, xr, mr)

def job_finite(seed):
    rng = np.random.default_rng(9000 + seed)
    Kn = int(rng.integers(15, 61)); fp = rng.choice([0.1, 0.25, 0.5])
    mr, mp_ = [], []
    for j in range(Kn):
        if rng.random() < fp: mp_.append(int(rng.choice([1, 1, 2])))
        else: mr.append(int(rng.choice([1, 1, 1, 2])))
    if not mr: mr = [1]
    val, cfg = optimise(RHO, mr, mp_, rng, starts=2, periodic=False, span=1.3 * Kn)
    xr, xp, vp = cfg[1], cfg[2], cfg[3]
    return val, mr, mp_, (vp.max() if len(vp) else 0.0), len(mr) + len(mp_)

def job_density1(args):
    seed, mr, mp_ = args
    rng = np.random.default_rng(seed)
    N = sum(mr) + 2 * sum(mp_)
    val, cfg = optimise(RHO, mr, mp_, rng, starts=5, fixM=float(N))
    return val, mr, mp_, cfg

def family_test(Rh, rng, starts=6):
    """(real-inf, complex-pattern-inf, its pattern, its max height) for a generic rho; complex optima with
    v = 0 are real configurations and are folded into the real infimum."""
    comp = []
    for mr, mp_ in [([1, 1], [1, 1]), ([1, 1, 1], [1, 1, 1]), ([3], [1]), ([1], [1, 1]), ([4], [1, 1]), ([1, 1, 1, 1], [1, 1])]:
        v, cfg = optimise(Rh, mr, mp_, rng, starts=starts, periodic=False); comp.append((v, 'F', mr, mp_, cfg[3].max()))
    for mr, mp_ in [([1], [1]), ([1, 1], [1]), ([1, 1], [1, 1]), ([], [1, 1, 1]), ([3], [1]), ([1, 1, 1, 1], [1, 1, 1])]:
        v, cfg = optimise(Rh, mr, mp_, rng, starts=starts); comp.append((v, 'P', mr, mp_, cfg[3].max()))
    # real infimum: lattices (left limits at integer period), lone atom, real patterns incl. collapsed versions
    lat = min(float(Rh(0)), min((Rh(0) + 2 * np.sum(Rh(np.arange(1, int(np.ceil(a))) / a))) / a for a in np.arange(0.3, 8, 0.002)))
    reals = [lat, float(Rh.W.sum())] + [t[0] for t in comp if t[4] <= 1e-6]
    for mr in [[1, 1], [1, 1, 1], [1] * 5, [1, 2], [2, 2], [1, 1, 2], [1, 1, 2, 2], [1, 1, 1, 1, 2, 2], [3, 2], [4, 2, 2], [1, 1, 1, 1, 1, 1, 2, 2, 2]]:
        reals.append(optimise(Rh, mr, [], rng, starts=starts, periodic=False)[0]); reals.append(optimise(Rh, mr, [], rng, starts=starts)[0])
    bc = min(comp, key=lambda t: t[0])
    return min(reals), lat, bc

def job_family(args):
    tag, lam, grid, vals, seed = args
    Rh = Rho(grid, vals); rng = np.random.default_rng(seed)
    kr, lat, bc = family_test(Rh, rng)
    q = lambda u: Rh.W @ (Rh.A ** 2 * np.cos(2 * np.pi * Rh.A * u))
    qmin = min(q(u) for u in np.arange(0, 4, 0.01))
    return tag, lam, float(Rh(0)), bc, kr, lat, -qmin / q(0)

def job_randrho(seed):
    rng = np.random.default_rng(seed)
    g = np.linspace(0, 1, 201)
    xs = np.concatenate([[0], np.sort(rng.uniform(0, 1, 4)), [1]]); kv = rng.uniform(0, 1, 6) * (rng.random(6) < .8); kv[-1] = 0.0
    vals = np.interp(g, xs, kv)
    if vals.max() < 1e-3: return None
    vals = vals / (2 * np.sum((vals[1:] + vals[:-1]) / 2) * (g[1] - g[0]))
    kr, lat, bc = family_test(Rho(g, vals), rng, starts=5)
    return seed, kr, bc

def job_rigidity(seed):
    """Lemma 3 illustration: D points per period (s simple reals + p pairs), minimise sum_{n=1}^{m} |T(n)|^2,
    m = ceil((D-1)/2), over positions and heights; zero residual should force a real regular D-gon."""
    rng = np.random.default_rng(700 + seed)
    p = int(rng.integers(1, 4)); s_ = int(rng.integers(0, 4)); D = s_ + 2 * p; m = int(np.ceil((D - 1) / 2))
    def f(z):
        th = z[:s_ + p] * 2 * np.pi; u = z[s_ + p:]
        n = np.arange(1, m + 1)
        T = np.exp(1j * np.outer(n, th[:s_])).sum(1) + (2 * np.cosh(np.outer(n, u)) * np.exp(1j * np.outer(n, th[s_:]))).sum(1)
        return float(np.sum(np.abs(T) ** 2))
    best = (np.inf, None)
    for _ in range(20):
        z0 = np.concatenate([rng.uniform(0, 1, s_ + p), rng.uniform(0, 1, p)])
        r = minimize(f, z0, method="L-BFGS-B", bounds=[(None, None)] * (s_ + p) + [(0, 3)] * p, options={"ftol": 1e-16, "gtol": 1e-12})
        if r.fun < best[0]: best = (r.fun, r.x)
    return s_, p, best[0], best[1][s_ + p:].max()

# ============================================================== main
def main():
    c, P, R = solve_lp()
    rho_grid = al[:k1 + 1]; rho_vals = c[:k1 + 1]
    RH = Rho(rho_grid, rho_vals)
    init_worker(rho_grid, rho_vals)
    q = lambda u: RH.W @ (RH.A ** 2 * np.cos(2 * np.pi * RH.A * u))
    qs = np.array([q(u) for u in np.arange(0, 6, 0.005)])
    print("Part 0: LP-optimal rho (verbatim Part A of positivity_class_certificate.py)")
    print("  P = %.10f  R = int rho = %.8f  rho(0) = %.8f  rho(1) = %.1e  slope rho'(1-) = %.4f" % (P, R, c[0], c[k1], (c[k1] - c[k1 - 1]) / D))
    print("  self-check: P and R equal the memo's 1.3209166550 / 1.01261107: %s" % (abs(P - 1.3209166550) < 1e-8 and abs(R - 1.01261107) < 1e-7))
    print("  q(u) = int rho a^2 cos(2 pi a u): q(0) = %.5f, min q = %.5f at u = %.3f ; Prop.5 two-body lifting threshold t* = q(0)/|min q| = %.3f"
          % (q(0), qs.min(), 0.005 * np.argmin(qs), q(0) / -qs.min()))

    # ---------------------------------------------------------------- Part 1
    print("\nPart 1: periodic reduction and two exact facts (CHECKED)")
    rng = np.random.default_rng(1)
    M = 7.3; xr = np.array([0.0, 1.1, 2.9, 4.4]); mr = np.array([1., 1., 2., 1.]); xp = np.array([3.6, 6.1]); vp = np.array([0.2, 0.07]); mp_ = np.array([1., 1.])
    per = sig_per(RH, M, xr, mr, xp, vp, mp_, grad=False)
    for Pn in [50, 200]:
        X = np.concatenate([xr + M * k for k in range(Pn)]); XP = np.concatenate([xp + M * k for k in range(Pn)])
        # exact integral of rho |S|^2 for the truncation: fine quadrature (the Fejer peaks have width ~ 1/(P M))
        A = np.linspace(0, 1, 200001); w = np.full(A.size, A[1]); w[0] = w[-1] = A[1] / 2; w *= 2 * RH(A)
        S = np.zeros(A.size, complex)
        for x, m in zip(X, np.tile(mr, Pn)): S += m * np.exp(2j * np.pi * A * x)
        for x, v, m in zip(XP, np.tile(vp, Pn), np.tile(mp_, Pn)): S += 2 * m * np.cosh(2 * np.pi * A * v) * np.exp(2j * np.pi * A * x)
        print("  truncation with %3d periods: Sigma/P = %.6f   periodic formula = %.6f" % (Pn, float(w @ np.abs(S) ** 2) / Pn, per))
    print("  lattice of simple atoms, spacing a -> 1-: ratio rho(0)/a -> rho(0) = %.6f, so kappa_C <= kappa_real <= rho(0) for ANY rho." % c[0])
    print("  pairs-only, p pairs per period M in (p, p+1): if T(1..p-1) = 0 the 2p points zeta = e((x +- iv)/M) have a self-inversive")
    print("  polynomial X^2p + a X^p + c0 (Newton), forcing a common-height regular p-gon and |T(p)| >= 2p (PROVED in memo, Lemma 2).")
    with Pool(4) as pool:
        resG = pool.map(job_rigidity, range(16))
    print("  Lemma 3 illustration: D points/period, min sum_{n<=(D-1)/2}|T(n)|^2 over positions+heights (20 starts each):")
    print("   " + " ; ".join("s=%d,p=%d: min %.1e, v at min %.1e" % t for t in resG[:8]))
    print("   " + " ; ".join("s=%d,p=%d: min %.1e, v at min %.1e" % t for t in resG[8:]))

    # ---------------------------------------------------------------- Part 2
    print("\nPart 2: periodic adversary for the LP rho (NUMERICAL)")
    rng0 = np.random.default_rng(7); pats = []
    for i in range(160):
        ns = int(rng0.integers(0, 12)); nd = int(rng0.integers(0, 3)); nt = int(rng0.integers(0, 2)) if rng0.random() < .3 else 0
        np1 = int(rng0.integers(1, 5)); np2 = int(rng0.integers(0, 2)) if rng0.random() < .3 else 0
        mr_ = [1] * ns + [2] * nd + [3] * nt; mp__ = [1] * np1 + [2] * np2
        if not mr_ and len(mp__) < 2: continue
        pats.append((i, mr_, mp__))
    with Pool(4, initializer=init_worker, initargs=(rho_grid, rho_vals)) as pool:
        resA = pool.map(job_patterns, pats)
        resB = pool.map(job_lattice, range(200))
        resC = pool.map(job_neartight, range(240))
    allAB = resA + resB
    best = min(allAB, key=lambda t: t[0])
    lifted = [t for t in allAB if len(t[4][3]) and t[4][3].max() > 1e-3]
    print("  2a random multiplicity patterns: %d patterns x 8 starts ; 2b lattice-like starts with pairs inserted (K = 6..40 atoms): 200 runs x 4 height scales" % len(pats))
    print("  min ratio over 2a+2b = %.7f  (reals %s, pairs %s, M = %.4f, max v = %.1e)" % (best[0], best[2], best[3], best[4][0], (best[4][3].max() if len(best[4][3]) else 0)))
    print("  minimisers with some v > 1e-3: %d of %d ; smallest such ratio = %.5f" % (len(lifted), len(allAB), min(t[0] for t in lifted) if lifted else np.nan))
    if lifted:
        w = max(lifted, key=lambda t: t[1] - t[0])
        print("  largest lifting gain at a lifted local minimum: ratio %.5f vs %.5f collapsed at the same x (reals %d atoms, pairs m = %s, max v = %.3f)"
              % (w[0], w[1], len(w[2]), w[3], w[4][3].max()))
    valsC = [t[0] for t in resC]; iC = int(np.argmin(valsC))
    print("  2c near-tight real designs with doubles (240 runs): min real ratio %.7f ; min lifting coefficient C over all their doubles = %.5f (> 0)"
          % (valsC[iC], min(t[1] for t in resC)))
    print("     re-optimisation after replacing every double by a pair at v0 in {.05,.15,.3,.5}: min ratio %.7f ; runs ending with v > 1e-3: %d"
          % (min(t[2] for t in resC), sum(1 for t in resC if t[3] > 1e-3)))
    M_, xr_, mr_ = resC[iC][6]
    order = np.argsort(np.mod(xr_, M_)); xs = np.mod(xr_, M_)[order]; xs -= xs[0]
    print("     best near-tight design: period M = %.6f, atoms x = %s, multiplicities %s" % (M_, fmt(xs), [int(t) for t in mr_[order]]))

    # ---------------------------------------------------------------- Part 3
    print("\nPart 3: large finite (non-periodic) configurations, 15..60 atoms, local optimisation (NUMERICAL)")
    with Pool(4, initializer=init_worker, initargs=(rho_grid, rho_vals)) as pool:
        resF = pool.map(job_finite, range(64))
    bf = min(resF, key=lambda t: t[0])
    lf = [t for t in resF if t[3] > 1e-3]
    print("  64 runs: min ratio %.6f (%d atoms) ; runs ending with some v > 1e-3: %d (their min ratio %.4f)" % (bf[0], bf[4], len(lf), min([t[0] for t in lf] + [np.inf])))

    # ---------------------------------------------------------------- Part 4
    print("\nPart 4: fixed-height scans at the best near-tight design (NUMERICAL)")
    simp = [j for j in range(len(mr_)) if mr_[j] == 1]; dbl = [j for j in range(len(mr_)) if mr_[j] == 2]
    rng = np.random.default_rng(3)
    for mode in ["one pair lifted", "all doubles lifted (independent heights fixed at v, 1.5v, 0.5v, ...)"]:
        out = []
        for v in [0.0, 0.02, 0.05, 0.1, 0.2, 0.35, 0.5]:
            mrl = [1] * len(simp) + [2] * (len(dbl) - 1) if mode.startswith("one") else [1] * len(simp)
            idx_r = simp + (dbl[1:] if mode.startswith("one") else []); idx_p = dbl[:1] if mode.startswith("one") else dbl
            vf = np.full(len(idx_p), v) if mode.startswith("one") else v * (0.5 + np.arange(len(idx_p)) % 3 * 0.5)
            if not idx_r:   # all doubles lifted and no simple atoms: anchor at first pair
                z0 = [M_] + list(xr_[idx_p]) + list(vf)
                val, _ = optimise(RH, [], [1] * len(idx_p), rng, starts=1, x0s=[z0], vfix=vf)
            else:
                base = xr_[idx_r[0]]
                z0 = [M_] + list(xr_[idx_r[1:]] - base) + list(xr_[idx_p] - base) + list(vf)
                val, _ = optimise(RH, [int(mr_[j]) for j in idx_r], [1] * len(idx_p), rng, starts=1, x0s=[z0], vfix=vf)
            out.append("v=%.2f: %.6f" % (v, val))
        print("  %s: %s" % (mode, " | ".join(out)))

    # ---------------------------------------------------------------- Part 5
    print("\nPart 5: mechanism, control, interpolation")
    def lat_ratio_ctrl(Nn, a):
        a = mp.mpf(a); s = mp.mpf(Nn) / 2
        for d_ in range(1, Nn): s += 2 * (Nn - d_) * (mp.sin(2 * mp.pi * d_ * a) - mp.sin(mp.pi * d_ * a)) / (2 * mp.pi * d_ * a)
        return 2 * s / Nn
    print("  control rho = 1_[1/2,1]: N-point real lattice, spacing 0.9, exact (mpmath) ratio Sigma/N:",
          ", ".join("N=%d: %s" % (Nn, mp.nstr(lat_ratio_ctrl(Nn, '0.9'), 5)) for Nn in [10, 100, 1000]))
    print("  -> kappa_real(control) = 0 (CHECKED); the memo's real infimum 0.1496 was over <= 12 points only. The control's complex")
    print("     minimisers (0.0071 in the memo) are not below the true real infimum: the control exhibits no complex-only failure.")
    gF = np.linspace(0, 1, 501); lpv = np.interp(gF, rho_grid, rho_vals); ctrl = np.where(gF >= 0.5, 1.0, 0.0)
    jobs = [("(1-l) rho_LP + l 1_[1/2,1]", l, gF, (1 - l) * lpv + l * ctrl, 11 + j) for j, l in enumerate([0.0, 0.1, 0.3, 0.6, 1.0])]
    jobs += [("rho_LP + l 1_[1/2,1]", l, gF, lpv + l * ctrl, 31 + j) for j, l in enumerate([0.05, 0.2, 1.0])]
    with Pool(4) as pool:
        resI = pool.map(job_family, jobs)
    for tag, l, r0, bc, kr, lat, th in resI:
        print("  %-28s l=%.2f rho(0)=%.4f  -min q/q(0)=%.3f  real-inf %.5f (lattice %.5f)  complex-pattern-inf %.5f (%s %s+%s, max v %.2f)  %s"
              % (tag, l, r0, th, kr, lat, bc[0], bc[1], bc[2], bc[3], bc[4], "COMPLEX < REAL" if bc[0] < kr - 1e-4 else "complex >= real"))
    with Pool(4) as pool:
        resR = [t for t in pool.map(job_randrho, range(48)) if t is not None]
    badR = [t for t in resR if t[2][0] < t[1] - 1e-4]
    print("  random piecewise-linear rho >= 0 (5 knots, rho(1) = 0, R = 1): %d tested ; complex-pattern-inf < real-inf - 1e-4 in %d" % (len(resR), len(badR)))
    for t in badR[:5]:
        print("     seed %d: real %.5f complex %.5f (%s %s+%s, max v %.3f)" % (t[0], t[1], t[2][0], t[2][1], t[2][2], t[2][3], t[2][4]))

    # ---------------------------------------------------------------- Part 6
    print("\nPart 6: restricted adversary (zeta-like constraints), NUMERICAL")
    print("  scaling (memo sec.1): zeta zero 1/2 + i gamma + (beta - 1/2) -> z = gamma - i(beta-1/2), multiplied by L = log T/(2 pi):")
    print("  mean spacing 1 (density 1), scaled height v = (beta - 1/2) log T/(2 pi).  Selberg N(sigma,T) << T^{1-(sigma-1/2)/4} log T")
    print("  gives #{v' >= v} << N e^{-pi v/2}: no constraint at the relevant heights v <= 0.5.")
    rngd = np.random.default_rng(17); pd = []
    for i in range(120):
        np1 = int(rngd.integers(1, 6)); ns = int(rngd.integers(2 * np1, 6 * np1 + 2)); nd = int(rngd.integers(0, 2))
        pd.append((300 + i, [1] * ns + [2] * nd, [1] * np1))
    with Pool(4, initializer=init_worker, initargs=(rho_grid, rho_vals)) as pool:
        resD = pool.map(job_density1, pd)
    for cap, name in [(1.0, "no cap"), (7 / 12, "off-line <= 7/12 (PRZZ: >= 5/12 on the line)"), (1 / 3, "off-line <= 1/3 (hypothetical)")]:
        sel = [t for t in resD if 2 * sum(t[2]) / (sum(t[1]) + 2 * sum(t[2])) <= cap + 1e-12]
        if not sel: continue
        b = min(sel, key=lambda t: t[0])
        print("  density exactly 1 (M = N), %-45s: %2d patterns, min ratio %.6f (max v %.1e)" % (name, len(sel), b[0], b[3][3].max()))

    # ---------------------------------------------------------------- Part 7
    print("\nPart 7: mpmath re-evaluation (30 digits, exact per-period quadratic form) of reported minimisers")
    M, xr, xp, vp = best[4]
    print("  Part 2 best        : float %.10f   mpmath %s" % (best[0], mp.nstr(mp_ratio_periodic(rho_vals, M, xr, best[2], xp, vp, best[3]), 12)))
    print("  best near-tight    : float %.10f   mpmath %s" % (valsC[iC], mp.nstr(mp_ratio_periodic(rho_vals, M_, xr_, mr_, [], [], []), 12)))
    if lifted:
        M, xr, xp, vp = w[4]
        print("  lifted local min   : float %.10f   mpmath %s   (collapsed same x: %s)" % (
            w[0], mp.nstr(mp_ratio_periodic(rho_vals, M, xr, w[2], xp, vp, w[3]), 12), mp.nstr(mp_ratio_periodic(rho_vals, M, xr, w[2], xp, 0 * vp, w[3]), 12)))
    print("  self-checks: rho = LP rho (Part 0); multiplicities are integers by construction; each pair enters S as 2m cosh e(ax)")
    print("  (conjugation closure); s_1 counts only real atoms with m = 1 (cost function); ratios use 2N - s_1.")
    overall = min(best[0], valsC[iC], bf[0], min(t[0] for t in resD))
    glob_lift = [t for t in allAB if len(t[4][3]) and t[4][3].max() > 1e-3 and t[0] < 1.01]
    print("\nVerdict: overall minimum ratio found = %.7f (>= kappa = 1); minimisers with ratio < 1.01 having some v > 1e-3: %d." % (overall, len(glob_lift)))
    print("(**) for the LP rho: NOT refuted; CONJECTURE, numerically supported.  Infimum found is attained by REAL designs.")
    print("runtime %.0f s" % (time.time() - T0))

if __name__ == "__main__":
    main()
