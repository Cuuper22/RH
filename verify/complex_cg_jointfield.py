#!/usr/bin/env python3
"""
complex_cg_jointfield.py -- the joint-field inequality (Conjecture 3.2 of the multi-height memo) for sub-case O2.

Companion of docs/research/complex_cg_jointfield_20261003.md.  Re-uses the certified test rho, the closed forms
of G_v = r + Q_v and the H1 cell machinery of verify/complex_cg_hybrid.py / complex_cg_multiheight.py.

Normalisation: Phi = sum_k W_k G_v(. - x_k) (W_k = 2 m_k);  a cell c costs Psi_c(sup_c Phi^- / 2)  (this is what
the H1 reduction needs; it equals the script convention Psi_c(sup_c (sum_k 4 G_v)^- / 4) of complex_cg_multiheight.py
for W = 2).

  Part 0  re-solve and re-certify rho (as in complex_cg_hybrid.py)
  Part 1  REFUTATION of Conjecture 3.2: finite pair-lattice segments of spacing 2 at v = 0.5 (H1 cells and
          optimal cell partitions; every approximation biased towards a SMALLER damage)
  Part 2  the true O2 ratio on the same configurations (it is far from tight)
  Part 3  periodic pair lattices (exact Poisson forms): H1 cells / optimal cells / component-local bookkeeping
  Part 4  two-pair and random periodic motifs: component-local bookkeeping (Conjecture 3.2')
  Part 5  field-energy duality: tau_0(v) (sharp for signed P, PROVED) and the positive-P constants (NUMERICAL)
Default run: about 6 minutes on 1 core.
"""
import os, sys, time, math
os.environ.setdefault("OMP_NUM_THREADS", "1")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.optimize import minimize
import complex_cg_hybrid as H
import complex_cg_multiheight as M

T0 = time.time()
def el(): return "[%.0fs]" % (time.time() - T0)

# ------------------------------------------------------------------ basic closed forms
def rr(d):
    """r(|d|), with r(0) = 1."""
    d = np.abs(np.atleast_1d(d)).astype(float); out = np.ones_like(d); m = d > 1e-12
    out[m] = H.r_and_dr(d[m])[0]; return out
def cfun(a):
    """c = Fourier transform of r: PL on the LP grid of [0, 2.5]; c = rho on [0,1], c <= 0 on [1, 2.5]."""
    return np.interp(np.abs(a), H.al, H.G['c'], right=0.0)
def Yv(v, d):
    """Y_v(d) = int rho sinh^2(2 pi a v) cos(2 pi a d) (Gauss nodes)."""
    A, Wq, rq = M.nodes()
    return 2 * np.cos(2 * np.pi * np.outer(np.atleast_1d(d), A)) @ (Wq * rq * np.sinh(2 * np.pi * A * v) ** 2)
RMIN_GRID = {}
def rmin_up(L):
    """min of r over the grid {0, 1e-3, ...} of [0, L]: an UPPER bound for min_[0,L] r (makes Psi smaller)."""
    if 'g' not in RMIN_GRID:
        g = np.arange(0, 1.2, 1e-3); RMIN_GRID['g'] = np.minimum.accumulate(rr(g))
    return RMIN_GRID['g'][min(int(L / 1e-3 + 1e-9), len(RMIN_GRID['g']) - 1)]

def components(f):
    neg = f < 0; dd = np.diff(np.r_[0, neg.astype(int), 0]); return list(zip(np.where(dd == 1)[0], np.where(dd == -1)[0]))

def damage_H1(f, h, lmax, rminf):
    """H1 cells: each component of {Phi<0} cut into equal pieces of length <= lmax; sum Psi_c(sup_c Phi^-/2)."""
    tot = 0.0
    for a, b in components(f):
        L = (b - a) * h; npc = max(1, int(math.ceil(L / lmax - 1e-12))); e = np.linspace(a, b, npc + 1).round().astype(int)
        for t in range(npc):
            if e[t + 1] > e[t]:
                tot += H.Psi_exact(np.array([-f[e[t]:e[t + 1]].min() / 2]), rminf((e[t + 1] - e[t]) * h))[0]
    return tot

def damage_DP(f, h, step=0.01, dmax=1.02, rminf=rmin_up):
    """best partition of every component into pieces of length <= dmax with cut points on a mesh 'step' (DP)."""
    tot = 0.0; s = max(1, int(round(step / h)))
    for a, b in components(f):
        cuts = list(range(a, b, s)) + [b]; m = len(cuts); best = [0.0] + [np.inf] * (m - 1)
        for j in range(1, m):
            for i in range(j - 1, -1, -1):
                L = (cuts[j] - cuts[i]) * h
                if L > dmax: break
                rc = rminf(L)
                if rc <= 0: break
                val = best[i] + H.Psi_exact(np.array([-f[cuts[i]:cuts[j]].min() / 2]), rc)[0]
                best[j] = min(best[j], val)
        tot += best[-1]
    return tot

def pen(w): return np.where(w <= 1, 0, w * w - 2 * w)
def local_min(fx, xs, step=0.02, starts=6, seed=1):
    """component-local exact functional  min over integer real configurations in the component of
       sum(W^2 - cost) + sum_{j != k} W_j W_k r + 2 sum W_j Phi(x_j)
    (NUMERICAL: exhaustive over <= 2 atoms on a mesh, plus greedy unit-weight local search from several starts)."""
    rng = np.random.default_rng(seed)
    idx = np.arange(0, len(xs), max(1, int(round(step / (xs[1] - xs[0]))))); X = xs[idx]; F = fx[idx]; n = len(X)
    R = rr((X[:, None] - X[None, :]).ravel()).reshape(n, n); np.fill_diagonal(R, 0.0)
    wmax = int(2 * max(0.0, -F.min()) + 4)
    w1 = np.arange(1, wmax + 1); best = min(0.0, float(((pen(w1))[None, :] + 2 * w1[None, :] * F[:, None]).min()))
    ws = np.unique(np.r_[np.arange(1, min(wmax, 12) + 1), np.round(np.geomspace(13, max(wmax, 13), 20))]).astype(int)
    for a in ws:
        for b in ws:
            val = pen(a) + pen(b) + 2 * a * b * R + 2 * a * F[:, None] + 2 * b * F[None, :]
            np.fill_diagonal(val, np.inf); best = min(best, float(val.min()))
    for s in range(starts):
        w = np.zeros(n, int)
        if s > 0: k = rng.integers(0, n); w[k] = max(1, int(-F[k] + 1))
        val = lambda w: float(pen(w).sum() + w @ R @ w + 2 * w @ F); cur = val(w); imp = True
        while imp:
            imp = False; Rw = R @ w
            for dl in (1, -1):
                wn = w + dl; dv = np.where(wn >= 0, pen(np.maximum(wn, 0)) - pen(w) + 2 * dl * Rw + 2 * dl * F, np.inf)
                i = int(np.argmin(dv))
                if dv[i] < -1e-12: w[i] += dl; cur += dv[i]; imp = True; break
            if not imp:
                for i in np.nonzero(w)[0]:
                    for j in (i - 1, i + 1):
                        if 0 <= j < n:
                            w2 = w.copy(); w2[j] += w2[i]; w2[i] = 0
                            if val(w2) < cur - 1e-12: w, cur, imp = w2, val(w2), True; break
                    if imp: break
        best = min(best, cur)
    return best

# ------------------------------------------------------------------ Part 1: refutation on finite segments
def segment_field(v, xk, W, h=1e-3, pad=60.0):
    """joint field Phi on the grid x0 + i h (x0 = min xk - pad), exact closed forms on lattice-aligned distances."""
    x0 = xk.min() - pad; N = int(round((xk.max() + pad - x0) / h)) + 1
    ik = np.round((xk - x0) / h).astype(int); assert np.allclose(x0 + ik * h, xk)
    Gt = M.G_u(v, np.maximum(np.arange(N) * h, 1e-9))
    f = np.zeros(N); ii = np.arange(N)
    for i, w in zip(ik, W): f += w * Gt[np.abs(ii - i)]
    return x0 + ii * h, f

def part1():
    print("\nPart 1: Conjecture 3.2 on pair-lattice segments of spacing 2 (W = 2 at x = 0, 2, ..., 2(n-1)), v = 0.5")
    print("  LHS = sum_c Psi_c(sup_c Phi^-/2), RHS = E_P + pair r-bonds + sum W(W-2) (= 0 here).  Grid h = 1e-3, window +-60;")
    print("  rho_c = grid minimum of r on [0, d_c] (>= true minimum), grid sup of Phi^- (<= true sup), tail cells omitted:")
    print("  every approximation makes the LHS SMALLER.")
    v = 0.5; out = []
    for n in (8, 20, 40):
        xk = 2.0 * np.arange(n); W = 2.0 * np.ones(n)
        d = xk[:, None] - xk[None, :]
        EP = float(np.sum(4 * Yv(v, d.ravel())))
        bonds = float(np.sum(4 * rr(d.ravel())) - 4 * n)
        xs, f = segment_field(v, xk, W)
        dH = {l: damage_H1(f, 1e-3, l, rmin_up) for l in (0.5, 0.6, 0.7)}
        dDP = damage_DP(f, 1e-3)
        den = EP + bonds
        print("  n = %2d: E_P = %9.4f, bonds = %.5f | H1 cells l=0.5: %9.4f (ratio %.4f), l=0.6: %.4f, l=0.7: %.4f, best l: ratio %.4f | optimal cells: %9.4f (ratio %.4f)"
              % (n, EP, bonds, dH[0.5], dH[0.5] / den, dH[0.6] / den, dH[0.7] / den, min(dH.values()) / den, dDP, dDP / den))
        out.append((n, min(dH.values()) / den, dDP / den))
    print("  -> ratio > 1 from n = 20 on: Conjecture 3.2 is REFUTED (with H1 cells and with optimal cell partitions).  %s" % el())
    sys.stdout.flush(); return out

# ------------------------------------------------------------------ Part 2: the true O2 ratio there
def per_sigma(xr, wr, v, L, Wp=2.0):
    """periodic Sigma per period / cost per period: pairs W=Wp at 0 (period L), reals xr with weights wr."""
    ks = np.arange(-int(L), int(L) + 1); a = ks / L; m = np.abs(a) < 1; a = a[m]
    T = Wp * np.cosh(2 * np.pi * a * v) + (wr[None, :] * np.exp(2j * np.pi * np.outer(a, xr))).sum(1)
    cost = 2 * Wp + sum(1 if w == 1 else 2 * w for w in wr)
    return np.sum(H.rho_at(a) * np.abs(T) ** 2) / L / cost

def part2():
    print("\nPart 2: the true inequality (**) on the same configurations (Sigma_Z(rho)/cost; NUMERICAL)")
    v = 0.5
    for n in (20, 40):
        xk = 2.0 * np.arange(n)
        for w in (1, 2, 3, 4):
            xr = xk[:-1] + 1.0; x = np.r_[xk, xr]; vv = np.r_[v + 0 * xk, 0 * xr]; Wt = np.r_[2 + 0 * xk, w + 0 * xr]
            isp = np.r_[np.ones(n, bool), np.zeros(n - 1, bool)]
            print("  segment n = %d, v = 0.5, reals of multiplicity %d at the field minima x = 1, 3, ...: Sigma/cost = %.4f" % (n, w, M.Sig(x, vv, Wt) / M.cost(Wt, isp)))
    rng = np.random.default_rng(3)
    for v, L in ((0.5, 2.0), (1.0, 2.0), (0.7, 1.75)):
        best = (np.inf, None, None)
        for nr in (1, 2):
            for wr in ([1], [2], [3], [4], [6], [8], [12], [16], [24]) if nr == 1 else ([1, 1], [2, 2], [3, 3], [2, 4], [4, 4], [6, 6], [8, 8], [12, 12]):
                wr = np.array(wr, float)
                for t in range(3):
                    r = minimize(lambda x: per_sigma(x, wr, v, L), L / 2 + 0.3 * rng.standard_normal(nr), method='Nelder-Mead', options=dict(xatol=1e-6, fatol=1e-10))
                    if r.fun < best[0]: best = (r.fun, wr, np.mod(r.x, L))
        print("  periodic lattice v = %.2f, L = %.2f, <= 2 reals per period, multiplicities <= 24: min Sigma/cost = %.4f (reals %s at %s)"
              % (v, L, best[0], best[1].astype(int), np.round(best[2], 3)))
    print("  -> (**) holds there with margin >= 40%%: the failure in Part 1 is the bookkeeping's, not the inequality's.  %s" % el())
    sys.stdout.flush()

# ------------------------------------------------------------------ Part 3/4: periodic lattices and motifs (Poisson)
def per_field(v, L, xs, pos=(0.0,), Wts=(2.0,)):
    """periodic joint field of the pairs pos + L Z (weights Wts) by Poisson summation: (1/L) sum_k Ghat(k/L) T(k/L) e(k x/L)."""
    k = np.arange(-int(2.5 * L), int(2.5 * L) + 1); a = k / L
    Gh = cfun(a) + H.rho_at(a) * (np.cosh(2 * np.pi * a * v) - 1)
    T = (np.array(Wts)[None, :] * np.exp(-2j * np.pi * np.outer(a, pos))).sum(1)
    return np.real(np.exp(2j * np.pi * np.outer(xs, a)) @ (Gh * T)) / L

def per_resource(v, L, pos=(0.0,), Wts=(2.0,)):
    """per period: E_P, pair-pair r-bonds, sum W(W-2)."""
    k = np.arange(-int(2.5 * L), int(2.5 * L) + 1); a = k / L
    T = (np.array(Wts)[None, :] * np.exp(2j * np.pi * np.outer(a, pos))).sum(1)
    E = np.sum(H.rho_at(a) * np.sinh(2 * np.pi * a * v) ** 2 * np.abs(T) ** 2) / L
    bonds = np.sum(cfun(a) * np.abs(T) ** 2) / L - np.sum(np.array(Wts) ** 2)
    return E, bonds, sum(w * (w - 2) for w in Wts)

def per_ratios(v, L, pos=(0.0,), Wts=(2.0,), h=1e-3, which=('H1', 'DP', 'loc')):
    xs = np.arange(0, L, h); f = per_field(v, L, xs, pos, Wts)
    i0 = int(np.argmax(f)); f = np.r_[f[i0:], f[:i0]]; xs = np.r_[xs[i0:], xs[:i0] + L]
    E, b, sl = per_resource(v, L, pos, Wts); den = E + b + sl; res = {}
    if 'H1' in which: res['H1'] = min(damage_H1(f, h, l, rmin_up) for l in (0.5, 0.6, 0.7)) / den
    if 'DP' in which: res['DP'] = damage_DP(f, h) / den
    if 'loc' in which: res['loc'] = sum(-local_min(f[a:b], xs[a:b]) for a, b in components(f)) / den
    return res, f.min()

def part3():
    print("\nPart 3: infinite pair lattices of spacing L (W = 2) at height v, per period (exact Poisson forms).  Ratios damage/(E_P + bonds):")
    print("  H1 = H1 cells (best l in {0.5,0.6,0.7}); DP = optimal partition into cells <= 1.02 (mesh 0.01); loc = component-local exact functional (Conj. 3.2')")
    Ls = (1.25, 1.5, 1.75, 2.0, 2.5, 3.0, 4.0, 6.0); worst = {'H1': 0, 'DP': 0, 'loc': 0}
    print("  %5s | " % "v\\L" + " | ".join("%17.2f" % L for L in Ls))
    for v in (0.2, 0.3, 0.5, 0.7, 1.0, 1.5, 2.0):
        row = []
        for L in Ls:
            res, fm = per_ratios(v, L)
            for kk in worst: worst[kk] = max(worst[kk], res[kk])
            row.append("%5.2f %5.2f %5.2f" % (res['H1'], res['DP'], res['loc']))
        print("  %5.2f | " % v + " | ".join(row)); sys.stdout.flush()
    print("  worst: H1 cells %.3f, optimal cells %.3f, component-local %.3f   %s" % (worst['H1'], worst['DP'], worst['loc'], el()))

def part4():
    print("\nPart 4: periodic motifs (component-local bookkeeping, Conj. 3.2'; NUMERICAL)")
    worst = [0, 0, None]; ncase = 0
    for v in (0.2, 0.3, 0.5, 0.7, 1.0, 1.5):
        for L in (2.0, 3.0, 4.0, 5.0):
            for d in (0.25, 0.5, 0.75, 1.0, 1.25):
                if d >= L - 0.2: continue
                res, _ = per_ratios(v, L, (0.0, d), (2.0, 2.0), which=('H1', 'loc')); ncase += 1
                if res['loc'] > worst[1]: worst[2] = (v, L, d)
                worst[0] = max(worst[0], res['H1']); worst[1] = max(worst[1], res['loc'])
    print("  two pairs per period {0, d} + L Z (v in [0.2,1.5], L in [2,5], d in [0.25,1.25], %d cases): worst H1 %.3f, worst component-local %.3f at (v,L,d) = %s"
          % (ncase, worst[0], worst[1], worst[2]))
    rng = np.random.default_rng(7); worst = [0, 0]
    for t in range(60):
        v = rng.choice([0.15, 0.3, 0.5, 0.8, 1.2]); L = rng.uniform(3, 8); k = rng.integers(2, 5)
        pos = tuple(np.sort(rng.uniform(0, L, k))); W = tuple(2.0 * rng.integers(1, 3, k))
        res, _ = per_ratios(v, L, pos, W, which=('H1', 'loc'))
        worst = [max(worst[0], res['H1']), max(worst[1], res['loc'])]
    print("  60 random motifs (2-4 pairs, W in {2,4}, period 3-8): worst H1 %.3f, worst component-local %.3f   %s" % (worst[0], worst[1], el()))
    sys.stdout.flush()

# ------------------------------------------------------------------ Part 5: field-energy duality constants
def part5():
    print("\nPart 5: field-energy duality at one point.  Lemma 5.1 of the memo (PROVED): Phi_Q(y)^2 <= tau_0(v) E_P, tau_0 = int rho tanh^2(pi a v),")
    print("  sharp over signed P.  Positive P (NUMERICAL, convex QP over densities nu >= 0 on [-6, 6], mesh 0.1; window-limited, so lower bounds):")
    print("  kappa_+(v) = sup Phi_Q^-(0)^2 / E_P ;  kappa(v) = sup Phi^-(0)^2 / (E_P + pair r-bonds)  (continuum limit, integrality irrelevant at scale)")
    A, Wq, rq = M.nodes()
    t = np.arange(-6.0, 6.0 + 1e-9, 0.1); n = len(t); d = t[:, None] - t[None, :]
    Rb = rr(d.ravel()).reshape(n, n)
    rng = np.random.default_rng(11); worst_gram = 0.0
    for v in (0.2, 0.5, 1.0, 2.0):
        tau0 = 2 * np.sum(Wq * rq * np.tanh(np.pi * A * v) ** 2)
        K = Yv(v, d.ravel()).reshape(n, n)
        qQ = 2 * np.cos(2 * np.pi * np.outer(t, A)) @ (Wq * rq * (np.cosh(2 * np.pi * A * v) - 1))
        qG = M.G_u(v, np.maximum(np.abs(t), 1e-9))
        vals = []
        for q, KK in ((qQ, K), (qG, K + Rb)):
            x0 = np.maximum(-q, 0) + 1e-6; x0 /= (-q @ x0); sc = 1.0 / np.max(np.abs(KK))
            r = minimize(lambda x: sc * x @ KK @ x, x0, jac=lambda x: 2 * sc * KK @ x, method='SLSQP',
                         constraints=[dict(type='eq', fun=lambda x: -q @ x - 1, jac=lambda x: -q)], bounds=[(0, None)] * n,
                         options=dict(maxiter=500, ftol=1e-15))
            vals.append(1.0 / (r.x @ KK @ r.x))
        single = np.max(np.maximum(-qQ, 0) ** 2) / K[0, 0]
        # sanity of Lemma J1 on random signed sums at random points
        for trial in range(20):
            k = rng.integers(2, 8); xk = rng.uniform(-5, 5, k); Wk = rng.uniform(-3, 3, k); ys = rng.uniform(-6, 6, 4); b = rng.standard_normal(4)
            EP = Wk @ Yv(v, (xk[:, None] - xk[None, :]).ravel()).reshape(k, k) @ Wk
            PhiQ = np.array([Wk @ (2 * np.cos(2 * np.pi * np.outer(y - xk, A)) @ (Wq * rq * (np.cosh(2 * np.pi * A * v) - 1))) for y in ys])
            Mm = (2 * np.cos(2 * np.pi * np.outer((ys[:, None] - ys[None, :]).ravel(), A)) @ (Wq * rq * np.tanh(np.pi * A * v) ** 2)).reshape(4, 4)
            worst_gram = max(worst_gram, (b @ PhiQ) ** 2 / (EP * (b @ Mm @ b)))
        print("  v = %.1f: tau_0 = %.4f | kappa_+ >= %.4f | kappa >= %.4f | one pair alone: max Q_v^-(t)^2/X(v) = %.4f" % (v, tau0, vals[0], vals[1], single))
    print("  Lemma 5.1 check on random signed configurations: max (sum b Phi_Q)^2 / (E_P b'Mb) = %.6f (<= 1)   %s" % (worst_gram, el()))
    sys.stdout.flush()

# ------------------------------------------------------------------ Part 6: the s-hat term at large heights (HEURISTIC)
def part6():
    from scipy.integrate import quad
    print("\nPart 6: continuum one-layer configurations: pairs with density Lambda*nu, nu = beta - b >= 0, one real atom of weight Lambda at 0,")
    print("  b = FT^{-1}[sech(2 pi a v)] = sech(pi x/(2v))/(2v), beta = sech(pi theta x/(2v))/(2v) (theta < 1).  Then S_Z/Lambda = c * beta^ exactly, and")
    print("  [Sigma_Z(rho) - int shat |S_Z0|^2]/Lambda^2 = Q = int rho c^2 |beta^|^2 - int shat |1 + nu^|^2   (order Lambda^2; costs are O(Lambda))")
    rho = lambda a: float(H.rho_at(a))
    shat = lambda a: max(0.0, -float(cfun(a))) if abs(a) > 1 else 0.0
    print("  int shat = %.6f  (= s(0) = R - 1)" % (2 * quad(shat, 1, 2.5, limit=400, points=list(np.arange(1.01, 2.5, 0.01)[:80]))[0]))
    def sech(x): return 1 / math.cosh(x) if abs(x) < 700 else 0.0
    for v in (10, 20, 50, 66, 70, 100, 200):
        th = 0.5
        f1 = lambda a: rho(a) / th ** 2 * ((1 + math.exp(-4 * math.pi * a * v)) / (1 + math.exp(-4 * math.pi * a * v / th))) ** 2 * math.exp(-4 * math.pi * a * v * (1 / th - 1))
        I1 = 2 * quad(f1, 0, 1, limit=400, points=[0.001, 0.01, 0.05])[0]
        f2 = lambda a: shat(a) * (1 + sech(2 * math.pi * a * v / th) / th - sech(2 * math.pi * a * v)) ** 2
        I2 = 2 * quad(f2, 1, 2.5, limit=400)[0]
        print("  v = %3d, theta = 1/2: int rho c^2 |beta^|^2 = %.5f, s-hat term = %.5f, Q = %+.5f" % (v, I1, I2, I1 - I2))
    print("  -> Q < 0 for v >~ 66: dropping int shat|S_Z0|^2 (H1-type reductions, 3.2, 3.2') loses (**) at order Lambda^2 there (HEURISTIC transfer)   %s" % el())
    sys.stdout.flush()

# ------------------------------------------------------------------ main
if __name__ == "__main__":
    c, P, R = H.part0(); H.setup(c)
    print("  rho(1/2) = %.4f, s(0) = R - 1 = %.5f, r(0.37) = %.4f, r(0.736) = %.4f, rmin(0.5) >= %.4f" % (H.rho_at(0.5), R - 1, rr(0.37)[0], rr(0.736)[0], H.rmin_lo(0.5)[0]))
    part1(); part2(); part3(); part4(); part5(); part6()
    print("\nStatus: Conjecture 3.2 (joint field with H1 cells) REFUTED (Part 1); (**) itself holds with margin on the refuting")
    print("        configurations (Part 2); component-local version 3.2' NUMERICAL (Parts 3-4); O2 and (**) remain OPEN.  total %.0fs" % (time.time() - T0))
