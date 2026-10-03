#!/usr/bin/env python3
"""
complex_cg_multiheight.py -- the multi-height case of the complex Cheer-Goldston inequality (**).

Companion of docs/research/complex_cg_multiheight_20261003.md.  Re-uses the certified test rho of
verify/complex_cg_hybrid.py (same LP, same closed forms).  Parts:

  0  re-solve and re-certify rho (identical to complex_cg_proof.py / complex_cg_hybrid.py)
  1  exact identities (CHECKED to ~1e-13): height-difference form, Abel/layer form, one-layer identity,
     Cauchy-Schwarz bound  Sigma_Z >= Sigma_{Z0} - Sigma_R(rho tanh^2(pi a v))
  2  Theorem C (cluster criterion): no negative cross-height bond => (**); Delta*(u) table
  3  the two minimal open sub-cases: (O2) common height + reals, (O3) two pairs at unequal heights + one real atom:
     targeted local optimisation (NUMERICAL) and the joint-field bookkeeping on pair-lattice segments

Run time of the default run: about 4 minutes on 4 cores.
"""
import os, sys, time, math
os.environ.setdefault("OMP_NUM_THREADS", "1")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.optimize import minimize
from multiprocessing import Pool
import complex_cg_hybrid as H

T0 = time.time()
rng = np.random.default_rng(20261003)

# ------------------------------------------------------------------ exact evaluation on the Gauss nodes
def nodes():
    return H.G['Aq'], H.G['Wq'], H.G['rhoq']

def S_of(x, v, W, A):
    """S_Z(alpha) on nodes A: x positions, v heights (0 for reals), W weights (m for reals, 2m for pairs)."""
    return (W[None, :] * np.cosh(2 * np.pi * np.outer(A, v)) * np.exp(2j * np.pi * np.outer(A, x))).sum(1)

def Sig(x, v, W, g=None):
    """Sigma_Z(rho g) = int rho g |S_Z|^2 (g even weight on nodes, default 1)."""
    A, Wq, rq = nodes(); S = S_of(x, v, W, A)
    gg = 1.0 if g is None else g
    return 2 * np.sum(Wq * rq * gg * np.abs(S) ** 2)

def cost(W, isp):
    return float(np.sum(np.where(isp, 2 * W, np.where(W == 1, 1, 2 * W))))

def random_config(nr, npairs, vmax=1.0, L=6.0):
    x = rng.uniform(0, L, nr + npairs)
    W = np.r_[rng.integers(1, 4, nr), 2 * rng.integers(1, 3, npairs)].astype(float)
    v = np.r_[np.zeros(nr), rng.uniform(0.05, vmax, npairs)]
    isp = np.r_[np.zeros(nr, bool), np.ones(npairs, bool)]
    return x, v, W, isp

# ------------------------------------------------------------------ Part 1: identities
def part1():
    print("\nPart 1: exact identities (CHECKED on random configurations, Gauss nodes, relative error)")
    A, Wq, rq = nodes()
    worst = dict(hd=0.0, abel=0.0, one=0.0, one2=0.0); cs_min = np.inf; cs_cases = []
    for trial in range(60):
        nr, npr = rng.integers(0, 4), rng.integers(2, 5)
        x, v, W, isp = random_config(nr, npr, vmax=1.2)
        Sg = Sig(x, v, W)
        # (a) height-difference form: Sigma = int rho |U|^2 + sum_{j,k} W_j W_k t(0, |v_j - v_k|, Delta_jk)
        U = (W[None, :] * np.sinh(2 * np.pi * np.outer(A, v)) * np.exp(2j * np.pi * np.outer(A, x))).sum(1)
        Phi = 0.0
        for j in range(len(x)):
            Phi += 2 * np.sum(Wq * rq * np.sum(W[None, :] * W[j] * np.cosh(2 * np.pi * np.outer(A, np.abs(v - v[j])))
                                               * np.cos(2 * np.pi * np.outer(A, x - x[j])), 1))
        hd = abs(Sg - (2 * np.sum(Wq * rq * np.abs(U) ** 2) + Phi)) / Sg
        worst['hd'] = max(worst['hd'], hd)
        # (b) Abel / layer form: S = sum_l d_l T_l with T_l the collapsed sum of all atoms at height >= v_l
        hs = np.unique(v); c = np.cosh(2 * np.pi * np.outer(A, hs)); d = np.diff(np.c_[np.zeros(len(A)), c], axis=1)   # d_0 = c_0, d_l = c_l - c_{l-1}
        Sab = sum(d[:, i] * (W[None, v >= hs[i]] * np.exp(2j * np.pi * np.outer(A, x[v >= hs[i]]))).sum(1) for i in range(len(hs)))
        worst['abel'] = max(worst['abel'], abs(2 * np.sum(Wq * rq * np.abs(Sab) ** 2) - Sg) / Sg)
    for trial in range(60):
        # one layer: pairs at a common height vv, reals at 0
        nr, npr = rng.integers(1, 5), rng.integers(1, 5); vv = rng.uniform(0.05, 1.5)
        x, v, W, isp = random_config(nr, npr); v[isp] = vv
        Sg = Sig(x, v, W); c = np.cosh(2 * np.pi * A * vv)
        S0 = Sig(x, 0 * v, W); EP = Sig(x[isp], 0 * v[isp], W[isp], c ** 2 - 1)
        SR = S_of(x[~isp], 0 * v[~isp], W[~isp], A); SP = S_of(x[isp], 0 * v[isp], W[isp], A)
        cross = 2 * 2 * np.sum(Wq * rq * (c - 1) * np.real(SR * np.conj(SP)))
        worst['one'] = max(worst['one'], abs(Sg - (S0 + EP + cross)) / Sg)
        alt = Sig(x, 0 * v, W, c) + Sig(x[isp], 0 * v[isp], W[isp], c * (c - 1)) - Sig(x[~isp], 0 * v[~isp], W[~isp], c - 1)
        worst['one2'] = max(worst['one2'], abs(Sg - alt) / Sg)
        # (c) Cauchy-Schwarz: Sigma_Z >= Sigma_{Z0} - Sigma_R(rho tanh^2(pi a v))
        TR = Sig(x[~isp], 0 * v[~isp], W[~isp], np.tanh(np.pi * A * vv) ** 2)
        gap = Sg - (S0 - TR); cs_min = min(cs_min, gap)
        cs_cases.append((vv, Sg / cost(W, isp), (S0 - TR) / cost(W, isp)))
    print("  (a) Sigma = int rho|U|^2 + sum W_j W_k t(0,|v_j-v_k|,Delta_jk)      max rel. err %.1e" % worst['hd'])
    print("  (b) Abel form S = sum_l (c_l - c_{l-1}) T_l                          max rel. err %.1e" % worst['abel'])
    print("  (c) one layer: Sigma = Sigma_{Z0} + E_P + 2 sum W_j W_k Q_v           max rel. err %.1e" % worst['one'])
    print("      = Sigma_{Z0}(rho cosh) + Sigma_P(rho cosh(cosh-1)) - Sigma_R(rho(cosh-1))   max rel. err %.1e" % worst['one2'])
    print("  (d) CS bound Sigma_Z >= Sigma_{Z0} - Sigma_R(rho tanh^2): min slack over 60 configs %.3e (>= 0: %s)" % (cs_min, cs_min >= -1e-12))
    cs_cases.sort(key=lambda t: t[2] - 1)
    print("      CS lower bound / cost for the 3 worst configs: " + ", ".join("v=%.2f: true %.4f, CS %.4f" % t for t in cs_cases[:3]))
    sys.stdout.flush()

# ------------------------------------------------------------------ Part 2: Theorem C
def G_u(u, D):
    """G_u(Delta) = r(Delta) + Q_u(Delta) on an array D > 0 (closed forms)."""
    r, _, _ = H.r_and_dr(D)
    Ip = H.Ifun(2 * np.pi * (u + 1j * D))[0]; Im = H.Ifun(2 * np.pi * (-u + 1j * D))[0]; I0 = H.Ifun(2j * np.pi * D)[0]
    return r + np.real(Ip + Im - 2 * I0)

def part2():
    print("\nPart 2: Theorem C -- no negative cross-height bond => (**).  Delta*(u) = sup{d : G_u >= 0 on (0, d]}  (NUMERICAL, grid 1e-4)")
    D = np.arange(1e-4, 1.5, 1e-4); out = []
    for u in (0.02, 0.05, 0.08, 0.1, 0.15, 0.2, 0.3, 0.4, 0.5, 0.7, 1.0, 1.5, 2.0, 3.0, 5.0):
        g = G_u(u, D); bad = np.where(g < 0)[0]
        ds = D[bad[0]] if len(bad) else D[-1]; out.append((u, ds))
    print("  u      : " + " ".join("%6.2f" % o[0] for o in out))
    print("  Delta* : " + " ".join("%6.4f" % o[1] for o in out))
    print("  PROVED: Delta*(u) >= 1/4 for every u (cos(2 pi a Delta) >= 0 for |a| <= 1, |Delta| <= 1/4, and r >= 0); Delta*(u) -> 1/4 as u -> oo.")
    # sanity: random clusters of diameter <= 1/4 with reals, arbitrary heights: ratio >= 1 and the certificate of Thm C
    worst = np.inf; worstc = np.inf
    for trial in range(300):
        nr, npr = rng.integers(0, 3), rng.integers(2, 5)
        x, v, W, isp = random_config(nr, npr, vmax=2.0, L=0.25)
        c = cost(W, isp); Sg = Sig(x, v, W)
        A, Wq, rq = nodes()
        U = (W[None, :] * np.sinh(2 * np.pi * np.outer(A, v)) * np.exp(2j * np.pi * np.outer(A, x))).sum(1)
        cert = 2 * np.sum(Wq * rq * np.abs(U) ** 2) + np.sum(W ** 2) - c   # drops the nonnegative bonds and int shat|S0|^2
        worst = min(worst, Sg / c); worstc = min(worstc, cert)
    print("  300 random clusters (diameter <= 1/4, 2-4 pairs at heights in [0.05, 2], 0-2 reals): min ratio %.4f, min certificate int rho|U|^2 + sum(W^2 - cost) = %.3e (>= 0: %s)"
          % (worst, worstc, worstc >= -1e-12))
    sys.stdout.flush()
    return out

# ------------------------------------------------------------------ Part 3: the minimal open sub-cases (NUMERICAL)
def ratio_fn(z, isp, W, vfix, nvar):
    x = z[:len(W)]; v = np.zeros(len(W))
    if vfix is None: v[isp] = np.clip(z[len(W):len(W) + nvar], 0.05, 2.0)
    else: v[isp] = vfix
    return Sig(x, v, W) / cost(W, isp)

def opt_job(args):
    kind, seed, W, isp, vfix = args
    r = np.random.default_rng(seed); W = np.asarray(W, float); isp = np.asarray(isp, bool); nvar = int(isp.sum())
    best = (np.inf, None)
    for s in range(6):
        z0 = np.r_[r.uniform(0, 4, len(W)), (r.uniform(0.05, 1.5, nvar) if vfix is None else [])]
        res = minimize(ratio_fn, z0, args=(isp, W, vfix, nvar), method='Nelder-Mead', options=dict(maxiter=4000, xatol=1e-7, fatol=1e-11))
        if res.fun < best[0]: best = (res.fun, res.x)
    z = best[1]; x = z[:len(W)]; v = np.zeros(len(W)); v[isp] = vfix if vfix is not None else np.clip(z[len(W):len(W) + nvar], 0.05, 2.0)
    return kind, W, isp, vfix, best[0], x - x[~isp][0] if (~isp).any() else x - x[0], v

def part3(pool):
    print("\nPart 3: minimal open sub-cases (NUMERICAL: Nelder-Mead from 6 random starts per job, exact Gauss-node evaluation)")
    jobs = []
    # (O2) common height: 2 or 3 pairs of weight 2 plus reals (patterns), heights fixed
    pats = {'1 simple': [1], '1 double': [2], '2 simples': [1, 1], '1 triple': [3], 'simple+double': [1, 2]}
    for vv in (0.15, 0.3, 0.5, 1.0):
        for k in (2, 3):
            for name, wr in pats.items():
                W = wr + [2] * k; isp = [False] * len(wr) + [True] * k
                jobs.append(('O2 v=%.2f k=%d %s' % (vv, k, name), len(jobs), W, isp, vv))
    # (O3) two pairs at free unequal heights plus one real atom
    for m0 in (1, 2, 3):
        for Wp in ((2, 2), (2, 4), (4, 2), (4, 4)):
            jobs.append(('O3 m0=%d W=%s' % (m0, Wp), 1000 + len(jobs), [m0] + list(Wp), [False, True, True], None))
    # (O1) three pairs alone at free heights
    for Wp in ((2, 2, 2), (2, 2, 4), (2, 4, 4)):
        jobs.append(('O1 W=%s' % (Wp,), 2000 + len(jobs), list(Wp), [True] * 3, None))
    t1 = time.time(); res = pool.map(opt_job, jobs, chunksize=2)
    print("  %d jobs [%.0fs]; minima of Sigma/cost (all >= 1: %s)" % (len(res), time.time() - t1, all(r[4] >= 1 for r in res)))
    for grp in ('O2 v=0.15', 'O2 v=0.30', 'O2 v=0.50', 'O2 v=1.00', 'O3', 'O1'):
        R_ = [r for r in res if r[0].startswith(grp)]; b = min(R_, key=lambda r: r[4])
        print("  %-9s min ratio %.6f  at %s: x = %s, v = %s" % (grp, b[4], b[0], np.array2string(b[5], precision=3), np.array2string(b[6], precision=3)))
    print("  reference: pair lattice ratio rho(0) = %.6f; Lemma A floor for two pairs alone 1.00777" % H.rho_at(0))
    sys.stdout.flush()

def cell_damage(f, xs, h, scale):
    """H1-type cells: components of {f < 0} cut into pieces of length <= lmax (best of 0.5, 0.6, 0.7), rho_c = rmin(piece length);
    damage = sum_c Psi_c(sup_c (-f) / scale) (scale 4 for the joint field sum_k 4 G, 1 for a single pair's G)."""
    neg = f < 0; dd = np.diff(np.r_[0, neg.astype(int), 0]); st = np.where(dd == 1)[0]; en = np.where(dd == -1)[0]
    best = np.inf
    for lmax in (0.5, 0.6, 0.7):
        tot = 0.0
        for a, b in zip(st, en):
            L = (b - a) * h; npc = max(1, int(math.ceil(L / lmax - 1e-12))); edges = np.linspace(a, b, npc + 1).round().astype(int)
            for t in range(npc):
                if edges[t + 1] > edges[t]:
                    g = -f[edges[t]:edges[t + 1]].min() / scale; rc = H.rmin_lo(np.array([(edges[t + 1] - edges[t]) * h]))[0]
                    tot += H.Psi_exact(np.array([g]), rc)[0]
        best = min(best, tot)
    return best

def part3c():
    print("\nPart 3c: joint-field bookkeeping on pair-lattice segments (W = 2 at x = 0..n-1, common height v), reals anywhere (NUMERICAL)")
    print("  resource E_P = int rho sinh^2 |S_P|^2 (+ pair r-bonds); damage = sum over H1-type cells (components of the negative set, pieces <= 0.5-0.7 as in H1)")
    print("  of Psi_c(sup_c Phi^-/4), Phi = joint field sum_k 4 G_v(x - x_k); 'separate' = H1 bookkeeping pair by pair (own negative field),")
    print("  which ignores the cancellation.  x in [-40, n+40], h = 1e-3 (tail beyond omitted: O(T(v)/40)).")
    A, Wq, rq = nodes(); h = 1e-3
    print("  %4s %4s | %9s %9s | %8s %8s | %s" % ("v", "n", "E_P", "sum W^2 X", "joint", "separate", "ratios = damage / (E_P + pair r-bonds)"))
    for vv in (0.2, 0.5, 1.0):
        X = H.Xv(vv)
        for n in (1, 2, 3, 4, 6, 8, 12):
            xk = np.arange(n, dtype=float); EP = Sig(xk, 0 * xk, 2 + 0 * xk, np.sinh(2 * np.pi * A * vv) ** 2)
            slack = sum(2 * 2 * H.r_and_dr(np.array([abs(xk[i] - xk[j])]))[0][0] for i in range(n) for j in range(n) if i != j)
            xs = np.arange(-40.0, n + 40.0, h); xs = xs[np.abs(xs[:, None] - xk[None, :]).min(1) > 1e-9]
            Gk = np.array([G_u(vv, np.abs(xs - xx)) for xx in xk])          # per-pair fields G_v(x - x_k)
            joint = cell_damage(4 * Gk.sum(0), xs, h, 4.0)
            sep = sum(cell_damage(Gk[kk], xs, h, 1.0) for kk in range(n))
            print("  %4.1f %4d | %9.3f %9.3f | %8.3f %8.3f | joint %.3f, separate %.3f" % (vv, n, EP, 4 * n * X, joint, sep, joint / (EP + slack), sep / (EP + slack)))
    sys.stdout.flush()

# ------------------------------------------------------------------ main
if __name__ == "__main__":
    c, P, R = H.part0(); H.setup(c)
    print("  rho(0) = %.6f, R = %.6f, rmin(1/2) >= %.4f, X(0.2) = %.4f, X(0.5) = %.4f, X(1) = %.2f" % (H.rho_at(0), R, H.rmin_lo(0.5)[0], H.Xv(0.2), H.Xv(0.5), H.Xv(1.0)))
    part1(); part2()
    with Pool(4) as pool: part3(pool)
    part3c()
    print("\nStatus: identities CHECKED; Theorem C (cluster criterion) PROVED; minimal open cases O1-O3 survive targeted search (NUMERICAL);")
    print("        (**) for several pairs at unequal heights close together, and for >= 2 pairs at a common height v > 0.08 with reals, remains OPEN.  total %.0fs" % (time.time() - T0))
