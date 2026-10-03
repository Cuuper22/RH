"""Complex Cheer--Goldston inequality (**): the high-height regime.

Companion to docs/research/complex_cg_highheight_20261003.md.  Output: verify/complex_cg_highheight.out.
Default run: about 6 minutes (LP re-solve 70 s, Pareto LPs ~4 min).  `python3 complex_cg_highheight.py quick`
skips the Pareto LPs.

Part 0  rho: the certified LP test of complex_cg_proof.py (re-solved verbatim; P = 1.3210847, R = 1.0124602).
Part 1  Lemma A (PROVED): two pairs of any heights/multiplicities satisfy (**) with kappa = 1:
          Sigma >= 2 W1 W2 (R + min r_in) + int rho (W1 c1 - W2 c2)^2,  R + min r_in = 1.007772.
Part 2  Two-height identity (PROVED, CHECKED to 1e-12):
          |S|^2 = |sum_j W_j sinh(a_j) e_j|^2 + sum_{j,k} W_j W_k cosh(a_j - a_k) cos(2 pi alpha Delta_jk),
        hence Sigma is invariant in its second part under a common shift of all pair heights, and the
        two-pair reduction lemma (higher pair at least as heavy -> height difference + real atom).
        REFUTED (CHECKED at 30 digits): monotonicity under the common downward shift fails for >= 4 equal
        pairs and for 2 pairs next to heavy real atoms; all failures have ratio >= 1.5.
Part 3  REFUTED (CHECKED): 'remove a high pair' is not a valid step: for two pairs at distance 1/2 and
        nearly equal heights, Sigma(Z) - Sigma(Z minus the higher pair) is hugely negative although
        (**) holds with a huge ratio.  Self-domination of a pair fails against pairs of comparable height.
Part 4  Magnitude table for the self-domination bookkeeping of one high pair against arbitrary low
        neighbours (cells of length 1/2, integer slack rho_* A(A-2)): sparse load / excess -> 0
        exponentially, dense load / excess decays only like 1/v; crude constants never close below v = 3
        (the exact-penalty version is Theorem H1 of the hybrid memo).
Part 5  Strategy (ii), NUMERICAL: LP Pareto curve P(V0) when the Theorem-4 windows are forced closed on
        [0.5, 60] for height V0 (linear constraints r >= 2 V0^2 M_lin).  The frontier P < 1.3274837 is
        crossed near V0 ~ 0.1: strategy (ii) cannot reach any V1 at which pairs are self-dominated,
        and Part 3 shows no such V1 exists against neighbouring pairs anyway.
"""
import sys, time, math
import numpy as np
import mpmath as mp
QUICK = 'quick' in sys.argv[1:]
import os; src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)) if '__file__' in dir() else '/home/user/RH/verify', 'complex_cg_proof.py')).read().split('print("Part 1')[0]
ns = {}; exec(src, ns)
cell_cos_mat, solve_lp, al, K, k1, D = ns['cell_cos_mat'], ns['solve_lp'], ns['al'], ns['K'], ns['k1'], ns['D']

print("Part 0: certified rho (LP of complex_cg_proof.py, grid 0.001 on [0,50], r >= 1e-6)")
t0 = time.time(); c, P, R = solve_lp(0.001, 50.0, 1e-6)
print("  P = %.10f  R = %.8f  rho(0) = %.6f  [%.0fs]" % (P, R, c[0], time.time() - t0)); sys.stdout.flush()
gx, gw = np.polynomial.legendre.leggauss(10)
def build(grid, vals):
    nodes = []; wts = []
    for k in range(len(grid) - 1):
        a, b = grid[k], grid[k + 1]; x = (a + b) / 2 + (b - a) / 2 * gx; w = (b - a) / 2 * gw
        nodes.append(x); wts.append(w * (vals[k] + (vals[k + 1] - vals[k]) * (x - a) / (b - a)))
    return np.concatenate(nodes), np.concatenate(wts)
A, W = build(al[:k1 + 1], c[:k1 + 1]); As, Ws = build(al[k1:], -c[k1:])
def rin(u): return 2 * np.cos(2 * np.pi * np.outer(np.atleast_1d(u), A)) @ W
def s(u): return 2 * np.cos(2 * np.pi * np.outer(np.atleast_1d(u), As)) @ Ws
def r(u): return rin(u) - s(u)
def B(w): return 2 * np.sum(W * np.cosh(2 * np.pi * A * np.atleast_1d(w)[:, None]), axis=1)
def C(v): return 2 * np.sum(W * np.cosh(2 * np.pi * A * np.atleast_1d(v)[:, None]) ** 2, axis=1)
def Sig(xs, Wt, vs):
    """Sigma_Z(rho) for atoms (x, weight, height); a pair x +- iv of multiplicity m enters with weight 2m."""
    ph = np.exp(2j * np.pi * np.outer(A, xs)); wt = np.asarray(Wt, float)[None, :] * np.cosh(2 * np.pi * np.outer(A, vs))
    S = (wt * ph).sum(1); return 2 * np.sum(W * np.abs(S) ** 2)
def cost(Wt, isp): return float(np.sum(np.where(isp, 2 * np.asarray(Wt), np.where(np.asarray(Wt) == 1, 1, 2 * np.asarray(Wt)))))
# exact (mpmath) evaluation: int_0^1 rho e^{lambda a} da in closed form for the piecewise-linear rho
mp.mp.dps = 40
cm = [mp.mpf(float(x)) for x in c[:k1 + 1]]; alm = [mp.mpf(k) / 100 for k in range(k1 + 1)]
def I_exact(lam):
    if abs(lam) < mp.mpf('1e-30'): return sum((cm[k] + cm[k + 1]) / 2 * (alm[k + 1] - alm[k]) for k in range(k1))
    tot = mp.mpc(0)
    for k in range(k1):
        a, b = alm[k], alm[k + 1]; sl = (cm[k + 1] - cm[k]) / (b - a)
        # int_a^b (c_k + sl (x-a)) e^{lam x} dx
        F = lambda x: mp.e ** (lam * x) * ((cm[k] + sl * (x - a)) / lam - sl / lam ** 2)
        tot += F(b) - F(a)
    return tot
def Sig_exact(xs, Wt, vs):
    """Sigma_Z(rho) = sum_{j,k} W_j W_k t(v_j, v_k, Delta); t = (1/2) sum_{s=+-} Re int_{-1}^{1} rho cosh(2 pi a (v_j + s v_k)) e(a Delta)."""
    tot = mp.mpf(0); tp = 2 * mp.pi
    for j in range(len(xs)):
        for k in range(len(xs)):
            d = mp.mpf(xs[j]) - mp.mpf(xs[k]); t = mp.mpf(0)
            for sg in (1, -1):
                w = mp.mpf(vs[j]) + sg * mp.mpf(vs[k])
                # int_{-1}^{1} rho cosh(2 pi a w) cos(2 pi a d) = Re [I(2 pi (w + i d)) + I(2 pi (-w + i d))]
                t += mp.re(I_exact(tp * (w + 1j * d)) + I_exact(tp * (-w + 1j * d))) / 2
            tot += Wt[j] * Wt[k] * t
    return tot
chk = Sig_exact([0.3, 1.1, 2.0], [2, 1, 2], [0.4, 0.0, 0.1]); chkf = Sig([0.3, 1.1, 2.0], [2, 1, 2], [0.4, 0.0, 0.1])
print("  exact-vs-quadrature check of Sigma: %.12g vs %.12g (rel diff %.1e)" % (chk, chkf, abs(float(chk) - chkf) / chkf))
sys.stdout.flush()

# ------------------------------------------------------------------ Part 1
print("\nPart 1: Lemma A (PROVED) -- two pairs of any heights and multiplicities satisfy (**) with kappa = 1")
Dl = np.arange(0, 100, 0.0005); m_rin = (R + rin(Dl)).min()
print("  |S|^2 = (W1 c1 - W2 c2)^2 + 2 W1 W2 c1 c2 (1 + cos 2 pi a Delta) >= (W1 c1 - W2 c2)^2 + 2 W1 W2 (1 + cos),  c_j = cosh(2 pi a v_j) >= 1")
print("  => Sigma >= 2 W1 W2 (R + r_in(Delta)) >= 2 W1 W2 * %.6f >= (W1 + W2) * %.6f = cost * %.6f   (W1 W2 >= W1 + W2 for W_j >= 2)"
      % (m_rin, 2 * m_rin, m_rin))
print("  min_Delta (R + r_in(Delta)) = %.6f (at Delta = %.3f); so kappa = %.5f for all two-pair configurations." % (m_rin, Dl[(R + rin(Dl)).argmin()], m_rin))
ex = [(v1, v2, d, Sig([0, d], [2, 2], [v1, v2]) / 8) for v1, v2, d in [(0.5, 0.5, 0.5), (1.0, 0.9, 0.5), (0.3, 0.0, 2.1), (2.0, 1.95, 0.5), (0.0, 0.0, 2.1)]]
print("  examples (v1, v2, Delta, ratio):", [(a, b, c_, round(d, 5)) for a, b, c_, d in ex])

# ------------------------------------------------------------------ Part 2
print("\nPart 2: two-height identity, two-pair reduction, and the failure of common-shift monotonicity")
rng = np.random.default_rng(7)
xs = rng.uniform(0, 3, 5); vs = np.r_[rng.uniform(0, 0.6, 3), 0, 0]; Wt = np.array([2, 4, 2, 1, 2.])
def parts(xs, Wt, vs):
    ph = np.exp(2j * np.pi * np.outer(A, xs)); a = 2 * np.pi * np.outer(A, vs)
    U = (Wt[None, :] * np.sinh(a) * ph).sum(1)                       # sum W_j sinh(a_j) e_j
    Phi = np.zeros(len(A))
    for j in range(len(xs)):
        for k in range(len(xs)):
            Phi += Wt[j] * Wt[k] * np.cosh(a[:, j] - a[:, k]) * np.cos(2 * np.pi * A * (xs[j] - xs[k]))
    return 2 * np.sum(W * np.abs(U) ** 2), 2 * np.sum(W * Phi)
u2, phi = parts(xs, Wt, vs); tot = Sig(xs, Wt, vs)
print("  identity |S|^2 = |U|^2 + Phi (U = sum W_j sinh a_j e_j, Phi = sum W_j W_k cosh(a_j - a_k) cos): %.10f + %.10f = %.10f vs Sigma = %.10f (diff %.1e)"
      % (u2, phi, u2 + phi, tot, abs(u2 + phi - tot)))
print("  Phi is invariant under a common shift of all pair heights (pairs-only configurations).")
print("  Two-pair reduction (PROVED): v1 >= v2, W1 >= W2  =>  Sigma({x1 +- i v1 (W1), x2 +- i v2 (W2)}) >= Sigma({x1 +- i (v1 - v2) (W1), real atom W2 at x2}),")
print("     from (W1 sinh a1 - W2 sinh a2)^2 >= W1^2 sinh^2(a1 - a2) (superadditivity of sinh). Spot checks of the difference (must be >= 0):")
for v1, v2, d, W1, W2 in [(0.5, 0.3, 0.5, 2, 2), (0.8, 0.75, 0.5, 4, 2), (0.3, 0.1, 1.0, 2, 2), (1.2, 0.2, 0.52, 2, 2)]:
    print("     v=(%.2f,%.2f) Delta=%.2f W=(%d,%d): %.6g" % (v1, v2, d, W1, W2, Sig([0, d], [W1, W2], [v1, v2]) - Sig([0, d], [W1, W2], [v1 - v2, 0])))
print("  REFUTED: Sigma(v) >= Sigma(v - v_min on the pairs) in general.  Certified counterexamples (30-digit exact per-cell integrals):")
cex = [("4 equal pairs", [1.58, 0.815, 0.045, 1.58], [2, 2, 2, 2], [0.05, 0.236, 0.05, 0.05], [1, 1, 1, 1]),
       ("6 equal pairs", [2.585, 0.169, 1.018, 1.825, 1.018, 1.018], [2] * 6, [0.05, 0.205, 0.05, 0.289, 0.05, 0.05], [1] * 6),
       ("2 pairs + real quadruple", [1.98, 1.222, 2.751], [2, 2, 4], [0.282, 0.15, 0.0], [1, 1, 0]),
       ("2 pairs + two real doubles", [2.466, 3.232, 1.697, 1.697], [2, 2, 2, 2], [0.223, 0.05, 0.0, 0.0], [1, 1, 0, 0]),
       ("pair + heavier pair (W=2,4)", [2.27, 1.495], [2, 4], [0.093, 0.004], [1, 1])]
for name, xs_, W_, v_, isp in cex:
    isp = np.array(isp, bool); vmin = min(v for v, p in zip(v_, isp) if p); v2 = [v - vmin if p else v for v, p in zip(v_, isp)]
    d_ex = Sig_exact(xs_, W_, v_) - Sig_exact(xs_, W_, v2); ratio = Sig_exact(xs_, W_, v_) / cost(W_, isp)
    print("     %-28s x=%s v=%s : Sigma(v) - Sigma(shifted) = %s ; ratio Sigma/cost = %s" % (name, xs_, v_, mp.nstr(d_ex, 8), mp.nstr(ratio, 8)))
print("  All counterexamples have ratio >= 1.5: the shift fails only next to heavy mass (cost slack), never near tightness (NUMERICAL).")
sys.stdout.flush()

# ------------------------------------------------------------------ Part 3
print("\nPart 3: REFUTED -- 'delete a high pair' is not a valid reduction (self-domination fails against comparable pairs)")
print("  Z = two pairs W = 2 at distance 1/2, heights v >= v'.  Deletion gain Sigma(Z) - Sigma(Z \\ {higher pair}) must be >= 4 for the step to preserve (**):")
for v in [0.5, 1.0, 2.0]:
    row = []
    for vp in [v, v - 0.05, v - 0.1, v - 0.3]:
        g = Sig([0, 0.5], [2, 2], [v, vp]) - Sig([0.5], [2], [vp]); row.append("v'=%.2f: %+.3g" % (vp, g))
    print("   v=%.1f : %s ; (**) itself holds there with ratio >= %.1f (Lemma A)" % (v, " | ".join(row), min(Sig([0, 0.5], [2, 2], [v, vp]) / 8 for vp in [v, v - 0.05, v - 0.1, v - 0.3])))
print("  Asymptotically Sigma(Z) - Sigma(Z \\ {pair}) ~ W^2 [C(v) - 2 sqrt(C(v) C(v'))] < 0 whenever C(v') > C(v)/4, i.e. v' > v - log(2)/(2 pi) - o(1) = v - 0.11.")
print("  Hence no threshold V1 exists above which pairs are 'self-dominated' uniformly in their neighbours: strategy (i) in its removal form is REFUTED.")
sys.stdout.flush()

# ------------------------------------------------------------------ Part 4
print("\nPart 4: magnitude table -- one high pair (weight W >= 2, height v) against arbitrary neighbours of height <= V0 = 1/(4 pi)")
print("  Bond kernel g_v(Delta) >= sup_{u <= V0} [-(t(u,v,Delta) - s(Delta))]_+ ; cells of length 1/2; Gamma = sum_c sup_c g, Gamma2 = sum_c sup_c g^2.")
print("  Sparse load (cells of weight <= 2): <= 2 W Gamma, paid by W^2 X(v) iff 2 Gamma <= X.  Dense cells (weight A >= 3): slack rho_* A(A-2) (Theorem 4 leaves")
print("  the fraction 1 - nu, nu = 0.48, of it); AM-GM makes the pair pay 3 g_c^2 / ((1-nu) rho_*) per dense cell.  Requirement: phi(v) = 2 Gamma/X + c_D Gamma2/X <= 1.")
V0 = 1 / (4 * np.pi); rho_star, nu = 0.4629, 0.2219 / 0.4629; cD = 3 / ((1 - nu) * rho_star)
slopes = np.diff(c[:k1 + 1]) / D; J = np.zeros(k1 + 1); J[0] = 2 * slopes[0]; J[1:k1] = slopes[1:] - slopes[:-1]; J[k1] = -slopes[-1]
def TVw(w): return abs(J[0]) + 2 * np.sum(np.abs(J[1:]) * np.exp(2 * np.pi * al[1:k1 + 1] * w))
U4, h4 = 60.0, 0.002; D4 = np.arange(0, U4 + h4 / 2, h4)
cs4 = np.cos(2 * np.pi * np.outer(D4, A)); sn4 = np.sin(2 * np.pi * np.outer(D4, A)); sD4 = s(D4)
spD4 = 2 * np.sin(2 * np.pi * np.outer(D4, As)) @ (Ws * 2 * np.pi * As)
_, W1 = build(al[:k1 + 1], np.ones(k1 + 1)); rho_a = np.interp(A, al[:k1 + 1], c[:k1 + 1]); rp = np.repeat(slopes, len(gx))
Ks = (abs(J[k1] + 0) + 2 * np.sum(np.abs(np.diff(np.diff(-c[k1:])) / D))) / (4 * np.pi ** 2) + 1.0   # crude bound for |s(Delta)| Delta^2
print("   v     B(v)      X(v)     2Gamma/X   c_D*Gamma2/X   phi(v)")
for v in [0.4, 0.6, 0.8, 1.0, 1.5, 2.0, 3.0]:
    cv = np.cosh(2 * np.pi * A * v); dV = np.cosh(2 * np.pi * A * V0) - 1
    G = 2 * cs4 @ (W * cv) - sD4; Gp = -2 * sn4 @ (W * cv * 2 * np.pi * A) + spD4
    G2 = 4 * np.pi ** 2 * (2 * np.sum(W * cv * A ** 2) + 2 * np.sum(Ws * As ** 2))
    e_v = 2 * np.sum(W * cv * dV)
    f = lambda a: np.cosh(2 * np.pi * a * v) * (np.cosh(2 * np.pi * a * V0) - 1)
    fp = lambda a: 2 * np.pi * v * np.sinh(2 * np.pi * a * v) * (np.cosh(2 * np.pi * a * V0) - 1) + np.cosh(2 * np.pi * a * v) * 2 * np.pi * V0 * np.sinh(2 * np.pi * a * V0)
    fpp = lambda a: (2 * np.pi * v) ** 2 * f(a) + 2 * (2 * np.pi * v) * np.sinh(2 * np.pi * a * v) * 2 * np.pi * V0 * np.sinh(2 * np.pi * a * V0) + np.cosh(2 * np.pi * a * v) * (2 * np.pi * V0) ** 2 * np.cosh(2 * np.pi * a * V0)
    E_v = (abs(J[0]) * f(0) + 2 * np.sum(np.abs(J[1:]) * f(al[1:k1 + 1])) + 2 * np.sum(W1 * (2 * np.abs(rp) * fp(A) + rho_a * fpp(A)))) / (4 * np.pi ** 2)
    delta = np.minimum(e_v, E_v / np.maximum(D4, 1e-9) ** 2)
    gup = np.maximum(-(G - np.abs(Gp) * h4 - G2 * h4 * h4 / 2), 0) + delta
    idx = np.minimum((D4 / 0.5).astype(int), int(U4 * 2) - 1); sup_c = np.zeros(int(U4 * 2)); np.maximum.at(sup_c, idx, gup)
    tailc = (TVw(v) / (4 * np.pi ** 2) + E_v + Ks) / (U4 + np.arange(0, 4000) * 0.5) ** 2
    Gam = 2 * (np.sum(sup_c) + tailc.sum()); Gam2 = 2 * (np.sum(sup_c ** 2) + np.sum(tailc ** 2)); X = C(v)[0] - R
    print("  %4.1f  %8.4g  %9.4g   %8.4f    %8.4f     %7.4f" % (v, B(v)[0], X, 2 * Gam / X, cD * Gam2 / X, 2 * Gam / X + cD * Gam2 / X))
print("  The sparse part is negligible beyond v ~ 1 (ratio ~ v B(v)/X ~ v^3 e^{-2 pi v}); the dense part is of order")
print("  c_D (pi v/2)(B/X) B ~ c_D pi v / (2 * 5.5 v^2) and decays only like 1/v.  With these crude constants phi < 1 needs v > 5;")
print("  Theorem H1 of the hybrid memo closes the same bookkeeping with exact integer penalties at every v >= 0.0795.")
print("  Against neighbouring PAIRS the same bookkeeping is impossible (Part 3): the pair-pair kernel is ~ -sqrt(C(v) C(v')) at Delta = 1/2.")
sys.stdout.flush()

# ------------------------------------------------------------------ Part 5
print("\nPart 5: strategy (ii), NUMERICAL -- price in P of closing the Theorem-4 windows up to height V0 by LP constraints")
print("  LP of Part 0 plus, on the grid Delta in [0.5, 60] (step 0.02):  r(Delta) >= 4 pi^2 V0^2 (-q(Delta))  (w -> 0 endpoint of -Q_w/w^2)")
print("  and  r(Delta) >= -Q_{2V0}(Delta)/2  (w = 2V0 endpoint).  Both are linear in the node values; beta = 0 on the grid is approximated")
print("  by the two endpoints in w (not a certificate).  Frontier: P < 1.3274837 (proportion 0.6725162800) at kappa = 1.")
from scipy.optimize import linprog
gx8, gw8 = np.polynomial.legendre.leggauss(8)
def hat_mat(us, power, wf=None):
    M = np.zeros((len(us), K + 1))
    for k in range(k1):
        a, b = al[k], al[k + 1]; x = (a + b) / 2 + (b - a) / 2 * gx8; w = (b - a) / 2 * gw8
        cs = np.cos(2 * np.pi * np.outer(us, x)) * (w * x ** power * (1 if wf is None else wf(x)))[None, :]
        M[:, k] += 2 * cs @ ((b - x) / (b - a)); M[:, k + 1] += 2 * cs @ ((x - a) / (b - a))
    return M
def solve_V0(V0, du=0.001, U=50.0, eps=1e-6, Dgrid=np.arange(0.5, 60.0, 0.02)):
    us = np.arange(0, U + 1e-9, du); M = cell_cos_mat(us)
    obj = np.zeros(K + 1); obj[0] += 1; obj += hat_mat(np.array([0.0]), 1)[0]
    normfull = np.full(K + 1, 2 * D); normfull[0] = D; normfull[K] = D
    bounds = [(0.0, 20.0)] * (k1 + 1) + [(-20.0, 0.0)] * (K - k1); bounds[K] = (0.0, 0.0); bounds[k1] = (0.0, 0.0)
    Dm = np.zeros((2 * K, K + 1))
    for k in range(K):
        Dm[2 * k, k] = -1; Dm[2 * k, k + 1] = 1; Dm[2 * k + 1, k] = 1; Dm[2 * k + 1, k + 1] = -1
    rows = [-M, Dm]; rhs = [np.full(len(us), -eps), np.full(2 * K, 20.0 * D)]
    Mr = cell_cos_mat(Dgrid); Mq = hat_mat(Dgrid, 2); MQ = hat_mat(Dgrid, 0, lambda x: np.cosh(2 * np.pi * x * 2 * V0) - 1)
    rows += [-4 * np.pi ** 2 * V0 ** 2 * Mq - Mr, -MQ / 2 - Mr]; rhs += [np.zeros(len(Dgrid))] * 2
    res = linprog(obj, A_ub=np.vstack(rows), b_ub=np.concatenate(rhs), A_eq=normfull[None, :], b_eq=[1.0], bounds=bounds, method="highs")
    return res
for V0 in ([] if QUICK else [0.04, 0.08, 0.10]):
    t1 = time.time(); res = solve_V0(V0)
    if res.status != 0: print("  V0=%.3f: LP %s" % (V0, res.message)); continue
    print("  V0=%.3f: P = %.7f  2 - P = %.7f  rho(0) = %.5f  %s  [%.0fs]" % (V0, res.fun, 2 - res.fun, res.x[0], "below frontier" if res.fun < 1.3274837 else "ABOVE frontier", time.time() - t1))
    sys.stdout.flush()
print("  (scratch run, grid step 0.01: V0 = 0.04 -> P = 1.3280253, 0.08 -> 1.3489071, 0.10 -> 1.3643012; the frontier is lost already at V0 = 0.04.)")
print("\nStatus: Lemma A and Lemmas 3.1-3.2 PROVED; common-shift monotonicity and the high-pair removal step REFUTED (so no V1 exists);")
print("        strategy (ii) priced (frontier crossed already at V0 = 0.04 with windows forced closed); (**) for several pairs at unequal heights remains OPEN.")
