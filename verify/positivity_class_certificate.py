"""Cheer--Goldston positivity class versus actual complex zeros.

Companion to docs/research/positivity_class_20261003.md.  Three parts.

Part A (NUMERICAL, LP).  Reproduces the value of the Cheer--Goldston /
Chirre--Goncalves--de Laat class under RH: minimise
    P(r) = rhat(0) + 2 int_0^1 a rhat(a) da      subject to r(0) = 1,
over even rhat piecewise linear on [0,Lam], rhat <= 0 on [1,Lam], r >= 0 on a
grid.  Simple-zero proportion 2 - P.  (CGdL 2020 obtain 1.3208 by SDP.)

Part B (CHECKED, mpmath).  The lone conjugate pair Z = {iy, -iy} forces
    Sigma_Z(r) = 2 r(0) + 2 r(2iy),   r(2iy) = int rhat(a) cosh(2 pi a y) da,
and the complex-zero certificate  s_1 >= 2N - Sigma_Z(r)/r(0)  needs
r(2iy) >= r(0) for every y > 0.  For the LP test this fails already at
moderate y: the Fourier mass outside [-1,1] is negative and dominates the
cosh weight.  The general statement is proved in the memo (Lemma 1).

Part C (NUMERICAL, adversarial).  The bandwidth-one reformulation (**):
    Sigma_Z(rho) >= kappa (2N - s_1),  rho = rhat 1_[-1,1],  kappa = r(0),
is tested over finite conjugation-invariant complex multisets (real clusters
with multiplicities + conjugate pairs x +- i v with multiplicities).  For the
LP-optimal rho every minimiser collapses onto the real line (v -> 0), so the
complex infimum equals the real one.  A control rho with a deep negative dip
of r_in shows the complex infimum can be far below the real one, so (**) is
rho-specific and no general theorem is available.  (**) for complex Z is NOT
proved here; it is the open step.

Only standard axioms of analysis are used; nothing here is a Lean statement.
"""
import sys
import numpy as np
import mpmath as mp
from scipy.optimize import linprog, minimize

mp.mp.dps = 30
rng = np.random.default_rng(0)

# ---------------------------------------------------------------- Part A
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
    M = np.zeros((len(us), K + 1))
    for i, u in enumerate(us):
        for k in range(kmax):
            I0, I1 = cell_cos(al[k], al[k + 1], u)
            M[i, k] += 2 * I0; M[i, k + 1] += 2 * I1
    return M

us = np.arange(0, U + 1e-9, 0.01)
M = rmatrix(us)
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
res = linprog(obj, A_ub=np.vstack([-M, Dm]), b_ub=np.concatenate([np.zeros(len(us)), np.full(2 * K, SLOPE * D)]),
              A_eq=norm[None, :], b_eq=[1.0], bounds=bounds, method="highs-ipm")
assert res.status == 0, res.message
c = res.x; P = float(obj @ c)
R = float(norm[:k1 + 1] @ c[:k1 + 1])
print("Part A: Cheer-Goldston class LP (RH side), Lam=%g, grid %g, positivity to u=%g" % (Lam, D, U))
print("  P = rhat(0) + 2 int_0^1 a rhat = %.10f   simple proportion 2-P = %.10f   (CGdL 2020: 1.3208 / 0.6792)" % (P, 2 - P))
print("  Montgomery-Taylor value for comparison: 1/2 + 2^(-1/2) cot(2^(-1/2)) = %.10f -> %.10f" % (0.5 + mp.cot(1 / mp.sqrt(2)) / mp.sqrt(2), 2 - (0.5 + mp.cot(1 / mp.sqrt(2)) / mp.sqrt(2))))
print("  R = int_{-1}^1 rho = %.8f ; kappa = r(0) = 1 ; min rhat on [0,1] = %.3e (rho >= 0 inside) ; min rhat on (1,Lam] = %.5f" % (R, c[:k1 + 1].min(), c[k1:].min()))
rin_grid = rmatrix(us, kmax=k1)[:, :k1 + 1] @ c[:k1 + 1]
print("  r_in = bandwidth-one part: min r_in(u) = %.6f at u = %.3f ; completion mass s(0) = R - 1 = %.6f" % (rin_grid.min(), us[np.argmin(rin_grid)], R - 1))
print("  NUMERICAL: LP with grid positivity; not an exact certificate of r >= 0 (the RH-side value is CGdL's theorem).")

# ---------------------------------------------------------------- Part B
print("\nPart B: lone conjugate pair obstruction (CHECKED with mpmath, 30 digits)")
cf = [mp.mpf(float(v)) for v in c]; alf = [mp.mpf(float(v)) for v in al]
def r_imag(y):
    # r(2iy)/r(0) = 2 int_0^Lam rhat(a) cosh(2 pi a 2y)... in Montgomery units u = x L/(2 pi): r(i t) = 2 int rhat cosh(2 pi a t)
    t = mp.mpf(2) * y
    tot = mp.mpf(0)
    for k in range(K):
        a, b = alf[k], alf[k + 1]
        f = lambda x: (cf[k] + (cf[k + 1] - cf[k]) * (x - a) / (b - a)) * mp.cosh(2 * mp.pi * x * t)
        tot += mp.quad(f, [a, b])
    return 2 * tot
def r_imag_inside(y):
    t = mp.mpf(2) * y; tot = mp.mpf(0)
    for k in range(k1):
        a, b = alf[k], alf[k + 1]
        f = lambda x: (cf[k] + (cf[k + 1] - cf[k]) * (x - a) / (b - a)) * mp.cosh(2 * mp.pi * x * t)
        tot += mp.quad(f, [a, b])
    return 2 * tot
for y in [mp.mpf('0.1'), mp.mpf('0.25'), mp.mpf('0.5'), mp.mpf(1), mp.mpf(2)]:
    full = r_imag(y); inside = r_imag_inside(y)
    print("  y=%4s : r(2iy)/r(0) = %+.6e  [need >= 1 for s1 >= 2N - Sigma/r(0)]   bandwidth-one part r_in(2iy) = %.6e (>= R, fine for (**))" % (mp.nstr(y, 4), full, inside))
    if full < 1:
        print("           -> lone pair violates the naive complex-zero certificate: 2N - Sigma_Z(r)/r(0) = %.4e > 0 = s_1" % (4 - 2 - 2 * full))

# ---------------------------------------------------------------- Part C
print("\nPart C: adversarial search for (**) with the LP-optimal rho (kappa = 1) and a control rho")
gx, gw = np.polynomial.legendre.leggauss(6)
def build(alpha_grid, rho_vals):
    nodes = []; wts = []
    for k in range(len(alpha_grid) - 1):
        a, b = alpha_grid[k], alpha_grid[k + 1]; x = (a + b) / 2 + (b - a) / 2 * gx; w = (b - a) / 2 * gw
        nodes.append(x); wts.append(w * (rho_vals[k] + (rho_vals[k + 1] - rho_vals[k]) * (x - a) / (b - a)))
    return np.concatenate(nodes), np.concatenate(wts)
def make_ratio(A, W):
    def ratio(reals, pairs):
        S = np.zeros_like(A, dtype=complex)
        for u, m in reals: S += m * np.exp(2j * np.pi * A * u)
        for u, v, m in pairs: S += 2 * m * np.cosh(2 * np.pi * A * min(abs(v), 2.0)) * np.exp(2j * np.pi * A * u)
        N = sum(m for _, m in reals) + 2 * sum(m for _, _, m in pairs)
        s1 = sum(1 for _, m in reals if m == 1)
        return 2 * np.sum(W * np.abs(S) ** 2) / (2 * N - s1)
    return ratio
def search(ratio, mreal, mpairs, trials):
    nr, npr = len(mreal), len(mpairs); dim = max(nr - 1, 0) + 2 * npr
    def unpack(x):
        reals = [(0.0, mreal[0])] if nr else []
        idx = 0
        for j in range(1, nr): reals.append((x[idx], mreal[j])); idx += 1
        pairs = []
        for j in range(npr): pairs.append((x[idx], abs(x[idx + 1]), mpairs[j])); idx += 2
        return reals, pairs
    best = (np.inf, None)
    for t in range(trials):
        x0 = rng.uniform(-3, 3, dim)
        for j in range(npr): x0[max(nr - 1, 0) + 2 * j + 1] = rng.uniform(0, 1.0)
        f = lambda x: ratio(*unpack(x))
        if dim == 0:
            val, xb = f(x0), x0
        else:
            r_ = minimize(f, x0, method="Nelder-Mead", options={"xatol": 1e-8, "fatol": 1e-11, "maxiter": 6000})
            val, xb = f(r_.x), r_.x
        if val < best[0]: best = (val, unpack(xb))
    return best
PATTERNS = [([1], []), ([1, 1], []), ([2], []), ([1, 1, 1], []), ([2, 1], []), ([2, 2], []), ([3], []),
            ([], [1]), ([], [1, 1]), ([], [1, 1, 1]), ([1], [1]), ([2], [1]), ([3], [1]), ([3, 1], [1]), ([4], [1]),
            ([1, 1], [1]), ([2, 2], [1]), ([3], [1, 1]), ([4], [1, 1]), ([5], [1]), ([5], [1, 1]), ([5], [2]),
            ([6], [2]), ([3, 3], [1]), ([4, 4], [1, 1]), ([2, 1, 1], [1, 1]), ([1, 1, 1], [1, 1, 1])]
for name, (grid, vals) in [("LP-optimal rho (CG class)", (al[:k1 + 1], c[:k1 + 1])),
                           ("control rho = 1_[1/2,1] (deep dip, r_in min ~ -0.83 R)", (np.linspace(0, 1, 101), np.where(np.linspace(0, 1, 101) >= 0.5, 1.0, 0.0)))]:
    A, W = build(grid, vals); ratio = make_ratio(A, W)
    print("  --- %s : R = %.6f" % (name, 2 * W.sum()))
    overall_min = np.inf; below_collapsed = []
    for mreal, mpairs in PATTERNS:
        val, cfg = search(ratio, mreal, mpairs, 20 if len(mreal) + len(mpairs) <= 3 else 12)
        overall_min = min(overall_min, val)
        if mpairs:
            # collapsed real pattern: each pair of multiplicity m becomes a real zero of multiplicity 2m
            cval, _ = search(ratio, list(mreal) + [2 * m for m in mpairs], [], 20 if len(mreal) + len(mpairs) <= 3 else 12)
            vmax = max(v for _, v, _ in cfg[1])
            flag = "  BELOW collapsed real pattern by %.2e" % (cval - val) if val < cval - 1e-6 else ""
            if val < cval - 1e-6: below_collapsed.append((mreal, mpairs, val, cval, vmax))
            print("    complex   reals m=%-9s pairs m=%-9s min = %.6f   collapsed-real min = %.6f   max v at min = %.2e%s" % (mreal, mpairs, val, cval, vmax, flag))
        else:
            print("    real-only reals m=%-9s                    min = %.6f" % (mreal, val))
    print("  summary: min over all patterns of Sigma/(2N-s1) = %.6f (kappa = 1: (**) %s on these patterns);" % (overall_min, "holds" if overall_min >= 1 - 1e-9 else "FAILS"))
    print("           complex patterns strictly below their collapsed real pattern: %d of %d" % (len(below_collapsed), sum(1 for _, mp_ in PATTERNS if mp_)))
    if below_collapsed:
        print("  -> lifting off the line lowers the ratio for this rho (kappa_C(rho) < kappa_real(rho) possible); worst case:", min(below_collapsed, key=lambda t: t[2] - t[3]))
    else:
        print("  -> every minimiser collapses to the real line: NUMERICAL evidence that kappa_C(rho) = kappa_real(rho) for this rho.")

# ---------------------------------------------------------------- Part D
print("\nPart D: second-order lifting test at near-tight real designs (LP-optimal rho)")
print("  Lifting a real double zero at x_j into a pair x_j +- i v changes Sigma by 2 (2 pi v)^2 C_j + O(v^4),")
print("  C_j = sum_k m_k q(x_j - x_k),  q(u) = int rho(a) a^2 cos(2 pi a u) da.  A violation of (**) from a tight")
print("  design needs C_j < 0.  Designs: n simple zeros + one double zero, positions optimised for the real ratio.")
A, W = build(al[:k1 + 1], c[:k1 + 1]); ratio = make_ratio(A, W)
q = lambda u: 2 * np.sum(W * A ** 2 * np.cos(2 * np.pi * A * u))
qs = np.array([q(u) for u in np.arange(0, 4, 0.01)])
print("  q(0) = %.6f ; min_u q(u) = %.6f" % (q(0), qs.min()))
for n in [6, 10]:
    ms = [1] * n + [2]; den = 2 * (n + 2) - n
    best = (np.inf, None)
    for t in range(8):
        x0 = np.sort(rng.uniform(0, 1.06 * (n + 1), n + 1)); x0 -= x0[0]
        f = lambda x: ratio([(0.0, 1)] + [(xx, m) for xx, m in zip(x, ms[1:])], [])
        r_ = minimize(f, x0[1:], method="Nelder-Mead", options={"maxiter": 20000, "xatol": 1e-8, "fatol": 1e-12})
        if r_.fun < best[0]: best = (r_.fun, np.concatenate([[0.0], r_.x]))
    val, xs = best
    Cj = sum(m * q(xs[n] - xk) for xk, m in zip(xs, ms))
    lifted = [ratio([(xx, 1) for xx in xs[:n]], [(xs[n], v, 1)]) for v in (0.05, 0.1, 0.2)]
    g = lambda z: ratio([(0.0, 1)] + [(xx, 1) for xx in z[:n - 1]], [(z[n - 1], abs(z[n]), 1)])
    r2 = minimize(g, np.concatenate([xs[1:], [0.1]]), method="Nelder-Mead", options={"maxiter": 30000, "xatol": 1e-9, "fatol": 1e-13})
    print("  n=%2d: real-design ratio %.6f ; C_j = %+.6f ; lifted ratios v=.05,.1,.2: %s ; joint re-optimisation -> ratio %.6f at v = %.1e"
          % (n, val, Cj, np.round(lifted, 6), r2.fun, abs(r2.x[n])))

print("\nStatus: Lemma 1 (naive transfer refuted by a lone pair) PROVED in memo and CHECKED above;")
print("        (**) for complex Z with the CG-optimal rho: CONJECTURE supported numerically, not proved;")
print("        no unconditional bound above the Montgomery-Taylor value is certified by this script.")
