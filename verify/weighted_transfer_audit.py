#!/usr/bin/env python3
"""Independent referee audit of the vertex-weighted transfers used by
docs/research/multiwindow_20261003.md (diagonal multiplier phi, 1/64200) and
docs/research/triple_correlation_20261003.md section 5 (mark a, 1/216600).

Memo: docs/research/weighted_transfer_audit_20261003.md.
Written independently of verify/multiwindow_certificate.py and
verify/triple_correlation_certificate.py: only the polynomial coefficients
(the certificate data) are copied from those scripts.  All functionals are
coded from the auditor's own derivation, as functionals of a GENERAL
(non-factorized) vertex integrand F(x,y,z,t), not through slot sums.

  [1] support geometry: a vertex weight cannot enlarge the frequency support
  [2] generic-symbol limit formulas; reductions (flat 73/180, phi=1) and
      symmetry checks of the ordered formula (path swap y<->t, reflection)
  [3] independent float evaluation of the certificate inputs; comparison
  [4] independent sup / range checks of phi and of the mark
  [5] scalar margins recomputed from [3]; largest certifiable delta_0
  [6] operator identities and the two finite inequalities, on random
      matrices and on discretized continuous zero-side configurations
Labels: CHECKED = rigorous up to stated float tolerance with large margin;
NUMERICAL = diagnostic.
"""
import time
from fractions import Fraction as Fr
import numpy as np
from numpy.polynomial.legendre import leggauss, legval

T0 = time.time()
np.set_printoptions(precision=12)


def hdr(s):
    print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78, flush=True)


def poly(c):
    c = [float(Fr(x)) for x in c]

    def f(s):
        s = np.asarray(s, dtype=float)
        r = np.zeros_like(s)
        for a in reversed(c):
            r = r * s + a
        return r
    return f


# ---------------------------------------------------------------- quadrature
def gl(n, lo, hi):
    t, w = leggauss(n)
    return (hi - lo) / 2 * t + (hi + lo) / 2, (hi - lo) / 2 * w


N1, N2, N3 = 160, 110, 84
X1, W1 = gl(N1, -0.5, 0.5)
# 2D: bottom b, gap v>0, top b+v; b in [-1/2, 1/2-v]
_v, _wv = gl(N2, 0.0, 1.0)
_s, _ws = leggauss(N2)
B2 = (-0.5 + (1 - _v[:, None]) * (1 + _s[None, :]) / 2).ravel()
V2 = np.repeat(_v, N2)
WT2 = (_wv[:, None] * (1 - _v[:, None]) / 2 * _ws[None, :]).ravel()
# 3D: z bottom, v,w>0, z+v+w<=1/2 ; s=v+w, v=s*tau
_S, _wS = gl(N3, 0.0, 1.0)
_tau, _wtau = gl(N3, 0.0, 1.0)
_r, _wr = leggauss(N3)
SS = _S[:, None, None]
Z3 = (-0.5 + (1 - SS) * (1 + _r[None, None, :]) / 2) * np.ones((1, N3, 1))
V3 = SS * _tau[None, :, None] * np.ones((1, 1, N3))
Wv3 = SS * (1 - _tau[None, :, None]) * np.ones((1, 1, N3))
WT3 = (_wS[:, None, None] * SS * _wtau[None, :, None] * (1 - SS) / 2 * _wr[None, None, :])
Z3, V3, Wv3, WT3 = Z3.ravel(), V3.ravel(), Wv3.ravel(), WT3.ravel()


def I1(f):
    return np.sum(W1 * f(X1))


def pair_limit(F2):
    """lim tr(G-cycle of length 2 with vertex integrand F2(x,y))/N
       = int F2(x,x) + int int |x-y| F2(x,y)."""
    top, bot = B2 + V2, B2
    return (np.sum(W1 * F2(X1, X1))
            + np.sum(WT2 * V2 * (F2(top, bot) + F2(bot, top))))


def cubic_limit(F3):
    """S_3 = delta delta + sum_c delta(xi_c)|xi_a| on the hexagon, cycle x->y->z->x,
       xi=(x-y,y-z,z-x).  xi_1=0: x=y ; xi_2=0: y=z ; xi_3=0: z=x."""
    top, bot = B2 + V2, B2
    tot = np.sum(W1 * F3(X1, X1, X1))
    for (p, q) in ((top, bot), (bot, top)):
        tot += np.sum(WT2 * V2 * (F3(p, p, q) + F3(p, q, q) + F3(p, q, p)))
    return tot


C0, C1, C2 = 1 / 6, 1 / 3, 1.0


def ordered_limit(F4):
    """lim ||.||^2/N of the ordered two-path statistic with GENERAL vertex
    integrand F4(x,y,z,t) on x>y>z, x>t>z (frequencies x-y,y-z | z-t,t-x).
    Contractions derived in the audit memo (section 3)."""
    t0 = C0 * np.sum(W1 * F4(X1, X1, X1, X1))
    X, Y = B2 + V2, B2                      # top, bottom
    one = (F4(X, Y, Y, X)                   # prime pair on slots (1,3)
           + F4(X, Y, Y, Y)                 # (1,4)
           + F4(X, X, Y, X)                 # (2,3)
           + F4(X, X, Y, Y))                # (2,4)
    t1 = C1 * np.sum(WT2 * V2 * one)
    z, v, w = Z3, V3, Wv3
    two = (F4(z + v + w, z + w, z, z + v)   # matching (1,3)(2,4)
           + F4(z + v + w, z + w, z, z + w))  # matching (1,4)(2,3)
    t2 = C2 * np.sum(WT3 * v * w * two)
    return t0 + t1 + t2


# ---------------------------------------------------------------- data
p8 = poly([1, 0, -1, 0, Fr(1, 6), 0, Fr(-1, 90), 0, Fr(1, 2520)])
PHI = ['9991281/10000000', '0', '623581/1000000', '0', '-1316105007/10000000', '0',
       '35539677201/5000000', '0', '-184900986473/2500000', '0',
       '-7105319268637/2500000', '0', '65741450766381/1000000', '0',
       '-5706449438243701/10000000', '0', '781128124322477/312500', '0',
       '-3460209003147011/625000', '0', '1545712609558661/312500']
phi = poly(PHI)
COEFF = [1091974251780, -1092598710370, 183563572147, -13799851355, 11008450474,
         -46499927506, 75463768564]
p12 = poly(sum([[Fr(c, 10**12), 0] for c in COEFF], [])[:-1])
ALPHA = [Fr(n, 10**12) for n in (472828210507, -1129673802345, 389359086226, 386110142863,
                                  -458489619579, 22317526742, 282317470468, -176140789998,
                                  -68490929761, 138998680169, -35983150606, -43743837471,
                                  33967978797)]
EPS = 1 / 250000


def mark(s):
    c = np.zeros(25)
    for j, a in enumerate(ALPHA):
        c[2 * j] = float(a)
    return legval(2 * np.asarray(s, float), c) - EPS


def normalized(p):
    m = I1(p)
    return lambda s: p(s) / m


u_mw = normalized(p8)
u_tc = normalized(p12)


def D_of(u):
    return pair_limit(lambda x, y: u(x) * u(y))


def kappa_weighted(u, wt):
    """-lim tr(M_wt p(G))/N, p(t)=t^3-3t^2+2t, weight at the cycle's start vertex."""
    c3 = cubic_limit(lambda x, y, z: wt(x) * u(x) * u(y) * u(z))
    c2 = pair_limit(lambda x, y: wt(x) * u(x) * u(y))
    c1 = I1(lambda x: wt(x) * u(x))
    return -(c3 - 3 * c2 + 2 * c1)


def EY_general(u, wt):
    """||Phi V^2 + V Phi V + V^2 Phi||^2: weight (wx+wy+wz)(wx+wt+wz)."""
    return ordered_limit(lambda x, y, z, t: (wt(x) + wt(y) + wt(z)) * (wt(x) + wt(t) + wt(z))
                         * u(x) * u(y) * u(z) * u(t))


# ---------------------------------------------------------------- [1]
hdr("[1] support geometry under vertex weights (exact rational sampling)")
rng = np.random.default_rng(1003)
ok = True
for _ in range(20000):
    pts = [Fr(int(k), 1000) for k in rng.integers(-499, 500, size=4)]
    x, y, z, t = pts
    xi4 = (x - y, y - z, z - t, t - x)
    rngw = max(pts) - min(pts)
    # cubic triangle cycle
    xi3 = (x - y, y - z, z - x)
    ok &= sum(abs(a) for a in xi3) == 2 * (max(x, y, z) - min(x, y, z))
    if x > y > z and x > t > z:      # ordered orthant
        ok &= sum(abs(a) for a in xi4) == 2 * (x - z)
    ok &= sum(abs(a) for a in xi4) <= 4 * rngw
print("xi = vertex differences; sum|xi| = 2*range on triangles and on the ++-- orthant: %s" % ok)
print("=> supp Psi_w is contained in {xi = differences of points of supp u} for ANY bounded")
print("   vertex weight w: weights multiply the Fourier-side density, they do not convolve it.")
assert ok

# ---------------------------------------------------------------- [2]
hdr("[2] generic-symbol formulas: reductions and symmetries")
one = lambda s: np.ones_like(np.asarray(s, float))  # noqa: E731
flat = one
Qflat = ordered_limit(lambda x, y, z, t: one(x))
print("flat width 1: D=%.15f (4/3)  M3=%.15f (2)  Q=%.15f (73/180=%.15f)"
      % (D_of(flat), cubic_limit(lambda x, y, z: one(x)), Qflat, 73 / 180))
assert abs(Qflat - 73 / 180) < 1e-13
lam = 0.8
ul = lambda s: (np.abs(s) <= lam / 2) / lam  # noqa: E731  (only for closed form check)
print("closed form Q_flat(lam)=1/(6lam^3)+2/(9lam)+lam/60 at lam=1: %.15f" % (1 / 6 + 2 / 9 + 1 / 60))
r2 = np.sqrt(2)
ucos = lambda s: np.cos(r2 * s) / (r2 * np.sin(1 / r2))  # noqa: E731
Dc = D_of(ucos)
print("cosine: D=%.13f (closed form %.13f)  kappa=%.13f  Q=%.13f"
      % (Dc, 0.5 + 1 / (r2 * np.tan(1 / r2)), kappa_weighted(ucos, one),
         ordered_limit(lambda x, y, z, t: ucos(x) * ucos(y) * ucos(z) * ucos(t))))
# symmetry checks with a deliberately non-symmetric, signed vertex weight
f1 = poly([0.3, -1.1, 0.7, 2.0])
f2 = poly([-0.4, 0.9, 1.3])
f3 = poly([1.0, 0.5, -2.2, 0.1])
f4 = poly([0.2, -0.6, 0.0, 1.7])
u0 = lambda s: 1.0 + 0.3 * s - 0.8 * s ** 2  # noqa: E731
R = lambda f: (lambda s: f(-s))  # noqa: E731
base = ordered_limit(lambda x, y, z, t: f1(x) * f2(y) * f3(z) * f4(t) * u0(x) * u0(y) * u0(z) * u0(t))
swap = ordered_limit(lambda x, y, z, t: f1(x) * f4(y) * f3(z) * f2(t) * u0(x) * u0(y) * u0(z) * u0(t))
refl = ordered_limit(lambda x, y, z, t: R(f3)(x) * R(f2)(y) * R(f1)(z) * R(f4)(t)
                     * R(u0)(x) * R(u0)(y) * R(u0)(z) * R(u0)(t))
print("asymmetric signed weights: Q=%.15f  path-swap y<->t: %.15f  reflection: %.15f"
      % (base, swap, refl))
assert abs(base - swap) < 1e-13 and abs(base - refl) < 1e-13
# cubic: rotation invariance of the cycle (start vertex) and reflection (orientation)
c_a = cubic_limit(lambda x, y, z: f1(x) * f2(y) * f3(z))
c_b = cubic_limit(lambda x, y, z: f1(y) * f2(z) * f3(x))
c_c = cubic_limit(lambda x, y, z: f1(x) * f2(z) * f3(y))
print("cubic: cyclic rotation %.15f vs %.15f; orientation reversal %.15f" % (c_a, c_b, c_c))
assert abs(c_a - c_b) < 1e-13 and abs(c_a - c_c) < 1e-13
# product weight phi at all four vertices = unweighted Q of the profile u*phi
g = poly([1.0, 0.2, -0.9])
lhs = ordered_limit(lambda x, y, z, t: g(x) * g(y) * g(z) * g(t) * u0(x) * u0(y) * u0(z) * u0(t))
ug = lambda s: g(s) * u0(s)  # noqa: E731
rhs = ordered_limit(lambda x, y, z, t: ug(x) * ug(y) * ug(z) * ug(t))
print("product weight consistency: %.15f = %.15f" % (lhs, rhs))
# inherited height constants C0=int|P_+ 1_[1,2]|^4, C1=int_1^2|P_+ 1_[1,2]|^2 (not re-derived,
# only re-evaluated): P_+ 1_[1,2] = 1_[1,2]/2 + (i/2pi) log|(r-1)/(r-2)| up to conjugation
from scipy.integrate import quad  # noqa: E402
ell = lambda r: np.log(abs((r - 1) / (r - 2)))  # noqa: E731
inside4 = quad(lambda r: (0.25 + ell(r) ** 2 / (4 * np.pi ** 2)) ** 2, 1, 2, points=[1.5], limit=400)[0]
outside4 = (quad(lambda r: (ell(r) ** 2 / (4 * np.pi ** 2)) ** 2, -np.inf, 1, limit=400)[0]
            + quad(lambda r: (ell(r) ** 2 / (4 * np.pi ** 2)) ** 2, 2, np.inf, limit=400)[0])
c1 = quad(lambda r: 0.25 + ell(r) ** 2 / (4 * np.pi ** 2), 1, 2, points=[1.5], limit=400)[0]
print("inherited height constants re-evaluated: C0=%.10f (1/6)  C1=%.10f (1/3)"
      % (inside4 + outside4, c1))
assert abs(inside4 + outside4 - 1 / 6) < 1e-7 and abs(c1 - 1 / 3) < 1e-8
# phi=1 controls
print("phi=1: E_Y/9 = %.13f   Q(cos) as above" % (EY_general(ucos, one) / 9))

# ---------------------------------------------------------------- [3]
hdr("[3] independent evaluation of the certificate inputs (float, GL exact for polynomials)")
D_mw = D_of(u_mw)
k_mw = kappa_weighted(u_mw, phi)
EY_mw = EY_general(u_mw, phi)
uphi2 = I1(lambda s: u_mw(s) * phi(s) ** 2)
k1_mw = kappa_weighted(u_mw, one)
Q1_mw = ordered_limit(lambda x, y, z, t: u_mw(x) * u_mw(y) * u_mw(z) * u_mw(t))
claim_mw = dict(kappa=0.02572936695466, EY=1.94205279052313, uphi2=0.81431323705434,
                D=1.3274992963205883)
print("multiwindow (Taylor-8 cosine, degree-20 phi):")
for name, val in (("D", D_mw), ("kappa", k_mw), ("EY", EY_mw), ("uphi2", uphi2)):
    print("   %-6s audit %.14f   memo %.14f   diff %.1e" % (name, val, claim_mw[name], val - claim_mw[name]))
    assert abs(val - claim_mw[name]) < 1e-10
print("   phi=1: kappa=%.13f  Q=%.13f" % (k1_mw, Q1_mw))

D_tc = D_of(u_tc)
k_tc = kappa_weighted(u_tc, one)
ka_tc = kappa_weighted(u_tc, mark)
QA_tc = EY_general(u_tc, mark)
Q_tc = ordered_limit(lambda x, y, z, t: u_tc(x) * u_tc(y) * u_tc(z) * u_tc(t))
claim_tc = dict(D=1.3274992970376471, kappa=0.0117776203966976, kappa_a=0.0202278132161081,
                QA=1.6234380071702812, Q=0.3989636506914728)
print("triple-correlation (degree-12 profile, degree-24 mark):")
for name, val in (("D", D_tc), ("kappa", k_tc), ("kappa_a", ka_tc), ("QA", QA_tc), ("Q", Q_tc)):
    print("   %-8s audit %.14f   memo %.14f   diff %.1e" % (name, val, claim_tc[name], val - claim_tc[name]))
    assert abs(val - claim_tc[name]) < 1e-10
# density check: general d(x) vs the Euler-identity form (valid only for exact cosine)
xs, wxs = gl(400, -0.5, 0.5)


def Kop(f, x):
    out = []
    for xx in np.atleast_1d(x):          # split at the kink of |x-y|
        a, wa = gl(80, -0.5, xx)
        b, wb = gl(80, xx, 0.5)
        out.append(np.sum(wa * (xx - a) * f(a)) + np.sum(wb * (b - xx) * f(b)))
    return np.array(out)


for nm, u in (("cosine", ucos), ("Taylor-8", u_mw)):
    D_ = D_of(u)
    xx = np.array([0.0, 0.25, 0.5])
    uu = u(xx)
    dgen = -(uu ** 3 + 2 * uu ** 2 * Kop(u, xx) + uu * Kop(lambda s: u(s) ** 2, xx)
             - 3 * uu ** 2 - 3 * uu * Kop(u, xx) + 2 * uu)
    deul = uu * (uu ** 2 - 2 * D_ * uu - Kop(lambda s: u(s) ** 2, xx) + 3 * D_ - 2)
    print("   %s: general d(x) at 0,1/4,1/2 = %s ; Euler form diff %.1e"
          % (nm, np.array2string(dgen, precision=6), np.max(np.abs(dgen - deul))))

# ---------------------------------------------------------------- [4]
hdr("[4] sup|phi| and the range of the mark (dense grid + second-derivative bound)")


def coeffs_float(c):
    return np.array([float(Fr(x)) for x in c])


cphi = coeffs_float(PHI)
k = np.arange(len(cphi))
M2 = np.sum(np.abs(cphi[2:]) * k[2:] * (k[2:] - 1) * 0.5 ** (k[2:] - 2))
xg = np.linspace(0, 0.5, 2_000_001)
hgrid = xg[1] - xg[0]
vals = phi(xg)
sup_grid = np.max(np.abs(vals))
sup_bound = sup_grid + hgrid ** 2 / 8 * M2 + 1e-9
print("phi: max on grid %.10f ; |phi''|<=%.3e ; rigorous-ish sup bound %.10f (memo 1.0001797009)"
      % (sup_grid, M2, sup_bound))
print("     phi(0)=%.6f phi(1/2)=%.6f" % (phi(0.0), phi(0.5)))
assert sup_bound <= 1.0001797009 + 1e-8
xg2 = np.linspace(0, 0.5, 10_000_001)     # mark is even
h2 = xg2[1] - xg2[0]
am = np.concatenate([mark(xg2[i:i + 1_000_000]) for i in range(0, len(xg2), 1_000_000)])
# |P_n''| <= P_n''(1) = (n-1)n(n+1)(n+2)/8 on [-1,1]; a''(x) = 4 sum alpha_j P_2j''(2x)
M2a = 4 * sum(abs(float(a)) * (2 * j - 1) * (2 * j) * (2 * j + 1) * (2 * j + 2) / 8
              for j, a in enumerate(ALPHA))
slack = h2 ** 2 / 8 * M2a + 1e-10
print("mark a: min %.8f max %.8f on grid (|a''|<=%.2e, grid slack %.1e); need 1-beta=%.5f < a < 1"
      % (am.min(), am.max(), M2a, slack, 1 - 6001 / 5000))
assert am.max() + slack < 1 and am.min() - slack > 1 - 6001 / 5000

# ---------------------------------------------------------------- [5]
hdr("[5] scalar margins from the audit's own values")


def solve_delta(kap, q, C):
    # largest delta0 with kap > q delta0 + sqrt(delta0) C : root of q s^2 + C s - kap = 0, s=sqrt
    s = (-C + np.sqrt(C * C + 4 * q * kap)) / (2 * q)
    return s * s


sp_phi = 1.0001797009
d0 = 1 / 64200
sig = min(sp_phi ** 2 * D_mw, uphi2 + (D_mw - 1) * sp_phi ** 2 + sp_phi ** 2 * np.sqrt(d0))
Cphi = np.sqrt(sig) + r2 * (np.sqrt(EY_mw) + 3 * sp_phi * np.sqrt(D_mw - 2 / 3))
q = 6 * sp_phi
marg = (k_mw - q * d0) ** 2 - d0 * Cphi ** 2
print("multiwindow: C_phi=%.10f q=%.10f margin at 1/64200 = %.6e" % (Cphi, q, marg))
dl = d0
for _ in range(50):   # fixed point (sigma depends weakly on delta0)
    sig_ = min(sp_phi ** 2 * D_mw, uphi2 + (D_mw - 1) * sp_phi ** 2 + sp_phi ** 2 * np.sqrt(dl))
    C_ = np.sqrt(sig_) + r2 * (np.sqrt(EY_mw) + 3 * sp_phi * np.sqrt(D_mw - 2 / 3))
    dl = solve_delta(k_mw, q, C_)
print("   largest certifiable delta0 = 1/%.1f ; proportion 2-D(u)+1/64200 = %.13f"
      % (1 / dl, 2 - D_mw + 1 / 64200))
assert marg > 9e-7
beta = 6001 / 5000
d0t = 1 / 216600
Ct = 3 * beta * np.sqrt(D_tc) + r2 * np.sqrt(QA_tc) + 3 * r2 * np.sqrt(D_tc - 2 / 3)
margt = (ka_tc - 6 * d0t) ** 2 - d0t * Ct ** 2
print("triple: C=%.10f margin at 1/216600 = %.6e ; largest delta0 = 1/%.1f ; proportion %.13f"
      % (Ct, margt, 1 / solve_delta(ka_tc, 6.0, Ct), 2 - D_tc + d0t))
assert margt > 1.5e-7
Cun = 3 * r2 * (np.sqrt(Q_tc) + np.sqrt(D_tc - 2 / 3))
print("control (unmarked, sharpened (6)): largest delta0 = 1/%.1f" % (1 / solve_delta(k_tc, 6.0, Cun)))

# ---------------------------------------------------------------- [6]
hdr("[6] operator algebra: identities (zero-diagonal matrices) and full inequalities")
tr = np.trace
rng = np.random.default_rng(271803)


def lowr(n):
    return np.tril(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)), -1)


worst = 0.0
for _ in range(200):
    n = 10
    V, W = lowr(n), lowr(n)
    G, H = V + V.conj().T, W + W.conj().T
    X, Z = G - H, V - W
    ph = rng.uniform(-2, 2, n)
    Ph = np.diag(ph)
    Yf = lambda A, B: Ph @ A @ B + A @ Ph @ B + A @ B @ Ph  # noqa: E731
    pG = G @ G @ G - 3 * G @ G + 2 * G
    pH = H @ H @ H - 3 * H @ H + 2 * H
    Rm = Ph @ H @ H + H @ Ph @ H + H @ H @ Ph - 3 * (Ph @ H + H @ Ph) + 2 * Ph
    lhs = tr((pG - pH) @ Ph)
    rhs = (tr(Rm @ X) + 2 * np.real(tr(Z.conj().T @ (Yf(V, V) - Yf(W, W))))
           + 2 * np.real(tr(H @ Yf(Z, Z))) - 3 * tr(X @ X @ Ph))
    K = (W - W.conj().T) / 1j
    w4 = np.real(tr((W.conj().T @ W) @ (W.conj().T @ W)))
    worst = max(worst, abs(lhs - rhs), abs(w4 - np.real(tr(H @ H @ K @ K)) / 2) / w4,
                abs(np.real(tr(H @ K @ K)) - np.real(tr(H @ H @ H)) / 3),
                abs(np.real(tr(G @ G @ G @ Ph)) - 2 * np.real(tr(V.conj().T @ Yf(V, V)))))
    assert np.linalg.norm(W @ Ph @ W) ** 2 <= np.max(np.abs(ph)) ** 2 * w4 * (1 + 1e-12)
print("identity (3.2), tr G^3 Phi = 2Re tr(V*Y(V,V)), ||W||_4^4=tr(H^2K^2)/2, tr HK^2=trH^3/3:"
      " max residual %.1e" % worst)
print("||W Phi W||_2^2 <= ||phi||^2 ||W||_4^4 on 200 random cases: OK")
assert worst < 1e-9


# discretized continuous zero-side configurations
def config(M, uprof, rng):
    xg = -0.5 + (np.arange(M) + 0.5) / M
    sw = np.sqrt(uprof(xg) / M)
    sw = sw / np.sqrt(np.sum(sw ** 2))
    nS = int(rng.integers(2, 9))
    nd = int(rng.integers(0, 3))
    npair = int(rng.integers(0, 3))
    base = rng.permutation(np.arange(0, 14))
    jit = rng.choice([0.02, 0.1, 0.3])
    gam = 2 * np.pi * (base[:nS + nd + npair] + jit * rng.normal(size=nS + nd + npair))
    vec = lambda z: sw * np.exp(1j * z * xg)  # noqa: E731
    P = np.zeros((M, M), complex)
    Q = np.zeros((M, M), complex)
    for g in gam[:nS]:
        v = vec(g)
        P += np.outer(v, v.conj())
    for g in gam[nS:nS + nd]:
        v = vec(g)
        Q += 2 * np.outer(v, v.conj())
    for g in gam[nS + nd:]:
        bt = rng.uniform(0.2, 3.0)
        a, b = vec(g + 1j * bt), vec(g - 1j * bt)
        Q += np.outer(a, b.conj()) + np.outer(b, a.conj())
    N = nS + 2 * nd + 2 * npair
    return xg, P, Q, nS, N


def proj_pos(A, tol=1e-9):
    w, U = np.linalg.eigh((A + A.conj().T) / 2)
    idx = w > tol
    return U[:, idx] @ U[:, idx].conj().T


def volt(A):
    return np.tril(A, -1) + np.diag(np.diag(A)) / 2


viol_mw = viol_tc = -1e9
ratios_mw, ratios_tc = [], []
for trial in range(60):
    M = 500
    xg, P, Q, S, N = config(M, ucos if trial % 2 else flat, rng)
    G = P + Q
    w, U = np.linalg.eigh(Q)
    Bq = (U * np.maximum(w, 0)) @ U.conj().T
    Cq = (U * np.maximum(-w, 0)) @ U.conj().T
    F = proj_pos(Bq)
    J = np.eye(M) - F
    E = proj_pos(J @ (P - Cq) @ J)
    H = E + 2 * F
    X = G - H
    d2 = np.linalg.norm(X) ** 2
    Mtr = np.real(tr(G))
    Delta = np.real(tr(G @ G)) - 4 * Mtr + 2 * N + S
    V = volt(G)
    pG = G @ G @ G - 3 * G @ G + 2 * G
    # multiwindow inequality with a random signed polynomial multiplier
    cc = rng.normal(size=4)
    ph = np.polyval(cc, xg)
    nph = np.max(np.abs(ph))
    Ph = np.diag(ph)
    Yv = Ph @ V @ V + V @ Ph @ V + V @ V @ Ph
    lhs = -np.real(tr(pG @ Ph))
    rhs = (6 * nph * Delta + np.sqrt(max(Delta, 0)) * (nph * np.sqrt(2 * N - S)
           + r2 * (np.linalg.norm(Yv) + 3 * nph * np.sqrt((4 * N - 3 * S) / 3))))
    viol_mw = max(viol_mw, lhs - rhs)
    ratios_mw.append(lhs / rhs if rhs > 0 else 0)
    # triple inequality with a random mark in [1-beta,1]
    bt = rng.uniform(0, 2.5)
    bvec = bt * rng.uniform(0, 1) * (1 + np.cos(2 * np.pi * rng.uniform() + 7 * xg)) / 2
    beta_ = max(np.max(bvec), 1e-12)
    a = 1 - bvec
    alpha = max(1.0, beta_ - 1)
    A = np.diag(a)
    Sv = A @ V @ V + V @ A @ V + V @ V @ A
    lhs = -np.real(tr(A @ pG))
    rhs = (6 * alpha * Delta + np.sqrt(max(Delta, 0)) * (beta_ * np.sqrt(2 * N - S) + r2 * (
        np.linalg.norm(Sv) + (2 * alpha + 1) * np.sqrt((4 * N - 3 * S) / 3)
        + beta_ * np.sqrt(2 * (2 * N - S)))))
    viol_tc = max(viol_tc, lhs - rhs)
    ratios_tc.append(lhs / rhs if rhs > 0 else 0)
print("discretized continuous configurations (M=500, simple/double/off-line pairs, 60 cases):")
print("   multiwindow Thm 3.2: max(lhs-rhs)=%.3e, max lhs/rhs=%.3f" % (viol_mw, max(ratios_mw)))
print("   triple Thm 5.1     : max(lhs-rhs)=%.3e, max lhs/rhs=%.3f" % (viol_tc, max(ratios_tc)))
assert viol_mw < 1e-6 and viol_tc < 1e-6
print("\nall assertions passed (%.0fs)" % (time.time() - T0))
