#!/usr/bin/env python3
"""Multiwindow / localized certificates for the simple-zero proportion.

Companion to docs/research/multiwindow_20261003.md.  Sections and labels:

  [A] NUMERICAL sanity: finite-matrix checks of the operator identities used
      in the memo (strictly lower-triangular matrices are the exact finite
      analogue of continuous Volterra kernels).
  [B] NUMERICAL: Gauss-Legendre evaluation of the vertex-weighted (polarized)
      pair, cubic and ordered-fourth functionals; flat and cosine controls;
      the localized cubic defect density c(x) of the cosine profile.
  [C] CHECKED (exact rational arithmetic): the localized certificate for the
      Taylor-8 cosine profile and a fixed rational even multiplier phi of
      degree 20.  All profile integrals are exact rationals, sup|phi| is
      bounded by exact Bernstein subdivision, square roots by rational
      ceilings.  Also a phi=1 control reproducing the 2026-09-05 constant.
      This checks the scalar/profile part ONLY; the operator inequality is
      proved in the memo and the analytic transfer is the multilinear
      extension of ordered_moment_20260905.md sections 1-5, 8 (not
      machine-checked).
  [D] NUMERICAL: the second-order (pair-measure) LP, with and without
      off-band Bochner positivity of the form factor.
  [E] NUMERICAL (optional, needs cvxpy, flag --socp): the SOCP that selects
      the best multiplier phi in an even Legendre basis.
  [F] NUMERICAL: independent checks of the vertex-weighted formulas against
      CUE (full circle for traces; half-circle arc + fine grid for ordered
      norms) and the exact lattice reduction of the C0 term.

Run:  python3 verify/multiwindow_certificate.py [--socp]
"""

import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial, isqrt

import numpy as np
from numpy.polynomial.legendre import leggauss

T0 = time.time()


def hdr(s):
    print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78, flush=True)


# ---------------------------------------------------------------------------
# [A] finite-matrix identity checks
# ---------------------------------------------------------------------------
hdr("[A] NUMERICAL sanity: finite-matrix operator identities")
rng = np.random.default_rng(20261003)
n = 11


def rlow():
    return np.tril(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)), -1)


tr = np.trace
worst = 0.0
for _ in range(5):
    V, Wm = rlow(), rlow()
    Z = V - Wm
    G = V + V.conj().T
    H = Wm + Wm.conj().T
    X = G - H
    Phi = np.diag(rng.normal(size=n))

    def Y(A, B):
        return Phi @ A @ B + A @ Phi @ B + A @ B @ Phi

    def p(M):
        return M @ M @ M - 3 * M @ M + 2 * M

    R = Phi @ H @ H + H @ Phi @ H + H @ H @ Phi - 3 * (Phi @ H + H @ Phi) + 2 * Phi
    lhs = tr((p(G) - p(H)) @ Phi)
    rhs = (tr(R @ X) + 2 * np.real(tr(Z.conj().T @ (Y(V, V) - Y(Wm, Wm))))
           + 2 * np.real(tr(H @ Y(Z, Z))) - 3 * tr(X @ X @ Phi))
    worst = max(worst, abs(lhs - rhs))
print("identity (3.2) tr((p(G)-p(H))Phi) = tr(R X)+2Re tr(Z*(Y_V-Y_W))"
      "+2Re tr(H Y(Z,Z))-3tr(X^2 Phi): max error %.2e" % worst)
assert worst < 1e-9

Q_, _ = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))
E = Q_[:, :3] @ Q_[:, :3].conj().T
F = Q_[:, 3:5] @ Q_[:, 3:5].conj().T
I = np.eye(n)
P0 = I - E - F
H2 = E + 2 * F
Phi = np.diag(rng.normal(size=n))
R2 = (Phi @ H2 @ H2 + H2 @ Phi @ H2 + H2 @ H2 @ Phi
      - 3 * (Phi @ H2 + H2 @ Phi) + 2 * Phi)
err = np.abs(R2 - (2 * P0 @ Phi @ P0 - E @ Phi @ E + 2 * F @ Phi @ F)).max()
print("block form R = 2 Pi0 Phi Pi0 - E Phi E + 2 F Phi F for H=E+2F: error %.2e" % err)
assert err < 1e-12

worst4 = 0.0
worst3 = 0.0
ratio = 0.0
for _ in range(5):
    Wm = rlow()
    H = Wm + Wm.conj().T
    K = (Wm - Wm.conj().T) / 1j
    A = Wm.conj().T @ Wm
    s4 = np.real(tr(A @ A))
    worst4 = max(worst4, abs(s4 - np.real(tr(H @ H @ K @ K)) / 2) / s4)
    worst3 = max(worst3, abs(np.real(tr(H @ K @ K)) - np.real(tr(H @ H @ H)) / 3))
    for _ in range(20):
        ph = rng.uniform(-1, 1, n)
        ratio = max(ratio, np.linalg.norm(Wm @ np.diag(ph) @ Wm) ** 2 / s4)
print("||W||_4^4 = tr(H^2K^2)/2 : max rel. error %.2e" % worst4)
print("tr(H K^2) = tr(H^3)/3    : max error %.2e" % worst3)
print("max ||W Phi W||_2^2/||W||_4^4 over |phi|<=1 samples: %.4f (must be <=1)" % ratio)
assert worst4 < 1e-10 and worst3 < 1e-9 and ratio <= 1

# ---------------------------------------------------------------------------
# [B] float functionals
# ---------------------------------------------------------------------------
hdr("[B] NUMERICAL: polarized functionals (Gauss-Legendre)")
NG = 48
gt, gw = leggauss(NG)


def nodes(a, b):
    a = np.asarray(a)[..., None]
    b = np.asarray(b)[..., None]
    return (b - a) / 2 * gt + (b + a) / 2, (b - a) / 2 * gw


z1, wz1 = nodes(np.array(-0.5), np.array(0.5))
v2, wv2 = nodes(np.zeros(NG), 0.5 - z1)
Z2 = np.broadcast_to(z1[:, None], v2.shape)
W2 = wz1[:, None] * wv2
s3, ws3 = nodes(np.zeros(NG), 0.5 - z1)
v3, wv3 = nodes(np.zeros((NG, NG)), s3)
Z3 = np.broadcast_to(z1[:, None, None], v3.shape)
W3 = wz1[:, None, None] * ws3[:, :, None] * wv3
w3 = np.broadcast_to(s3[:, :, None], v3.shape) - v3


def Kabs(f, g):
    a, b = Z2 + v2, Z2
    return np.sum(W2 * v2 * (f(a) * g(b) + f(b) * g(a)))


def Pf(wx, wy):
    return np.sum(wz1 * wx(z1) * wy(z1)) + Kabs(wx, wy)


def Tf(wa, wb, wc):
    def pr(f, g):
        return lambda s: f(s) * g(s)
    return (np.sum(wz1 * wa(z1) * wb(z1) * wc(z1)) + Kabs(pr(wa, wc), wb)
            + Kabs(pr(wa, wb), wc) + Kabs(pr(wb, wc), wa))


def Qf(wx, wy, wz, wt):
    t0 = np.sum(wz1 * wx(z1) * wy(z1) * wz(z1) * wt(z1)) / 6
    a, b = Z2 + v2, Z2
    f = (wx(a) * wt(a) * wy(b) * wz(b) + wx(a) * wy(b) * wz(b) * wt(b)
         + wx(a) * wy(a) * wt(a) * wz(b) + wx(a) * wy(a) * wz(b) * wt(b))
    t1 = np.sum(W2 * v2 * f) / 3
    zz, v, w = Z3, v3, w3
    f2 = (wx(zz + v + w) * wy(zz + w) * wt(zz + w) * wz(zz)
          + wx(zz + v + w) * wy(zz + w) * wt(zz + v) * wz(zz))
    return t0 + t1 + np.sum(W3 * v * w * f2)


one = lambda s: np.ones_like(s)  # noqa: E731
print("flat: D=%.12f (4/3)  M3=%.12f (2)  Q=%.12f (73/180=%.12f)"
      % (Pf(one, one), Tf(one, one, one), Qf(one, one, one, one), 73 / 180))
r2 = np.sqrt(2)
ucos = lambda s: np.cos(r2 * s) / (r2 * np.sin(1 / r2))  # noqa: E731
Dc = Pf(ucos, ucos)
M3c = Tf(ucos, ucos, ucos)
Qc = Qf(ucos, ucos, ucos, ucos)
print("cosine: D=%.13f  kappa=3D-2-M3=%.13f  Q=%.13f" % (Dc, 3 * Dc - 2 - M3c, Qc))


def kappa_phi(u, phi):
    up = lambda s: u(s) * phi(s)  # noqa: E731
    return -(Tf(up, u, u) - 3 * Pf(up, u) + 2 * np.sum(wz1 * up(z1)))


def EY(u, phi):
    tot = 0.0
    for A in range(3):
        for B in range(3):
            fx = lambda s, A=A, B=B: u(s) * phi(s) ** ((A == 0) + (B == 0))  # noqa: E731
            fy = lambda s, A=A: u(s) * phi(s) ** (A == 1)  # noqa: E731
            fz = lambda s, A=A, B=B: u(s) * phi(s) ** ((A == 2) + (B == 2))  # noqa: E731
            ft = lambda s, B=B: u(s) * phi(s) ** (B == 1)  # noqa: E731
            tot += Qf(fx, fy, fz, ft)
    return tot


print("\nlocalized cubic defect density of the cosine, c(x)=u(u^2-2Du-K(u^2)+3D-2):")
gx, gwx = leggauss(400)
xs, wx4 = gx / 2, gwx / 2      # fine grid: the kernel |x-y| has a kink
Kmat = np.abs(xs[:, None] - xs[None, :]) * wx4[None, :]
uu = ucos(xs)
cd = uu * (uu ** 2 - 2 * Dc * uu - Kmat @ (uu ** 2) + 3 * Dc - 2)
print("  int c = %.10f (=kappa), int |c| = %.10f, int c_+ = %.10f, int c_- = %.10f"
      % (wx4 @ cd, wx4 @ np.abs(cd), wx4 @ np.maximum(cd, 0), wx4 @ np.minimum(cd, 0)))
for xv in [0, 0.1, 0.2, 0.3, 0.4, 0.5]:
    xx = np.array([xv])
    ux = ucos(xx)
    kx = np.sum(wx4 * np.abs(xv - xs) * ucos(xs) ** 2)
    print("  x=%.1f  c(x)=%+.6f" % (xv, (ux * (ux ** 2 - 2 * Dc * ux - kx + 3 * Dc - 2))[0]))
print("  phi=1 control: kappa=%.10f, E_Y=9Q=%.10f" % (kappa_phi(ucos, one), EY(ucos, one)))

# ---------------------------------------------------------------------------
# [C] exact certificate
# ---------------------------------------------------------------------------
hdr("[C] CHECKED: exact rational localized certificate")
from sympy import QQ  # noqa: E402
from sympy.polys.rings import ring  # noqa: E402

Rg, Xg, Vg, Wg = ring("x,v,w", QQ)
HALF = QQ(1, 2)
Zs = Xg - HALF


def simplex(Pol, k):
    s = QQ(0)
    for (a, b, c), co in Pol.terms():
        if k == 2:
            assert c == 0
        s += co * QQ(factorial(a) * factorial(b) * factorial(c), factorial(a + b + c + k))
    return s


def interval(Pol):
    s = QQ(0)
    for (a, b, c), co in Pol.terms():
        assert b == 0 and c == 0
        s += co * QQ(1, a + 1)
    return s


class Wt:
    def __init__(self, c):
        self.c = [QQ(x) for x in c]

    def at(self, arg):
        r, pw = Rg(0), Rg(1)
        for c in self.c:
            r += c * pw
            pw = pw * arg
        return r

    def __mul__(self, o):
        out = [QQ(0)] * (len(self.c) + len(o.c) - 1)
        for i, a in enumerate(self.c):
            for j, b in enumerate(o.c):
                out[i + j] += a * b
        return Wt(out)


def eK(f, g):
    return simplex(Vg * (f.at(Zs + Vg) * g.at(Zs) + f.at(Zs) * g.at(Zs + Vg)), 2)


def eP(wx, wy):
    return interval((wx * wy).at(Zs)) + eK(wx, wy)


def eT(wa, wb, wc):
    return (interval((wa * wb * wc).at(Zs)) + eK(wa * wc, wb) + eK(wa * wb, wc)
            + eK(wb * wc, wa))


def eQ(wx, wy, wz, wt):
    t0 = interval((wx * wy * wz * wt).at(Zs)) / 6
    a, b = Zs + Vg, Zs
    f = ((wx * wt).at(a) * (wy * wz).at(b) + wx.at(a) * (wy * wz * wt).at(b)
         + (wx * wy * wt).at(a) * wz.at(b) + (wx * wy).at(a) * (wz * wt).at(b))
    t1 = simplex(Vg * f, 2) / 3
    f2 = (wx.at(Zs + Vg + Wg) * (wy * wt).at(Zs + Wg) * wz.at(Zs)
          + wx.at(Zs + Vg + Wg) * wy.at(Zs + Wg) * wt.at(Zs + Vg) * wz.at(Zs))
    return t0 + t1 + simplex(Vg * Wg * f2, 3)


def eint(w):
    return interval(w.at(Zs))


def eEY(p, phi):
    tot = QQ(0)
    for A in range(3):
        for B in range(3):
            def pw(k):
                r = Wt([1])
                for _ in range(k):
                    r = r * phi
                return r
            tot += eQ(p * pw((A == 0) + (B == 0)), p * pw(A == 1),
                      p * pw((A == 2) + (B == 2)), p * pw(B == 1))
    return tot


def sqrt_up(r, den=10 ** 12):
    r = Fr(int(r.numerator), int(r.denominator))
    s = Fr(isqrt(r.numerator * den * den // r.denominator) + 1, den)
    assert s * s >= r
    return QQ(s.numerator, s.denominator)


def sup_abs_bernstein(c, lo=Fr(0), hi=Fr(1, 2), pieces=400):
    """Rigorous upper bound of max |poly| on [lo,hi] (exact Bernstein subdivision)."""
    h = (hi - lo) / pieces
    m = Fr(0)
    nn = len(c) - 1
    for i in range(pieces):
        a = lo + i * h
        cs = [Fr(0)] * (nn + 1)
        for j, cj in enumerate(c):
            if cj == 0:
                continue
            for k in range(j + 1):
                cs[k] += cj * comb(j, k) * a ** (j - k) * h ** k
        b = [sum(Fr(comb(k, j), comb(nn, j)) * cs[j] for j in range(k + 1)) for k in range(nn + 1)]
        m = max(m, max(abs(x) for x in b))
    return m


# profile: degree-8 Taylor polynomial of cos(sqrt2 x), normalized on [-1/2,1/2]
pc = [1, 0, -1, 0, QQ(1, 6), 0, QQ(-1, 90), 0, QQ(1, 2520)]
pW = Wt(pc)
mass = eint(pW)
# positivity of the profile on |x|<=1/2, with t=x^2 in [0,1/4]:
# p = (1-t) + t^2 (1/6 - t/90 + t^2/2520) >= 3/4 + t^2 (1/6 - 1/360) > 0.
assert Fr(1, 6) - Fr(1, 360) > 0
D = eP(pW, pW) / mass ** 2
twoD = 2 - D
print("profile u = p8/int p8,  D(u) = %.16f,  2 - D(u) = %.16f" % (float(D), float(twoD)))
print("  (2 - D* = 0.6725007036794116457..., difference < 1e-17)")

# --- control: phi = 1 with the 2026-09-05 scalar inequality (6) ---
M3 = eT(pW, pW, pW) / mass ** 3
kap1 = 3 * D - 2 - M3
Q1 = eQ(pW, pW, pW, pW) / mass ** 4
d1 = QQ(1, 272000)
C1 = 3 * sqrt_up(QQ(2)) * (sqrt_up(Q1) + sqrt_up(D - QQ(2, 3)))
lhs1 = kap1 - 6 * d1
ok1 = lhs1 > 0 and lhs1 ** 2 > d1 * C1 ** 2
print("control phi=1: kappa=%.12f Q=%.12f ; inequality (6) excludes delta<=1/272000: %s"
      % (float(kap1), float(Q1), ok1))
assert ok1

# --- localized multiplier phi (rational, even, degree 20; from the SOCP of [E]) ---
PHI = ['9991281/10000000', '0', '623581/1000000', '0', '-1316105007/10000000', '0',
       '35539677201/5000000', '0', '-184900986473/2500000', '0',
       '-7105319268637/2500000', '0', '65741450766381/1000000', '0',
       '-5706449438243701/10000000', '0', '781128124322477/312500', '0',
       '-3460209003147011/625000', '0', '1545712609558661/312500']
phic = [Fr(s) for s in PHI]
t = time.time()
sp = sup_abs_bernstein(phic)        # phi even: [0,1/2] suffices
spq = QQ(sp.numerator, sp.denominator)
print("sup_{|x|<=1/2} |phi| <= %.10f  (Bernstein, 400 pieces, %.1fs)" % (float(sp), time.time() - t))
phiW = Wt([QQ(x.numerator, x.denominator) for x in phic])
t = time.time()
pphi = pW * phiW
kap = -(eT(pphi, pW, pW) / mass ** 3 - 3 * eP(pphi, pW) / mass ** 2 + 2 * eint(pphi) / mass)
EYx = eEY(pW, phiW) / mass ** 4
uphi2 = eint(pW * phiW * phiW) / mass
print("kappa_phi = %.14f   E_Y(phi) = %.14f   int u phi^2 = %.14f   (%.1fs)"
      % (float(kap), float(EYx), float(uphi2), time.time() - t))

K_DEN = 64200
d0 = QQ(1, K_DEN)
sd0 = sqrt_up(d0)
sig = min(spq ** 2 * D, uphi2 + (D - 1) * spq ** 2 + spq ** 2 * sd0)
w2 = sqrt_up(D - QQ(2, 3))
Cphi = sqrt_up(sig) + sqrt_up(QQ(2)) * (sqrt_up(EYx) + 3 * spq * w2)
q = 6 * spq
lhs = kap - q * d0
margin = lhs ** 2 - d0 * Cphi ** 2
print("C_phi <= %.12f,  q = 6 sup|phi| = %.12f" % (float(Cphi), float(q)))
print("(kappa_phi - q d0)^2 - d0 C_phi^2 = %s ~ %.6e  with d0 = 1/%d"
      % ("positive" if margin > 0 else "NOT positive", float(margin), K_DEN))
assert lhs > 0 and margin > 0
prop = twoD + d0
print("CHECKED scalar implication: liminf N_0^s/N >= 2 - D(u) + 1/%d = %.13f..."
      % (K_DEN, float(prop)))
print("  previous frontier 0.6725043820976; increment over it: %.3e"
      % (float(prop) - 0.6725043820976089))

# ---------------------------------------------------------------------------
# [D] pair LP
# ---------------------------------------------------------------------------
hdr("[D] NUMERICAL: second-order (pair-measure) LP, multiplicities <= 2, real zeros")
from scipy.integrate import quad  # noqa: E402
from scipy.optimize import linprog  # noqa: E402

Dstar = 0.5 + 1 / np.tan(1 / r2) / r2


def pair_lp(S=40.0, ds=0.02, h=0.05, positivity=False, amax=4.0):
    s = np.arange(1, int(round(S / ds)) + 1) * ds
    rows, rhs = [], []
    for am in np.arange(0, 1 - h + 1e-9, h / 2):
        mult = 1.0 if am == 0 else 2.0
        f = lambda t, am=am, mult=mult: mult * h * np.sinc(h * t) ** 2 * np.cos(2 * np.pi * am * t)  # noqa: E731
        tail = 2 * quad(f, S, S + 4000, limit=4000)[0]
        fhat0 = mult * max(0.0, 1 - am / h)
        mom = mult * quad(lambda a, am=am: abs(a) * max(0, 1 - abs(a - am) / h),
                          am - h, am + h, points=[0])[0]
        rows.append(np.concatenate([[mult * h], 2 * f(s)]))
        rhs.append(fhat0 + mom - tail)
    Aub = bub = None
    if positivity:
        ag = np.arange(1.0, amax, 0.01)
        Aub = -np.column_stack([np.ones_like(ag), 2 * np.cos(2 * np.pi * np.outer(ag, s))])
        bub = -np.sin(2 * np.pi * S * ag) / (np.pi * ag)
    c = np.zeros(len(s) + 1)
    c[0] = -1
    r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=np.array(rows), b_eq=np.array(rhs),
                bounds=[(0, None)] * (len(s) + 1), method="highs")
    return -r.fun if r.status == 0 else None


print("max diagonal atom A (simple fraction = 2 - A) ; D* = %.10f" % Dstar)
for S in [20.0, 40.0]:
    a0 = pair_lp(S)
    a1 = pair_lp(S, positivity=True)
    print("  S=%4.0f  band data only: A=%.6f (D*-A=%.5f)   + F>=0 on [1,4]: A=%.6f"
          % (S, a0, Dstar - a0, a1))
print("  (truncation: tail beyond S fixed to Lebesgue density 1; gap ~0.08/S)")

# ---------------------------------------------------------------------------
# [E] optional SOCP
# ---------------------------------------------------------------------------
if "--socp" in sys.argv:
    hdr("[E] NUMERICAL: SOCP selection of the multiplier (even Legendre basis)")
    import cvxpy as cp
    from numpy.polynomial import legendre as Lg

    def basis(k):
        c = np.zeros(2 * k + 1)
        c[2 * k] = 1
        return lambda s, c=c: Lg.legval(2 * s, c)

    def Mentry(f, g):
        tot = 0.0
        for A in range(3):
            for B in range(3):
                def wv(s, vert, A=A, B=B):
                    r = ucos(s)
                    if vert == "x":
                        r = r * (f(s) if A == 0 else 1) * (g(s) if B == 0 else 1)
                    if vert == "y":
                        r = r * (f(s) if A == 1 else 1)
                    if vert == "z":
                        r = r * (f(s) if A == 2 else 1) * (g(s) if B == 2 else 1)
                    if vert == "t":
                        r = r * (g(s) if B == 1 else 1)
                    return r
                tot += Qf(lambda s: wv(s, "x"), lambda s: wv(s, "y"),
                          lambda s: wv(s, "z"), lambda s: wv(s, "t"))
        return tot

    for K in [0, 2, 4, 6]:
        bs = [basis(k) for k in range(K + 1)]
        kv = np.array([kappa_phi(ucos, b) for b in bs])
        M = np.zeros((K + 1, K + 1))
        for i in range(K + 1):
            for j in range(i, K + 1):
                M[i, j] = M[j, i] = 0.5 * (Mentry(bs[i], bs[j]) + Mentry(bs[j], bs[i]))
        U = np.array([[np.sum(wz1 * ucos(z1) * bi(z1) * bj(z1)) for bj in bs] for bi in bs])
        xg = np.linspace(0, 0.5, 301)
        B = np.array([b(xg) for b in bs]).T

        def sq(A):
            w, V = np.linalg.eigh(A)
            return (V * np.sqrt(np.clip(w, 0, None))) @ V.T
        a = cp.Variable(K + 1)
        s = cp.Variable()
        C = (cp.norm(cp.hstack([sq(U) @ a, np.sqrt(Dc - 1) * s]))
             + r2 * (cp.norm(sq(M) @ a) + 3 * s * np.sqrt(Dc - 2 / 3)))
        cp.Problem(cp.Maximize(kv @ a), [C <= 1, B @ a <= s, -B @ a <= s]).solve(solver="CLARABEL")
        val = kv @ a.value
        print("  K=%d (degree %2d): max kappa/C = %.6f, (kappa/C)^2 = 1/%.0f"
              % (K, 2 * K, val, 1 / val ** 2), flush=True)

# ---------------------------------------------------------------------------
# [F] independent random-matrix checks of the vertex-weighted formulas
# ---------------------------------------------------------------------------
hdr("[F] NUMERICAL: independent checks (CUE, lattice) of the weighted formulas")
rngF = np.random.default_rng(17)


def haar(Nn):
    Zg = (rngF.normal(size=(Nn, Nn)) + 1j * rngF.normal(size=(Nn, Nn))) / np.sqrt(2)
    Qm, Rm = np.linalg.qr(Zg)
    return Qm * (np.diag(Rm) / abs(np.diag(Rm)))


# (F1) localized cubic defect: full-circle CUE in mode space samples traces exactly
Nn, SAMP = 160, 300
ks = np.arange(-(Nn // 2), Nn // 2 + 1)
xk = ks / Nn
uk = ucos(xk) / Nn
tests = {"1": lambda s: np.ones_like(s), "1-8x^2": lambda s: 1 - 8 * s ** 2,
         "4x^2": lambda s: (2 * s) ** 2}
accF = {k: [] for k in tests}
for _ in range(SAMP):
    th = np.angle(np.linalg.eigvals(haar(Nn)))
    trU = np.exp(1j * np.outer(np.arange(-Nn, Nn + 1), th)).sum(1)
    Gm = np.sqrt(np.outer(uk, uk)) * trU[(ks[:, None] - ks[None, :]) + Nn]
    pG = Gm @ Gm @ Gm - 3 * Gm @ Gm + 2 * Gm
    for k, f in tests.items():
        accF[k].append(-np.real(np.sum(np.diag(pG) * f(xk))) / Nn)
for k, f in tests.items():
    v = np.array(accF[k])
    print("  kappa_phi, phi=%-7s CUE N=%d (%d samples): %.5f +- %.5f   formula %.5f"
          % (k, Nn, SAMP, v.mean(), v.std() / np.sqrt(SAMP), kappa_phi(ucos, f)))

# (F2) ordered quartic E_Y: eigenvalues on a half-circle arc (a height window),
# continuous frequency grid, trapezoid-corrected triangular truncation.
phiF = lambda s: 1 - 8 * s ** 2  # noqa: E731
EYth, Qth = EY(ucos, phiF), Qc
for Nc, ng, smp in [(80, 800, 24), (160, 1600, 12)]:
    xg = np.linspace(-0.5, 0.5, ng)
    hg = xg[1] - xg[0]
    wg = np.full(ng, hg)
    wg[0] = wg[-1] = hg / 2
    pg = phiF(xg)
    Qs, Es = [], []
    for _ in range(smp):
        th = np.angle(np.linalg.eigvals(haar(Nc)))
        th = th[np.abs(th) < np.pi / 2]
        Fm = np.sqrt(ucos(xg) * wg)[:, None] * np.exp(2j * np.pi * np.outer(xg, Nc * th / (2 * np.pi)))
        Gm = Fm @ Fm.conj().T
        Vm = np.tril(Gm, -1) + np.diag(np.diag(Gm)) / 2
        V2 = Vm @ Vm
        Ym = pg[:, None] * V2 + Vm @ (pg[:, None] * Vm) + V2 * pg[None, :]
        Qs.append(np.linalg.norm(V2) ** 2 / len(th))
        Es.append(np.linalg.norm(Ym) ** 2 / len(th))
    Qs, Es = np.array(Qs), np.array(Es)
    print("  arc-CUE Nc=%d (~%d pts): Q %.4f+-%.4f (formula %.4f)   E_Y(1-8x^2) %.4f+-%.4f (formula %.4f)"
          % (Nc, Nc // 2, Qs.mean(), Qs.std() / np.sqrt(smp), Qth, Es.mean(), Es.std() / np.sqrt(smp), EYth))
print("  (finite-size values approach the formulas from below; see the memo)")

# (F3) lattice (no fluctuation in band): ordered quartic reduces exactly to
# u^4 int_0^lam (lam-s)|K_+*K_+(s)|^2 ds -> C0 int u^4 = 1/(6 lam^3).
lam = 0.8
for Mm in [40, 80]:
    jj = np.arange(Mm)
    dd = jj[:, None] - jj[None, :]

    def cK(s):
        with np.errstate(divide="ignore", invalid="ignore"):
            term = np.where(dd != 0, (np.exp(2j * np.pi * dd * s) - 1) / (2j * np.pi * np.where(dd != 0, dd, 1)), s)
        return np.sum(np.exp(2j * np.pi * jj[None, :] * s) * term)
    edges = np.linspace(0, lam, int(40 * Mm * lam) + 1)
    tt, ww = leggauss(6)
    tot = 0.0
    for lo_, hi_ in zip(edges[:-1], edges[1:]):
        ss = (hi_ - lo_) * (tt + 1) / 2 + lo_
        tot += np.sum(ww * (hi_ - lo_) / 2 * (lam - ss) * np.array([abs(cK(s)) ** 2 for s in ss]))
    print("  lattice M=%d: ||V^2||^2/M = %.4f   (limit C0/lam^3 = %.4f, log-slow)" % (Mm, tot / lam ** 4 / Mm, 1 / (6 * lam ** 3)))

print("\ntotal time %.1fs" % (time.time() - T0))
