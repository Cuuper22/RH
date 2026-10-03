#!/usr/bin/env python3
"""
Unconditional (complex-zero) analogue of the Conrey--Ghosh--Gonek mollified
discrete moments, and the exact size of the loss caused by off-line zeros.

Companion to docs/research/mollified_discrete_20261003.md.  Every block prints
its label (CHECKED = exact rational/Gaussian-rational arithmetic, NUMERICAL =
floating point diagnostics).  No zeta data is used; the inputs are the published
main-term constants of CGG (1998) (2.5)-(2.7), proved unconditionally for the
holomorphic sums S1, S2 by Bui--Heath-Brown (2013, Lemma 1 + Lemma 2).

Notation (CGG):  F(s) = B(s) zeta'(s),  B(s) = sum_{k<=y} mu(k) P(log(y/k)/log y) k^{-s},
y = T^theta, P(0)=0, P(1)=1, L = log(T/2pi), N = T L/(2pi).
    S1 = sum_{0<gamma<=T} F(rho)            ~ c1(P,theta) N L
    S2 = sum_{0<gamma<=T} F(rho) F(1-rho)   ~ c2(P,theta) N L^2
    c1 = 1/2 + theta I,  c2 = 1/3 + theta I + theta^2 I^2 + J/(12 theta),
    I = int_0^1 P,  J = int_0^1 P'^2.
Both sums run over ALL zeros in the rectangle (residues of zeta'/zeta), each
nonsimple zero contributing 0 because F vanishes there.
"""
from fractions import Fraction as Fr
import math
import random
import sys

random.seed(20261003)

OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    OUT.append(s)


# ----------------------------------------------------------------------------
# exact polynomial helpers (coefficient lists, index = power)
# ----------------------------------------------------------------------------
def p_eval(c, x):
    return sum(ci * x**i for i, ci in enumerate(c))


def p_int01(c):
    return sum(ci / (i + 1) for i, ci in enumerate(c))


def p_der(c):
    return [i * ci for i, ci in enumerate(c)][1:] or [Fr(0)]


def p_mul(a, b):
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            r[i + j] += ai * bj
    return r


def cgg_constants(P, th):
    """c1, c2 of CGG (2.5)-(2.7) for polynomial P (exact)."""
    assert p_eval(P, Fr(0)) == 0 and p_eval(P, Fr(1)) == 1
    I = p_int01(P)
    J = p_int01(p_mul(p_der(P), p_der(P)))
    c1 = Fr(1, 2) + th * I
    c2 = Fr(1, 3) + th * I + th * th * I * I + J / (12 * th)
    return c1, c2, I, J


say("=" * 78)
say("BLOCK A (CHECKED): CGG/BHB main-term constants, exact rational")
say("=" * 78)
th = Fr(1, 2)
P_cgg = [Fr(0), 1 + th, -th]          # P(x) = (1+theta) x - theta x^2
c1, c2, I, J = cgg_constants(P_cgg, th)
say(f"theta = {th}, P = (1+theta)x - theta x^2: I = {I}, J = {J}")
say(f"c1 = {c1}  (CGG: 19/24)   c2 = {c2}  (CGG: 57/64)   c1^2/c2 = {c1*c1/c2}  (CGG: 19/27)")
assert c1 == Fr(19, 24) and c2 == Fr(57, 64) and c1 * c1 / c2 == Fr(19, 27)
say("PASS: reproduces 19/24, 57/64, 19/27 exactly.")

# ----------------------------------------------------------------------------
say()
say("=" * 78)
say("BLOCK B (CHECKED): quadratic P is optimal; closed form kappa(theta)=1-(1+theta)^-3")
say("=" * 78)
# B1: for fixed I, J >= 1 + 12 (I-1/2)^2 with equality iff P is the quadratic
#     q(x) = x + 6(I-1/2) x(1-x); check J - J_min = int (P'-q')^2 exactly on random P.
for trial in range(6):
    deg = random.randint(2, 7)
    # random polynomial with P(0)=0 then rescale to P(1)=1
    c = [Fr(0)] + [Fr(random.randint(-9, 9), random.randint(1, 5)) for _ in range(deg)]
    s = p_eval(c, Fr(1))
    if s == 0:
        c[1] += 1
        s = p_eval(c, Fr(1))
    c = [ci / s for ci in c]
    I = p_int01(c)
    J = p_int01(p_mul(p_der(c), p_der(c)))
    k = 6 * (I - Fr(1, 2))
    q = [Fr(0), 1 + k, -k]
    dq = p_der(q)
    diff = [a - b for a, b in zip(p_der(c) + [Fr(0)] * 10, dq + [Fr(0)] * 10)]
    diff = diff[:max(len(p_der(c)), len(dq))]
    resid = p_int01(p_mul(diff, diff))
    Jmin = 1 + 12 * (I - Fr(1, 2)) ** 2
    assert J - Jmin == resid, (J, Jmin, resid)
    say(f"  deg {deg}: J - (1+12(I-1/2)^2) = int(P'-q')^2 = {resid} >= 0  exact")
say("PASS: J_min(I) = 1 + 12 (I-1/2)^2, attained by the quadratic.")

# B2: with I = 1/2 + t, kappa(t) = A^2/D, A=(1+th)/2+th t,
#     D = 1/3+th/2+th t+th^2(1/2+t)^2+(1+12t^2)/(12 th).  Stationary point t=th/6 exact.
def kappa_t(th, t):
    A = (1 + th) / 2 + th * t
    D = Fr(1, 3) + th / 2 + th * t + th * th * (Fr(1, 2) + t) ** 2 + (1 + 12 * t * t) / (12 * th)
    return A * A / D


for th in [Fr(1, 10), Fr(1, 4), Fr(2, 5), Fr(49, 100), Fr(1, 2), Fr(3, 4), Fr(1)]:
    t0 = th / 6
    A = (1 + th) / 2 + th * t0
    D = Fr(1, 3) + th / 2 + th * t0 + th * th * (Fr(1, 2) + t0) ** 2 + (1 + 12 * t0 * t0) / (12 * th)
    Dp = th + 2 * th * th * (Fr(1, 2) + t0) + 2 * t0 / th
    stat = 2 * th * D - A * Dp          # derivative numerator of A^2/D up to factor A
    closed = 1 - 1 / (1 + th) ** 3
    assert stat == 0 and kappa_t(th, t0) == closed
    # second-order / global check on a grid
    best = max(kappa_t(th, Fr(i, 200) - 1) for i in range(0, 401))
    assert best <= closed
    say(f"  theta={str(th):6s}: kappa = {closed} = {float(closed):.10f}; grid max over t in [-1,1] <= kappa: ok")
say("PASS: kappa(theta) = 1 - (1+theta)^{-3} exactly, optimum P = (1+theta)x - theta x^2.")
say("      kappa(1/2) = 19/27; kappa is increasing in theta; the unconditional range is theta < 1/2.")

# ----------------------------------------------------------------------------
say()
say("=" * 78)
say("BLOCK C (CHECKED): the holomorphic pairing on mirror pairs; exact identities")
say("=" * 78)
# Gaussian-rational complex numbers as (re, im) Fractions.
def cadd(x, y): return (x[0] + y[0], x[1] + y[1])
def csub(x, y): return (x[0] - y[0], x[1] - y[1])
def cmul(x, y): return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])
def cconj(x): return (x[0], -x[1])
def cabs2(x): return x[0] * x[0] + x[1] * x[1]
def cre(x): return x[0]


def rand_c():
    return (Fr(random.randint(-20, 20), random.randint(1, 7)), Fr(random.randint(-20, 20), random.randint(1, 7)))


# Model: simple on-line zeros with values F(rho)=f_j (any complex); mirror pairs
# (rho, rho'=1-conj(rho)) with values a_k=F(rho), c_k=F(rho'); F(1-rho)=conj(F(rho'))
# because F has real Dirichlet coefficients.  Nonsimple zeros contribute 0.
for trial in range(5):
    nS, nP = random.randint(1, 8), random.randint(0, 6)
    f = [rand_c() for _ in range(nS)]
    pairs = [(rand_c(), rand_c()) for _ in range(nP)]
    # S1 and S2 as the residue sums
    S1 = (Fr(0), Fr(0))
    S2 = (Fr(0), Fr(0))
    for v in f:
        S1 = cadd(S1, v)
        S2 = cadd(S2, cmul(v, cconj(v)))                      # on-line: F(1-rho)=conj F(rho)
    for a, c in pairs:
        S1 = cadd(cadd(S1, a), c)
        S2 = cadd(S2, cmul(a, cconj(c)))                      # rho : F(rho)F(1-rho)=a conj(c)
        S2 = cadd(S2, cmul(c, cconj(a)))                      # rho': c conj(a)
    assert S2[1] == 0, "S2 must be real"
    S2 = S2[0]
    Delta = sum(cabs2(csub(a, c)) for a, c in pairs) / 2
    Eoff = sum(cabs2(a) + cabs2(c) for a, c in pairs)
    sumabs2_all = sum(cabs2(v) for v in f) + Eoff
    # identity 1: sum |F|^2 - S2 = 2 Delta
    assert sumabs2_all - S2 == 2 * Delta
    # identity 2: S2 + Delta = sum_S |F|^2 + (1/2) sum_P |a+c|^2
    assert S2 + Delta == sum(cabs2(v) for v in f) + sum(cabs2(cadd(a, c)) for a, c in pairs) / 2
    # inequality 1 (weighted Cauchy-Schwarz, pairs weight 2): N_s (S2+Delta) >= |S1|^2
    Ns = nS + 2 * nP
    assert Ns * (S2 + Delta) >= cabs2(S1)
    # inequality 2 (pairs weight 1): (|S|+|P|)(S2 + E_off) >= |S1|^2
    assert (nS + nP) * (S2 + Eoff) >= cabs2(S1)
    say(f"  config |S|={nS}, |P|={nP}: sum|F|^2-S2=2Delta={2*Delta}; N_s(S2+Delta)-|S1|^2="
        f"{Ns*(S2+Delta)-cabs2(S1)} >=0; (|S|+|P|)(S2+E_off)-|S1|^2={(nS+nP)*(S2+Eoff)-cabs2(S1)} >=0")
say("PASS: Delta = (1/2) sum_pairs |F(rho)-F(1-conj rho)|^2 = (1/2)(sum_rho |F(rho)|^2 - S2);")
say("      N_s >= |S1|^2/(S2+Delta) and N_0^s >= 2|S1|^2/(S2+E_off) - N hold identically.")

# C2: indefiniteness is forced: any Hermitian form Q(a,c) = alpha*2Re(a conj c)
#     + beta*2Re(a^2) + beta'*2Re(c^2) that is >=0 on the on-line locus c=a for all a
#     must have beta+beta'=0 and then Q(a,-a) = -2 alpha |a|^2.
say("  Degree-2 holomorphic pairings on a mirror pair: on-line positivity forces")
say("  Q(a,c)=2alpha Re(a conj c)+2beta Re(a^2-c^2); then Q(a,-a) = -2 alpha|a|^2 < 0.  (algebraic)")

# ----------------------------------------------------------------------------
say()
say("=" * 78)
say("BLOCK D (CHECKED): the adversary.  CGG data alone give NO bound on simple on-line zeros")
say("=" * 78)
# Normalised units: S1 = c1 N L, S2 = c2 N L^2, all F-values scaled by sqrt(N) L.
# Configuration: s N simple on-line zeros with equal value f, ONE mirror pair with
# values (a,-a), the rest nonsimple (contribute 0).  Then S1 = sN f, S2 = sN|f|^2 - 2|a|^2.
c1, c2 = Fr(19, 24), Fr(57, 64)
for s in [Fr(6725043820976, 10**13), Fr(1, 2), Fr(1, 10), Fr(1, 1000)]:
    # want sN f = c1 N L  -> f = c1 L / s ;  S2 = c1^2 N L^2 / s - 2|a|^2 = c2 N L^2
    # -> 2|a|^2 / (N L^2) = c1^2/s - c2  (must be >= 0)
    a2 = (c1 * c1 / s - c2) / 2
    assert a2 >= 0
    say(f"  s = |S|/N = {float(s):.6f}: one off-line pair with |F(rho)|^2 = {float(a2):.6g} N L^2,"
        f" values (a,-a), matches S1 and S2 exactly; Delta/(N L^2) = {float(2*a2):.6g}")
say("PASS: for every s>0 a configuration with |S| = sN reproduces the CGG values of S1 and S2.")
say("      Hence inf |S|/N = 0 over configurations consistent with S1, S2 and with any count")
say("      bound on off-line zeros (the construction uses a single pair).")

# D2: how many pairs are needed if the pointwise bound |F(rho)|^2 << T^{1/2+theta+eps} is imposed
say("  With the convexity-type pointwise bound |F(rho)|^2 <= T^{1/2+theta+eps}, the energy")
say("  0.04 N L^2 ~ T L^3 needs about T^{1/2-theta-eps} off-line pairs; Selberg's density bound")
say("  N(sigma,T) << T^{1-(sigma-1/2)/4} log T excludes only zeros with beta-1/2 >= 4(1/2+theta) > 1.")

# ----------------------------------------------------------------------------
say()
say("=" * 78)
say("BLOCK E (NUMERICAL): what survives under a hypothetical off-line energy cap")
say("=" * 78)
REPO = 0.6725043820976
c1f, c2f = float(c1), float(c2)
say(f"theta -> 1/2 constants: c1 = {c1f:.6f}, c2 = {c2f:.6f}, c1^2/c2 = {c1f*c1f/c2f:.6f}")
dstar = c1f * c1f / REPO - c2f
say(f"N_s/N >= c1^2/(c2+delta) exceeds the repo bound {REPO} iff delta < {dstar:.6f}")
say(f"  i.e. iff Delta <= {dstar:.4f} N L^2 = {dstar/c2f*100:.2f}% of S2  (Delta = (1/2)(sum|F|^2 - S2))")
d23 = c1f * c1f / (2 / 3) - c2f
say(f"N_s/N >= 2/3 iff delta < {d23:.6f}")
say(f"On-line variant with pairs weighted once: N_0^s/N >= 2 c1^2/(c2+e_off) - 1 = {2*c1f*c1f/c2f-1:.6f} at e_off=0 (=11/27)")
say("  (kappa_on(theta) = 1 - 2(1+theta)^-3 would need theta >= %.4f to reach %.4f; formal extrapolation only,"
    % ((2 / (1 - REPO)) ** (1 / 3) - 1, REPO))
say("   the CGG main terms are proved only for theta < 1/2)")
say(f"  N_s bound 1-(1+theta)^-3 exceeds {REPO} iff theta > {(1/(1-REPO))**(1/3)-1:.6f} (inside theta<1/2)")


# E2: adversary with pair fraction p and energy cap e0 (units N L^2): minimise s.
def min_s(p, e0, c1=c1f, c2=c2f, grid=4001):
    """inf over pairs data of |S|/N subject to S1=c1, S2=c2 (units), |U|^2<=p(E+V),
    -E<=V<=E, E<=e0.  |S| >= (c1-u)^2/(c2-v)."""
    best = 1.0
    if p == 0:
        e0 = 0.0                     # no pairs: no off-line energy at all
    for i in range(grid):
        e = e0 * i / (grid - 1)
        for j in range(201):
            v = -e + 2 * e * j / 200
            Y = c2 - v                      # = sum_S |F|^2 / (N L^2), must be >= 0
            if Y < 0:
                continue                    # infeasible configuration
            umax = math.sqrt(max(p * (e + v), 0.0))
            if Y == 0:
                if umax >= c1:
                    best = 0.0
                continue
            u = min(c1, umax)
            s = (c1 - u) ** 2 / Y
            best = min(best, s)
    return best


say("  inf |S|/N consistent with (S1,S2) for pair fraction p and off-line energy cap e0 (units N L^2):")
say("    p \\ e0    0.00    0.01    0.02    0.04    0.08    0.16    0.32    1.00")
for p in [0.0, 0.001, 0.01, 0.05, 0.16375]:
    row = [min_s(p, e0) for e0 in [0.0, 0.01, 0.02, 0.04, 0.08, 0.16, 0.32, 1.0]]
    say("    %-8.5f" % p + "".join("  %.4f" % r for r in row))
say("  (p = 0.16375 is the largest pair fraction allowed by the repo's 0.6725 simple-on-line theorem;")
say("   row p=0 has no pairs, hence E_off=0 and the RH value 19/27 = 0.7037 for every cap.)")

# ----------------------------------------------------------------------------
say()
say("=" * 78)
say("BLOCK F (NUMERICAL): kappa(theta) table and higher-degree numerical optimisation")
say("=" * 78)
for thf in [0.1, 0.2, 0.3, 0.4, 0.45, 0.4507, 0.49, 0.499, 0.5]:
    k = 1 - (1 + thf) ** -3
    say(f"  theta={thf:.4f}: kappa={k:.6f}  N_s bound; on-line (pairs weight 1, e_off=0): {2*k-1:.6f}")
try:
    import numpy as np
    from scipy.optimize import minimize

    def neg_kappa(coef, th):
        # P(x) = x + sum_{k>=1} coef_k x^k (1-x)   satisfies P(0)=0,P(1)=1
        xs = np.linspace(0, 1, 4001)
        w = np.ones_like(xs); w[0] = w[-1] = 0.5; w /= (len(xs) - 1)
        P = xs.copy(); dP = np.ones_like(xs)
        for k, ck in enumerate(coef, start=1):
            P += ck * xs**k * (1 - xs)
            dP += ck * (k * xs**(k - 1) * (1 - xs) - xs**k)
        I = (w * P).sum(); J = (w * dP * dP).sum()
        c1 = 0.5 + th * I; c2 = 1 / 3 + th * I + th * th * I * I + J / (12 * th)
        return -c1 * c1 / c2

    for thf in [0.3, 0.49]:
        res = minimize(neg_kappa, np.zeros(5), args=(thf,), method="BFGS")
        say(f"  theta={thf}: degree-6 numerical optimum {-res.fun:.8f} vs closed form {1-(1+thf)**-3:.8f}"
            f"  (coef {np.round(res.x,4).tolist()}, quadratic has coef=[theta,0,0,0,0])")
except Exception as ex:  # pragma: no cover
    say("  (numpy/scipy unavailable: skipped)", ex)

say()
say("ALL CHECKS PASSED")

with open(__file__.replace(".py", ".out"), "w") as fh:
    fh.write("\n".join(OUT) + "\n")
