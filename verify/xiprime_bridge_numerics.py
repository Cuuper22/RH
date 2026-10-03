"""Numerical diagnostics for the xi' -> xi bridge (2026-10-03).  NUMERICAL only.

f(t) = xi(1/2 + i t) is real; f'/f(t) = -Im (xi'/xi)(1/2+it), computed from
  xi'/xi(s) = 1/s + 1/(s-1) - (log pi)/2 + psi(s/2)/2 + zeta'/zeta(s).
Real zeros of f' = critical-line zeros of xi'.  In each gap between consecutive
zeros of f the number of sign changes of f'/f is odd, 2m+1, with m wrong extrema.

Part 1: count critical points per gap on two blocks of actual zeros (expect 1:
        all computed zeros are simple and on the line, so f is locally in the
        Laguerre-Polya class and W = 0 identically).  Checks the Morse identity
        Rd = G - W + delta on each block.
Part 2: susceptibility.  B_n = f'/f at the midpoint m_n of the gap
        (gamma_n, gamma_{n+1}) (the two bounding zeros cancel there).  If the
        two real zeros were replaced by the conjugate pair m_n +- i*delta, the
        constant-background approximation predicts a wrong extremum iff
        delta < 1/|B_n|.  We report 1/|B_n| in units of the local mean spacing
        2 pi / log(t/2 pi), and for a sample of gaps the exact threshold
        delta* found by bisection on the modified log-derivative
          f'/f - 1/(t-g_n) - 1/(t-g_{n+1}) + 2(t-m)/((t-m)^2 + delta^2).
"""
import sys, time
import mpmath as mp

mp.mp.dps = 15
LOGPI = mp.log(mp.pi)


def dlog(t):
    s = mp.mpc(0.5, t)
    E = 1 / s + 1 / (s - 1) - LOGPI / 2 + mp.digamma(s / 2) / 2 + mp.zeta(s, derivative=1) / mp.zeta(s)
    return float(-E.imag)


def spacing(t):
    return float(2 * mp.pi / mp.log(t / (2 * mp.pi)))


def block(n0, n1, pts=32):
    zeros = [float(mp.zetazero(n).imag) for n in range(n0, n1 + 1)]
    counts, mids, Bs, mono_fail = [], [], [], 0
    for g0, g1 in zip(zeros, zeros[1:]):
        h = (g1 - g0) / (pts + 1)
        grid = [g0 + h * (k + 1) for k in range(pts)]
        vals = [dlog(t) for t in grid]
        sc = sum(1 for a, b in zip(vals, vals[1:]) if a * b < 0)
        if any(b >= a for a, b in zip(vals, vals[1:])):
            mono_fail += 1
        counts.append(sc)
        m = (g0 + g1) / 2
        mids.append(m)
        Bs.append(dlog(m))
    return zeros, counts, Bs, mids, mono_fail


def exact_delta_star(zeros, j, pts=240):
    """largest delta for which collapsing gap j into a pair at midpoint gives 3 critical points."""
    gm1, g0, g1, g2 = zeros[j - 1], zeros[j], zeros[j + 1], zeros[j + 2]
    m = (g0 + g1) / 2
    h = (g2 - gm1) / (pts + 1)
    grid = [gm1 + h * (k + 1) for k in range(pts)]
    base = [dlog(t) - 1 / (t - g0) - 1 / (t - g1) for t in grid]

    def ncrit(delta):
        vals = [b + 2 * (t - m) / ((t - m) ** 2 + delta ** 2) for b, t in zip(base, grid)]
        return sum(1 for a, b in zip(vals, vals[1:]) if a * b < 0)

    lo, hi = 0.0, 2 * (g1 - g0)
    if ncrit(hi) != 1:
        hi *= 4
    if ncrit(1e-6 * (g1 - g0)) < 3:
        return 0.0, ncrit(1e-6 * (g1 - g0))
    for _ in range(40):
        mid = (lo + hi) / 2
        if ncrit(mid) >= 3:
            lo = mid
        else:
            hi = mid
    return lo, 3


def quantiles(xs):
    xs = sorted(xs)
    q = lambda f: xs[min(len(xs) - 1, int(f * len(xs)))]
    return min(xs), q(0.25), q(0.5), q(0.75), max(xs)


def main():
    t0 = time.time()
    out = []
    P = lambda *a: (print(*a), out.append(" ".join(str(x) for x in a)))
    blocks = [(1, 500), (10000, 10060)]
    all_ratio = []
    saved = None
    for n0, n1 in blocks:
        zeros, counts, Bs, mids, mono_fail = block(n0, n1)
        gaps = len(counts)
        W = sum((c - 1) // 2 for c in counts)
        G = sum((c + 1) // 2 for c in counts)
        even = sum(1 for c in counts if c % 2 == 0)
        # interior real zeros of f strictly between zeros[0] and zeros[-1]
        Rd = len(zeros) - 2
        # delta = [sigma(b) - sigma(a)]/2 with sigma = sgn(f f') just inside the end gaps:
        # just right of zeros[0] f'/f has the sign of f f', = +1 ; just left of zeros[-1] it is -1
        a_sig, b_sig = +1, -1
        delta = (b_sig - a_sig) // 2
        P(f"Block zeros #{n0}..#{n1}: heights {zeros[0]:.3f}..{zeros[-1]:.3f}, {gaps} gaps")
        P(f"  critical points per gap: histogram {dict((c, counts.count(c)) for c in sorted(set(counts)))}")
        P(f"  gaps with even sign-change count (grid artefact if any): {even}")
        P(f"  gaps where sampled f'/f is not strictly decreasing: {mono_fail}")
        P(f"  G = {G}, W = {W}, Rd (interior distinct real zeros) = {Rd}, delta = {delta}")
        P(f"  Morse identity Rd = G - W + delta : {Rd} = {G - W + delta}  -> {'OK' if Rd == G - W + delta else 'FAIL'}")
        ratios = [1 / abs(B) / spacing(m) for B, m in zip(Bs, mids)]
        all_ratio += ratios
        mn, q1, med, q3, mx = quantiles(ratios)
        P(f"  susceptibility 1/|B_n| in mean spacings: min {mn:.4f}  q1 {q1:.4f}  median {med:.4f}  q3 {q3:.4f}  max {mx:.4f}")
        P(f"  fraction of gaps with 1/|B_n| > 0.5 spacing: {sum(1 for r in ratios if r > 0.5) / gaps:.3f};"
          f" > 1 spacing: {sum(1 for r in ratios if r > 1) / gaps:.3f}")
        if saved is None:
            saved = (zeros, Bs, mids)
    zeros, Bs, mids = saved
    P("Exact delta* (bisection) vs heuristic 1/|B_n| for gaps j = 10, 25, ..., 460 of block 1 (units: mean spacing):")
    P("   j   gap/spacing   delta*/spacing   heur/spacing   ratio exact/heur")
    rat = []
    for j in range(10, 470, 15):
        ds, nc = exact_delta_star(zeros, j)
        sp_ = spacing(mids[j])
        heur = 1 / abs(Bs[j])
        rat.append(ds / heur if heur > 0 else float('nan'))
        P(f"  {j:4d}   {(zeros[j+1]-zeros[j])/sp_:9.4f}   {ds/sp_:12.4f}   {heur/sp_:12.4f}   {ds/heur:8.4f}")
    mn, q1, med, q3, mx = quantiles(rat)
    P(f"  exact/heuristic ratio: min {mn:.3f} median {med:.3f} max {mx:.3f}")
    P(f"elapsed {time.time() - t0:.1f}s")
    return out


if __name__ == "__main__":
    main()
