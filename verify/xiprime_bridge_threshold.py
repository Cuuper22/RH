"""Exact threshold function for the xi' -> xi bridge (2026-10-03).

Everything here is exact rational arithmetic (fractions / sympy).  It checks
scalar consequences of statements proved elsewhere; it does not prove the
analytic transfer.

Inputs (all from the repository):
  * kap9Flat, kap9Quartic, eps9     Zeta23/XiPrime/Certificate/AtOne.lean, D1.lean
    (kappaXi(1,v) <= kap9 + eps9, so 2 - kappaXi(1,v) >= 2 - kap9 - eps9 =: c'_v;
     the Lean headlines use the safe decimals 0.85838 / 0.86864).
  * the optimized bandwidth-one profile p(x) and the increment 1/271803
    verify/optimized_profile_gain.py, docs/research/sharpened_cubic_gain_20260905.md
    (proposed frontier F = 2 - D(u) + 1/271803 for simple critical-line zeros of xi).
  * vQuartic(s) = 1 - (7/100)(2s)^2 - (51/200)(2s)^4     Zeta23/XiPrime/Defs.lean.

Transfer identity (docs/research/xiprime_bridge_20261003.md, Prop. 1, PROVED):
  N0s_xi = s - 2 Ws - 2 C2 - Wd + Gd - M>=3 + delta,  |delta| <= 1,
so with the obstruction  Omega := Ws + C2 + (Wd + M>=3)/2  one has
  N0s_xi >= s - 2 Omega - 1 >= c'_v N' - 2 Omega - 1.
Threshold function  Theta_v(omega) = c'_v - 2 omega  (omega = limsup Omega/N).
"""

from fractions import Fraction as F
from math import factorial, prod

import sympy as sp

# ---------------------------------------------------------------- constants
eps9 = F(1024, 2990212875)
kap9_flat = F(100905635384, 88388425125)
kap9_quartic = F(277244140547469154168336, 245053976636191319722125)
c_flat = 2 - kap9_flat - eps9          # certified lower bound for 2 - kappaXi(1,vFlat)
c_quartic = 2 - kap9_quartic - eps9    # certified lower bound for 2 - kappaXi(1,vQuartic)
c_flat_lean = F(85838, 100000)         # compiled headline constants
c_quartic_lean = F(86864, 100000)
assert c_flat > F(85838371, 10**8) > c_flat_lean
assert c_quartic > F(86864017, 10**8) > c_quartic_lean

# ------------------------------------------------- frontier F (exact rational)
x, v, w = sp.symbols("x v w")
coeff = [1091974251780, -1092598710370, 183563572147, -13799851355,
         11008450474, -46499927506, 75463768564]
p = sum(sp.Rational(c, 10**12) * x ** (2 * j) for j, c in enumerate(coeff))
mass = sp.integrate(p, (x, -sp.Rational(1, 2), sp.Rational(1, 2)))
u = sp.cancel(p / mass)


def simplex_integral(poly, variables):
    terms = sp.Poly(sp.expand(poly), *variables).terms()
    return sum(c * sp.Rational(prod(factorial(k) for k in powers),
                               factorial(sum(powers) + len(variables)))
               for powers, c in terms)


lo = u.subs({x: x - sp.Rational(1, 2)})
up = u.subs({x: x + v - sp.Rational(1, 2)})
i2 = sp.integrate(u**2, (x, -sp.Rational(1, 2), sp.Rational(1, 2)))
D_xi = F(sp.cancel(i2 + 2 * simplex_integral(v * lo * up, (x, v))))
gain = F(1, 271803)
frontier = 2 - D_xi + gain
assert frontier > F(336252191, 500000000)          # 0.672504382 (as in the verifier)
assert frontier < F(6725043821, 10**10)            # 0.6725043821 upper enclosure
D_xi_flat = F(4, 3)                                # flat bandwidth-one zeta cost 1+2*int(1-u)u

# ------------------------------------------------- threshold function
def theta(c, omega):
    return c - 2 * omega


results = {}
for name, c in (("flat", c_flat), ("quartic", c_quartic),
                ("flat_lean", c_flat_lean), ("quartic_lean", c_quartic_lean)):
    wstar = (c - frontier) / 2          # Omega/N < wstar  beats the frontier
    omega_triv = (1 - frontier) / 2     # PROVED unconditional bound  Omega <= (N' - N0s + 1)/2
    results[name] = (c, wstar, omega_triv)
    assert theta(c, wstar) == frontier
    assert theta(c, omega_triv) == c - 1 + frontier < frontier

# the 85% threshold of critical_values_20260905.md, for comparison
w85_quartic = (c_quartic - F(85, 100)) / 2
assert w85_quartic > F(932, 100000)

# ------------------------------------------------- cross-correlation constants
# prime-layer cross density rho_x(r) = r(2r-1) (xi coefficient Lambda(p), xi'
# coefficient Lambda(p)(2r-1), r = log p / ell); cost = (int v^2 + 2 int rho_x vConv)/(int v)^2.
r, s_ = sp.symbols("r s")
vq = 1 - sp.Rational(7, 100) * (2 * s_) ** 2 - sp.Rational(51, 200) * (2 * s_) ** 4
convQ = sp.integrate(vq * vq.subs(s_, s_ + r), (s_, -sp.Rational(1, 2), sp.Rational(1, 2) - r))
convQ = sp.expand(convQ)
int_vq = sp.integrate(vq, (s_, -sp.Rational(1, 2), sp.Rational(1, 2)))
int_vq2 = sp.integrate(vq**2, (s_, -sp.Rational(1, 2), sp.Rational(1, 2)))
# consistency with Zeta23.XiPrime.two_integral_convQ:  2 int_0^1 convQ = (2777/3000)^2
assert sp.Rational(2) * sp.integrate(convQ, (r, 0, 1)) == sp.Rational(2777, 3000) ** 2
assert int_vq == sp.Rational(2777, 3000)
rho_x = r * (2 * r - 1)
cross_flat = 1 + 2 * sp.integrate(rho_x * (1 - r), (r, 0, 1))
cross_quartic = (int_vq2 + 2 * sp.integrate(rho_x * convQ, (r, 0, 1))) / int_vq**2
assert cross_flat == 1
cross_flat = F(1)
cross_quartic = F(cross_quartic)

# union Gram of xi and xi' zeros at bandwidth one: per-point cost
union_flat = (D_xi_flat + (2 - c_flat) + 2 * cross_flat) / 2
union_quartic = (D_xi + (2 - c_quartic) + 2 * cross_quartic) / 2
assert union_flat > 2 and union_quartic > 2      # rank-trace certificate vacuous

# ------------------------------------------------- LP feasible point (CHECKED)
# normalized unknowns: rs (simple real xi zeros), c2, p (nonreal xi pairs),
# s (simple real xi' zeros), bp (nonreal/nonsimple xi' blocks), ws (wrong extrema)
for Dz, Dp in ((D_xi_flat, 2 - c_flat), (D_xi, 2 - c_quartic)):
    pz = (Dz - 1) / 2
    rs, c2, s, bp = 2 - Dz, F(0), F(1), F(0)
    ws = pz
    assert rs + 2 * c2 + 2 * pz == 1                      # xi count
    assert 3 * rs + 4 * (c2 + pz) >= 4 - Dz               # xi rank-trace (equality)
    assert s + 2 * bp == 1                                # xi' count
    assert 3 * s + 4 * bp >= 4 - Dp                       # xi' rank-trace
    assert rs == s - 2 * ws - 2 * c2                      # Morse identity, simple case
    assert ws <= pz                                       # Rolle bound W <= p
    # with the hypothesis ws + c2 <= omega one gets rs >= Dp-free bound
    assert rs == 2 - Dz                                   # LP optimum = xi certificate alone

# ------------------------------------------------- triple-zero remark
dist_q = (3 - kap9_quartic - eps9) / 2                 # certified distinct fraction for xi'
m3_from_xiprime = 1 - dist_q                            # sum_{m>=3}(m-2) over xi zeros <= this

# ---------------------------------------------------------------- report
def show(q, nd=13):
    return f"{q} = {float(q):.{nd}f}"


print("xi' certified constants c'_v = 2 - kap9 - eps9 (lower bounds for 2 - kappaXi(1,v))")
print("  flat    :", show(c_flat))
print("  quartic :", show(c_quartic))
print("Frontier F = 2 - D(u) + 1/271803 (simple critical-line xi zeros, proposed)")
print("  D(u)    :", show(D_xi))
print("  F       :", show(frontier))
print()
print("Threshold function  Theta_v(omega) = c'_v - 2*omega ;  Omega = Ws + C2 + (Wd + M>=3)/2")
for name in ("flat", "quartic", "flat_lean", "quartic_lean"):
    c, wstar, omega_triv = results[name]
    print(f"  [{name}] c' = {float(c):.10f}")
    print(f"      W*  = (c' - F)/2        = {wstar}")
    print(f"          = {float(wstar):.13f}")
    print(f"      PROVED unconditional bound omega_triv = (1 - F)/2 = {float(omega_triv):.13f}")
    print(f"      Theta(omega_triv) = c' - 1 + F = {float(theta(c, omega_triv)):.10f}  (< F: loss 1 - c' = {float(1 - c):.6f})")
    print(f"      W*/omega_triv = {float(wstar / omega_triv):.6f}   (need this fraction of the trivial bound)")
print()
print("85% threshold of critical_values_20260905.md (quartic):", show(w85_quartic))
print("ratio W*(quartic, frontier) / W*(85%) =", float(results['quartic'][1] / w85_quartic))
print()
print("Cross xi x xi' bandwidth-one prime-layer cost (main-term density r(2r-1)):")
print("  flat    :", cross_flat)
print("  quartic :", show(cross_quartic))
print("Union Gram per-point cost (xi and xi' zeros together):")
print("  flat    :", show(union_flat), " > 2  => rank-trace certificate vacuous")
print("  quartic :", show(union_quartic), " > 2  => rank-trace certificate vacuous")
print()
print("LP feasible point (all doublets nonreal, all xi' zeros simple real, Ws = p):")
print("  rs = 2 - D_xi, ws = p = (D_xi - 1)/2, s = 1, c2 = 0  satisfies every constraint;")
print("  flat: rs =", show(2 - D_xi_flat), " ws =", show((D_xi_flat - 1) / 2))
print("  prof: rs =", show(2 - D_xi), " ws =", show((D_xi - 1) / 2))
print()
print("xi' distinct theorem => sum_{xi zeros, m>=3} (m-2) <= (1 - dist_q) N' with 1 - dist_q =",
      show(m3_from_xiprime))
print("All exact checks passed.")
