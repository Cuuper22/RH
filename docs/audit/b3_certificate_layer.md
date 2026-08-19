> **Canonical reference**: [FINDINGS.md](../../FINDINGS.md) (certificate arithmetic). See also [GUIDE.md](../../GUIDE.md) topic index.

# B-3 certificate layer: exact finite algebra, rational windows, and the frozen R-9383 endpoint

## Scope

This audit separates the finite certificate calculation from the analytic
bridges which would make it a statement about zeta zeros.  It does not call a
quartic rung unconditional.  In particular, the A1 pair-trace input, an R1a
mean-one principal block, and the R1b Rudnick--Sarnak/grid limit remain absent.

The machine-checked part has four components:

1. the sharp top-hat scalar integrals entering terminal formula (21);
2. finite trimmed fourth-moment weak duality and the two displayed rational
   quartics for R-8686 and R-9506;
3. explicit rational-polynomial saturated-window witnesses at supports
   `14999/10000` and `19999/10000`; and
4. an exact directed enclosure showing that the flat three-atom endpoint used
   for R-9383 lies strictly below the frozen decimal.

No result in this layer repairs the alias/construction failure proved in the
A2 audits.

## Independent verification before formalization

The numeric and rational claims were recomputed independently before their
Lean statements were added:

```bash
python3 -m pip install -r verify/requirements.txt
cmp -s verify/b3_certificate_audit.out \
  <(python3 verify/b3_certificate_audit.py)
cmp -s verify/b3_r9383_exact_endpoint.out \
  <(python3 verify/b3_r9383_exact_endpoint.py)
```

`b3_certificate_audit.py` uses exact rational arithmetic for the two terminal
moment vectors, quartics, global factor signs, fixed-point arithmetic, and
window-cost integrations.  Its high-precision primal calculations are
labelled calibration only and are not used as proof decisions.

`b3_r9383_exact_endpoint.py` uses only integers and
`fractions.Fraction`.  Square roots are enclosed by exact integer-square-root
inequalities; sine and cosine use rational Taylor polynomials with explicit
remainders; the fourth-moment equation is checked as a bivariate polynomial
identity; and interval automatic differentiation proves uniqueness on the
isolating interval.

## Top-hat integrals

`RH/Zeta85/Discharge/TopHatMoments.lean` defines the sharp top hat

\[
 r_p(x)=p^{-1}{\bf 1}_{[-p/2,p/2]}(x),\qquad q_p=r_p-1,
\]

as an actual indicator function and proves, by Mathlib interval integration,

\[
\begin{aligned}
 \int q_p&=0,\\
 \int q_p^2&=\frac{1-p}{p},\\
 \int q_p^3&=\frac{(1-p)^3}{p^2}-(1-p),\\
 \int q_p^4&=\frac{(1-p)^4}{p^3}+(1-p).
\end{aligned}
\]

For
\(h_p(x)=\int |x-y|r_p(y)\,dy\), it proves on the support that

\[
 h_p(x)=\frac{x^2}{p}+\frac p4,
\]

and then proves the four mixed terms

\[
 \int r_ph_p=\frac p3,\qquad
 \int q_pr_ph_p=\frac{1-p}{3},\qquad
 \int q_p^2r_ph_p=\frac{(1-p)^2}{3p},
\]

\[
 \iint q_p(x)r_p(x)q_p(y)r_p(y)|x-y|\,dx\,dy
   =\frac{(1-p)^2}{3p}.
\]

It also proves from nested interval integrals

\[
 \int r_p^2h_p^2=\frac{7p}{60}
\]

and evaluates the reduced crossing simplex as `p/30`.  The source's original
three-dimensional crossing functional is defined separately, so its affine
change of variables is not hidden in a definition.  Lean proves the
determinant-one substitution

\[
 (u,v,y)\longmapsto(x,y,z)=(y+u,y,y-v),
\]

preserves volume, evaluates the four-support intersection in the `y` fiber,
and reduces the four sign quadrants to the simplex integral.  Thus
`TopHatMoments.crossingReduction` proves the original crossing functional is
exactly `p/30`, and `formula21M4Integral_eq` assembles the original (not merely
reduced) fourth-moment formula without an input proposition.

This integral calculation still does not prove that Rudnick--Sarnak's theorem
produces terminal formula (18).  That R1b bridge is the separate blocker
listed in `docs/audit/rs_reduction.md`.

## Finite trimmed-moment duality

`RH/Zeta85/Discharge/TrimmedMoment.lean` proves weak duality over a finite
type.  The full weights and the removed submeasure are explicit functions;
nonnegativity, moment equalities through degree four, and the removed-mass
bound are Prop-valued structure fields.  If a quartic `P` satisfies globally

\[
 P(y)\leq0\ (y\leq0),\qquad
 P(y)\leq y^2\ (y\geq0),\qquad
 P(y)\leq L\ (y\geq0),
\]

then the file proves the exact finite trimmed-tail lower bound and its affine
fixed-point consequence.  It makes no primal-equality or sharpness claim.

For both terminal certificates, Lean checks the displayed contact identities
and factors each of `P`, `y^2-P`, and `L-P` into a double-root factor and a
quadratic.  Exact coefficient/discriminant signs prove the inequalities on
the whole real line.  The resulting conditional arithmetic is:

| source certificate | directed cost | exact lower output | frozen target | result |
|---|---:|---:|---:|---|
| R-8686 | `1.13434643` | `0.868552508285414235...` | `0.86855250` | clears by `8.2854e-9` |
| R-9506 | `1.06772567` | `0.950638321875659418...` | `0.95063832187565` | clears by `9.4187e-15` |

These are finite implications only.  The bridge structures in the theorem
statements are not asserted for a zeta-zero compression.

The rational contact quartics are deliberately near-optimal, not exact
complementary-slackness pairs.  The independent primal calibration has a
strict positive primal-minus-dual gap in both cases.  Weak duality is the
correct proof mechanism; no equality is claimed for the displayed rational
polynomials.

## Explicit rational window witnesses

`RH/Zeta85/Discharge/QuarticWindowWitnesses.lean` gives the actual test
functions.  They are even rational polynomials of degrees 18 and 10; every
coefficient is written in the Lean source and reconstructed independently by
`verify/b3_certificate_audit.py`.

| support | degree | exact cost (decimal display only) | proved bound |
|---:|---:|---:|---:|
| `14999/10000` | 18 | `1.134346428834212809924583...` | `< 1.13434643` |
| `19999/10000` | 10 | `1.067725667876031819106202...` | `< 1.06772567` |

Positivity is not sampled: the polynomials are converted exactly to Bernstein
form on `[-1/2,1/2]`, and every Bernstein coefficient has a positive rational
lower bound.  Autocorrelations, both one-variable integrals, the saturated
`J`, and the normalized costs are exact Mathlib polynomial integrals.  The
files therefore prove `SaturatedWindowCost` for each exact rational cost and
then the two directed decimal inequalities.

The allocation check is also pointwise.  Exact derivative-quotient Bernstein
bounds prove that each even profile is decreasing on its relevant normalized
central interval; the exact edge value is strictly above `1/p`.  Hence the
mean-one top hat lies strictly below the full symbol throughout its active
interval.  This verifies the scalar cap only.  A2.1 and A2.2 show why that cap
does not furnish the required principal-block modulation system.

## Frozen R-9383 endpoint

For the flat law with moments `(1,0,1/3,0,4/15)`, the exact fourth-moment
condition on the relevant three-atom branch reduces to

\[
 135F(q,t)=7-12q+9qt^2-45qt^4=0,
 \qquad
 t^2=\frac{9+\sqrt{1260/q-2079}}{90}.
\]

The independent exact verifier encloses the Euler support-two cost by

\[
1.0677173760647041522687642216851958360927317655602367316616310902521452
\leq D_2
\]

and by the same number with the last digit increased by one.  It isolates the
unique fixed root on this branch as

\[
 0.0616866729490511152\leq q\leq0.0616866729490511153.
\]

Therefore

\[
 0.9383133270509488847
 \leq 1-q
 \leq0.9383133270509488848
 <0.938313327050949.
\]

The frozen source decimal is larger by at least
`0.0000000000000001152`.  A second exact rational five-atom law gives an
independent strict comparison.  The rational endgame is replayed in
`RH/Zeta85/Discharge/R9383ExactEndpoint.lean`.

The Lean file proves the rational law, moment identities, trim comparison,
tail inequality, and the final implication from the certified lower endpoint
for `q`.  It does not assert the Taylor enclosure or root isolation as Lean
theorems; those exact-integer/Fraction checks remain in the committed
independent verifier.  Consequently this is a rigorous method audit, not an
unconditional kernel theorem about the analytic endpoint.

This is a finish-or-kill result for the exact flat three-atom endpoint
certificate class used in files 17 and 19: that class cannot prove frozen
R-9383 because its endpoint is strictly smaller.  A different, genuinely
stronger construction could still prove the frozen rung, so the constant is
not edited or weakened.

## Status after B-3

- The finite R-8686 and R-9506 dual arithmetic is proved.
- Their scalar window costs and pointwise caps are proved by explicit
  rational constructions.
- The original three-dimensional crossing contraction and all four top-hat
  moments in formula (21) are proved from Mathlib integrals.
- The flat certificate underlying the frozen R-9383 decimal is exactly
  obstructed by upward rounding.
- No quartic rung is unconditional: A1, R1a, and R1b remain exact named
  blockers.
