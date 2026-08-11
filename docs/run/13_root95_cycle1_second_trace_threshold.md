# Root 95% cycle 1: the second-trace distance to 95%

## Terminal outcome

The precise class consisting of one positive rank-one Weil compression,
the first trace, the Frobenius trace, and the accepted rank--trace simple-zero
inequality cannot reach 95% with the currently proved support
\(\sigma<3/2\).

For a nonnegative mass-one profile \(u\) on
\([-\sigma/2,\sigma/2]\), the optimized cost is

\[
D_\sigma^*=\inf_u\left\{
\int u(x)^2\,dx+
\iint \min(|x-y|,1)u(x)u(y)\,dx\,dy
\right\}.
\]

The zero-side certificate is

\[
\frac{N_0^s}{N}\ge 2-D_\sigma^*-o(1).
\]

At the proved endpoint,

\[
D_{3/2}^*=1.134325745543364\ldots,
\qquad
2-D_{3/2}^*=0.865674254456636\ldots .
\]

The variational optimizer already ranges over every admissible window in this
class.  Thus changing the fixed window, mixing windows into one direct-sum
rank-one atom, or taking a nonnegative convex combination of the same
Frobenius observables cannot reach 95% at support at most \(3/2\).

## First calculation outside the killed support range

Writing

\[
(I+K_\sigma)u=\text{constant},
\qquad
(K_\sigma u)(x)=
\int_{-\sigma/2}^{\sigma/2}\min(|x-y|,1)u(y)\,dy,
\]

reduces the optimal cost to the reciprocal mass of
\((I+K_\sigma)^{-1}1\).  A symmetric Nystr\"om solve gives the pure
second-trace 95% threshold

\[
\boxed{\sigma_{95}^{(2)}\approx2.26078781,}
\]

where \(D_\sigma^*=1.05\).  Representative values are

\[
\begin{array}{c|c|c}
\sigma&D_\sigma^*&2-D_\sigma^*\\ \hline
2.25&1.05060154&0.94939846\\
2.26079&1.05000000&0.95000000\\
2.30&1.04789276&0.95210724
\end{array}
\]

The computed optimizer remains strictly positive throughout this range, so
the positivity constraint is inactive in the numerical scouting problem.

## Consequence for the 95% fork

The arithmetic branch must either evaluate the signed prime-pair trace out to
roughly support \(2.261\), or a mixed/higher-trace certificate must reduce that
support requirement substantially.  The old cycle-5 parameterization cannot
be continued mechanically: it uses
\(N_1=T^{1/2-\eta}\), whereas \(\sigma=1+\eta\approx2.261\) would require
\(\eta>1/2\) and make that factor shorter than one.

The next constructive operations are therefore:

1. re-factor the signed-shift terminal form for \(H>\sqrt T\), rather than
   extending the invalid old split; and
2. solve a joint moment certificate using the proved support-\(<3/2\)
   second trace plus unconditional lower-support cubic/quartic information.

This cycle ends with a rigorous impossibility for the present
support-\(<3/2\), two-trace method class and the first quantified attack
outside it.
