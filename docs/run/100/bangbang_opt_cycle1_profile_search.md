> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Zeta100 cycle 1: capped-symbol bang--bang optimization

## Best low-complexity profile found

Fix the inherited strict parameters

\[
 \sigma=1.9999,\qquad \mu=0.4999,
\]

and write

\[
 W(t)=V_\sigma(\mu t),\qquad -\tfrac12\leq t\leq\tfrac12.
\]

The strongest low-complexity profile found was not the pure cap/zero
profile.  It is the two-phase even profile

\[
 r_g(t)=
 \begin{cases}
   a_g,& |t|<g/2,\\
   W(t),& g/2\leq |t|\leq 1/2,
 \end{cases}
 \qquad
 a_g={1-2\int_{g/2}^{1/2}W(t)\,dt\over g}.
 \tag{1}
\]

Thus the outer phase saturates the admissible cap, while the central phase
is a free constant chosen to make \(\int r_g=1\).  The convenient rational
choice

\[
 \boxed{g={103\over400}=0.2575},\qquad |t|< {103\over800},
 \tag{2}
\]

gives

\[
 a_g=0.3395478345\ldots .
 \tag{3}
\]

It has a very large feasibility margin on the central phase:
\(a_g<0.34\), whereas \(W(t)>1.25\) there.  The outer phase is cap
saturation by definition.  A directed implementation can replace \(W\) by
a rational lower step envelope and adjust the central constant; the
geometry and all moment integrands are then piecewise polynomial.

Using formula (18) of `certificate95_cycle2.md`, an 800-cell midpoint
evaluation whose discontinuity is exactly aligned with (2) gives

\[
 \boxed{
 (M_2,M_3,M_4)=
 (0.24211130\ldots,-0.02052160\ldots,0.10588550\ldots).}
 \tag{4}
\]

The aligned 400/800-grid difference at the nearby rational width
\(g=0.255\) was below \(5\cdot10^{-7}\) in every displayed moment.  Thus
six decimal places in (4) are stable; a final certificate should use
directed quadrature or a rational step envelope.

## Fixed rational trimmed-moment dual

Use the rational contacts

\[
 A=-{3049\over5000}=-0.6098,\qquad
 C={1603\over5000}=0.3206,\qquad
 T={2657\over2500}=1.0628.
 \tag{5}
\]

Let \(P\) and \(L\) be defined by

\[
 P(A)=P'(A)=0,\quad P(C)=C^2,\quad P'(C)=2C,
 \quad P(T)=L,\quad P'(T)=0.
 \tag{6}
\]

Their decimal display is

\[
\begin{aligned}
P(y)={}&-0.03259888+0.19135742y+0.70697059y^2\\
       &+0.19985106y^3-0.49382691y^4,\\
L={}&0.5791885186915733\ldots .
\end{aligned}
\tag{7}
\]

The three global-dual checks reduce to

\[
\begin{aligned}
P(y)&=(y-A)^2(-0.08766532+0.80212235y-0.49382691y^2),\\
y^2-P(y)&=(y-C)^2(0.31715796+0.11679075y+0.49382691y^2),\\
L-P(y)&=(y-T)^2(0.54162342+0.84982741y+0.49382691y^2).
\end{aligned}
\tag{8}
\]

The first residual quadratic has both roots positive,
\(0.1178409\ldots,1.5064577\ldots\), hence is negative on \(y\leq0\).
The last two have discriminants

\[
 -0.61284445\ldots,\qquad -0.34766623\ldots,
\]

so they are positive on the real line.  Therefore this rational-contact
dual is globally feasible, not merely grid-feasible.

With (4),

\[
 P_0+P_2M_2+P_3M_3+P_4M_4
 =0.0821763179\ldots .
 \tag{9}
\]

At the inherited

\[
 D=1.0677256658589\ldots,
\]

the affine fixed point is

\[
 \boxed{\varepsilon=0.03021791077\ldots},\qquad
 \alpha={D-1-\varepsilon\over2\mu}=0.03751525814\ldots,
 \tag{10}
\]

and hence

\[
 \boxed{{s\over N}=2-D+\varepsilon
       =0.9624922449\ldots .}
 \tag{11}
\]

The continuously optimized contacts were

\[
 (-0.60984396\ldots,\ 0.32063705\ldots,\ 1.06282492\ldots),
\]

and improve (10) by only \(6.5\cdot10^{-10}\).  Thus (5) loses no
meaningful margin.

## Width scan and response-field evidence

The aligned 800-cell scan was

\[
\begin{array}{c|c|c}
g&a_g&\varepsilon\\ \hline
0.2525&0.32150362&0.0302086392\\
0.2550&0.33061455&0.0302160334\\
0.2575&0.33954783&0.0302179126\\
0.2600&0.34830859&0.0302143872\\
0.2625&0.35690174&0.0302055642
\end{array}
\tag{12}
\]

Quadratic interpolation places the continuous optimum near
\(g=0.2571\).  Thus the rational width (2) is effectively optimal within
this family.

For the fixed dual (5), a symmetric 81-cell SLSQP allowing every central
cell to move independently returned a central range only

\[
 0.3455991\leq r_i\leq0.3457991
\]

(the grid-snapped width changes the normalized constant).  Its mass-normalized
response field was constant on the free central phase to \(5.4\cdot10^{-5}\),
while every cap-active outer cell had strictly larger response.  An
unrestricted run produced maximum left/right asymmetry \(2.6\cdot10^{-5}\).
These are the expected KKT signs: constant response on the free phase and
the upper-obstacle inequality on the saturated phase.

A separate three-level scan split the central phase into a center and an
annulus.  Its best values were \(0.376724\) and \(0.376110\) on the coarse
grid, collapsing back to one constant; the score was microscopically below
the corresponding two-level value.  Central-cap, one-sided, two-gap,
oscillatory, and random active-set starts all finished below (11).  The best
pure cap/zero profile was about \(0.96012\), also below (11).

## Handoff

The profile (1)--(3) is the recommended certificate target.  It improves
the previous cap/zero result by about \(0.00238\) in simple proportion and
the earlier central top-hat certificate by about \(0.01185\).  Its useful
feature is a two-phase obstacle solution: outer cap saturation plus a
central constant, rather than a zero central gap.