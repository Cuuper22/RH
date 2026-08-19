> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Arithmetic 100, cycle 8: an independent exact charged quadratic

## Terminal outcome

Take as accepted the simultaneous strict inputs

\[
 D<1.06771746,
 \qquad
 \mu={333333\over500000}=0.666666,
 \qquad
 M_2>{18717\over50000}=0.37434,
 \tag{1}
\]

and the charged stability inequality

\[
 T_b(C)+H_b(C)\leq\varepsilon N+o(N),
 \qquad
 {b\over N}\leq{D-1-\varepsilon\over2}+o(1).
 \tag{2}
\]

Here, for the decreasing eigenvalues of the positive compression \(C\),

\[
 T_b(C)=\sum_{i>b}(\lambda_i-1)_+^2,
 \qquad
 H_b(C)=\sum_{i\leq b}(\lambda_i-2)_+^2,
 \tag{3}
\]

and

\[
 {s\over N}=2-D+\varepsilon.
 \tag{4}
\]

The exact quadratic below gives the fixed-point lower bound

\[
 \varepsilon>{9939998859\over143750000000}
 =0.0691478181495652\ldots,
 \tag{5}
\]

whereas \(s/N\leq1\) forces

\[
 \varepsilon\leq D-1<0.06771746.
 \tag{6}
\]

Thus the accepted inputs exclude every subsequential simple-line density
strictly below one.  In the standard asymptotic formulation,

\[
 \boxed{\displaystyle
 \liminf_{T\to\infty}
 {N_{0,\mathrm{simple}}(T,2T)\over N(T,2T)}=1.}
 \tag{7}
\]

This is a density-one statement, not the assertion that every individual
nontrivial zero is simple and on the critical line.

## 1. Exact rational quadratic

Choose the rational contact

\[
 c={3\over8}
\]

and set

\[
 \boxed{\displaystyle
 P(y)=y^2-{64\over121}\left(y-{3\over8}\right)^2
 ={57y^2+48y-9\over121}.}
 \tag{8}
\]

This quadratic was obtained by imposing a root at \(-1\) and a double
contact with \(y^2\) at \(c\).  Both required untrimmed signs are immediate
from the exact factors

\[
 P(y)={3(y+1)(19y-3)\over121}\leq0
 \qquad(-1\leq y\leq0),
 \tag{9}
\]

and

\[
 y^2-P(y)={(8y-3)^2\over121}\geq0
 \qquad(y\geq0).
 \tag{10}
\]

No sampled or floating-point sign check is being used.

## 2. Exact charged top-direction cost

For a top-\(b\) direction the retained charge is
\((y-1)_+^2\).  Its exact removal cost is therefore

\[
 L^\sharp=\sup_{y\geq0}
 \{P(y)-(y-1)_+^2\}.
 \tag{11}
\]

On \(0\leq y\leq1\),

\[
 P'(y)={114y+48\over121}>0,
 \qquad
 P(y)\leq P(1)={96\over121}.
 \tag{12}
\]

For \(y\geq1\), exact completion of the square gives

\[
 P(y)-(y-1)^2
 ={105\over64}
 -{64\over121}\left(y-{145\over64}\right)^2.
 \tag{13}
\]

Since \(96/121<105/64\), equations (12)--(13) prove the exact global value

\[
 \boxed{L^\sharp={105\over64}=1.640625<2.}
 \tag{14}
\]

For negative centered eigenvalues, (9) already gives
\(P(y)\leq0\leq (y-1)_+^2+L^\sharp\).  Hence (9), (10), and (14), applied
eigenvalue by eigenvalue, yield

\[
 \operatorname{tr}P(C-I)
 \leq T_b(C)+H_b(C)+{105\over64}b.
 \tag{15}
\]

## 3. Directed moment score

Put \(Y=C-I\).  The block is mean one, so its centered first moment is zero.
Since its dimension is \(\mu N+o(N)\), (8) gives

\[
 {1\over N}\operatorname{tr}P(Y)
 =\mu A_P+o(1),
 \qquad
 A_P=-{9\over121}+{57\over121}M_2.
 \tag{16}
\]

The coefficient of \(M_2\) is positive.  The one-sided input in (1) therefore
gives, entirely over the rationals,

\[
 \begin{aligned}
 A_P
 &>-{9\over121}
   +{57\over121}{18717\over50000}\\
 &={56079\over550000}
 =0.1019618181818\ldots,
 \end{aligned}
 \tag{17}
\]

and consequently

\[
 \boxed{\displaystyle
 \mu A_P>
 {333333\over500000}{56079\over550000}
 ={1699361937\over25000000000}
 =0.06797447748.}
 \tag{18}
\]

Even the deliberately rounded comparison already has the strict margin

\[
 {1699361937\over25000000000}
 -{3385873\over50000000}
 ={6425437\over25000000000}
 =0.00025701748>0.
 \tag{19}
\]

## 4. Fixed-point closure

Combine (2), (15), and (18), and put

\[
 \delta_0={3385873\over50000000}=0.06771746.
\]

Because \(D-1<\delta_0\), the directed inequality is

\[
 \begin{aligned}
 \varepsilon
 &> {1699361937\over25000000000}
 -{105\over128}(\delta_0-\varepsilon)-o(1).
 \end{aligned}
 \tag{20}
\]

As \(1-105/128=23/128>0\), solving (20) gives

\[
 \begin{aligned}
 \varepsilon
 &>{128\over23}
 \left(
 {1699361937\over25000000000}
 -{105\over128}{3385873\over50000000}
 \right)\\
 &={9939998859\over143750000000}
 =0.0691478181495652\ldots .
 \end{aligned}
 \tag{21}
\]

The excess over the ceiling-compatible value \(\delta_0\) is itself an
exact positive rational:

\[
 {9939998859\over143750000000}
 -{3385873\over50000000}
 ={6425437\over4492187500}
 =0.0014303581495652\ldots>0.
 \tag{22}
\]

Equivalently, the formal affine lower expression is

\[
 1-\delta_0
 +{9939998859\over143750000000}
 ={4498612937\over4492187500}
 =1.0014303581495652\ldots .
 \tag{23}
\]

The quantity above one in (23) is the strict contradiction that forces the
density-one endpoint; it is not reported as a proportion greater than one.

## Closed handoff

The complete independent exact certificate is

\[
 \left(
 D<{106771746\over10^8},\;
 \mu={333333\over500000},\;
 M_2>{18717\over50000},\;
 P(y)={57y^2+48y-9\over121},\;
 L^\sharp={105\over64}
 \right).
 \tag{24}
\]

It uses only the second centered moment, so its trace bandwidth is
\(2\mu=1.333332<2\); the inherited cubic admissibility margin is more than
is needed.  The factors (9), (10), and (13) are the full sign proof, and
(17)--(22) are the full directed rational arithmetic.