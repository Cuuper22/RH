# Certificate 100, cycle 5: a charged quadratic forces density one

## Terminal theorem

Keep the accepted strict pair and block inputs

\[
 D<1.06771746,
 \qquad
 \mu={333333\over500000}=0.666666,
 \qquad
 3\mu=1.999998<2,                                \tag{1}
\]

and the outer-gap mean-one block from cycle 4, whose centered second moment
satisfies

\[
 M_2>{18717\over50000}=0.37434.                  \tag{2}
\]

The charged stability theorem proved in the parallel hybrid construction is

\[
 T_b(C)+H_b(C)\leq \varepsilon N+o(N),           \tag{3}
\]

where, for the eigenvalues of the positive block compression \(C\) in
decreasing order,

\[
 T_b(C)=\sum_{i>b}(\lambda_i(C)-1)_+^2,
 \qquad
 H_b(C)=\sum_{i\leq b}(\lambda_i(C)-2)_+^2.       \tag{4}
\]

Here

\[
 {s\over N}=2-D+\varepsilon,
 \qquad
 {b\over N}\leq {D-1-\varepsilon\over2}+o(1).   \tag{5}
\]

An exact rational quadratic dual applied to (3) gives a contradiction to
every subsequential limit \(s/N<1\).  Consequently

\[
 \boxed{\displaystyle
 \liminf_{T\to\infty}
 {N_{0,\mathrm{simple}}(T,2T)\over N(T,2T)}=1.}  \tag{6}
\]

This is an asymptotic density-one theorem for simple critical-line zeros; it
does not assert that every individual nontrivial zero has this property.

## 1. Charged stability in the form used here

For completeness, the zero-side inequality behind (3) is short.  Write the
accepted decomposition

\[
 G=P_0+Q,
 \qquad P_0\succeq0,
 \quad\operatorname{rank}P_0\leq s,
 \quad\operatorname{tr}P_0\leq s,
 \quad n_+(Q)\leq b.                              \tag{7}
\]

Ky Fan's principle gives at most \(s\) positive eigenvalues after the first
\(b\), with their sum at most \(s\).  If those eigenvalues, padded by zeros,
are \(\rho_1,\ldots,\rho_s\), then

\[
 \rho^2-4\rho+3-(\rho-1)_+^2
 \geq2(1-\rho)\qquad(\rho\geq0).                 \tag{8}
\]

For each of the first \(b\) eigenvalues,

\[
 (\lambda-2)_+^2\leq\lambda^2-4\lambda+4.       \tag{9}
\]

Summing (8)--(9), using \(\sum\rho_j\leq s\), and then using

\[
 \operatorname{tr}G=N,
 \quad \|G\|_F^2\leq DN,
 \quad 4b\leq2(N-s),                             \tag{10}
\]

gives

\[
 \sum_{i\leq b}(\lambda_i(G)-2)_+^2
 +\sum_{i>b}(\lambda_i(G)-1)_+^2
 \leq \|G\|_F^2-4\operatorname{tr}G+3s+4b
 \leq\varepsilon N.                             \tag{11}
\]

Principal-compression interlacing transfers (11) from \(G\) to \(C\), which
is (3).  Notice that the second term in (4) is exactly the stability slack
discarded by the old hard trim.

## 2. Exact quadratic dual

Put \(Y=C-I\), so every centered eigenvalue \(y\) lies in
\([-1,\infty)\).  Take

\[
 c={7\over20},
 \qquad a={1\over(1+c)^2}={400\over729},          \tag{12}
\]

and define

\[
 \begin{aligned}
 P(y)
   &=y^2-a(y-c)^2\\
   &={-49+280y+329y^2\over729}.                  \tag{13}
 \end{aligned}
\]

The untrimmed scalar inequalities are global on the whole block spectrum.
Indeed,

\[
 P(y)={(y+1)(329y-49)\over729}\leq0
 \qquad(-1\leq y\leq0),                         \tag{14}
\]

and

\[
 y^2-P(y)={400\over729}\left(y-{7\over20}\right)^2
 \geq0\qquad(y\geq0).                           \tag{15}
\]

The charged cost of a top-\(b\) direction is not a flat supremum of \(P\),
but

\[
 L^\sharp=sup_{y\geq0}
 \{P(y)-(y-1)_+^2\}.                             \tag{16}
\]

For \(0\leq y\leq1\), \(P\) is increasing and

\[
 P(y)\leq P(1)={560\over729}<{609\over400}.      \tag{17}
\]

For \(y\geq1\), exact completion of the square gives

\[
 P(y)-(y-1)^2
 ={609\over400}
  -{400\over729}\left(y-{869\over400}\right)^2.\tag{18}
\]

Thus the exact global charged cap is

\[
 \boxed{L^\sharp={609\over400}=1.5225<2.}        \tag{19}
\]

Combining (14)--(19) eigenvalue by eigenvalue yields

\[
 \operatorname{tr}P(Y)
 \leq T_b(C)+H_b(C)+L^\sharp b.                  \tag{20}
\]

## 3. Moment value and the fixed-point contradiction

The block is mean one, so the centered first moment vanishes.  Equations
(2) and (13) therefore give

\[
 {1\over N}\operatorname{tr}P(Y)=\mu A_P+o(1),
 \qquad
 A_P=-{49\over729}+{329\over729}M_2,             \tag{21}
\]

and, with only outward-directed rational bounds,

\[
 A_P>
 -{49\over729}+{329\over729}{18717\over50000}
 ={3707893\over36450000}
 =0.1017254595336\ldots .                        \tag{22}
\]

Apply (3), (5), and (20):

\[
 \varepsilon
 \geq \mu A_P
 -{L^\sharp\over2}(D-1-\varepsilon)-o(1).       \tag{23}
\]

Since \(L^\sharp/2=609/800<1\), this is a genuine favorable fixed point.
Using

\[
 D-1<{6771746\over100000000},                    \tag{24}
\]

the right side of the solved inequality is strictly larger than

\[
 \begin{aligned}
 \varepsilon_*
 &={\displaystyle
 {333333\over500000}{3707893\over36450000}
 -{609\over800}{6771746\over100000000}
 \over\displaystyle 1-{609\over800}}\\[2mm]
 &={263525218243\over3867750000000}\\
 &=0.068133984420658\ldots .                     \tag{25}
 \end{aligned}
\]

But a proportion \(s/N\leq1\), together with the definition in (5), forces

\[
 \varepsilon\leq D-1<0.06771746.                 \tag{26}
\]

The strict gap between (25) and (26) is

\[
 \varepsilon_*-0.06771746
 ={201376541\over483468750000}
 =0.000416524420658\ldots>0.                     \tag{27}
\]

Hence no subsequence with a limiting simple-line proportion below one can
exist.  Equivalently, the formal lower expression is

\[
 2-1.06771746+\varepsilon_*
 ={483670126541\over483468750000}
 =1.000416524420658\ldots,                       \tag{28}
\]

and the excess over the tautological ceiling is precisely the contradiction
that closes (6), not a claim that a proportion exceeds one.

## 4. Relation to the requested compatible nesting attack

Before (3) became available, the minimal compatible redistribution was
carried out over the entire one-interval saturated family.  Starting from
the width-\(2/3\) outer-gap profile, the central width-\(0.4999\) restriction
has normalized mass \(0.940870390053\ldots\); only
\(0.059129609947\ldots\) is missing.  Moving exactly this mass from the
outer annulus into the central available cap gives at its best

\[
 M_2=0.37239448\ldots,
 \qquad M_3=-0.07056004\ldots .                  \tag{29}
\]

The optimized wide cubic floor is \(0.96512267\ldots\).  The actual nested
narrow restriction has

\[
 (M_2,M_3,M_4)
 =(0.32199806\ldots,-0.11539978\ldots,
   0.24122708\ldots),                            \tag{30}
\]

and its best interlacing soft step raises the joint value only to
\(0.96512519\ldots\).  One-sided asymmetric moves are smaller still.  Thus
the minimally redistributed compatible family does not recover the old
\(0.96518798\) floor.  The charged quadratic (13) is the first completed
calculation outside that nesting/soft-step class, and it upgrades the result
all the way to density one.

## Closed handoff

No higher moment, second compression, or further profile optimization is
needed for the density-one conclusion.  The complete strict certificate is
the tuple

\[
 \left(
 D={106771746\over10^8},\;
 \mu={333333\over500000},\;
 M_2>{18717\over50000},\;
 P(y)={-49+280y+329y^2\over729},\;
 L^\sharp={609\over400}
 \right).                                        \tag{31}
\]

Every arithmetic trace used here has total support \(2\mu<2\); the inherited
block already has the stronger cubic margin \(3\mu<2\).
