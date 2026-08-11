# Hybrid cycle 6: the complete (K=2) geometric moment

## Outcome

The first divisor-sensitive geometric correction is completely covered by the
structured (4/7) twisted-second-moment theorem.  No term has to be shortened
to the generic (T^{1/2+1/46}=T^{12/23}) range.

After retaining every cross term and optimizing the two profiles, the explicit
parameters

\[
 \theta={4\over7},\qquad a=0.96857558,\qquad R=1.11664332,
\tag{1}
\]

\[
\begin{aligned}
 P_1(x)={}&x+0.05132072x(1-x)-0.64290509x(1-x)^2\\
          &-0.04287273x(1-x)^3-0.07298717x(1-x)^4,\\
 P_2(x)={}&1.05546375x-0.14748502x^2+0.07464249x^3
\end{aligned}
\tag{2}
\]

give

\[
 I_2=1.93789060\ldots,
 \qquad
 1-{\log I_2\over R}=0.40750995\ldots .
\tag{3}
\]

Thus the (K=2) Routh/Levinson charge is

\[
 {\mathfrak R_a(T)\over N(T)}
 \le {\log I_2\over 2R}
 =0.29624503\ldots,
\tag{4}
\]

and its simple-critical-line conclusion is only (40.750995\%\).  The
accepted (67.25007036\%\) theorem is strictly stronger.  Adding (K=3)
changes this only to the already available (40.7511457\%\).  Consequently
the finite geometric (K=2,3), length-(4/7), linear-(V_a) thread is
terminated: it supplies no unconditional gain over the accepted base.

At (1), the (85\%\) stopping threshold is

\[
 e^{0.15R}=1.18234115\ldots,
\tag{5}
\]

whereas (3) is (1.93789060\ldots).  This is not a missing-cross-term
problem; (3) includes all six blocks below.

## 1. Reduction of the literal geometric coefficients

Put

\[
 \psi^{(2)}(s)=\sum_{j=0}^2{1\over(aL)^j}
 \sum_{n\le T^\theta}{(\mu*\Lambda^{*j})(n)\over
 n^{s+R/L}}W_j\!\left({\log(T^\theta/n)\over\theta L}\right).
\tag{6}
\]

The identity

\[
                (\mu*\Lambda)(n)=-\mu(n)\log n                 
\tag{7}
\]

is exact.  Hence the (j=0,1) pieces of (6) combine into an arbitrary
Conrey profile

\[
 P_1(x)=W_0(x)-{\theta\over a}(1-x)W_1(x).
\tag{8}
\]

For example, (2) is represented literally by taking (W_1(x)=x) and

\[
 W_0(x)=P_1(x)+{\theta\over a}x(1-x).
\tag{9}
\]

The first new arithmetic piece is (j=2).  In the normalization used in
the structured moment its profile is

\[
 P_2(x)={\theta^2\over a^2}W_2(x),
 \qquad W_2(x)={a^2\over\theta^2}P_2(x).
\tag{10}
\]

Thus (1)--(2) are an actual member of the stated geometric family, not an
unrelated Feng mollifier.  Independent smooth cutoffs make (8)--(10) an
exact reparametrization.

## 2. Complete (K=2) quadratic functional

Write (p=P_1, q=P_2), and, for a shift variable (z), define

\[
\begin{aligned}
 V_0(z,t)={}&z\theta p(1-t)+p'(1-t)
       +\int_0^{1-t}q(1-t-u)e^{-z\theta u}\,du,\\
 V_1(z,t)={}&-2q(1-t),\\
 V_2(z,t)={}&z\theta q(1-t)+q'(1-t).
\end{aligned}
\tag{11}
\]

Specializing the general structured coefficient formula to (K=2), and
performing the overlap combinatorics before taking any inequality, gives

\[
\begin{aligned}
 {\cal F}_2(z,w;t)={}&V_0(z)V_0(w)\\
 &+t\{V_0(z)V_1(w)+V_1(z)V_0(w)\}\\
 &+{t^2\over2}\{V_0(z)V_2(w)+V_2(z)V_0(w)\}\\
 &+t^2V_1(z)V_1(w)\\
 &+{t^3\over2}\{V_1(z)V_2(w)+V_2(z)V_1(w)\}\\
 &+{7t^4\over24}V_2(z)V_2(w).
\end{aligned}
\tag{12}
\]

The coefficient (7/24=(1+4+2)/4!) in the final block is the sum of
the zero-, one-, and two-common-prime overlaps.  In particular, replacing
it by a diagonal or Cauchy bound loses part of the actual cancellation.

Because the two lengths are both (4/7), the extra unequal-length
integral is empty.  Set

\[
 {\cal H}_2(z,w;t)=
 { {\cal F}_2(w,z;t)-e^{-z-w}{\cal F}_2(-w,-z;t)
  \over \theta(z+w)}.
\tag{13}
\]

For

\[
 G_a(s)=\zeta(s)+{\zeta'(s)\over aL},
 \qquad Q_a(x)=1-{x\over a},
\tag{14}
\]

the complete normalized second moment is

\[
 \boxed{
 I_2(a,R;p,q)=\int_0^1
 \left(1+{\partial_z\over a}\right)
 \left(1+{\partial_w\over a}\right)
 {\cal H}_2(z,w;t)\bigg|_{z=w=-R}\,dt .}
\tag{15}
\]

Equations (11)--(15) are the requested bilinear functional.  They contain
the (00,01,02,11,12,22) blocks before any absolute value or Cauchy
inequality.  Every integral is elementary for polynomial (p,q).

The optimization used the stable bases

\[
 p(x)=x+x(1-x)\sum_{j=0}^7c_jP_j(2x-1),\qquad
 q(x)=x\sum_{j=0}^7d_jP_j(2x-1),
\tag{16}
\]

where (P_j) is the Legendre polynomial.  At fixed (a,R), (15) is a
positive quadratic polynomial in ((c,d)), so its profile minimum is
obtained by one linear solve, with no alternating or coordinatewise
optimization.  Optimizing the remaining two scalars gives (1)--(3).
Increasing the two profile spaces beyond (16) changes the displayed
constant below the last quoted digit.

## 3. Why the (12/23) asymmetric fallback is inactive

The (22) block is the apparently longest term, but its coefficients are
the structured convolution (\mu*\Lambda*\Lambda).  The (4/7) theorem
evaluates this block together with the (02) and (12) crosses.  Hence
there is no unsupported generic-coefficient term to map to (12/23).
Shortening only (q) to (12/23) discards admissible length and cannot
repair the large numerical gap in (5).

## 4. Non-scalar union with the support-(5/4) Gram certificate

Let

\[
 D_{5/4}=1.20278584713866\ldots,qquad
 \beta_{5/4}=2-D_{5/4}=0.79721415286134\ldots,
\tag{17}
\]

and choose any (K=2)-certified set of

\[
 \kappa_2N=(0.4075099495\ldots)N
\tag{18}
\]

simple critical-line zeros.  If (K_T) is the sum of their normalized
rank-one Gram atoms and (G_T) is the support-(5/4) Gram matrix, deleting
those atoms before applying the residual rank--trace inequality gives the
exact block-union identity

\[
 {N_0^s\over N}\ge
 \beta_{5/4}+2x-q-\kappa_2-o(1),
 \quad
 x={\operatorname{tr}(G_TK_T)\over N},\quad
 q={\|K_T\|_F^2\over N}.
\tag{19}
\]

Thus (85\%\) would follow from the single mixed bound

\[
 \boxed{2x-q\ge0.4602957967\ldots,}
\tag{20}
\]

or equivalently from a residual gain

\[
 2x-q-\kappa_2\ge0.05278584714\ldots .
\tag{21}
\]

This is a genuine non-scalar combination.  Counts alone cannot prove
(21), because the selected set may be wholly contained in the set already
certified by (17).  Under independent thinning of the Gram atoms, its
expected gain is

\[
 \kappa_2(2-\kappa_2)(D_{5/4}-1)
 =0.1315989989\ldots,
\tag{22}
\]

which would give (92.88131518\%\).  Only (40.1112\%\) of that benchmark
is required.  Unconditionally, however, the finite geometric moment
(15) provides no lower bound for the mixed statistic (21); extracting
that statistic requires a weighted Levinson selector on the zero side.

## Terminal gate

* Unconditional output of the (K=2) construction: (40.750995\%\).
* Strongest unconditional output after taking the accepted theorem: still
  (67.25007036\%\).
* Rigorous reason to kill this finite-geometric thread: its complete
  evaluable (K=2) functional, and the adjacent (K=3) functional, both
  give Routh charges near (0.29624N), strictly weaker than the accepted
  charge (0.16374965N); no omitted cross term or available length
  extension remains inside this method class.
* First concrete step outside it: turn the weighted Levinson argument into
  a zero-side selector whose weight is retained in
  (2\operatorname{tr}(G_TK_T)-\|K_T\|_F^2-\operatorname{tr}K_T), rather
  than collapsing it to the scalar count (18).
