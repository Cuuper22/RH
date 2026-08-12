# Root 95% cycle 2: a strict nested-quartic stability increment

## Result

At the fixed proved support

\[
\sigma_0=1.499999<3/2,
\]

use the conservative full-matrix cost

\[
D_0=1.134325953,
\qquad \beta_0=2-D_0=0.865674047.
\]

Embed an absolute-bandwidth

\[
\mu=\frac{499}{1000}<\frac12
\]

block as an exact principal compression by the power-complementary Gabor
partition from certificate cycle 3.  Its centered eigenvalue
\(Y=C-I\), scaled as \(Z=Y/\mu\), has the unconditional four moments

\[
\mathbb E1=1,
\qquad \mathbb EZ=\mathbb EZ^3=0,
\qquad \mathbb EZ^2=\frac13,
\qquad \mathbb EZ^4=\frac4{15}.
\tag{1}
\]

The stability and moment argument below gives the fixed unconditional bound

\[
\boxed{
\liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
\ge 0.8671703150772\ldots .}
\tag{2}
\]

This improves the support-\(<3/2\) checkpoint by more than
\(0.001496\), without extending the prime-pair support.

## 1. Stability form of the rank--trace inequality

Use the accepted zero-side decomposition

\[
G=P+Q,
\qquad P\succeq0,
\qquad \operatorname{rank}P\le s,
\qquad \operatorname{tr}P\le s,
\qquad n_+(Q)\le b,
\tag{3}
\]

where \(s=N_0^s\) and \(s+2b\le N\).  Write
\(Q=Q_+-Q_-\), with \(Q_+Q_-=0\), and put

\[
R=P-Q_-.
\]

Since \(Q_+\) has rank at most \(b\), Weyl's inequality gives

\[
\lambda_{b+j}(G)\le\lambda_j(R).
\tag{4}
\]

Also \(n_+(R)\le s\), because \(R\preceq0\) on the orthogonal complement
of the range of \(P\).  Consequently

\[
\sum_{i>b}(\lambda_i(G)-1)_+^2
\le \sum_j(\lambda_j(R)-1)_+^2
\le \|R\|_F^2-2\operatorname{tr}R+s.
\tag{5}
\]

Expand the rank--trace slack.  All the omitted terms below are nonnegative:

\[
\begin{aligned}
&\|G\|_F^2-4\operatorname{tr}G+3s+4b\\
&\quad\ge
\|R\|_F^2-2\operatorname{tr}R+s.
\end{aligned}
\tag{6}
\]

Indeed, after subtracting the right side, the remaining terms are

\[
\|Q_+\|_F^2-4\operatorname{tr}Q_++4b
+2\operatorname{tr}(PQ_+)+2\operatorname{tr}Q_-
+2(s-\operatorname{tr}P),
\]

and the first three terms in the first group equal
\(\sum(q_j-2)^2+4(b-\operatorname{rank}Q_+)\).

With \(\operatorname{tr}G=N\), \(\|G\|_F^2\le D_0N\), and
\(b\le(N-s)/2\), equations (5)--(6) prove the stability inequality

\[
\boxed{
\sum_{i>b}(\lambda_i(G)-1)_+^2
\le s-(2-D_0)N.}
\tag{7}
\]

If \(C\) is any principal compression of \(G\), interlacing transfers the
same bound to its eigenvalues.

## 2. Exact trimmed four-moment certificate

The worst allowed number of free positive directions in the \(\mu N\)
block is

\[
\theta_0
=\frac{D_0-1}{2\mu}
=0.1345951432865\ldots
\tag{8}
\]

of its eigenvalues.  Let \(\rho\) be the empirical law of \(Z\), and let
\(\nu\le\rho\) be any measure supported on \(z>0\), with
\(\nu(\mathbb R)\le\theta_0\).  The measure \(\nu\) represents the positive
directions that the nonsimple block may absorb for free.

Set

\[
a=-\frac{811}{1000},
\qquad b_0=\frac17,
\qquad c=\frac{128}{125}.
\]

Let \(P(z)=p_0+p_1z+\cdots+p_4z^4\) and \(L\) be the unique rational
solution of

\[
\begin{array}{lll}
P(a)=P'(a)=0,&
P(b_0)=b_0^2,&P'(b_0)=2b_0,\\
P(c)=L,&P'(c)=0.&
\end{array}
\tag{9}

Explicitly,

\[
\begin{aligned}
p_0&=-\frac{57395327653955816}{4363642419687893859},\\
p_1&= \frac{265658044611543808}{1454547473229297953},\\
p_2&= \frac{1624414019009558875}{4363642419687893859},\\
p_3&=-\frac{19870174322250000}{1454547473229297953},\\
p_4&=-\frac{916480914125000000}{4363642419687893859},\\
L&=\frac{1803294431147272}{5659717794666529}.
\end{aligned}
\tag{10}

These coefficients obey, for every real \(z\),

\[
P(z)\le0\quad(z\le0),
\qquad
P(z)\le z^2\quad(z\ge0),
\qquad
P(z)\le L\quad(z\ge0).
\tag{11}

This is an algebraic sign check, not a numerical assumption.  The three
differences factor respectively by

\[
(z-a)^2,
\qquad (z-b_0)^2,
\qquad (z-c)^2.
\]

For \(P\), the remaining quadratic has negative leading coefficient and
two positive roots.  For \(z^2-P\) and \(L-P\), the remaining quadratics
have positive leading coefficients and negative discriminants.

It follows from (1) and (11) that the positive square energy remaining after
the free measure is removed satisfies

\[
\begin{aligned}
\int z_+^2\,d(\rho-\nu)
&\ge \int P(z)\,d\rho-L\theta_0\\
&=p_0+\frac{p_2}{3}+\frac{4p_4}{15}-L\theta_0\\
&>0.01204225.
\end{aligned}
\tag{12}

Returning to the \(\mu N\)-dimensional block and \(Y=\mu Z\),

\[
\sum_{i>b}(\lambda_i(C)-1)_+^2
>\mu^3(0.01204225)N
>0.0014962680772N.
\tag{13}

## 3. Transfer to simple zeros

Combine the lower bound (13) with the upper stability bound (7):

\[
\frac{s}{N}
\ge \beta_0+0.0014962680772
>0.8671703150772.
\]

The input inventory is limited to the accepted support-\(<3/2\) two-trace
theorem, the exact nested Gabor compression, the unconditional
Rudnick--Sarnak-range moments (1), interlacing, and the rational polynomial
(9)--(11).  No RH, new prime-pair asymptotic, or phase-current estimate is
used.

## Immediate continuation

The same stability certificate becomes substantially stronger if the
signed-shift arithmetic reaches support \(2\).  At the prospective
\(D_2\approx1.06771738\), the first-pass trimmed-quartic increment is about
\(0.00546\), and iterating the implicit stability inequality points to a
checkpoint near \(0.93826\).  That branch is now waiting only on the
support-\(<2\) trace construction, not on a new higher-moment theorem.
