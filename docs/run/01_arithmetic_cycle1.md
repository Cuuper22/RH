# Arithmetic construction, cycle 1

## Accepted base and normalization

All statements and prime-side asymptotics in `zeta-two-thirds.pdf` are treated as established.  Write

\[
  \ell=\log(T/2\pi),\qquad L=\lambda\ell,\qquad X=e^L,
  \qquad N=N(T,2T)\sim \frac{T\ell}{2\pi}.
\]

For a nonnegative profile \(u\) supported in an interval of length \(\sigma\), normalized by
\(\int u=1\), the two-trace certificate has normalized Frobenius cost

\[
 D(u)=\int u(x)^2\,dx+\iint K(x-y)u(x)u(y)\,dx\,dy,
 \qquad \frac{N_{0}^{s}}N\ge 2-D(u)-o(1).
\]

On the already established Fourier band, \(K(t)=|t|\) for \(|t|\le1\).  If the expected
prime-pair main term is available at a frequency \(|t|>1\), then \(K(t)=1\) there.  Thus 85%
is exactly the target

\[
  D(u)\le 1.15. \tag{1}
\]

This form is the rescaling of (7.3) in the paper: if
\(u(x)=v(x/\lambda)\), then

\[
 \frac{1}{c_\lambda(v)}
 =\frac{\int u^2+\iint |x-y|u(x)u(y)}{(\int u)^2}.
\]

## 1. Two direct one-interval targets

### 1.1 Diagonal-only one-sided target

For one connected interval, ignoring the off-diagonal prime-pair main term gives the optimizer

\[
 u_\lambda(x)\propto \cos(\sqrt2x),\qquad |x|\le\lambda/2,
\]

and

\[
 c_\lambda^*=
 \frac{\sqrt2\tan(\lambda/\sqrt2)}
 {1+(\lambda/\sqrt2)\tan(\lambda/\sqrt2)}.
\]

The equation \(2-1/c_\lambda^*=0.85\) has the root

\[
 \boxed{\lambda_{\rm diag}=1.47342692508525}. \tag{2}
\]

At this value it is enough to prove a *one-sided* estimate saying that the exact off-diagonal
prime contribution is at most \(o(TL^3)\).  No full asymptotic is needed.  The expected
pair-correlation main term is in fact negative: for the normalized cosine profile,

\[
 \int u^2=0.7008349033,\qquad
 \iint |x-y|uu=0.4491650926,
\]

while

\[
 R_{>1}(u):=\iint (|x-y|-1)_+u(x)u(y)\,dx\,dy=0.0095210260.
\]

Thus the expected cost is \(1.15-R_{>1}=1.140478970\), which would actually certify
85.9521%.  The needed one-sided assertion is weaker: it permits any off-diagonal contribution
up to zero at main-term scale.

### 1.2 Correct connected-interval target with the prime-pair main term

If the weighted pair input gives \(K(t)=\min(|t|,1)\) throughout the support, the variational
problem is

\[
 D_\sigma^*=\min_{\substack{u\ge0,\ \mathrm{supp}(u)\subset[-\sigma/2,\sigma/2]\\
 \int u=1}}
 \left(\int u^2+\iint\min(|x-y|,1)u(x)u(y)\right).
\]

For \(1<\sigma<2\), put \(\delta=\sigma-1\), \(q=\delta/2\), and
\(b=(1-\delta)/2\).  The Euler equation is

\[
 u(x)+\int\min(|x-y|,1)u(y)\,dy=C.
\]

The even solution has the explicit shape

\[
u(x)=
\begin{cases}
C_0\cos(\sqrt2x),&0\le |x|\le b,\\
A\cos(t)+B\sin(\sqrt3t),&b\le |x|\le\sigma/2,
\end{cases}
\]

where on the positive edge \(t=|x|-1/2\), and \(A,B\) are fixed by matching value and
derivative at \(x=b\).  With \(C_0=1\), writing

\[
U=\cos(\sqrt2b),\quad U'=-\sqrt2\sin(\sqrt2b),\quad
\Delta=\sqrt3\cos q\cos(\sqrt3q)+\sin q\sin(\sqrt3q),
\]

one obtains

\[
A=\frac{\sqrt3\cos(\sqrt3q)U+\sin(\sqrt3q)U'}{\Delta},\qquad
B=\frac{-\sin q\,U+\cos q\,U'}{\Delta}.
\]

Evaluating \(C/(\int u)\) and solving \(D_\sigma^*=1.15\) gives

\[
 \boxed{\sigma_{85}=1.42960385087046}. \tag{3}
\]

At this point the diagonal cost is 1.158389023 and the required negative prime-pair correction
is only 0.008389039.  Equation (3), rather than (2), is the correct target if the main term is
evaluated instead of merely bounded above.

## 2. Exact prime sum that must be controlled

Retain the paper's notation

\[
a_n=\frac{\Lambda(n)}{\sqrt n},\qquad
\alpha_n^+=\int_0^T\Phi(x)^2 n^{ix}\,dx,\qquad
\alpha_n^-=\int_{-T}^0\Phi(x)^2 n^{ix}\,dx.
\]

The difficult part of Proposition 5.6, before Montgomery--Vaughan is applied, is exactly

\[
\begin{aligned}
\mathcal O_1(T;u)
=\frac1{2\pi^2}\Re\sum_{n\ne m}
\frac{a_na_m}{i(\log n-\log m)}
\bigg[&\Big(\frac nm\Big)^{2iT}(\alpha_m^++\alpha_n^-)\\
&-\Big(\frac nm\Big)^{iT}(\alpha_n^++\alpha_m^-)\bigg].
\end{aligned} \tag{4}
\]

For \(X\le T\), the paper bounds (4) by \(O(L^2X)=o(TL^3)\).  For \(X>T\), this
bound is too large and (4) has a genuine main term.  In additive-shift variables \(m=n+h\),
after a smooth dyadic partition in \(n\), (4) becomes a finite collection of weighted sums

\[
 \sum_h\sum_{n\asymp M}
 \frac{\Lambda(n)\Lambda(n+h)}{\sqrt{n(n+h)}}
 W_{T,M,u}(n,h), \tag{5}
\]

with natural shift length

\[
 H=\frac MT=M^{\,1-1/\alpha}\quad\text{when }M=T^\alpha. \tag{6}
\]

The weight in (5) is not conjectural: it is obtained directly from (4), or equivalently from

\[
\int_{-T}^{T}\Phi(x)^2e^{ix\log n}
\int_{T+x_-}^{2T-x_+}e^{it\log(n/(n+h))}\,dt\,dx. \tag{7}
\]

A smooth height cutoff can replace the sharp inner interval and makes (7) rapidly decreasing
for \(|h|\gg H\log^B T\).

For a connected profile, the trace-grade prime-pair statement is

\[
 \mathcal O_1(T;u)
 =-\frac{T\ell^3}{2\pi}R_{>1}(u)+o(T\ell^3), \tag{8}
\]

where \(R_{>1}\) is as above.  In the paper's \(v\)-coordinates this is

\[
 \mathcal O_1(T;v)
 =-\frac{TL^3}{2\pi\lambda}
 \iint_{|s-t|>1/\lambda}(\lambda|s-t|-1)v(s)v(t)\,ds\,dt
 +o(TL^3). \tag{9}
\]

For the direct route (2), only the upper bound \(\mathcal O_1(T;u)\le o(TL^3)\) is needed.

The same-sign term \(\mathcal O_2\) in (5.10) has no near-diagonal singularity because
\(\log(nm)\ge\log4\).  It reduces to endpoint exponential sums of
\(\sum\Lambda(n)n^{-1/2+it}\) and is a secondary Type-I/exponent-pair task.  It is not the
prime-pair bottleneck in (4).

## 3. Sparse support that bypasses the unknown band immediately above 1

The averaged Hardy--Littlewood theorem of Matomaki--Radziwill--Tao (MRT), *Correlations
of the von Mangoldt and higher divisor functions I*, gives the expected correlation for almost
all shifts in a range of length

\[
 H\ge M^{8/33+\varepsilon}.
\]

Via (6), this threshold corresponds to

\[
 \alpha\ge \alpha_0:=\frac{1}{1-8/33}=\frac{33}{25}=1.32. \tag{10}
\]

This suggests a profile whose autocorrelation never samples \(1<|x-y|<\alpha_0\).
Take three identical lobes.  Each lobe has width 1 and uses the accepted optimal width-one
profile.  Separate neighboring lobes by a nearest-point gap \(\alpha_0+\eta\).  Then every
difference is either

\[
 |x-y|\le1\quad\text{(same lobe)},
 \qquad\text{or}\qquad
 |x-y|\ge\alpha_0+\eta\quad\text{(different lobes)}. \tag{11}
\]

No mass lies in the hard band \((1,33/25]\).  The total support diameter is

\[
 \lambda_{3}=3+2(33/25+\eta)=5.64+2\eta. \tag{12}
\]

Let

\[
c_1^*=0.7532960678560707,\qquad D_1=1/c_1^*=1.3274992963205883.
\]

Give each lobe mass \(1/3\).  Within-lobe cost is \(D_1/3\), and all ordered cross-lobe
pairs have kernel value 1 and total mass \(2/3\).  Hence

\[
 D_3=\frac{D_1}{3}+\frac23
 =1+\frac{D_1-1}{3}
 =1.1091664321068628, \tag{13}
\]

so

\[
 c_3=\frac1{D_3}=0.9015779517421014,
 \qquad
 \boxed{2-D_3=0.8908335678931372}. \tag{14}
\]

Thus a three-lobe certificate has 4.08 percentage points of slack above 85% and only asks for
prime correlations in the established band \(|\alpha|\le1\) and the separated bands
\(|\alpha|\ge33/25+\eta\).

## 4. Why the published MRT theorem does not yet close (14)

MRT proves, outside \(O_A(H\log^{-A}M)\) exceptional shifts,

\[
 C_M(h):=\sum_{M<n\le2M}\Lambda(n)\Lambda(n+h)
 =\mathfrak S(h)M+O_A(M\log^{-A}M). \tag{15}
\]

Even after using a sieve bound on exceptional shifts, (15) licenses only

\[
 \sum_{|h|\ll H}|C_M(h)-\mathfrak S(h)M|
 \ll_A MH\log^{-A}M. \tag{16}
\]

The trace requires a much stronger *signed, weighted aggregate* statement.  For each of the
finitely many weights produced by pairs of lobes, it needs

\[
\boxed{
 \sum_h w(h/H)
 \big(C_M(h)-\mathfrak S(h)M\big)
 \ll_A M\log^{-A}M,
}\tag{AS}
\]

uniformly for \(M=T^\alpha\) in each cross band and \(H=M/T\).  Derivatives in \(n\)
arising from (7) require the corresponding smoothly weighted version of (AS).

There is a full factor \(H\) between (16) and (AS).  Arbitrarily strong logarithmic saving
does not replace that factor because \(H\) is a fixed power of \(M\).  This is why simply citing
the almost-all-shifts theorem does not evaluate the Frobenius trace, even though its exponent
motivates the spectral gap in (11).

The required factor can also be seen from (4): on \(n\asymp M\), the endpoint integral is
of size \(T\) and \(a_na_{n+h}\) supplies a factor \(1/M\).  An aggregate correlation error
\(E(M,H)\) therefore enters at scale roughly \((T/M)E(M,H)\), up to powers of \(L\).
To keep it at \(o(TL^3)\), one needs \(E(M,H)\ll M\operatorname{polylog}M\), not
\(MH\log^{-A}M\).

## 5. Type-I/II construction target

The next arithmetic step is not a full Hardy--Littlewood theorem.  It is (AS) for the six
cross-lobe weights in (7).

Insert a Heath-Brown or Vaughan decomposition of each \(\Lambda\) in (AS).

* Type-I terms have one short factor.  Poisson summation in the long factor and the smooth
  \(h/H\) weight should give the missing factor \(H\); these are the first terms to complete.
* The genuine Type-II remainder is a smooth shifted bilinear form of the shape

  \[
  \sum_h w(h/H)
  \sum_{ab-cd=h}\alpha_a\beta_b\overline{\alpha_c\beta_d}\,V(ab/M), \tag{17}
  \]

  after subtraction of its major-arc/singular-series term.
* MRT's Type \(d_3\) and Type \(d_4\) estimates control an absolute or exceptional-shift
  average and yield (16).  What is needed is to retain the oscillatory weight through the
  circle-method reduction and prove directly

  \[
   (17)_{\rm minor}\ll_A M\log^{-A}M. \tag{18}
  \]

  Candidate tools are the dispersion method followed by a Kuznetsov/large-sieve estimate,
  or the Robert--Sargos/Jutila estimates used by MRT without the absolute-value step that
  loses \(H\).

Equation (18), only for the fixed cross-lobe weights, is the narrowest currently visible
arithmetic bridge to (14).

## 6. Pole, endpoint, and tail handling for the long sparse support

The diameter (12) makes the paper's crude pointwise pole bound
\(\Pi_X\ll X^{1/2}/T\) useless.  This is an artifact of that bound, not yet a structural
obstruction.  Use \(C_c^r\) or Gevrey lobe edges and estimate the pole evaluations before
taking absolute values.  Repeated integration by parts gives, schematically,

\[
 |\widehat\varphi(\tau\pm i/2)|
 \ll_{r,\varphi} T^{-r}e^{L/4}\operatorname{poly}(L),\qquad \tau\asymp T. \tag{19}
\]

For fixed \(\lambda_3\), choosing \(r\ge6\) makes the rank-two pole contribution negligible
after summing over the \(O(TL)\) Gabor centers.  The same smoothness, or a Gevrey taper,
gives arbitrary polynomial/stretched-exponential decay away from the height window and can
absorb the Paley--Wiener factor \(e^{L/4}\) in the zero tail.  These estimates must be written
into the long-support version of Theorem 5.8, but they do not demand new information about
primes.

## 7. Result of cycle 1

* **Unconditional support already completed by the accepted PDF:** \(|\alpha|\le1\), giving
  0.6725007.
* **Direct connected support sufficient for 85%:** \(1.4734269251\) with the one-sided
  estimate \(\mathcal O_1\le o(TL^3)\), or \(1.4296038509\) with the expected weighted
  pair main term.
* **Sparse algebraic construction:** three width-one lobes separated past \(33/25\), giving
  0.8908336 if (AS) is established.
* **Exact blocker:** the trace-grade aggregate Type-II estimate (AS)/(18).  Published MRT
  machinery reaches the correct shift *range* but loses one factor \(H\) in the strength of
  the remainder.
* **Next construction:** prove Type-I parts of (AS), carry the six explicit cross-lobe weights
  through MRT's circle-method decomposition, and isolate the minimal Type-\(d_3/d_4\)
  bilinear inequality (18).  No further kernel search is needed until that estimate is either
  obtained or shown to require a different lobe geometry.
