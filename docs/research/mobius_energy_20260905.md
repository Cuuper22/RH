# Complete Möbius coefficient energy and the one-sided 85% target

Date: 2026-09-05. Ordinary mathematical derivations; not Lean-verified.
The estimates below concern explicit complete divisor sums. Their application
through the repository's terminal decomposition remains incomplete; no improved
unconditional zero proportion is claimed.

## 1. Sharp mean-square bounds with a slowly varying Mellin twist

For real a and positive integer n, define

\[
 E_a(n)=\sum_{d\mid n}\mu(d)d^{ia}
       =\prod_{p\mid n}(1-p^{ia}),\qquad
 D_a(n)=\sum_{d\mid n}\mu(d)d^{ia}\log d.
\]

Let Z>=3, let ell/log Z lie in a fixed compact subinterval of (0,infinity),
and put a=tau/ell. There are fixed constants C and B, depending only on that
comparability interval, such that, uniformly for real tau,

\[
 \sum_{n\le Z}|E_a(n)|^2\le C(2+|\tau|)^B\frac Z{\log Z},\qquad
 \sum_{n\le Z}|D_a(n)|^2\le C(2+|\tau|)^B Z\log Z.       \tag{1}
\]

The arithmetic input is Shiu's theorem for nonnegative multiplicative f with
uniform bounds f(p^k)<=A_1^k and f(n)<=A_2(epsilon)n^epsilon for every epsilon>0.
Its modulus-one, dyadically summed consequence is

\[
 \sum_{n\le Z}f(n)\ll\frac Z{\log Z}
       \exp\!\left(\sum_{p\le Z}\frac{f(p)}p\right).     \tag{2}
\]

The constant is uniform over a family with the same growth constants.
Source: P. Shiu, *A Brun–Titchmarsh theorem for multiplicative functions*,
J. reine angew. Math. 313 (1980), 161–170, Theorem 1,
[DOI](https://doi.org/10.1515/crll.1980.313.161).
The hypotheses and uniform dependence are also stated in Theorem 1.1 of
[T. Wright's research paper](https://arxiv.org/html/2508.17217v1#S1).
Only Shiu's original bounded-growth theorem is used, not Wright's weaker
logarithmic denominator for a larger function class.

**Proof of (1).** Extend E to the entire function
E_z(n)=product_{p|n}(1-p^{iz}). For z on the circle |z-a|=r=1/log Z,
we have |Im z|<=1/log Z. Define a nonnegative multiplicative function by
f_z(p^k)=|1-p^{iz}|^2 for p<=Z and f_z(p^k)=1 for p>Z, k>=1.
Then f_z(n)=|E_z(n)|^2 for n<=Z and

\[
 f_z(p^k)\le(1+e)^2,
 \qquad f_z(n)\le((1+e)^2)^{\omega(n)}\ll_\epsilon n^\epsilon.
\]

These are uniform growth bounds; modifying primes beyond Z is essential for
that claim when Im z<0. Taylor's inequality on small primes and the bound
(1+e)^2 on the remaining primes, split at log p=1/|z|, give

\[
 \sum_{p\le Z}\frac{f_z(p)}p
   \le C_0+C_1\log(2+|z|\log Z)
   \le C_2+C_1\log(2+|\tau|).                         \tag{3}
\]

For the small primes use sum_{p<=Y}(log p)^2/p=O((log Y)^2);
for the rest use Mertens' prime-harmonic estimate. If the split lies outside
[2,Z], the same bounds apply to the single nonempty piece.
Equations (2)–(3) bound sum_{n<=Z}|E_z(n)|^2 by poly(tau)Z/log Z,
uniformly on the circle and also at its real center.
Since E'_a(n)=iD_a(n), Cauchy's derivative formula and Cauchy–Schwarz give

\[
 |D_a(n)|^2\le r^{-2}\frac1{2\pi}\int_0^{2\pi}
                  |E_{a+r e^{i\theta}}(n)|^2\,d\theta.
\]

Sum over n and use the circle bound. The factor r^{-2}=(log Z)^2
proves the second estimate in (1), without an extra log log Z.

## 2. Why the coupled source weight need not cost logarithmic powers

For a fixed smooth compactly supported G, use the Fourier convention
G(v)=integral Ghat(tau)e^{i tau v}d tau. Then, for positive p,q,x,

\[
 G\!\left(\frac{\log(pqx)}\ell\right)
 =\int\widehat G(\tau)p^{i\tau/\ell}q^{i\tau/\ell}
                         x^{i\tau/\ell}\,d\tau.          \tag{4}
\]

Complete divisor sums carrying log(px) become D_a+log(x)E_a.
The polynomial dependence in (1) is integrable against Ghat, so (4)
retains the actual weight rather than replacing it by a constant.
If an exact transformation yields complete coefficients with Z comparable
to T and an x interval of bounded length, full-period Parseval and (1),
including an outer ell factor, suggest the adequate size O_G(T ell^2).
This implication requires the precise coefficient representation and all
weights to meet the stated bounds; it is not a proved terminal-block estimate.

## 3. Exact complementary identity, including nonsquarefree integers

For R>0 define Lambda_R(n)=sum_{d|n,d<=R}mu(d)log(R/d), with value zero
when R<=1. For n>1 and r=rad(n),

\[
 \sum_{d\mid n,\ d\ge R}\mu(d)\log(d/R)
 =\Lambda_R(n)-\Lambda(n)
 =\mu(r)\Lambda_{r/R}(r).                              \tag{5}
\]

The first equality subtracts the d<R terms from the full sum
sum_{d|n}mu(d)log(d/R)=-Lambda(n); boundary terms vanish.
For the second, only squarefree divisors contribute. Write d=r/e and use
mu(r/e)=mu(r)mu(e), valid because r is squarefree. The remaining sum is
exactly Lambda_{r/R}(r). This proves (5) for every n, without discarding
nonsquarefree integers. The complementary cutoff r/R is at most n/R.
A sharp average with this radical-dependent cutoff requires additional work.

## 4. Normalize the actual one-sided target

Write ell=log(T/(2*pi)), N=N(T,2T)~T ell/(2*pi), and let u>=0 be even
with integral u=1. Choose phi(y)^2=u(y/ell) and define

\[
 Q_T=\frac{T\ell^3}{2\pi}\sim\ell^2N,\quad
 A_u(t)=\int u(x)u(x+t)\,dx,\quad
 D_{\rm diag}(u)=\int u^2+\int|t|A_u(t)\,dt.
\]

The accepted base PDF, §§5.3–5.8 and 7.1, gives these raw normalizations.
Once the actual first-trace and zero-side hypotheses are supplied, it suffices
for the genuine off-diagonal term O_1 and all remaining normalized errors that

\[
 \limsup_{T\to\infty}\frac{\mathcal O_1+E_{\rm secondary}}{Q_T}
             \le1.15-D_{\rm diag}(u).                    \tag{6}
\]

Here E_secondary includes the same-sign, mixed, pole, localization and
zero-side tail terms after putting them on the same raw scale.
For u_s(x)=cos(sqrt(2)x)/(sqrt(2)sin(s/sqrt(2))) on |x|<=s/2,

\[
 D_{\rm diag}(u_s)=\frac s2+\frac1{\sqrt2}\cot\frac{s}{\sqrt2}.
\]

At s=1.49 this is 1.147244350490937..., permitting a **positive** excess
of 0.002755649509063... in (6). The exact threshold is the trigonometric
expression; the decimals are illustrative numerical evaluations.
Smooth endpoint approximations must spend part of that margin.
No saturated-kernel asymptotic is needed for this formulation.

## 5. Preserve the special height kernel and the remaining gaps

For chi in C_c^infinity((1,2)), define k(s)=integral chi(v)cos(vs)dv.
Its Fourier transform is supported away from zero; hence k is Schwartz and
integral_R s^j k(s)ds=0 for every integer j>=0. The actual shift weight has
this cancellation. Taking its absolute value destroys it.

Two gaps prevent promoting (1) to the desired prime estimate. Internal
factor restrictions may prevent the complete Möbius sum used in (1) and (5).
Also, for x~1/R<1, a recombined shifted sum can require the short-arc energy
integral_{x~1/R}|sum_{t~TR}residual_R(t)e^{2*pi*i*t*x}|^2 dx.
Global Parseval supplies its full-period norm, not an additional factor 1/R.
Neither (1) nor (5) supplies that missing local-energy estimate. The source
normalization, divisor restrictions, and this short-arc issue must be resolved
in the actual transformation before claiming any gain in the zero proportion.
