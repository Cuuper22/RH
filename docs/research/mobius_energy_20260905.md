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


## Further arithmetic: exact cancellation, unresolved estimate

In the following continuation, $r_R=\Lambda-\Lambda_R$, $Z=TR$,
$R=T^\eta$, and $W$ is a fixed smooth profile supported in $[1,2]$.
The bandpass form is
$B(a,b)=\int\chi(R\alpha)\widehat a(\alpha)\overline{\widehat b(\alpha)}\,d\alpha$,
where $\chi\ge0$ is smooth and supported away from zero; $B_{\rm off}$
subtracts the exact diagonal coefficient. The signed inverse transform
is retained. Section numbers below refer to this research continuation.

## 12. Euler-product symmetry: a coercive reduction with an explicit cubic term

This attack uses the actual coefficients, so the modulated counterexamples of Section11 no longer satisfy the starting identity. All statements here concern the explicit reduced residual model from Section7; a bridge to every coupled original source weight is still required.

### Exact arithmetic identity and its identifying strength

Let Lf(n)=(log n)f(n), and use Dirichlet convolution. Differentiating the Euler product, or simply differentiating `Lambda=mu*log`, gives Selberg's exact identity

    L Lambda + Lambda*Lambda = mu*log^2.

Here log^2 denotes the pointwise square of log, not a convolution square. Put

    r_R = Lambda-Lambda_R,
    Xi  = Lambda*Lambda,
    A_R = mu*log^2 - (log n)Lambda_R.

Then coefficientwise

    (log n) r_R(n) = A_R(n)-Xi(n).

This really excludes additive modulation. Among functions f with f(1)=0, the equation `Lf+f*f=mu*log^2` uniquely identifies Lambda: for n>1, the convolution term involves only f at proper divisors, so induction determines f(n). Already at a prime p it requires f(p)=log p. Thus the identity uses substantially more information than prime support and sieve upper bounds.

### Multiplication by log n is coercive in the bandpass norm

Take `chi=|psi|^2` with psi smooth and compactly supported in (1,2), and let B be the bandpass form of Section7. Let W be a fixed bounded smooth dyadic profile, write

    a_n = r_R(n) W(n/Z),       Z=TR,
    B_off(a,b)=B(a,b)-k0 sum_n a_n conjugate(b_n),
    k0=(1/R) integral chi,     E_off=B_off(a,a).

The following estimate retains the signed kernel:

    (log Z) E_off
       <= Re B_off(a, A_R W) - Re B_off(a, Xi W)
          + O_{psi,W}(T log Z + R log Z).

It holds for fixed `R=T^eta`, 0<eta<1. Consequently

    E_off <= [Re B_off(a,A_R W)-Re B_off(a,Xi W)]/log Z
               + O_{psi,W}(T+R).

The remainder is o(T log T), the scale relevant to a fixed bandpass constant.

Proof of the analytic coercivity, rather than a formal log replacement: let P_psi be the Fourier multiplier psi(R alpha) on l2(Z), so `B(a,b)=<P_psi a,P_psi b>`. Extend log n from [Z,2Z] to a bounded real function l(n) on all integers with `l>=log Z` and Lipschitz constant O(1/Z). The convolution kernel of P_psi has first absolute moment O(R), hence Schur's test gives

    ||[P_psi,l]|| <= C_psi R/Z.

It follows that

    Re B(a,l a) >= (log Z) B(a,a)
                       - C_psi (R/Z)||a||_2^2.

The ordinary diagonal estimates give `||a||_2^2=O_W(Z log Z)` for fixed eta<1, since R^2 is a fixed power below Z. Thus the commutator costs only O(R log Z). Subtracting the exact bandpass diagonal introduces

    k0 sum_n log(n/Z)|a_n|^2 = O_W(T log Z).

Finally use the exact coefficient identity above. No main signed bilinear form is replaced by its absolute value in this argument.

### The cubic term and its support budget

The prime-supported nonlinear contribution is exactly

    C_R = Re sum_{n,d,m>=1; n!=dm}
           (Lambda(n)-Lambda_R(n)) Lambda(d)Lambda(m)
           W(n/Z) conjugate(W(dm/Z)) K_R(n-dm),

where `K_R(h)=R^(-1) integral chi(v)e(hv/R)dv`. It is a cubic prime term minus its mixed truncated-divisor correction, with both signs retained. In shift coordinates n=dm+h, this is a prime/prime-power versus product-of-two-prime-powers correlation, with h!=0. The Schwartz decay of K_R concentrates h on scale R without requiring a sharp cutoff.

Hyperbola symmetry permits d<m plus the d=m contribution. In every remaining dyadic block,

    D M ~ Z=T^(1+eta),
    2 <= D <= sqrt(2Z)=O(T^((1+eta)/2)),
    M >= constant*sqrt Z,
    |h| has scale R=T^eta.

At eta=.49 the factor boundary is .745, not the .49 boundary of the sieve cutoff. The region D<=R is distinguished by the additive phase scaling d/R<=1; the region R<D<=sqrt Z has a genuinely oscillating dilation. This is the precise new cubic geometry an arithmetic estimate must exploit.

The d=m contribution can be removed at negligible cost. For every interval of length R,

    sum_interval |Lambda(n)-Lambda_R(n)| = O(R log^2 Z),

by the elementary Lambda bound and by counting multiples in the defining divisor sum. Kernel decay therefore implies `sum_n |a_n K_R(n-s)|=O(log^2 Z)` uniformly in s~Z. The square-product vector is supported at s=d^2 with total weight at most `O(sqrt Z log^2 Z)`. Its entire contribution to C_R, including diagonal subtraction, is consequently

    O(sqrt Z log^4 Z).

After division by log Z this is o(T log T) for every fixed eta<1. General higher prime powers in d or m are NOT discarded by this argument; they remain in the exact formula.

### Exact quantitative target, and what has not been estimated

For a desired off-diagonal bound `E_off<=c T log T+o(T log T)`, it is sufficient to prove the single signed estimate

    Re B_off(a,A_R W)-C_R
       <= c(1+eta) T(log T)^2 + o(T(log T)^2).

For eta=.49 the coefficient is 1.49c. This reduction has a justified leading constant and a negligible error. Its gain is the explicit Euler-product/prime-semiprime structure; it is NOT a weakened hypothesis obtained for free.

In particular, the mixed term `B_off(a,A_R W)` contains the full divisor sum mu*log^2. It has not independently been estimated at the required scale. Treating it as an already-known short-sieve moment would be incorrect. A successful use of this reduction must estimate that mixed term together with C_R, or provide a justified short-divisor decomposition with controlled remainder.

### Sign check on actual coefficients

An independent sieve computation checked `mu*log^2 = Lambda log + Lambda*Lambda` through n=131072 with maximum floating error 1.26e-13. With Z=65536, hard dyadic W, and the same cosine band profile used in Section11, the exact cubic off-diagonal C_R had these values:

| R | E_off | C_R | Re B_off(a,A_R W) |
|---:|---:|---:|---:|
| 16 | 1438.93 | -110.01 | 16465.71 |
| 32 | 69.42 | -2526.00 | -1770.51 |
| 64 | 1.41 | 121.32 | 148.22 |
| 128 | 159.29 | -928.13 | 911.79 |
| 256 | 99.81 | -503.87 | 645.75 |

The bilinear symmetry identity agreed numerically to 8e-11. These signs rule out simply dropping C_R as a manifestly nonnegative correction, even for the actual prime coefficients. They do not rule out a useful asymptotic one-sided estimate for the linked mixed/cubic combination.

Result: the Euler-product constraint gives an exact prime-supported nonlinear identity, a valid leading-log coercivity estimate, and a precise cubic support budget. No new asymptotic constant for the linked signed combination has been proved.

## 13. Finite Vaughan cancellation and an explicit resonant bilinear form

This continues Section12 by cancelling the full long-Mobius/Selberg combination exactly before estimating it. The output is a finite identity with bounded coefficients, a grouped Poisson formula, and a negligible analytic remainder. It does not yet estimate the remaining arithmetic forms.

### Exact decomposition adapted to the residual cutoff

Write

    M_R = mu_{<R}*1,
    beta_V = 1*Lambda_{>V}.

The second coefficient is nonnegative, vanishes for m<=V, and satisfies `beta_V(m)<=log m`. The finite Vaughan identity is

    Lambda = Lambda_{<=V} + mu_{<R}*log
                 - M_R*Lambda_{<=V} + mu_{>=R}*beta_V.

Since `mu_{<R}*log-Lambda_R = log(n/R) M_R(n)`, it gives EXACTLY

    r_R(n) = Lambda_{<=V}(n) + log(n/R) M_R(n)
                       - (M_R*Lambda_{<=V})(n)
                       + (mu_{>=R}*beta_V)(n).

This is also the exact finite cancellation of `mu*log^2-Lambda*Lambda` in Section12 after multiplication by log n. No full-Mobius term is silently replaced by a short-sieve evaluation. On n~Z=TR the first term vanishes for the cutoffs below.

Set `V=T/R`, so the Type I merged modulus has q<RV=T. Let

    b_q = sum_{dc=q; d<R,c<=V} mu(d)Lambda(c).

The two pieces, with the SAME source profile W(n/Z), are

    I(n)  = log(n/R) sum_{d|n,d<R}mu(d) - sum_{q|n} b_q,
    II(n) = sum_{dm=n; d>=R,m>V} mu(d) beta_V(m),
    r_R(n)=I(n)+II(n)       (n~Z).

The support budget is explicit:

| eta | Type I modulus q | Type II exponent for d | Type II exponent for m | Product dm |
|---:|---:|---:|---:|---:|
| .49 | <=1 | [.49,.98] | [.51,1] | 1.49 |
| .9 | <=1 | [.9,1.8] | [.1,1] | 1.9 |

All exponents are in T, with harmless fixed constants at endpoints. Thus for eta<1/2 both Type II factors are at most O(T), but their product is still T^(1+eta). Calling the product a short polynomial would be wrong. For eta>.5 the Mobius factor also extends past T.

There is additional factor geometry when eta<1/2: both d and m are below V^2, and n is below V^3, eventually by fixed powers. Each factor has at most one prime exceeding V, and n at most two such primes. Prime powers with base below V remain in beta_V and must still be retained. The cofactor after two primes exceeding V is at most `O(Z/V^2)=O(T^(3eta-1))`, exponent .47 at eta=.49. This simplification is absent at eta=.9.

### Group every common rational resonance before taking a norm

Use $e(t)=e^{2\pi i t}$ and $\widehat W(u)=\int W(v)e(-uv)\,dv$, and define

    A_r = sum_{d<R; r|d} mu(d)/d,
    B_r = sum_{q; r|q} b_q/q,
    C_r = (log T) A_r-B_r,
    F(v)=W(v)log v.

The prime support of b gives the exact coefficient formula

    B_r = sum_{p^j<=V} (log p)/p^j * A_{r/gcd(r,p^j)}.

Poisson summation in the unweighted long slot, followed by reducing each rational k/q, gives the EXACT identity

    sum_n I(n)W(n/Z)e(n alpha)
       = Z sum_{r<=T; (a,r)=1}
           [ C_r W_hat(Z(a/r-alpha))
              + A_r F_hat(Z(a/r-alpha)) ].

Here a ranges over all integers, and 0/1 is included. This formula retains cancellation among all multiples of a reduced denominator; estimating the original q terms independently loses it.

For alpha in the support of chi(R alpha), all reduced denominators `r<cR`, with any fixed c<1/2, are rapidly negligible: their nonzero rationals lie a fixed multiple of 1/R outside the band, while the Poisson peak width is 1/Z. The separation in the transform argument is of order T. The zero rational is likewise separated. The surviving denominator range is therefore `r~R` through T, with numerators `a~r/R`.

An alternative form displays the logarithmic cancellation inside these coefficients. If `H_V=sum_{p^j<=V}log(p)/p^j`, then

    C_r = (log T-H_V)A_r
              - sum_{p|r; p^j<=V} (log p)/p^j
                   [A_{r/gcd(r,p^j)}-A_r].

Since H_V=log V+O(1), the first scalar is log R+O(1). The rest is an exact prime-divisor difference operator; it is not replaced by an absolute divisor bound in the resonant formula.

### The height derivative costs 1/T, with a proved remainder budget

Let J(alpha) be the Type II exponential sum with profile W. Consider the FULL mixed energy integral `integral chi(R alpha) I(alpha) conjugate(J(alpha)) d alpha`. At each rational put

    y=Ra/r,     u=Z(alpha-a/r),     v=dm/Z.

The height weight becomes `chi(y+u/T)`. Hence the mixed integral equals the following explicit resonant bilinear sum, up to the remainder described below:

    sum_{r,a; (a,r)=1} sum_{d>=R,m>V}
        mu(d) beta_V(m) e(-adm/r)
        { chi(y) W(v)[C_r W(v)+A_r F(v)]
           + i chi'(y)/(2pi T)
                W(v)[C_r W'(v)+A_r F'(v)] }.

Both the zeroth and first derivative terms are retained, including their phases. The real part of the first derivative term is a sine-weighted arithmetic sum; it cannot be dropped just because it carries an i.

The error after these two terms is

    O_W,chi( log^2 T + T^(eta-1) log^5 T ),

and is consequently o(T log T) for fixed eta<1. Here is an explicit budget rather than an unproved smooth-weight claim. Over the rationals in a fixed collar of the band,

    sum_{r,a} (|C_r|+|A_r|) << V+log^3 T.

Indeed `sum_r r|A_r|<<R`, `sum_r |A_r|<<log^2 R`, `sum_r r|B_r|<<RV=T`, and `sum_r |B_r|<<log^3 T`. The last two estimates follow by expanding b_q, using sigma_{-1}(dc)<=sigma_{-1}(d)sigma_{-1}(c), and using the prime-power support of Lambda(c). Also

    sum_{dm~Z; d>=R,m>V} |mu(d)| beta_V(m) << Z log^2 T.

Taylor's second-order remainder therefore costs at most

    T^(-2) (V+log^3 T) Z log^2 T
       = O(log^2 T+T^(eta-1)log^5 T).

The rapid Fourier tails outside the rational collar are smaller than any required fixed negative power after choosing enough Schwartz decay. Taking absolute values is used only for this negligible Taylor/tail remainder, not for the main mixed sums.

To obtain the mixed OFF-DIAGONAL form, subtract its exact single-index term `k0 sum_n I(n)II(n)W(n/Z)^2`; no asymptotic replacement of that diagonal is necessary.

### What remains, and an explicit cancellation check

The remaining arithmetic input includes bilinear sums

    sum_{d~D,m~M} mu(d) beta_V(m) W_*(dm/Z)e(-adm/r),

with `DM~Z`, `R<=D<=O(R^2)`, `V<=M<=O(T)`, `R<<r<=T`, and `a~r/R`, weighted by the EXACT C_r and A_r above. The two Type I/Type II squared terms must also be combined with this mixed contribution. Their product length has not fallen below T. In the Type I square, overlapping rational peaks satisfy

    |a s-b r| <= approximately rs/Z,

whose largest determinant scale is `T^2/Z=T/R=V`. This identifies the actual near-resonance scale but does not estimate its signed divisor coefficients.

A bounded computation at Z=65536, R=32, T=2048, V=64 checked the residual Vaughan identity independently with maximum error 9.2e-15. With the dyadic profile and chi(v)=sin^4(pi(v-1)) on [1,2], its off-diagonal decomposition was

| Term | Value |
|---|---:|
| Type I square | 5067.8182 |
| Type II square | 3381.2551 |
| Twice the mixed term | -8298.7807 |
| Actual residual | 150.2927 |

This demonstrates the cancellation destroyed by bounding the pieces separately. It supplies no asymptotic sign or sufficient constant.

Result: the full Selberg/Mobius tail has been converted exactly into a finite Vaughan split, and the mixed form has an explicit rational bilinear representation with a negligible, rigorously budgeted height-window remainder. Neither factorization nor this derivative gain supplies the missing arithmetic cancellation by itself. No estimate reaching the required 85-percent constant has been proved here.


## 14. Exact Buchstab regrouping and cancellation of the primary Ramanujan term

This gives a quantitative cancellation inside the decomposition of Section13. It estimates the explicitly defined principal model, not the remaining additive prime errors.

### Regrouping, with the dyadic endpoints retained

Since `beta_V=1*Lambda_{>V}`, group q=dl in the Type II term. For q>1,

    sum_{d|q,d>=R}mu(d) = -M_R(q).

Therefore, EXACTLY on n~Z,

    II(n) = -sum_{qc=n; q>=R,c>V} M_R(q)Lambda(c).

For Z<=n<=2Z, its ranges are `R<=q<2R^2` and `V<c<=2T`. No assumption about uniqueness of prime powers is required: Lambda(c) retains every prime power with its correct weight. In particular, at eta=.49 the prime-power factor ranges from T^.51 to O(T), while q ranges from T^.49 to O(T^.98).

### Exact arithmetic formula for the principal coefficient

Fix a reduced rational a/r and define the Ramanujan sum

    c_r(q)=sum_{b mod r,(b,r)=1}e(bq/r).

If g=(q,r), the principal coefficient for the prime exponential sum is

    mu(r/g)/phi(r/g) = c_r(q)/phi(r).

This defines a model; replacing the actual prime sum by it requires an error estimate. Let v be in [1,2], Y=R^2 v, and use strict upper endpoints in the following finite sums. The Type II principal coefficient is minus

    D_r(v) = (1/phi(r)) sum_{R<=q<Y} M_R(q)c_r(q)/q.

The same-rational Type I primary coefficient from Section13 is

    P_r(v)=A_r log(Tv)-B_r.

Also put

    L_r = sum_{d<R,r|d} mu(d)log(R/d)/d,
    H_V = sum_{p^j<=V}log(p)/p^j,
    L_infty(r) = sum_{p|r,j>=1} (log p)/p^j
                    [A_{r/gcd(r,p^j)}-A_r],
    L_V(r)=B_r-H_V A_r.

The infinite sum is convergent and explicit: after j reaches the exponent of p in r, its tail is geometric. Then the following identity is EXACT:

    P_r(v)-D_r(v)
       = mu(r)/phi(r)-L_r
          + A_r(log V-gamma-H_V)
          + [L_infty(r)-L_V(r)] - E_r(Y),

where the harmonic-floor remainder satisfies

    |E_r(Y)| <= C R sigma_1(r)/(phi(r)Y).

Here gamma is Euler's constant. The next paragraph defines this remainder exactly and proves the identity, so it is not an unspecified asymptotic error.

### Proof of the cancellation and the floor-error bound

Because M_R(q)=0 for 1<q<R and M_R(1)=1, the sum defining D_r is the full sum over q<Y with its q=1 term mu(r) removed. Expanding M_R gives

    sum_{q<Y} M_R(q)c_r(q)/q
       = sum_{d<R} mu(d)/d * sum_{k<Y/d} c_r(dk)/k.

Use `H_<x=sum_{1<=k<x}1/k` and `epsilon(x)=H_<x-log x-gamma`, for which `|epsilon(x)|<=C/x` for x>0. The exact divisor formula for Ramanujan sums yields

    sum_{k<X} c_r(dk)/k
       = sum_{s|r}(s,d)mu(r/s) H_<(X(s,d)/s).

The coefficient of log X+gamma is `phi(r)1_{r|d}`. Its constant term divided by phi(r) is

    -sum_{p^j>=1} (log p)/p^j
           [1_{r|dp^j}-1_{r|d}].

One can check the latter prime by prime. It is zero if r|d or if at least two prime factors of r have deficient valuation in d. If the sole deficiency is p^j, its value is `-log p/[p^(j-1)(p-1)]`.

Consequently the full q-sum divided by phi(r) is

    A_r(log Y+gamma)
      - sum_{d<R,r|d}mu(d)log d/d - L_infty(r) + E_r(Y),

with the exact remainder

    E_r(Y)=(1/phi(r)) sum_{d<R}mu(d)/d
          * sum_{s|r}(s,d)mu(r/s)
                epsilon(Y(s,d)/(ds)).

Its absolute value is at most `C R sigma_1(r)/(phi(r)Y)`. Substituting log Y=2log R+log v and log V=log T-log R proves the displayed identity for P_r-D_r.

### Uniform cancellation throughout the surviving rational collar

First, for fixed `c>0` and `cR<=r<R`, the elementary estimates

    |A_r|+|L_r|<<1/R,
    |L_infty(r)-L_V(r)|<<log^2(T)/V,
    A_r(log V-gamma-H_V)=o(1/R)

give the same `O((loglog T)^2/R)` conclusion from the exact formula. The
last term uses the prime number theorem
`H_V=log V-gamma+o(1)`.

Beyond that comparable range, every `r>=R` enjoys a stronger exact
simplification: the strict cutoff `d<R` gives

    A_r=L_r=0.

Consequently the `A_r(log V-gamma-H_V)` term also vanishes. Moreover,
`L_infty(r)-L_V(r)` is precisely the tail of the defining prime-power sum
with `p^j>V`. Summing its geometric tails and using
`|A_s|<=(1+log(R/s))/s` gives, uniformly for `R<=r<=T`,

    |L_infty(r)-L_V(r)| << log^2(T)/V.

The exact floor remainder and elementary Euler-product estimates give

    |E_r(R^2v)| << [sigma_1(r)/phi(r)]/R
                 << (loglog T)^2/R,
    |mu(r)|/phi(r) << loglog(T)/R.

It follows, uniformly for `v` in `[1,2]`, `cR<=r<=T`, and fixed
`eta<1/2`, that

    P_r(v)-D_r(v)
       = mu(r)/phi(r)
          +O(log^2(T)/V+(loglog T)^2/R)
       = O((loglog T)^2/R).                         (14.1)

Thus the principal Ramanujan model cancels across the entire denominator
range met by the bandpass. Before taking norms, every overlap between two
different rational packets carries the combined coefficients
`(P_r-D_r)(P_s-D_s)`. This does not assert a Bessel inequality for the
highly overlapping packet family, nor does it estimate the actual additive
prime errors or the Type II square.

For `r` comparable to `R`, (14.1) recovers the earlier interpretation:
the separate primary coefficients can have size `log R/R`, but their
leading `log R` terms cancel.

For a bounded check, R=32, V=64, v=1.3 gave the following coefficients; the exact identity agreed to 2.1e-16:

| r | Type I primary | Type II principal | Combined | mu(r)/phi(r)-L_r |
|---:|---:|---:|---:|---:|
| 19 | -.224889 | .198614 | -.026275 | -.028119 |
| 29 | -.145086 | .111877 | -.033209 | -.032320 |
| 31 | -.135419 | .102994 | -.032424 | -.032309 |
| 41 | .005682 | -.031742 | -.026060 | -.025000 |

### Exact descent for denominators with a large prime factor

There is a complementary structural reduction. Let `p` be prime,
`p` not divide `s`, and `p>Y/R`, where `Y=R^2v`. Comparing the Ramanujan
sums modulo `s` and `ps` gives the exact identity

    D_(ps)=[1_(p<Y) mu(s)/phi(s)-D_s]/(p-1).           (14.2)

The indicator is essential when `p>=Y`, because the term `q=p` then lies
outside the strict cutoff. For `eta>1/3`, direct substitution in `B_r`
also gives

    P_(ps)-D_(ps)
      =[D_s-1_(p<Y)mu(s)/phi(s)]/(p-1)
        -1_(p<=V)(log p/p)A_s.                         (14.3)

Thus every denominator containing a prime `p>Y/R` descends to a smaller
denominator, apart from the displayed one-prime boundary term. Iterating
(14.2) strips all such distinct primes; at `eta=.49` there can be at most
two of them in `r<=T`. This reduces the irreducible coefficient class to
`Y/R`-smooth bases. It is an exact coefficient identity only: after
coprime-numerator weighting, the resulting prime-harmonic square sums still
do not bound the synthesized packet norm because neighboring Farey packets
overlap. Formula (14.3) is consistent with (14.1); its two displayed terms
must not be estimated separately near `r~R`.

### Rigorous packet norm in a logarithmic collar

The pointwise bound (14.1) controls more than a single denominator shell,
but not a fixed-power collar. Put `Q=RH`, `B=(loglog T)^2`, and synthesize
every principal packet with `cR<=r<=Q`. Farey spacing, Plancherel, and one
integration by parts for each off-diagonal packet pair give

    ||principal_[cR,Q]||_2^2
      << T B^2 H^2
         +R B^2 H^4 log T
         +R B H^3 log^C T.                            (14.4)

This retains the `v`-dependence of `P_r-D_r`. For `r>=R`, its variation is
the step variation of `D_r`, and the finite q-sum gives

    Var D_r << log R tau(r)^2/phi(r).

For `cR<=r<R`, the additional `A_r log v` variation is `O(1/R)`.
Consequently (14.4) is `o(T log T)` whenever

    H^2(loglog T)^4=o(log T),

for example `H=(log T)^(1/2-epsilon)/(loglog T)^2`. This includes every
Farey overlap in that collar. Conversely, for `H=T^theta` the diagonal
upper scale from the uniform coefficient bound alone is
`T^(1+2theta)B^2`; essentially orthogonal packets show that no fixed-power
extension follows without additional arithmetic cancellation.

### Precisely what is still unevaluated

For each q and r, set `g=(q,r)`, `k=r/g`, `b=-a(q/g) mod k`, and prime length `X_q=Z/q`. The ACTUAL remaining additive prime error is

    E_{k,b}(X_q;w)
       = sum_{c>V} Lambda(c) w(c/X_q)e(bc/k)
          - [mu(k)/phi(k)] X_q
                * integral_{v>V/X_q} w(v)dv.

In the mixed term it occurs with the linked weights `C_r chi(Ra/r) M_R(q)`, together with the explicit A_r and first-derivative variants from Section13. Prime powers sharing a factor with k remain in this exact error definition; they have not been discarded.

For r~R, a generic reduced modulus k~R is below sqrt(X_q) only when q<=V. This gives the exponent-compatible interval `R<=q<=V`, but is NOT by itself a Bombieri--Vinogradov estimate for the aggregate: converting maximum single-residue progression errors into an additive Fourier error can lose a factor k.

The neighboring Type I rational packets also remain. At r~R and s<=T their relevant determinants satisfy `|as-br|=O(1)`. Substituting the b_s coefficients makes the associated product congruence have scale T, but its signed Mobius/prime coefficients have not been bounded here. Finally, evaluating only a mixed error does not control the Type II square.

Result: exact Buchstab regrouping and a quantified cancellation of the primary Ramanujan logarithm are proved. The next advance must estimate these remaining signed arithmetic errors or the linked energy; another identity alone will not establish the 85-percent target.


## 15. A proved small-reduced-modulus prime-error range

Research checkpoint, 2026-09-05. This note proves a negligible contribution
from **polylogarithmic reduced moduli** in the mixed prime-error form. It
does not estimate its complementary range or the Type II square, and gives
no new zero percentage.

### Exact variables and error

Use the coefficients in Sections13–14 above:

    R=T^eta, V=T/R, Z=TR, M_R=mu_<R * 1,
    II(n)=-sum_(qc=n; q>=R,c>V) M_R(q)Lambda(c).

Here q<=2R^2 and c<=2T. In the resonant mixed form the source denominator is
r, not q. Put

    g=(r,q), k=r/g, b=-a(q/g) mod k, Y=Z/q.

Then (b,k)=1, and the exact additive prime error is

    E_(k,b)(Y;w_q)
      =sum_(c>V) Lambda(c)w_q(c/Y)e(bc/k)
        -[mu(k)/phi(k)] Y integral_(v>V/Y) w_q(v)dv.

The leading mixed error is the signed sum of M_R(q)E_(k,b), weighted by
C_r chi(Ra/r); there are analogous A_r terms and explicit1/T derivative
terms. The profiles involved have uniformly bounded smooth norms and
variation. No coprime prime-power terms are omitted in this definition.

### Proved small-reduced-modulus lemma

For every fixed B>0 and M>0, the contribution to all these mixed errors
from

    k=r/(r,q) <= (log T)^B

is

    O_(B,M,W,chi)( T(log T)^(-M)
                   + T^eta(log T)^C ),                  (1)

for a fixed C depending on B and the profiles. In particular it is
o(T log T) for every fixed0<eta<1. At eta=.49 the second power is T^.49.
This is an unconditional asymptotic statement; its constants inherit the
usual ineffectivity of Siegel–Walfisz.

Proof. Write ell=log T and K=ell^B. The exact coefficient formulas imply

    |A_r| <= (1+log R)/r,
    |B_r| <= [(1+log R)/r]
              sum_(p^j<=V) (log p) gcd(r,p^j)/p^j
           << ell^2/r.

Indeed the last prime-power sum is O(log V+log r): the terms with p not
dividing r contribute O(log V), while for p^nu exactly dividing r the
additional contribution is O((nu+1)log p). Therefore

    |C_r|+|A_r| << ell^2/r.                              (2)

On the support of chi(Ra/r), r is bounded below by a fixed positive
multiple of R, and there are O(r/R) possible numerators a. Thus the sum
of absolute coefficient weights over a, for each r, is O(ell^2/R).
For fixed q, every eligible r has the form r=gk with g dividing q and
k<=K, so there are at most K tau(q) such r. Consequently the entire outer
weight for that q is at most

    O(K tau(q) ell^2/R).                                 (3)

Siegel–Walfisz is uniform over all reduced AP residues for moduli bounded
by a fixed power of log Y. We use the explicit statement in
[Baier–Pujahari, Propositions4–5](https://arxiv.org/html/2107.04348v5).
Here Y lies between fixed multiples of V and T, so log Y is comparable to
ell. Expanding the additive phase into residue classes and using partial
summation gives, for any fixed A,

    E_(k,b)(Y;w_q) << Y ell^(-A)+log k,
                         uniformly k<=K.                (4)

The factor at most phi(k) from additive Fourier expansion is absorbed by
choosing the Siegel–Walfisz logarithmic saving larger. Here one applies
Siegel--Walfisz directly to `psi(x;k,h)=sum Lambda(n)`, so every prime
power coprime to `k` is already included. The noncoprime Lambda-support
in a fixed dyadic window consists only of `c=p^j` with `p|k`; there are
`O(1)` eligible exponents per such prime and their total weight is
`O(sum_(p|k) log p)=O(log k)`. The cutoff `c>V` is retained by partial
summation with its endpoint. Thus (4) has no omitted prime-power term.

Finally `|M_R(q)|<=tau(q)`, and the elementary divisor estimates give

    sum_(q<=2R^2) tau(q)^2/q << ell^4,
    sum_(q<=2R^2) tau(q)^2 << R^2 ell^3.

Combining these with (3)–(4) proves a bound

    K T ell^(6-A)+K R ell^C.

Choose A sufficiently large in terms of B,M. This proves (1). The other
smooth profiles and the1/T derivative terms satisfy the same estimate.
Taking absolute values here does not destroy a required main cancellation:
it is used only for this now-negligible error subrange.

### Exponent match for the remaining moduli

At eta=.49 write q=T^t, r=T^rho, g=T^gamma. Then

    .49<=t<=.98, .49<=rho<=1,
    log_T Y=1.49-t, log_T k=rho-gamma.

A distribution theorem with exponent theta requires at minimum

    rho-gamma < theta(1.49-t),                           (5)

with a fixed margin. For r near R and bounded gcd, this gives:

| Theorem's exponent | Necessary upper endpoint for t |
|---|---:|
| Bombieri–Vinogradov,1/2 | .510000 |
| BFI,4/7 | .632500 |
| Maynard,3/5 | .673333… |
| Pascadi,5/8 | .706000 |

These are **size-compatible regions only**, not estimates for our weighted
additive error. In the balanced factor block t=.745, even the smallest
source denominator r near R requires prime-distribution exponent
.49/.745=98/149≈.65772, beyond5/8. For generic coprime r near T, none of
the listed exponents covers any of the q range. At q near R^2, even5/8
requires k<T^.31875, hence gcd(r,q)>r/T^.31875.


The exponent table is not a theorem match. The current $5/8$ result fixes
an AP residue and requires triply well-factorable modulus weights
([Pascadi, Theorem 1.3](https://arxiv.org/html/2505.00653v2)). Our reduced
modulus is $k$, our additive numerator varies, and converting a maximum
single-residue AP error into its additive Fourier sum can lose a factor
$\varphi(k)$. These losses have not been removed.

Nor is $M_R$ well-factorable at its natural level $2R^2$: it equals one
at every prime above $R$, whereas a sequence admitting a bounded
convolution for the balanced level split must vanish at primes above
$\sqrt2 R$. Its displayed convolution is only one factorization. This
does not exclude every possible regrouping of the actual $k$-weights.

The complementary moduli $k>(\log T)^B$, neighboring Type I packets, and
Type II square remain unestimated. The proved small-modulus range may be
removed with the displayed error budget; it does not change the zero count.

### Why an unconstrained Farey projection does not close the remainder

For packet synthesis $\Phi$, Gram matrix $G=\Phi^*\Phi$, arithmetic
coefficient vector $c$, and $v=\Phi^*II$, the exact identity is

\[
 \|I+II\|^2=\|II\|^2-v^*G^\dagger v
                 +(Gc+v)^*G^\dagger(Gc+v).
\]

The normal defect $Gc+v=\Phi^*(I+II)$ is the original prime-minus-sieve
transform at the linked rational frequencies. The packets can be highly
redundant, so this identity does not estimate that defect. Moreover the
small height-expansion remainder established for the original coefficients
cannot be passed through $G^\dagger$ without a separate amplification
bound. No such bound is asserted here.


## 16. Type-II square and a closed balanced mixed block

This section expands the remaining positive square before applying any
triangle inequality. Put

    C_(u,v,g)(h)=sum_(u c1-v c2=h) Lambda(c1)Lambda(c2)
                   W(gu c1/Z)W(gv c2/Z).

Writing `q1=gu`, `q2=gv`, `(u,v)=1`, gives the exact off-diagonal identity

    B_off(II,II)
      =R^(-1) sum_g sum_((u,v)=1) M_R(gu)M_R(gv)
          sum_(h!=0) hat_chi(-gh/R) C_(u,v,g)(h).       (16.1)

Thus the terminal quadratic error is a signed average of binary prime
correlations with the two linked `M_R` weights. For every fixed
`delta>0`, the range `g>=R^(1+delta)` is negligible. Indeed Schwartz
decay and Chebyshev give, for every `A>1`,

    contribution << T^2 R^(-delta(A+1)) log^C(T),       (16.2)

so `A` may be chosen after `delta`. The hard range is therefore
`g<R^(1+delta)`.

There is also a useful diagonal audit. Equality `q1 c1=q2 c2` forces
`u|c2` and `v|c1`. Since `c1,c2` are prime powers, the only possibilities
are the same representation, two distinct prime-power bases with
`c1=v,c2=u`, or a chain of powers of one prime. For distinct ordinary
primes at `eta=.49`, the cross-representation family has `g=1` and
`n=pq`, `p,q>V`. On it, exactly,

    I(pq)=log(pq/R),   II(pq)=-log(pq),   r_R(pq)=-log R.

The prime number theorem then shows that the combined diagonal coefficient
is `eta^2/(1+eta)^2` times the Type-II-square coefficient on this stratum.
At `eta=.49`, this removes `89.185%` of the separate Type-II diagonal.
This is an accounting identity, not an off-diagonal estimate; it proves
that estimating the Type-II square in isolation loses the main available
cancellation.

### Residue-class dispersion closes the balanced mixed block

A first grouping by the reduced phase `aq/r` gives only
`T^1.1175 log^A(T)` in the balanced block. That loss is artificial: it
counts all colliding q-values with the same sign before using complete
residue-class Parseval.

Let

    F(x)=sum_(q~Q) M_R(q)w(q/Q)e(qx),
    D(Q,R)=sum_(r~R) sum_(h mod r)
              |sum_(q~Q, q=h mod r) M_R(q)w(q/Q)|^2.

Parseval and reduction of `a/r=b/k` give the exact decomposition

    D(Q,R)=sum_(k<=2R) W_R(k) sum_((b,k)=1)|F(b/k)|^2,
    W_R(k)=sum_(g: R<=gk<2R) 1/(gk) << 1/k.           (16.3)

For `k~K`, the dual additive large sieve and `|M_R|<=tau` therefore give

    D_K << (Q/K+K) Q log^A(T).                         (16.4)

In particular, throughout `Q/R<=K<=R`, geometric summation yields

    D_K << RQ log^A(T).

This is the required diagonal-size bound; no cancellation conjecture for
`M_R` is used.

Here is the correct interface with the actual balanced mixed prime term.
Mellin separation of `W(qc/Z)` reduces it, up to harmless logarithmic
factors, to

    S_Q=sum_(r~R) C_r sum_(c~C) Lambda(c)F(a_r c/r),
    C=TR/Q,

with `O(1)` reduced source numerators `(a_r,r)=1`. For each reduced residue `h mod r`,
split the prime progression into its principal part and error:

    P_(r,h)=sum_(c~C,c=h mod r) Lambda(c)w_c,
    E_(r,h)=P_(r,h)-[C I_c/phi(r)]1_((h,r)=1).          (16.5)

The principal pairing is exactly

    [C I_c/phi(r)] sum_((h,r)=1)F(a_rh/r)
      =[C I_c/phi(r)]sum_(q~Q)M_R(q)w_q c_r(q).

After restoring `C=Z/Q` and the smooth `1/q` weight, this is the Section 14
Ramanujan principal coefficient and combines with Type I as `P_r-D_r`.
For `r~R`, distinct reduced source rationals are spaced by at least
`1/(rs)>>1/R^2`, whereas each smooth packet has width `1/Z` and
`Z/R^2=T/R` tends to infinity. Schwartz almost-orthogonality and (14.1)
therefore give

    ||principal packets||^2
       << Z sum_(r~R,a=O(1))|P_r-D_r|^2
       << T(loglog T)^4=o(T log T).                    (16.6)

For the error, character orthogonality and the multiplicative large sieve
give the unconditional dyadic variance bound

    sum_(r~R)sum_((h,r)=1)|E_(r,h)|^2
       << C(C/R+R)log^A(T) << CR log^A(T),              (16.7)

because `R^2>C` in the balanced block. Also
`sum_(r~R)sum_(h,r)=1 |F(h/r)|^2 << R D_(K~R)` and
`|C_r|<<log^A(T)/R`. A final Cauchy inequality therefore yields

    |S_(Q,error)| << log^A(T)sqrt(C D_(K~R))
                  << log^A(T)sqrt(C R Q).              (16.8)

At `eta=.49`, `Q=C=T^.745`, this is `T^.99+o(1)`, a genuine power saving
from the previous `T^1.1175+o(1)` bound. Ordinary primes have full reduced
denominator because `c>V>2R`; prime powers whose base divides `r` have an
elementary negligible total weight. Thus the balanced `r~R` mixed block is
closed after its principal term is combined as in Section 14. This argument
does not yet cover all boundary/complementary dyadic blocks, and it does not
control the Type-II square (16.1), which contains two independently varying
prime factors.

For completeness, small Fourier denominators have the exact Poisson form

    F(b/k)=Q hat_w(0) A_k
       +O_A(Q log R (Rk/Q)^A),
    A_k=sum_(d<R,k|d) mu(d)/d,                         (16.9)

when `(b,k)=1` and `k<Q/R`. The centered part is rapidly small when
`Rk/Q` is power-small (or sufficiently log-small after choosing `A`). The raw
principal term contains truncated Möbius sums and has no known fixed-power
bound. It is **not** the Section 14 coefficient: `k` here is the dual
denominator created by the q-collision norm, whereas Section 14 uses
`r/(r,q)` and a `1/q` weight. Summing this new rank-one direction over all
reduced numerators converts it to an ordinary PNT remainder plus the finitely
many prime powers whose bases divide `k`, but q-dependent lengths and outer
weights must still be restored. This issue does not occur in the interior
balanced full-denominator block above; it remains a separate
boundary/complementary-block task.

### The exact two-sided variance missing even from the packet projection

The same two large sieves do not close even the part of the Type-II error
seen by the `r~R` Type-I packet neighborhoods. After subtracting the
prime-progression principal term, put

    A_r=sum_((x,r)=1)|E_(r,x)|^2,
    H_r=sum_((x,r)=1)|F_r(x)|^2.

The error packet at a reduced `a/r` is

    R_(r,a)=sum_((x,r)=1) E_(r,x)F_r(ax),
    |R_(r,a)|^2<=A_r H_r.                              (16.10)

The multiplicative and additive large sieves, together with their elementary
pointwise counterparts, give

    sum_(r~R) A_r << C R log^A T,
    max_(r~R) A_r << (C^2/R)log^A T,
    sum_(r~R) H_r << R^2 Q log^A T,
    max_(r~R) H_r << Q^2 log^A T.                      (16.11)

Combining (16.10)--(16.11) in both directions and using the Type-I packet
width `1/Z` gives only

    B_(packet-projected error) << R min(C,Q)log^A T.   (16.12)

At balance `Q=C=T^((1+eta)/2)`, the exponent is `(1+3eta)/2`, namely
`1.235` at `eta=.49`. These four variance facts alone permit both energies
to concentrate on the same exceptional moduli, so reordering their Cauchy
inequalities cannot improve (16.12).

The precise missing decorrelation estimate is

    sum_(r~R) A_r H_r << C R^2 Q log^A T.              (16.13)

It would imply a packet-projected bound
`<<R^2 log^A T=T^(.98+o(1))`.
The proved bound exceeds (16.13) by `C/R=T^.255`; reaching the target
`T log T` needs a `T^(.235-o(1))` saving. In character coordinates this is
a mixed fourth moment coupling

    |sum_q M_R(q)chi(q)|^2 |sum_c Lambda(c)chi(c)|^2

over the same moduli. Separate character large sieves control its two
factors but not their covariance.

This calculation does **not** localize the full positive Type-II square.
The `r~R`, `a=O(1)` neighborhoods have total measure `R/Z=1/T`, whereas
the band has measure `1/R`; the remaining Type-II error is not supported on
those packets. Thus (16.13) is already necessary to control this projection,
but the full square (16.1) and its complementary minor-arc mass remain a
strictly larger open problem.


## 17. Conductor-stratified estimate for the mixed block

The balanced calculation extends to most nonprincipal mixed blocks, but only
after characters are stratified by conductor. Write

    r=gk~P,  q=gh~Q,  k~K,  g~P/K,
    a~P/R,  h~QK/P,  c~C=TR/Q,

and let a character modulo `k` be induced from a primitive conductor `f~F`,
with `k=f l`. Its Gauss coefficient is zero unless `l` is squarefree and
coprime to `f`; otherwise its size divided by `phi(k)` is
`<<log^B(T)sqrt(F)/K`.

Multiply the source-numerator and h-polynomials before applying the primitive
character large sieve. Their product has length

    N=(P/R)(QK/P)=QK/R

and averaged coefficient energy `<<N log^B T`. Cauchy between this product
and the prime character polynomial gives the audited conductor-shell bound

    |S_F(P,Q,K)|
      << [log^B(T)/(K sqrt(F))]
          sqrt(N C(F^2+N)(F^2+C)).                    (17.1)

Using `NC=TK` and
`sqrt((F^2+N)(F^2+C))<=F^2+F sqrt(N)+F sqrt(C)+sqrt(NC)`, this implies

    |S_F| << log^B(T) {
       T/sqrt(F) + Q sqrt(CF)/R
       + C sqrt(QF/(RK)) + sqrt(T)F^(3/2)/sqrt(K)}.    (17.2)

At `eta=.49`, if `Q=T^t`, `K=T^kappa`, and `F=T^phi`, a fixed-power
conductor shell is controlled whenever

    phi < min(1.49-t, t+kappa-.49, (1+kappa)/3)

with a fixed margin. In particular every **nonprincipal** conductor in a
whole reduced-modulus block is `o(T log T)` throughout

    Q>=R T^epsilon,       K<=T^(1/2-epsilon).          (17.3)

Conductors between one and a sufficiently large log power are removed by
Siegel--Walfisz; conductors above that log power gain through `T/sqrt(F)` in
(17.2). Nonunit terms are prime powers `p^j` with `p|k` and contribute
`<<QK/R log^B T`, also power-saving in (17.3).

The conductor `f=1` is exactly the induced principal-character/Ramanujan
term. Its signed dyadic `Q,K` pieces must first be recombined, after which
Section 14 supplies coefficient cancellation. They must not be bounded
absolutely shell by shell, and the large-source-denominator packet norm is
not supplied by (17.1). Thus (17.3) closes the nonprincipal mixed block,
not the positive Type-II square or the global principal packet synthesis.
The remaining mixed boundaries are `Q~R`, `K~sqrt(T)`, and high conductors
when `K>sqrt(T)`.
