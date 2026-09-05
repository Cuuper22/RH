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

### A proved logarithmic improvement for r comparable to R

Take fixed 0<c<C and cR<=r<=CR, and fixed eta<1/2. Then

    |A_r|+|L_r|=O_{c,C}(1/R),
    |L_infty(r)-L_V(r)|=O_{c,C}(log^2 R/V)=o(1/R),
    A_r(log V-gamma-H_V)=o(1/R).

For the tail bound, use V/r tending to infinity by a fixed power, sum the prime-power tails geometrically, and use `|A_s|<=(1+log(R/s))/s`. The last estimate uses the classical consequence of the prime number theorem `H_V=log V-gamma+o(1)`.

Thus, uniformly for v in [1,2],

    P_r(v)-D_r(v)
       = mu(r)/phi(r)-L_r-E_r(R^2v)+o(1/R)
       = O_{c,C}((loglog R)^2/R).

The separate primary coefficients can have size log R/R. Their leading log R therefore cancels, with an explicit quantitative remainder, in the actual eta=.49 range. This statement does not assert orthogonality of all rational packets or an upper bound for the full bandpass energy.

For a bounded check, R=32, V=64, v=1.3 gave the following coefficients; the exact identity agreed to 2.1e-16:

| r | Type I primary | Type II principal | Combined | mu(r)/phi(r)-L_r |
|---:|---:|---:|---:|---:|
| 19 | -.224889 | .198614 | -.026275 | -.028119 |
| 29 | -.145086 | .111877 | -.033209 | -.032320 |
| 31 | -.135419 | .102994 | -.032424 | -.032309 |
| 41 | .005682 | -.031742 | -.026060 | -.025000 |

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
                   + T^((1+eta)/2)(log T)^C ),          (1)

for a fixed C depending on B and the profiles. In particular it is
o(T log T) for every fixed0<eta<1. At eta=.49 the second power is T^.745.
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

    E_(k,b)(Y;w_q) << Y ell^(-A)+sqrt(Y) ell^2,
                         uniformly k<=K.                (4)

The factor at most phi(k) from additive Fourier expansion is absorbed by
choosing the Siegel–Walfisz logarithmic saving larger. The second term
retains ALL higher prime powers by their elementary total-weight bound;
this also covers powers whose base divides k. The cutoff c>V is retained
by partial summation with its endpoint. Thus (4) has no missing
non-coprime contribution.

Finally |M_R(q)|<=tau(q), and the elementary divisor estimates give

    sum_(q<=2R^2) tau(q)^2/q << ell^4,
    sum_(q<=2R^2) tau(q)^2/sqrt(q) << R ell^3.

Combining these with (3)–(4) proves a bound

    K T ell^(6-A)+K sqrt(Z) ell^7.

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
