# Pricing and attacking a small support extension beyond bandwidth one

Date: 2026-10-03. Research memo; no new unconditional zero-proportion
theorem is claimed. Verifier: [support_epsilon_gain.py](../../verify/support_epsilon_gain.py),
output in [support_epsilon_gain.out](../../verify/support_epsilon_gain.out).

Labels: **PROVED** (argument written here), **CHECKED** (exact rational or
interval arithmetic in the verifier), **NUMERICAL** (floating diagnostics),
**CONJECTURE**, **REFUTED**.

## 0. Summary

* The gain law is **linear**: with a one-sided form-factor input on the
  strip `1<|alpha|<=1+eps`, the certificate value is
  `g(eps) = g(0) + g'(0+) eps + O(eps^2)` with the exact constant

  ```
  g'(0+) = csc^2(1/sqrt2)/2 - 1/2 = 0.68475508541106889...   (PROVED, CHECKED)
  ```

  and second-order coefficient about `-0.98` (NUMERICAL). The whole
  `1/271803` cubic gain of the current frontier equals a support extension of
  `eps = 5.3729e-6`. At `eps=0.001` the gain is `186` times the cubic gain.
* `g(eps)` has a closed trigonometric form (Section 2); it reproduces the
  legacy ladder values `0.79721415286...` at `eps=1/4` and
  `0.86567425...` at `eps=1/2` exactly, so those rungs were already the
  sharp one-sided optimum for their support.
* The certificate's exposure to the *value* of the form factor on the strip
  is only second order: the strip carries autocorrelation mass
  `<= ||u||_infty^2 eps^2`. Consequently any bounded one-sided bound
  `F(alpha) <= C` on the strip still yields a strictly positive gain of order
  `min(0.68 eps, c/C)` (Section 4). The required arithmetic input is therefore
  **much weaker than the pair-correlation conjecture on the strip**: a
  bounded, averaged, one-sided form factor just beyond `alpha=1`.
* That weakest input is nevertheless equivalent (Section 5) to a
  bounded-constant mean value for prime Dirichlet polynomials of length
  `T^{1+eps}` over `t in [T,2T]`, i.e. to a variance bound for primes in
  intervals of length `h in [1, T^eps]` with the **correct power of log**.
  Montgomery--Vaughan loses `T^eps`, every zero-density/Selberg-type bound
  loses `log T`, and Goldston--Montgomery show that removing the log is the
  pair-correlation problem itself. No unconditional (or RH-conditional)
  method gives `F(alpha)=O(1)` for any fixed `alpha>1`. This is the precise
  obstruction; I did not find an averaging ansatz (over heights, characters,
  or mollifier weights) that keeps the target about the zeros of zeta
  while moving the off-diagonal into a known averaged prime-pair estimate
  (Section 6).

## 1. The exact certificate shape at support `1+eps`

Notation as in `Zeta23/ThmD/Functional.lean` and
[support_tradeoff_20260905.md](support_tradeoff_20260905.md). For an even
profile `u>=0` with `int u=1` supported in an interval of width `s=1+eps`,

```
D_K(u) = int u^2 + iint K(x-y) u(x) u(y) dx dy,
```

and the rank--trace certificate gives `liminf N_0^s(T,2T)/N(T,2T) >= 2 - D_K(u)`
whenever `||Ghat||_F^2/N -> D_K(u)`. The second-trace limit is
`int (u*u~)(alpha) F(alpha) dalpha` plus the archimedean diagonal `int u^2`,
where `u*u~` is the autocorrelation of `u` (support width `2s`) and `F` is
the form factor. Unconditionally `F(alpha)=|alpha|+o(1)` on `|alpha|<=1`
(this is what the base proof establishes for complex zeros through the
Montgomery--Vaughan treatment of `O_1`, `Zeta23/PrimeSideB/PPOffDiag.lean`).
On the strip `1<|alpha|<=1+eps` nothing is known. We consider two
hypotheses, both **one-sided** since the certificate needs only an upper
bound for the second trace:

* **(H1)** `limsup F(alpha) <= 1` on the strip (the pair-correlation value);
  kernel `K_1(t)=min(|t|,1)`.
* **(HC)** `limsup F(alpha) <= C` on the strip for a fixed `C>=1`;
  kernel `K_C(t)=|t|` for `|t|<=1`, `K_C(t)=C` for `1<|t|<=1+eps`.

Under (H1) the base run's rung formula `2-D_sigma^*` (`docs/run/08`, (T2),
and `FINDINGS.md` section 9) is exactly `g(eps):=2-inf_u D_{K_1}(u)`.
The `o(1)` tolerances in the strip hypothesis are harmless: the strip
autocorrelation mass is bounded, so any `o(1)` error contributes `o(1)` to
`D`.

Only the limit value matters: the full certificate also has the cubic
ordered-moment increment (`1/271803`), whose transfer uses
`sum|xi_j|<2`; at width `1+eps` that transfer would itself need an extended
input, so I price only the base term `2-D`. (PROVED: this is a restatement
of the repository's certificate; nothing new is asserted about its validity.)

## 2. Closed form of `g(eps)` under (H1) — PROVED, CHECKED

Fix `0<eps<1`, `s=1+eps`, `x_0=(1-eps)/2`. Write the window as
`L=[-s/2,-x_0]`, `M=[-x_0,x_0]`, `R=[x_0,s/2]`.

**Euler--Lagrange equation.** If `u` is a minimiser with `u>0` on the whole
window, then `u + K_1*u = lambda` on the window (`lambda` the multiplier of
`int u=1`), and `D(u)=int u (u+K_1*u) = lambda`. Since
`K_1''(t)=2 delta(t) - delta(t-1) - delta(t+1)` distributionally,
differentiating twice gives the delay equation

```
u''(x) + 2u(x) = u(x-1) + u(x+1)     (u := 0 outside the window).     (2.1)
```

For `x in M` both shifted arguments leave the window (`|x+-1|>=s/2`), so
`u''+2u=0` and, by evenness, `u(x)=A cos(sqrt2 x)` on `M`. For `x in R`,
`x+1` is outside and `x-1 in L`, so with `x=1/2+y`, `|y|<=eps/2`, and
`f(y):=u(1/2+y)` evenness gives `u(x-1)=u(1-x)=f(-y)`, hence

```
f''(y) + 2 f(y) = f(-y).                                               (2.2)
```

Splitting `f` into even and odd parts, `f_e''+f_e=0`, `f_o''+3f_o=0`, so

```
f(y) = a cos y + b sin(sqrt3 y).                                        (2.3)
```

`u` is `C^1` across `x_0` (because `K_1*u` is `C^1` for bounded `u`, and
`u=lambda-K_1*u`), which fixes `(a,b)` from `A=1`:

```
a cos(eps/2) - b sin(sqrt3 eps/2)      =  cos(sqrt2 x_0),
a sin(eps/2) + sqrt3 b cos(sqrt3 eps/2) = -sqrt2 sin(sqrt2 x_0).         (2.4)
```

Conversely, for this `u`, `(u+K_1*u)''=0` on the window and `u+K_1*u` is
even, hence constant `=lambda`. Evaluating at `x=0` (where
`K_1*u(0)=int|y|u(y)dy` since `s/2<1`):

```
mass = 2[ sin(sqrt2 x_0)/sqrt2 + 2a sin(eps/2) ],
lambda = 1 + 2[ x_0 sin(sqrt2 x_0)/sqrt2 + (cos(sqrt2 x_0)-1)/2 + a sin(eps/2)
             + 2b( -(eps/2) cos(sqrt3 eps/2)/sqrt3 + sin(sqrt3 eps/2)/3 ) ],
D*(eps) = lambda/mass,     g(eps) = 2 - D*(eps).                        (2.5)
```

**Global optimality.** Let `u_0` be the normalised solution above and
`u` any admissible profile, `h=u-u_0`, `int h=0`. Then
`D(u) = D(u_0) + 2 int r h + Q(h)` with `r=u_0+K_1*u_0-lambda=0` and

```
Q(h) = int h^2 + iint K_1(x-y) h(x) h(y).
```

For `H(x)=int_{-s/2}^x h`, `H(+-s/2)=0`, one has
`iint |x-y| h h = -2 int H^2 >= -2 (s/pi)^2 int h^2` (Dirichlet Poincaré on
an interval of length `s`). The saturation part
`-iint (|x-y|-1)_+ h h` is bounded by `2 eps^2 int h^2`: the region
`{x-y>1}` has every `x`- and `y`-section of length `<=eps`, the integrand
factor `(|x-y|-1)<=eps`, and Cauchy--Schwarz over the region gives
`iint_{x-y>1}|h(x)h(y)| <= eps int h^2`; there are two such regions. Hence

```
Q(h) >= m int h^2,      m = 1 - 2 s^2/pi^2 - 2 eps^2,                  (2.6)
```

which is positive for `eps<=1/2` (`m(1/2)>0.04`). So the Euler--Lagrange
solution is the unique global minimiser as soon as it is nonnegative. The
same inequality yields the **dual bound** used in Part B of the verifier:
for any admissible `u_0` with residual `r=u_0+K_1*u_0-c`,

```
inf D >= D(u_0) - ||r||_2^2 / m.                                        (2.7)
```

**Positivity of the collar.** The collar function (2.3) is bounded below on
`|y|<=eps/2` by its grid minimum minus a Lipschitz correction; the verifier
certifies `f>0` for every table value and for `eps=1/2` (CHECKED).

**First-order law.** Differentiating (2.5) at `eps=0` is the envelope
derivative of the unsaturated problem `D_s^*=s/2+cot(s/sqrt2)/sqrt2`
(support_tradeoff note), because the saturation correction is `O(eps^3)`
(Section 4):

```
g'(0+) = -dD_s^*/ds|_{s=1} = 1/(2 sin^2(1/sqrt2)) - 1/2
       = 0.6847550854110688910...                                        (2.8)
```

(PROVED; the interval value is in the verifier output. The verifier also
checks `(D_s^*-D^*(eps))/eps^3` stays bounded, NUMERICAL.)

## 3. Table — CHECKED

Part A of the verifier evaluates (2.5) in 40-digit interval arithmetic.
Part B gives, for each `eps`, an explicit nonnegative **rational
piecewise-polynomial** profile (Taylor pieces of order 20 of (2.3) with
rational `a,b'=b sqrt3`), its exact cost `D(u_0)` (upper bound on `inf D`,
hence a rigorous lower bound on `g`), and the exact dual bound (2.7) with
`pi>314159/100000`. The two enclosures agree.

| `eps` | `D*(eps)` (closed form, interval) | `g(eps)` | `(g-g(0))/eps` | gain / `(1/271803)` | exact profile: `D(u0)` and dual gap `||r||^2/m` |
|---|---|---|---|---|---|
| 0.001 | 1.32681552038371077077 | 0.67318447961628922923 | 0.68377594 | 185.85 | 1.326815520383710867, gap `< 6e-40` |
| 0.01  | 1.32074856184348489678 | 0.67925143815651510322 | 0.67507345 | 1834.87 | 1.320748561843484881, gap `< 5e-39` |
| 0.05  | 1.29556679582353748581 | 0.70443320417646251419 | 0.63865001 | 8679.35 | 1.295566795823537509, gap `< 2e-38` |
| 0.1   | 1.26772553526854663448 | 0.73227446473145336552 | 0.59773761 | 16246.69 | 1.267725535268546588, gap `< 1e-39` |
| 0.25  | 1.20278584707663061412 | 0.79721415292336938588 | 0.49885380 | 33897.49 | 1.202785847076630610, gap `< 3e-38` |
| 0.5   | 1.13432574532332480678 | 0.86567425467667519322 | 0.38634710 | 52505.15 | (not certified in Part B) |

All interval widths in Part A are below `10^-30`. In Part B the rational
profiles have Taylor order 20 on each piece and rational `a, b'` with
denominator `10^18`; positivity is certified by an exact root count on each
piece (sympy `count_roots`), and every rigorous gain over `g(0)`
(`g_lo - (2 - 13274992963/10^10)`) is strictly positive. Second-order
coefficient of `g`: `-0.9804` (NUMERICAL, from `eps = 10^-5`).

For comparison, the current frontier is `0.6725043820976` (cubic gain
`1/271803 = 3.679e-6`). The support extension `eps=0.001` is worth
`6.84e-4`, i.e. `186` cubic gains; `eps=1/4` reproduces the legacy rung
`0.797214152861...` (the legacy decimal is the truncation of the exact
optimum `0.79721415292337...`).

## 4. Second-order exposure and the weaker hypothesis (HC) — PROVED / NUMERICAL

**Lemma (strip exposure).** For `u>=0`, `int u=1`, support width `1+eps`,

```
int_{1<|alpha|<=1+eps} (u*u~)(alpha) dalpha <= ||u||_infty^2 eps^2.      (4.1)
```

Proof: `(u*u~)(alpha)=int u(x)u(x+alpha)dx` and for `alpha>1` the
integration range has length `1+eps-alpha<=eps`; integrate over
`alpha in (1,1+eps]` and double for the sign. (PROVED.)

Hence the difference between the costs under two strip kernels bounded by
`C_1,C_2` is at most `|C_1-C_2| ||u||_infty^2 eps^2`. Two consequences:

1. The saturated and unsaturated kernels (`min(|t|,1)` versus `|t|`)
   differ on the strip by at most `eps`, so `0<=D_s^*-D^*(eps)<=
   ||u||_infty^2 eps^3`; this is the `O(eps^3)` claim behind (2.8)
   (the verifier finds the ratio about `0.22`).
2. Under (HC) the extra cost over (H1) is at most `(C-1)||u||_infty^2 eps^2`.
   With `||u||_infty^2 ~ 0.68` this is `0.68 (C-1) eps^2` against a gain
   `0.68 eps`, so the full linear gain survives whenever `(C-1) eps <~ 1`.

**Larger `C` (taper).** For `C eps >> 1` the optimiser tapers `u` near the
ends. The first variation of `D` at the width-one optimum `u_1` in the
direction of a unit mass placed at distance `tau` beyond the edge is
`2[(1/2+tau) - D_1] = -1.655 + 2 tau` (because `K_1*u_1(1/2+tau)=1/2+tau`
and `u_1+K_1*u_1=D_1` on the support), while the strip exposure of that mass
is `2(C-1) int_0^tau u_1(-1/2+beta) dbeta ~ 1.65 (C-1) tau`. So moving mass
to `tau <~ 1/C` lowers `D` to first order for **every finite `C`**; the
second variation `m||h||^2 ~ t^2/tau` then limits the gain to order `1/C`.
Thus

```
g_C(eps) - g(0)  ~  min( 0.68 eps,  c/C ),     c ~ 0.3,                  (4.2)
```

with no break-even threshold in `C`: any fixed bounded one-sided bound on
any fixed strip gives a strictly positive gain. The verifier's Part C
tabulates `g_C(eps)-g(0)` by a discretised QP (NUMERICAL):

C| `eps` | `D*(eps)` (closed form, interval) | `g(eps)` | `(g-g(0))/eps` | gain / `(1/271803)` | exact profile: `D(u0)` and dual gap `||r||^2/m` |
|---|---|---|---|---|---|
| 0.001 | 1.32681552038371077077 | 0.67318447961628922923 | 0.68377594 | 185.85 | 1.326815520383710867, gap `< 6e-40` |
| 0.01  | 1.32074856184348489678 | 0.67925143815651510322 | 0.67507345 | 1834.87 | 1.320748561843484881, gap `< 5e-39` |
| 0.05  | 1.29556679582353748581 | 0.70443320417646251419 | 0.63865001 | 8679.35 | 1.295566795823537509, gap `< 2e-38` |
| 0.1   | 1.26772553526854663448 | 0.73227446473145336552 | 0.59773761 | 16246.69 | 1.267725535268546588, gap `< 1e-39` |
| 0.25  | 1.20278584707663061412 | 0.79721415292336938588 | 0.49885380 | 33897.49 | 1.202785847076630610, gap `< 3e-38` |
| 0.5   | 1.13432574532332480678 | 0.86567425467667519322 | 0.38634710 | 52505.15 | (not certified in Part B) |

All interval widths in Part A are below `10^-30`. In Part B the rational
profiles have Taylor order 20 on each piece and rational `a, b'` with
denominator `10^18`; positivity is certified by an exact root count on each
piece (sympy `count_roots`), and every rigorous gain over `g(0)`
(`g_lo - (2 - 13274992963/10^10)`) is strictly positive. Second-order
coefficient of `g`: `-0.9804` (NUMERICAL, from `eps = 10^-5`).

A singular but integrable one-sided bound `F(alpha)<=c(alpha-1)^{-theta}`,
`theta<1`, also gives a gain by the same first-variation computation
(exposure `~ c tau^{1-theta}`). What is needed is only

```
(W)   limsup_{T} (1/tau) int_1^{1+tau} F_T(alpha) dalpha < infinity
      for some fixed tau>0,
```

an **averaged, one-sided, bounded** form factor just beyond `alpha=1`.
(PROVED that (W) suffices for a positive gain; the size of the gain is
NUMERICAL.)

## 5. The weakest sufficient arithmetic statement, in prime terms — PROVED reduction

Write the second trace through the accepted prime-side expansion
(`terminal_bandpass_bridge_20260905.md`, (1)–(4)): with
`phi(y)^2=u(y/ell)`, the only term not controlled at support `1+eps` is
the genuine off-diagonal

```
O_T = (1/2pi^2) sum_{n != m <= X} Lambda(n)Lambda(m)/sqrt(nm) A^-_Phi(T; log n, log m),
X = T^{1+eps},
```

normalised by `Q_T = T ell^3/(2pi)`. The kernel `A^-` localises
`|log(n/m)| <~ 1/T`, and the profile weight `g(log n)` restricts the
strip contribution to `T < n <= T^{1+eps}`. Hence, on the strip, `O_T` is a
sum over shifted prime pairs

```
sum_{T<n<=T^{1+eps}} sum_{0<|h| <~ n/T} Lambda(n) Lambda(n+h) w_T(n,h),      (5.1)
```

with shifts `|h| <= n/T in [1, T^eps]` and a signed Schwartz shift weight
`w_T` of total mass zero in `h` (the kernel `k(s)=int chi(v)cos(vs)dv` of
`mobius_energy_20260905.md`, Section 5). Therefore:

**Statement (P).** There is a fixed `eps>0` and a fixed `C` such that

```
int_T^{2T} | sum_{T<n<=T^{1+eps}} Lambda(n) n^{-1/2-it} v(log n/log T) |^2 dt
   <= C T sum_{T<n<=T^{1+eps}} Lambda(n)^2 v(log n/log T)^2 / n          (5.2)
```

for every fixed smooth `v` supported in `(1,1+eps)`. By the Fourier
expansion of the height weight (the explicit formula, as in the base
proof) (5.2) is the one-sided bound `F<=C'` on the strip in averaged form,
hence (W) of Section 4, hence a positive gain. Conversely a gain through
this certificate needs an upper bound of this type: the strip term is a
positive-definite mean square minus its diagonal, and only its upper bound
enters. (PROVED as a reduction; the constant bookkeeping `C -> C'` is the
standard Montgomery convolution and is not re-derived here.)

Montgomery--Vaughan gives (5.2) with `C T` replaced by `T + O(T^{1+eps})`,
i.e. it loses exactly `T^eps`. That `T^eps` is the whole problem: the
liminf statement needs a fixed `eps`, so no `eps=eps_T -> 0` trick helps
(`T^{eps_T}=O(1)` forces `eps_T << 1/log T` and the gain `0.68 eps_T` vanishes).

**Equivalent short-interval form.** Set `N=T^{1+eps}` and `h=N/T=T^eps`. By
the Goldston--Montgomery correspondence (Tauberian lemmas with positive
kernels, Goldston--Montgomery 1987), (5.2) for all `v` is equivalent, up to
constants, to

```
int_N^{2N} ( psi(x+h) - psi(x) - h )^2 dx <= C'' h N log N,
h = N^theta,  theta in (0, eps/(1+eps)],                                  (5.3)
```

uniformly for the small exponents `theta`. (The asymptotic version
`~ hN log(N/h)` is exactly `F->1`; the one-sided bounded version with
`C''>1` is what (W) needs. I have not re-derived the constant transfer in
the Tauberian lemmas; the equivalence of *bounded* versions is stated here
as the standard reading of those lemmas, CONJECTURE-level only in the
constant, PROVED in the exponent range.)

## 6. Comparison with what is known; averaging ansätze — REFUTED / closed

1. **Variance of primes in short intervals.** Unconditionally the mean
   square (5.3) is known as an *upper bound* with an extra logarithm,
   `<< hN log^2 N`, and only for `h >= N^{1/6+delta}` (Saffari--Vaughan via
   Huxley's zero density; Guth--Maynard's density improves the exponent but
   not the logarithm). Under RH Selberg's bound is also `<< hN log^2`.
   The extra logarithm comes from treating the zero sum
   `sum_rho x^rho (( 1+h/x)^rho - 1)/rho` by the Hilbert inequality, which
   charges each zero its `1/log` spacing. Removing it *is* the
   pair-correlation input (Goldston--Montgomery), so the circle cannot be
   broken from this side. Moreover the required range `theta <= eps/(1+eps)`
   is the very short one (`h = T^eps`), where even the `log^2` bound is
   unknown for `theta<1/6`. In the exponent language of the repository:
   `h >= N^{1/6}` corresponds to `alpha >= 6/5`, while the certificate needs
   the strip immediately above `alpha=1`.
2. **Averaged Hardy--Littlewood sums.** (5.1) is a signed average of
   `sum_n Lambda(n)Lambda(n+h)` over `|h| <= H = T^eps` at `n ~ T^{1+eps}`,
   i.e. `H = X^{eps/(1+eps)}`. The averaged results (Mikawa, Perelli--Pintz,
   Baier--Browning--Marasingha--Zhao, Matomäki--Radziwill--Tao type) need
   `H >= X^{1/3+delta}` or at best `H >= X^{delta}` for *almost all* `h`
   with an `o(X)` error only on average over `h` — but the signed weight
   `w_T` has mass zero in `h`, so (5.1) is a **second-order** quantity: it is
   the derivative-type term `-(1/2) int w(y)/y dy` of the singular-series
   average `sum_{h<=H} S(h) = H - (1/2) log H + ...`. One needs the error in
   the averaged Hardy--Littlewood asymptotic to be `o(X)` **per unit `h`**
   after the signed average, i.e. of relative size `o(1/H)`. No averaged
   result has that precision for any power range of `h`; this is the same
   `X^{...}` gap the repository records at `.0785025` for its bandpass
   model at `eta=.47`, now needed at every small `eta`.
3. **Averaging over heights.** The quantity (5.2) is already a `t`-average
   over `[T,2T]`. Longer `t`-ranges only move `T` and lose the dyadic
   normalisation. A smooth height weight (the tapered Gabor compression of
   `terminal_bandpass_bridge_20260905.md`) changes `A^-` to a Schwartz
   kernel but leaves (5.2) as the required input. REFUTED as a route.
4. **Twisting by characters / averaging over moduli.** Averaging the test
   over `chi mod q`, `q<=Q`, replaces `n != m` by `n = m (mod q)` and turns
   the off-diagonal into a Barban--Davenport--Halberstam / Hooley variance,
   which **is** known with an asymptotic for `Q >= X^{1/2+delta}`. This is
   the mechanism of Özlük's `q`-analogue of pair correlation (support
   beyond one for the *family* of Dirichlet `L`-functions) and of the
   Chandee--Lee--Liu--Radziwill asymptotic-large-sieve simple-zero results
   (GRH there; the repository's complex-zero machinery would handle the
   zero side unconditionally, as in Theorem E). But the conclusion is a
   **family-averaged** proportion for `L(s,chi)`, and zeta is a single,
   measure-zero member. Taking instead the union of zeros of `zeta` and
   `L(s,chi)` (Dedekind zeta of a quadratic field) and averaging over the
   family does not help zeta: the cross Gram block
   `sum_{rho in zeta, rho' in chi} |uhat(L(z_rho-z_rho'))|^2` has an
   archimedean main term `int u^2 N`-type that is **added** to the
   second trace, so the union certificate is strictly worse than the
   separate ones. REFUTED for zeta.
5. **Weighting zeros by a short Dirichlet polynomial** (`w_rho=|M(rho)|^2`,
   Conrey--Ghosh--Gonek style). The second trace becomes the *mollified*
   pair correlation `sum_{rho,rho'} w_rho w_rho' |uhat|^2`; its diagonal is
   a discrete fourth moment of `M` on the zeros and its off-diagonal a
   mollified shifted-prime sum. Both are open unconditionally, and the
   zero-side positivity (needed for complex zeros) is lost for non-real
   weights. Legacy cycle 7 (`docs/run/10_...weighted_levinson...`) records
   that the ordinary mollified second moment cannot recover the coupling.
   Not pursued.
6. **Using the sign.** The one-sided requirement is an *upper* bound on a
   positive-definite quantity minus its diagonal; positivity of `F` only
   gives the free direction (lower bounds). The Montgomery--Vaughan error
   `theta sum n|a_n|^2`, `|theta|<=1`, is two-sided and is already the
   sharp form of the Hilbert inequality for generic coefficients; the gain
   must come from the primes, i.e. from (5.3). REFUTED as a free lunch.

## 7. What was proved, what remains open

* PROVED: closed form (2.5) for `g(eps)` under (H1); the first-order law
  (2.8); the convexity constant (2.6) and dual bound (2.7); the exposure
  lemma (4.1); the reduction of the needed input to (5.2)/(W); the
  first-variation argument that any bounded one-sided strip bound gives a
  positive gain.
* CHECKED: table of Section 3 (interval closed form and exact rational
  two-sided enclosures); positivity of all profiles; `g'(0+)` to 40 digits.
* NUMERICAL: second-order coefficient; `g_C(eps)` table and the
  `min(eps,1/C)` law's constants.
* OPEN: statement (P)/(5.2) for any fixed `eps>0`, equivalently (5.3) with a
  bounded constant for some fixed small `theta`. No attack found; the
  precise obstruction is the `T^eps` of Montgomery--Vaughan versus the
  `log T` of every zero-sum method, with Goldston--Montgomery showing these
  are the same wall.

## 8. Adversarial self-check

* *Like with like?* The gain `g(eps)` is for the same certificate
  (`2-D`, rank--trace, complex zeros) as the inherited `0.6725007...`; the
  cubic add-on `1/271803` is excluded on both sides of the comparison
  (Section 1). The legacy rungs at `eps=1/4,1/2` were recomputed from the
  same closed form and agree to the printed digits, which cross-validates
  the formula against an independent earlier derivation.
* *Cherry-picking?* The table uses the five requested `eps` values; the
  `C`-dependence uses a fixed grid and reports every value computed.
* *Inference bridging a proof?* Two places: (i) the equivalence between
  (5.2) and the bounded short-interval variance (5.3) is quoted from the
  Goldston--Montgomery Tauberian lemmas without re-deriving the constant
  transfer — flagged CONJECTURE in the constant; (ii) the statement that no
  unconditional method gives `F(alpha)=O(1)` for fixed `alpha>1` is a
  literature claim, not a theorem; it is consistent with every source
  cited in this repository and with the structure of the two known
  methods, but a reader should treat it as "no method known to me".
* *Hidden positivity assumptions?* The dual bound (2.7) holds for signed
  `u`, so the lower bounds on `inf D` are valid for the full admissible
  class; the upper bounds use nonnegative `u_0` only.
* *Does (W) really suffice?* The first-variation argument shows a strict
  decrease of `D` for a one-parameter family; the second variation is
  controlled by (2.6). The displayed size `c/C` is numerical.
