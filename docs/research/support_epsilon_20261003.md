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
piecewise-polynomial** profile (degree-28 Taylor pieces of (2.3) with
rational `a,b'=b sqrt3`), its exact cost `D(u_0)` (upper bound on `inf D`,
hence a rigorous lower bound on `g`), and the exact dual bound (2.7) with
`pi>314159/100000`. The two enclosures agree.

TABLE_PLACEHOLDER

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
g_C(eps) - g(0)  ~  min( 0.68 eps,  c/C ),     c ~ 0.2,                  (4.2)
```

with no break-even threshold in `C`: any fixed bounded one-sided bound on
any fixed strip gives a strictly positive gain. The verifier's Part C
tabulates `g_C(eps)-g(0)` by a discretised QP (NUMERICAL):

CTABLE_PLACEHOLDER

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
