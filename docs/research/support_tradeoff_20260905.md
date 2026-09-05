# Exact one-sided support/profile tradeoff

Date: 2026-09-05. Ordinary variational calculation with exact rational
verification. This constrains the present one-sided arithmetic route; it is
not a new zero-percentage theorem.

Let the profile support width be `s=1+eta`. For an even nonnegative mass-one
profile on an interval of width `s`, write

$$
 D_{\rm diag}(u)=\int u^2+\iint |x-y|u(x)u(y)\,dx\,dy.
$$

## Sharp threshold

For `s<pi/sqrt(2)`, the unique minimizer is

$$
 u_s(x)=\frac{\cos(\sqrt2x)}{\sqrt2\sin(s/\sqrt2)},
 \qquad |x|\le s/2,
$$

and

$$
 D_s^*=\frac s2+\frac1{\sqrt2}\cot\frac{s}{\sqrt2}.
$$

Indeed, if `h` has zero mass and
`H(x)=int_(-s/2)^x h`, then

$$
 \iint |x-y|h(x)h(y)\,dx\,dy=-2\int H^2.
$$

The Dirichlet Poincare inequality makes the second variation strictly
positive for `s<pi/sqrt(2)`, while the Euler equation is `u''+2u=0`.

The equation `D_s^*=23/20` has the unique root

$$
 s_0=1.47342692508524676589\ldots,
 \qquad \eta_0=s_0-1=0.47342692508524676589\ldots .
$$

Exact alternating-series arithmetic gives

$$
 0.47342692508524<\eta_0<0.47342692508525.
$$

Thus `eta_0` is the sharp infimum; the desired inequality is strict, so it
is not attained.

## A rational certificate with margin

Take

$$
 s=\frac{147343}{100000},\qquad
 \eta=\frac{47343}{100000},
$$

and normalize on `[-s/2,s/2]` the positive rational polynomial

$$
 p(x)=\sum_{j=0}^{6}\frac{(-1)^j2^jx^{2j}}{(2j)!}.
$$

Exact integration gives

$$
 D_{\rm diag}(p/\!\int p)
 =1.149999474789463633\ldots<1.15,
$$

with margin `5.25210536...*10^-7`. Smooth strict-support approximations
preserve this margin.

The corresponding balanced prime-distribution exponent is

$$
 \frac{2\eta}{1+\eta}=\frac{94686}{147343}
 =0.6426229953238362\ldots .
$$

At the sharp infimum it tends to `0.6426201625952453...`.

Profile optimization alone cannot reach the current `5/8` distribution
range. The inequality `2eta/(1+eta)<=5/8` is equivalent to `eta<=5/11`,
or `s<=16/11`, whereas the exact variational lower bound gives

$$
 D_{16/11}^*>1.1533254428473587>1.15.
$$

The exact verifier
[diag_support_tradeoff.py](../../verify/diag_support_tradeoff.py) checks the
polynomial positivity and integral, the root bracket, and the `5/8`
obstruction.
