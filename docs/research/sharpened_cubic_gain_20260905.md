# A sharper unconditional ordered cubic increment

Research derivation, 2026-09-05. This improves the finite operator part of
[the ordered-moment derivation](ordered_moment_20260905.md) and its exact scalar constants. It adds no
full fourth-moment premise for the actual zero operator.

## 1. Orthogonal comparison at distance squared at most the slack

Use the finite zero-side decomposition $G=P+B-C$, with $P,B,C\ge0$,
$BC=0$, $\operatorname{tr}P\le S$, $\operatorname{rank}P\le S$,
$\operatorname{rank}B\le b$, and $S+2b\le N$.
Assume first $\operatorname{tr}G=N$ and set

$$
 \Delta=\operatorname{tr}G^2-2N+S.
$$

Let $F$ be the support projection of $B$, $J=I-F$, and let $E$ be the
positive spectral projection of $J(P-C)J$ on $JH$.
Then $EF=0$. Set $H=E+2F$, $X=G-H$, and $d^2=\|X\|_2^2$.
Write

$$
 e=\operatorname{rank}E,\quad f=\operatorname{rank}F,\quad
 \tau=\operatorname{tr}(J(P-C)J)_+,\quad
 \nu=\operatorname{tr}(J(P-C)J)_-.
$$

Since $\tau\le\operatorname{tr}(JPJ)\le S$ and $e\le S$, the quantities

$$
 b_0=N-S-2f,\qquad k=S-e,\qquad h=S-\tau
$$

are nonnegative. Direct expansion gives the exact identity

$$
 \Delta-d^2=2b_0+k+2h+4\nu.                           \tag{1}
$$

In particular $d^2\le\Delta$, while

$$
 p(H)=0,\quad 0\le H\le2I,\quad
 \operatorname{tr}H\le N,\quad
 \operatorname{tr}H^3=e+8f\le4N-3S,                  \tag{2}
$$

where $p(t)=t^3-3t^2+2t$.
This improves the earlier nonorthogonal comparison with distance squared
$2\Delta$ and operator norm three.

The linear term in the cubic expansion is also controlled by the slack:

$$
 L=\operatorname{tr}(p'(H)X)
   =2\operatorname{tr}X-3\operatorname{tr}(EX)
   =2b_0-k+3h
   \ge d^2-\Delta.                                  \tag{3}
$$

Indeed the difference between the last two sides is
$4b_0+5h+4\nu\ge0$.

## 2. A fourth-energy bound for the comparison operator

Let $W$ be the continuous triangular restriction of $H$, and set
$K=(W-W^*)/i$, so $W=(H+iK)/2$.
All strictly triangular cyclic traces vanish, including
$\operatorname{tr}W^3=\operatorname{tr}W^4=0$.
Expansion of their real parts gives

$$
 \operatorname{tr}(HK^2)=\frac13\operatorname{tr}H^3,\qquad
 \|W^2\|_2^2=
 \frac{\operatorname{tr}(H^2K^2)+\operatorname{tr}(HKHK)}4.
$$

Hilbert--Schmidt Cauchy--Schwarz gives
$\operatorname{tr}(HKHK)\le\operatorname{tr}(H^2K^2)$.
Since $0\le H\le2I$, also $H^2\le2H$. Therefore

$$
 \boxed{\ \|W^2\|_2^2\le\frac13\operatorname{tr}H^3
                         \le\frac{4N-3S}{3}.\ }       \tag{4}
$$

This is finite comparison-operator algebra. It is not a fourth trace
estimate for $G$.

## 3. The sharper cubic inequality

Let $V$ be the triangular restriction of $G$ and $Z=V-W$.
Then $\|Z\|_2=d/\sqrt2$ and $\operatorname{tr}Z^2=0$.
Expanding $V=W+Z$, and using the vanishing triangular traces, gives

$$
 \operatorname{tr}p(G)
 =L+6\Re\operatorname{tr}[(V^2-W^2)Z^*]
       +6\Re\operatorname{tr}[(H-I)Z^2]-3d^2.
$$

The middle quadratic term is at least $-3d^2$, since
$\|H-I\|_{\rm op}\le1$ and $\|Z^2\|_1\le\|Z\|_2^2$.
Combining (3), (4), and Cauchy--Schwarz yields

$$
 -\operatorname{tr}p(G)
 \le6\Delta+3\sqrt{2\Delta}
                  \left(\|V^2\|_2+\sqrt{(4N-3S)/3}\right).          \tag{5}
$$

Write $\delta=\Delta/N$, $D_G=\operatorname{tr}G^2/N$,
$Q_G=\|V^2\|_2^2/N$, and
$\kappa=-\operatorname{tr}p(G)/N>0$.
Since $S/N=2-D_G+\delta$, the scalar form is

$$
 \boxed{\quad
 \kappa\le6\delta+
       3\sqrt{2\delta}
       \left(\sqrt{Q_G}+\sqrt{D_G-\frac23-\delta}\right).
       \quad}                                                       \tag{6}
$$

For $M=\operatorname{tr}G\ne N$, use the exact slack
$\Delta=\operatorname{tr}G^2-4M+2N+S$. Identity (1) is unchanged,
while the linear term in (3) gains $2(M-N)$. Hence the earlier
height-collar construction supplies the same asymptotic inequality with
$o(N)$ trace errors, followed by the existing collar and profile limits.

## 4. Exact cosine certificate

For the limiting optimal cosine, alternating Taylor series give

$$
 D_*<\frac{531}{400},\qquad
 \kappa_*>\frac{471}{40000}.
$$

A short positive polynomial envelope bounds its ordered fourth energy:

$$
 u_*(x)\le
 \frac{40320}{37043}\left(1-x^2+\frac{x^4}{6}\right)
 \quad (|x|\le1/2).
$$

The denominator comes from the lower alternating sum
$1-1/12+1/480-1/40320$ for $\sin(1/\sqrt2)/(1/\sqrt2)$.
All integrands in $Q(u)$ are nonnegative, so exact polynomial integration
on the interval, triangle, and three-simplex gives

$$
 Q(u_*)\le
 \frac{3154631940664954715840}{7906248876401653709399}
 <\left(\frac{63167}{100000}\right)^2.
$$

Also
$D_*-2/3<(81292/100000)^2$.
If $\delta\le\delta_0=1/272000$, (6) would imply

$$
 \frac{471}{40000}
 \le6\delta_0+\frac{433377}{100000}\sqrt{2\delta_0}.
$$

But the exact rational difference after squaring is positive:

$$
 \left(\frac{471}{40000}-6\delta_0\right)^2
 -18\delta_0\left(\frac{144459}{100000}\right)^2
 =\frac{737589807}{23120000000000000}>0.
$$

Thus the same analytic moment input now gives

$$
 \liminf\frac{N_0^s(T,2T)}{N(T,2T)}
 \ge2-D_*+\frac1{272000}
 >\frac{33625219}{50000000}
 =0.672504380.                                       \tag{7}
$$

The increment is $2205/17\approx129.706$ times the previous
$1/35280000$. The rational verifier
[sharpened_cubic_gain.py](../../verify/sharpened_cubic_gain.py) checks the Taylor bounds, derives the
polynomial integral, and verifies the final squared margin.

## 5. A profile-optimization formula

Dropping the favorable $-\delta$ inside the last square root of (6), put

$$
 C(u)=3\sqrt2\left(\sqrt{Q(u)}+\sqrt{D(u)-2/3}\right),\qquad
 \gamma(u)=
 \left(\frac{2\kappa(u)}
 {\sqrt{C(u)^2+24\kappa(u)}+C(u)}\right)^2.
$$

Then $2-D(u)+\gamma(u)$ is a rigorous objective whenever $\kappa(u)>0$.
It is directly usable for profile optimization, with polynomial upper
envelopes supplying rational certificates.
At the cosine, $D'(h)=0$ for mass-preserving perturbations, and

$$
 \kappa'(h)=3\int h(x)\,[u_*^2(x)-2D_*u_*(x)-K(u_*^2)(x)]\,dx,
 \qquad Kf(x)=\int|x-y|f(y)\,dy.
$$

Thus the scalar objective has an explicit first variation; no claim that
the cosine remains exactly optimal for the improved objective is made.

The final scalar implication was also checked by AXLE in `lean-4.31.0`
on 2026-09-05, request `a7b008bc-9067-47f4-8256-1ec8643b49d2`.
[refined_gap_scalar.lean](../../verify/refined_gap_scalar.lean) uses only
`propext`, `Classical.choice`, and `Quot.sound`. This checks the scalar
step, not the operator argument, analytic moment transfer, or repository build.

An independent audit checked the distance identity, linear term, both
triangular trace expansions, the coefficient `6 delta`, the height trace
error above, and the exact rational verifier; no new gap was found in
this operator/scalar extension.
