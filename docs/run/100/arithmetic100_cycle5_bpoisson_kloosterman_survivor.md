> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Zeta-100 arithmetic, cycle 5: sharpness of the modulus Cauchy step and signed \(b\)-Poisson

## 0. Terminal output

This cycle takes the permitted **sharp method-class kill plus concrete signed
bilinear-in-\(b\) calculation** branch.  No support extension is claimed.

Set

\[
 \rho={1\over1001},\qquad L=H^\rho,\qquad
 P=H^{1/3},\qquad b\asymp P^2.                             \tag{1}
\]

Cycle 4 reached, for each selected shift,

\[
 E_{\rm III}(\ell)={1\over P}\sum_{b\asymp P^2}\beta_b
 \mathcal G_b(\ell),                                      \tag{2}
\]

with

\[
 \|\beta\|_2\ll P H^{o(1)},\qquad
 \sum_b|\mathcal G_b(\ell)|^2\ll P^7H^{o(1)}.              \tag{3}
\]

The norm-only Cauchy step gives

\[
                         |E_{\rm III}(\ell)|
                         \ll P^{7/2}H^{o(1)}.               \tag{4}
\]

Section 2 proves that (4) is intrinsically sharp for the precisely defined
norm-only modulus class.  The saturating model is explicit:

\[
 \mathcal G_b=P^{5/2}\xi_b,\qquad
 \beta_b=\overline{\xi_b},\qquad |\xi_b|=1,\qquad
 b\asymp P^2.                                              \tag{5}
\]

It is pointwise divisor-bounded and attains equality in Cauchy.  The MD
target would require the uniform scale

\[
                         {H\over L}={P^3\over L},           \tag{6}
\]

so the exact missing gain in amplitude is

\[
                         P^{1/2}L,                          \tag{7}
\]

or, after squaring and summing the \(L\) shifts,

\[
                         \boxed{P L^2=H^{1/3+2\rho}}.       \tag{8}
\]

Thus no rearrangement using only (3) and Cauchy can close the block.

Outside that class, retain the actual convolution

\[
                         \beta_b=\sum_{y_1y_2=b}v_1(y_1)v_2(y_2) \tag{9}
\]

and use the signed reciprocal phase before Cauchy in \(b\).  Additive
reciprocity followed by Poisson summation in \(y_2\) gives an exact second
dual decomposition.

The new zero dual frequency is unconditionally trace-safe:

\[
 \boxed{E_{b,0}(\ell)\ll P^2L\,H^{o(1)}
       =H^{2/3+\rho+o(1)}}.                                \tag{10}
\]

Its whole MD contribution is below budget by

\[
 \boxed{H^{-2/3+4\rho+o(1)}
       =H^{-0.662670662\ldots+o(1)}}.                      \tag{11}
\]

For the nonzero \(b\)-dual, the \(h,n\) variables both have length \(P\)
against modulus \(a\asymp P^2\), exactly the square-root range of
Blomer--Pascadi.  One insertion gives

\[
 \boxed{E_{b,\ne0}(\ell)
 \ll P^{63/16+o(1)}
 =H^{21/16+o(1)}}.                                        \tag{12}
\]

This signed \(b\)-Poisson route does not close: its induced MD output misses
\(H^{2-\rho}\) by

\[
 \boxed{H^{5/8+2\rho+o(1)}}.                               \tag{13}
\]

Although (12) is weaker than the product-residue large-sieve bound (4), it
is a completed calculation outside the sharp norm class.  It proves that
the second \(b\)-Poisson **zero mode is not the obstruction**.  The loss
lies in the nonzero Kloosterman family together with the still-unaveraged
\(a\) and \(y_1\) variables.

The unconditional endpoint and accepted floor remain

\[
 \boxed{\sigma<2,\qquad
 \liminf_{T\to\infty}{N_{0,\mathrm{simple}}(T)\over N(T)}
 >0.96250068026-o(1).}                                    \tag{14}
\]

## 1. Exact modulus sum inherited from cycle 4

For fixed \(\ell\asymp L\), the centered first Poisson transform is

\[
\begin{aligned}
 E_{\rm III}(\ell)
 ={1\over P}
 \sum_{0<|h|\ll P}
 \sum_{a=x_1x_2\asymp P^2}
 \sum_{b=y_1y_2\asymp P^2}
 c_{h,\ell}\alpha_a\beta_b
 e\!\left({h\ell\bar a\over b}\right),
                                                               \tag{15}
\end{aligned}
\]

up to fixed unit twists, smooth Mellin integrals, and \(H^{o(1)}\) gcd
splits.  Cycle 3 allows the reciprocity replacement

\[
 e(h\ell\bar a/b)
 =e(-h\ell\bar b/a)
 +O\!\left({h\ell\over ab}\right),                         \tag{16}
\]

whose accumulated error is \(PL^2H^{o(1)}=o(H)\).

Cycle 4 kept \(a=x_1x_2\) through one multiplicative-Fourier difference and
obtained (2)--(4).  The only operation left in that route was the sum over
the variable two-factor modulus \(b\).

## 2. Exact sharpness of norm-only \(L^1\)-to-\(L^2\)

Define \(\mathscr C_{b,2}\) to consist of arguments which:

1. use the product-residue large-sieve output (3);
2. retain no information about \(\beta_b\) beyond
   \(\|\beta\|_2\le P H^{o(1)}\) and pointwise divisor boundedness;
3. estimate (2) by Cauchy, duality, or an operator-norm consequence of
   those two pieces of information.

The upper bound is

\[
\begin{aligned}
 |E_{\rm III}(\ell)|
 &\le {1\over P}\|\beta\|_2
       \left(\sum_b|\mathcal G_b(\ell)|^2\right)^{1/2}\\
 &\ll {1\over P}\cdot P\cdot P^{7/2}H^{o(1)}
 =P^{7/2}H^{o(1)}.                                        \tag{17}
\end{aligned}
\]

It cannot be improved in this information class.  There are
\(\asymp P^2\) admissible \(b\)'s.  Choose arbitrary unit phases \(\xi_b\)
and set (5).  Then

\[
 \|\beta\|_2\asymp P,\qquad
 \|\mathcal G\|_2\asymp P^{7/2},                           \tag{18}
\]

and

\[
 {1\over P}\sum_b\beta_b\mathcal G_b
 ={1\over P}\sum_bP^{5/2}
 \asymp P^{7/2}.                                           \tag{19}
\]

The coefficients \(\beta_b\) in this model are 1-bounded, hence
divisor-bounded.  Equations (18)--(19) prove:

> **Norm-only modulus barrier.**  No argument in \(\mathscr C_{b,2}\)
> improves (4).  Relative to the MD target, its exact squared loss is
> \(PL^2=H^{1/3+2\rho}\).

This is a theorem about discarding the convolution and phase of
\(\beta_b\), not about the actual HB coefficient.

## 3. Outside the class: open \(b=y_1y_2\) before Cauchy

Insert (9) into the reciprocal reading of (15):

\[
\begin{aligned}
 E_{\rm III}(\ell)
 ={1\over P}
 \sum_{0<|h|\ll P}\sum_{a\asymp P^2}\sum_{y_1,y_2\asymp P}
 c_{h,\ell}\alpha_a v_1(y_1)v_2(y_2)
 e\!\left(-{h\ell\,\overline{y_1y_2}\over a}\right)
 +O(PL^2H^{o(1)}).                                        \tag{20}
\end{aligned}
\]

Fix \(a,h,y_1\) and Poisson-complete \(y_2\) modulo \(a\).  The exact
identity is

\[
\begin{aligned}
 &\sum_{y_2}v_2(y_2)W(y_2/P)
 e\!\left(-{h\ell\bar y_1\bar y_2\over a}\right)\\
 &\quad={P\over a}\sum_{n\in\mathbb Z}
 \widehat W(nP/a)
 S(n,-h\ell\bar y_1;a),                                   \tag{21}
\end{aligned}
\]

where

\[
 S(m,n;a)=\sum_{x\bmod a}^{*}e((mx+n\bar x)/a).            \tag{22}
\]

As \(a/P\asymp P\), rapid decay restricts

\[
                              |n|\ll P H^{o(1)}.             \tag{23}
\]

Together with the first Poisson factor \(P^{-1}\), equation (21) gives the
overall prefactor

\[
                         {1\over P}{P\over a}
                         \asymp P^{-2}.                     \tag{24}
\]

## 4. The \(b\)-Poisson zero mode is safe

For \(n=0\),

\[
                         S(0,-h\ell\bar y_1;a)=c_a(h\ell), \tag{25}
\]

the Ramanujan sum, provided \((y_1,a)=1\); the standard gcd split gives the
same bound in the remaining cases.  Use

\[
 |c_a(m)|\le(a,m),\qquad
 \sum_{0<|h|\ll P}(a,h\ell)
 \ll PL\,H^{o(1)}.                                        \tag{26}
\]

There are \(P^2H^{o(1)}\) weighted \(a\)'s and \(PH^{o(1)}\) weighted
\(y_1\)'s.  Thus (24)--(26) give

\[
\begin{aligned}
 |E_{b,0}(\ell)|
 &\ll P^{-2}\cdot P^2\cdot P\cdot(PL)H^{o(1)}\\
 &\ll P^2L\,H^{o(1)},                                     \tag{27}
\end{aligned}
\]

which proves (10).

Its MD contribution is

\[
 \sum_{\ell\asymp L}|E_{b,0}(\ell)|^2
 \ll L(P^2L)^2H^{o(1)}
 =P^4L^3H^{o(1)}
 =H^{4/3+3\rho+o(1)}.                                     \tag{28}
\]

Dividing by \(H^{2-\rho}\) gives \(H^{-2/3+4\rho+o(1)}\), proving (11).

## 5. Nonzero \(b\)-dual and the square-root BP insertion

For fixed \(a,y_1\), the nonzero part of (21) contains

\[
 \sum_{0<|h|,|n|\ll P}
 c_{h,\ell}d_{n,a}\,
 S(n,-\ell\bar y_1\,h;a).                                  \tag{29}
\]

Both sequences have \(L^2\) norm \(P^{1/2}H^{o(1)}\).
The modulus is \(a\asymp P^2\), so \(h,n\) are in its square-root range.
The balanced Blomer--Pascadi theorem therefore gives

\[
\begin{aligned}
 (29)
 &\ll
 P^{1/2}P^{1/2}
 (P^2)^{1-1/32+o(1)}\\
 &=P^{47/16+o(1)}.                                        \tag{30}
\end{aligned}
\]

Unit and nonunit multipliers are handled by the standard fixed-divisor
split; shortening the modulus does not worsen (30).

Now sum \(y_1\) in \(L^1\), sum the \(a\)-coefficient in \(L^1\), and use
(24):

\[
\begin{aligned}
 |E_{b,\ne0}(\ell)|
 &\ll P^{-2}\cdot P^2\cdot P\cdot P^{47/16+o(1)}\\
 &=P^{63/16+o(1)}
 =H^{21/16+o(1)},                                         \tag{31}
\end{aligned}
\]

which proves (12).

The induced MD output is

\[
 L\left(H^{21/16}\right)^2H^{o(1)}
 =H^{21/8+\rho+o(1)}.                                     \tag{32}
\]

Relative to \(H^{2-\rho}\), the gap is

\[
                         H^{5/8+2\rho+o(1)},                \tag{33}
\]

proving (13).

## 6. Handoff

* The norm-only \(b\)-Cauchy step is exactly sharp; saturating model (5)
  attains \(P^{7/2}\).
* Exact missing norm-class gain: \(P^{1/2}L\) in amplitude,
  \(PL^2=H^{1/3+2\rho}\) in MD.
* Opening the actual \(d_2\)-coefficient and Poisson summing \(y_2\) creates
  a Ramanujan zero mode and a square-root Kloosterman family.
* The Ramanujan mode is safely \(H^{2/3+\rho+o(1)}\).
* One BP insertion on the nonzero family gives
  \(H^{21/16+o(1)}\) per shift, still short of trace grade.
* No support extension is claimed; the accepted floor remains
  \(0.96250068026-o(1)\).