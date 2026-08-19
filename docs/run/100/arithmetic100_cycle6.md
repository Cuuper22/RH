> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Zeta-100 arithmetic, cycle 6: Kuznetsov mismatch and the second \(y\)-Poisson

## 0. Terminal output

This cycle takes the permitted **exact spectral-class kill plus concrete
second-\(y\) Poisson calculation** branch.  It does not claim support beyond
two.

Use

\[
 \rho={1\over1001},\qquad L=H^\rho,\qquad
 P=H^{1/3},\qquad a\asymp P^2.                             \tag{1}
\]

Cycle 5 left the nonzero family

\[
 {1\over P^2}
 \sum_{a\asymp P^2}\alpha_a
 \sum_{y\asymp P}\sum_{0<|h|,|n|\ll P}
 c_{h,\ell}d_{n,a}v(y)\,
 S(n,-h\ell\bar y;a).                                     \tag{2}
\]

A Deshouillers--Iwaniec/Kuznetsov modulus average does **not** apply to
(2).  The exact mismatch has two independent parts:

1. the modulus weight
   \(\alpha_a=\sum_{x_1x_2=a}u_1(x_1)u_2(x_2)\) is an
   unsmoothed HB convolution, whereas Kuznetsov requires a controlled
   test transform in the modulus;
2. more decisively, one Kloosterman index is
   \(-h\ell\bar y\pmod a\), hence changes with the modulus \(a\).
   Kuznetsov requires fixed integer indices across the modulus sum.

Section 2 proves that even splitting \(a\) into residue classes modulo
\(y\) does not repair the second defect: the chosen integer representative
of \(\bar y\pmod a\) is affine in \(a\), so the spectral Fourier index still
moves with the modulus.  Consequently no zero, continuous, or exceptional
Kuznetsov spectrum can be invoked for (2) without first changing the
geometry.

Outside that inapplicable class, Poisson summation in the remaining
\(y\)-variable is exact.  It produces the rank-three complete sum

\[
 \mathcal K_3(n,t,q;a)
 :=\sum_{x,u\bmod a}^{*}
 e\!\left({nx+tu-q\overline{xu}\over a}\right),            \tag{3}
\]

with

\[
                         |t|\ll P H^{o(1)}.                 \tag{4}
\]

The new \(t=0\) dual frequency factors completely:

\[
                         \mathcal K_3(n,0,q;a)
                         =c_a(n)c_a(q).                    \tag{5}
\]

It is far inside trace grade:

\[
 \boxed{E_{y,0}(\ell)\ll PL\,H^{o(1)}
       =H^{1/3+\rho+o(1)}}.                                \tag{6}
\]

Its entire MD contribution is below \(H^{2-\rho}\) by

\[
 \boxed{H^{-4/3+4\rho+o(1)}
       =H^{-1.329337329\ldots+o(1)}}.                      \tag{7}
\]

For \(t\ne0\), the complete rank-three bound

\[
                         |\mathcal K_3(n,t,q;a)|
                         \ll a^{1+o(1)}=P^{2+o(1)}          \tag{8}
\]

gives

\[
 \boxed{E_{y,\ne0}(\ell)\ll P^{4+o(1)}
       =H^{4/3+o(1)}}.                                     \tag{9}
\]

This first valid geometry-changing calculation still fails.  Its induced
MD output misses \(H^{2-\rho}\) by

\[
 \boxed{P^2L^2=H^{2/3+2\rho}
       =H^{0.668664668\ldots}}.                            \tag{10}
\]

The exact remaining object is now a bilinear/trilinear form in the
rank-three sums (3), not a falsely claimed Kuznetsov average of the original
rank-two sums.  The zero dual has been evaluated and removed; the loss is
entirely in the nonzero rank-three geometric family.

The unconditional endpoint and accepted floor remain

\[
 \boxed{\sigma<2,\qquad
 \liminf_{T\to\infty}{N_{0,\mathrm{simple}}(T)\over N(T)}
 >0.96250068026-o(1).}                                    \tag{11}
\]

## 1. Exact family left by cycle 5

The first third-factor Poisson transform and the subsequent
\(b=y_1y_2\) opening gave

\[
\begin{aligned}
 E_{b,\ne0}(\ell)
 ={1\over P^2}
 \sum_{a\asymp P^2}\alpha_a
 \sum_{y\asymp P}v(y)
 \sum_{0<|h|,|n|\ll P}
 c_{h,\ell}d_{n,a}
 S(n,-h\ell\bar y;a),                                     \tag{12}
\end{aligned}
\]

up to fixed smooth Mellin integrals and divisor-many gcd splittings.
The length inventory is

\[
\begin{array}{c|c}
\text{variable}&\text{length}\\ \hline
a& P^2\\
y& P\\
h& P\\
n& P\\
\text{Kloosterman modulus}&a\asymp P^2\\
\text{overall prefactor}&P^{-2}.
\end{array}                                                 \tag{13}
\]

For fixed \(a,y\), the \(h,n\) variables are at square-root length, which
is why the single-modulus Blomer--Pascadi insertion in cycle 5 was valid.
The question here is whether the outer \(a,y\) sums form a genuine spectral
modulus average.

## 2. Why the DI/Kuznetsov modulus geometry does not match

The classical Kuznetsov geometric side has the form

\[
 \sum_{c\ge1}{S(m,n;c)\over c}\,
 \Phi\!\left({4\pi\sqrt{|mn|}\over c}\right),              \tag{14}
\]

where \(m,n\) are fixed integers while \(c\) varies and \(\Phi\) is a
controlled smooth test function.  Neither requirement is met by (12).

First,

\[
                         \alpha_a=(u_1*u_2)(a)              \tag{15}
\]

is a dyadic divisor convolution, not a smooth function of \(a\).  Mellin
separation opens it as \(a=x_1x_2\); it does not turn it into a fixed
Kuznetsov test transform.

Second, use the scaling identity

\[
 S(n,-h\ell\bar y;a)=S(n\bar y,-h\ell;a).                  \tag{16}
\]

The first index \(n\bar y\pmod a\) still depends on \(a\).  To see that
residue-class splitting does not fix this, hold \(y\) fixed and place
\(a\) in one reduced residue class modulo \(y\).  Then the integer
\(k\in[0,y)\) satisfying

\[
                         ka\equiv-1\pmod y                 \tag{17}
\]

is fixed on that class, and

\[
                         \bar y\pmod a={1+ka\over y}.       \tag{18}
\]

Thus the putative Kuznetsov index is

\[
                         m_a=n{1+ka\over y},                \tag{19}
\]

which is affine in the varying modulus \(a\), not fixed.  The Bessel
argument and the spectral Fourier coefficient in (14) therefore vary
together with the modulus.

Define \(\mathscr C_{\rm Kuz}\) to consist of arguments that try to apply a
DI/Kuznetsov spectral large sieve directly to (12) while treating
\(\alpha_a\) as a modulus coefficient and \(n\bar y\) as if it were a fixed
Kloosterman index.  Equations (15) and (19) prove:

> **Kuznetsov geometry barrier.**  No member of
> \(\mathscr C_{\rm Kuz}\) is a valid substitution into the Kuznetsov
> formula.  In particular, zero/Eisenstein, continuous, regular cusp, and
> exceptional cusp contributions cannot be assigned to (12) inside this
> class.

This is a compatibility theorem, not an estimate.  The valid zero and
nonzero spectra appear only after the geometry-changing Poisson transform
below.

## 3. Poisson summation in the remaining \(y\)-factor

Open the Kloosterman sum in (12):

\[
 S(n,-q\bar y;a)
 =\sum_{x\bmod a}^{*}
 e\!\left({nx-q\bar x\bar y\over a}\right),
 \qquad q=h\ell.                                           \tag{20}
\]

For fixed \(a,x,q\), Poisson-complete \(y\) modulo \(a\):

\[
\begin{aligned}
 \sum_yv(y)W(y/P)e\!\left(-{q\bar x\bar y\over a}\right)
 ={P\over a}\sum_{t\in\mathbb Z}
 \widehat W(tP/a)S(t,-q\bar x;a).                          \tag{21}
\end{aligned}
\]

Substitute (21) into (20) and interchange \(x,t\).  The complete sum is

\[
\begin{aligned}
 \sum_{x\bmod a}^{*}e(nx/a)S(t,-q\bar x;a)
 &=\sum_{x,u\bmod a}^{*}
 e\!\left({nx+tu-q\bar x\bar u\over a}\right)\\
 &=\mathcal K_3(n,t,q;a),                                  \tag{22}
\end{aligned}
\]

which proves (3).  Since \(a/P\asymp P\), rapid decay gives (4).

The extra Poisson factor is

\[
                         {P\over a}\asymp P^{-1}.           \tag{23}
\]

Together with the inherited prefactor \(P^{-2}\), the transformed family
has total prefactor \(P^{-3}\):

\[
\begin{aligned}
 E_{b,\ne0}(\ell)
 ={1\over P^3}
 \sum_{a\asymp P^2}\alpha_a
 \sum_{0<|h|,|n|\ll P}\sum_{|t|\ll P}
 C_{a,h,n,t,\ell}\,
 \mathcal K_3(n,t,h\ell;a).                                \tag{24}
\end{aligned}
\]

Equation (24) is the first valid complete-sum family in which the old
modulus-dependent inverse \(y\) has disappeared.

## 4. Exact zero dual and spectral inventory

Set \(t=0\) in (22).  For fixed \(x\), inversion permutes the reduced
residues \(u\bmod a\), so

\[
 \sum_{u\bmod a}^{*}e(-q\bar x\bar u/a)=c_a(q).            \tag{25}
\]

The remaining \(x\)-sum is \(c_a(n)\).  Hence

\[
                         \mathcal K_3(n,0,q;a)
                         =c_a(n)c_a(q),                    \tag{26}
\]

proving (5).

Use

\[
\begin{aligned}
 \sum_{|n|\ll P}|c_a(n)|&\ll P H^{o(1)},\\
 \sum_{0<|h|\ll P}|c_a(h\ell)|&\ll PL H^{o(1)}.             \tag{27}
\end{aligned}
\]

There are \(P^2H^{o(1)}\) weighted moduli \(a\).  Therefore (24), (26),
and (27) give

\[
\begin{aligned}
 |E_{y,0}(\ell)|
 &\ll P^{-3}\cdot P^2\cdot P\cdot(PL)H^{o(1)}\\
 &\ll PL\,H^{o(1)},                                       \tag{28}
\end{aligned}
\]

which proves (6).

Its MD contribution is

\[
 L(PL)^2H^{o(1)}
 =P^2L^3H^{o(1)}
 =H^{2/3+3\rho+o(1)}.                                     \tag{29}
\]

Relative to \(H^{2-\rho}\), this is \(H^{-4/3+4\rho+o(1)}\), proving (7).

The honest spectral inventory after (24) is therefore:

\[
\begin{array}{c|c}
\text{piece}&\text{status}\\ \hline
t=0\text{ / Ramanujan zero dual}&\text{evaluated by (26)--(29)}\\
t\ne0\text{ complete geometric family}&\text{rank-three sums (3)}\\
\text{Kuznetsov continuous spectrum}&\text{not present without a new trace formula}\\
\text{regular cusp spectrum}&\text{not present without a new trace formula}\\
\text{exceptional cusp spectrum}&\text{not present without a new trace formula}.
\end{array}                                                 \tag{30}
\]

No exceptional-spectrum loss is hidden in (28); the obstruction is already
on the nonzero geometric side.

## 5. Nonzero rank-three family and its exact exponent

For \(t\ne0\), the complete two-dimensional sum (3) obeys the standard
square-root-in-dimension-two bound

\[
 |\mathcal K_3(n,t,q;a)|
 \ll a^{1+o(1)}(a,ntq)^{O(1)}
 \ll P^{2+o(1)}                                           \tag{31}
\]

after the fixed-divisor split.  Insert (31) into (24).  The outer inventory
is

\[
\begin{array}{c|c}
a&P^2\\
h&P\\
n&P\\
t&P\\
\mathcal K_3&P^2\\
\text{prefactor}&P^{-3}.
\end{array}                                                 \tag{32}
\]

Consequently

\[
 |E_{y,\ne0}(\ell)|
 \ll P^{-3}\cdot P^2\cdot P^3\cdot P^2H^{o(1)}
 =P^{4+o(1)},                                              \tag{33}
\]

which proves (9).

The induced MD output is

\[
                         L(P^4)^2H^{o(1)}
                         =P^8L\,H^{o(1)}.                   \tag{34}
\]

The target is

\[
                         {H^2\over L}
                         ={P^6\over L}.                     \tag{35}
\]

Their ratio is

\[
                         P^2L^2
                         =H^{2/3+2\rho},                    \tag{36}
\]

which proves (10).

Termwise rank-three square-root cancellation is therefore insufficient.
The calculation nevertheless moves outside the invalid Kuznetsov class,
evaluates its true zero dual, and identifies the exact nonzero complete
family on which any further averaging must act.

## 6. Handoff

* Direct DI/Kuznetsov fails exact compatibility: rough convolution modulus
  weight and modulus-dependent index \(n\bar y\).
* Splitting \(a\bmod y\) makes that index affine in \(a\), not fixed.
* Valid geometry change: Poisson in \(y\), producing \(\mathcal K_3\).
* Exact \(t=0\) factorization:
  \(\mathcal K_3(n,0,q;a)=c_a(n)c_a(q)\).
* Zero-dual output: \(H^{1/3+\rho+o(1)}\), safely negligible.
* Nonzero output under complete rank-three bounds:
  \(H^{4/3+o(1)}\) per shift, MD gap \(H^{2/3+2\rho}\).
* No support extension is claimed; the accepted floor remains
  \(0.96250068026-o(1)\).