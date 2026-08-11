# Certificate 100, cycle 3: a wide cubic block

## Terminal theorem

Use the inherited strict pair-trace window at

\[
 \sigma_1=1.99999,
 \qquad D_{\sigma_1}<1.06771821,                   \tag{1}
\]

and the strict cubic-block width

\[
 \boxed{\mu=0.6666},
 \qquad 3\mu=1.9998<2.                            \tag{2}
\]

The block profile and rational cubic dual constructed below give

\[
 \boxed{
 \liminf_{T\to\infty}
 {N_{0,\mathrm{simple}}(T,2T)\over N(T,2T)}
 >0.96512.}                                       \tag{3}
\]

The directed value before the final rounding is

\[
 0.9651208\ldots .                                \tag{4}
\]

This is a strict increase of more than \(0.002619\) over the operative
floor \(0.962501736\).  It is genuinely outside the exhausted quartic
profile/pinching class: the new statistic is the signed third trace of a
single block wider than \(1/2\).  No shared trim, off-block estimate, or
two-compression comparison is used.

## 1. Why a cubic is admissible here

Let \(C\) be the accepted Gram compression and put

\[
 Y=C-I.
\]

The Gram positivity in the accepted compression model gives

\[
 C\succeq0,
 \qquad \operatorname{spec}Y\subset[-1,\infty).  \tag{5}
\]

Consequently a negative-leading cubic dual only has to satisfy its negative
side inequality on the compact interval \([-1,0]\).  The obstruction at
\(y\to-\infty\), which forced the earlier global duals to have even degree,
is absent.  At the same time, (2) places the complete third trace strictly
inside the accepted Rudnick--Sarnak range.

## 2. A fixed admissible outer-cap profile

Retain the old strict Euler profile at

\[
 \sigma_0=1.9999.
\]

For \(1<\sigma<2\), put \(b_\sigma=(2-\sigma)/2\) and

\[
u_\sigma(x)=
\begin{cases}
\cos(\sqrt2x),&|x|\le b_\sigma,\\
A_\sigma\cos(|x|-1/2)
+B_\sigma\sin(\sqrt3(|x|-1/2)),
&b_\sigma\le |x|\le\sigma/2,
\end{cases}                                      \tag{6}
\]

where \(u,u'\) match at \(b_\sigma\).  Normalize

\[
 V_\sigma(x)=
 {\sigma u_\sigma(x)\over
  \displaystyle\int_{-\sigma/2}^{\sigma/2}u_\sigma(v)\,dv}. \tag{7}
\]

At \(\sigma_0\), the elementary constants are

\[
\begin{aligned}
A_{\sigma_0}&=0.8312126609842\ldots,\\
B_{\sigma_0}&=-0.3551542095562\ldots,\\
\int_{-\sigma_0/2}^{\sigma_0/2}u_{\sigma_0}
 &=1.5939724171891\ldots .
\end{aligned}                                     \tag{8}
\]

On \(I=[-1/2,1/2]\), set

\[
 W(t)=V_{\sigma_0}(\mu t).                        \tag{9}
\]

Let \(g\) be the unique solution of

\[
 2\int_{g/2}^{1/2}W(t)\,dt=1.                    \tag{10}
\]

Directed elementary evaluation gives

\[
 0.17612<g<0.17614,
 \qquad
 g=0.1761268299240\ldots .                        \tag{11}
\]

Define

\[
 \boxed{
 r(t)=W(t)1_{\{|t|\ge g/2\}}.}                   \tag{12}
\]

Then \(r\ge0\), \(\int_Ir=1\), and \(r\le W\).  Moreover, on the whole
physical interval \(|x|\le\mu/2=0.3333\),

\[
 V_{\sigma_1}(x)-V_{\sigma_0}(x)>6.3\cdot10^{-6}. \tag{13}
\]

Thus (12) lies strictly under the actual \(\sigma_1\) allocation cap.
Smooth the two jumps and make an arbitrarily small adjustment inside the
central gap to restore mass one.  The margin (13) keeps every approximant
strictly admissible, and its moments converge to those below.

## 3. Exact second and third moments

Put

\[
 q=r-1,
 \qquad h(x)=\int_I|x-y|r(y)\,dy.                 \tag{14}
\]

The accepted colored-cycle contraction through degree three is

\[
\begin{aligned}
 M_1&=\int_Iq=0,\\
 M_2&=\int_Iq^2+\mu^2\int_Irh,\\
 M_3&=\int_Iq^3+3\mu^2\int_Iqrh.
\end{aligned}                                     \tag{15}
\]

Every integral is elementary after splitting at \(\pm g/2\).  A directed
display of the four components is

\[
\begin{aligned}
\int_Iq^2&=0.21443815249\ldots,\\
\int_Iq^3&=-0.16766289992\ldots,\\
\int_Irh&=0.35981382883\ldots,\\
\int_Iqrh&=0.07542229550\ldots .
\end{aligned}                                     \tag{16}
\]

With \(\mu=0.6666\), this gives

\[
\boxed{
 M_2=0.37432342789\ldots>0.37432,
 \qquad
 M_3=-0.06711995084\ldots<-0.06711.}              \tag{17}
\]

Only the one-sided bounds in (17) will be used.

## 4. A fixed rational cubic dual

Choose the rational contacts

\[
 c={251\over1000},
 \qquad t={1797\over1000}.                        \tag{18}
\]

Define the cubic \(P\) and the cap \(L\), over the rationals, by

\[
 P(-1)=0,
 \quad P(c)=c^2,
 \quad P'(c)=2c,
 \quad P(t)=L,
 \quad P'(t)=0.                                   \tag{19}
\]

The exact coefficients are

\[
\begin{aligned}
p_0&=-{61070710533971\over1233940688460000},\\
p_1&={52802473929781\over137104520940000},\\
p_2&={59232000817\over205656781410},\\
p_3&=-{9045048550\over61697034423},\\
L&={72023818210661\over99768813750000}.
\end{aligned}                                     \tag{20}
\]

For readability,

\[
\begin{aligned}
P(y)={}&-0.04949241978+0.38512569511y
       +0.28801384720y^2-0.14660426769y^3,\\
L={}&0.72190713213.
\end{aligned}                                     \tag{21}
\]

The global signs required on the actual spectral domain follow from exact
rational factorizations:

\[
\begin{aligned}
P(y)&=(y+1)
 (-0.04949242+0.43461811y-0.14660427y^2),\\
y^2-P(y)&=(y-c)^2(0.78558150+0.14660427y),\\
L-P(y)&=(y-t)^2(0.23888189+0.14660427y).
\end{aligned}                                     \tag{22}
\]

The quadratic in the first line has its two roots at

\[
 0.11862\ldots,
 \qquad2.84594\ldots,
\]

so it is negative throughout \([-1,0]\).  The remaining linear factors
are coefficientwise positive for \(y\ge0\).  Hence, exactly,

\[
 P(y)\le0\quad(-1\le y\le0),
 \qquad
 P(y)\le y^2\quad(y\ge0),
 \qquad
 P(y)\le L\quad(y\ge0).                           \tag{23}
\]

## 5. One global trim and the fixed point

Write

\[
 {s\over N}=2-D+\varepsilon,
 \qquad
 {b\over N}\le {D-1-\varepsilon\over2}.          \tag{24}
\]

By (5) and (23), deleting the largest \(b\) positive centered eigenvalues
costs at most \(Lb\), while every remaining positive eigenvalue contributes
at least its value under \(P\).  Therefore

\[
 \varepsilon\ge
 \mu A_P-{L\over2}(D-1-\varepsilon),              \tag{25}
\]

where

\[
 A_P=p_0+p_2M_2+p_3M_3.                           \tag{26}
\]

Since \(p_2>0>p_3\), the two directed sides of (17) give

\[
 A_P>p_0+0.37432p_2-0.06711p_3>0.06815.           \tag{27}
\]

Also \(L/2<0.361\), so the affine fixed point is monotone and (25) yields

\[
\begin{aligned}
\varepsilon
&>{\mu(0.06815)-\frac L2(1.06771821-1)
       \over1-L/2}\\
&>0.03283902.                                     \tag{28}
\end{aligned}
\]

Combining (1) and (28),

\[
 {s\over N}
 >2-1.06771821+0.03283902
 =0.96512081,                                     \tag{29}
\]

which proves (3).

## Constructive handoff

The decisive feature is not a small refinement of the quartic profile.  It
is the combination of

* the one-sided spectral endpoint \(y\ge-1\);
* an odd, negative-leading polynomial;
* a block as wide as the strict cubic support limit permits; and
* the outer-cap/central-gap profile, whose negative third moment rewards the
  sign of \(p_3\).

The next cycle should optimize this same cubic certificate jointly over
\(\mu<2/3\), the gap profile, and rational contacts before adding any second
compression.  The present fixed choices already establish the strict
\(96.512\%\) floor without an endpoint limit.
