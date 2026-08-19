> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Certificate 100, cycle 1: optimized capped nonflat block

## Outcome

Fix the inherited strict pair-trace support and the strict quartic block width

\[
 \sigma=1.9999,\qquad \mu=0.4999,\qquad 4\mu=1.9996<2.
 \tag{1}
\]

Optimizing the entire mean-one block symbol under the support-(2) Euler cap
produces a two-phase obstacle profile: the outer phase saturates the cap, while
the central phase is a free constant.  A fixed rational width and a fixed
rational quartic dual give

\[
 \boxed{
 \liminf_{T\to\infty}\frac{N_{0,\mathrm{simple}}(T,2T)}{N(T,2T)}
 >0.96249.}
 \tag{2}
\]

The directed value before conservative rounding is

\[
 0.9624922\ldots .
 \tag{3}
\]

This is a strict increase of more than (0.01185) over the inherited
(0.95063832187565), with no additional higher-correlation input: the only
new ingredient is the choice of symbol inside the already unconditional
fourth-trace range.

## 1. The exact cap and the admissible symbol cone

For (1<\sigma<2), put (b=(2-\sigma)/2).  The positive Euler optimizer for
the saturated pair kernel is

\[
 u_\sigma(x)=
 \begin{cases}
 \cos(\sqrt2x),&|x|\leq b,\\
 A\cos(|x|-1/2)+B\sin(\sqrt3(|x|-1/2)),
       &b\leq|x|\leq\sigma/2,
 \end{cases}
 \tag{4}
\]

where (A,B) are determined by matching (u,u') at (b).  Set

\[
 M_\sigma=\int_{-\sigma/2}^{\sigma/2}u_\sigma(x)\,dx,
 \qquad
 W(t)=\frac{\sigma u_\sigma(\mu t)}{M_\sigma},quad |t|\leq\frac12.
 \tag{5}
\]

In the accepted mean-one principal-compression normalization, the admissible
symbol cone is exactly

\[
 \mathcal A=\left\{r:0\leq r(t)\leq W(t),\quad
                       \int_{-1/2}^{1/2}r(t)\,dt=1\right\}.
 \tag{6}
\]

At the fixed value in (1), direct elementary evaluation gives

\[
\begin{aligned}
 D&=1.0677256658589\ldots<1.06772567,\\
 W(0)&=1.25467\ldots,qquad W(1/2)=1.19747\ldots .
 \tag{7}
\end{aligned}
\]

Thus the cap has substantial room above one throughout the small block.

## 2. The optimized two-phase profile

For (0<g<1), define

\[
 r_g(t)=
 \begin{cases}
 h_g,&|t|<g/2,\\
 W(t),&g/2\leq|t|\leq1/2,
 \end{cases}
 \qquad
 h_g=\frac{1-2\int_{g/2}^{1/2}W(t)\,dt}{g}.
 \tag{8}
\]

The rational choice

\[
 \boxed{g=\frac{103}{400}=0.2575}
 \tag{9}
\]

gives

\[
 2\int_{103/800}^{1/2}W(t)\,dt=0.9125664\ldots,
 \qquad
 h_g=0.3395479\ldots .
 \tag{10}
\]

Hence (int r_g=1) exactly.  On the central phase (h_g<0.34), whereas
(W(t)>1.25); on the outer phase (r_g=W).  Thus (r_g\in\mathcal A).
For literal smooth windows, replace the outer equality by
((1-\delta)W), smooth the jump in a width (delta), and adjust (h_g)
to restore mean one.  The large central margin makes this admissible, and all
moments converge to those below as (delta\downarrow0).

The shape in (8) is not a guess based on standalone variance.  The outer
cap phase increases the long-distance contractions, while the nonzero central
phase suppresses the quartic cost that made the pure cap/zero profile stop at
approximately (0.96012).

## 3. Profile-sensitive moments

Let (C) be the nested block, (Y=C-I), (q=r-1), and

\[
 h(x)=\int_{-1/2}^{1/2}|x-y|r(y)\,dy.
 \tag{11}
\]

Because (4\mu<2), the accepted Fourier-cycle contraction gives

\[
\begin{aligned}
M_1&=\int q,\\
M_2&=\int q^2+\mu^2\int rh,\\
M_3&=\int q^3+3\mu^2\int qrh,\\
M_4&=\int q^4+4\mu^2\int q^2rh
 +2\mu^2\iint q(x)r(x)q(y)r(y)|x-y|\,dx\,dy\\
&\quad+2\mu^4\int r^2h^2+\mu^4\mathcal X(r),
 \tag{12}
\end{aligned}
\]

where

\[
 \mathcal X(r)=
 \iiint_{\substack{x,y,z\in[-1/2,1/2]\\x+z-y\in[-1/2,1/2]}}
 |x-y||y-z|r(x)r(y)r(z)r(x+z-y)\,dx\,dy\,dz.
 \tag{13}
\]

Every integral in (12)--(13) is elementary on the three cells cut out by
(\pm103/800).  Directed evaluation gives the deliberately widened
enclosures

\[
\boxed{\begin{aligned}
 M_1&=0,\\
 0.242110&<M_2<0.242112,\\
 -0.020523&<M_3<-0.020520,\\
 0.105884&<M_4<0.105889.
\end{aligned}}
\tag{14}
\]

Central values are

\[
 (M_2,M_3,M_4)=
 (0.2421113\ldots,-0.0205216\ldots,0.105886\ldots).
 \tag{15}
\]

For reproducibility, (13) can be reduced without a three-dimensional
discontinuity: for fixed (x,y), split (z) at the three symbol cells and at
the translated three cells for (x+z-y), then integrate
(|x-y||y-z|r(z)r(x+z-y)).  The resulting finite elementary integrals give
(14) with outward rounding.

## 4. A fixed rational quartic dual

Let

\[
 a=-\frac{3049}{5000},\qquad
 c=\frac{1603}{5000},\qquad
 t=\frac{2657}{2500}.
 \tag{16}
\]

Define the quartic (P) and constant (L) uniquely by

\[
 P(a)=P'(a)=0,qquad
 P(c)=c^2, P'(c)=2c,qquad
 P(t)=L, P'(t)=0.
 \tag{17}
\]

Since all contacts are rational, this defines an exact rational certificate.
Its decimal display is

\[
\begin{aligned}
P(y)={}&-0.03259887789734+0.19135742095254y
 +0.70697058837051y^2\\
&+0.19985105985092y^3-0.49382690633791y^4,\\
L={}&0.57918851869157.
\end{aligned}
\tag{18}
\]

The global inequalities

\[
 P(y)\leq0\ (y\leq0),\qquad
 P(y)\leq y^2\ (y\geq0),\qquad
 P(y)\leq L\ (y\geq0)
 \tag{19}
\]

follow from the exact double-root factorizations.  Numerically displaying
their remaining quadratic factors,

\[
\begin{aligned}
P(y)&=(y-a)^2(-0.08766532+0.80212235y-0.49382691y^2),\\
y^2-P(y)&=(y-c)^2(0.31715796+0.11679075y+0.49382691y^2),\\
L-P(y)&=(y-t)^2(0.54162342+0.84982741y+0.49382691y^2).
\end{aligned}
\tag{20}
\]

The first residual quadratic has both roots positive, so it is negative for
(y\leq0).  The last two have positive leading coefficient and discriminants

\[
 -0.61284445\ldots,qquad -0.34766623\ldots,
 \tag{21}
\]

so they are positive on the real line.  Thus (19) is global, not a sampled
condition.

## 5. Trim and fixed point

Write

\[
 \frac{s}{N}=2-D+\varepsilon.
 \tag{22}
\]

The inherited stability lemma permits at most the block fraction

\[
 \alpha\leq\frac{D-1-\varepsilon}{2\mu}
 \tag{23}
\]

to be removed for free.  Equations (19) and the four moments imply

\[
 \varepsilon\geq
 \mu\left(A_P-L\alpha\right),qquad
 A_P=P_0+P_2M_2+P_3M_3+P_4M_4.
 \tag{24}
\]

Since (P_2,P_3>0>P_4), the lower endpoints for (M_2,M_3) and the upper
endpoint for (M_4) in (14) give, conservatively,

\[
 A_P>0.08217339066.
 \tag{25}
\]

Substituting (23) into (24) and using (L/2<1) gives the affine fixed point

\[
 \varepsilon\geq
 \frac{\mu A_P-\frac L2(D-1)}{1-L/2}.
 \tag{26}
\]

With the directed upper bound (D\leq1.06772567), (25)--(26) yield

\[
 \varepsilon>0.03021584923,
 \tag{27}
\]

and therefore the completely rounded certificate

\[
 \boxed{
 \frac{s}{N}>
 2-1.06772567+0.03021584923
 =0.96249017923.}
 \tag{28}
\]

Using the central moment values instead of the deliberately wide enclosure
gives

\[
 \varepsilon=0.0302179\ldots,qquad
 \frac{s}{N}=0.9624922\ldots .
 \tag{29}
\]

## 6. Optimization over the admissible symbol

The following progression shows why the two-phase profile matters.  Every
row uses the same exact moment formula and optimizes the trimmed quartic dual.

\[
\begin{array}{l|c}
\text{admissible symbol}&\text{simple proportion}\\ \hline
\text{central constant top hat from cycle 95}&0.9506383\\
W\text{ on a central interval, zero at the edges}&0.95703\\
W\text{ on the two outer intervals, zero at the center}&0.96012\\
\text{central constant plus outer cap, (8)--(10)}&0.9624922
\end{array}
\tag{30}
\]

An aligned width scan was

\[
\begin{array}{c|c|c}
g&h_g&\varepsilon\\ \hline
0.2525&0.3215036&0.0302086\\
0.2550&0.3306146&0.0302160\\
0.2575&0.3395479&0.0302179\\
0.2600&0.3483086&0.0302144\\
0.2625&0.3569017&0.0302056
\end{array}
\tag{31}
\]

Quadratic interpolation places the continuous optimum near (g=0.2571), so
the rational choice (9) loses only a few parts in (10^6) in the increment.

The symbol was also released cell-by-cell under only (6).  The response field
was constant on the free central phase and strictly higher on the cap-active
outer phase, the obstacle KKT pattern.  Three-level center/annulus profiles
collapsed to equal central levels; unrestricted left/right release produced
asymmetry below (2.6\cdot10^{-5}).  Multi-gap, oscillatory, one-sided, and
random active-set starts all returned below (29).  These computations locate
the effective optimizer of the full admissible profile problem; the theorem
(28) itself needs only the single explicit profile (8)--(10).

## 7. Support-(2.03) merge calculation

The prospective arithmetic range (\sigma<63/31=2.032258\ldots) also
contains this block.  At the fixed strict value (\sigma=2.03), the
piecewise elementary Euler solution for (2<\sigma<3) gives

\[
 D_{2.03}=1.06529035197\ldots,qquad
 W_{2.03}(0)=1.256796\ldots,quad
 W_{2.03}(1/2)=1.201826\ldots .
 \tag{32}
\]

Thus the same (g=103/400,mu=0.4999) construction embeds with room; its
mean-one central level becomes (0.32948\ldots).  Re-evaluating (12) and the
trim fixed point gives

\[
 (M_2,M_3,M_4)\approx
 (0.24660,-0.02235,0.10994),qquad
 \varepsilon\approx0.03187,
 \tag{33}
\]

and the merge forecast

\[
 \boxed{\frac{s}{N}\approx0.96658.}
 \tag{34}
\]

This last number is a ready transfer calculation for the arithmetic branch;
the strict theorem of this cycle is (28).

## Terminal handoff

The profile-plus-quartic method class is not exhausted at (95\%\): optimizing
the symbol raises it immediately above (96.249\%\).  The strongest explicit
profile found has only two phases and admits a rational dual with global sign
factors.  The next zero-side attack toward (100\%\) should therefore retain
this capped outer phase and add a sixth-moment block or a second genuinely
mixed observable; refining the quartic profile further has only sub-(10^{-5})
room in the searches above.