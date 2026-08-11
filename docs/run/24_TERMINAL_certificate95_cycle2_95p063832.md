# Certificate 95, cycle 2: the multi-block obstruction and a nonflat block that crosses 95%

## Outcome

There are two conclusions.

1.  The proposed global sharing of the (b) free positive directions among
    disjoint principal blocks is false, even at exact equality in the full
    stability lemma.  A simultaneous (4\)-dimensional dilation below gives
    the obstruction, and its (2r\)-dimensional version works for every
    number (r\) of blocks.  Thus ordinary pinching cannot improve either the
    current support-(3/2) or the prospective support-(2) constants.

2.  A single nonflat mean-one block does improve them.  With fixed strict
    parameters

    \[
       \sigma=1.9999,\qquad \mu=0.4999,\qquad p=0.83,
       \tag{1}
    \]

    its exact fourth-moment certificate gives

    \[
       \boxed{\frac{s}{N}\geq 0.95063832\ldots .}
       \tag{2}
    \]

    Here the only prospective input is the saturated pair trace at the fixed
    support \(\sigma=1.9999<2\).  No endpoint limit is used, and the block's
    fourth trace has strict total support

    \[
       4\mu=1.9996<2.
       \tag{3}
    \]

    At the already proved support, the equally strict choice

    \[
       \sigma=1.4999,\qquad \mu=0.4999,\qquad p=0.89
       \tag{4}
    \]

    gives the unconditional increment

    \[
       \boxed{\frac{s}{N}\geq0.86855250\ldots,}
       \tag{5}
    \]

    improving the previous floor \(0.86725400194550\) by more than
    \(0.0012985\).

Throughout, \(N=N(T,2T)\) and \(s=N_{0,\mathrm{simple}}(T,2T)\).

## 1. Why a shared multi-block trim is impossible

The accepted stability lemma says that if

\[
 G=P+Q,\quad P\succeq0,\quad \operatorname{rank}P\leq s,
 \quad \operatorname{tr}P\leq s,\quad n_+(Q)\leq b,
 \quad s+2b\leq N,
 \tag{6}
\]

and

\[
 \operatorname{tr}G=N,\qquad \lVert G\rVert_F^2\leq DN,
 \qquad \frac{s}{N}=2-D+\varepsilon,
 \tag{7}
\]

then

\[
 E_b(G):=\sum_{i>b}(\lambda_i(G)-1)_+^2\leq\varepsilon N.
 \tag{8}
\]

Interlacing permits (8) to be applied to each principal compression, but the
same \(b\) cannot be shared after pinching.  Here is an exact equality witness.
In \(\mathbb C^4\), put

\[
 u=\frac{e_1+e_3}{\sqrt2},\qquad
 v=\frac{e_2+e_4}{\sqrt2},
 \tag{9}
\]

\[
 P=I-uu^*-vv^*,\qquad Q=2uu^*,\qquad
 G=P+Q=I+uu^*-vv^*.
 \tag{10}
\]

Then \(P\) is a rank-two projection of trace two, \(n_+(Q)=1\), and

\[
 (N,s,b)=(4,2,1),\qquad
 \operatorname{spec}G=(2,1,1,0),\qquad D=\frac32.
 \tag{11}
\]

Thus \(s/N=2-D\) and the full stability slack is exactly zero.  Nevertheless,
for the two coordinate blocks

\[
 H_1=\operatorname{span}(e_1,e_2),\qquad
 H_2=\operatorname{span}(e_3,e_4),
 \tag{12}
\]

both compressions are

\[
 G|_{H_j}=\begin{pmatrix}3/2&0\\0&1/2\end{pmatrix}.
 \tag{13}
\]

The pinched matrix therefore has two positive centered eigenvalues \(1/2\).
One global trim leaves energy \(1/4\), although the right side of (8) is zero.
There is no missing compatibility condition: (9)--(13) are already a
simultaneous dilation of both blocks.

For \(r\) blocks, take

\[
 u=r^{-1/2}\sum_{j=1}^r e_{j,+},\qquad
 v=r^{-1/2}\sum_{j=1}^r e_{j,-}.
 \tag{14}
\]

Each two-dimensional compression has centered eigenvalues \(\pm1/r\), while
one shared trim leaves

\[
 \frac{r-1}{r^2}>0.
 \tag{15}
\]

The positive equality direction is duplicated by its pairing with the zero
direction of the full \(0/1/2\) extremizer.  Consequently every proposed
multi-block inequality obtained solely by pinching (8) and replacing the
individual trims by one global rank-(b) trim is false.  This kills that exact
method class at both \(D_{3/2}\) and \(D_2\); before the construction below its
best constants remain, respectively, \(0.86725400194550\) and
\(0.93831332705095\).

## 2. Exact fourth moments for a nonflat nested block

Use the accepted mean-one principal-compression convention.  Let
\(I=[-1/2,1/2]\), let the absolute block bandwidth be \(\mu<1/2\), and let
\(r\geq0\) be its symbol, normalized by

\[
 \int_I r(x)\,dx=1.
 \tag{16}
\]

Write \(C\) for the block, \(Y=C-I\), \(q=r-1\), and

\[
 h(x)=\int_I |x-y|r(y)\,dy.
 \tag{17}
\]

In the strict range \(4\mu<2\), the Rudnick--Sarnak trace-cycle expansion is
the Gaussian contraction formula for the centered nonzero Fourier modes.
Indeed, every fourth-order cycle has total positive Fourier degree below one;
the Hall inner product pairs equal positive and negative partitions, and the
third centered contraction vanishes.  Expanding the diagonal multiplier
\(q\) and the centered off-diagonal part gives

\[
\begin{aligned}
 M_1&=\mathbb EY=\int_Iq,\\
 M_2&=\mathbb EY^2=\int_Iq^2+\mu^2\int_Irh,\\
 M_3&=\mathbb EY^3=\int_Iq^3+3\mu^2\int_Iqrh,\\
 M_4&=\mathbb EY^4
   =\int_Iq^4+4\mu^2\int_Iq^2rh\\
 &\quad+2\mu^2\iint_{I^2}q(x)r(x)q(y)r(y)|x-y|\,dx\,dy
       +2\mu^4\int_Ir(x)^2h(x)^2\,dx+\mu^4\mathcal X(r),
 \tag{18}
\end{aligned}
\]

where the crossing contraction is

\[
 \mathcal X(r)=
 \iiint_{\substack{x,y,z\in I\\x+z-y\in I}}
 |x-y||y-z|r(x)r(y)r(z)r(x+z-y)\,dx\,dy\,dz.
 \tag{19}
\]

For \(r=1\), (18) gives the accepted moments
\(M_2=\mu^2/3,M_3=0,M_4=4\mu^4/15\), so (18) is the required
profile-sensitive extension of the flat calculation.

The particularly effective profile is the oversampled top hat

\[
 r_p(x)=\frac1p\,1_{[-p/2,p/2]}(x),\qquad 0<p<1.
 \tag{20}
\]

Put \(q_0=1-p\).  Scaling the elementary flat integrals in (18) gives

\[
\boxed{\begin{aligned}
 M_1&=0,\\
 M_2&=\frac{q_0}{p}+\frac{\mu^2p}{3},\\
 M_3&=\frac{q_0^3}{p^2}-q_0+\mu^2q_0,\\
 M_4&=\frac{q_0^4}{p^3}+q_0
       +\frac{2\mu^2q_0^2}{p}+\frac{4\mu^4p}{15}.
\end{aligned}}
\tag{21}
\]

For completeness, the two fourth-order constants used here are

\[
 \int r_p^2h^2=\frac{7p}{60},\qquad
 \mathcal X(r_p)=\frac p{30}.
 \tag{22}
\]

The sharp cutoff is only notation for a standard taper limit.  If
\(r_p\) lies strictly below the full profile, choose a smooth cutoff
\(\chi_\eta\) supported in the same interval and put
\(r_{p,\eta}=\chi_\eta/\int\chi_\eta\).  The strict pointwise margin makes
\(r_{p,\eta}\) admissible for all sufficiently small \(\eta>0\), and all
four expressions in (18) converge to (21).  Thus (21) is attained in the
same fixed-width-ramp limiting convention as the accepted matrix theorem.

## 3. The trimmed four-moment dual

Let \(\rho\) be the limiting law of \(Y\) in a block of dimension
\(\mu N+o(N)\).  At most \(b\) positive directions can be free, so their
fraction in the block is at most

\[
 \alpha\leq\frac{D-1-\varepsilon}{2\mu},
 \qquad \frac{s}{N}=2-D+\varepsilon.
 \tag{23}
\]

For a quartic \(P(y)=\sum_{j=0}^4P_jy^j\) and \(L\geq0\) satisfying

\[
 P(y)\leq0\ (y\leq0),\qquad
 P(y)\leq y^2\ (y\geq0),\qquad
 P(y)\leq L\ (y\geq0),
 \tag{24}
\]

the residual positive-square energy is at least

\[
 \frac1N\sum_{i>b}(\lambda_i(C)-1)_+^2
 \geq
 \mu\left(P_0+P_2M_2+P_3M_3+P_4M_4-\alpha L\right).
 \tag{25}
\]

Combining (8), (23), and (25) yields the explicit affine fixed-point bound

\[
 \varepsilon\geq
 \mu A_P-\frac L2(D-1-\varepsilon),
 \qquad
 A_P=P_0+P_2M_2+P_3M_3+P_4M_4.
 \tag{26}
\]

In particular, if \(L/2<1\),

\[
 \boxed{\displaystyle
 \varepsilon\geq
 \frac{\mu A_P-\frac L2(D-1)}{1-L/2}.}
 \tag{27}
\]

This is also the fixed-point monotonicity statement: the right side before
rearrangement has slope \(L/2<1\).

## 4. A fixed strict support-(2\) certificate above 95%

For \(1<\sigma<2\), put \(b_\sigma=(2-\sigma)/2\).  The positive Euler
optimizer for the saturated kernel is, up to scale,

\[
 u_\sigma(x)=
 \begin{cases}
 \cos(\sqrt2x),&|x|\leq b_\sigma,\\
 A\cos(|x|-1/2)+B\sin(\sqrt3(|x|-1/2)),
       &b_\sigma\leq|x|\leq\sigma/2,
 \end{cases}
 \tag{28}
\]

where \(A,B\) are fixed by continuity of \(u,u'\) at \(b_\sigma\).  Let

\[
 M=\int_{-\sigma/2}^{\sigma/2}u_\sigma(x)\,dx,
 \qquad V_\sigma(x)=\frac{\sigma u_\sigma(x)}M.
 \tag{29}
\]

Thus \(V_\sigma\) is the full symbol in the accepted mean-one convention.
A local symbol \(r(t)\) on the central absolute-width-\(\mu\) block is an
exact power-complementary principal block whenever

\[
 r(t)\leq V_\sigma(\mu t),\qquad |t|\leq\frac12.
 \tag{30}
\]

Take the fixed values in (1).  Elementary directed evaluation of (28)--(29)
gives

\[
\begin{aligned}
 A&=0.8312126609842\ldots,&B&=-0.3551542095562\ldots,\\
 M&=1.5939724172081\ldots,&
 D_\sigma&=1.0677256658589\ldots<1.06772567.
 \tag{31}
\end{aligned}
\]

The optimizer is decreasing on the central interval used below.  At its
edge,

\[
 V_\sigma\!\left(\frac{\mu p}{2}\right)
 =1.2148300069\ldots>
 \frac1p=\frac{100}{83}=1.2048192771\ldots .
 \tag{32}
\]

Hence (30) holds with a pointwise margin greater than \(0.0100\), including
after a sufficiently narrow smooth taper.

For \(\mu=4999/10000\), \(p=83/100\), (21) gives the exact moments

\[
\begin{aligned}
 M_2&=\frac{682156116889}{2490000000000}
      =0.2739582798751\ldots,\\
 M_3&=-\frac{8293346012887}{68890000000000}
      =-0.1203853391332\ldots,\\
 M_4&=\frac{434598816917989781038321}
 {2144201250000000000000000}
      =0.2026856466565\ldots .
 \tag{33}
\end{aligned}
\]

Here is an exact rational dual.  Set

\[
 a=-\frac{9081}{10000},\qquad
 c=\frac{113}{500},\qquad
 t=\frac{4839}{5000},
 \tag{34}
\]

and define \(P,L\) uniquely by

\[
 P(a)=P'(a)=0,\quad
 P(c)=c^2,\ P'(c)=2c,\quad
 P(t)=L,\ P'(t)=0.
 \tag{35}
\]

Its decimal display is

\[
\begin{aligned}
P(y)={}&-0.03081012951546+0.26255085362744y
 +0.47272747317368y^2\\
&-0.07857608141935y^3-0.26387052614930y^4,\\
L={}&0.36334253565069.
\end{aligned}
\tag{36}
\]

The inequalities (24) are exact, not sampled.  Polynomial division gives

\[
\begin{aligned}
P(y)&=(y-a)^2(-0.03736166074+0.40066556817y-0.26387052615y^2),\\
y^2-P(y)&=(y-c)^2(0.60322126861+0.19784555924y+0.26387052615y^2),\\
L-P(y)&=(y-t)^2(0.42081695737+0.58932387183y+0.26387052615y^2).
\end{aligned}
\tag{37}
\]

The first remaining quadratic has both roots positive
\((0.0998\ldots,1.4185\ldots)\), so it is negative for \(y\leq0\).
The other two have positive leading coefficient and discriminants

\[
 -0.5975463888\ldots,qquad -0.0968621419\ldots,
 \tag{38}
\]

so they are positive on the real line.  This proves (24) globally.

Substitution of the exact moments gives

\[
 A_P=0.05467411586816\ldots .
 \tag{39}
\]

Using the directed upper bound \(D\leq1.06772567\) in (27) gives

\[
 \varepsilon\geq0.01836399187565\ldots,
 \tag{40}
\]

and therefore

\[
 \frac{s}{N}\geq
 2-1.06772567+0.01836399187565
 =0.95063832187565\ldots .
 \tag{41}
\]

The primal law at equality, included to identify the sharp branch, has atoms

\[
 (-0.90812647\ldots,\ 0.22602854\ldots,\ 0.96776010\ldots)
 \tag{42}
\]

of masses

\[
 (0.23158120\ldots,\ 0.71904726\ldots,\ 0.04937155\ldots).
 \tag{43}
\]

The smooth-taper approximation in Section 2 and the strict margins in
(3), (31), (32), and (41) preserve, conservatively,

\[
 \boxed{s/N>0.9506-o(1).}
 \tag{44}
\]

## 5. The unconditional strict support-(3/2\) increment

Repeat the construction with (4).  The Euler profile (28) gives

\[
 D_{1.4999}=1.1343464247878\ldots<1.13434643,
 \tag{45}
\]

and the allocation has the strict margin

\[
 V_{1.4999}\!\left(\frac{\mu p}{2}\right)
 =1.1304617832\ldots>
 \frac{100}{89}=1.1235955056\ldots .
 \tag{46}
\]

The exact top-hat moments are

\[
 (M_2,M_3,M_4)=
 (0.1977325085846\ldots,-0.0808306555090\ldots,
   0.1318241870970\ldots).
 \tag{47}
\]

For a compact exact dual, take the rational contacts

\[
 a=-\frac{8905}{10000},\qquad
 c=\frac{911}{10000},\qquad
 t=\frac{6623}{10000},
 \tag{48}
\]

and impose (35).  Then

\[
\begin{aligned}
P(y)={}&-0.00686317131939+0.14917568735725y
 +0.20427252783473y^2\\
&-0.14444828857654y^3-0.19764418243119y^4,\\
L={}&0.10154630967752.
\end{aligned}
\tag{49}
\]

The three remaining quadratic factors in (37) are now, respectively,

\[
\begin{aligned}
&-0.00865479912+0.20755600033y-0.19764418243y^2,\\
&0.82696682207+0.18045905862y+0.19764418243y^2,\\
&0.24714837264+0.40624777262y+0.19764418243y^2.
\end{aligned}
\tag{50}
\]

The first has both roots positive; the last two have discriminants
\(-0.62121525\ldots\) and \(-0.03035250\ldots\).  Thus this is again a
global dual certificate.  Equation (27), with the directed bound in (45),
gives

\[
 \varepsilon\geq0.0028989382854\ldots,
 \tag{51}
\]

and hence

\[
 \boxed{
 \frac{s}{N}\geq
 2-1.13434643+0.0028989382854
 =0.8685525082854\ldots .}
 \tag{52}
\]

This is already unconditional under the accepted support-(<3/2) theorem.

## Terminal handoff

The global multi-block budget-sharing idea is obstructed by the exact
simultaneous dilation (9)--(15).  The useful replacement is not another
block; it is a deliberately nonflat symbol in one block.  It yields:

* an immediate proved support-(1.4999) floor \(0.86855250\ldots\);
* a fixed strict support-(1.9999) implication \(0.95063832\ldots\);
* no arithmetic input beyond that one prospective saturated pair trace,
  since the profile-sensitive fourth trace stays in \(4\mu<2\).

Thus a pair-trace theorem at the single fixed support \(1.9999\), with cost
at most \(1.06772567\), is sufficient for more than (95\%\) simple critical-line
zeros.  The zero-side part is complete.
