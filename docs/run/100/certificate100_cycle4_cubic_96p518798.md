> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Certificate 100, cycle 4: banked cubic and boundary optimization

## Terminal outcome

At the fixed strict pair support

\[
 \sigma=1.999999,
 \qquad D<1.06771746,                              \tag{1}
\]

the sharper rational cubic at \(\mu=0.6666\) first gives

\[
 \boxed{s/N>0.96517745659}.                        \tag{2}
\]

Pushing the block to the still-strict rational width

\[
 \boxed{\mu={333333\over500000}=0.666666},
 \qquad3\mu=1.999998<2,                            \tag{3}
\]

and using a second fixed rational cubic improves this to

\[
 \boxed{
 \liminf_{T\to\infty}{N_{0,\mathrm{simple}}(T,2T)\over N(T,2T)}
 >0.96518798.}                                     \tag{4}
\]

The directed central value of the displayed certificate is

\[
 0.9651879899\ldots .                              \tag{5}
\]

This is a strict gain over both the previous cycle's \(0.96512081\) and the
banked value (2).  The cycle also closes the natural mixed cubic--quartic
trace algebra at these widths: below total arithmetic support two, it has no
genuinely noncommutative invariant.

## 1. Bank the sharper rational cubic

Keep the cycle-3 block

\[
 \mu_0=0.6666,
 \qquad M_2>0.37432,
 \qquad M_3<-0.06711.                              \tag{6}
\]

Choose

\[
 c={259\over1000},
 \qquad t={1823\over1000},                         \tag{7}
\]

and define \(P(y)=p_0+p_1y+p_2y^2+p_3y^3\) and \(L\) exactly by

\[
 P(-1)=0,
 \quad P(c)=c^2,
 \quad P'(c)=2c,
 \quad P(t)=L,
 \quad P'(t)=0.                                   \tag{8}
\]

The exact rational coefficients are

\[
\begin{aligned}
p_0&=-{66734312579529\over1276719342260000},\\
p_1&={502619626742471\over1276719342260000},\\
p_2&={189991065161\over638359671130},\\
p_3&=-{9468590450\over63835967113},\\
L&={617040463458087\over816316715000000}.
\end{aligned}                                     \tag{9}
\]

In decimals,

\[
\begin{aligned}
P(y)={}&-0.052270150824+0.393680592207y
       +0.297623853375y^2-0.148326889655y^3,\\
L={}&0.755883656576.
\end{aligned}                                     \tag{10}
\]

Exact rational division gives

\[
\begin{aligned}
P(y)&=(y+1)(-0.05227015+0.44595074y-0.14832689y^2),\\
y^2-P(y)&=(y-c)^2(0.77920948+0.14832689y),\\
L-P(y)&=(y-t)^2(0.24317599+0.14832689y).
\end{aligned}                                     \tag{11}
\]

The two roots of the first residual quadratic are positive.  Therefore

\[
 P\le0\quad[-1,0],
 \qquad P\le y^2\quad[0,\infty),
 \qquad P\le L\quad[0,\infty).                   \tag{12}
\]

The directed moment substitution is

\[
 A_P=p_0+p_2M_2+p_3M_3
 >p_0+0.37432p_2-0.06711p_3
 =0.0690906275363\ldots .                         \tag{13}
\]

With the one global trim

\[
 {b\over N}\le{D-1-\varepsilon\over2},
\]

the accepted cubic stability inequality is

\[
 \varepsilon\ge
 \mu_0A_P-{L\over2}(D-1-\varepsilon).             \tag{14}
\]

Substitution of (1), (9), and (13) gives

\[
 \varepsilon>0.03289491659,
 \qquad
 {s\over N}>2-1.06771746+0.03289491659
 =0.96517745659,                                  \tag{15}
\]

which proves the banked claim (2).

## 2. Move strictly toward the cubic support boundary

Retain the fixed old allocation cap \(V_{1.9999}\), which lies strictly
below the cap at the actual pair support in (1).  At the width (3), set

\[
 W_\mu(t)=V_{1.9999}(\mu t),
 \qquad t\in[-1/2,1/2].                            \tag{16}
\]

Let \(g_\mu\) be the unique mass root

\[
 2\int_{g_\mu/2}^{1/2}W_\mu(t)\,dt=1             \tag{17}
\]

and use the mean-one outer-cap symbol

\[
 r_\mu(t)=W_\mu(t)1_{\{|t|\ge g_\mu/2\}}.         \tag{18}
\]

Elementary directed evaluation gives

\[
 0.17611<g_\mu<0.17613,
 \qquad
 g_\mu=0.1761216802\ldots .                       \tag{19}
\]

On \(|x|\le\mu/2<0.333334\), the cap separation is

\[
 V_{1.999999}(x)-V_{1.9999}(x)>6.9\cdot10^{-6}.   \tag{20}
\]

Thus (18), after the standard taper and mass restoration inside its central
gap, is a strict admissible block for (1).  The complete cubic trace is also
strictly inside support two by (3).

For

\[
 q=r_\mu-1,
 \qquad h(x)=\int_{-1/2}^{1/2}|x-y|r_\mu(y)\,dy,
\]

the accepted formulas

\[
 M_2=\int q^2+\mu^2\int rh,
 \qquad
 M_3=\int q^3+3\mu^2\int qrh                     \tag{21}
\]

give

\[
\begin{aligned}
M_2&=0.37434674\ldots>0.37434,\\
M_3&=-0.06710018\ldots<-0.06709.
\end{aligned}                                     \tag{22}
\]

The margins in (19), (20), and (22) are deliberately much wider than the
roundoff needed in the elementary trigonometric integrals.

## 3. A fixed rational boundary dual

Take

\[
 c={25903\over100000},
 \qquad t={182349\over100000}.                    \tag{23}
\]

Define \(P,L\) by the same five rational equations (8).  Their decimal
display is

\[
\begin{aligned}
P(y)={}&-0.052278266123+0.393696176135y
       +0.297677018690y^2-0.148297423567y^3,\\
L={}&0.756259278097.
\end{aligned}                                     \tag{24}
\]

Because (23) is rational, (24) denotes an exact rational certificate.  Its
exact factorization has the following directed display:

\[
\begin{aligned}
P(y)&=(y+1)(-0.05227827+0.44597444y-0.14829742y^2),\\
y^2-P(y)&=(y-c)^2(0.77914994+0.14829742y),\\
L-P(y)&=(y-t)^2(0.24316072+0.14829742y).
\end{aligned}                                     \tag{25}
\]

The roots of the first residual quadratic are

\[
 0.12218\ldots,
 \qquad2.88511\ldots,                             \tag{26}
\]

and the other two residual factors are coefficientwise positive.  Hence the
three global inequalities (12) hold exactly.

Since \(p_2>0>p_3\), (22) yields

\[
 A_P>p_0+0.37434p_2-0.06709p_3
 >0.0691034.                                      \tag{27}
\]

The fixed point (14), now with (3), gives

\[
 \varepsilon>
 {\mu(0.0691034)-\frac L2(1.06771746-1)
  \over1-L/2}
 >0.03290544.                                     \tag{28}
\]

Therefore

\[
 {s\over N}
 >2-1.06771746+0.03290544
 >0.96518798,                                     \tag{29}
\]

proving (4).

## 4. Joint cubic--quartic trace attack at strict support two

Let \(Y_3\) denote the width-\(0.666666\) centered block and \(Y_4\) the
width-\(0.4999\) centered quartic block.  Every mixed trace word containing
\(a\) copies of \(Y_3\) and \(b\) copies of \(Y_4\) requires total Fourier
support

\[
 a(0.666666)+b(0.4999)<2.                         \tag{30}
\]

Consequently all available genuinely mixed words have total degree at most
three.  Up to cyclicity of trace, their new components are only

\[
 \operatorname{tr}(Y_3Y_4),
 \quad\operatorname{tr}(Y_3^2Y_4),
 \quad\operatorname{tr}(Y_3Y_4^2).                \tag{31}
\]

At degree at most three, every trace word in two Hermitian variables is
cyclically indistinguishable from a commuting word: no commutator invariant
exists.  The first one is

\[
 \|[Y_3,Y_4]\|_F^2
 =-\operatorname{tr}[Y_3,Y_4]^2,                  \tag{32}
\]

which has bidegree \((2,2)\) and support

\[
 2(0.666666)+2(0.4999)=2.333132>2.                \tag{33}
\]

There is also a zero-side reason that (31) cannot distinguish the orthogonal
simple/double adversary beyond the cubic already used.  On one multiplicity
atom, the flat responses are affine in the multiplicity \(m\):

\[
 y_3(m)=\mu_3m-1,
 \qquad y_4(m)=\mu_4m-1,
\]

and therefore

\[
 y_4={\mu_4\over\mu_3}y_3+
 \left({\mu_4\over\mu_3}-1\right).               \tag{34}
\]

Every scalar mixed polynomial represented by (31) collapses on this
adversary to a univariate cubic in \(y_3\), already contained in the optimized
cubic dual.  Numerically, at a double atom,

\[
 y_3(2)=0.333332,
 \qquad y_4(2)=-0.0002,                            \tag{35}
\]

so the apparently new mixed signatures are in fact

\[
 y_3^2y_4=-2.22\cdot10^{-5}+O(10^{-10}),
 \qquad y_3y_4^2=1.33\cdot10^{-8}+O(10^{-13}).    \tag{36}
\]

Equations (30)--(36) kill the precisely defined class consisting of
atom-diagonal cubic--quartic mixed trace polynomials under strict support
two.  A genuinely shared noncommutative decomposition would first require
the degree-four invariant (32), which is arithmetically outside this width
pair.  The strict improvement (29) instead comes from the first statistic
outside that mixed class: the optimized one-sided cubic block itself.

### 4.1 The tempting threshold-interlacing route is not nested

There is a second apparent mixed gain which must not be booked.  The cubic
dual has its untrimmed positive contact near (0.259), while the optimized
quartic dual has one near (0.321).  If the optimized quartic block were a
principal subcompression of the optimized cubic block, interlacing at
\(\eta=0.30\) would indeed force extra cubic slack.

The required nesting fails at the profile level.  The physical half-gap of
the optimized wide block is

\[
 x_0={\mu g_\mu\over2}=0.0587071\ldots .           \tag{37}
\]

On the central physical interval of width \(\mu_4=0.4999\), the total power
available under that wide profile is only

\[
 {2\over\mu_4}
 \int_{x_0}^{\mu_4/2}V_{1.9999}(x)\,dx
 =0.94087039\ldots<1.                             \tag{38}
\]

Thus no mean-one width-\(0.4999\) block can be placed inside the optimized
wide outer-gap block.  This is a mass obstruction, independent of tapering.

For a completed outside calculation, force nesting by taking the old
quartic profile on \(|x|\le\mu_4/2\) and setting the wide profile equal to
one on the two remaining annuli.  The mass is then exactly \(\mu\), and the
profile is pointwise admissible, but its wide moments become

\[
 M_2=0.26723261\ldots,
 \qquad M_3=0.00118228\ldots .                     \tag{39}
\]

The optimized cubic fixed point for (39) is only

\[
 \varepsilon=0.00609318\ldots,
 \qquad s/N=0.93837572\ldots .                    \tag{40}
\]

Hence threshold interlacing cannot be combined with the present two
optimized profiles, and the simplest genuinely nested replacement loses far
more than the threshold statistic recovers.

## Closed handoff

The current rigorous floor is \(0.96518798\).  Further optimization of
\(\mu\) has only endpoint-sized room.  A next constant-sized zero-side gain
must either use a narrower pair of blocks whose commutator square satisfies
total support below two, or introduce a non-trace observable that couples
the width-\(2/3\) block to multiplicity atoms before cyclic trace erases the
noncommutativity.