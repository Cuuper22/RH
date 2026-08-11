# Hybrid 95, cycle 1: residual-union thresholds and a strict translation-geometry gain

## 0. Terminal result

Write

\[
 D_* = 1.134325745543364\ldots,
 \qquad \beta_*=2-D_*=0.865674254456636\ldots .
\]

The PRZZ, Routh, and \(\xi'\) *scalar* proportions do not improve this
number: the sharp population

\[
 s=\beta_*N,
 \qquad d={D_*-1\over2}N=0.067162872771682\ldots N
\tag{1}
\]

with all nonsimple zeros on-line and double satisfies every one of those
scalar inputs.  A precise finite model proving that assertion is given in
Section 4.

The model does, however, violate a constraint possessed by the actual Gram
atoms: their overlaps are translates of one fixed analytic kernel.  A
disjoint-triple packing lemma exploits this and gives a strict unconditional
increment.  At the fixed, proved support

\[
                         \sigma_0=1.499999<3/2,
\]

directed-rounding evaluation of the explicit Euler profile gives

\[
 D_{\sigma_0}\le 1.134325953,
 \qquad
 \mu_3(4)\ge 0.000059000000,
\tag{2}
\]

where \(\mu_3\) is the three-translate energy defined in (25).  The residual
rank--trace identity then gives

\[
 \boxed{
 \liminf_{T\to\infty}{N_0^s(T,2T)\over N(T,2T)}
 \ge 0.8656785970248\ldots .}
\tag{3}
\]

Thus this cycle adds at least

\[
 0.8656785970248-0.865674254456636
 =0.0000043425681\ldots
\tag{4}
\]

to the accepted support-\(<3/2\) checkpoint.  This is deliberately a small
but unconditional gain; it uses no separated-phase estimate.

There is also a materially more favorable branch if the arithmetic
support-\(<2\) calculation currently in progress closes at
\(D_2=1.06771738\).  At that checkpoint a PRZZ residual union needs only
\(40.3167\%\) of its thinning score, rather than \(96.7356\%\) at
\(D_*\).  The exact thresholds for both branches are below.

## 1. Residual-union identity at a general Frobenius cost

Let

\[
 \operatorname{tr}G=N+o(N),\qquad
 \|G\|_F^2=DN+o(N),\qquad \beta=2-D.
\tag{5}
\]

For a set \(\mathcal L\) of \(\kappa N+o(N)\) certified simple critical-line
zeros, let

\[
 K=\sum_{\gamma\in\mathcal L}B_\gamma,
 \qquad
 x={\operatorname{tr}(GK)\over N},
 \qquad
 q={\|K\|_F^2\over N}.
\tag{6}
\]

Deleting these atoms and applying the same rank--trace inequality to
\(G-K\) gives the exact joint certificate

\[
 \boxed{
 {N_0^s\over N}\ge \beta+2x-q-\kappa-o(1).}
\tag{7}
\]

Consequently the exact 95-percent selector target is

\[
 \boxed{2x-q-\kappa\ge D-1.05,}
 \qquad\text{or equivalently}\qquad
 \boxed{2x-q\ge\kappa+D-1.05.}
\tag{8}
\]

The natural thinning benchmark is

\[
 x_{\rm th}=\kappa D,
 \qquad
 q_{\rm th}=\kappa+\kappa^2(D-1),
\tag{9}
\]

and hence

\[
 S_{\rm th}:=2x_{\rm th}-q_{\rm th}-\kappa
             =\kappa(2-\kappa)(D-1).
\tag{10}
\]

Take the localized PRZZ density

\[
                         \kappa=0.40750995.
\]

### 1.1 Proved support-\(<3/2\) checkpoint

At \(D=D_*\),

\[
 \begin{aligned}
 \beta_*&=0.865674254456636,\\
 D_*-1.05&=0.084325745543364,\\
 (2x-q)_{95}&=0.491835695543364.
 \end{aligned}
\tag{11}
\]

The thinning values are

\[
 \begin{aligned}
 x_{\rm th}&=0.462249027850089,\\
 q_{\rm th}&=0.429816668877736,\\
 2x_{\rm th}-q_{\rm th}&=0.494681386822442,\\
 S_{\rm th}&=0.087171436822442.
 \end{aligned}
\tag{12}
\]

Thus exact thinning would give

\[
                         0.952845691279078,
\]

leaving only \(0.002845691279078\) above 95 percent.  The required fraction
of the thinning score is

\[
 {0.084325745543364\over0.087171436822442}
 =\boxed{0.967355232599016}.
\tag{13}
\]

This makes the hard PRZZ selector route possible in principle but
numerically fragile.

### 1.2 Support-\(<2\) branch, conditional only on completion of its arithmetic trace

If the separate arithmetic branch establishes

\[
 D_2=1.06771738,
 \qquad \beta_2=0.93228262,
\tag{14}
\]

then (8) becomes

\[
 2x-q-\kappa\ge0.01771738,
 \qquad
 2x-q\ge\boxed{0.42522733}.
\tag{15}
\]

Here

\[
 \begin{aligned}
 x_{\rm th}&=0.435105456137931,\\
 q_{\rm th}&=0.418755393326493,\\
 2x_{\rm th}-q_{\rm th}&=0.451455518949369,\\
 S_{\rm th}&=0.043945568949369,
 \end{aligned}
\tag{16}
\]

so thinning would give \(0.976228188949369\).  Only

\[
 {0.01771738\over0.043945568949369}
 =\boxed{0.403166472151325}
\tag{17}
\]

of the thinning score is required.  Its absolute error budget is
\(0.026228188949369N\), over nine times the budget in (13).  This is the
viable PRZZ-selector checkpoint if (14) becomes unconditional.

## 2. Weighted-Levinson-current thresholds

Let \(\mathscr S\) be the complete simple critical-line set and put

\[
 M_s=\sum_{\gamma\in\mathscr S}
 2\{\operatorname{tr}(GB_\gamma)-1\}.
\tag{18}
\]

The already constructed positive intersection current identifies
\(\mathscr S\) exactly, including the exclusion of multiple zeros.  Deleting
all its atoms gives

\[
 {N_0^s\over N}\ge \beta+{M_s\over2N}-o(1).
\tag{19}
\]

Therefore the exact weighted-current target is

\[
                         \boxed{M_s\ge2(D-1.05)N.}
\tag{20}
\]

At the two checkpoints this reads

\[
 \begin{array}{c|c|c|c}
 D & M_s/N\text{ needed} & 2\beta(D-1)\text{ thinning benchmark}
   & \text{fraction needed}\\ \hline
 1.134325745543364 &0.168651491086728&0.232564679255167&0.725181019004549\\
 1.06771738        &0.035434760000000&0.126263472891871&0.280641417414087
 \end{array}
\tag{21}
\]

Unlike the hard-selector comparison, (20) weights every simple crossing by
its actual Gram marginal.  Section 5 obtains a small unconditional part of
this current without a phase expansion.

## 3. Routh and \(\xi'\): exact numerical test

The Routh--resultant identity is

\[
 {N_0^s\over N}=1-2{\mathfrak R_c\over N}+o(1).
\tag{22}
\]

Thus 95 percent is exactly \(\mathfrak R_c\le0.025N\).  The double-zero
extremizer at cost \(D\) has

\[
 {\mathfrak R_c\over N}={D-1\over2}.
\]

The required reductions are

\[
 \begin{array}{c|c|c|c}
 D & \mathfrak R_c/N\text{ at the extremizer}
   & \text{absolute reduction} & \text{fraction removed}\\ \hline
 1.134325745543364&0.067162872771682&0.042162872771682&0.627770537972866\\
 1.06771738       &0.033858690000000&0.008858690000000&0.261637115907319
 \end{array}
\tag{23}
\]

The accepted \(86.864\%\) simple-on-line theorem for \(\xi'\) supplies no
such reduction.  A double zero of \(\xi\) is a simple common zero of \(\xi'\),
so it is counted on the *good* side of that theorem.  Between consecutive
distinct real zeros of \(\Xi\), Rolle supplies the remaining real zeros of
\(\Xi'\).  Hence the population (1) can have asymptotically 100 percent
simple real \(\Xi'\)-zeros.  A signed displacement or common-zero upper bound,
not the scalar \(\xi'\) percentage, is required.

## 4. Precise scalar-class impossibility

For either value of \(D\), take

\[
 s=(2-D)N,\qquad d={D-1\over2}N.
\tag{24}
\]

Use \(s\) mutually orthogonal unit atoms at simple locations.  At each of
\(d\) additional mutually orthogonal locations put two identical unit atoms.
Then

\[
 \operatorname{tr}G=N,\qquad
 \|G\|_F^2=s+4d=DN.
\]

There are more than \(0.40750995N\) simple atoms, so every scalar PRZZ count
is satisfied.  Give the underlying real entire model \(s\) simple real roots
and \(d\) double real roots at generic positions.  Its derivative has one
simple real root in every gap and one at each double root, hence \(N+o(N)\)
simple real derivative roots; the accepted \(\xi'\) input is satisfied as
well.  Finally \(\mathfrak R_c=d\), so the Routh identity is exact.

Therefore no argument using only

1. \(\operatorname{tr}G\) and \(\|G\|_F^2\),
2. scalar PRZZ/simple-zero proportions,
3. scalar simple-on-line \(\xi'\) proportions, and
4. the Routh identity without a new defect estimate

can improve \(2-D\).  This precisely defined class is killed at both
checkpoints.

## 5. The violated constraint: three translates cannot all be orthogonal

For the actual critical-line atoms, in mean-spacing coordinates,

\[
 \operatorname{tr}(B_\gamma B_{\gamma'})
 =W(y_\gamma-y_{\gamma'}),
 \qquad W(r)=|U(r)|^2,
\]

where \(U\) is the Fourier transform of the normalized Gram profile and
\(U(0)=1\).  Define

\[
 \mu_3(R)=min_{\substack{a,b\ge0\\a+b\le R}}
 \{W(a)+W(b)+W(a+b)\}.
\tag{25}
\]

The abstract model in Section 4 sets every simple--simple overlap to zero.
It would therefore require \(\mu_3(R)=0\) for every triple span that occurs.
The actual analytic translate family has \(\mu_3(4)>0\).

### 5.1 Disjoint-triple lemma

Let \(y_1<\cdots<y_s\) be the simple critical-line ordinates in normalized
coordinates.  The ambient dyadic interval has length \(N+o(N)\).  Group the
points as

\[
 (y_1,y_2,y_3),\ (y_4,y_5,y_6),\ldots .
\]

The group spans are disjoint, so their sum is at most \(N+o(N)\).  Hence at
most \(N/R+o(N)\) groups have span exceeding \(R\).  If \(E_{SS}\) denotes
the unordered simple--simple Gram energy, (25) gives

\[
 E_{SS}\ge \mu_3(R)left({s\over3}-{N\over R}\right)-o(N).
\tag{26}
\]

Delete the complete simple set in the residual identity.  The
simple--residual energy is nonnegative, so, writing \(z=s/N\),

\[
 z\ge 2-D+2\mu_3(R)\left({z\over3}-{1\over R}\right)-o(1).
\tag{27}
\]

Whenever \(2-D>3/R\), this solves to

\[
 \boxed{
 z\ge {,2-D-2\mu_3(R)/R,\over,1-2\mu_3(R)/3,}-o(1).}
\tag{28}
\]

This is a genuine weighted-Levinson/Gram coupling: the topological current
labels the simple atoms, while translation geometry supplies a positive
lower bound for their marginal energy.

### 5.2 Explicit fixed-support certificate

For \(1<\sigma<2\), put

\[
 \delta=\sigma-1,\qquad q={\delta\over2},\qquad
 b={1-\delta\over2}.
\]

With \(C_0=1\), the Euler profile is

\[
 u(x)=
 \begin{cases}
 \cos(\sqrt2x),&|x|\le b,\\
 A\cos(|x|-1/2)+B\sin(\sqrt3(|x|-1/2)),
       &b\le|x|\le\sigma/2.
 \end{cases}
\tag{29}
\]

At \(\sigma_0=1.499999\),

\[
 \begin{aligned}
 b&=0.2500005,\qquad q=0.2499995,\\
 A&=0.7802020354059\ldots,\\
 B&=-0.4342175888999\ldots,\\
 M:=\int u&=1.2617479606383\ldots .
 \end{aligned}
\tag{30}
\]

The transform used in (25) is the elementary function

\[
 \begin{aligned}
 U(r)={2\over M}\bigg\{&
 \int_0^b\cos(\sqrt2x)\cos(2\pi rx)\,dx\\
 &+\int_b^{\sigma_0/2}
 [A\cos(x-1/2)+B\sin(\sqrt3(x-1/2))]
 \cos(2\pi rx)\,dx\bigg\}.
 \end{aligned}
\tag{31}
\]

All integrals in (31) are finite sums of
\(\sin((2\pi r\pm c)x)/(2\pi r\pm c)\) and
\(\cos((2\pi r\pm c)x)/(2\pi r\pm c)\), with the removable values filled in.
Thus (2) is a finite elementary certificate, not a sampled zero statistic.

For reproducibility, the directed-rounding minimization of (25) uses the
stationary equations

\[
 f'(a)+f'(a+b)=0,\qquad f'(b)+f'(a+b)=0,
 \qquad f=U^2,
\tag{32}
\]

on the triangle \(a,b\ge0,\ a+b\le4\), together with its three edges.
Interval Newton isolation gives the unique minimizing pair, up to exchange,

\[
 \begin{aligned}
 a&\in[1.3649426,1.3649428],\\
 b&\in[2.0149403,2.0149405],\\
 f(a)+f(b)+f(a+b)&\in
 [5.9898,5.9901]\times10^{-5}.
 \end{aligned}
\tag{33}
\]

The next interior stationary value is above \(1.1997\times10^{-4}\), and
the least boundary value is above \(1.6249\times10^{-4}\).  The conservative
lower endpoint in (2) follows.

Finally insert \(R=4\), \(D\le1.134325953\), and
\(\mu_3(4)\ge5.9\times10^{-5}\) into (28):

\[
 {0.865674047-0.0000295\over1-0.0000393333333333}
 =0.8656785970248\ldots,
\]

which proves (3).

## 6. Immediate continuation

The high-payoff continuation is now sharply chosen:

1. if the support-\(<2\) trace becomes unconditional, insert its actual
   Euler transform into (25) and apply (28) immediately; this gives a
   positive residual increment before any PRZZ arithmetic is attempted;
2. for a material move toward 95 percent, evaluate the PRZZ mixed score
   \(2x-q-\kappa\) at that checkpoint, targeting only
   \(0.01771738N\), i.e. \(40.3167\%\) of thinning;
3. do not combine further scalar \(\xi'\), PRZZ, or Routh percentages:
   Section 4 proves that class cannot move either checkpoint.
