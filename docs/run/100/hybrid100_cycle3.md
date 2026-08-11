# Hybrid 100, cycle 3: signed kernel contrast, one-block kill, and a positive-definite two-profile block

## Terminal outcome

Work at the current strict support

\[
 \sigma=1.99999,
 \qquad D_\sigma<1.06771821,
 \qquad \beta=2-D_\sigma>0.93228179,
\tag{1}
\]

and retain the already proved capped-outer tail

\[
 \tau>0.03021889026.
\tag{2}
\]

Thus the operative unconditional floor is

\[
 \boxed{\displaystyle s/N>0.96250068026-o(1).}
\tag{3}
\]

This cycle does **not** claim a larger unconditional constant.  It terminates
by the allowed method-class kill, but it also completes a concrete calculation
outside that class.

The exact signed contrast of the existing capped block is positive only on the
initial gap interval

\[
 0\le d<0.35192803\ldots .
\tag{4}
\]

More strongly, among *all* nonnegative mean-one blocks below the available
support-(1.99999) cap, the largest possible universally dominated initial
interval ends no later than

\[
 \boxed{d_*=0.3520134738\ldots .}
\tag{5}
\]

By contrast, the present simple-zero density forces a positive density of
short consecutive simple gaps only after

\[
 R>\frac1{0.96250068026}
   =1.0389603046\ldots .
\tag{6}
\]

Consequently every one-block argument which obtains a signed simple current
solely from pointwise domination on a forced initial gap interval is rigorously
closed.  The unitary translate/modulate orbit of the capped block is closed as
well: its pair kernel is invariant, and its global-minus-local kernel is not
positive definite.

The first calculation outside that orbit is the admissible two-profile
convexification

\[
 r_\theta=(1-\theta)r_c+\theta,
 \qquad \theta=\frac{23}{50}.
\tag{7}
\]

It *does* make the global-minus-local kernel positive definite.  The spectral
density is nonnegative at every shift, with the sharpest nonendpoint margin

\[
 H_{23/50}(0)>1.0412\times10^{-4}.
\tag{8}
\]

However, after insertion into the completed one-/two-current formula, its
all-zero off-diagonal contrast is

\[
 \frac{J_G(\mathcal Z)-J_{\mu,23/50}(\mathcal Z)}N
 <-0.2481306606.
\tag{9}
\]

The density-only uniform simple-label adversary therefore gives, at the old
selector size \(\kappa=0.40750995\),

\[
 \frac{p\mathcal M_\Delta-p^2\mathcal Q_\Delta}{N}
 \le -0.1610257670.
\tag{10}
\]

Thus positive definiteness by itself does not select positive *off-diagonal*
contrast: its diagonal is doing the work.  Equations (4)--(10) are a precise
kill of the pointwise/positive-definite/density-only one-block current class,
not an unevaluated lemma.  The unconditional floor remains (3).

## 1. Exact kernel form of the deletion identity

Let \(p_\sigma\) be the normalized positive Euler density on
\([ -\sigma/2,\sigma/2]\), and define

\[
 U(d)=\int_{-\sigma/2}^{\sigma/2}
       p_\sigma(x)e^{2\pi i d x}\,dx.
\tag{11}
\]

For a nonnegative mean-one local symbol \(r\) on \([-1/2,1/2]\), put

\[
 \ell_r(x)=r(x/\mu)1_{|x|\le\mu/2},
 \qquad
 A_r(d)=\widehat\ell_r(d)
 =\mu\int_{-1/2}^{1/2}r(t)e^{2\pi i\mu d t}\,dt,
\tag{12}
\]

where

\[
 \mu=\frac{4999}{10000}.
\tag{13}
\]

The global and compressed rank-one pair kernels are

\[
 W_G(d)=|U(d)|^2,
 \qquad W_r(d)=|A_r(d)|^2,
\tag{14}
\]

so the signed kernel is

\[
 K_r(d)=W_G(d)-W_r(d).
\tag{15}
\]

For a hard selector \(\mathcal L\) of simple critical-line atoms, the exact
rank-one deletion theorem from cycle 2 gives

\[
 \frac{s}{N}\ge
 2-D_\sigma+\tau+
 \frac{J_G(\mathcal L)-J_r(\mathcal L)}N-o(1),
\tag{16}
\]

where

\[
 J_G(\mathcal L)-J_r(\mathcal L)
 =2\!\sum_{\substack{i<j\\i\in\mathcal L\ {m or}\ j\in\mathcal L}}
 K_r(d_{ij}).
\tag{17}
\]

At (1)--(3), any strictly positive lower bound for (17) improves the
operative floor, while density one requires

\[
 \frac{J_G(\mathcal L)-J_r(\mathcal L)}N
 \ge D_\sigma-1-\tau
 <0.03749931974.
\tag{18}
\]

For the simple current \(\mathscr S\), set

\[
 \mathcal M_r
 =2\sum_{i\in\mathscr S}\sum_{j\ne i}K_r(d_{ij}),
 \qquad
 \mathcal Q_r
 =\sum_{\substack{i,j\in\mathscr S\\i\ne j}}K_r(d_{ij}).
\tag{19}
\]

If \(\mathcal L\) is a uniformly chosen \(k\)-subset of \(\mathscr S\) and
\(p=k/s\), the completed one-/two-current identity is

\[
 \boxed{\displaystyle
 \mathbb E\{J_G(\mathcal L)-J_r(\mathcal L)\}
 =p\mathcal M_r-p^2\mathcal Q_r+o(N).}
\tag{20}
\]

No selector lemma remains in (20): some hard \(k\)-subset attains at least
the displayed average.  The problem is entirely the sign of this one fixed
combination.

## 2. Existing capped-outer block: the signed contrast changes sign too soon

Retain the block used in the proof of (3):

\[
 r_c(t)=
 \begin{cases}
 h,&|t|<g/2,\\
 V_{1.9999}(t),&g/2\le |t|\le1/2,
 \end{cases}
\tag{21}
\]

with

\[
 g=\frac{103}{400},\qquad
 h=0.3395479156016\ldots,
\tag{22}
\]

and

\[
 V_{1.9999}(t)=
 \frac{1.9999\,u_{1.9999}(\mu t)}
 {\int_{-1.9999/2}^{1.9999/2}u_{1.9999}(x)\,dx}.
\tag{23}
\]

The strict embedding proved in root cycle 3 makes (21) admissible below the
new \(\sigma=1.99999\) cap without changing it.

The elementary sine/cosine integrals in (11)--(15) give the following
directed values for \(K_c\):

\[
\begin{array}{c|rrrrr}
d&0&0.25&0.4&0.5&0.5898692281\\ \hline
K_c(d)&0.75009998&0.25700243&-0.08450825&-0.17233669&-0.17424746
\end{array}
\tag{24}
\]

The last displayed gap is the first zero of the new full amplitude \(U\).
The first contrast zero is uniquely enclosed by

\[
 0.35192802<d_c<0.35192804,
\tag{25}
\]

and \(K_c(d)<0\) immediately to its right.  Keeping the signs in (24),
rather than applying absolute values to the two kernels separately, is what
exposes the obstruction.

## 3. Optimization over every admissible nonnegative one-block symbol

Let

\[
 V_+(t)=
 \frac{1.99999\,u_{1.99999}(\mu t)}
 {\int_{-1.99999/2}^{1.99999/2}u_{1.99999}(x)\,dx}.
\tag{26}
\]

Consider the full admissible one-block class

\[
 \mathcal A_+=\left\{r:\ 0\le r(t)\le V_+(t),\quad
 \int_{-1/2}^{1/2}r(t)\,dt=1\right\}.
\tag{27}
\]

This includes asymmetric symbols.  For

\[
 0\le d\le\frac1{2\mu}=1.0002000400\ldots,
\tag{28}
\]

the function \(\cos(2\pi\mu d t)\) is nonnegative and decreases with
\(|t|\).  Hence

\[
 |A_r(d)|\ge \Re A_r(d)
 \ge A_{\rm out}(d)
\tag{29}
\]

for every \(r\in\mathcal A_+\), by the bathtub principle.  Here the extremal
outer-fill symbol is

\[
 r_{\rm out}(t)=V_+(t)1_{|t|\ge a},
 \qquad
 2\int_a^{1/2}V_+(t)\,dt=1,
\tag{30}
\]

and direct evaluation gives

\[
 a=0.0938267782\ldots .
\tag{31}
\]

The extremal contrast

\[
 K_{\rm out}(d)=|U(d)|^2-A_{\rm out}(d)^2
\tag{32}
\]

has its first zero at

\[
 0.35201347<d_*<0.35201348,
\tag{33}
\]

and the elementary phase split gives

\[
 K_{\rm out}(d)<0
 \quad(d_*<d\le1/(2\mu)).
\tag{34}
\]

Useful signed checkpoints are

\[
\begin{array}{c|rrrr}
d&0.4&0.5&0.5898692281&1/(2\mu)\\ \hline
K_{\rm out}(d)&-0.0842870&-0.1720073&-0.1738131&-0.0776347.
\end{array}
\tag{35}
\]

Equations (29) and (34) prove that **no** member of \(\mathcal A_+\) can
satisfy \(W_G(d)\ge W_r(d)\) on an initial interval \([0,R]\) with
\(R>d_*\).

To connect this kernel fact to the simple current, normalize gaps by the
mean zero spacing.  If \(z=s/N\), the consecutive simple gaps in the window
have total at most \(N+o(N)\).  Therefore the number of such gaps at most
\(R\) is bounded below by

\[
 \#\{d_j\le R\}\ge
 \left(z-\frac1R\right)N-o(N).
\tag{36}
\]

A pointwise initial-interval argument forces a positive-density current only
when \(R>1/z\).  Equations (3), (6), and (33) leave a factor of almost three
between the required and available intervals.  This kills the precisely
defined class of density-plus-pointwise-domination simple-current arguments.

## 4. Translate and modulation optimization is exactly flat

Write \(q_c\) for a square root of the physical density \(\ell_{r_c}\), and
form any admissible translated/modulated analysis window

\[
 q_{a,\nu}(x)=e^{2\pi i\nu x}q_c(x-a).
\tag{37}
\]

For two zero ordinates \(\gamma,\rho\), common modulation cancels and
translation supplies only a phase:

\[
 \left|\left\langle
 q_{a,\nu}e^{2\pi i\gamma x},
 q_{a,\nu}e^{2\pi i\rho x}
 \right\rangle\right|^2
 =|A_{r_c}(\gamma-\rho)|^2.
\tag{38}
\]

Consequently, for every \((a,\nu)\) for which the moved window remains
admissible,

\[
 K_{a,\nu}(d)=K_c(d),
 \qquad
 \boxed{\Delta(a,\nu)=\Delta(0,0).}
\tag{39}
\]

Thus optimization over the entire unitary translate/modulate orbit has no
free parameter at the pair-kernel level.

This orbit also cannot be rescued by positive-definite domination.  By
Wiener--Khinchin, \(K_c\) is positive definite exactly when

\[
 H_c(y):=(p_\sigma*\widetilde p_\sigma)(y)
 -(\ell_{r_c}*\widetilde\ell_{r_c})(y)
\tag{40}
\]

is a nonnegative measure.  Already at zero,

\[
\begin{aligned}
 (p_\sigma*\widetilde p_\sigma)(0)
 &=\int p_\sigma^2=0.5220816698782\ldots,\\
 (\ell_{r_c}*\widetilde\ell_{r_c})(0)
 &=\mu\int r_c^2=0.5756117508167\ldots,
\end{aligned}
\tag{41}
\]

so

\[
 H_c(0)<-0.05353008093.
\tag{42}
\]

Translations and modulations leave both autocorrelations in (40) unchanged.
Equations (39)--(42) rigorously kill positive-definite arguments throughout
the capped unitary orbit.

## 5. First outside calculation: a two-profile convex block crosses the PD barrier

The flat symbol \(1\) and \(r_c\) are both strictly below the new cap, so

\[
 r_\theta=(1-\theta)r_c+\theta
\tag{43}
\]

is admissible for \(0\le\theta\le1\).  This is not a translate or modulation
of \(r_c\).

Let \(R_2=\int r_c^2\).  From (41),

\[
 R_2=1.1514537923919\ldots .
\tag{44}
\]

At autocorrelation shift zero,

\[
 (\ell_{r_\theta}*\widetilde\ell_{r_\theta})(0)
 =\mu\{1+(1-\theta)^2(R_2-1)\}.
\tag{45}
\]

Therefore positive definiteness necessarily requires

\[
 \theta\ge
 1-\sqrt{\frac{\int p_\sigma^2/\mu-1}{R_2-1}}
 =0.4587281090\ldots .
\tag{46}
\]

Choose the simple rational value \(\theta=23/50=0.46\).  On each phase cut
by

\[
 0,\ \mu g,\ \frac{\mu(1-g)}2,\
 \frac{\mu(1+g)}2,\ \mu,\ 1,\ \sigma,
\tag{47}
\]

the autocorrelation difference

\[
 H_\theta(y)=
 (p_\sigma*\widetilde p_\sigma)(y)
 -(\ell_{r_\theta}*\widetilde\ell_{r_\theta})(y)
\tag{48}
\]

is a finite elementary trigonometric expression.  Directed evaluation of
those expressions gives

\[
\begin{array}{c|rrrrr}
y&0&0.12872425&0.185587875&0.314312125&0.4999\\ \hline
H_{23/50}(y)&
0.0001041233&0.17651886&0.23884171&0.23546756&0.41790158.
\end{array}
\tag{49}
\]

The phase derivatives place the minimum on \([0,\mu]\) at \(y=0\).  For
\(\mu\le |y|<\sigma\), the local autocorrelation vanishes and the global
autocorrelation is strictly positive.  Hence

\[
 H_{23/50}(y)\ge0\quad\hbox{for all }y,
\tag{50}
\]

with equality only at and beyond the endpoints of the global support.
Thus \(K_{23/50}\) is positive definite.  This is a completed constructive
step outside the killed capped orbit.

## 6. Exact one-/two-current insertion of the PD block

Positive definiteness includes diagonal self-energy, whereas the selector
contrast (17) is off diagonal.  The distinction is numerical here.

For the symbol (43) at \(\theta=23/50\), the accepted support-\(<2\)
second contraction is

\[
\begin{aligned}
 M_2(r_\theta)
 & =\int_{-1/2}^{1/2}(r_\theta-1)^2\,dt\\
 &\quad+\mu^2\iint_{[-1/2,1/2]^2}
 |t-u|r_\theta(t)r_\theta(u)\,dt\,du\\
 &=0.1317241060\ldots .
\end{aligned}
\tag{51}
\]

It follows that the complete compressed off-diagonal pair energy is

\[
\begin{aligned}
 \frac{J_{\mu,23/50}(\mathcal Z)}N
 &=\mu\{1+M_2(r_\theta)\}-\mu^2\\
 &=0.3158488706\ldots .
\end{aligned}
\tag{52}
\]

The full off-diagonal pair energy is at most \(D_\sigma-1<0.06771821\).
Therefore

\[
 T_\theta:=
 \frac{J_G(\mathcal Z)-J_{\mu,23/50}(\mathcal Z)}N
 <-0.2481306606.
\tag{53}
\]

This negative number gives a rigorous density-only adversary for the exact
current (20).  Uniformly mark a proportion \(z\) of the zero vertices as
simple, then choose a proportion \(p\) of those marked vertices.  With
\(\kappa=pz\), hypergeometric averaging gives

\[
 \mathbb E\frac{p\mathcal M_\theta-p^2\mathcal Q_\theta}{N}
 =(2\kappa-\kappa^2)T_\theta+o(1).
\tag{54}
\]

Since \(T_\theta<0\), (54) is negative for every \(0<\kappa\le z\).  In
particular, at \(\kappa=0.40750995\),

\[
 2\kappa-\kappa^2=0.6489555406\ldots,
\tag{55}
\]

and

\[
 \mathbb E\frac{p\mathcal M_\theta-p^2\mathcal Q_\theta}{N}
 <-0.1610257670.
\tag{56}
\]

Thus a theorem using only the simple density, positive definiteness, and the
global/local scalar pair totals cannot force the signed current in (20) to be
positive: the uniform-marking population obeys every such input and has the
opposite sign.  This is an impossibility theorem for that precisely defined
current class, not a request for a new estimate.

## Terminal handoff

The signed calculation has produced three closed facts.

1. The exact capped contrast changes sign at \(0.35192803\ldots\), and the
   optimal admissible nonnegative one-block domination radius is at most
   \(0.35201348\).  This is incompatible with the forced-gap threshold
   \(1.03896030\ldots\).
2. Every admissible translate/modulate of the capped block has the identical
   pair kernel and the identical negative spectral value (42), so neither
   optimization changes \(\Delta\).
3. The explicit outside profile \(r_{23/50}\) crosses the positive-definite
   barrier, but its completed one-/two-current value has the density-only
   adversary (56).  Positive definiteness is therefore insufficient after
   the mandatory diagonal deletion.

Accordingly the one-block pointwise/PD/density-only current class is
exhausted, and the operative unconditional theorem remains

\[
 \boxed{N_{0,\mathrm{simple}}(T,2T)/N(T,2T)
 >0.96250068026-o(1).}
\]

The explicit two-profile computation (43)--(56), rather than an open lemma,
is the completed first calculation outside the killed capped orbit.
