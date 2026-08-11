# Hybrid 100, cycle 2: deletion-stable tail and the signed Levinson contrast current

## Terminal outcome

Keep the fixed strict support-\(1.9999\) inputs

\[
D\leq1.06772567,\qquad
\beta=2-D=0.93227433,
\tag{1}
\]

and the capped-profile tail

\[
\tau_0>0.03021584923.
\tag{2}
\]

The inherited floor is therefore

\[
\beta+\tau_0=0.96249017923.
\tag{3}
\]

This cycle does not claim a new unconditional constant.  It closes a precise
method class and completes the first calculation outside it.

The new constructive result is a deletion theorem with no diagonal
Frobenius loss.  If \(\mathcal L\) is a hard simple-zero selector, let
\(J_G(\mathcal L)\) be the global pair energy covered by the selector and
let \(J_\mu(\mathcal L)\) be the corresponding covered pair energy after
compression to the capped block.  Then the tail which survives deletion
satisfies

\[
\boxed{\displaystyle
\tau_{\mathcal L}\geq
\left(\tau_0-\frac{J_\mu(\mathcal L)}N\right)_+-o(1).}
\tag{4}
\]

Consequently the exact residual identity gives

\[
\boxed{\displaystyle
\frac{s}{N}\geq
\beta+\tau_0+
\frac{J_G(\mathcal L)-J_\mu(\mathcal L)}N-o(1).}
\tag{5}
\]

Thus the completed loss calculation changes the selector target from a
global score to the signed contrast score

\[
\Delta(\mathcal L):=
\frac{J_G(\mathcal L)-J_\mu(\mathcal L)}N.
\tag{6}
\]

It improves (3) as soon as \(\Delta(\mathcal L)>0\), and it proves density
one if

\[
\boxed{\Delta(\mathcal L)\geq
D-1-\tau_0=0.03750982077.}
\tag{7}
\]

The ordinary scalar/random Levinson class cannot prove (7).  Its
Hoffman--Wielandt tail is identically zero at the present parameters, its
random-thinning local-loss benchmark is \(0.24078\ldots\), and a
three-atom compression below destroys positive tail with exactly zero
global selector score.  This is the precise class kill.

Outside that class, the positive Levinson intersection current evaluates
the one-current and two-current pieces of \(\Delta\) exactly.  For a
uniform \(k\)-subset of the simple current, with \(p=k/s\), the completed
selector formula is

\[
\boxed{\displaystyle
\mathbb E\,\Delta(\mathcal L)
=\frac{p\mathcal M_\Delta-p^2\mathcal Q_\Delta}{N}+o(1).}
\tag{8}
\]

The quantities \(\mathcal M_\Delta,\mathcal Q_\Delta\) are explicitly
defined weighted topological currents below; (8) is an identity, not a
selector-existence lemma.  In particular, at least one hard selector
attains its right side.

## 1. Exact additive selector identity

Let

\[
G=\sum_{\rho}B_\rho,\qquad
K=\sum_{\gamma\in\mathcal L}B_\gamma,\qquad
R=G-K,
\tag{9}
\]

where each \(B_\rho\) is a normalized rank-one zero atom and
\(\mathcal L\) consists only of simple critical-line zeros.  Put

\[
\kappa=\frac{|\mathcal L|}{N},\qquad
x=\frac{\operatorname{tr}(GK)}N,\qquad
q=\frac{\|K\|_F^2}{N},
\tag{10}
\]

and

\[
S_{\mathcal L}=2x-q-\kappa.
\tag{11}
\]

Deleting the selected atoms before applying the rank--trace stability
inequality gives the already established exact identity

\[
\boxed{\displaystyle
\frac{s}{N}\geq
\beta+S_{\mathcal L}+\tau_{\mathcal L}-o(1).}
\tag{12}
\]

For unordered pairs of distinct atoms write

\[
e_{ij}=\operatorname{tr}(B_iB_j)\geq0.
\tag{13}
\]

Expanding (11) shows that

\[
S_{\mathcal L}
=\frac2N
\sum_{\substack{i<j\\i\in\mathcal L\ {\rm or}\ j\in\mathcal L}}
e_{ij}
=\frac{J_G(\mathcal L)}N.
\tag{14}
\]

Hence \(S_{\mathcal L}\) is exactly covered global pair energy; no
independence assumption appears in (12) or (14).

For reference, if the whole tail (2) survived, density one would require

\[
S_{\mathcal L}\geq0.03750982077.
\tag{15}
\]

The old thinning benchmark \(S_{\rm th}=0.0439455664\ldots\) exceeds
(15), but only by

\[
0.0064357456\ldots .
\tag{16}
\]

Thus at that benchmark at least

\[
\tau_{\mathcal L}\geq
0.0237801036\ldots
\tag{17}
\]

must remain: no more than \(0.0064357456\ldots\), or \(21.30\%\), of the
capped tail may be lost.

## 2. Why the Frobenius deletion bound is terminally too expensive

Let \(P_\mu\) be the capped-block projection and set

\[
C=P_\mu GP_\mu,\qquad
C_K=P_\mu KP_\mu,\qquad
C_R=C-C_K.
\tag{18}
\]

The usual Hoffman--Wielandt estimate is

\[
\tau_{\mathcal L}\geq
\left(\sqrt{\tau_0}
-\frac{\|C_K\|_F}{\sqrt N}\right)_+^2-o(1).
\tag{19}
\]

At the ideal score in (16), (19) proves density one only if

\[
\frac{\|C_K\|_F^2}{N}
\leq0.0003849083\ldots .
\tag{20}
\]

But the accepted mean-one translation normalization gives, uniformly for
interior atoms,

\[
\operatorname{tr}(P_\mu B_\gamma P_\mu)=\mu+o(1),
\qquad \mu=0.4999.
\tag{21}
\]

The diagonal rank-one terms alone therefore force

\[
\frac{\|C_K\|_F^2}{N}
\geq\kappa\mu^2-o(1)
=0.1018367405\ldots-o(1)
\tag{22}
\]

for \(\kappa=0.40750995\).  Thus (19) always returns zero on a
positive-density selector.  Any useful loss theorem must cancel the
diagonal self-energy exactly.

## 3. Rank-one deletion theorem with exact self-energy cancellation

For a positive semidefinite matrix \(X\), define the trimmed tail

\[
T_b(X)=\sum_{j>b}(\lambda_j(X)-1)_+^2,
\tag{23}
\]

with eigenvalues in decreasing order.

### Lemma

Let \(R\succeq0\) and \(A=uu^*\) with
\(a=\operatorname{tr}A=\|u\|^2\leq1\).  Then

\[
\boxed{T_b(R+A)-T_b(R)\leq2\operatorname{tr}(AR).}
\tag{24}
\]

### Proof

Put

\[
f(x)=(x-1)_+^2,\qquad
d(x)=x^2-f(x)
=\begin{cases}
x^2,&0\leq x\leq1,\\
2x-1,&x\geq1.
\end{cases}
\tag{25}
\]

The function \(d\) is increasing and convex on \([0,\infty)\), with
\(d(0)=0\).  The trace superadditivity inequality for such convex
functions gives

\[
\operatorname{tr}d(R+A)
\geq\operatorname{tr}d(R)+\operatorname{tr}d(A).
\tag{26}
\]

Since \(A\) has the single nonzero eigenvalue \(a\leq1\),
\(\operatorname{tr}d(A)=a^2\).  Hence

\[
\begin{aligned}
\operatorname{tr}f(R+A)-\operatorname{tr}f(R)
&=\operatorname{tr}\{(R+A)^2-R^2\}\\
&\quad-\operatorname{tr}\{d(R+A)-d(R)\}\\
&\leq2\operatorname{tr}(AR)+a^2-a^2.
\end{aligned}
\tag{27}
\]

This proves (24) for \(b=0\).  For \(b>0\), subtract the first \(b\)
terms \(f(\lambda_j)\).  Weyl monotonicity gives
\(\lambda_j(R+A)\geq\lambda_j(R)\), and \(f\) is increasing, so the
increment of the subtracted top-\(b\) sum is nonnegative.  The trimmed
increment is therefore no larger than the untrimmed one in (27).

### Telescoping a hard selector

Write

\[
A_\gamma=P_\mu B_\gamma P_\mu.
\tag{28}
\]

Delete the atoms of \(\mathcal L\) in any fixed order.  At the step which
deletes \(A_\gamma\), apply (24) with \(R\) equal to the sum of all atoms
not yet deleted.  Every selected--unselected compressed pair is counted
once, and every selected--selected pair is counted once, at the earlier
of its two deletion times.  Thus

\[
T_b(C)-T_b(C_R)
\leq J_\mu(\mathcal L),
\tag{29}
\]

where

\[
J_\mu(\mathcal L)=
2\sum_{\substack{i<j\\i\in\mathcal L\ {\rm or}\ j\in\mathcal L}}
\operatorname{tr}(A_iA_j).
\tag{30}
\]

The original capped certificate gives \(T_b(C)\geq\tau_0N-o(N)\).
Equations (29)--(30) prove (4).  Combining (4), (12), and (14) gives
(5).  This is the requested deletion-loss calculation: it charges no
self-term and states exactly how much of the capped tail survives.

## 4. Exact numerical gates after the loss calculation

There are two useful forms.

First, without replacing the positive part in (4),

\[
\frac{s}{N}\geq
\beta+\frac{J_G(\mathcal L)}N+
\left(\tau_0-\frac{J_\mu(\mathcal L)}N\right)_+-o(1).
\tag{31}
\]

Therefore:

* if \(J_\mu(\mathcal L)\leq\tau_0N\), density one follows from

\[
\frac{J_G(\mathcal L)-J_\mu(\mathcal L)}N
\geq0.03750982077;
\tag{32}
\]

* if \(J_\mu(\mathcal L)>\tau_0N\), this deletion theorem retains no
tail, and density one requires \(J_G(\mathcal L)/N\geq0.06772567\).

Second, the weaker but affine form

\[
\frac{s}{N}\geq\beta+\tau_0+\Delta(\mathcal L)-o(1)
\tag{33}
\]

is valid in both cases because \(x_+\geq x\).  It gives the clean terminal
tests

\[
\Delta(\mathcal L)>0
\quad\Longrightarrow\quad
\text{strict improvement of (3)},
\tag{34}
\]

\[
\Delta(\mathcal L)\geq0.03750982077
\quad\Longrightarrow\quad
s/N\geq1-o(1).
\tag{35}
\]

At the old ideal global score, (32) allows only

\[
\frac{J_\mu(\mathcal L)}N
\leq0.0064357456\ldots ,
\tag{36}
\]

which is the loss allowance stated in (16)--(17).

## 5. Weighted Levinson selector with no selection lemma

Let \(\mathscr S\) be the set of all simple critical-line atoms in the
trimmed window.  The completed positive-intersection identity gives

\[
d\mathcal I_a=dN_0^s.
\tag{37}
\]

Thus every bounded weight of a simple zero can be summed exactly against
\(d\mathcal I_a\); the sign and smoothness of the weight are irrelevant
to the topological statement.

For distinct atoms define the signed contrast kernel

\[
k_\Delta(\gamma,\rho)
=\operatorname{tr}(B_\gamma B_\rho)
-\operatorname{tr}(A_\gamma A_\rho).
\tag{38}
\]

Its simple marginal is

\[
m_\Delta(\gamma)=
2\sum_{\rho\ne\gamma}k_\Delta(\gamma,\rho).
\tag{39}
\]

Define the exact one-current and ordered two-current

\[
\mathcal M_\Delta
=\int m_\Delta(t)\,d\mathcal I_a(t),
\tag{40}
\]

\[
\mathcal Q_\Delta
=\iint_{t\ne u}k_\Delta(t,u)\,
d\mathcal I_a(t)d\mathcal I_a(u).
\tag{41}
\]

If \(E_{SS}^\Delta\) and \(E_{SR}^\Delta\) are the unordered
simple--simple and simple--residual contrast sums, then exactly

\[
\mathcal M_\Delta=4E_{SS}^\Delta+2E_{SR}^\Delta,
\qquad
\mathcal Q_\Delta=2E_{SS}^\Delta.
\tag{42}
\]

Take a uniformly random \(k\)-subset of \(\mathscr S\), and put

\[
p=\frac{k}{s},\qquad
r_{s,k}=1-\frac{(s-k)(s-k-1)}{s(s-1)}
=2p-p^2+o(1).
\tag{43}
\]

A simple--residual edge is covered with probability \(p\), and a
simple--simple edge with probability \(r_{s,k}\).  Equations (42)--(43)
give

\[
\begin{aligned}
\mathbb E\{J_G(\mathcal L)-J_\mu(\mathcal L)\}
&=2r_{s,k}E_{SS}^\Delta+2pE_{SR}^\Delta\\
&=p\mathcal M_\Delta-p^2\mathcal Q_\Delta+o(N).
\end{aligned}
\tag{44}
\]

This proves (8).  Since an average of finitely many hard selectors is no
larger than their maximum, one actual \(k\)-element selector attains the
right side.  There is no unproved selector lemma.

For \(k=0.40750995N\) and the present
\(0.96249017923N\leq s\leq N\),

\[
0.40750995\leq p\leq0.42339129.
\tag{45}
\]

The exact topological stopping conditions are therefore

\[
\frac{p\mathcal M_\Delta-p^2\mathcal Q_\Delta}{N}>0
\tag{46}
\]

for a strict improvement, and

\[
\boxed{\displaystyle
\frac{p\mathcal M_\Delta-p^2\mathcal Q_\Delta}{N}
\geq0.03750982077}
\tag{47}
\]

for density one.

Equations (40)--(47) are the concrete weighted Levinson coupling:
the one-current rewards global marginal energy and the two-current removes
the double counting, while the identical pair current for the compressed
block is the deletion loss.

## 6. Precise kill of scalar, Frobenius, and random-loss selectors

Define the scalar deletion class to consist of arguments which use only

1. the selector cardinality or the scalar Levinson count;
2. the global score \(S_{\mathcal L}\);
3. the undeleted scalar tail \(\tau_0\); and
4. either Hoffman--Wielandt, a universal loss bound in terms of
   \(S_{\mathcal L}\), or an unweighted/random allocation of compressed
   pair energy.

This entire defined class is insufficient here.

### 6.1 Hoffman--Wielandt is zero

Equations (20)--(22) prove this quantitatively: the permitted squared norm
is \(3.85\times10^{-4}\), while the unavoidable diagonal is larger than
\(0.1018\).

### 6.2 Global score cannot control deletion loss

There is an exact three-atom compression obstruction.  In
\(\mathbb C^2\), put

\[
v=\frac{e_1+e_2}{\sqrt2},\qquad
w=\frac{e_1-e_2}{\sqrt2},
\tag{48}
\]

take one selected atom \(B_v\), two unselected copies \(B_w,B_w\), and
let \(P\) project onto \(\mathbb Ce_1\).  Then

\[
\langle v,w\rangle=0,
\tag{49}
\]

so the selected atom has exactly zero global selector score.  But

\[
P(B_v+2B_w)P=\frac32P,\qquad
P(2B_w)P=P.
\tag{50}
\]

For \(b=0\), the tail before deletion is \(1/4\), and the tail after
deletion is zero.  Thus positive tail can be destroyed with
\(S_{\mathcal L}=0\).  Direct sums, isolated atoms, and an arbitrarily
small perturbation of \(P\) give the same obstruction at positive density
and at the strict width \(0.4999\).  Hence no universal
\(\text{loss}\leq F(S_{\mathcal L})\) with \(F(0)=0\) can replace the
signed contrast current.

### 6.3 Random compressed energy has the wrong scale

For the capped profile, the accepted moment bound is

\[
M_2>0.242110.
\tag{51}
\]

The complete compressed pair energy of all zero atoms is

\[
\begin{aligned}
\frac{J_\mu(\mathcal Z)}N
&=\frac{\|C\|_F^2-\sum_\rho\|A_\rho\|_F^2}{N}\\
&=\mu(1+M_2)-\mu^2\\
&>0.371030779.
\end{aligned}
\tag{52}
\]

By contrast,

\[
\frac{J_G(\mathcal Z)}N=D-1\leq0.06772567.
\tag{53}
\]

At density \(\kappa=0.40750995\), the random edge-coverage factor is

\[
\kappa(2-\kappa)=0.6489555406\ldots .
\tag{54}
\]

Consequently the random compressed-loss benchmark is

\[
0.6489555406\ldots\times0.371030779
>0.24078247,
\tag{55}
\]

while the random global score benchmark is only

\[
0.6489555406\ldots\times0.06772567
=0.04395094\ldots .
\tag{56}
\]

The random contrast is therefore less than \(-0.19683\), not the positive
\(0.03750982\) required in (47).  Scalar thinning is killed even after
the exact diagonal cancellation of Section 3.

## 7. First calculation outside the killed class

The statistic in (47) is arithmetic within the already proved strict
bandwidth.  In the translation model,

\[
\operatorname{tr}(B_tB_u)=W_\sigma(t-u),
\qquad
\operatorname{tr}(A_tA_u)=W_\mu^{(r)}(t-u),
\tag{57}
\]

where \(W_\sigma\) is the full support-\(1.9999\) pair kernel and
\(W_\mu^{(r)}\) is the pair kernel of the capped symbol.  Therefore

\[
k_\Delta(t,u)=
W_\sigma(t-u)-W_\mu^{(r)}(t-u).
\tag{58}
\]

The full term has Fourier support strictly below \(2\), and every
compressed fourth product has support

\[
4\mu=1.9996<2.
\tag{59}
\]

Thus both currents in (40)--(41), including the simple--simple correction,
remain inside the proved arithmetic bandwidth.  No supercritical prime
correlation is introduced by the deletion calculation.

There is also a finite polynomial display of the loss insertion.  Let
\(Y=C-I\), \(A=uu^*\), \(a=\operatorname{tr}A\), and use the fixed capped
quartic

\[
P(y)=P_0+P_1y+P_2y^2+P_3y^3+P_4y^4.
\tag{60}
\]

Direct noncommutative expansion gives

\[
\begin{aligned}
\operatorname{tr}\{P(Y)-P(Y-A)\}
={}&c_0+c_1\,u^*Yu+c_2\,u^*Y^2u+c_3\,u^*Y^3u\\
&+c_{11}(u^*Yu)^2,
\end{aligned}
\tag{61}
\]

where, at \(a=\mu=0.4999\) and with the rational dual from the capped
certificate,

\[
\begin{aligned}
c_0&=-0.0252064880\ldots,\\
c_1&=\phantom{-}0.6205951469\ldots,\\
c_2&=\phantom{-}1.5870094614\ldots,\\
c_3&=-1.9753076253\ldots,\\
c_{11}&=\phantom{-}0.9876538126\ldots .
\end{aligned}
\tag{62}
\]

The exact coefficient identities are

\[
\begin{aligned}
c_0&=P_1a-P_2a^2+P_3a^3-P_4a^4,\\
c_1&=2P_2-3aP_3+4a^2P_4,\\
c_2&=3P_3-4aP_4,\qquad
c_3=4P_4,\qquad c_{11}=-2P_4.
\end{aligned}
\tag{63}
\]

Every term in (61) has total trace bandwidth at most \(4\mu<2\).  Thus
(61)--(63) are the first explicit mixed prime-side insertion for the
selector loss; the favorable combination is the global selector marginal
minus (61), before any absolute value.

This calculation also explains why simply reusing the old quartic witness
after deletion is not enough.  For an isolated compressed atom,
\(u^*Y^ju=a(a-1)^j\), and (61) equals

\[
P(a-1)-P(-1)=0.2032950490\ldots ,
\tag{64}
\]

although its actual thresholded tail loss is zero.  The polynomial witness
charges negative-spectrum motion which the true tail ignores.  Therefore
the fixed-quartic-reuse subclass is killed as well; the thresholded
rank-one theorem (24) and the signed current (58) are essential.

Finally, substituting the positive intersection current into (40)--(41)
gives the exact phase-current representation

\[
\mathcal M_\Delta
=\int m_\Delta(t)\,d\mathcal I_a(t),\qquad
\mathcal Q_\Delta
=\iint_{t\ne u}k_\Delta(t,u)\,
d\mathcal I_a(t)d\mathcal I_a(u).
\tag{65}
\]

The first object is a one-ratio insertion and the second is its
simple--simple two-current correction.  Their required signed combination
is already fixed numerically by (47); estimating them separately by
absolute values returns the killed random benchmark (55)--(56).

## Terminal handoff

The branch terminates by the second allowed gate:

* **Precise class kill.**  Scalar-count, Hoffman--Wielandt,
  global-score-only, random-thinning, and unchanged-quartic deletion
  arguments cannot retain enough of the \(0.03021584923\) capped tail.
  Equations (20)--(22), (48)--(56), and (64) give explicit obstructions.
* **Completed loss theorem.**  The rigorous surviving tail is (4), obtained
  from the rank-one deletion inequality (24), with no diagonal charge.
* **First calculation outside the killed class.**  The exact hard-selector
  contrast is (44), its strict numerical targets are (46)--(47), and its
  mixed support-\(<2\) insertion is expanded in (61)--(63).

The operative unconditional number from this branch remains
\(0.96249017923\).  Any positive lower bound in (46) is now automatically a
strict improvement; the density-one gate is the single signed current
(47), not a new selector lemma.
