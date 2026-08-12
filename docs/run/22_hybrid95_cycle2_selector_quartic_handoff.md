# Hybrid 95, cycle 2: all-\(k\) weighted-translate ceiling and a conditioned selector--quartic identity

> **Superseded terminal branch.**  While this calculation was being closed,
> the zero-side nonflat-block certificate crossed 95 percent at the already
> proved support-two trace (reported terminal value \(95.06594\%\)).  The
> present file is therefore retained as a rigorous method-class kill and a
> reusable selector--quartic identity, not as the operative numerical record.
> No new branch is opened here.

## 0. Terminal outcome

The operative unconditional checkpoint has moved during this cycle.  The
support-\(<2\) pair trace and the exact nested-quartic fixed point now give

\[
 D_2=1.067717376064704\ldots,
 \qquad \beta_2=2-D_2=0.932282623935296\ldots,
\tag{1}
\]

\[
 \varepsilon_2=0.006030703115653\ldots,
 \qquad
 \boxed{s/N\ge \beta_2+\varepsilon_2
 =0.938313327050949\ldots .}
\tag{2}
\]

The cycle-1 three-translate increment and every refinement of it in the
overlapping weighted-three-window class are dominated by (2).  In fact, the
entire all-\(k\) class defined in Section 2 has the unconditional ceiling

\[
                         \boxed{0.93248},
\tag{3}
\]

more than \(0.00583\) below the current floor.  This is a precise class kill,
not merely a failed parameter search.

The first calculation outside that class is completed in Section 3.  If
\(K_{\mathcal L}\) is a PRZZ simple-zero selector, delete it *before* applying
the quartic stability tail.  With

\[
 S_{\mathcal L}
 ={2\operatorname{tr}(GK_{\mathcal L})
   -\|K_{\mathcal L}\|_F^2
   -\operatorname{tr}K_{\mathcal L}\over N}
\tag{4}
\]

and \(\tau_{\mathcal L}\) the residual nested-block stability tail, one gets
the exact additive joint certificate

\[
 \boxed{{s\over N}\ge
 \beta_2+S_{\mathcal L}+\tau_{\mathcal L}-o(1).}
\tag{5}
\]

Thus 95 percent is reduced to the single signed target

\[
 \boxed{S_{\mathcal L}+\tau_{\mathcal L}
       \ge0.017717376064704.}
\tag{6}
\]

If the residual retains the already-certified quartic tail
\(\tau_{\mathcal L}=\varepsilon_2\), the selector need supply only

\[
 S_{\mathcal L}\ge0.011686672949051,
\tag{7}
\]

which is \(26.59352\%\) of its thinning benchmark.  With no retained tail,
the requirement is \(40.31664\%\).  Equations (5)--(7), rather than a raw
translate increment below \(\beta_2\), are the terminal outside-class
handoff.

## 1. The optimized translate profile at support two

At \(\sigma=2\), the saturated-kernel Euler profile has no central piece.
Before mass normalization,

\[
 u_2(x)=A\cos(|x|-1/2)+B\sin(\sqrt3(|x|-1/2)),
 \qquad |x|\le1,
\tag{8}
\]

where

\[
 \begin{aligned}
 A&=0.8312256089421584\ldots,\\
 B&=-0.3551392921595534\ldots,\\
 M:=\int_{-1}^{1}u_2(x)\,dx
  &=1.594043141074803\ldots .
 \end{aligned}
\tag{9}
\]

Put

\[
 U_2(r)={2\over M}\int_0^1u_2(x)\cos(2\pi rx)\,dx,
 \qquad W_2(r)=|U_2(r)|^2.
\tag{10}
\]

The integral is an elementary finite sum of sine quotients.  All numerical
constants below use directed rounding of that closed form.

For reference, the unweighted disjoint-triple calculation from cycle 1 does
extend to this profile.  It gives

\[
 \mu_{3,2}(4)ge2.67\times10^{-5},
 \qquad
 {\beta_2-2\mu_{3,2}(4)/4\over1-2\mu_{3,2}(4)/3}
 =0.93228587\ldots .
\tag{11}
\]

Equation (11) is valid but is strictly dominated by (2), so it is not counted
as a terminal improvement.

## 2. Optimization and kill of the weighted three-window all-\(k\) class

### 2.1 Exact class

For \(B_0\ge0\), define the sharp local affine constant

\[
 A_3(B_0)=
 \inf_{a,b\ge0}
 \{W_2(a)+W_2(b)+W_2(a+b)+B_0(a+b)\}.
\tag{12}
\]

Let \(y_1<\cdots<y_k\) be one block of simple ordinates, put
\(g_i=y_{i+1}-y_i\), and sum (12) over its \(k-2\) consecutive triples.
Each adjacent edge occurs at most twice, every other edge at most once, and
each gap occurs in at most two triple spans.  Consequently

\[
 \sum_{1\le i<j\le k}W_2(y_j-y_i)+B_0(y_k-y_1)
 \ge {k-2\over2}A_3(B_0).
\tag{13}
\]

This includes arbitrary nonnegative mixtures of span cutoffs: integrating
the cutoff inequalities produces a convex span penalty, whose supporting
affine lines are exactly (12).  It also includes every block size \(k\ge3\).
Thus (13) is the optimized weighted-three-window class, not just the single
\(R=4\) construction.

Partition the simple ordinates into consecutive \(k\)-blocks.  Their spans
sum to at most \(N+o(N)\).  Writing \(z=s/N\), (13) and the residual union
identity give

\[
 z\ge\beta_2+2\left{
 {z\over k}{k-2\over2}A_3(B_0)-B_0\right}-o(1),
\]

and hence

\[
 \boxed{
 z\ge F_k(B_0):=
 {\beta_2-2B_0\over
  1-(1-2/k)A_3(B_0)}-o(1).}
\tag{14}
\]

For fixed \(B_0\), \(F_k(B_0)\) increases to

\[
 F_\infty(B_0)=
 {\beta_2-2B_0\over1-A_3(B_0)}.
\tag{15}
\]

Therefore a ceiling for (15) kills every finite \(k\) at once.

### 2.2 Explicit adversarial configurations

An upper bound for \(A_3(B_0)\) is enough to upper-bound the best possible
certificate (15).  Taking \(a=b=c\) in (12) gives

\[
 A_3(B_0)\le E(c)+2cB_0,
 \qquad E(c)=2W_2(c)+W_2(2c).
\tag{16}
\]

The following fixed configurations, evaluated from (10), form a piecewise
linear upper envelope for all \(B_0\ge0\):

\[
\begin{array}{c|c|c}
c&2c&E(c)\ \hline
19.5011252813&39.0022505626&2.5050\times10^{-9}\\
2.0155663916&4.0311327832&1.4880\times10^{-5}\\
1.5216804201&3.0433608402&4.8370\times10^{-5}\\
1.0327831958&2.0655663916&2.1720\times10^{-4}\\
1.0277944486&2.0555888972&2.4637\times10^{-4}\\
0.5788072018&1.1576144036&3.5290\times10^{-3}.
\end{array}
\tag{17}
\]

The collapsed configuration handles the remaining large-\(B_0\) tail.
Maximizing (15) with \(A_3(B_0)\) replaced by the minimum of the affine
majorants in (17) is a finite one-variable calculation.  Its maximum occurs
near \(B_0=1.725\times10^{-4}\) and is

\[
                         F_\infty(B_0)<0.93248.
\tag{18}
\]

Because the true \(A_3\) is no larger than that envelope, (18) is an upper
bound on what the entire method class can prove.  Combining (14)--(18),

\[
 \boxed{
 \sup_{k\ge3}\sup_{B_0\ge0}F_k(B_0)<0.93248
 <0.938313327050949.}
\tag{19}
\]

This proves the announced class impossibility.  The obstruction is not a
poor choice of \(k\), cutoff, or positive weight: sparse near-zero translate
patterns (17) defeat all of them.

## 3. Outside the killed class: delete the selector, then retain the quartic tail

Let \(\mathcal L\) be a set of \(\kappa N+o(N)\) certified simple critical-line
zeros, with

\[
 \kappa=0.40750995,
 \qquad
 K=\sum_{\gamma\in\mathcal L}B_\gamma,
 \qquad R=G-K.
\tag{20}
\]

Normalize

\[
 x={\operatorname{tr}(GK)\over N},
 \qquad q={\|K\|_F^2\over N},
 \qquad S_{\mathcal L}=2x-q-\kappa.
\tag{21}
\]

Then

\[
 \operatorname{tr}R=(1-\kappa)N+o(N),
 \qquad
 \|R\|_F^2=(D_2-2x+q)N+o(N).
\tag{22}
\]

The nonsimple positive-index budget is unchanged by deleting simple atoms.
Apply the stability lemma to \(R\), and let \(C_R\) be its nested principal
compression.  If \(b\) is the nonsimple positive-index count, define

\[
 \tau_{\mathcal L}={1\over N}
 \sum_{j>b}(\lambda_j(C_R)-1)_+^2\ge0.
\tag{23}
\]

The residual stability inequality is

\[
 \tau_{\mathcal L}N
 \le (s-\kappa N)
 -\{2(1-\kappa)N-\|R\|_F^2\}+o(N).
\tag{24}
\]

Substituting (21)--(22) into (24) proves, with no independence assumption,

\[
 \boxed{{s\over N}\ge
 2-D_2+(2x-q-\kappa)+\tau_{\mathcal L}-o(1),}
\tag{25}
\]

which is (5).

This is the compatibility/additivity statement that was absent from the raw
translate route: the selector score changes the residual second trace, while
the quartic term is the spectral tail that remains *after* deletion.  They are
separate terms in (24), so no double counting occurs.

### 3.1 Exact numerical gates

At \(D_2\),

\[
 0.95-\beta_2=0.017717376064704,
\tag{26}
\]

so (25) proves 95 percent precisely under (6).  It improves the current floor
as soon as

\[
 S_{\mathcal L}+\tau_{\mathcal L}
 >\varepsilon_2=0.006030703115653.
\tag{27}
\]

The thinning benchmark for the PRZZ selector is

\[
 S_{\rm th}=\kappa(2-\kappa)(D_2-1)
 =0.043945566395537.
\tag{28}
\]

Hence:

\[
\begin{array}{c|c|c}
\text{retained residual tail}&S_{\mathcal L}\text{ needed for }95\%&
\text{fraction of thinning}\\ \hline
0&0.017717376064704&0.4031664060\\
\varepsilon_2/2&0.014702024506878&0.334553\ldots\\
\varepsilon_2&0.011686672949051&0.2659351991
\end{array}
\tag{29}
\]

Thus conditioning on the residual quartic tail removes one third of the
selector burden relative to the unconditioned residual union.

### 3.2 A two-statistic sufficient condition with no tail symbol

Let \(P_\mu\) be the nested-block projection and put

\[
 C=P_\mu GP_\mu,
 \qquad C_K=P_\mu KP_\mu,
 \qquad C_R=C-C_K,
 \qquad
 q_{\mu,\mathcal L}={\|C_K\|_F^2\over N}.
\tag{30}
\]

For

\[
 T_b(A)=\sum_{j>b}(\lambda_j(A)-1)_+^2,
\]

Hoffman--Wielandt and the \(1\)-Lipschitz property of the trimmed positive
spectral vector give

\[
 \left|\sqrt{T_b(C)}-\sqrt{T_b(C_R)}\right|
 \le\|C_K\|_F.
\tag{31}
\]

The unconditional quartic fixed point gives \(T_b(C)/N\ge\varepsilon_2-o(1)\).
Therefore

\[
 \boxed{
 \tau_{\mathcal L}\ge
 \left(\sqrt{\varepsilon_2}
       -\sqrt{q_{\mu,\mathcal L}}\right)_+^2-o(1).}
\tag{32}
\]

Combining (25) and (32), a completely explicit sufficient condition for
95 percent is

\[
 \boxed{
 2x-q-\kappa+
 \left(\sqrt{0.006030703115653}
       -\sqrt{q_{\mu,\mathcal L}}\right)_+^2
 \ge0.017717376064704.}
\tag{33}
\]

This retains the favorable selector combination \(2x-q\) and charges only
the part of the nested stability tail actually absorbed by the selector.
It is the concrete arithmetic target for a PRZZ one-ratio calculation.

For scale, if the selector supplies \(30\%\) of thinning, then

\[
 S_{\mathcal L}=0.013183669918661
\]

and (33) closes provided

\[
 q_{\mu,\mathcal L}\le0.000106601503.
\tag{34}
\]

At \(40\%\) of thinning, the corresponding allowance is

\[
 q_{\mu,\mathcal L}\le0.00433772887.
\tag{35}
\]

Equations (33)--(35) are the first executed inequality outside the killed
translate class.  They identify exactly two joint PRZZ observables and their
signs; no scalar headline proportion can substitute for them.

## 4. Handoff

The next hybrid calculation should evaluate, in one contour expansion,

\[
 \left(2\operatorname{tr}(GK)-\|K\|_F^2\right)/N
 \quad\text{and}\quad
 \|P_\mu KP_\mu\|_F^2/N,
\]

for the same canonical PRZZ selector.  The terminal comparison is (33), not
separate estimates for \(x\) and \(q\).  Further positive mixtures of local
three-translate inequalities should not be pursued: (19) proves that their
entire all-\(k\) closure remains below even the unrefined support-two base.
