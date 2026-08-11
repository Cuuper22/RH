# Hybrid cycle 7: the weighted Levinson intersection current

## Outcome

There is a canonical weighted Levinson selector; no choice of sign-change
intervals is needed.  For the completed linear perturbation, every simple
critical-line zero is a transverse crossing of the imaginary axis with
the same positive orientation, while every multiple zero is a zero of the
perturbed curve itself.  Thus the positive intersection current is
**exactly** the simple-zero counting measure.

Combining this current with the support-(5/4) residual Gram identity gives
the following numerical terminal gate.  Let

\[
 D=1.20278584713866\ldots,qquad
 \beta=2-D=0.79721415286134\ldots .
\tag{1}
\]

For a simple-zero atom (B_\gamma), define its non-diagonal Gram marginal

\[
 m_T(\gamma)=2\{\operatorname{tr}(G_TB_\gamma)-1\}\ge0,
\tag{2}
\]

and put

\[
                  M_s(T)=\sum_{\gamma\ {m simple\ line}}m_T(\gamma).
\tag{3}
\]

Then the residual certificate proves

\[
 \boxed{
 {N_0^s(T,2T)\over N(T,2T)}
 \ge \beta+{M_s(T)\over2N(T,2T)}-o(1).}
\tag{4}
\]

Consequently the exact weighted-Levinson target is

\[
 \boxed{M_s(T)\ge
 0.10557169427732\ldots,N(T,2T).}
\tag{WL85}
\]

This is stronger and cleaner than first forcing a hard
(0.40750995N)-element selector.  If one insists on that cardinality,
random fixed-size deletion shows that the sufficient marginal threshold is

\[
 M_s(T)\ge0.1626793945\ldots,N(T,2T).
\tag{5}
\]

The topology below is proved.  What is not forced by the accepted scalar
inputs is a positive value of (3).  A sharp finite model at the end of this
handoff proves that every method using only the scalar Levinson count,
(\operatorname{tr}G), and (\|G\|_F^2) can have (M_s=0).  Hence that
defined class is terminated.  The unconditional numerical output of this
cycle remains the new support-(5/4) baseline (79.721415286134\%\).

## 1. The positive intersection-current lemma

Write

\[
 \xi(s)=H(s)\zeta(s),\qquad
 \Xi(t)=\xi(\tfrac12+it)\in\mathbb R,qquad
 L=\log(T/2\pi),
\tag{6}
\]

and, for (a>1/2+\varepsilon), set

\[
 V_a(s)=\zeta(s)+{\zeta'(s)\over aL},\qquad
 E_a(t)=H(\tfrac12+it)V_a(\tfrac12+it).
\tag{7}
\]

Since (d\Xi/dt=i\xi'), one has the exact identity

\[
 E_a(t)=
 \left(1-{H'\over aLH}(\tfrac12+it)\right)\Xi(t)
 -{i\over aL}\Xi'(t).
\tag{8}
\]

Put (u_a=\Re E_a, v_a=\Im E_a), and

\[
 A_a(t)=1-{1\over aL}\Re {H'\over H}(\tfrac12+it).
\tag{9}
\]

Uniformly on a trimmed dyadic window,
(A_a(t)=1-(2a)^{-1}+o(1)>0), and (8) gives

\[
 u_a(t)=A_a(t)\Xi(t).
\tag{10}
\]

Define the oriented imaginary-axis intersection measure by

\[
 d\mathcal I_a(t)=
 \sum_{\substack{u_a(\gamma)=0\\E_a(\gamma)\ne0}}
 \operatorname{sgn}\{-v_a(\gamma)u_a'(\gamma)\}\,\delta_\gamma.
\tag{11}
\]

**Weighted Levinson intersection lemma.**  On the trimmed window,

\[
 \boxed{d\mathcal I_a(t)=dN_0^s(t).}
\tag{12}
\]

In particular, for every bounded Borel weight (h), with no sign or
smoothness restriction,

\[
 \int h(t)\,d\mathcal I_a(t)
 =\sum_{\gamma\ {m simple\ line}}h(\gamma).
\tag{13}
\]

### Proof

By (10), a point counted in (11) is a zero of (\Xi).  If it has
multiplicity one, (8)--(10) give

\[
 v_a(\gamma)=-{\Xi'(\gamma)\over aL},\qquad
 u_a'(\gamma)=A_a(\gamma)\Xi'(\gamma),
\tag{14}
\]

and hence

\[
 -v_a(\gamma)u_a'(\gamma)
 ={A_a(\gamma)\over aL}\,\Xi'(\gamma)^2>0.
\tag{15}
\]

Thus every simple zero contributes (+1).  If the multiplicity is at
least two, then (\Xi(\gamma)=\Xi'(\gamma)=0), so (8) gives
(E_a(\gamma)=0); it is excluded by (11).  There are no other crossings.
This proves (12)--(13).  Notice that this is a local identity, not an
asymptotic count or a request for a future selector lemma.

The usual scalar Levinson argument is the special case (h=1), followed
by an argument-principle upper bound for the zeros of (E_a\psi).  Formula
(13) is the weighted topological statement that is lost when that last
step is immediately averaged.

## 2. Phase form of the same lemma

For later arithmetic insertion, (13) has an exact phase form.  On every
component on which (E_a\ne0), choose a continuous phase
(\Theta_a=\arg E_a), and put

\[
 \mathfrak s(x)=left\lfloor{x+\pi/2\over\pi}\right\rfloor-{x\over\pi}.
\tag{16}
\]

The function (\mathfrak s) is (\pi)-periodic and bounded.  Pulling the
Stieltjes derivative of the first term in (16) back along (\Theta_a)
counts the oriented imaginary-axis crossings.  Therefore, after deleting
small symmetric intervals around the zeros of (E_a), integration by
parts gives

\[
\begin{aligned}
 \sum_{\gamma\ {m simple}}h(\gamma)
 ={}&{1\over\pi}\int h(t)\,
       \Im {d\over dt}\log E_a(t)\,dt\\
 &-\int h'(t)\mathfrak s(\Theta_a(t))\,dt
 +\mathcal B_a(h).
\end{aligned}
\tag{17}
\]

Here (\mathcal B_a(h)) is the explicit sum of the endpoint terms
([h\mathfrak s(\Theta_a)]) over those components.  Thus it includes the
two outer endpoints and the two sides of every deleted zero of (E_a).
Equation (17) is an identity; letting the deleted radii tend to zero
reproduces exactly the exclusion in (11).

The Fourier series

\[
 \mathfrak s(x)=\sum_{k\ge1}{(-1)^k\over\pi k}\sin(2kx)
\tag{18}
\]

shows precisely what a weighted Levinson calculation needs.  The scalar
case has (h'=0); a nonconstant Gram weight introduces ratios

\[
 e^{2ik\Theta_a(t)}=left({E_a(t)\over\overline{E_a(t)}}\right)^k.
\tag{19}
\]

This is why an ordinary mollified second moment cannot recover the
selector after the fact.

## 3. Coupling the current to the residual Gram matrix

Let (\mathscr S) be the full set of simple critical-line atoms and

\[
 K_{\mathscr S}=\sum_{\gamma\in\mathscr S}B_\gamma,qquad
 R_{\mathscr S}=G_T-K_{\mathscr S}.
\tag{20}
\]

Applying the support-(5/4) rank--trace inequality to
(R_{\mathscr S}), which contains no simple-line atom, gives exactly

\[
 {N_0^s\over N}\ge
 \beta+{1\over N}\left{
 2\operatorname{tr}(G_TK_{\mathscr S})
 -\|K_{\mathscr S}\|_F^2-\operatorname{tr}K_{\mathscr S}
 \right}-o(1).
\tag{21}
\]

For unordered distinct-atom pairs put
(e_{ij}=\operatorname{tr}(B_iB_j)\ge0).  If (E_{SS}) is the sum over
simple--simple pairs and (E_{SR}) the sum over simple--residual pairs,
then the brace in (21) is

\[
                    J(\mathscr S)=2E_{SS}+2E_{SR}.
\tag{22}
\]

On the other hand, (2)--(3) give

\[
 M_s=4E_{SS}+2E_{SR}.
\tag{23}
\]

Consequently (J(\mathscr S)\ge M_s/2), proving (4) and (WL85).
By (12), the marginal is now attached directly to the topological current:

\[
 \boxed{M_s=\int m_T(t)\,d\mathcal I_a(t).}
\tag{24}
\]

This is the desired weighted Levinson--Gram coupling.

For completeness, if (s=|\mathscr S|) and (k\le s), a uniformly
random (k)-subset covers a simple--simple edge with probability

\[
 r_{s,k}=1-{(s-k)(s-k-1)\over s(s-1)}
\tag{25}
\]

and a simple--residual edge with probability (k/s).  Hence some hard
selector (\mathcal L), (|\mathcal L|=k), satisfies

\[
 J(\mathcal L)\ge{r_{s,k}\over2}M_s.
\tag{26}
\]

With (k=0.4075099495N) and only (s\le N), (26) tends to

\[
 J(\mathcal L)\ge
 (0.3244777700\ldots)M_s,
\tag{27}
\]

which gives (5).  The all-simple current (21) has the better threshold.

## 4. Explicit prime-side marginal to insert

The support-(5/4) Gram construction gives, with its optimized window
normalization (a_5) and autocorrelation (g_5),

\[
\begin{aligned}
 m_T(t)={}&2A_{5,T}(t)-2\\
 &-{4\over a_5^2L^2}
 \sum_{n\le T^{5/4}}{\Lambda(n)\over\sqrt n}
 g_5(\log n)\cos(t\log n)+o(1).
\end{aligned}
\tag{28}
\]

At an actual simple zero the whole expression is nonnegative by (2), even
though its separate prime-side terms need not have a sign.  Substituting
(h=m_T) into (17) is an explicit, non-circular form of (24).  The exact
arithmetic stopping condition is that the right side of (17), with (28),
be at least (0.1055716943N).

The first nonconstant phase term is already finite and concrete:

\[
 -{1\over\pi}\int_T^{2T}m_T'(t)sin(2\Theta_a(t))\,dt
 =-{1\over\pi}\Im\int_T^{2T}m_T'(t)
 {E_a(t)\over\overline{E_a(t)}}\,dt.
\tag{29}
\]

On a right-hand contour the logarithmic derivative needed for the first
term of (17) has the convergent coefficient expansion

\[
 {V_a'\over V_a}(s)=\sum_{n\ge2}{c_a(n)\over n^s},
\quad
 c_a(n)=-\Lambda(n)+
 \sum_{k\ge0}{(\Lambda\log*\Lambda^{*k})(n)\over(aL)^{k+1}}.
\tag{30}
\]

Thus the linear phase contribution with (28) reduces before any absolute
value to the single diagonal coefficient sum

\[
 \sum_{n\le T^{5/4}}
 {\Lambda(n)g_5(\log n)c_a(n)\over n}
\tag{31}
\]

plus the standard smooth off-diagonal remainder.  Equations (29)--(31),
not another selector-existence assertion, are the immediate outside
calculation.  The (k=1) sawtooth harmonic carries
(6/\pi^2=0.607927\ldots) of the (L^2) Fourier energy of (18), while
the support-(5/4) union needs only (40.1112\%\) of its thinning
benchmark.  This makes the one-ratio term (29) the first branch to compute
before introducing any higher ratio power.

## 5. Defined-class impossibility

The need to evaluate (24) is rigorous, not a bookkeeping preference.
Consider the following finite positive-atom model.  Take

\[
 s=(2-D)N=0.79721415286134\ldots N,qquad
 d={D-1\over2}N=0.10139292356933\ldots N.
\tag{32}
\]

Use (s) mutually orthogonal unit atoms for the simple zeros.  At each of
the (d) remaining locations put two identical unit atoms, and make all
different locations orthogonal.  Then

\[
 \operatorname{tr}G=N,qquad \|G\|_F^2=s+4d=DN,
\tag{33}
\]

and the scalar Levinson demand (0.40750995N) is satisfied.  Every simple
atom nevertheless has

\[
 \operatorname{tr}(GB_\gamma)=1,qquad m_T(\gamma)=0,
\tag{34}
\]

so every simple selector has zero residual gain.  The simple crossings
may all be assigned the positive orientation (15), so the unweighted
topological information is satisfied as well.

Therefore no argument whose data consist only of

1. the scalar Levinson/simple-zero count,
2. (\operatorname{tr}G=N) and (\|G\|_F^2=DN), and
3. positivity of the Gram atoms and the unweighted winding,

can improve (1).  This precisely defined scalar/unweighted method class is
killed.  A positive theorem must evaluate the score-sensitive current
(24), beginning with the explicit one-ratio/one-coefficient calculation
(29)--(31).

## Terminal gate

* Unconditional numerical bound after this cycle:
  (N_0^s/N\ge0.79721415286134\ldots).
* No positive increment follows in the defined scalar/unweighted class;
  model (32)--(34) is a sharp obstruction.
* The topological selector lemma itself is completed in (12)--(17).
* First calculation outside the killed class: evaluate (29) with the
  coefficient sum (31), preserving the ratio before absolute values; then
  compare the resulting current directly with the numerical threshold
  (0.1055716943N).
