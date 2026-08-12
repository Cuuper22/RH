# Arithmetic construction, cycle 5: summing the signed shift before Watt

## 0. Result

Take the prime-side reduction, the recombined Heath--Brown block structure, and
the trace transfer from cycles 1--4 as given.  The proposed estimate (CSQD) is
stronger than necessary.  At its asymmetric factorization, the full nonzero
Poisson contribution can instead be bounded by summing the signed shift first.

For every fixed

\[
                    0<\eta<\frac12,
\qquad A=B=H=T^\eta,
\qquad M=N=T,                                             \tag{1}
\]

the resulting terminal remainder satisfies

\[
 \boxed{
 R_{\rm HB}\ll
 \left(T^{1+\eta}+T^{1/2+2\eta}\right)(\log T)^C .}
                                                               \tag{2}
\]

Here $C$ is fixed by the finite identity and the fixed smooth weights.  In
particular, (2) is $T^{1+\eta}\operatorname{polylog}T$ for every fixed
$\eta<1/2$, exactly the trace-grade criterion isolated in cycles 1 and 4.
The second term even saves $T^{1/2-\eta}$.  This replaces both corrected
BBLR errors

\[
 T^{1/2+3\eta}\quad\hbox{and}\quad T^{3/4+2\eta}            \tag{3}
\]

on the terminal family; it does **not** assert the stronger power-saving
CSQD inequality term by term.

Consequently, within the already accepted all-block recombination and
prime-to-zero transfer, connected support may be taken to every fixed
$\sigma=1+\eta<3/2$.  The limiting numerical certificate is

\[
 \boxed{
 \liminf_{T\to\infty}\frac{N_{0,\mathrm{simple}}(T)}{N(T)}
 \ge 0.865674254456636\ldots .}                              \tag{4}
\]

Thus the construction passes 85 percent.  The point is not a newer spectral
large sieve: it is the order in which the already present averages are used.

## 1. Exact terminal form retained before absolute values

Start with BBLR Proposition 3.1, equation (14) in its proof.  After writing

\[
 d=(am_1,bn_1),\qquad d_1d_2=d_3d_4=d,
\]

put

\[
 p=(a/d_1)(m_1/d_2),\qquad q=(b/d_3)(n_1/d_4).               \tag{5}
\]

The nonzero Poisson part is a fixed finite sum of expressions of the form

\[
 \mathcal R_d=
 \sum_{\ell\ne0}\sum_{\substack{p\asymp P_d,\ q\asymp Q_d\\(p,q)=1}}
 c_{d,p}\,e_{d,q}\,F_{d,\ell}(p,q)
 \sum_h w_d(h) e\!\left(\mp\ell h\frac{\bar p}{q}\right),  \tag{6}
\]

where

\[
 P_d\asymp\frac{AM_1}{d},\qquad
 Q_d\asymp\frac{BN_1}{d},\qquad
 w_d(h)=W_0(dh/H),\qquad H_d:=H/d.                           \tag{7}
\]

The coefficients $c_{d,p}$ and $e_{d,q}$ are the actual fixed-depth
convolution coefficients, with the factor variables retained.  They admit
fixed-divisor majorants; the explicit logarithmic factors are kept in the
smooth weights.  This is the coefficient information lost when they are
replaced by arbitrary $T^\varepsilon$-bounded sequences.

Use the asymmetric factorization already isolated in cycle 4:

\[
 M_1=M_2=T^{1/2},\qquad
 N_1=T^{1/2-\eta},\qquad N_2=T^{1/2+\eta}.                   \tag{8}
\]

Fixed dyadic constants are harmless.  A fixed support cushion and a deeper
finite identity handle the usual $T^{o(1)}$ factor-grouping slack; blocks on
the shorter side have stronger Fourier decay.  At (8),

\[
 P_d\asymp T^{\eta+1/2}/d,\quad
 Q_d\asymp T^{1/2}/d,\quad
 H_d\asymp T^\eta/d.                                        \tag{9}
\]

The Fourier integral in (6) has physical scale

\[
 X_d\asymp\frac{dN_2}{AM_1}\asymp d.                        \tag{10}
\]

Integration by parts, followed only by the standard two-variable Mellin
separation of its smooth $(p,q)$-weight, gives for every fixed $J$

\[
 \|F_{d,\ell}\|_{\rm sep}
 \ll_J d(1+|\ell|d)^{-J}(\log T)^{C_J}.                      \tag{11}
\]

This is important: the artificial cutoff
$|\ell|\le (AM)^\varepsilon/d$ is not summed by cardinality.  The actual
Fourier decay in (11) is retained.

## 2. Signed-shift reciprocal lemma

Let $w\in C_c^\infty((1,2))$, and put

\[
 S_{H_0}(\theta)=\sum_h w(h/H_0)e(h\theta).
\]

Poisson summation gives, for every $J\ge2$,

\[
 |S_{H_0}(\theta)|\ll_J
 H_0(1+H_0\|\theta\|)^{-J}.                                 \tag{12}
\]

Multiplication by $\ell$ on the reduced residues modulo $q$ has fibres of
size at most $(\ell,q)$.  Therefore

\[
 \sum_{r\,({\rm mod}\ q)}^{*}
 |S_{H_0}(\ell r/q)|
 \ll_J q+H_0(\ell,q).                                       \tag{13}
\]

For completeness, divide the unit circle into arcs of length $1/H_0$.
Equation (12) gives a convergent geometric tail away from the nearest integer;
the image of the reduced residues has spacing at least
$(\ell,q)/q$, with multiplicity at most $(\ell,q)$.  This proves (13).

The actual recombined coefficients obey the progression majorants

\[
 \sum_{\substack{p\asymp P\\p\equiv r\pmod q}}|c_p|
 \ll \frac{P}{\varphi(q)}(\log T)^{C},                       \tag{14}
\]

uniformly here because $q\le P T^{-\eta+o(1)}$.  One may prove (14)
directly before collapsing the factor variables: fix every short factor, and
the remaining smooth factor occupies one residue class; the interval contains
$P/q\gg T^{\eta-o(1)}$ representatives.  Equivalently, (14) is the standard
Shiu/Brun upper bound for a fixed-divisor majorant.  Also

\[
 \sum_{q\asymp Q}|e_q|\frac q{\varphi(q)}\ll Q(\log T)^C,
\qquad
 \sum_{q\asymp Q}|e_q|\frac{(\ell,q)}{\varphi(q)}
 \ll \tau(\ell)^C(\log T)^C.                                \tag{15}
\]

Using (13)--(15), without taking an absolute value inside the $h$-sum,
gives the lemma

\[
 \boxed{
 \sum_{q\asymp Q}\sum_{\substack{p\asymp P\\(p,q)=1}}
 |c_p e_q S_{H_0}(\ell\bar p/q)|
 \ll P\bigl(Q+H_0\tau(\ell)^C\bigr)(\log T)^C .}            \tag{16}
\]

The notation on the left means that the $h$-sum itself is performed first;
only its resulting transform is majorized.  This is precisely the step that
is unavailable after Watt's Cauchy/large-sieve diagonal has already been
formed.

## 3. Summing the Poisson frequency and the gcd

Apply (16) to (6), use (11), and take $J>C+4$.  Then

\[
 \begin{aligned}
 |\mathcal R_d|
 &\ll P_d(\log T)^C
 \sum_{\ell\ge1}d(1+\ell d)^{-J}
       \bigl(Q_d+H_d\tau(\ell)^C\bigr)\\
 &\ll P_d(Q_d+H_d)(1+d)^{-2}(\log T)^C.                      \tag{17}
 \end{aligned}

There are only fixed-divisor-many splittings
$d_1d_2=d_3d_4=d$, which changes the logarithmic power only.  From (9),

\[
 P_dQ_d\asymp\frac{T^{1+\eta}}{d^2},\qquad
 P_dH_d\asymp\frac{T^{1/2+2\eta}}{d^2}.                     \tag{18}
\]

Summing (17) over $d$ proves (2).  The preliminary replacement of
$W_4((am_1m_2\mp h)/(bn_1N_2))$ by its zero-shift value contributes the
already present $H^2(\log T)^C$, which is smaller than $T^{1+\eta}$ for
all $\eta<1$.

The exponent comparison is now transparent:

\[
 \begin{array}{c|c|c}
 \text{piece}&\text{exponent}&\text{condition for trace grade }T^{1+\eta}\\ \hline
 P_dQ_d&1+\eta&\text{always (natural signed scale)}\\
 P_dH_d&\frac12+2\eta&\eta\le\frac12\\
 H^2&2\eta&\eta\le1.
 \end{array}                                                   \tag{19}
\]

Thus the new local ceiling is $\eta=1/2$, not $1/4$.  At
$\eta>1/2$, (13) genuinely changes from the $q$-dominated to the
$H_0$-dominated regime, so this particular $L^1$ construction stops there.

## 4. Why this is outside the old black-box class

In the Watt route the terminal sixfold sum is first converted into an operator
norm.  Its regular $SX$ diagonal is insensitive to the sign of the $h$-weight
and produces

\[
                         T^{1/2+3\eta}.                       \tag{20}
\]

No improvement to the exceptional Maaß spectrum can remove that regular
diagonal.  Likewise, substituting the 2026 fixed-modulus bilinear Kloosterman
bound after this Cauchy step does not recover the lost shift transform: one
completed index is either of length one in (8), or the short coefficient is
carried to inverse residues rather than an interval.  Hence every norm-only
application at that stage retains the $\eta\le1/4$ obstruction.

Equations (12)--(16) are the promised construction outside that class.  They
use the signed $h$-average at the fraction level, while it is still a
one-dimensional smooth exponential sum.  The gain over (20) is

\[
 T^{1/2+3\eta}/T^{1+\eta}=T^{2\eta-1/2}                      \tag{21}
\]

whenever $\eta>1/4$: exactly the power previously missing from the AB line.

## 5. Transfer and numerical constant

Cycle 4 already reduced the full expansion to Type-I blocks plus the
recombined terminal family and supplied the pole, tail, zero-mode, and
matrix-transfer normalization.  Type-I blocks are unchanged.  Applying (2)
to the terminal family gives the accepted $M\operatorname{polylog}M$
aggregate scale; the two explicit logarithmic weights from the two von
Mangoldt factors are below the accepted $T\ell^3$ trace normalization after
recombination.  No individual-shift Hardy--Littlewood estimate is used.

Letting $\sigma\uparrow3/2$, the optimal connected profile for
$K(t)=\min(|t|,1)$ has

\[
 A_0=0.780202109385319\ldots,qquad
 B_0=-0.434217418074353\ldots,                                \tag{22}
\]

\[
 \int u=1.261748607282221\ldots,qquad
 C=1.431233929643706\ldots,                                   \tag{23}
\]

and therefore

\[
 D_{3/2}^{*}=\frac C{\int u}
 =1.134325745543364\ldots,                                    \tag{24}
\]

\[
 2-D_{3/2}^{*}=0.865674254456636\ldots.                       \tag{25}
\]

Relative to the rigorous cycle-4 checkpoint this is an absolute increase of

\[
 0.865674254456636-0.797214152861340
 =0.068460101595296\ldots.                                    \tag{26}
\]

## 6. Input inventory and next construction

The proof uses only:

1. BBLR Proposition 3.1 up to its exact Poisson identity (14), not its Watt
   majorization;
2. Poisson summation for the smooth signed $h$-weight;
3. the standard fixed-divisor progression upper bound, applied before the
   finite Heath--Brown factors are collapsed;
4. the already accepted asymmetric block recombination and trace transfer of
   cycles 1--4.

The Wright trilinear-fraction theorem and the 2026 Blomer--Pascadi theorem are
not inputs to (2).  Direct substitution of Wright's theorem in the fully
grouped sixfold sum is weaker here: at (8) its dominant factor gives only
$T^{1+2\eta-(1-2\eta)/40+o(1)}$, above trace near $\eta=1/4$.

The next arithmetic construction, if support beyond (3/2) is desired, is
now sharply isolated: improve the second term in (16), i.e. prove cancellation
in the inverse-residue discrepancy when $H_0>Q$.  That is a genuinely
bilinear problem.  It is no longer the old AB/Watt loss, and it is unnecessary
for the requested 85 percent threshold.
