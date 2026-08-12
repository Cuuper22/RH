# Arithmetic construction, cycle 4: corrected BBLR barrier and a rigorous 79.7214% checkpoint

## 0. Output of this cycle

This cycle produces a rigorous unconditional checkpoint, conditional only on the
infrastructure already accepted from the two supplied PDFs:

\[
 \boxed{\liminf_{T\to\infty}\frac{N_{0,\mathrm{simple}}(T)}{N(T)}
        \ge 0.79721415286134\ldots .}                         \tag{1}
\]

It also identifies an exact obstruction for every argument which feeds the
terminal Heath--Brown block into BBLR Proposition 3.1 as a black box.  In that
class, support strictly beyond \(5/4\) is impossible.  The first inequality
outside that class which would break the barrier is stated in Section 7.

The main correction is important: the first term in the BBLR error is \(AB\),
not \((AB)^{1/2}\).  Thus this report supersedes the exponent substitution in
cycle 3, equations (12)--(20).  The final all-block support \(5/4\) happens to
remain the same, but for a different reason: **two** terms, rather than one,
meet the trace scale at \(\eta=1/4\).

## 1. Exact corrected BBLR substitution

Write

\[
 X=T^{1+\eta},\qquad H=T^\eta,\qquad
 A=B=H=T^\eta,\qquad M=N=T.                                  \tag{2}
\]

BBLR Proposition 3.1 gives, when
\(H\ll(AB)^{1/2+\varepsilon}\),

\[
 E\ll_\varepsilon
 (ABMNH^2)^{1/4+\varepsilon}
 \left(AB+H^{1/4}(A+B)^{1/2}(ABMN)^{1/8}\right).              \tag{3}
\]

The outside factor is

\[
 (ABMNH^2)^{1/4}=T^{1/2+\eta}.                                \tag{4}
\]

The first, non-cuspidal/large-divisor term is therefore

\[
 E_A=T^{1/2+\eta}T^{2\eta}
     =T^{1/2+3\eta+\varepsilon}.                              \tag{5}
\]

The Watt term is

\[
 \begin{aligned}
 E_W
 &=T^{1/2+\eta}
   T^{\eta/4}T^{\eta/2}T^{(2\eta+2)/8}T^\varepsilon\\
 &=T^{3/4+2\eta+\varepsilon}.                                \tag{6}
 \end{aligned}
\]

The signed prime correlation must be \(O(T^{1+\eta}\operatorname{polylog}T)\).
Consequently

\[
 \begin{array}{rclcl}
 E_A\le T^{1+\eta}&\Longleftrightarrow&
       \frac12+3\eta\le1+\eta&\Longleftrightarrow&\eta\le\frac14,\\[2mm]
 E_W\le T^{1+\eta}&\Longleftrightarrow&
       \frac34+2\eta\le1+\eta&\Longleftrightarrow&\eta\le\frac14.
 \end{array}                                                   \tag{7}
\]

At the desired 85% exponent
\(\eta=0.42960385087046\ldots\), the two errors are respectively

\[
 E_A=T^{1.78881155261138\ldots+\varepsilon},\qquad
 E_W=T^{1.60920770174092\ldots+\varepsilon},                  \tag{8}
\]

against trace scale

\[
 T^{1.42960385087046\ldots}.                                  \tag{9}
\]

Thus the missing savings are \(T^{0.35920770174092\ldots}\) in
\(E_A\) and \(T^{0.17960385087046\ldots}\) in \(E_W\).

## 2. Complete fixed-support theorem and closure of the HB blocks

Fix \(\kappa>0\) and set

\[
 \eta=\frac14-\kappa,\qquad
 \sigma=1+\eta=\frac54-\kappa,
 \qquad X=T^\sigma,\qquad H=X/T=T^\eta.                         \tag{T1}
\]

> **Theorem (fixed support).**  With the explicit-formula, pole, tail and
> matrix-transfer statements of the supplied PDFs taken as infrastructure, the
> complete signed prime remainder for every fixed smooth kernel supported in
> \((-\sigma,\sigma)\) is \(o\) of its trace scale.  Consequently the optimal
> connected profile at this support gives
> \[
>  \liminf_{T\to\infty}\frac{N_{0,\mathrm{simple}}(T)}{N(T)}
>  \ge 2-D_\sigma^* .                                          \tag{T2}
> \]

Here is the block closure.  Choose a fixed Heath--Brown depth \(K\) so large
that every truncated irregular factor has length at most
\(X^{1/K}<H T^{-10\varepsilon}\).  After dyadic subdivision, apply the standard
factor-grouping dichotomy separately to the two von Mangoldt factors.

* If an unrestricted \(\mathbf 1\)- or \(\log\)-factor crosses the long
  threshold \(X/H=T\), keep it as the long variable.  This is a Type-I block.
  Poisson summation in that smooth variable gives the zero-frequency
  Ramanujan term; integration by parts and the ordinary hybrid large sieve give
  \(O_A(X\log^{-A}X)\) for the nonzero frequencies.  This is precisely the
  Type-I estimate already used in the accepted MRT/PDF infrastructure.

* Otherwise, multiply consecutive short factors until their product first
  crosses \(H T^{-10\varepsilon}\).  Because each irregular factor is shorter
  than \(H T^{-10\varepsilon}\), dyadic refinement produces a grouped factor
  \(a\asymp H T^{O(\varepsilon)}\).  Do this on both sides, obtaining
  \(A,B=H T^{O(\varepsilon)}\).  The remaining positive/smooth factors may be
  split into \(m_1m_2\) and \(n_1n_2\), with the shorter member listed first.
  This is exactly the terminal BBLR block.  Its grouped coefficients are
  fixed-divisor-bounded, as required by Proposition 3.1.

There is no third block: failure of subset grouping means that a single smooth
unrestricted factor crossed the threshold, which is the first alternative.
The number of identities and dyadic subdivisions is \(O_K((\log X)^{O_K(1)})\)
and is absorbed by the power savings below.

For the terminal block, equations (5)--(6) become

\[
 E_A=T^{1/2+3(1/4-\kappa)+\varepsilon}
     =T^{5/4-3\kappa+\varepsilon},                             \tag{T3}
\]

\[
 E_W=T^{3/4+2(1/4-\kappa)+\varepsilon}
     =T^{5/4-2\kappa+\varepsilon},                             \tag{T4}
\]

whereas the trace scale is

\[
 X=T^{1+\eta}=T^{5/4-\kappa}.                                  \tag{T5}
\]

Taking the internal smoothing exponent \(\varepsilon<\kappa/4\), (T3) saves
more than \(T^{3\kappa/2}\) and (T4) saves more than
\(T^{3\kappa/4}\).  Polylogarithmically many blocks therefore remain
\(o(X)\).  The diagonal and four zero-frequency terms recombine to the
Ramanujan main term because polarization and the sum over the signed shift are
performed before triangle inequality.

Finally, on every dyadic prime interval \(n\asymp X\), the explicit-formula
weights satisfy
\(1/\sqrt{n(n+h)}=X^{-1}(1+O(H/X))\).  This same factor multiplies the main
term and the BBLR remainder, so the relative saving in (T3)--(T5) is unchanged.
The \((\log X)^{O_K(1)}\) dyadic and Heath--Brown losses are swallowed by the
fixed power \(T^{-3\kappa/4}\).  The accepted pole and tail bounds then transfer
the prime estimate to the Frobenius/trace functional without a new loss.  This
proves (T2).

The published-input inventory for this theorem is:

| Input | Exact job | New hypothesis |
|---|---|---|
| Finite Heath--Brown identity and its Type-I/II grouping lemma | decomposes both \(\Lambda\)-factors and isolates \(A,B\asymp H\) | none |
| Standard Poisson/hybrid-large-sieve Type-I bound | evaluates blocks with a long smooth \(\mathbf1\) or \(\log\) variable | none |
| Bettin--Bui--Li--Radziwiłł, Proposition 3.1 | evaluates every terminal signed quadratic-divisor block, including its zero modes | none |
| The two supplied PDFs | explicit formula, pole/tail control, matrix trace-to-simple-zero transfer | accepted infrastructure |
| Euler solution for \(K(t)=\min(|t|,1)\) | optimizes \(D_\sigma^*\) | none |

The Pascadi, Milićević--Qin--Wu, Blomer--Pascadi and Robles results discussed
later are **not** inputs to the unconditional constant (1).

## 3. Rigorous all-block support and numerical certificate

Taking any fixed \(\eta<1/4\), both errors in (5)--(6) are power-saving
relative to the trace scale.  Letting \(\eta\uparrow1/4\) gives evaluated
prime-pair support

\[
                         \sigma=1+\eta\uparrow\frac54.         \tag{10}
\]

For the accepted pair kernel \(K(t)=\min(|t|,1)\), the optimal connected
profile at \(\sigma=5/4\) has

\[
 \delta=\frac14,\qquad q=\frac18,\qquad b=\frac38,             \tag{11}
\]

and, before mass normalization,

\[
 u(x)=
 \begin{cases}
 \cos(\sqrt2x),&|x|\le3/8,\\
 A_0\cos(|x|-1/2)+B_0\sin(\sqrt3(|x|-1/2)),
     &3/8\le|x|\le5/8,
 \end{cases}                                                   \tag{12}
\]

where

\[
 A_0=0.765651150533640\ldots,\qquad
 B_0=-0.479300891051646\ldots .                                \tag{13}
\]

The numerical input inventory is

\[
 \int u=1.09716424928793\ldots,\qquad
 C=1.31965363103003\ldots,                                    \tag{14}
\]

\[
 D_{5/4}^*=\frac{C}{\int u}
           =1.20278584713866\ldots,                            \tag{15}
\]

and hence

\[
 2-D_{5/4}^*=0.79721415286134\ldots .                          \tag{16}
\]

Relative to the accepted PDF constant \(0.6725007037\), this is an absolute
gain

\[
 0.79721415286134-0.6725007037
 =0.12471344916134\ldots .                                    \tag{17}
\]

No prime-pair conjecture is used in (1): the only new arithmetic input is the
BBLR quadratic-divisor theorem in the range (7), applied to the signed smooth
shift average before taking absolute values.

## 4. Exact black-box impossibility statement

Define the **BBLR black-box dispersion class** to consist of constructions which

1. decompose both von Mangoldt factors by a finite Heath--Brown/Vaughan
   identity;
2. contain the terminal block (2), with the two grouped irregular factors
   treated as arbitrary divisor-bounded sequences;
3. estimate every dyadic block by BBLR Proposition 3.1, and only then recombine
   the blocks by triangle inequality; and
4. require an \(O(T^{1+\eta}\operatorname{polylog}T)\) remainder for that block.

Then (7) proves:

> **Barrier theorem.**  No member of the BBLR black-box dispersion class can
> evaluate the complete prime-side kernel at any fixed support
> \(\sigma=1+\eta>5/4\).

This is a theorem about the specified proof class, not about the prime
correlation itself.  Disconnected lobes do not evade it if all their pairwise
difference bands are estimated by the same black box: every band extending
beyond \(5/4\) contains the same terminal block.

## 5. Why the 2024--26 exceptional-spectrum refinement does not remove (5)

Pascadi's frequency-concentrated large sieve (arXiv:2404.04239v3, Theorems
2, 3, 13 and Corollaries 15--18) improves the factor attached to the
**exceptional** Maaß spectrum.  The relevant saving parameter is available for
additively structured coefficients such as

\[
 a_n=\sum_{h_1\ell_1-h_2\ell_2=n}
      \Phi_1(h_1/H)\Phi_2(h_2/H)e(h_1\alpha_1+h_2\alpha_2).     \tag{18}
\]

The terminal coefficient in (2), however, is a multiplicative convolution of
short Möbius factors.  It has neither the representation (18) nor a known
frequency measure satisfying Theorem 13's concentration conditions.  More
decisively, (5) is present in the regular/large-divisor part before any
exceptional-eigenvalue loss is inserted.  It remains even under the Selberg
eigenvalue conjecture.  Therefore these results substitute no power saving into
\(E_A\), and the rigorous ceiling from them is still

\[
                              \eta<\frac14.                    \tag{19}
\]

## 6. Fixed-modulus Kloosterman advances: exact threshold comparison

The phase after Poisson summation is a Kloosterman fraction

\[
 e\!\left(\mp \ell h\,
       \frac{\overline{a m_1/d}}{b n_1/d}\right).              \tag{20}
\]

Completing the smooth inverse variable turns a fixed denominator
\(q\asymp T^{\eta+1/2}\) into a bilinear form of Kloosterman sums with both
completed variables of natural length \(T^\eta\) in the balanced terminal
block.  Thus their exponent relative to the modulus is

\[
             \frac{\log T^\eta}{\log T^{\eta+1/2}}
             =\frac{\eta}{\eta+1/2}.                           \tag{21}
\]

Blomer--Pascadi (arXiv:2607.24311, Theorem 1.1) is nontrivial in the
balanced general-modulus range only when this is greater than \(13/28\), i.e.

\[
 \frac{\eta}{\eta+1/2}>\frac{13}{28}
 \quad\Longleftrightarrow\quad \eta>\frac{13}{30}.             \tag{22}
\]

In particular, it supplies no saving in a neighborhood immediately to the
right of the existing \(\eta=1/4\) barrier, and is still just below its
nontrivial range at \(\eta=0.42960385\ldots\).

The Milićević--Qin--Wu general-modulus result has balanced threshold
\(10/21\), which here requires

\[
 \frac{\eta}{\eta+1/2}>\frac{10}{21}
 \quad\Longleftrightarrow\quad \eta>\frac5{11}.                \tag{23}
\]

It therefore does not bridge the barrier either.  The unbalanced
Blomer--Pascadi Theorem 5.7 can save one factor of size at most
\(T^{\eta-1/4}\) after an extreme asymmetric split.  But (5) needs
\(T^{2(\eta-1/4)}\), while the remaining Watt contribution needs another
\(T^{\eta-1/4}\).  A single lossless insertion is therefore insufficient even
before accounting for the outer modulus averages.

The claimed 2026 extension of the twisted zeta second moment to
\(T^{1/2+1/46}\) (arXiv:2601.00292) is withdrawn because of a missing
\(L^2\) factor, so it contributes no unconditional input.

## 7. The depth-five fractional-zeta identity does not by itself cancel AB

Robles, arXiv:2608.07198, proves exact depth-five Heath--Brown identities in
which every irregular factor is supported below \(x^{1/5}\), and proves

\[
 \sum_{n\le x}d_{\pm a/b}(n)e(n\alpha)
 \ll_{a,b}\left(xq^{-1/2}+x^{4/5}+x^{1/2}q^{1/2}\right)
             (\log 2x)^C.                                     \tag{24}
\]

This is useful one-dimensional additive cancellation.  The BBLR terminal
remainder instead contains a *pair* of grouped irregular factors inside the
reciprocal phase (20).  Regrouping the depth-five factors into \(a\) and \(b\)
returns two divisor-bounded sequences of total lengths \(A=B=T^\eta\), and
Proposition 3.1 again contributes the \(AB\) term in (3).  Estimate (24) does
not apply after the reciprocal modulus and the second irregular coefficient
are present.  Consequently the identity improves the factor inventory but
does not, without a new bilinear reciprocal estimate, change (19).

For the all-smooth subfamily \(A=B=1\), one must use BBLR's general error
because the strong estimate assumes \(H\ll(AB)^{1/2+\varepsilon}\).  That
general error is

\[
                         T^{3/4+\eta+\varepsilon}+T^{2\eta+\varepsilon},
                                                                    \tag{25}
\]

which is trace-grade for every \(\eta<1\).  Hence the earlier cycle-3
"smooth-only \(\sigma<4/3\)" number is not a genuine ceiling of Proposition
3.1.  The obstruction is entirely the irregular all-block terminal family.

## 8. First constructive inequality outside the black-box class

Retain the actual signed endpoint phase and choose the asymmetric internal
factorization

\[
 M_1=T^{1/2},\quad M_2=T^{1/2},\quad
 N_1=T^{1/2-\eta+\varepsilon},\quad
 N_2=T^{1/2+\eta-\varepsilon}.                                 \tag{26}
\]

Then the Poisson frequency length is only \(T^{O(\varepsilon)}\).  The precise
coefficient-sensitive estimate to prove is

\[
 \boxed{
 \begin{aligned}
 R_{\rm HB}\ll_\varepsilon T^\varepsilon\big[&
 (AB)^{1/2}H^{1/2}(AM)^{1/2}\\
 &+A^{1/4}B^{1/2}H^{3/4}N_1^{1/2}(AM)^{1/2}\big],
 \end{aligned}}                                                \tag{CSQD}
\]

for the *actual recombined Heath--Brown coefficients*, not for arbitrary
pointwise-bounded sequences.  The first line asks for square-root cancellation
in the signed \((a,b)\)-average before absolute values; it is exactly the
replacement \(AB\mapsto(AB)^{1/2}\) missing from (3).  The second line is the
existing Watt-shaped contribution with the true \(N_1\) retained rather than
maximized by \(N_1\le N^{1/2}\).

At (2) and (26), the two lines of (CSQD) have exponents

\[
 T^{1/2+2\eta+\varepsilon},\qquad
 T^{3/4+(3/2)\eta+\varepsilon}.                                \tag{27}
\]

Both are below \(T^{1+\eta}\) for every fixed \(\eta<1/2\).  Thus (CSQD)
would immediately give connected support \(\sigma<3/2\), whose already
computed optimal Frobenius constant is

\[
 D_{3/2}^*=1.13432574582\ldots,qquad
 2-D_{3/2}^*=0.86567425418\ldots .                              \tag{28}
\]

Even the weaker one-parameter estimate

\[
 R_A\ll ABH^{1/2}(AM)^{1/2}T^{-\delta}                         \tag{29}
\]

for any fixed \(\delta>0\), together with a matching treatment of the Watt
line, moves the support ceiling from \(1+1/4\) to at least
\(1+1/4+\delta/2\).  Therefore the next construction should not seek a longer
generic Kloosterman theorem.  It should prove (29), ideally (CSQD), by keeping
the Möbius/fractional-zeta factors separate and applying dispersion to the
signed \((a,b)\)-pair before Cauchy--Schwarz.

## 9. Handoff

* **Unconditional delivered constant:** \(0.79721415286134\ldots\).
* **Correct all-block ceiling inside BBLR black-box dispersion:**
  \(\sigma<5/4\).
* **Two exact terminal errors:** \(T^{1/2+3\eta}\) and
  \(T^{3/4+2\eta}\).
* **New 2024--26 results tested:** exceptional-spectrum concentration and
  fixed-modulus Kloosterman bounds do not cross the local \(1/4\) barrier;
  the claimed \(T^{1/2+1/46}\) zeta twist result is withdrawn.
* **Immediate construction:** prove (CSQD), or first obtain any fixed power
  saving in (29), without grouping the irregular factors before the signed
  reciprocal average.
