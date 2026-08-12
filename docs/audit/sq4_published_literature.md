# Published-theorem audit for the signed SQ4 Gauss-product survivor

Status: **no published theorem was found in the audited classes whose
literal left-hand side contains the full source moment below.**  Every
numerically testable published route is power-killed at the source scales,
and every remaining cited class has an explicit structural mismatch.  This
is a finish/kill result for the theorem classes and sources listed here.  It
is not a universal nonexistence claim.

This note is source-first.  The exact rational arithmetic is independently
replayed by `verify/a1_sq4_published_literature.py` and proved in
`RH/Zeta85/Discharge/SQ4PublishedLiterature.lean`.  The Lean file asserts no
analytic theorem and no literature-applicability statement.

## 1. Exact target and source boundary

Use the scales

\[
 U=T^{43/200},\quad M=T^{2/5},\quad P=T^{83/100},\quad
 V=K=T^{43/100},\quad R=T^{33/50},\quad L=T^{23/100}.
 \tag{1}
\]

Here \(p=u_1u_2m\asymp P\), \(r=\ell h\) with
\(|\ell|\asymp L\), \(|h|\asymp T^{43/100}\), and the Poisson
completion prefactor is

\[
 {M\over P}=T^{-43/100}.                               \tag{2}
\]

With the complete-sum convention and shifted Gauss sum

\[
 S(a,b;p)=\sum_{z\bmod p}^{*}e_p(az+b\bar z),\qquad
 G_p(\chi;t)=\sum_{z\bmod p}^{*}\chi(z)e_p(tz),          \tag{3}
\]

the exact finite transform in `sq4_gauss_square_transform.md` gives the
pre-completion survivor

\[
\begin{aligned}
 \mathfrak M_4(T,x)=
 \sum_{u_1,u_2,m,r,k\ne0}
 &\mu(u_1)\mu(u_2)\Gamma_{\sigma,x}(r)
 {P\over p\varphi(p)}\\
 &\times\sum_{\chi\bmod p}
 A_{u_1,u_2,m,r,k,x,T}(\chi)
 G_p(\chi;k)G_p(\chi;\sigma r),
\end{aligned}                                           \tag{4}
\]

where

\[
 A_{u_1,u_2,m,r,k,x,T}(\chi)
 =\sum_{v_1,v_2}\mu(v_1)\mu(v_2)
   \mathcal W_{T,x}(u_1,u_2,m,v_1,v_2,r,k)\chi(v_1v_2). \tag{5}
\]

All source cutoffs remain inside \(\mathcal W\); (5) assumes no
separability.  The sufficient analytic target is

\[
 \boxed{\lvert\mathfrak M_4(T,x)\rvert
 \ll_{\varepsilon,\mathbf W}
 T^{48/25+\varepsilon}(\log T)^0.}                       \tag{6}
\]

Restoring (2) gives \(48/25-43/100=149/100\).  The exponent zero in
(6) is the normalized fixed logarithmic exponent.  Restoring the two raw
Heath--Brown long slots changes it to exactly two.

## 2. The conductor decomposition cannot be omitted

Let \(\chi\pmod q\) be induced by the primitive character
\(\chi^*\pmod f\), and write \(q=f\lambda\).  With primitive characters
extended by zero off the units, finite inclusion--exclusion gives

\[
 \boxed{
 G_q(\chi;t)=\tau(\chi^*)
 \sum_{\substack{c\mid(\lambda,t)\\(\lambda/c,f)=1}}
 c\,\mu(\lambda/c)\chi^*(\lambda/c)
 \overline{\chi^*}(t/c).}                               \tag{7}
\]

Indeed, insert
\(1_{(a,\lambda)=1}=\sum_{d\mid(a,\lambda)}\mu(d)\), discard
\((d,f)>1\), write \(a=db\), and sum the \(\lambda/d\) lifts of
\(b\pmod f\).  Equivalently, with \(c=\lambda/d\), the lift sum is zero
unless \(c\mid t\), and otherwise is
\(c\tau(\chi^*)\overline{\chi^*}(t/c)\).

The boundary checks are exact:

- \(\lambda=1\) gives
  \(G_f(\chi^*;t)=\tau(\chi^*)\overline{\chi^*}(t)\);
- \(f=1\) gives the Ramanujan sum
  \(\sum_{c\mid(q,t)}c\mu(q/c)\), including \(t=0\), where it is
  \(\varphi(q)\);
- primes shared by \(f\) and \(\lambda\) are retained by
  \((\lambda/c,f)=1\), rather than silently deleted.

Thus the product in (4) contains, for every \(f\mid p\), independent
divisor sums

\[
 c_k\mid(\lambda,k),\qquad c_r\mid(\lambda,r).           \tag{8}
\]

Primitive-character theorems cover only \(\lambda=1\).  A reduction to
primitive characters that drops (8) is not a reduction of the full source.
Moreover, \(p=u_1u_2m\) is not a coprime or squarefree factorization:
\(u_1\) and \(u_2\) can share a squarefree factor, and \(m\) can share
further primes.

## 3. Exact quantitative verdicts

Every output in this table is in the pre-completion normalization (4).
The comparison target is \(48/25\).  A positive excess kills the displayed
method class; it is not a lower bound for the source moment.

| Method class | Hypotheses granted for the test | Output | Excess | Normalized/raw fixed logs | Verdict |
|---|---|---:|---:|---:|---|
| Coefficient-blind all-modulus character Cauchy/large sieve | all-character induction, conductor/gcd control, favorable energies | \(121/50\) | \(1/2\) | \(0/2\) | power-killed |
| Ideal joint square root in \((k,r)\) at each fixed \((p,v)\) | locally optimal cancellation, then triangle in both outer families | \(111/50\) | \(3/10\) | \(0/2\) | power-killed |
| Reciprocity, completion, pointwise Weil, full triangle | base power before its additional \(T^{\eta+\varepsilon}\) | \(553/200\) | \(169/200\) | \(0/2\) | power-killed |
| Shparlinski 2019, Theorem 2.1 | unit/coprime stratum and favorable collapsed coefficient norms | \(2071/800\) | \(107/160\) | \(0/2\) | power-killed |
| Shparlinski 2019, Theorem 2.2, good moduli at moment \(s=2\) | same grants; exceptional source mass omitted | \(1017/400+\varepsilon\) | \(249/400+\varepsilon\) | \(0/2\) | good part power-killed; not a full-level estimate |
| KSWX 2023, Theorem 2.1 | \((\ell,p)=1\) and favorable collapsed \(L^2\) norm | \(507/200\) | \(123/200\) | \(0/2\) | power-killed |
| Pascadi 2026, Corollary 5.11, literal fixed-\((d,a)\) recombination | squarefree-\(v\), \((p,v)=1\) Ramanujan-lift stratum | \(599/200\) | \(43/40\) | \(1/3\) | power-killed and incomplete |
| Unstated general-first-sequence Pascadi variant | favorable extra theorem and recombination grants | \(139/50\) | \(43/50\) | \(2/4\) | conditional class power-killed |
| Blomer--Pascadi 2026, Theorem 5.5 | literal fixed-\((p,v)\) block, then outer triangle | \(977/360\) | \(1429/1800\) | \(0/2\) | power-killed; preprint only |

All unspecified \(q^{o(1)}\), Mellin, truncation, and theorem losses are
recorded as \(T^\varepsilon\), rather than assigned unsupported fixed
logarithmic exponents.  The explicitly derived Pascadi divisor and dyadic
losses are the fixed powers displayed in the table.

### 3.1 Shparlinski 2019, Theorem 2.1

The published source is Igor Shparlinski,
[*On sums of Kloosterman and Gauss sums*](https://doi.org/10.1090/tran/7506),
Transactions of the AMS **371** (2019), 8679--8697.  Its Theorem 2.1
uses an arbitrary integer \(q\ge1\), an interval
\(J=\{L_0+1,\ldots,L_0+N\}\subset[1,q-1]\), and coefficients
\(\alpha_a\) supported on \(a\in(\mathbb Z/q\mathbb Z)^\times\).  In the
paper's notation,

\[
 \sum_{a\bmod q}^{*}\alpha_a\sum_{n\in J}S(a,n;q)
 \ll (\|\alpha\|_1\|\alpha\|_2)^{1/2}
 \left(N^{1/8}q+N^{1/2}q^{3/4}\right)q^{o(1)}.           \tag{9}
\]

For a favorable source-shaped test, freeze \(p,\ell\), and the smooth
Fourier/Mellin parameter \(t\).  Source coprimality supplies \((v,p)=1\);
on the additional stratum \((k\ell,p)=1\), the exact unit change of
variables gives

\[
 S(k\bar v,\sigma\ell h;p)
   =S(\sigma\ell k\bar v,h;p).                          \tag{10}
\]

Collapse \((k,v)\) with the same residue
\(a=\sigma\ell k\bar v\pmod p\) into \(\alpha_a(t)\), split signs,
and use the \(h\)-interval of length \(N=T^{43/100}\).  The explicit
favorable coefficient grants are

\[
 \|\alpha(t)\|_1\ll T^{43/50+\varepsilon},\qquad
 \|\alpha(t)\|_2\ll T^{43/100+\varepsilon}.             \tag{11}
\]

They are grants for this method-class test, not source theorems.  From (9),

\[
 {1\over2}\left({43\over50}+{43\over100}\right)
 ={129\over200},                                        \tag{12}
\]

and the two kernel powers are

\[
 {43\over800}+{83\over100}={707\over800},\qquad
 {43\over200}+{3\over4}{83\over100}={67\over80}.       \tag{13}
\]

The first dominates.  The local output is \(1223/800\); absolute
summation in \(p\) and \(\ell\) contributes \(83/100+23/100\), so

\[
 {1223\over800}+{83\over100}+{23\over100}
 ={2071\over800},\qquad
 {2071\over800}-{48\over25}={107\over160}.              \tag{14}
\]

Thus this favorable unit-stratum application is already power-killed.  It
also omits \(k\)-nonunit strata and uses the unproved norm grant (11).

Theorem 2.2 is an almost-all-moduli pointwise assertion, not a summed-level
inequality.  With its moment parameter \(s=2\), the same grants give mixed
norm exponent \(129/200\) and kernel exponent
\(\max(83/100,67/80)=67/80\).  Even its good-modulus part has base power

\[
 {83\over100}+{23\over100}+{129\over200}+{67\over80}
 ={1017\over400},                                       \tag{15}
\]

which exceeds (6) by \(249/400\), before its positive theorem loss.
For the paper's positive parameter \(\delta\), the theorem allows up to
\(Q^{1-2s\delta+o(1)}\) exceptional moduli and contributes
\(q^{\delta+o(1)}\) on the good moduli; the latter is relabeled as the
aggregate \(T^\varepsilon\) loss in the table.  It does not bound the
source mass supported on them.

### 3.2 Shparlinski 2019, Theorems 2.3--2.4

The same paper defines, for primitive characters modulo one fixed \(q\),

\[
 T_q(W;J)=\sum_{\chi\bmod q}^{*}\sum_{n\in J}
 \omega_\chi G_q(\chi;n),                               \tag{16}
\]

with \(\omega_\chi\) independent of \(n\), and proves

\[
 |T_q(W;J)|\ll(\|W\|_1\|W\|_2)^{1/2}
 (q+N^{1/2}q^{3/4})q^{o(1)}.                            \tag{17}
\]

Theorem 2.4 is the corresponding almost-all-\(q\) pointwise statement.
A direct substitution \(q=p,n=k\),
\(\omega_\chi=G_p(\chi;\sigma r)A_{p,r,k}(\chi)\) is illegal because
\(A\) depends on \(k\).  Freezing \(r\) can absorb the second Gauss sum into
\(\omega_\chi\), but exact \(t\)-separation still leaves a generally
nonconstant coefficient of \(k\), while (16) has no \(n\)-dependent
coefficient slot.  Thus even the primitive/unit subblock has no literal
substitution without an additional weighted theorem.  In any case, the
theorems freeze \(p\), sum only primitive characters, omit (8), and do not
supply a horizontal signed level average.  The exceptional moduli in
Theorem 2.4 require a separate source-mass bound.

### 3.3 Audited published correlated Kloosterman routes

Kerr--Shparlinski--Wu--Xi,
[*Bounds on bilinear forms with Kloosterman sums*](https://doi.org/10.1112/jlms.12753),
Journal of the London Mathematical Society **108** (2023), 578--621,
Theorem 2.1, treat

\[
 S_{q,a}(\alpha)=\sum_{m\in\mathcal I}\alpha_m
   \sum_{n\in\mathcal J}S(m,an;q)                      \tag{17a}
\]

for any positive integer \(q\), intervals of lengths
\(M_{\rm th},N_{\rm th}>1\), and \(d=(a,q)\).  The exact source test
sets \(q=p\), \(M_{\rm th}=p\), \(N_{\rm th}=T^{43/100}\), and
\(a=\sigma\ell\), while collapsing \((k,v)\) into \(\alpha_m(t)\).
The full map still needs the explicit grants

\[
 (\ell,p)=1,\qquad
 \|\alpha(t)\|_2\ll_\varepsilon T^{43/100+\varepsilon}. \tag{17b}
\]

Under them, the best of the theorem's three displayed
\(\Delta_1\)-powers is \(-43/200\); its per-\((p,\ell)\) power is
\(59/40\), and its completed power is \(421/200\).  Removing the
completion prefactor gives the table's \(507/200\), with exact target gap
\(123/200\).  These values are derived term by term in
`sq4_correlated_moment.md` and replayed independently here.  The theorem is
published, but (17b) and the omitted noncoprime frequency strata prevent a
full-source application.

Alexandru Pascadi,
[*Large sieve inequalities for exceptional Maass forms and the greatest
prime factor of \(n^2+1\)*](https://doi.org/10.1017/fmp.2026.10025),
Forum of Mathematics, Pi **14** (2026), e8, Corollary 5.11, is also
published.  On the squarefree-\(v\) stratum with \((p,v)=1\), the exact
identity

\[
 S(k,rv;pv)=c_v(k)S(k\bar v,r;p),\qquad
 {1\over c_v(k)}=\mu(v)\sum_{d\mid(v,k)}
   \mu(d){d\over\varphi(d)}                             \tag{17c}
\]

and additive resolution of \(1_{d\mid k}\) permit literal, separate
fixed-\((d,a)\) applications.  Pascadi's equation (5.32) contains the
factor \(S\sqrt R\,C\); at the source scales its four geometry powers are
\(63/50,19/25,209/200,11/8\).  The last dominates, and literal
recombination gives pre-completion power \(599/200\), gap \(43/40\), and
normalized/raw fixed log powers \(1/3\).  The smaller \(139/50\) value
requires an unstated level-averaged general-first-sequence variant and has
fixed log powers \(2/4\).  Moreover, if \(v_1=ga,v_2=gb\), then
\(v=g^2ab\) and \(c_v(k)=0\) when \(g\nmid k\), so division in (17c)
cannot reach those source strata.

## 4. Character and Gauss-moment literature

### 4.1 Direct root-number squares

J. Berg, N. Ryan, and M. P. Young,
[*Vanishing of quartic and sextic twists of L-functions*](https://doi.org/10.1007/s40993-023-00499-x),
Research in Number Theory **10** (2024), Proposition 17, prove for every
nonzero even integer \(j\)

\[
 \sum_{\substack{q\le X\\(q,2)=1}}
 \sum_{\substack{\chi^4=1\\\operatorname{cond}(\chi)=q}}
 \left({\tau(\chi)^2\over q}\right)^j
 =c_jX+o(X).                                             \tag{18}
\]

The first power \(j=1\) for the full odd-conductor, order-dividing-four
family is the \(j=1\) case of their Conjecture 18, which is stated for every
odd power:

\[
 \sum_{\substack{q\le X\\(q,2)=1}}
 \sum_{\chi^4=1,\,\operatorname{cond}\chi=q}
 {\tau(\chi)^2\over q}\ll X^{1-\delta}.                 \tag{19}
\]

This is already much narrower than (4): character order dividing four, primitive
characters, no \(\chi(kr)A_{p,r,k}(\chi)\), and no prescribed factorized
modulus.  Proposition 17 gives an unspecified \(o(X)\), not a usable power
or fixed-log output.  The paper separately proves qualitative
equidistribution for the narrower totally-quartic primitive odd-conductor
family; (19) must not be described as the status of that subfamily.

### 4.2 Fixed-field Gauss moments and bilinear Gauss sums

Shparlinski,
[*On the distribution of arguments of Gauss sums*](https://doi.org/10.2996/kmj/1238594554),
Kodai Mathematical Journal **32** (2009), Lemma 2, proves for one finite
field, a subset \(A\subset\mathbb F_q^\times\), a set \(X\) of
nonprincipal multiplicative characters, and \(d=(j,q-1)\),

\[
 \left|\sum_{a\in A}\sum_{\chi\in X}G(a,\chi)^j\right|
 \le q^{(j+1)/2}\sqrt{d|A||X|}.                          \tag{20}
\]

At \(j=2\), (20) is a same-shift square at one field modulus with subset
weights.  It is not the two-shift product, arbitrary joint coefficient,
varying composite modulus, all-character family in (4).

Shparlinski,
[*Bilinear sums of Gauss sums*](https://doi.org/10.4064/aa210523-3-2),
Acta Arithmetica **202** (2022), likewise works at one fixed odd prime and
with separated bilinear weights.  The fixed-prime hypothesis alone prevents
a literal map to the horizontal composite-modulus moment; the coefficient
shape also omits (5) and the conductor sums (8).

### 4.3 Ordinary and fixed-order character large sieves

The classical all-modulus multiplicative large sieve of Gallagher,
[*The large sieve*](https://doi.org/10.1112/S0025579300007968),
Mathematika **14** (1967), has the primitive-character form

\[
 \sum_{q\le Q}{q\over\varphi(q)}\sum_{\chi\bmod q}^{*}
 \left|\sum_{n}a_n\chi(n)\right|^2
 \ll (Q^2+N)\sum_n|a_n|^2.                              \tag{21}
\]

Even after granting every applicability repair in its favor, the two
coefficient-blind Cauchy norms have powers \(209/200\) and \(11/8\).
Their sum is \(121/50\), giving the exact \(1/2\) gap in the first row of
the table.  Squaring the coefficient polynomial destroys the original four
signed Möbius correlation.

Iwaniec,
[*The large sieve with prime moduli*](https://doi.org/10.4171/RMI/1381),
Revista Matemática Iberoamericana **38** (2022), obtains a
\(Q^2/\log Q\) improvement only for prime moduli, cropped coefficients, and
the paper's small-prime energy condition.  The source modulus is composite,
and neither the crop nor the energy condition has been constructed for
(5).  A logarithmic gain cannot repair the \(T^{1/2}\) power gap in (21).

Heath--Brown's real-character large sieve (Acta Arithmetica **72** (1995),
Theorem 1) and Blomer--Goldmakher--Louvel's fixed \(n\)-th-order Hecke
character large sieve (IMRN 2014, Theorem 1.3) cover fixed-order,
squarefree/coprime families with one conductor-independent sequence.  The
full character group in (4) has unbounded orders as \(p\) varies, and its
coefficient depends jointly on \(p,r,k\).  There is no decomposition into a
fixed finite union of those families.

Conrey--Iwaniec--Soundararajan,
[*The mean square of the product of a Dirichlet L-function and a Dirichlet
polynomial*](https://doi.org/10.7169/facm/1767), Functiones et Approximatio
**61** (2019), average a conjugate \(L\)-pair with one
conductor-independent polynomial; the root numbers cancel.  The standalone
*Asymptotic Large Sieve*, arXiv:1105.1176, remains a preprint record and in
any event retains primitive-character and coefficient-shape restrictions.

## 5. Spectral reciprocity and PBK formulas

### 5.1 The published generalized PBK framework

Y. Hu, I. Petrow, and M. P. Young,
[*A generalized PGL(2) Petersson/Bruggeman--Kuznetsov formula for analytic
applications*](https://doi.org/10.1017/fms.2026.10176), Forum of Mathematics,
Sigma **14** (2026), e27, is the closest published structural framework.
For its fixed local test at \(p\), the local Fourier/Mellin transform in
Section 7 contains a factor \(\tau(\chi)^2/\varphi(p^k)\), and Theorem 1.8
gives a generalized PBK formula.

The literal boundary is decisive.  The theorem fixes the local test and
fixed integer indices \(m_1,m_2\), with the stated coprimality hypotheses;
its spectral large sieve is a fixed-conductor GL(2) statement.  Remark 1.25
explicitly records that the paper's conductor-versus-family condition fails
for the exact-conductor test \(f_{=c}\) in horizontal \(p\)-aspect.  The
framework therefore does not average the moving \(k,r\), arbitrary
\(p\)-dependent coefficient (5), or \(p=u_1u_2m\) with its signs and shared
prime factors.

### 5.2 Other reciprocity and \(L\)-moment formulas

- Kwan--Leung, Bulletin of the London Mathematical Society **57** (2025),
  DOI [10.1112/blms.70218](https://doi.org/10.1112/blms.70218), give a
  character-sum reciprocity/Voronoi identity for one fixed primitive
  character.  The functional equation exposes a root-number square, but
  the result is not a character/conductor average and its coefficients are
  GL(2) Hecke coefficients, not arbitrary (5).
- Blomer--Humphries--Khan--Milićević,
  *Motohashi's fourth moment identity for non-archimedean test functions and
  applications*, Compositio Mathematica **156** (2020), Theorems 1 and 4,
  use one prime modulus, primitive characters, and intrinsic products of
  \(L\)-values.  Their polynomial result permits length at most \(q^{1/4}\);
  at the source scales this is \(T^{83/400}\), below
  \(V=T^{43/100}\).  The \(L\)-factors cannot be chosen away to leave (4).
- Blomer--Khan (Duke Mathematical Journal **168** (2019)), Petrow--Young
  (Duke Mathematical Journal **172** (2023)), and Kaneko (Forum of
  Mathematics, Sigma **10** (2022)) concern fixed level or prime modulus
  and structured moments of \(L\)-values.  Their test weights do not permit
  the arbitrary source-dependent four-sign coefficient (5), and none is a
  horizontal all-character \(\tau(\chi)^2\) large sieve.

These are structural inapplicability statements; no exponent is assigned to
a nonexistent substitution.

## 6. Kloosterman, trace-function, and modulus-factorization classes

### 6.1 Kloosterman sums over moduli

Blomer--Milićević,
[*Kloosterman sums in residue classes*](https://doi.org/10.4171/JEMS/498),
Journal of the European Mathematical Society **17** (2015), Theorem 1,
average \(S(m,n;c)\) over \(c\), but \(m,n\) and the congruence modulus are
fixed and the modulus weight is one function of \(c\).  In the source,
\(m=k\bar v\pmod p\) moves with \(p=c\), and its coefficient depends on all
inner variables.  That is not a literal theorem input.

The classical Deshouillers--Iwaniec Kuznetsov large-sieve family has the
same fixed-integer-index boundary.  The exact squarefree-\(v\) Ramanujan lift
used in the Pascadi test can fix selected indices, but it fails when
\(v_1=ga,v_2=gb\) and \(g\nmid k\), because then \(c_v(k)=0\).  Dividing by
that Ramanujan factor would delete a source stratum.

Bettin--Chandee's trilinear Kloosterman-fraction theorem has one reciprocal
phase and separated coefficients.  Expanding the source complete sum gives
two phases sharing both \(p\) and the complete-sum variable, together with
the nonseparable coefficient (5).  No literal parameter map results.

### 6.2 Fixed-prime trace functions and higher Kloosterman sums

The bilinear trace-function theorems of Fouvry--Kowalski--Michel and
Kowalski--Michel--Sawin require a prime modulus and a bounded-conductor
trace function.  Shparlinski, *Sums of multidimensional Kloosterman sums*,
Periodica Mathematica Hungarica **90** (2025), treats product intervals at
one fixed \(q\) and a different higher-dimensional kernel.  These theorems
do not accept a varying composite \(p\), all conductor strata, and an
arbitrary joint coefficient.

Shao--Shparlinski--Wijaya, *Sums of Kloosterman sums over square-free and
smooth integers*, Bulletin of the Australian Mathematical Society **113**
(2026), place \(|\mu(n)|\) on a squarefree argument for one fixed prime
modulus.  This is not signed Möbius averaging in the modulus and does not
retain the four signs of (4).

### 6.3 Factorable modulus weights

Maynard, *Primes in arithmetic progressions to large moduli I: fixed
residue classes*, Memoirs of the AMS **306** (2025), Theorem 1.1, controls
prime-counting errors averaged with triply well-factorable level weights.
Its left-hand side is not a Kloosterman or character/Gauss-product moment.
Writing \(p=u_1u_2m\) does not by itself construct one admissible triply
well-factorable sequence: the coefficient (5) still depends on \(p,r,k\),
and the required pointwise factorization bounds have not been proved.

## 7. Preprints kept outside the published-input class

The following results are useful comparisons, but cannot be transcribed as
published inputs at this date:

- Blomer--Pascadi, arXiv:2607.24311v1, Theorem 5.5.  After exact
  \(t\)-separation, sign splitting, and zero padding, it applies literally
  to each fixed-\((p,v)\) bilinear \((k,r)\) block, including nonunit
  frequencies.  Its five auxiliary powers are
  \(7/320,1/3200,27/500,71/900,-17/1500\), so the dominant power is
  \(71/900\).  Outer triangle gives \(977/360\), the last row of the
  quantitative table.
- Milićević--Qin--Wu, arXiv:2511.07550, and Pascadi,
  arXiv:2505.00653, remain preprints.
- Pascadi, arXiv:2511.08445, is described as accepted by GAFA in the
  Blomer--Pascadi bibliography, but no journal publication record was found
  in this audit as of 2026-08-11.  It is therefore labeled an accepted
  preprint, not a published input.

Pascadi's Forum of Mathematics, Pi **14** (2026) Corollary 5.11, KSWX's
JLMS **108** (2023) Theorem 2.1, and the Hu--Petrow--Young FMS article are
published.  Their quantitative or structural failures are recorded above.

## 8. Narrowest honest survivor

The primitive near-full-conductor core already requires an estimate of the
shape

\[
 \sum_{p=u_1u_2m}\mu(u_1)\mu(u_2)
 \sum_{\chi\bmod p}^{*}{\tau(\chi)^2\over p}
 \sum_{k,r}\overline{\chi}(kr)
 A_{p,r,k}(\chi),                                      \tag{22}
\]

with the actual smooth cutoffs and signs.  The full survivor is harder: it
must restore every \(f\mid p\) and both divisor sums in (8).

The exact \(3/10\) gap for ideal cancellation at fixed \((p,v)\) shows that
a theorem local in both outer families is insufficient.  A sufficient new
result must average \(p\) and at least one further source family before
absolute values or coefficient-blind Cauchy.  One possible theorem class is
a horizontal root-number-square/generalized-Gauss-product large sieve or a
relative trace formula that permits all of the following simultaneously:

1. \(p=u_1u_2m\) with \(\mu(u_1)\mu(u_2)\), including shared and repeated
   primes;
2. the two signed Möbius slots inside \(A\);
3. moving \(k,r\) and a coefficient jointly dependent on
   \((p,\chi,k,r)\);
4. all induced-character and nonunit divisor strata from (7).

No published theorem found in the audited classes has that left-hand side.
Consequently (6), not a primitive-only or unit-only substitute, is the
narrowest honest surviving estimate.

## 9. Exact checks

The arithmetic-only checks are:

```sh
python3 verify/a1_sq4_published_literature.py
diff -u verify/a1_sq4_published_literature.out \
  <(python3 verify/a1_sq4_published_literature.py)
lake build RH.Zeta85.Discharge.SQ4PublishedLiterature
lake env lean comparator/PrintAxioms/SQ4PublishedLiterature.lean
```

The verifier uses only `fractions.Fraction`.  The Lean printer covers every
headline rational/log theorem in the new module.  Neither checker asserts
(6), any cited analytic theorem, or any favorable applicability grant.
