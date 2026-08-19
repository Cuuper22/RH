> **Canonical reference**: [AXIOMS.md](../../AXIOMS.md) (Axioms 2–4: trace transfer and signed pairs). See also [GUIDE.md](../../GUIDE.md) topic index.

# Correlated four-Möbius moment for the SQ4 nonzero family

Status: **no proof of (SQ4-HB) is obtained.  There is an exact
multiplicative-character transform which retains all four Möbius factors, but
the full composite-modulus transform contains two generalized shifted Gauss
sums.  It becomes a Gauss-square twist only when both shifted residues are
units.  One coefficient-blind Cauchy/large-sieve step gives fixed-\(x\)
exponent \(199/100\), exceeding the literal budget by \(33/100\) and
(SQ4-HB) by \(1/2\).  On the squarefree stratum \((v_1,v_2)=1\), an exact
Ramanujan lift reaches Pascadi's 2026 level-aspect Kuznetsov geometry, but his
stated Corollary 5.11 (Corollary 17 in the arXiv version) has the first-index
coefficient \(e(k\omega)\) with one
fixed \(\omega\).  The source coefficient \(1/c_v(k)\) depends jointly on
that index and the level factor \(v\).  Applying the stated theorem separately
to every additive component and then recombining literally gives
\(513/200\), missing the budget by \(181/200\).  The previously tempting
\(47/20\) calculation is not a literal application.  It is retained below
only as conditional arithmetic under an explicit favourable general-sequence
and recombination grant; even that output exceeds the budget by \(69/100\)
and (SQ4-HB) by \(43/50\).  Writing \(g=(v_1,v_2)\), the Ramanujan lift also
vanishes when \(g\nmid k\) on nonsquarefree-\(v\) strata and cannot represent
the source sum there.  Blomer--Pascadi's July 2026 primary preprint does
literally estimate each fixed-\((p,v)\) \((k,r)\)-block, including its nonunit
indices after zero padding, but triangle summation in the two outer families
gives \(4111/1800\), exceeding the literal budget by \(1123/1800\).
The published Kerr--Shparlinski--Wu--Xi Type-I theorem can instead couple
the \((k,v)\)-slots on a favourable coprime-frequency/coefficient-energy
class, but its completed output is \(421/200\), exceeding the budget by
\(89/200\).**

The conclusions concern the precise method classes below.  They are not
lower bounds for the source family, and they do not exclude a signed
generalized-Gauss-product moment before Cauchy or a conductor-stratified trace
formula with nontrivial local data.

## 1. Granted nonzero family and exact scales

Start from family (33) of
docs/audit/sq4_simultaneous_routes.md.  It is the nonzero dual family after
reciprocity and Poisson summation in the smooth \(n\)-slot:

\[
 {M\over p}
 \sum_{u_1,u_2,m}\sum_{v_1,v_2}\sum_r\sum_{k\ne0}
 \mu(u_1)\mu(u_2)\mu(v_1)\mu(v_2)
 \Gamma_{\sigma,x}(r)\,\mathcal W_{T,x}(\cdots)
 S(k\overline{v_1v_2},\sigma r;u_1u_2m).               \tag{1}
\]

Here

\[
 p=u_1u_2m,\qquad v=v_1v_2,                             \tag{2}
\]

and, on the top nonzero dual block,

\[
 U=T^{43/200},\quad M=T^{2/5},\quad
 P=T^{83/100},\quad V=K=T^{43/100},\quad
 R=T^{33/50}.                                           \tag{3}
\]

Thus the completion prefactor has exponent

\[
 \operatorname{exp}(M/P)=-{43\over100}.                \tag{4}
\]

The fixed-\(x\) exponents to distinguish throughout are

\[
 \underbrace{{149\over100}}_{\text{(SQ4-HB)}}
 \quad\hbox{and}\quad
 \underbrace{{83\over50}}_{\text{literal budget}}.      \tag{5}
\]

The grant here is the same as in the preceding audit: (1) is used to test an
analytic continuation, but the missing smooth Heath--Brown recombination is
not silently supplied.

## 2. Exact multiplicative Mellin transform

Use the convention

\[
 S(a,b;p)=\sum_{z\bmod p}^{*}e\!\left({az+b\bar z\over p}\right),
 \qquad
 G_p(\chi;t)=\sum_{z\bmod p}^{*}\chi(z)e(tz/p).          \tag{6}
\]

For fixed \(p,k,r\), put

\[
 F_{p,k,r}(v)=S(k\bar v,r;p),\qquad
 v\in(\mathbb Z/p\mathbb Z)^\times.                     \tag{7}
\]

Its multiplicative Fourier transform is exact:

\[
 \boxed{
 \sum_{v\bmod p}^{*}\overline{\chi(v)}F_{p,k,r}(v)
       =G_p(\chi;k)G_p(\chi;r).}                        \tag{8}
\]

Indeed, expand the Kloosterman sum and put \(y=z\bar v\).  Then
\(v=z\bar y\), so the two finite sums separate.  In the \(z\)-sum, the
change \(w=\bar z\) gives the second copy of \(G_p(\chi;\cdot)\).  This uses
only finite changes of variables and \((v,p)=1\), the latter being supplied by
the source coprimality.

After a fixed Mellin separation of the smooth product cutoffs, define

\[
 A_i(\chi)=\sum_{v_i\asymp U}
   \mu(v_i)V_i(v_i/U)\chi(v_i),\qquad i=1,2.             \tag{9}
\]

Fourier inversion in (8) turns the \(v_1,v_2\)-sum into

\[
 {1\over\varphi(p)}\sum_{\chi\bmod p}
 A_1(\chi)A_2(\chi)G_p(\chi;k)G_p(\chi;r).              \tag{10}
\]

The two outer factors \(\mu(u_1)\mu(u_2)\) are still present in the
factorized varying modulus \(p=u_1u_2m\).  Thus (10) retains all four signed
slots; no Möbius factor has been replaced by its absolute value.

### 2.1 Why (10) is not plain character orthogonality

If \(\chi\) is primitive modulo \(p\) and \((kr,p)=1\), then

\[
 G_p(\chi;k)G_p(\chi;r)
   =\tau(\chi)^2\overline{\chi(kr)}.                    \tag{11}
\]

The factor is \(\tau(\chi)^2\), not
\(\tau(\chi)\tau(\bar\chi)=\chi(-1)p\).  Its phase varies with \(\chi\).
Consequently, applying character orthogonality as if (11) were a constant
multiple of \(\overline{\chi(kr)}\) would simply delete the Kloosterman
geometry and is invalid.

For an imprimitive character the two generalized Gauss sums in (8) also
carry conductor and gcd conditions.  Equation (8), rather than the primitive
simplification (11), is the source-faithful full-family identity.
In particular, the source condition \(k,r\ne0\) does not imply that either
residue is a unit modulo the composite \(p\).  The unit hypotheses in (11)
are essential and cannot be inferred from nonvanishing as integers.

### 2.2 CRT does not decouple the literal slots

On a coprime factorization \(p=p_1p_2\), with
\(\chi=\chi_1\chi_2\), CRT gives

\[
 G_p(\chi;t)=
 \chi_1(p_2)\chi_2(p_1)
 G_{p_1}(\chi_1;t)G_{p_2}(\chi_2;t).                   \tag{12}
\]

The complementary-modulus twists in (12) are squared in (11).  More
importantly, \(u_1,u_2,m\) are not pairwise coprime.  If
\(g=(u_1,u_2)\), then the squarefreeness of each Möbius variable gives the
unique decomposition

\[
 u_1=ga,\qquad u_2=gb,\qquad
 (g,a)=(g,b)=(a,b)=1,                                   \tag{13}
\]

with \(g,a,b\) squarefree, and

\[
 u_1u_2=g^2ab,\qquad
 \mu(u_1)\mu(u_2)=\mu(a)\mu(b).                         \tag{14}
\]

The common factor \(g\) has no remaining Möbius sign.  The smooth variable
\(m\) may share further primes with \(g^2ab\).  Hence a literal CRT treatment
must first stratify the prime powers of \(p\); replacing \(p\) by a squarefree
product of the displayed slots discards same-power strata.  The identical
observation applies to \(v_1,v_2\).

## 3. The coefficient-blind character moment is power-killed

Define the **generalized-Gauss-product/single-Cauchy class** to use (8)--(10), grant every
conductor, gcd, Mellin, divisor, and coefficient-energy loss logarithmic
exponent \(0\), grant normalized generalized Gauss factors power exponent
\(0\), and then apply one Cauchy inequality followed by one all-modulus
multiplicative large sieve.

The coefficient energies used below have explicit constructions.  If

\[
 b_v=\sum_{v_1v_2=v}\mu(v_1)\mu(v_2)
       V_1(v_1/U)V_2(v_2/U),
\]

then multiplicative-energy parametrization, or simply Cauchy in each product
cell followed by the divisor bound, gives

\[
 \sum_v|b_v|^2\ll_\varepsilon U^2T^\varepsilon
 =T^{43/100+\varepsilon}.                              \tag{14a}
\]

Likewise the collapsed \(kr\)-coefficient has energy
\(\ll_\varepsilon KRT^\varepsilon
=T^{109/100+\varepsilon}\), using
\(|\Gamma_{\sigma,x}(r)|\ll_\varepsilon T^\varepsilon\).
The analogous \(u_1u_2m\)-multiplicities are also divisor-bounded and cost
only the displayed \(T^\varepsilon\).  No fixed logarithm is hidden in these
grants.

There are \(T^{2(83/100)}\) modulus-character pairs.  The two \(v\)-slot
polynomials have product length \(T^{43/100}\), so the first norm has exponent

\[
 {2(83/100)+43/100\over2}={209\over200}.                \tag{15}
\]

The product of the \(k\)- and \(r\)-polynomials has length exponent

\[
 {43\over100}+{33\over50}={109\over100}.                \tag{16}
\]

The conductor family \(T^{166/100}\) dominates that length.  The second norm
therefore has exponent

\[
 {166/100+109/100\over2}={11\over8}.                    \tag{17}
\]

Restoring the completion prefactor (4), this prescribed chain gives

\[
 -{43\over100}+{209\over200}+{11\over8}
 ={199\over100}.                                        \tag{18}
\]

Consequently

\[
 {199\over100}-{83\over50}={33\over100},\qquad
 {199\over100}-{149\over100}={1\over2}.                 \tag{19}
\]

Physical integration subtracts \(23/100\) from both an output and its budget,
so the literal-budget excess remains \(33/100\).  The normalized auxiliary
logarithmic exponent in this favourable test is \(0\); restoring the two raw
long Heath--Brown slots adds exactly \((\log T)^2\).

This finishes only the coefficient-blind Cauchy class.  It does not estimate
the signed generalized-Gauss-product moment in (10) before Cauchy.

### 3.1 The exact diagonal created by Cauchy

For fixed \(p\asymp P\), the products \(v_1v_2\ll V\) are smaller than \(p\)
for all sufficiently large \(T\).  On the unit support, character Parseval is
therefore the exact integer identity

\[
 {1\over\varphi(p)}\sum_{\chi\bmod p}
 \left|\sum_v b_v\chi(v)\right|^2
 =\sum_v|b_v|^2.                                      \tag{19a}
\]

Opening the right-hand side gives the four-variable constraint

\[
 \sum_{v_1v_2=w_1w_2}
 \mu(v_1)\mu(v_2)\mu(w_1)\mu(w_2)
 V_1(v_1/U)V_2(v_2/U)
 \overline{V_1(w_1/U)V_2(w_2/U)}.                     \tag{19b}
\]

Thus the literal equality diagonal \(v_1=w_1,\ v_2=w_2\) becomes positive
inside the squared norm.  Off-diagonal representations of the same product
can still interact, so (19b) is not asserted as a lower bound for arbitrary
complex Mellin weights.  Its precise force is methodological: after Cauchy,
the original two Möbius signs have become the nonnegative energy (19a), and
no later coefficient-blind large sieve can recover their unsquared
correlation.

### 3.2 Freezing \(p,v\) and cancelling only \(k,r\) is power-killed

Define the **fixed-\((p,v)\) square-root class** to triangle-sum the \(p\)-
and \(v\)-families, grant Weil size \(P^{1/2}\) for each complete sum, and
grant ideal joint square-root cancellation over the \(KR\) pairs before
restoring the completion factor.  This prescribed chain has exponent

\[
 -{43\over100}+{83\over100}+{43\over100}
 +{43/100+33/50\over2}+{83\over200}
 ={179\over100}.                                      \tag{19c}
\]

Consequently

\[
 {179\over100}-{83\over50}={13\over100},\qquad
 {179\over100}-{149\over100}={3\over10}.              \tag{19d}
\]

Physical integration gives \(39/25\), still \(13/100\) above the integrated
budget.  The normalized auxiliary logarithmic exponent in this favourable
test is \(0\), and the raw exponent is exactly \(2\).  This kills only the
class which obtains square-root cancellation in \(k,r\) and then takes
absolute values in both outer families.  It is not a lower bound for a
fixed-modulus bilinear form; a route with stronger special-structure
cancellation would be a different class.

### 3.3 A fixed-modulus theorem applies literally but loses the outer signs

Blomer and Pascadi, *Bilinear forms with Kloosterman sums via quadratic
characters*, [arXiv:2607.24311v1](https://arxiv.org/abs/2607.24311), Theorem
5.5, give the following arbitrary-modulus estimate.  For \(1\le M,N\le c\),
intervals \(\mathcal I,\mathcal J\) of lengths \(M,N\), arbitrary complex
sequences, and \(a\in(\mathbb Z/c\mathbb Z)^\times\), their left side is

\[
 \sum_{\substack{m\in\mathcal I,n\in\mathcal J\\(m,n,c)=1}}
 \alpha_m\beta_n S(am,n;c),                             \tag{19e}
\]

and their bound is

\[
 |(19e)|\ll \|\alpha\|_2\|\beta\|_2c^{1+o(1)}H(M,N,c).
                                                               \tag{19f}
\]

The theorem defines the factor used here by

\[
\begin{aligned}
H(M,N,c)={}&
 {M^{1/8}((c+MN)(c+N^2))^{1/16}\over c^{1/4}}
   \min\!\left({c\over M},c^{1/2}\right)^{1/16}\\
&+\left({N^2\over c^2}
 +{N^{1/2}M(c+N^2)\over c^{5/2}}\right)^{1/16}
 +{M^{1/3}+N^{1/3}\over c^{1/5}}\\
&+{M^{1/2}N^{1/6}+M^{1/6}N^{1/2}\over c^{7/18}}
 +{M^{1/15}+N^{1/15}\over c^{1/15}}.                  \tag{19f'}
\end{aligned}
\]

When \(\mathcal I=\{1,\ldots,M\}\) and
\(\mathcal J=\{1,\ldots,N\}\), the theorem explicitly removes the gcd
constraint.  This last clause makes the following fixed-block substitution
literal, rather than a unit-stratum grant.  The apparent \((k,r)\)-coupling
in the Poisson profile also separates exactly before the invocation.  With
the profile notation of the source audit,

\[
 \widehat G_{p,v,r,x,T}(kM/p)=
 \int H_{p,v,x,T}(t)
 e\!\left(-{kMt\over p}\right)
 e\!\left(-{\sigma r\over pvMt}\right)\,dt,            \tag{19f''}
\]

where

\[
 H_{p,v,x,T}(t)=W_3(t)\widetilde W_{2,T}
       \!\left({vMtx\over T^{3/5}}\right)
\]

is independent of \(k,r\), compactly supported, and has uniformly bounded
\(L^1\)-norm.  Apply Theorem 5.5 pointwise in \(t\), with the two exponential
factors absorbed into the separate \(k\)- and \(r\)-coefficients, and then
integrate the bound.  The finite Mellin parameters used to separate the
remaining product cutoffs are treated in the same order.  Their absolute
integrals are fixed weight-dependent constants, so this exact separation
costs power exponent \(0\) and fixed logarithmic exponent \(0\).

Now fix \(p,v\), split the two signs of \(k\), and zero-pad the complete
truncated source coefficients into initial intervals of lengths
\(O(KT^\eta)\) and \(O(R)\).  At the power level, set

\[
 c=p,\qquad M=K,\qquad N=R,\qquad
 a=\sigma\operatorname{sgn}(k)\bar v.                  \tag{19g}
\]

More precisely, after writing \(k=\operatorname{sgn}(k)|k|\), the change
\(z\mapsto-z\) gives
\(S(A,-r;p)=S(-A,r;p)\).  Thus the theorem's unit is
\(a=\sigma\operatorname{sgn}(k)\bar v\), fixed on each of the two sign
blocks.  Source coprimality supplies \((v,p)=1\); also \(K,R<p\).  The
arbitrarily small \(T^\eta\) in the proved \(k\)-truncation preserves
\(KT^\eta<p\).  Thus every stated hypothesis of Theorem 5.5 holds for this
fixed-\((p,v)\) block.  The paper is a primary preprint as of this audit, not
a journal publication, and it averages neither \(p\) nor \(v\).

At the exact source exponents, the five positive summands defining its
factor \(H(K,R,p)\) have power exponents

\[
 {7\over320},\qquad {1\over3200},\qquad {27\over500},
 \qquad {71\over900},\qquad -{17\over1500}.             \tag{19h}
\]

The fourth dominates.  The two coefficient norms, the factor \(p\), and
\(H\) therefore give the fixed-block output

\[
 {43/100+33/50\over2}+{83\over100}+{71\over900}
 ={2617\over1800}.                                     \tag{19i}
\]

Triangle summation over \(p\) and \(v\), followed by the completion factor,
gives

\[
 -{43\over100}+{83\over100}+{43\over100}
   +{2617\over1800}={4111\over1800}.                   \tag{19j}
\]

Hence

\[
 {4111\over1800}-{83\over50}={1123\over1800},\qquad
 {4111\over1800}-{149\over100}={1429\over1800}.       \tag{19k}
\]

Physical integration gives \(3697/1800\), with the first excess unchanged.
The theorem's \(c^{o(1)}\) and the arbitrarily small Poisson-truncation power
are recorded as \(T^\varepsilon\), not as a fixed logarithm.  Zero padding
avoids a dyadic scale sum, so this class has normalized fixed logarithmic
exponent \(0\), and restoring the two raw long slots gives exponent exactly
\(2\).  The theorem is therefore genuinely applicable locally and the
outer-triangled chain is power-killed.  Any surviving use must couple at
least one of the \(p,v\) families to the bilinear estimate instead of taking
both in absolute value.

### 3.4 A published Type-I theorem couples \((k,v)\), but not enough

Kerr, Shparlinski, Wu, and Xi, *Bounds on bilinear forms with Kloosterman
sums*, Journal of the London Mathematical Society **108** (2023), 578--621,
[DOI](https://doi.org/10.1112/jlms.12753), Theorem 2.1, consider

\[
 S_{q,a}(\alpha)=
 \sum_{m\in\mathcal I}\alpha_m
 \sum_{n\in\mathcal J}K_q(m,an),                       \tag{19l}
\]

where \(q\) is any positive integer, \(\mathcal I,\mathcal J\) are integer
intervals of lengths \(M_{\rm th},N_{\rm th}\ge1\), \(\alpha\) is an arbitrary
complex sequence on \(\mathcal I\), \(a\in\mathbb Z\), and
\(d=(a,q)\).  Their theorem states

\[
 |S_{q,a}(\alpha)|\ll
 \|\alpha\|_2M_{\rm th}^{1/2}N_{\rm th}q^{1/2+o(1)}
 \Delta_1(M_{\rm th},N_{\rm th},q,d),                 \tag{19m}
\]

where one may freely choose any of

\[
\begin{aligned}
\Delta_{1a}={}&M_{\rm th}^{-1/4}N_{\rm th}^{-1}q^{1/2}d^{-1/4}
 +q^{1/2}N_{\rm th}^{-1}M_{\rm th}^{-1/2}
 +N_{\rm th}^{-1/2},\\
\Delta_{1b}={}&M_{\rm th}^{-1/2}
  (N_{\rm th}^{-3/4}q^{1/2}+d^{1/2})+N_{\rm th}^{-1/2},\\
\Delta_{1c}={}&M_{\rm th}^{-1/2}
  (N_{\rm th}^{-1}q^{1/2}+(qd)^{1/4})+N_{\rm th}^{-1/2}.
                                                               \tag{19n}
\end{aligned}
\]

Define the **favourable KSWX Type-I class** as follows.  Before collapsing
the numerator \(r=\ell h\), keep

\[
 L=T^{23/100},\qquad H=T^{43/100}.                     \tag{19o}
\]

Fix \(p,\ell\) and the Fourier variable \(t\).  Put \(q=p\), take
\(\mathcal I\) to be a full residue interval of length
\(M_{\rm th}=p\), take \(\mathcal J\) to be the \(h\)-interval of length
\(N_{\rm th}=H\), and collapse the \((k,v)\)-pairs into

\[
 \alpha_m(t)=
 \sum_{\substack{k,v\\k\bar v\equiv m\pmod p}}
   b_{k,v}\,e(-kMt/p),                                 \tag{19p}
\]

where \(b_{k,v}\) includes the two \(v\)-side Möbius signs and all fixed
source weights.  Then
\(K_p(m,\sigma\ell h)=S(k\bar v,\sigma\ell h;p)\)
term by term.  Smooth partial summation turns the fixed \(h\)-profile into
interval indicators with total variation \(O(1)\), so that step has power
and fixed logarithmic exponents \(0\).

The reciprocity phase omitted in (19p) is not a grant.  Uniformly on the
source support,

\[
 e\!\left(-{\sigma\ell h\over pvMt}\right)=1+O(T^{-1}).
                                                               \tag{19q}
\]

The already-audited direct Weil/triangle output is
\(467/200+\eta+\varepsilon\), where \(\eta>0\) is the Poisson-truncation
loss and \(\varepsilon>0\) contains the aggregate divisor/theorem loss.
The replacement error therefore has exponent

\[
 {267\over200}+\eta+\varepsilon.                       \tag{19r}
\]

Choose the explicit admissible allocation
\(\eta=1/20\), \(\varepsilon=1/20\).  It respects \(0<\eta<2/5\), gives
error exponent \(287/200\), and leaves the exact margin

\[
 {149\over100}-{287\over200}={11\over200}.             \tag{19r'}
\]

What remains favourable and unproved is stated explicitly: restrict to
\((\ell,p)=1\), so \(d=1\), and grant the collapsed coefficient energy

\[
 \|\alpha(t)\|_2\ll_\varepsilon T^{43/100+\varepsilon}
                                                               \tag{19s}
\]

uniformly in \(p,\ell,t\).  Thus this is not a full-source application and
does not assert the noncoprime frequency strata or (19s).

With \(M_{\rm th}=q=T^{83/100}\), \(N_{\rm th}=T^{43/100}\), and \(d=1\),
the three choices in (19n) have exponents

\[
 \operatorname{exp}\Delta_{1a}=-{43\over200},\qquad
 \operatorname{exp}\Delta_{1b}=-{43\over200},\qquad
 \operatorname{exp}\Delta_{1c}=-{83\over400}.         \tag{19t}
\]

The first two attain the better saving.  Equation (19m), together with the
grant (19s), therefore has per-\((p,\ell)\) exponent

\[
 {43\over100}+{83\over200}+{43\over100}+{83\over200}
 -{43\over200}={59\over40}.                            \tag{19u}
\]

Restoring completion and triangle-summing the \(p\)- and \(\ell\)-families
gives

\[
 -{43\over100}+{83\over100}+{23\over100}+{59\over40}
 ={421\over200}.                                       \tag{19v}
\]

Hence the excesses over the literal budget and (SQ4-HB) are exactly

\[
 {421\over200}-{83\over50}={89\over200},\qquad
 {421\over200}-{149\over100}={123\over200}.           \tag{19w}
\]

Physical integration gives \(15/8\), leaving the first excess unchanged.
The theorem's \(q^{o(1)}\) is recorded as \(T^\varepsilon\), not a fixed
logarithm.  This class has normalized fixed logarithmic exponent \(0\) and
raw exponent exactly \(2\).  It couples both \(v\)-side signs to the
Kloosterman kernel before the norm, but even the favourable energy and
coprimality grants do not close the power budget.  A survivor must additionally
use the \(p\)- or \(\ell\)-family, improve (19s), or exploit structure outside
this Type-I theorem.

## 4. Exact Ramanujan lift and its boundary

For \((p,v)=1\), ordinary CRT gives a second exact identity:

\[
 \boxed{S(k,rv;pv)=c_v(k)S(k\bar v,r;p),}               \tag{20}
\]

where \(c_v(k)=S(k,0;v)\) is the Ramanujan sum.  The factor modulo \(p\) in
the CRT product is the source sum, while the factor modulo \(v\) is
\(S(k\bar p,0;v)=c_v(k)\).

If \(v\) is squarefree, then \(c_v(k)\ne0\) for every \(k\), and

\[
 {1\over c_v(k)}
 =\mu(v)\sum_{d\mid(v,k)}\mu(d){d\over\varphi(d)}.       \tag{21}
\]

On the stratum \((v_1,v_2)=1\), one also has
\(\mu(v)=\mu(v_1)\mu(v_2)\).  Thus the factor \(\mu(v)\) in (21)
cancels the two original \(v\)-side Möbius signs exactly.  The lifted
coefficient-norm theorem cannot recover cancellation from those signs after
this division.

Formula (21) follows prime by prime from

\[
 c_\ell(k)=
 \begin{cases}
   -1,&\ell\nmid k,\\
   \ell-1,&\ell\mid k.
 \end{cases}                                            \tag{22}
\]

The divisibility condition \(d\mid k\) in (21) has the explicit additive
resolution

\[
 {\bf1}_{d\mid k}={1\over d}\sum_{a\bmod d}e(ak/d).      \tag{23}
\]

For each fixed pair \((d,a)\), (23) has the fixed additive \(k\)-phase needed
by Pascadi's Corollary 5.11.  Recombining all pairs is not a
\(T^\varepsilon\)-cost for free; the literal triangle calculation is carried
out in Section 5.1.

The nonsquarefree boundary is exact.  Write

\[
 v_1=ga,\qquad v_2=gb,\qquad (g,a)=(g,b)=(a,b)=1.        \tag{24}
\]

Then \(v=g^2ab\), and the standard formula

\[
 c_v(k)=\mu\!\left({v\over(v,k)}\right)
 {\varphi(v)\over\varphi(v/(v,k))}                      \tag{25}
\]

shows that \(c_v(k)\ne0\) exactly when \(g\mid k\).  Hence (20) cannot be
divided by \(c_v(k)\) on the source subfamily \(g\nmid k\).  Since a fixed
nontrivial \(g\) causes no power reduction in the original dyadic family,
that subfamily cannot be omitted from a full-family proof.

## 5. Pascadi geometry: exact coefficient mismatch and a favourable grant

On the squarefree-\(v\) stratum, insert (20)--(23).  Put

\[
 d_u=u_1u_2,\qquad q=d_uv,\qquad n'=vr.                 \tag{26}
\]

The lifted ordinary Kloosterman sum is

\[
 S(k,n';qm),                                             \tag{27}
\]

with exact scales

\[
 q=T^{43/50},\qquad k=T^{43/100},\qquad
 n'=T^{109/100},\qquad m=T^{2/5}.                       \tag{28}
\]

The source profiles have uniformly bounded scaled derivatives, as proved in
the preceding reciprocity audit.  Fixed Mellin inversion separates the
remaining product profiles.  The signed factorizations of \(q\) and \(n'\)
may be collected into a level-dependent sequence \(a_{n',q}\), and for an
arbitrary such sequence Pascadi's Assumption 5.4 (Assumption 14 in the
arXiv version) applies with \(Y_N=1\) and
\(A_{N,q}\asymp\lVert a_{\cdot,q}\rVert_2\).

This does **not** yet match the stated corollary.  Its first-index coefficient
is exactly \(e(k\omega)\), with one \(\omega\) fixed throughout the level
average.  In contrast, (21) contributes

\[
 {1\over c_v(k)}=\mu(v)\sum_{d\mid v}\mu(d){d\over\varphi(d)}
                 {\bf1}_{d\mid k},                     \tag{28a}
\]

and therefore depends simultaneously on \(k\) and on the level factor
\(v\).  Additively resolving \({\bf1}_{d\mid k}\) makes
\(\omega=a/d\), but \(d\mid v\), so no single invocation has a fixed phase
for the complete source.  Swapping the two Kloosterman indices merely moves
the problem: the other coefficient then contains the level-dependent
factorization \(n'=vr\).  Pascadi's Corollary 5.9 (Corollary 16 in the arXiv
version) allows two general sequences
only at fixed level and loses the horizontal level average.

The published source is Alexandru Pascadi, *Large sieve inequalities for
exceptional Maass forms and the greatest prime factor of \(n^2+1\)*,
Forum of Mathematics, Pi **14** (2026), e8,
[DOI](https://doi.org/10.1017/fmp.2026.10025), Corollary 5.11 and equations
(5.31)--(5.32).

### 5.1 Literal Corollary 5.11 after additive resolution

There is a literal, but power-expensive, way to respect the fixed-phase
hypothesis.  Apply the corollary separately for every fixed \(d\mid v\) and
\(a\bmod d\) in (23).  The phase \(\omega=a/d\) is then fixed within that
invocation, while the restriction \(d\mid v\) is placed in the allowed
level-dependent coefficient \(a_{n',q}^{(d)}\).

The literal hypothesis map for each such invocation is:

| Corollary 5.11, equation (5.32) | Source component |
|---|---|
| \(r_{\rm th}\sim R_{\rm th}\) | \(r_{\rm th}=1\), \(R_{\rm th}=1/2\), so \(R_{\rm th}<r_{\rm th}\le2R_{\rm th}\) |
| \(s_{\rm th}\sim S_{\rm th}\) | \(s_{\rm th}=q=(u_1u_2)v\), exponent \(43/50\) |
| \(m_{\rm th}\sim M_{\rm th}\) | \(m_{\rm th}=|k|\), exponent \(43/100\) |
| \(n_{\rm th}\sim N_{\rm th}\) | \(n_{\rm th}=n'=vr\), exponent \(109/100\) |
| \(c_{\rm th}\sim C_{\rm th}\) | the source smooth quotient \(m_0\), exponent \(2/5\) |
| fixed \(e(m_{\rm th}\omega)\) | \(\omega=a/d\), fixed for this invocation |
| \(a_{n_{\rm th},r_{\rm th},s_{\rm th}}\) | all signed source factorizations with \(d\mid v\) |
| \((r_{\rm th},s_{\rm th})=1\) and \((c_{\rm th},r_{\rm th})=1\) | automatic because \(r_{\rm th}=1\) |
| Assumption 5.4 | arbitrary second-index coefficient, \(Y_N=1\), \(A_{N,q}\asymp\|a_{\cdot,q}\|_2\) |
| \(\Phi_{r_{\rm th},s_{\rm th}}\) | the bounded-derivative source profile after the fixed Mellin separations |
| one consistent \(\pm\) sign | the fixed source sign \(\sigma\) |

The support bounds \(R_{\rm th},S_{\rm th}\ge1/2\), the positive length
bounds, and the smooth derivative hypotheses follow from the displayed
scales and the source profile audit.  The Mellin integrals have fixed
weight-dependent absolute mass and logarithmic exponent \(0\).  Assumption
5.4 (Assumption 14 in the arXiv version) with \(Y_N=1\) is the
general-sequence baseline.  Published Theorem 1.2, applied to the twisted
sequence \(e(n\xi/N)a_n\), verifies this instance: the twist does not change
the coefficient norm, and the theorem's \(X\)-range contains the range
required here.  This direct deduction avoids relying on the different norm
normalization printed in the example following Assumption 5.4.  Its
\((QN)^\varepsilon\) loss is recorded as \(T^\varepsilon\), not as a fixed
logarithmic exponent.

The coefficient norm has an explicit \(d\)-saving.  On the coprime
squarefree-\(v\) stratum, allocate every prime of \(d\) uniquely to
\(d=d_1d_2\), where \(d_i\mid v_i\).  There are at most
\(2^{\omega(d)}\) allocations, and

\[
 \#\{v_i\asymp U:d_i\mid v_i\}
 \le {U\over d_i}+1\le {3U\over d_i}                  \tag{28b}
\]

for every allocation which occurs.  Hence the direct cell count (31a)
sharpens to

\[
 \sum_{q,n'}|w_q a_{n',q}^{(d)}|^2
 \ll_\varepsilon {T^{38/25+\varepsilon}\over d},
 \qquad
 \|w_qA_{N,q}^{(d)}\|_2
 \ll_\varepsilon T^{19/25+\varepsilon}d^{-1/2}.       \tag{28c}
\]

The coefficient of each additive phase is \(1/\varphi(d)\), and there are
\(d\) phases.  Separate application followed by triangle inequality therefore
costs

\[
 \sum_{d\le V}{d\over\varphi(d)}d^{-1/2}
 \ll_\varepsilon\sum_{d\le V}d^{-1/2+\varepsilon}
 \ll_\varepsilon V^{1/2+\varepsilon}.                 \tag{28d}
\]

Thus the literal recombination adds power exponent \(43/200\) to the
geometry calculation below.  Its output before completion is

\[
 {139\over50}+{43\over200}={599\over200},              \tag{28e}
\]

and after completion it is

\[
 {599\over200}-{43\over100}={513\over200}.             \tag{28f}
\]

This exceeds the literal budget and (SQ4-HB), respectively, by

\[
 {513\over200}-{83\over50}={181\over200},\qquad
 {513\over200}-{149\over100}={43\over40}.              \tag{28g}
\]

The two signs of \(k\) cost a fixed factor \(2\), with logarithmic exponent
\(0\).  Splitting \(1\le |k|\ll KT^\eta\) into the dyadic blocks required by
the theorem contributes \((\log T)^1\).  The literal normalized/raw fixed
logarithmic exponents of this class are therefore \(1\) and \(3\).  All
remaining divisor, cell-multiplicity, Mellin, and theorem losses in
(28b)--(28d) are the displayed \(T^\varepsilon\).

This is a genuine application of the stated published theorem to each
squarefree-\(v\) component and a source-faithful triangle recombination of
those components.  It is power-killed and still does not cover the
nonsquarefree \(g\nmid k\) family.

### 5.2 Favourable general-first-sequence grant

Pascadi remarks immediately after Corollary 5.11 that a level-averaged version
with a fixed general first-index sequence \(b_k\) can be stated, replacing a
factor \(\sqrt K\) by \(\lVert b\rVert_2\), but the paper does not state that
theorem and says its exceptional parameter \(T_0\) must be changed using the
Deshouillers--Iwaniec general-sequence theorem.  For the conditional geometry
calculation, grant that unstated variant with the same rational geometry and
a power-neutral adjusted \(T_0\).

For fixed \(d\), take \(b_k^{(d)}={\bf1}_{d\mid k}\).  Then
\(\lVert b^{(d)}\rVert_2\ll(K/d)^{1/2}\), while (28c) supplies the other
\(d^{-1/2}\).  Multiplication by \(d/\varphi(d)\) from (28a) leaves
\(1/\varphi(d)\), and the elementary identity

\[
 {n\over\varphi(n)}=\sum_{e\mid n}{\mu(e)^2\over\varphi(e)}
\]

gives

\[
 \sum_{d\le V}{1\over\varphi(d)}
 \le \log(2V)\sum_{e\ge1}{\mu(e)^2\over e\varphi(e)}
 =\log(2V)\prod_{\ell\ {\rm prime}}
   \left(1+{1\over\ell(\ell-1)}\right)
 \ll\log(2V).                                           \tag{28h}
\]

Thus this grant recombines (28a) with no additional power and with one
explicit logarithm.  In the second form of the corollary, the formal
parameters are

\[
 R_{\rm th}={1\over2},\quad S_{\rm th}=q,\quad
 M_{\rm th}=K,\quad N_{\rm th}=VR,\quad C_{\rm th}=M.   \tag{29}
\]

The exceptional-spectrum factor is power-neutral because

\[
 {C_{\rm th}\over R_{\rm th}\sqrt{S_{\rm th}Y_N}}
 \asymp T^{\,2/5-43/100}=T^{-3/100}.                   \tag{30}
\]

The fixed factor \(R_{\rm th}^{-1}=2\) has power and logarithmic exponent
zero and is suppressed in the exponent identity (30).

The corollary's prefactor and the favourable source coefficient norm have
exponents

\[
 {43/50+43/100\over2}={129\over200},\qquad
 {43/50+33/50\over2}={19\over25}.                       \tag{31}
\]

The second exponent is backed by the direct cell-count construction

\[
 \sum_{q,n'}|w_q a_{n',q}|^2
 \ll_\varepsilon
 T^\varepsilon\,U^4R
 =T^{38/25+\varepsilon}.                               \tag{31a}
\]

Indeed, a source tuple \((u_1,u_2,v_1,v_2,r)\) determines
\((q,n')=((u_1u_2)(v_1v_2),(v_1v_2)r)\); Cauchy in each cell costs only
its divisor-bounded representation multiplicity.  The square root of
(31a) has exponent \(19/25\).

The four terms in its rational geometry factor have exponents

\[
\begin{aligned}
 S_{\rm th}\sqrt{R_{\rm th}}C_{\rm th} &: {63\over50},\\
 \sqrt{M_{\rm th}N_{\rm th}} &: {19\over25},\\
 \sqrt{S_{\rm th}M_{\rm th}}C_{\rm th} &: {209\over200},\\
 \sqrt{S_{\rm th}N_{\rm th}}C_{\rm th} &: {11\over8}.
\end{aligned}                                           \tag{32}
\]

Therefore the quotient of the two numerator factors by the denominator in
Pascadi's equation (5.32) has exponent \(11/8\).  Before the Poisson
prefactor the output is

\[
 {129\over200}+{19\over25}+{11\over8}={139\over50}.     \tag{33}
\]

After (4), the fixed-\(x\) exponent is

\[
 -{43\over100}+{139\over50}={47\over20}.                \tag{34}
\]

It misses the two targets by

\[
 {47\over20}-{83\over50}={69\over100},\qquad
 {47\over20}-{149\over100}={43\over50}.                 \tag{35}
\]

The top \(k\)-range calculation may favourably set its auxiliary logarithmic
exponent to \(0\) when testing the power obstruction.  A literal application
of the granted variant stated on \(k\asymp K_0\), summed over the complete range
\(1\le |k|\ll KT^\eta\), uses at most
\(1+\lceil\log_2(KT^\eta)\rceil\) blocks and hence contributes the explicit
factor \((\log T)^1\).  The \(d\)-recombination (28h) contributes a second
explicit \((\log T)^1\).  The conditional class therefore has
normalized/raw fixed logarithmic exponents \(2\) and \(4\), respectively.
The granted theorem's remaining losses are displayed as \(T^\varepsilon\).

Thus \(47/20\) is a **conditional arithmetic output**, not an application of
the published corollary to the source.  The grant is deliberately favourable:
it supplies the missing general-first-sequence level average and a
power-neutral exceptional factor.  Even under that grant the chain is
power-killed.  It also does not
cover the \(g\nmid k\) strata in (24)--(25).

## 6. Exact surviving estimate

Let \(\mathcal Z_{33}^{\rm nz}(T,x)\) denote the literal sum (1), including
its full source weight, and put \(P=T^{83/100}\).  Define exactly

\[
 \mathfrak M_4(T,x):={P\over M}\mathcal Z_{33}^{\rm nz}(T,x). \tag{36}
\]

For clarity, (8) gives the following exact character representation.  With

\[
\begin{aligned}
 A_{u_1,u_2,m,r,k,x,T}(\chi)
 :=\sum_{v_1,v_2}
 &\mu(v_1)\mu(v_2)\,
 \mathcal W_{T,x}(u_1,u_2,m,v_1,v_2,r,k)\\
 &\times\chi(v_1v_2),
\end{aligned}
\]

one has

\[
\begin{aligned}
 \mathfrak M_4(T,x)=
 \sum_{u_1,u_2,m,r,k\ne0}
 &\mu(u_1)\mu(u_2)\Gamma_{\sigma,x}(r)
 {P\over p\varphi(p)}\\
 &\times\sum_{\chi\bmod p}
 A_{u_1,u_2,m,r,k,x,T}(\chi)
 G_p(\chi;k)G_p(\chi;\sigma r).
\end{aligned}                                          \tag{36a}
\]

All source cutoffs in (1) are inside the displayed \(A\)-coefficient; no
separability is assumed in (36a).  Normalizing the two generalized Gauss
sums by \(p^{1/2}\) leaves the factor \(P/\varphi(p)\), which is
\(O_\varepsilon(T^\varepsilon)\) on \(p\asymp P\) by the elementary bound
\(p/\varphi(p)\ll_\varepsilon p^\varepsilon\).

The exact full-family target sufficient for (SQ4-HB) is

\[
 \boxed{|\mathfrak M_4|\ll_{\varepsilon,\mathbf W}
 T^{48/25+\varepsilon}(\log T)^0.}                     \tag{37}
\]

Indeed, \(48/25-43/100=149/100\).  Merely closing the literal fixed-\(x\)
budget would require the weaker exponent \(209/100\) in (37).  The
coefficient-blind character chain gives \(121/50\) before completion, missing
these two pre-completion targets by \(1/2\) and \(33/100\), respectively.
The exponent \(0\) in (37) is the normalized long-log exponent; restoring the
two raw Heath--Brown long slots changes it to exactly \(2\).

No primary theorem audited here has left side (36).  The locally applicable
Blomer--Pascadi preprint freezes both \(p\) and \(v\); Pascadi's published
level theorem reaches only the squarefree-\(v\) Ramanujan-lift components;
the published KSWX Type-I theorem reaches (19l) only after the explicit
coprime-frequency and coefficient-energy grants in (19s).
The required full estimate must retain the two Möbius character polynomials,
both generalized shifted Gauss sums (specializing to the Gauss-square phase
only on unit strata), and the two Möbius factors in the varying composite
modulus before Cauchy.  This is the exact analytic blocker.  The statement is
not a claim that no such theorem can exist.

## 7. Formal and independent checks

`RH/Zeta85/Discharge/SQ4CorrelatedMoment.lean` proves only the rational power
and fixed-log calculations, including (19h)--(19k), (19r)--(19w), and the
corrected Corollary 5.11 geometry in (28e)--(35).  It declares no analytic
input and does not assert any cited analytic theorem, the Ramanujan lift
(20), the coefficient grant (19s), or the target (37).

`RH/Zeta85/Discharge/SQ4GaussSquareTransform.lean` separately proves the
exact finite transform (8), its Dirichlet-character inversion, the generalized
Gauss-product formula for arbitrary residues over composite moduli, and the
Gauss-square specialization under explicit unit hypotheses.  It declares no
analytic estimate.

The independent checkers use only `fractions.Fraction`:

    lake build RH.Zeta85.Discharge.SQ4CorrelatedMoment \
      RH.Zeta85.Discharge.SQ4GaussSquareTransform
    lake env lean comparator/PrintAxioms/SQ4CorrelatedMoment.lean
    lake env lean comparator/PrintAxioms/SQ4GaussSquareTransform.lean
    python3 verify/a1_sq4_correlated_moment.py
    diff -u verify/a1_sq4_correlated_moment.out \
      <(python3 verify/a1_sq4_correlated_moment.py)
    python3 verify/a1_sq4_gauss_square_transform.py
    diff -u verify/a1_sq4_gauss_square_transform.out \
      <(python3 verify/a1_sq4_gauss_square_transform.py)

The printer reports only [propext, Classical.choice, Quot.sound] for every
selected theorem.
