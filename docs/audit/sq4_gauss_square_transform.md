> **Canonical reference**: [AXIOMS.md](../../AXIOMS.md) (Axioms 2–4: trace transfer and signed pairs). See also [GUIDE.md](../../GUIDE.md) topic index.

# Finite Gauss-square transform for the SQ4 survivor

Status: **the finite multiplicative transform and its Dirichlet-character
inversion are proved in Lean for every modulus, including composite moduli.
They do not prove `(SQ4-HB)`.  The full source family contains nonunit
frequency strata, where the exact transform is a product of two shifted
Gauss sums rather than a Gauss square.  The remaining analytic statement is
the signed, conductor-stratified level moment in (14), before a
coefficient-blind Cauchy inequality.**

This note isolates the exact algebra behind family (33) of
`docs/audit/sq4_simultaneous_routes.md`.  It supplies no complete-sum bound,
primitivity assumption, CRT recombination, or smooth Heath--Brown
recombination.

## 1. Exact transform, with conventions fixed

Let \(q\ge1\), let \(G_q=(\mathbb Z/q\mathbb Z)^\times\), and let

\[
 \psi_q(t)=e(t/q),\qquad
 G_q(\chi;a)=\sum_{z\bmod q}^{*}\chi(z)\psi_q(az).       \tag{1}
\]

Use the complete-sum convention

\[
 S(a,b;q)=\sum_{z\bmod q}^{*}\psi_q(az+b\bar z).        \tag{2}
\]

For arbitrary residue classes \(k,r\bmod q\), define

\[
 F_{q,k,r}(v)=S(k\bar v,r;q),\qquad v\in G_q,            \tag{3}
\]

and fix the inverse-character Fourier convention

\[
 \widehat F(\chi)=\sum_{v\bmod q}^{*}\chi(v)^{-1}F(v).  \tag{4}
\]

Then the exact identity is

\[
 \boxed{\widehat F_{q,k,r}(\chi)
        =G_q(\chi;k)G_q(\chi;r).}                       \tag{5}
\]

No condition on \((kr,q)\), no primitivity condition on \(\chi\), and no
squarefreeness condition on \(q\) is used in (5).  Expanding (4), use the
bijection

\[
 (v,z)\longmapsto(w,y)=(\bar v z,\bar z),qquad
 (w,y)\longmapsto(v,z)=((wy)^{-1},y^{-1}).              \tag{6}
\]

The character factor becomes

\[
 \chi(v)^{-1}=\chi(w)\chi(y),                           \tag{7}
\]

and the additive character splits into
\(\psi_q(kw)\psi_q(ry)\).  This proves (5) without an
estimate.

The Lean theorem
`kloosterman_transform_eq_gauss_product` proves (5) over the unit group of
an arbitrary commutative ring with finite unit group.  The more general
`correlation_transform_factorization` proves the same change of variables
for arbitrary functions in place of the two additive phases.

## 2. Exact inversion and the unit-stratum square

Character orthogonality gives

\[
 \boxed{
 F_{q,k,r}(v)={1\over\varphi(q)}
   \sum_{\chi\bmod q}\chi(v)
       G_q(\chi;k)G_q(\chi;r).}                         \tag{8}
\]

Here the sum is over all Dirichlet characters modulo \(q\), equivalently all
characters of \(G_q\).  The Lean theorem
`dirichlet_fourier_inversion` proves the inversion formula for every function
on \(G_q\), and `kloosterman_kernel_character_inversion` specializes it to
(8).  Thus both directions of the finite transform are machine-verified.

If \(a\in G_q\), reindexing \(z\mapsto a z\) gives

\[
 G_q(\chi;a)=\chi(a)^{-1}G_q(\chi;1).                  \tag{9}
\]

This scaling identity does **not** require \(\chi\) to be primitive.  Hence,
only on the stratum \((kr,q)=1\),

\[
 G_q(\chi;k)G_q(\chi;r)
 =\chi(kr)^{-1}G_q(\chi;1)^2.                          \tag{10}
\]

For an ordinary finite complex character,
\(\chi(a)^{-1}=\overline{\chi(a)}\).  The formal statement uses inverse
values in \(\mathbb C^\times\), so it does
not hide a nonvanishing or unitarity premise.  Theorems
`unitGaussSum_unit_scale` and
`kloosterman_transform_eq_gauss_square` prove (9)--(10).

The phase in (10) is a **Gauss square**.  It is not
\(G_q(\chi;1)G_q(\bar\chi;1)\), so character orthogonality cannot replace it
by a character-independent multiple of \(q\).

## 3. Composite-modulus and gcd boundary

The nonzero Poisson condition \(k\ne0\), even together with \(|k|<q\), does
not imply \((k,q)=1\).  The source numerator \(r\) is likewise not restricted
to be coprime to \(q\).  Consequently (10) is not a full-family identity.
The source-faithful formula on every gcd stratum is (5) or (8), retaining the
two generalized shifted Gauss sums.

For imprimitive characters those shifted sums have conductor- and
gcd-dependent support.  No pointwise \(q^{1/2}\) size, and no primitive
reduction, follows from the algebra proved here.

If \(q=q_1q_2\) with \((q_1,q_2)=1\), CRT gives, with the induced local
characters,

\[
 G_q(\chi;t)=
 \chi_1(q_2)\chi_2(q_1)
 G_{q_1}(\chi_1;t)G_{q_2}(\chi_2;t).                   \tag{11}
\]

Equivalently, before scaling the local additive arguments, the two local
sums have arguments \(t\bar q_2\bmod q_1\) and
\(t\bar q_1\bmod q_2\).  These complementary-modulus twists remain in the
local moment and are squared on the unit Gauss-square stratum.

In the actual source modulus

\[
                         p=u_1u_2m,                     \tag{12}
\]

the three displayed factors are not pairwise coprime.  In particular, if
\(g=(u_1,u_2)\), then the two squarefree Möbius variables have the unique
form \(u_1=ga,u_2=gb\), with \(g,a,b\) pairwise coprime, and
\(u_1u_2=g^2ab\).  The smooth variable \(m\) may share further primes.
Therefore a local CRT continuation must first stratify prime powers and all
shared gcds.  Applying a squarefree CRT factorization directly to
\(u_1,u_2,m\) would delete source strata.

## 4. The exact analytic moment still needed

Return to the nonzero family after reciprocity and Poisson summation, with

\[
 U=T^{43/200},\quad M=T^{2/5},\quad
 P=T^{83/100},\quad K=V=T^{43/100},\quad R=T^{33/50}.    \tag{13}
\]

Let \(\mathcal Z_{33}^{\rm nz}(T,x)\) be the literal family (33), including
its full source weight, and define the pre-completion moment

\[
 \mathfrak M_4(T,x)={P\over M}\mathcal Z_{33}^{\rm nz}(T,x).
\]

For \(p=u_1u_2m\), put all \(v_1,v_2\)-dependent source cutoffs, without a
separability assumption, into

\[
 A_{u_1,u_2,m,r,k,x,T}(\chi)
 =\sum_{v_1,v_2}\mu(v_1)\mu(v_2)
   \mathcal W_{T,x}(\cdots)\chi(v_1v_2).
\]

The exact inversion (8) gives

\[
\begin{aligned}
 \mathfrak M_4(T,x)=
 \sum_{u_1,u_2,m,r,k\ne0}
 &\mu(u_1)\mu(u_2)\Gamma_{\sigma,x}(r)
 {P\over p\varphi(p)}                                  \\
 &\times\sum_{\chi\bmod p}
 A_{u_1,u_2,m,r,k,x,T}(\chi)
 G_p(\chi;k)G_p(\chi;\sigma r).                       \tag{14}
\end{aligned}
\]

Formula (14), with the generalized products on all nonunit strata and the
Gauss-square phase on the unit strata, is the exact surviving analytic
object.  A sufficient estimate for `(SQ4-HB)` is

\[
 \boxed{|\mathfrak M_4(T,x)|
   \ll_{\varepsilon,\mathbf W}T^{48/25+\varepsilon}.}   \tag{15}
\]

Indeed, restoring the completion exponent
\(M/P=T^{-43/100}\) gives
\(48/25-43/100=149/100\).  The weaker literal fixed-\(x\) budget would require
the pre-completion exponent \(209/100\).  The already-audited
coefficient-blind Cauchy chain has pre-completion exponent \(121/50\),
exceeding (15) by exactly \(1/2\) and the literal target by \(33/100\).
Restoring the two unnormalized long slots contributes exactly
\((\log T)^2\).

Thus the missing analytic result is not ordinary character orthogonality.
It must estimate (14) while retaining the two outer Möbius factors, the two
Möbius factors inside \(A(\chi)\), the varying factorized composite modulus,
the Gauss-square phase, and every nonunit conductor/gcd stratum before a
coefficient-blind Cauchy step.  No such estimate is asserted here.

## 5. Formal and independent checks

`RH/Zeta85/Discharge/SQ4GaussSquareTransform.lean` declares no analytic
input and contains no placeholder.  It proves six exact finite-algebra
theorems: the abstract correlation transform, the Gauss-product transform,
unit scaling, the Gauss-square specialization, Dirichlet Fourier inversion,
and the source kernel inversion.

The independent power checker uses only `fractions.Fraction`:

```sh
lake build RH.Zeta85.Discharge.SQ4GaussSquareTransform
lake env lean comparator/PrintAxioms/SQ4GaussSquareTransform.lean
python3 verify/a1_sq4_gauss_square_transform.py
diff -u verify/a1_sq4_gauss_square_transform.out \
  <(python3 verify/a1_sq4_gauss_square_transform.py)
```

The comparator reports only
`[propext, Classical.choice, Quot.sound]` for each selected theorem.
