# CRT and conductor strata for the SQ4 Gauss product

Status: **exact finite CRT, gcd, conductor-support, and imprimitive
conductor-formula identities are proved in Lean.  The conductor theorem is
for an explicitly induced arbitrary complex primitive Dirichlet character;
an independent finite checker additionally calibrates 3,336 real-character
cases.  No estimate for `(SQ4-HB)` is obtained.**

This note starts from the generalized product in family (33),

\[
 G_p(\chi;k)G_p(\chi;\sigma r),\qquad p=u_1u_2m,
\]

with neither \(k\) nor \(r\) assumed to be a unit modulo the composite
modulus \(p\).  Here

\[
 G_q(\chi;t)=\sum_{z\bmod q}^{*}\chi(z)e(tz/q).
\]

The conclusions below retain all nonunit and imprimitive strata.

## 1. Exact CRT identity

Let \(q=q_1q_2\), with \((q_1,q_2)=1\).  Transport a global unit character
and additive character through

\[
 \mathbb Z/q\mathbb Z\simeq
 \mathbb Z/q_1\mathbb Z\times\mathbb Z/q_2\mathbb Z.
\]

Write the resulting restrictions as \(\chi_i,\psi_i\), and let \(t_i\) be
the image of \(t\) in the two factors.  Then, for every residue \(t\),

\[
 \boxed{G_q(\chi;t)
   =G_{q_1}(\chi_1,\psi_1;t_1)
    G_{q_2}(\chi_2,\psi_2;t_2).}                       \tag{1}
\]

For the standard additive characters, this is equivalently

\[
 G_q(\chi;t)=
 G_{q_1}(\chi_1;t\overline{q_2})
 G_{q_2}(\chi_2;t\overline{q_1}).                     \tag{2}
\]

Scaling by the complementary moduli, which are units in the local rings,
gives

\[
 G_q(\chi;t)=\chi_1(q_2)\chi_2(q_1)
 G_{q_1}(\chi_1;t)G_{q_2}(\chi_2;t).                 \tag{3}
\]

The local twists in (2)--(3) must not be dropped.  Applying (1) to both
shifts gives four local generalized Gauss sums.  It does not turn a
nonunit local shift into a Gauss square.

Lean theorem `unitGaussSum_crt` proves (1) for arbitrary global characters.
Theorem `gauss_product_crt` proves the corresponding four-factor identity.
Their definitions `crtAddCharLeft` and `crtAddCharRight` retain the two
complementary-modulus twists exactly.

## 2. Exact imprimitive conductor formula

Let \(\chi^*\) be a primitive character modulo \(f\), write \(q=f\ell\),
and define \(\chi\) at level \(q\) by the explicit `changeLevel`
construction.  Extend \(\chi^*\) by zero on nonunits and put

\[
 \tau(\chi^*)=G_f(\chi^*;1).
\]

For every natural representative \(t\) of a residue modulo \(q\) (and hence
for every integer shift after reduction modulo \(q\)), define

\[
 \mathcal D_{\ell,f,\chi^*}(t)=
 \sum_{\substack{s\mid(\ell,t)\\(\ell/s,f)=1}}
   \mu(\ell/s)\chi^*(\ell/s)s\,
   \overline{\chi^*(t/s)}.                            \tag{4}
\]

Then the exact formula is

\[
 \boxed{G_q(\chi;t)=
   \tau(\chi^*)\mathcal D_{\ell,f,\chi^*}(t).}        \tag{5}
\]

The condition \((\ell/s,f)=1\) is redundant if the zero-extension
convention is applied literally to \(\chi^*(\ell/s)\), but it records the
surviving divisors explicitly.  Formula (5) includes conductors sharing
primes with \(\ell\).  When \(f=1\), it reduces to

\[
 G_q(1;t)=\sum_{s\mid(q,t)}\mu(q/s)s=c_q(t),           \tag{6}
\]

the Ramanujan sum.  Thus (5) also covers the principal imprimitive stratum.

The Lean theorem
`gaussSum_changeLevel_eq_conductor_formula` first proves the exactly
equivalent divisor-\(d\) form

\[
 \tau(\chi^*)
 \sum_{d\mid\ell}
  1_{\ell/d\mid t}\,\mu(d)\chi^*(d){\ell\over d}
  \overline{\chi^*\!\left(t/(\ell/d)\right)}.        \tag{5d}
\]

Its hypotheses and construction are literal: `chi : DirichletCharacter ℂ f`,
`hchi : chi.IsPrimitive`, and
`changeLevel (f.dvd_mul_right l) chi` at level `f * l`.  The theorem permits
shared primes between \(f\) and \(\ell\), nonunit shifts, and nonreal complex
characters.  `gaussSum_changeLevel_eq_conductor_formula_conj` proves that the
inverse-character phase is complex conjugation.  The finite involution
`sum_divisors_complement` proves the reindexing \(s=\ell/d\), and
`gaussSum_changeLevel_eq_conductor_formula_s` proves (4)--(5) in the displayed
\(s\)-coordinates.  The corresponding unit-supported statement is
`unitGaussSum_changeLevel_eq_conductor_formula_s`.

### Finite derivation

Insert

\[
 1_{(z,\ell)=1}=\sum_{d\mid(z,\ell)}\mu(d)
\]

into the unit sum and write \(z=dy\).  This gives

\[
 G_q(\chi;t)=
 \sum_{d\mid\ell}\mu(d)\chi^*(d)
 \sum_{y\bmod q/d}\chi^*(y)e(ty/(q/d)).              \tag{7}
\]

Put \(s=\ell/d\), so \(q/d=fs\), and write \(y=a+fj\) with
\(a\bmod f\) and \(0\le j<s\).  The inner geometric sum is

\[
 \sum_{j=0}^{s-1}e(tj/s)=
 \begin{cases}s,&s\mid t,\\0,&s\nmid t.\end{cases} \tag{8}
\]

When \(s\mid t\), the remaining sum is

\[
 sG_f(\chi^*;t/s)
 =s\overline{\chi^*(t/s)}\tau(\chi^*),               \tag{9}
\]

where the primitive scaling formula includes value zero when \(t/s\) is a
nonunit.  Substitution of \(d=\ell/s\) proves (5), including \(t=0\),
\(f=1\), and shared-prime cases.

In addition to the complete formula, the formally proved support consequences
needed to prevent invalid simplification are:

- `unitGaussSum_eq_gaussSum`, identifying the repository's unit sum with
  Mathlib's zero-extended Gauss sum;
- `conductor_dvd_quotient_gcd_of_unitGaussSum_ne_zero`, proving
  \(G_q(\chi;t)\ne0\Rightarrow f\mid q/(q,t)\);
- `conductor_dvd_gcd_of_gauss_product_ne_zero`, proving

  \[
  G_q(\chi;k)G_q(\chi;r)\ne0
  \Longrightarrow
  f\mid\gcd\!\left({q\over(q,k)},{q\over(q,r)}\right); \tag{10}
  \]

- `primitive_nonunit_shift_vanishes`, proving that a primitive character
  kills every nonunit shift.

For an arbitrary character at a positive level, Mathlib's theorem
`changeLevel_primitiveCharacter` supplies the corresponding primitive
character at its conductor.  The formal boundary claimed here is the literal
explicit-`changeLevel` theorem above; no Python calibration or prose-only
specialization is counted as its proof.

## 3. The source modulus and shared gcds

Nonzero Möbius coefficients make \(u_1,u_2\) squarefree, but they do not
make them coprime.  Put

\[
 g=(u_1,u_2),\qquad a=u_1/g,\qquad b=u_2/g.
\]

Then \(g,a,b\) are pairwise coprime and

\[
 u_1u_2=g^2ab,qquad p=g^2abm.                        \tag{11}
\]

Theorem `squarefree_gcd_decomposition` proves these statements.  The common
Möbius sign occurs twice and cancels:

\[
 \mu(u_1)\mu(u_2)=\mu(a)\mu(b),                       \tag{12}
\]

proved by `moebius_pair_shared_gcd_cancellation`.  The common prime does
not disappear from the modulus: it contributes exponent two before the
additional valuation coming from \(m\).

The smallest surviving source stratum is \(u_1=u_2=2\).  Both Möbius
coefficients equal \(-1\), but \((u_1,u_2)=2\).  Hence a direct CRT split
into the displayed factors \(u_1,u_2,m\) is false.  Lean theorem
`zmod_four_not_crt_two_two` proves the stronger finite-ring counterexample

\[
 \mathbb Z/4\mathbb Z\not\simeq
 \mathbb Z/2\mathbb Z\times\mathbb Z/2\mathbb Z.      \tag{13}
\]

Indeed, \(2\bmod4\) is nonzero and square-zero, whereas every element of
the product ring on the right is idempotent.

The valid local decomposition is by distinct prime powers.  If a prime
\(\varpi\) has indicators
\(\epsilon_i=1_{\varpi\mid u_i}\) and
\(j=v_\varpi(m)\), its exponent in \(p\) is

\[
 e_\varpi=\epsilon_1+\epsilon_2+j.                    \tag{14}
\]

For local conductor exponent \(c_\varpi\), (10) forces

\[
 c_\varpi\le
 \min\bigl((e_\varpi-v_\varpi(k))_+,
           (e_\varpi-v_\varpi(r))_+\bigr).            \tag{15}
\]

Thus the shared outer gcd, the smooth modulus variable, the two
frequencies, and the character conductor occupy the same local stratum.

## 4. Do the four Möbius slots factor?

Only their bare arithmetic signs factor prime by prime.  Two independent
obstructions prevent a factorization of family (33):

1. The outer slots \(u_1,u_2\) can share primes.  Equation (12) cancels the
   duplicate sign but (11), (14), and (15) retain the shared prime in the
   modulus and conductor support.
2. On the source coprime stratum,
   \(\chi(v_1v_2)=\chi(v_1)\chi(v_2)\), but the literal source weight
   \(\mathcal W_{T,x}(u_1,u_2,m,v_1,v_2,r,k)\) and its cutoffs are joint.
   No separability identity for this weight is available.  Therefore the
   inner two Möbius sums do not become a product of independent character
   polynomials.

CRT enumerates the local prime-power states exactly; it does not manufacture
an Euler product for a nonseparable dyadic weight.  Any such factorization
would require an explicit pointwise factorization of the source weight and
cutoffs, which is absent from family (33).

## 5. Exact analytic moment still needed

Using (5), the product in (14) of
`docs/audit/sq4_gauss_square_transform.md` becomes

\[
 G_p(\chi;k)G_p(\chi;\sigma r)
 =\tau(\chi^*)^2
   \mathcal D_{\ell,f,\chi^*}(k)
   \mathcal D_{\ell,f,\chi^*}(\sigma r),              \tag{16}
\]

where \(f=\operatorname{cond}(\chi)\) and \(p=f\ell\).  This is the exact
conductor-stratified replacement; the two divisor sums share \(\ell\), and
the outer variables determine \(p=g^2abm\).

The unresolved estimate remains the literal signed moment

\[
 \left|\mathfrak M_4(T,x)\right|
 \ll_{\varepsilon,\mathbf W}
 T^{48/25+\varepsilon}(\log T)^0,                     \tag{17}
\]

with all four Möbius factors, the joint source weight, the sum over varying
\(p\), and the conductor/divisor coupling in (16) retained before Cauchy.
Restoring completion subtracts \(43/100\), giving the `(SQ4-HB)` exponent
\(149/100\).  The coefficient-blind pre-completion exponent remains
\(121/50\), exceeding (17) by \(1/2\).  Neither CRT nor (5) supplies the
required cancellation.

## 6. Formal and independent checks

`RH/Zeta85/Discharge/SQ4CRTConductor.lean` contains no analytic input and no
placeholder.  Its comparator is
`comparator/PrintAxioms/SQ4CRTConductor.lean`.

The independent checker is a finite calibration, not the proof of the general
complex-character phase.  It uses integer polynomial arithmetic modulo the
exact cyclotomic polynomial \(\Phi_q\) and checks (5) for primitive real
characters of conductors \(1,3,4,5,8\), twelve quotient levels, every tested
shift including zero, and shared-prime cases.  The arbitrary complex phase,
including conjugation, is covered by the general Lean theorems above.  The
checker also rechecks (11), the smallest CRT obstruction, and every exponent
in (17):

```sh
lake build RH.Zeta85.Discharge.SQ4CRTConductor
lake env lean comparator/PrintAxioms/SQ4CRTConductor.lean
python3 verify/a1_sq4_crt_conductor.py
diff -u verify/a1_sq4_crt_conductor.out \
  <(python3 verify/a1_sq4_crt_conductor.py)
```
