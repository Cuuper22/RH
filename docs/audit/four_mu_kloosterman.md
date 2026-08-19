> This file is the **canonical reference** for the Kloosterman / four-mu topic. See [GUIDE.md](../../GUIDE.md) topic index.

# Four-Möbius-slot Kloosterman route

Status: **among the audited published theorem families, no directly
applicable estimate was found which retains all four Möbius slots.  The
precisely defined one-sided
fixed-modulus/square-root/triangle class is finished and power-incompatible:
even after granting an ideal square-root-size bound with no theorem or
logarithmic loss, it gives fixed-\(x\) exponent \(381/200\), missing the
required \(83/50\) by \(49/200\).  A genuinely simultaneous two-sided
estimate with exponent \(149/100+\varepsilon\) is stated explicitly below as
the surviving candidate; it is not proved.**

This audit is for the exact route left open by
`docs/audit/premajorant_di_one_shot.md`.  Its finish/kill conclusion concerns
the prescribed architecture in Section 4.  It is not a lower bound for the
signed source sum, and it is not a claim that every possible analytic method
has exponent at least \(381/200\).

## 1. Granted source-shaped block and the seven scales

The primary source is Bettin--Bui--Li--Radziwiłł, *A quadratic divisor
problem and moments of the Riemann zeta-function*, JEMS 22 (2020),
3953--3980, Proposition 3.1 and equation (14)
([published article](https://doi.org/10.4171/JEMS/999),
[author PDF](https://www.math.mcgill.ca/radziwill/twisted.pdf)).  At \(d=1\),
the already-audited nonzero-frequency phase is

\[
 e\!\left(\mp {\ell h\,\overline{am}\over bn}\right)e(\ell x),
 \qquad (am,bn)=1.                                      \tag{1}
\]

The zero-based \(j=1\) summand of the proved sharp depth-four Heath--Brown
identity is

\[
             -6\,\mu_Z*\mu_Z*\zeta*\log .               \tag{2}
\]

Apply (2) on both sides and retain the two Möbius factors separately.  For
one fixed dyadic rectangle put

\[
 U=T^{43/200},\qquad M=T^{2/5},\qquad
 L=T^{23/100},\qquad H=T^{43/100},\qquad R=LH=T^{33/50}.
                                                               \tag{3}
\]

Fix the BBLR \(S_+\) branch, corresponding to the upper inverse-phase sign
in (1), and let \(\sigma\in\{-1,1\}\) be the sign of \(\ell\).  Define the
exact collapsed numerator coefficient

\[
 \Gamma_{\sigma,x}(r)
 :=\sum_{\substack{\ell h=r\\ \ell,h>0}}
 W_L(\ell/L)W_0(h/H)e(\sigma\ell x).                     \tag{4}
\]

All base cutoff functions in this section are fixed, smooth, and supported
in \([1,2]\).  Let \(V_1,\ldots,V_4\) be the four Möbius-slot cutoffs.  The
two long logarithmic slots have length \(T^{3/5}\).  The normalized families
below depend on \(T\); for \(T\ge2\) they retain the same support and have
uniformly bounded derivatives of every fixed order.  Normalize them exactly
by

\[
 \widetilde W_{2,T}(t)
 =W_2(t){\log(T^{3/5}t)\over\log T},\qquad
 \widetilde W_{4,T}(t)
 =W_4(t){\log(T^{3/5}t)\over\log T}.                     \tag{5}
\]

Write

\[
 p=u_1u_2m,\qquad q=v_1v_2n,                             \tag{6}
\]

and

\[
\begin{aligned}
 \Omega_{T,x}(\mathbf u,m,\mathbf v,n)
 :={}&\prod_{i=1}^{2}V_i(u_i/U)
       \prod_{i=1}^{2}V_{i+2}(v_i/U)\\
 &\times W_1(m/M)W_3(n/M)
 \widetilde W_{2,T}(qx/T^{3/5})
 \widetilde W_{4,T}(px/T^{3/5}).                         \tag{7}
\end{aligned}
\]

The normalized, source-shaped candidate block is

\[
\boxed{
\begin{aligned}
 \mathcal Z^{(0)}_{4,\sigma}(x)
 :=36\!\sum_{u_1,u_2,v_1,v_2,m,n,r}
 &\mu(u_1)\mu(u_2)\mu(v_1)\mu(v_2)\,\Gamma_{\sigma,x}(r)\\
 &\times\Omega_{T,x}(\mathbf u,m,\mathbf v,n)
 \mathbf 1_{(p,q)=1}
 e\!\left(-\sigma {r\bar p\over q}\right).
                                                               \tag{SQ4-form}
\end{aligned}}
\]

The scalar \(36=(-6)^2\) is displayed; it changes neither a power nor a
logarithmic exponent.  The inverse \(\bar p\) is taken modulo the literal
source modulus \(q\), and the coprimality in (SQ4-form) is exactly what makes
it defined.  Thus (SQ4-form) is exactly the \(S_+\) branch after splitting
signed frequencies.  The \(S_-\) branch replaces \(-\sigma\) by
\(+\sigma\), without changing any estimate below.
Formula (4) includes the source factor \(e(\ell x)\); it is not replaced by
an arbitrary numerator sequence.

The unnormalized two-log-slot block is exactly

\[
 \mathcal Z^{\rm raw}_{4,\sigma}(x)
   =(\log T)^2\mathcal Z^{(0)}_{4,\sigma}(x).             \tag{8}
\]

Thus the normalized long-log exponent is \(0\), and the raw long-log
exponent is exactly \(2\).  On one dyadic rectangle, (4) has the elementary
bound

\[
 \sum_r|\Gamma_{\sigma,x}(r)|
 \le \|W_L\|_\infty\|W_0\|_\infty\,\#\{\ell\}\,\#\{h\}
 \ll T^{33/50};                                          \tag{9}
\]

there is no logarithmic scale-count loss in (9).

There is an important provenance boundary.  `HBDepthFour.lean` proves (2),
and `BBLRGCDAllocation.lean` proves the canonical BBLR allocation for
*supplied* outer and smooth sequences.  The repository still has no smooth
partition and recombination identity identifying every actual Heath--Brown
block with (SQ4-form).  Accordingly this audit grants (SQ4-form) for the
purpose of testing the analytic route.  It does not mark the actual cycle
coefficient identification as proved.

The seven retained variable exponents are

| variable | exponent |
|---|---:|
| \(u_1,u_2,v_1,v_2\) | \(43/200\) each |
| \(m,n\) | \(2/5\) each |
| \(r=\ell h\) | \(33/50\) |

Consequently

\[
 \operatorname{exp}p=\operatorname{exp}q
 =2{43\over200}+{2\over5}={83\over100},                 \tag{10}
\]

and the raw tuple volume is

\[
 4{43\over200}+2{2\over5}+{33\over50}={58\over25}.
                                                               \tag{11}
\]

The physical \(x\)-interval has exponent \(-23/100\).  Therefore the exact
requirements are

\[
 |\mathcal Z^{(0)}_{4,\sigma}(x)|
 \ll T^{83/50}(\log T)^C,\qquad C<1,                    \tag{12}
\]

at fixed \(x\), and \(143/100\) after physical integration.

## 2. Primary-source theorem audit

The search below was restricted to published theorem families whose left
sides can plausibly interact with (1): incomplete multilinear inverses,
multiplicatively weighted incomplete Kloosterman sums, trilinear Kloosterman
fractions, and horizontal Kuznetsov/dispersion estimates.  It is an audited
applicability result for these stated theorems, not a proof that no theorem
anywhere could address (SQ4-form).

### 2.1 Bourgain--Garaev: the right inner shape, the wrong modulus

Bourgain--Garaev, *Sumsets of reciprocals in prime fields and multilinear
Kloosterman sums*, Izv. Math. 78 (2014), 656--707, Theorems 7--13
([primary PDF](https://arxiv.org/pdf/1211.4184),
[published record](https://doi.org/10.1070/IM2014v078n04ABEH002703)) treat
separated interval coefficients in sums of the form

\[
 \sum_{x_1\in I_1}\cdots\sum_{x_k\in I_k}
 \alpha_1(x_1)\cdots\alpha_k(x_k)
 e_p(a x_1^{-1}\cdots x_k^{-1}),                         \tag{13}
\]

where the modulus \(p\) is prime.  In particular, their Theorem 13 assumes
\(\prod_i|I_i|>p^{1/2+\varepsilon}\) and then gives a fixed power saving.

For a *hypothetical prime* \(q\), the inverse-side variables
\((u_1,u_2,m)\) in (SQ4-form) have product length

\[
 q\asymp U^2M=T^{83/100},                                \tag{14}
\]

so this is the closest published multilinear inverse shape found.  But the
literal source modulus is

\[
                         q=v_1v_2n.                       \tag{15}
\]

For all sufficiently large \(T\), the displayed dyadic variables are at
least \(2\), so \(v_1\) is a proper nonunit divisor of (15).  Hence (15) is
not prime.  `source_modulus_not_prime` formalizes this elementary obstruction.
Chinese-remainder stratification by prime factors would be a new
construction: (13) supplies no theorem that recombines a variable composite
modulus while retaining the two Möbius factors \(v_1,v_2\).  Moreover, a
fixed-modulus use of (13) acts only on \(u_1,u_2,m\), leaving the entire
modulus side and numerator to be estimated separately.

### 2.2 Gong--Jia and Korolev: arbitrary modulus, but one long variable

Gong--Jia, *Kloosterman sums with multiplicative coefficients*, Sci. China
Math. 59 (2016), 653--660, prove for a multiplicative \(|f(n)|\le1\),
\((a,q)=1\), and \(q\le N^2\) the explicit estimate

\[
 \sum_{\substack{n\le N\\(n,q)=1}}f(n)e(a\bar n/q)
 \ll \sqrt{\tau(q)/q}\,N\log\log(6N)
 +q^{1/4+\varepsilon/2}N^{1/2}(\log(6N))^{1/2}
 +{N\over\sqrt{\log\log(6N)}}                            \tag{16}
\]

([published article](https://doi.org/10.1007/s11425-015-5108-z),
[primary prepublication text](https://arxiv.org/abs/1401.4556)).
Korolev, *Kloosterman sums with multiplicative coefficients*, Izv. Math. 82
(2018), 647--661, Theorems 1--3, likewise treats one multiplicatively
weighted variable for arbitrary modulus, always under \((a,q)=1\).
Theorem 1 applies for \(q^{1/2+\varepsilon}\le N\le q\).  Theorems 2 and 3 reach
\(\sqrt q\) times explicit subpower factors only with, respectively,
\[
 \tau(q)\le \exp\!\left({1\over4}(\log\log q)^{1+\gamma}\right)
 \quad\text{and}\quad
 \tau(q)\le(\log q)^{\gamma/4},
\]
and their length hypotheses are
\(\sqrt q\exp((\log\log q)^{1+\gamma})\le N\le q\) and
\(\sqrt q(\log q)^{1+2\gamma}\le N\le q\), respectively
([published PDF](https://www.mathnet.ru/eng/im8633),
[DOI](https://doi.org/10.1070/IM8633)).

One retained Möbius slot has relative length

\[
 {43/200\over83/100}={43\over166}<{1\over2},\qquad
 {1\over2}-{43\over166}={20\over83}.                     \tag{17}
\]

Equivalently, Gong--Jia's condition fails by

\[
 \operatorname{exp}q-\operatorname{exp}U^2
 ={83\over100}-{43\over100}={2\over5}.                  \tag{18}
\]

Grouping \(u_1u_2\) produces a dyadically truncated convolution, not the
single 1-bounded multiplicative function in (16), and it is exactly the
pair-collapse forbidden in this route.  Grouping all of \(u_1u_2m\) also
destroys the four-slot structure and leaves the other product side
untouched.  Thus neither published arbitrary-modulus theorem applies to an
individual retained slot in the required range.

There is a second unmapped hypothesis shared by Gong--Jia and Korolev: their
phase assumes \((a,q)=1\), whereas the source numerator \(a=\sigma r\) is not
constrained to be coprime to the composite modulus \(q=v_1v_2n\).  The range
failure above already excludes the application, so no coprimality
decomposition is silently supplied here.

### 2.3 Trilinear fractions: a direct map forces both collapses

Bettin--Chandee, *Trilinear forms with Kloosterman fractions*, Adv. Math.
328 (2018), 1234--1262, Theorem 1
([published DOI](https://doi.org/10.1016/j.aim.2018.01.026),
[primary text](https://arxiv.org/abs/1502.00769)) bounds

\[
 \sum_{a,m,n}\nu_a\alpha_m\beta_n
 e(a\bar m/n)                                             \tag{19}
\]

for three independent coefficient sequences.  The source-faithful direct
substitution into (19) is

\[
 a=r,\qquad m=u_1u_2m_0,\qquad n=v_1v_2n_0,              \tag{20}
\]

which collapses each Möbius pair and each adjacent smooth variable.  If one
instead sets the theorem variable \(m=u_1\), then the required numerator is
\(r\overline{u_2m_0}\pmod n\); it depends on the variable modulus \(n\) and
is not the independent interval variable \(a\) in (19).  Consequently (19)
has no direct seven-variable substitution preserving (SQ4-form).

### 2.4 Horizontal DI/Kuznetsov estimates still take collapsed sequences

The directly applicable incomplete-sum theorem after collapse is Drappeau,
*Sums of Kloosterman sums in arithmetic progressions, and the error term in
the dispersion method*, Proc. LMS 114 (2017), 684--732, Theorem 2.1
([published DOI](https://doi.org/10.1112/plms.12022),
[primary text](https://arxiv.org/pdf/1504.05549)).  The exact map and output
are already audited in `premajorant_di_one_shot.md`: its coefficient
\(b_{n,r,s}\) contains the collapsed products, and the resulting integrated
exponent is \(179/100\).

Pascadi, *Smooth numbers in arithmetic progressions to large moduli*,
Compos. Math. 161 (2025), 1923--1974, Theorem 10.3
([published DOI](https://doi.org/10.1112/S0010437X2500747X),
[published PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D8E4EE07BDAA6D41CCD8C5455D81CD7A/S0010437X2500747Xa.pdf/smooth-numbers-in-arithmetic-progressions-to-large-moduli.pdf))
also takes one collapsed coefficient \(b_{n,r,s}\).  Literal completion of
the source gives

\[
                  S(k\bar a,\sigma r;q),                  \tag{21}
\]

whereas the proposed substitution requires \(S(ka,\sigma r;q)\).  The exact
finite regression and the untreated zero frequency are recorded in
`PreMajorantDI.lean`; no support-preserving reindex is available.

Finally, Pascadi, *Large sieve inequalities for exceptional Maass forms and
the greatest prime factor of \(n^2+1\)*, Forum Math. Pi 14 (2026), e8, has
three relevant variants, Corollaries 5.9, 5.11, and 5.14
([published article](https://doi.org/10.1017/fmp.2026.10025),
[published PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/DC9B30CB4824955671C7B018C473863A/S2050508626100250a.pdf/large_sieve_inequalities_for_exceptional_maass_forms_and_the_greatest_prime_factor_of_n21.pdf)).
Corollaries 5.9 and 5.11 bound smooth horizontal averages of complete
Kloosterman sums.  Corollary 5.9 takes two one-dimensional sequences, each
satisfying Assumption 5.4; Corollary 5.11 takes one such sequence together
with the pure phase
\(e(m\omega)\).  Corollary 5.14 is already an incomplete Kloosterman bound
averaged over \(r,s,n,c,d\), but its arithmetic is packaged into the single
sequence \((a_{n,r,s})_{n\asymp N}\), whose tuple must satisfy Assumption
5.4.  Thus none of these corollaries exposes four Möbius variables in a
variable denominator.  Applying Corollary 5.9 or 5.11 through the source's
literal completion still encounters (21); applying Corollary 5.14 instead
would require matching its phase \(e(\pm n\overline{rd}/sc)\), thereby
packaging retained products and Möbius pairs among its theorem variables
\(r,s,c,d\) or its coefficient data.  In particular, its structured
coefficient \((a_{n,r,s})_{n\asymp N}\) must satisfy Assumption 5.4.  The
paper supplies no direct seven-variable specialization that retains the
four slots as separate exposed variables.

The conclusion of this primary-source audit is therefore narrow and exact:
none of the displayed published theorems is directly applicable to
(SQ4-form) while retaining \(u_1,u_2,v_1,v_2\) as four separate variables.

## 3. Exact exponent of one-sided square-root cancellation

Before defining the method class, grant more than the cited fixed-modulus
results uniformly supply: after freezing \(q=v_1v_2n\) and \(r\), suppose the
whole \((u_1,u_2,m)\) sum of volume \(T^{83/100}\) is bounded at exact
square-root size

\[
                         T^{83/200},                       \tag{22}
\]

with no \(T^\varepsilon\), logarithmic, support, derivative, coprimality, or
composite-modulus loss.  Summing the frozen modulus side and numerator by
triangle inequality gives

\[
 {83\over200}+{83\over100}+{33\over50}
 ={381\over200}.                                         \tag{23}
\]

The fixed-\(x\) target is \(83/50\), and

\[
 {381\over200}-{83\over50}={49\over200}.                 \tag{24}
\]

Physical integration subtracts \(23/100\) from both the chain and its
comparison target:

\[
 {381\over200}-{23\over100}={67\over40},\qquad
 {67\over40}-{143\over100}={49\over200}.                 \tag{25}
\]

Thus the power miss survives unchanged before logarithms matter.

## 4. Finished method class

Define the **one-sided fixed-modulus square-root/triangle class**
\(\mathscr F_1\) to consist of the following prescribed operations:

1. grant the candidate block (SQ4-form) and its source coprimality;
2. fix \(v_1,v_2,n,r\), hence fix the literal modulus \(q=v_1v_2n\);
3. apply one fixed-modulus inverse/Kloosterman estimate to the three exposed
   variables \(u_1,u_2,m\), and grant that its output is the ideal
   square-root size (22) with every loss set to zero;
4. sum \(v_1,v_2,n,r\) by triangle inequality, using (9), with no
   cancellation across moduli, numerator values, signs, Heath--Brown
   components, or dyadic scales;
5. integrate the resulting pointwise absolute bound over the physical
   \(x\)-interval.

The class is symmetric under exchanging the two product sides.  Equations
(23)--(25) finish and kill exactly this class: its prescribed exponent
output exceeds the target by \(49/200\), and adding any nonnegative theorem
or logarithmic loss cannot repair that output.

This statement does **not** say that the source sum is at least
\(T^{381/200}\).  It does **not** prohibit a special-coefficient estimate
better than square-root size on one side.  Most importantly, it does not
cover an estimate that couples the two product sides, retains \(r\), or
cancels before freezing the modulus.  Those are precisely the operations
excluded in item 4.

## 5. Exact surviving simultaneous estimate

The clean coefficient-sensitive target left by the calculation is the
following statement for the explicit normalized block (SQ4-form): for every
fixed \(\varepsilon>0\), uniformly for
\(x\asymp T^{-23/100}\),

\[
\boxed{
 |\mathcal Z^{(0)}_{4,\sigma}(x)|
 \ll_{\varepsilon,\mathbf W}
 (U^2M)^{1/2}(U^2M)^{1/2}(LH)T^\varepsilon
 =T^{149/100+\varepsilon}.}
                                                               \tag{SQ4-HB}
\]

`(SQ4-HB)` is a candidate estimate, not a theorem or an input silently used
elsewhere.  Its exponent is

\[
 {83\over200}+{83\over200}+{33\over50}={149\over100}.     \tag{26}
\]

It improves the one-sided output by

\[
 {381\over200}-{149\over100}={83\over200}.                \tag{27}
\]

Only \(49/200\) is needed, so its exact fixed-\(x\) margin is

\[
 {83\over50}-{149\over100}={17\over100},
 \qquad {83\over200}={49\over200}+{17\over100}.           \tag{28}
\]

Restoring both unnormalized long log slots gives the fully explicit bound

\[
 |\mathcal Z^{\rm raw}_{4,\sigma}(x)|
 \ll T^{149/100+\varepsilon}(\log T)^2.                   \tag{29}
\]

For example, allocate \(\varepsilon=17/400\) to `(SQ4-HB)`.  Since
\((\log T)^2\ll T^{17/400}\) for sufficiently large \(T\), (29) would give

\[
 |\mathcal Z^{\rm raw}_{4,\sigma}(x)|
 \ll T^{149/100+17/400+17/400}=T^{63/40}
 <T^{83/50}.                                               \tag{30}
\]

Thus `(SQ4-HB)` would meet the literal fixed-\(x\) budget with logarithmic
exponent \(C=0<1\), and after physical integration it would have exponent
\(269/200\).  Both the allocated fixed-\(x\) exponent and the allocated
integrated exponent lie below their respective targets by exactly
\(17/200\).  Before allocating either power loss, the candidate exponents
are \(149/100\) at fixed \(x\) and \(63/50\) after integration, with the
intrinsic \(17/100\) margin recorded in (28).  This is why a genuine
two-sided coefficient-sensitive estimate is sufficient without a separate
cross-\(Y\) input.

What remains open is analytic and source-identification work, not exponent
bookkeeping:

- prove `(SQ4-HB)` or another estimate reaching (12), while retaining both
  Möbius pairs before any absolute-value theorem;
- or construct a source-faithful completion/CRT/divisor-switch that maps all
  four slots into a published theorem without variable-dependent
  coefficients;
- construct the missing smooth Heath--Brown partition and recombination
  identity connecting the granted (SQ4-form) to every required source block;
- record every additional dyadic/recombination logarithm explicitly.  The
  present exponent margin can absorb any fixed explicit power, but no
  unspecified `polylog` is being claimed here.

## 6. Formal and independent checks

`RH/Zeta85/Discharge/FourMuKloosterman.lean` proves only exact arithmetic and
the elementary non-primality of a displayed product modulus.  It proves:

- all seven literal exponents, both product-side exponents, and total volume;
- the relative one-slot length \(43/166<1/2\);
- the prescribed one-sided output \(381/200\), its integrated output
  \(67/40\), and both exact \(49/200\) misses;
- the simultaneous candidate exponents \(149/100\) before and \(63/50\)
  after integration, their \(17/100\) margins, and the gain decomposition
  (28);
- `simultaneous_concrete_loss_allocation_exact`, the strict allocation in
  (30), including the \(63/40\) and \(269/200\) outputs and their
  \(17/200\) margins;
- the normalized/raw long-log exponents \(0\) and \(2\).

It declares no analytic theorem, no premise, and no proof placeholder.  In
particular, it does not assert `(SQ4-HB)`.

```sh
lake build RH.Zeta85.Discharge.FourMuKloosterman
lake env lean comparator/PrintAxioms/FourMuKloosterman.lean
python3 verify/a1_four_mu_kloosterman.py
diff -u verify/a1_four_mu_kloosterman.out \
  <(python3 verify/a1_four_mu_kloosterman.py)
```

The independent verifier uses only exact `fractions.Fraction` arithmetic and
commits its complete output.
