> **Canonical reference**: [AXIOMS.md](../../AXIOMS.md) (Axioms 2–4: trace transfer and signed pairs). See also [GUIDE.md](../../GUIDE.md) topic index.

# Simultaneous SQ4 route audit

Status: **no proof of `(SQ4-HB)` is obtained.  Six concrete method classes
are finished.  Multiplicative Fourier followed by one all-modulus character
large sieve has fixed-\(x\) exponent \(58/25\), exceeding the target by
\(33/50\).  A coefficient-uniform two-sided operator has an unavoidable
single-column exponent \(83/200\); the prescribed chain combining a
favourable upper bound at that floor with crude coefficient-energy bounds
gives \(381/200\), exceeding the target by \(49/200\).  One
additive large sieve in the numerator gives \(199/100\), exceeding the target
by \(33/100\).  Reciprocity and Poisson summation make the zero frequency
power-safe at \(149/100+\varepsilon\), but the literal classical Kuznetsov
map for the nonzero frequencies has a modulus-dependent index and is
inapplicable.  Its direct Weil-and-triangle fallback gives \(467/200\),
exceeding the target by \(27/40\).**

These are statements about the exact classes defined below.  They are not
lower bounds for the source sum and do not rule out a correlated four-slot
moment or a geometry-changing trace formula.

## 1. Granted source block and notation

This audit starts from the normalized source-shaped block `(SQ4-form)` in
`docs/audit/four_mu_kloosterman.md`.  It grants that block only for testing
the analytic transformations here.  It does not discharge the missing
smooth Heath--Brown recombination.

Put

\[
 P=Q=T^{83/100},\qquad R=T^{33/50},\qquad
 M=T^{2/5},\qquad V=T^{43/100}.                         \tag{1}
\]

Thus \(p=u_1u_2m\asymp P\), \(q=v_1v_2n\asymp Q\),
\(v=v_1v_2\asymp V\), and \(r=|\ell|h\asymp R\).  The
fixed-\(x\) and physically integrated targets are respectively

\[
 T^{83/50}(\log T)^C,\qquad
 T^{143/100}(\log T)^C,\qquad C<1.                      \tag{2}
\]

Every calculation below first uses the normalized two long logarithmic
slots, whose logarithmic exponent is exactly zero.  Every auxiliary
large-sieve, coefficient-energy, Mellin, dyadic, and complete-sum logarithmic
loss is explicitly granted exponent zero in the power-incompatibility
tests.  Restoring the two raw long slots adds exactly \((\log T)^2\).  Hence
the normalized and raw logarithmic exponents used in each failed power chain
are respectively \(0\) and \(2\).  Positive \(T^\varepsilon\) losses can
only worsen those failed powers.

For fixed \(r\), collapse notation only after displaying the retained
factors:

\[
 A(\chi)=\sum_{u_1,u_2,m}
   \mu(u_1)\mu(u_2)W_{T,x}(u_1,u_2,m)\chi(u_1u_2m),       \tag{3}
\]

and let \(B_q\) denote the corresponding signed
\((v_1,v_2,n)\)-coefficient.  A fixed Mellin inversion separates the product
cutoff in (3) into the three character polynomials.  Its absolute Mellin
integral is a fixed weight-dependent constant, so its logarithmic exponent
is \(0\).  This retains the two Möbius slots until a norm estimate is actually
applied.

## 2. Multiplicative characters and CRT

For a Dirichlet character modulo \(q\), define

\[
 \tau_q(\chi;a)=\sum_{z\bmod q}^{*}\chi(z)e(az/q).       \tag{4}
\]

Finite character orthogonality gives the exact identity

\[
 e(-\sigma r\bar p/q)
 ={1\over\varphi(q)}\sum_{\chi\bmod q}
   \tau_q(\chi;-\sigma r)\chi(p).                        \tag{5}
\]

No primitivity or coprimality between \(r\) and \(q\) is needed for (5).
Parseval on \((\mathbb Z/q\mathbb Z)^\times\) gives another exact identity:

\[
 \sum_{\chi\bmod q}|\tau_q(\chi;-\sigma r)|^2
 =\varphi(q)^2.                                          \tag{6}
\]

Consequently Cauchy over \((q,\chi)\) gives

\[
 |S_r|
 \le \|B\|_2
 \left(\sum_{q\asymp Q}\sum_{\chi\bmod q}
 |A(\chi)|^2\right)^{1/2}.                              \tag{7}
\]

This use of (6) is stronger and cleaner than inserting a pointwise Gauss-sum
bound.

Define the **single character-large-sieve class** \(\mathscr C_{\rm char}\)
to perform (5), retain the factorization (3), then use Cauchy as in (7), one
classical all-modulus multiplicative large sieve, coefficient-energy
\(L^2\) bounds, and finally triangle inequality in \(r\).  To test the most
favourable power output, grant the stronger log-free estimates

\[
 \sum_{q\asymp Q}\sum_{\chi\bmod q}|A(\chi)|^2
 \ll (Q^2+P)\|A\|_2^2,\qquad
 \|A\|_2\ll P^{1/2},\quad \|B\|_2\ll Q^{1/2}.            \tag{8}
\]

The standard induction from primitive to all characters can add divisor
factors; (8) grants all of them logarithmic exponent \(0\).  Since
\(Q^2\) dominates \(P\), (7)--(8) have per-\(r\) exponent

\[
 {83\over200}+{83\over200}+{83\over100}={83\over50}.     \tag{9}
\]

Triangle summation over \(r\) then gives

\[
 {83\over50}+{33\over50}={58\over25},\qquad
 {58\over25}-{83\over50}={33\over50}.                  \tag{10}
\]

Physical integration subtracts \(23/100\) from both the chain and its
target, so the excess remains \(33/50\).  Thus \(\mathscr C_{\rm char}\) is
power-killed even with auxiliary logarithmic exponent \(0\).

If \(q=q_1q_2\) with \((q_1,q_2)=1\), CRT factors (4) as

\[
 \tau_q(\chi_1\chi_2;a)
 =\tau_{q_1}(\chi_1;a\bar q_2)
  \tau_{q_2}(\chi_2;a\bar q_1).                          \tag{11}
\]

The literal factors \(v_1,v_2,n\) are not internally coprime, so (11) cannot
be applied to them directly.  A source-faithful use first requires a gcd and
prime-power stratification, including the strata where a prime divides two
of those variables; no such recombination is supplied here.  On a granted
coprime stratum, (11) retains the local character factors, but also displays
the cross twists by the complementary modulus.  Applying (8) after (11) still
counts the full family of conductors and has the \(Q^2\) term in (9).  The
route outside \(\mathscr C_{\rm char}\) is now precise: it would require a
correlated local moment which sums \(v_1,v_2,n\), both Möbius character
polynomials, and the cross twists in (11) before Cauchy.  No such theorem is
asserted or ruled out here.

The classical \(Q^2+P\) conductor geometry is the large-sieve geometry of
Bombieri--Davenport, *Some inequalities involving trigonometrical
polynomials*, Ann. Scuola Norm. Sup. Pisa 23 (1969), 223--241.  Equation (8)
is deliberately a more favourable all-character, no-loss grant, not a claim
that the source paper states (8) in this exact notation.

## 3. Two-sided Cauchy and large-sieve classes

For fixed \(r\), let

\[
 K_r(p,q)={\bf1}_{(p,q)=1}e(-\sigma r\bar p/q).           \tag{12}
\]

### 3.1 A coefficient-uniform operator has a diagonal barrier

Define \(\mathscr C_{2,\rm norm}\) to discard the factor support and signs,
replace the two source coefficient energies by the crude favourable bounds
\(\|A\|_2\ll P^{1/2}\) and \(\|B\|_2\ll Q^{1/2}\), each with logarithmic
exponent \(0\), use a coefficient-uniform operator norm for (12), and then
use triangle inequality in \(r\).  Let \(I_P\) be the actual ambient interval
of \(p\)-rows, of length
\(L_P\asymp P\), and select any admissible source column
\(q_0\asymp Q\).  Inclusion--exclusion constructs its exact coprime-row
count as

\[
 N(q_0;I_P)
 ={L_P\varphi(q_0)\over q_0}+O(2^{\omega(q_0)}).          \tag{13a}
\]

The elementary divisor estimates
\(\varphi(q)/q\ge q^{-\eta}\) and
\(2^{\omega(q)}\le q^\eta\), for every fixed \(\eta>0\) and all sufficiently
large \(q\), show from (13a) that
\(N(q_0;I_P)\ge P T^{-\eta}\), after relabelling \(\eta\).  Thus this actual
dyadic column has norm at least \(P^{1/2}T^{-\eta}\), and a uniform operator
bound has unavoidable power exponent at least

\[
                         {1\over2}\operatorname{exp}P
                         ={83\over200}.                   \tag{13}
\]

This is the diagonal seen after the first Cauchy step.  The lower barrier is
witnessed on the ambient full interval as follows.  Choose one admissible
column \(q_0\), put
\(B_{q_0}=Q^{1/2}\) and \(B_q=0\) otherwise, and on the reduced \(p\)-rows
put \(A_p=\overline{K_r(p,q_0)}\).  Then

\[
 \|A\|_2=N(q_0;I_P)^{1/2},\qquad \|B\|_2=Q^{1/2},
 \qquad
 \left|\sum_{p,q}A_pB_qK_r(p,q)\right|
 =N(q_0;I_P)Q^{1/2}.                                     \tag{14}
\]

Since \(\eta>0\) can be chosen arbitrarily small, a theorem uniform over all
sequences having only these two norm constraints cannot replace (13) by a
smaller power.  This saturating sequence is on the ambient interval, not the
source product support, and is not asserted to be the source Möbius
coefficient.  It proves a floor only for a coefficient-uniform operator
constant; it does not lower-bound the operator on the fixed source vector.

Now make the explicit favourable grant that the coefficient-uniform upper
bound attains the unavoidable exponent (13), grant coefficient norms
\(P^{1/2}\) and \(Q^{1/2}\), and grant every logarithmic loss exponent
\(0\).  The fixed-\(r\) exponent is

\[
 {83\over200}+{83\over200}+{83\over200}={249\over200}.   \tag{15}
\]

Triangle summation over the numerator gives

\[
 {249\over200}+{33\over50}={381\over200},\qquad
 {381\over200}-{83\over50}={49\over200}.                \tag{16}
\]

The same excess remains after physical integration.  Therefore the
prescribed upper-bound chain \(\mathscr C_{2,\rm norm}\) is finished and
power-killed.  The column witness says that a coefficient-uniform matrix
estimate alone cannot supply operator exponent zero.  It does not rule out a
\(49/200\) saving in the literal source coefficient energies or an estimate
which uses the four Möbius factors before this norm-only reduction.

### 3.2 Putting the numerator into one additive large sieve is worse

The reduced fractions \(\bar p/q\), after consolidating the bounded
multiplicity coming from \(p\asymp P\asymp Q\), have spacing
\(Q^{-2}\).  Define \(\mathscr C_{r,\rm add}\) to apply one additive large
sieve in \(r\), using only the three \(L^2\) norms.  Granting all coefficient
logarithms exponent \(0\), its output is

\[
 (R+Q^2)^{1/2}\|\Gamma\|_2\|A\|_2\|B\|_2.              \tag{17}
\]

Here \(Q^2\) dominates \(R\).  Therefore the exact fixed-\(x\) exponent is

\[
 {83\over100}+{33\over100}
 +{83\over200}+{83\over200}={199\over100},              \tag{18}
\]

and

\[
 {199\over100}-{83\over50}={33\over100}.                \tag{19}
\]

After physical integration the output is \(44/25\), still exceeding
\(143/100\) by \(33/100\).  Thus \(\mathscr C_{r,\rm add}\) is also
power-killed.  A higher correlation which uses the Möbius factors inside the
large-sieve diagonal is outside this class.

## 4. Reciprocity and Poisson before absolute values

This route does change the geometry and gives one useful result: the zero
dual frequency is not the power obstruction.

Write \(q=vn\), where \(v=v_1v_2\asymp V\) and \(n\asymp M\).  The source
condition \((p,q)=1\) implies \((p,v)=1\) and leaves the condition
\((n,p)=1\) in the completed sum, so every inverse below is pointwise
defined.  Additive reciprocity gives the exact identity

\[
 e(-\sigma r\bar p/q)
 =e(\sigma r\bar q/p)e(-\sigma r/(pq)).                  \tag{20}
\]

Write the entire scaled \(n\)-profile explicitly as

\[
 G_{p,v,r,x,T}(t)
 =W_3(t)\widetilde W_{2,T}
   \!\left({vMtx\over T^{3/5}}\right)
   e\!\left(-{\sigma r\over pvMt}\right),\qquad t\asymp1.\tag{20a}
\]

The other source weights are independent of \(n\).  The two varying
parameters in (20a) have exponents

\[
 \operatorname{exp}{vMx\over T^{3/5}}=0,
 \qquad
 \operatorname{exp}{r\over pvM}=-1.                     \tag{20b}
\]

The normalized logarithm in \(\widetilde W_{2,T}\) and each of its scaled
derivatives are \(O_j(1)\); differentiating the reciprocity factor costs only
the parameter \(T^{-1}\).  Hence, uniformly in every source variable,

\[
             \|G_{p,v,r,x,T}^{(j)}\|_\infty\ll_j1.       \tag{20c}
\]

With \(\widehat G(y)=\int_{\mathbb R}G(t)e(-yt)\,dt\), Poisson summation in
the smooth \(n\)-slot gives the exact profile-scaled identity

\[
 \sum_{\substack{n\in\mathbb Z\\(n,p)=1}}
 G_{p,v,r,x,T}(n/M)e(\sigma r\bar v\bar n/p)
 ={M\over p}\sum_{k\in\mathbb Z}
 \widehat G_{p,v,r,x,T}(kM/p)
 S(k,\sigma r\bar v;p).                                  \tag{21}
\]

Here and below the complete sum convention is

\[
 S(a,b;c)=\sum_{z\bmod c}^{*}e\!\left({az+b\bar z\over c}\right).
                                                               \tag{21a}
\]

Changing the complete-sum variable by \(z=\bar v y\) gives

\[
 S(k,\sigma r\bar v;p)=S(k\bar v,\sigma r;p).            \tag{22}
\]

The completion prefactor and dual length have exact exponents

\[
 \operatorname{exp}(M/p)=-{43\over100},\qquad
 \operatorname{exp}K={43\over100}.                       \tag{23}
\]

Equation (20c), integrated by parts \(A\) times, gives
\(|\widehat G(y)|\ll_A(1+|y|)^{-A}\).  Fix
\(0<\eta<2/5\).  The nonzero sum may therefore be truncated at
\(|k|\le KT^\eta\), with an \(O_B(T^{-B})\) tail after all outer sums by
choosing \(A\) in terms of \(B\).  Since

\[
 {KT^\eta\over p}=T^{-2/5+\eta}<1,                       \tag{23a}
\]

every retained \(k\) satisfies \(|k|<p\).  The truncation contributes the
displayed power \(T^\eta\), logarithmic exponent \(0\), and validates the
dual exponent \(43/100\) in (23) without an unrecorded scale count.

The symmetric operation, completing \(m\) before reciprocity, gives the same
inventory with \(u_1u_2\) and \(v_1v_2\) interchanged.

### 4.1 The zero frequency is power-safe

At \(k=0\), (21) is the Ramanujan sum

\[
 S(0,\sigma r\bar v;p)=c_p(r).                            \tag{24}
\]

The elementary identities

\[
 |c_p(r)|\le(p,r),\qquad
 \sum_{r\le R}(p,r)
 =\sum_{d\mid p}\varphi(d)\left\lfloor{R\over d}\right\rfloor
 \le R\tau(p)                                           \tag{25}
\]

together with \(|\Gamma(r)|\ll\tau(r)\) give, for every fixed
\(\varepsilon>0\),

\[
 \sum_r|\Gamma(r)c_p(r)|\ll_\varepsilon R T^\varepsilon.\tag{26}
\]

The logarithmic exponent in (26) is recorded as \(0\); its loss is the
displayed power \(T^\varepsilon\).  The fixed-\(x\) zero-mode power is

\[
 -{43\over100}+{83\over100}+{43\over100}+{33\over50}
 ={149\over100}.                                         \tag{27}
\]

It has margin \(17/100\) below the target.  Restoring the raw slots adds
exactly \((\log T)^2\).  For example, allocating \(17/400\) to the divisor
power in (26) and \(17/400\) to the explicit square of the logarithm still
leaves power margin \(17/200\).  Thus the zero mode is not a power blocker.
Physical integration gives exponent \(63/50\), below \(143/100\) by the
same \(17/100\) before those allocations.

### 4.2 Literal classical Kuznetsov has a moving index

The geometric side of the classical Deshouillers--Iwaniec/Kuznetsov formula
has fixed integer indices while the modulus varies, schematically

\[
 \sum_c {S(a,b;c)\over c}
 \Phi\!\left({4\pi\sqrt{|ab|}\over c}\right).            \tag{28}
\]

The primary source is Deshouillers--Iwaniec, *Kloosterman sums and Fourier
coefficients of cusp forms*, Invent. Math. 70 (1982), 219--288
([published article](https://doi.org/10.1007/BF01390728)).

In (22), however, the first index is the residue \(k\bar v\pmod p\).  It
changes with the varying modulus \(p=u_1u_2m\).  Rewriting (22) as
\(S(k,\sigma r\bar v;p)\) merely moves the same inverse to the second index.
The factorized modulus weight is an additional issue, but the moving index
already blocks a literal substitution into (28).

Define the **literal reciprocal-completed Kuznetsov class**
\(\mathscr C_{\rm Kuz}^{\rm lit}\) to perform (20)--(22) and then apply the
classical fixed-index trace formula while treating \(k\bar v\) as if it were
independent of \(p\).  This class is structurally inapplicable.

Split the nonzero dual frequencies into \(k>0\) and \(k<0\); the two signs
are symmetric after changing the signs of the complete-sum indices.  For
\(k>0\), the obstruction can be written as an exact divisor switch.  Let
\(a_p\in[0,p)\) represent \(k\bar v\pmod p\).  Since \(k<p\), there is a
unique integer \(j\) with

\[
                  va_p-k=jp,\qquad 0\le j<v.              \tag{29}
\]

The zero winding \(j=0\) occurs exactly when \(v\mid k\), and then
\(a_p=k/v\) is a fixed index.  Since \(K\asymp V\), this is only the
distinguished divisibility subfamily, not the generic nonzero dual family.
For \(j\ne0\), (29) gives

\[
                         p={va_p-k\over j}.                \tag{30}
\]

Here \(a_p\) still ranges up to \(P\), while \(j\) has length at most \(V\).
Equation (30) exchanges the old modulus variable for a long complementary
variable; it does not turn \(S(a_p,r;p)\) into a Kloosterman sum of modulus
\(j\).  Define the **direct moving-index divisor-switch class** to use only
(29)--(30), select \(j\) as a proposed new conductor, and invoke the
classical trace formula without a further transform.  It is structurally
inapplicable because no such modulus-\(j\) complete sum is produced.

This conclusion agrees with the completed-index mismatch already audited
for the published theorems of Drappeau and Pascadi in
`premajorant_di_one_shot.md`.  It is not a claim about a new trace formula
whose indices and moduli vary together.

### 4.3 Direct nonzero Weil fallback is power-killed

The ordinary composite-modulus Weil bound is

\[
 |S(k,r;p)|\le \tau(p)(k,r,p)^{1/2}p^{1/2}.              \tag{30a}
\]

Its gcd factor can be averaged without a new power.  Put
\(K'=KT^\eta\) as in the proved truncation above.  Since
\(|\Gamma(r)|\ll\tau(r)\) and
\((k,r,p)^{1/2}\le\sum_{d\mid(k,r,p)}\sqrt d\), the constructed divisor
sum is

\[
\begin{aligned}
 &\sum_{0<|k|\le K'}\sum_{r\asymp R}
   |\Gamma(r)|(k,r,p)^{1/2}\\
 &\quad\ll_\varepsilon
 \sum_{d\mid p}\sqrt d\,{K'\over d}{R\over d}T^\varepsilon
 \ll_\varepsilon K'R T^\varepsilon,
\end{aligned}                                             \tag{30b}
\]

Only divisors \(d\le K'\) and \(d\le2R\) have a nonzero count, so the two
counting factors in (30b) introduce no hidden additive \(1\).  Since
\(\sum_{d\ge1}d^{-3/2}\) converges, (30b) follows.  The factor \(\tau(p)\) in
(30a) is absorbed into the displayed \(T^\varepsilon\), with logarithmic
exponent \(0\).  Apply (30a)--(30b) and triangle inequality only in the
remaining variables.  Apart from the explicit arbitrarily small
\(T^{\eta+\varepsilon}\), its power is

\[
 -{43\over100}+{83\over100}+{43\over100}+{33\over50}
 +{43\over100}+{83\over200}={467\over200}.               \tag{31}
\]

Thus

\[
 {467\over200}-{83\over50}={27\over40}.                 \tag{32}
\]

Physical integration gives \(421/200\), still exceeding \(143/100\) by
\(27/40\).

The **reciprocal-Poisson/Weil/triangle class** is therefore power-killed.
The normalized auxiliary logarithmic exponent is \(0\); the two raw slots
add exactly exponent \(2\).  The displayed positive
\(T^{\eta+\varepsilon}\) only increases the output.

## 5. Exact survivor

The first unresolved object after a valid geometry change is the nonzero
part of

\[
 {M\over p}
 \sum_{u_1,u_2,m}\sum_{v_1,v_2}\sum_r\sum_{k\ne0}
 \mu(u_1)\mu(u_2)\mu(v_1)\mu(v_2)
 \Gamma_{\sigma,x}(r)\,\mathcal W_{T,x}(\cdots)
 S(k\overline{v_1v_2},\sigma r;u_1u_2m).                 \tag{33}
\]

A successful continuation must do at least one of the following before an
absolute-value norm discards the four signed factors:

1. prove a correlated character/CRT moment which removes the \(Q^2\)
   conductor factor in (9);
2. prove a coefficient-sensitive bilinear operator estimate that is not
   uniform for arbitrary coefficient sequences and therefore evades the
   single-column class in Section 3.1;
3. transform the generic \(j\ne0\) family in (29) into a genuine fixed-index
   trace-formula geometry, with the zero and nonzero spectra both stated;
4. obtain signed cancellation across the two reciprocal completions before
   applying Cauchy.

No one of these statements is proved here.  The audit only finishes the six
literal classes above and isolates (33) as the source-shaped nonzero family.

## 6. Formal and independent checks

`RH/Zeta85/Discharge/SQ4SimultaneousRoutes.lean` proves only exact rational
power arithmetic.  It declares no analytic premise or placeholder.
In particular, it does not assert the character large sieve, the divisor
estimate, a complete-sum estimate, or a Kuznetsov application.

The exact checker uses only `fractions.Fraction`:

```sh
lake build RH.Zeta85.Discharge.SQ4SimultaneousRoutes
lake env lean comparator/PrintAxioms/SQ4SimultaneousRoutes.lean
python3 verify/a1_sq4_simultaneous_routes.py
diff -u verify/a1_sq4_simultaneous_routes.out \
  <(python3 verify/a1_sq4_simultaneous_routes.py)
```

It verifies every exponent in (9)--(10), (13)--(19), (23), (27), and
(31)--(32), together with the fixed and integrated excesses and the explicit
normalized/raw logarithmic exponents \(0\) and \(2\).
