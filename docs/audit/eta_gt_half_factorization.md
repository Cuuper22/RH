# Audit of the claimed `eta > 1/2` terminal factorization

## Verdict

The exponent calculation in
`docs/run/18_arithmetic95_cycle1_support_2_93p2283.md` section 2 is correct
**for a block already presented with the asserted asymmetric variables**.
It is not an all-block factorization theorem.  The literal construction in
that section only relabels factors, and a legal balanced `K=3`, `j=2`
Heath--Brown block has no whole-factor subproduct of the requested length.
Thus the relabel-only method is finished with a precise counterexample.  This
does not rule out a new coefficient identity which genuinely refactors the
balanced block.  The finite support-model audit now rules out the narrower
class in which every first factor of such a signed superposition remains in
one divisor-free asymmetric short box, but it does not identify the model
with an actual terminal Heath--Brown coefficient.  The actual coefficient
identity therefore remains open and is stated exactly below.  Independently,
even a repaired factorization would still have to meet the literal
logarithmic threshold `C < 1`.

Throughout this note, `eta` is fixed with

\[
             \frac12<\eta<1,\qquad
 X=T^{1+\eta},\qquad H=A=B=T^\eta,\qquad M=N=T.
\tag{1}
\]

All equalities between lengths below are exponent equalities.  Fixed dyadic
constants do not affect them.

## 1. Scope of the published BBLR input

The primary input is S. Bettin, H. M. Bui, X. Li and M. Radziwill,
“A quadratic divisor problem and moments of the Riemann zeta-function,”
*J. Eur. Math. Soc.* **22** (2020), 3953--3980, Proposition 3.1.  The exact
scope used in this repository is transcribed in
`RH/Zeta85/Arith.lean` (`BBLRHyps`, `bblrErrorFactor`, and
`BBLRErrorBound`) and documented in `RH/Zeta85/Hypotheses.lean`.

Proposition 3.1 estimates a sum which is **already** in the form

\[
 \sum_{a m_1m_2-b n_1n_2=h\ne0}
 \alpha_a\beta_b
 W_1(m_1/M_1)W_2(m_2/M_2)
 W_3(n_1/N_1)W_4(n_2/N_2)w(h/H).
\tag{2}
\]

Its hypotheses name the six supplied lengths
`A,B,M1,M2,N1,N2`, their balance conditions, the coefficient bounds, and
the derivative bounds of the four weights.  The proposition estimates (2);
it does not turn an arbitrary coefficient of total length `M` into a
Dirichlet convolution with any chosen pair of lengths `M1*M2=M`.
Likewise, equation (14) in its proof performs Poisson summation after the
variables in (2) have been supplied.  It is not a factorization lemma.

Consequently, applying Proposition 3.1 with

\[
 M_1=T^{1-\eta},\quad M_2=T^\eta,\qquad
 N_1\asymp1,\quad N_2=T
\tag{3}
\]

requires a pointwise coefficient identity producing those variables.  The
sentence “use the asymmetric split” in file 18 does not provide one.

## 2. What the asserted split would prove if it existed

The local arithmetic in file 18 is exact.  With (3), the reciprocal lengths
in the BBLR Poisson block are

\[
 P\asymp AM_1=T^{\eta+1-\eta}=T,\qquad
 Q\asymp BN_1=T^\eta,\qquad H=T^\eta.
\tag{4}
\]

Therefore the signed-shift-first estimate has

\[
              PQ\asymp PH\asymp T^{1+\eta}=TH.
\tag{5}
\]

The preliminary zero-shift replacement must also carry the smoothing loss
which is explicit in the BBLR hypotheses.  Its exponent is

\[
 H^2(AM)^\varepsilon
   =T^{2\eta+(1+\eta)\varepsilon}.
\tag{6}
\]

It is power-small relative to `TH` precisely when

\[
 \varepsilon<\frac{1-\eta}{1+\eta}.
\tag{7}
\]

For a fixed `eta<1`, the right side is positive, so (6) is not the
obstruction.  Any fixed, explicitly named logarithmic power is swallowed by
the strict power margin in (7).  These claims are theorems
`asymmetric_block_exponents`, `preliminary_exponent_lt`, and
`preliminary_with_log_is_o` in
`RH/Zeta85/Discharge/EtaClosure.lean`.

It is useful to name

\[
                    \delta=\frac{1-\eta}{2}.
\tag{8}
\]

For `1/2<eta<1`, one has `0<delta<1/2`, and

\[
                 \delta+\frac\eta2=\frac12.
\tag{9}
\]

Equation (9) describes how a *new* refinement could manufacture (3); it is
not an identity which follows from relabelling an integer variable.

## 3. Exact definition of the method class being tested

The **literal relabel-only terminal class** consists of arguments which:

1. start from a fixed finite Heath--Brown identity and a dyadic block of its
   displayed factor variables;
2. form `a,m1,m2` and `b,n1,n2` only by assigning each displayed variable,
   whole, to one of those groups (a bounded dummy group is permitted);
3. introduce no additional pointwise Dirichlet-convolution identity and no
   subdivision of an integer variable into new factors; and
4. claim (3) for every terminal block before applying the BBLR Poisson-stage
   estimate.

The counterexample below kills exactly this class.  Selecting a different
identity, proving an extra convolution decomposition, or exploiting the
signed aggregate before variables are collapsed leaves the class and is not
ruled out.

## 4. A legal balanced `K=3`, `j=2` block

The `j=2` summand of the depth-three Heath--Brown identity has the factor
shape

\[
             a_1a_2d_1d_2=n,\qquad
             a_i\le X^{1/3},
\tag{10}
\]

with the two truncated variables carrying the Mobius factors and one of the
unrestricted variables carrying the logarithm.  Consider the dyadic block

\[
 a_1,a_2\asymp T^{\eta/2},\qquad
 d_1,d_2\asymp T^{1/2}.
\tag{11}
\]

It is legal throughout the audited interval.  Indeed,

\[
 2\frac\eta2+2\frac12=1+\eta,
 \qquad
 \frac\eta2<\frac{1+\eta}{3}
 \quad\left(\frac12<\eta<1\right).
\tag{12}
\]

The last inequality places both `a_i` strictly below the depth-three cutoff.
No variable in (11) has length `T` by itself, so this is not the long-variable
Type-I alternative used in the earlier grouping discussion.

Within whole-variable relabelling, the only group in (11) having exponent
exactly `eta` is `a1*a2`.  To see this without genericity language, let `r`
be the number of `eta/2` atoms and `s` the number of `1/2` atoms assigned to
the `A` group.  For `r,s` in `{0,1,2}`, the equation

\[
                 r\frac\eta2+s\frac12=\eta
\tag{13}
\]

has the unique solution `(r,s)=(2,0)` when `1/2<eta<1`.  After that unique
group is removed, the available exponents for a subproduct of `d1,d2` are

\[
                         0,\quad\frac12,\quad1.
\tag{14}
\]

But (3) requires

\[
                       0<1-\eta<\frac12,
\tag{15}
\]

which is none of (14).  Hence this legal terminal block cannot be put into
the asserted `M1=T^(1-eta)` shape by literal relabelling.

The Lean theorems `balanced_j2_K3_legal`,
`balanced_j2_A_group_unique`, and `balanced_j2_no_asymmetric_M1` prove
(12)--(15) for every real `eta` in the interval.  The independent rational
check uses `eta=3/4`: the atoms are `3/8,3/8,1/2,1/2`, the cutoff is `7/12`,
and the missing target is `1/4`.

This is a counterexample to the factorization premise, not a contradiction
from which the support-two theorem may be inferred.

## 5. The balanced block is not rescued by the same estimate

Keeping the balanced variables gives

\[
 M_1=N_1=T^{1/2},\qquad
 P=Q=T^{\eta+1/2}.
\tag{16}
\]

For the same signed-shift-first estimate `P(Q+H)`, the two powers are

\[
 \begin{aligned}
  \operatorname{exp}(PQ)-(1+\eta)&=\eta,\\
  \operatorname{exp}(PH)-(1+\eta)&=\eta-\frac12.
 \end{aligned}
\tag{17}
\]

Both are positive for `eta>1/2`.  Thus merely retaining the balanced block
does not close it: the dominant `PQ` term misses the trace target by the full
power `T^eta`.  This is formalized by `balanced_PQ_excess`,
`balanced_PH_excess`, and `balanced_signedShift_misses`.

## 6. The logarithmic obstruction remains independent

Even the hypothetical asymmetric block (3) has no power saving in (5).  Its
logarithms must therefore fit the trace budget literally.  Under the
prime-dyadic accounting proved in `RH/Zeta85/Discharge/LogBudget.lean`, a
remainder `X(log T)^C` contributes

\[
                    T(\log T)^{C+2}
\tag{18}
\]

against the budget `T(log T)^3`.  Hence

\[
                     \text{closure}\quad\Longleftrightarrow\quad C<1.
\tag{19}
\]

In particular, `C=0` closes this budget by itself; no cross-scale estimate is
then required.  Every `C>=1` fails.  Theorems
`literal_log_budget_fails` and `literal_log_budget_C1_fails` reuse the exact
dichotomy already proved as `LogBudget.budget_primeDyadic_fails`.  The present
audit does not assign an unsupported numerical value to the coefficient loss:
it records the exact threshold which any repaired construction must prove.
The finish-or-kill results for the currently available ways of reaching that
threshold are in `docs/audit/log_budget_routes.md`.

## 7. Exact construction needed to leave the killed class

An enlarged factorization would have to establish the following statement,
not merely choose the symbols `M1` and `M2`.

For every terminal dyadic coefficient `c_T(m)` of total length
\(m\asymp T\)
arising from a specified finite identity, construct a finite signed index set
`I` and coefficients `u_i,v_i` such that, pointwise on the block,

\[
 c_T(m)=\sum_{i\in I}\ \sum_{rs=m}u_i(r)v_i(s),
\tag{EF_eta}
\]

with all of the following verified:

1. `u_i` is supported at \(r\asymp T^{1-\eta}\) and `v_i` at
   \(s\asymp T^\eta\), up to explicitly stated fixed dyadic constants;
2. every weight and coefficient in `(EF_eta)` satisfies the derivative,
   support, balance, and coefficient hypotheses of BBLR Proposition 3.1;
3. the equality is pointwise, including the logarithmic factor in the
   `j=2` block--replacing a coefficient `1` by an unweighted divisor
   convolution is not equality;
4. the analogous construction on the other side supplies a rigorously
   treated bounded `N1` factor and a length-`T` `N2` factor;
5. all zero modes from the signed decomposition recombine pointwise with the
   singular-series subtraction; and
6. after summing every identity and dyadic block in its mandated order, the
   effective logarithmic exponent in (18) is proved to satisfy `C<1` (with
   every logarithm explicitly counted).

At the atom level suggested by (9), this would amount to an exact refinement
of each `T^(1/2)` smooth atom into factors of exponents `delta` and `eta/2`,
then grouping the two `delta` factors into `M1` and the two `eta/2` factors
into `M2`.  Equation (9) checks the lengths; `(EF_eta)` is the missing
coefficient identity and admissibility proof.

No such construction is present in the run or in this repository.  Until it
is proved, file 18 section 2 does not discharge the support-`sigma<2`
prime-side layer.

## 8. Finite support-model obstruction and exact analytic survivor

`RH/Zeta85/Discharge/EtaSuperpositionObstruction.lean` proves a necessary
support warning for `(EF_eta)`.  At `eta=3/4` and `T=625`, the balanced
`[25,50]` box has coefficient two at `899=29*31`, but 899 has no divisor in
the asymmetric short box `[5,10]`.  Every finite signed superposition whose
first factors are all supported in that short box is therefore zero at the
witness.  Signs, overlap, cardinality, and scale-dependent coefficients do
not change the pointwise-zero conclusion.  The scale-free prime-square
theorem proves the same mechanism whenever the first support is strictly
between 1 and the model prime.

No theorem identifies this balanced model coefficient with an actual
terminal Heath--Brown coefficient.  Accordingly the result does not kill
`(EF_eta)`: a pointwise decomposition may survive by using
divisor-dependent or exceptional pieces outside the excluded box, and a
retained-variable or non-pointwise analytic recombination lies outside the
formalized finite class.

The exact surviving retained-variable theorem is per outer dyadic prime
scale `Y`.  With the full signed `h`-sum at `H_Y=Y/T` taken before absolute
values and the actual Poisson zero modes subtracted and matched within that
same scale, it must prove

\[
 |R_{\rm HD}(Y,T,\eta)|
   \ll_{\eta,\mathcal W}Y(\log T)^C,\qquad C<1. \tag{HD_eta}
\]

The `C<1` threshold is the literal outer-`Y`-dyadic threshold from (18)--(19).
If the remainder were instead defined after the outer `Y`-sum, that scale
could not be charged again and the generous threshold would be `C<2`.
Neither analytic theorem is asserted.  The missing actual HB source
identification, `(EF_eta)`, A1, and every frozen-rung status remain unchanged.

## 9. Machine checks

The exact rational verifier and its committed output are
`verify/b4_eta_closure.py` and `verify/b4_eta_closure.out`.  Reproduce them
with

```sh
cmp -s verify/b4_eta_closure.out <(python3 verify/b4_eta_closure.py)
```

The unconditional algebra is in
`RH/Zeta85/Discharge/EtaClosure.lean`; its isolated dependency audit is
`comparator/PrintAxioms/EtaClosure.lean`.  There are no declarations using
`axiom`, `sorry`, or `admit` in the new Lean file.

The finite support obstruction is in
`RH/Zeta85/Discharge/EtaSuperpositionObstruction.lean`; its twelve-theorem
dependency audit is
`comparator/PrintAxioms/EtaSuperpositionObstruction.lean`, and its independent
exact replay is `verify/b4_eta_superposition_obstruction.py`.
