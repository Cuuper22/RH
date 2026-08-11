# `eta > 1/2` superposition support audit

Status: **the finite support model cannot be represented by a pointwise
superposition whose every first factor stays in one divisor-free asymmetric
short box.  No theorem here identifies the model with an actual terminal
Heath--Brown coefficient, so this does not by itself kill `(EF_eta)`.**

## Scope

`EtaClosure.lean` already kills whole-variable relabelling on the legal
depth-three `j=2` block with exponents

\[
  (\eta/2,\eta/2,1/2,1/2),\qquad 1/2<\eta<1.
\]

The proposed escape `(EF_eta)` in
`docs/audit/eta_gt_half_factorization.md` asks for a pointwise finite signed
identity

\[
 c_T(m)=\sum_{i\in I}\sum_{rs=m}u_i(r)v_i(s),             \tag{1}
\]

with every `u_i` on one common `T^(1-eta)`-scale and every `v_i` on one
common `T^eta`-scale.  The present audit proves an obstruction for an exact
finite **support model** of that shape.  It does not prove that the actual
terminal coefficient in `(EF_eta)` is nonzero at the model witness, nor does
it construct the sharp/smooth source identification needed to make that
claim.  Accordingly it is a necessary support warning, not a proof that the
literal `(EF_eta)` statement is false for the actual Heath--Brown family.

## Exact support obstruction

A term on the right of (1) can be nonzero at `m` only if `m` has a divisor in
the support of `u_i`.  Signs and the cardinality of `I` cannot change this:
if every summand is zero at `m`, their sum is zero there.

The exact regression fixes

\[
 \eta=3/4,\qquad T=5^4=625.
\]

The balanced square-root boxes are `[25,50]` on both variables, while the
asymmetric short and long boxes are `[5,10]` and `[125,250]`.  At

\[
 899=29\cdot31=31\cdot29
\]

the balanced-box model coefficient has the two ordered representations
`(29,31)` and `(31,29)`.  The complete divisor list is

\[
 (1,899),(29,31),(31,29),(899,1),
\]

so no divisor lies in `[5,10]`.  Every finite signed superposition with that
common short support is therefore zero at 899, independently of its long
coefficients, while the balanced-box model coefficient equals 2.

The Lean theorem
`convolutionCoeff_eq_zero_of_no_supported_divisor` proves the general
support principle.  `no_prime_sq_divisor_between` gives its scale-free
prime-square form: if `q` is prime, no divisor of `q^2` lies strictly between
1 and `q`.  Consequently `no_primePointModel_finiteSuperposition` rules out
a finite common-short-support representation of the point-support model at
every such prime-square scale.  The concrete theorems
`finiteSuperposition_899_eq_zero`, `balancedBoxModelCoeff_899`, and
`no_balancedBoxModel_finiteSuperposition` provide the independently replayed
finite regression.  None of these theorems says that an actual terminal
Heath--Brown coefficient takes the corresponding nonzero value.

This conclusion is deliberately narrower than a universal impossibility
claim.  The module formalizes finite sums.  Signs, overlap, or a
scale-dependent indexing rule do not evade the support argument if **every**
first-factor support still lies inside the excluded box: every term remains
zero at the witness.  The same pointwise-zero observation applies to a
well-defined integral superposition under that same support condition, but
no measure-theoretic theorem is asserted here.  A pointwise construction can
survive only by including pieces which leave the excluded box--for example
divisor-dependent supports or an explicitly retained exceptional balanced
piece.  A non-pointwise analytic identity after the full shifted sum or a
transform is also outside the formalized class.

## Why the positive balanced estimate still fails

Keeping the original two square-root variables gives

\[
 P=Q=T^{\eta+1/2},\qquad H=T^\eta,qquad
 \text{trace}=T^{1+\eta}.
\]

Thus the positive progression majorant has exact excesses

\[
 \operatorname{exp}(PQ)-(1+\eta)=\eta,
 \qquad
 \operatorname{exp}(PH)-(1+\eta)=\eta-1/2.              \tag{2}
\]

Both are positive in the audited interval.  Theorems
`balanced_progression_PQ_excess`, `balanced_progression_PH_excess`, and
`balanced_progression_requires_cancellation` prove (2).  Hence merely
retaining the balanced variables and then applying `P(Q+H)` is not the
surviving route.

## Exact surviving analytic theorem

The narrow higher-dimensional survivor is a theorem for the actual balanced
terminal family before the progression absolute values are taken.  It first
requires the missing source theorem identifying that family and its weights;
the support model above does not supply it.  On each side the analytic
estimate must retain the two truncated variables of scale `T^(eta/2)` and
the two original unrestricted variables of scale `T^(1/2)`, including the
Möbius and logarithmic coefficients.

To make the logarithmic accounting unambiguous, define
`R_HD(Y,T,eta)` to be the remainder for **one outer dyadic prime scale `Y`**,
with its full signed `h`-sum at `H_Y=Y/T` performed before the absolute value,
after subtracting the actual Poisson zero modes.  The required per-`Y`
theorem is

\[
 |R_{\rm HD}(Y,T,\eta)|
   \ll_{\eta,\mathcal W} Y(\log T)^C,
 \qquad C<1,                                             \tag{HD_eta}
\]

uniformly over the legal factor blocks inside that `Y` scale and admissible
smooth weights.  At the top scale \(Y\asymp T^{1+\eta}\) this has power
`T^(1+eta)`.  It must obtain the `T^eta` cancellation missing from `PQ` in
(2), rather than
majorizing `p`- and `q`-progressions separately.  It must also prove that the
signed sum of the actual zero modes within the same `Y` scale equals its
prime-pair singular-series contribution with an error satisfying the same
per-`Y` bound, before the outer `Y`-sum is taken.  The threshold
`C<1` is specifically the literal outer-`Y`-dyadic threshold: its positive
half is `LogBudget.budget_primeDyadic_closes`.  The negative half for every
`C>=1` is `EtaClosure.literal_log_budget_fails`, which delegates to
`LogBudget.budget_primeDyadic_fails`.  If `R_HD` were instead defined after
the outer `Y`-sum, that logarithm could not be charged a second time and the
relevant generous threshold would be `C<2`; this audit deliberately uses the
per-`Y` formulation.  A direct full-aggregate theorem with arbitrary
logarithmic saving would be stronger and would bypass this blockwise
transport.

An alternative survivor is a non-pointwise analytic superposition: after
inserting the full shifted equation, use Mellin/Fourier parameters, preserve
the signed sum over all pieces, and prove `(HD_eta)` only after integration and
recombination.  A merely scale-dependent or overlapping pointwise partition
does not help while all its first supports stay in the excluded box.  A
surviving pointwise decomposition must include divisor-dependent or
exceptional pieces outside it.  Any application to `(EF_eta)` must also prove
the missing link from the actual terminal Heath--Brown coefficient to those
pieces; this support-model audit does not provide that link.

The B-4 and A1 audits use different endpoint geometries.  The A1 files
`HBToBBLRSmoothGrouping.lean` and `ActualScaleBBLR.lean` give the analogous
warning at `eta=43/100`: gcd allocation preserves supplied smooth variables,
and the direct actual-scale positive bounds miss trace.  They do not prove
`(HD_eta)` in the present `eta>1/2` range.

## Reproduction

```bash
lake build RH.Zeta85.Discharge.EtaSuperpositionObstruction
lake env lean comparator/PrintAxioms/EtaSuperpositionObstruction.lean
python3 verify/b4_eta_superposition_obstruction.py
diff -u verify/b4_eta_superposition_obstruction.out \
  <(python3 verify/b4_eta_superposition_obstruction.py)
```

The verifier uses only integers and `fractions.Fraction`.  It checks the 899
support model and the two positive-majorant power excesses; it does **not**
check a logarithmic budget.  The cited logarithmic threshold comes from the
existing Lean theorems named above.  The new Lean module declares no axiom or
proof placeholder.  It is imported by `RH.Zeta85.Main`, and its twelve public
theorems are included in the standard-three dependency gate.  This
integration does not identify an actual terminal coefficient, change A1 or
a frozen rung, kill `(EF_eta)`, or assert `(HD_eta)`.
