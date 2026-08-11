# AXIOMS.md — what the 85 % layer assumes

Toolchain: Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.

The base library `Zeta23/` is **unconditional**: it declares no axiom, and `#print axioms` on each of
its 33 headline theorems reports only `propext`, `Classical.choice`, `Quot.sound` (re-verified after
this change — see `VALIDATION.md` §2).  Nothing under `Zeta23/` imports anything under `RH/`.

`RH/` is the **conditional** layer.  It declares exactly **eight** axioms, all in the single file
[`RH/Zeta85/Hypotheses.lean`](RH/Zeta85/Hypotheses.lean).  No axiom is declared anywhere else in
`RH/`, and no `sorry` occurs anywhere in `Zeta23/` or `RH/` (the only `sorry`s in the repository are
the deliberate ones in the trusted challenge files under `comparator/`).

---

## Phase 0b source-intake status

Phase 0b added archived 95/100 analysis material only.  Phase C now defines an
explicit Prop-valued `Inputs95` boundary and proves conditional quartic transfer
and headline theorems, but constructs no analytic instance.  The legacy rung
dependency graph in §§1.1--1.3 is unchanged; the new quartic headlines are
audited separately in §1.5.  Claims in the ingested files remain evidence to
audit, not assumptions or theorems; `docs/run/100/FINAL_100_RESULT.md` is
withdrawn and has no formal dependency.

The Phase 0d workflow runs `verify/check_axioms.sh` on every push and pull
request.  That script extracts §§1.1–1.3 directly from this file, diffs them
against fresh output from `comparator/PrintAxioms/Zeta85.lean`, and also runs
all four base `PrintAxioms` files.  Changing a compiled rung's dependency list
without updating this audit therefore fails CI.

Phase A1.1 changes no declaration or dependency.  It kills only the method
class “published \(d_4\) progression mean value + residue norm +
absolute/Cauchy modulus aggregation”; it does not discharge or replace
`signedPair_traceGrade_lt_3_2`.  The exact remaining statement is the signed,
weighted cross-residue progression estimate `(EDB)` and its blockwise
main-term identity, as recorded in `docs/audit/log_budget_routes.md`, Route 5.
No cited theorem is transcribed as an `Inputs95` field because none has that
statement.

Phase A1.2 also changes no compiled dependency.  Recombining prime scales
before absolute values would close only for an effective coefficient exponent
\(C<2\); the currently forced \(C\ge3\) still misses the trace budget by at
least one logarithm.  The present per-block hypotheses cannot imply such a
recombination: `LogBudget.blockwise_triangle_sharp` constructs aligned
errors that saturate every individual bound.  The actual surviving input is
the common-scale, coefficient-sensitive \(o(T(\log T)^2)\) estimate (14) in
`docs/audit/log_budget_routes.md`.  The repository now constructs an exact
sharp-cutoff depth-four Heath--Brown expansion, arbitrary scale-indexed
factor groupings, divisor-split coefficient candidates, and a shared
\((j,d,\ell,p,q)\) address.  Reduced-residue progression centering is now
constructed for these candidate coefficients, but finite centering alone
does not identify the source main term: BBLR's frequency \(\ell=0\)
contribution is a gcd-weighted integral, not that residue mean.
`BBLRGCDAllocation.lean` now proves the source's canonical allocation of a
positive gcd, its multiplicity-one filtered coefficient collapse, and the
two-sided finite \((p,q)\)-kernel reindexing for supplied outer sequences and
inner smooth weights.  Run 12 still supplies no equality selecting such
outer/smooth variables from every signed Heath--Brown block, nor the signed
Euler/Ramanujan evaluation of the frequency \(\ell=0\) integrals with an
explicit error.  Thus estimate (14) is not yet a statement about the actual
source-identified Heath--Brown coefficients and cannot prove the explicit
`PairTraceGrade95` field.
Therefore `signedPair_traceGrade_lt_3_2` remains unchanged.

`RH/Zeta85/Discharge/HBDepthFour.lean` proves the exact remainder

\[
 \Lambda-H_{4,Z}=(\mu-\mu_Z)^4*\zeta^3*\log
\]

and hence the four-term identity with coefficients \(4,-6,4,-1\) for every
\(n\le Z^4\).  It retains eight literal factors, proves every supplied
grouping multiplies back to its signed component, builds the
\(d_1d_2=d_3d_4=d\) coefficient sums with exact triangle majorants, and
defines a finite nonzero-frequency cross-scale candidate before absolute
values.  Its closed natural-number floor blocks are not a source partition,
and its generic all-residue-class mean is provably not interchangeable with
the reduced-class mean.  The module constructs the latter and proves its
centered cells sum to zero, including for a signed four-component candidate.
It also proves by exact countermodels that the two means can differ and that
reduced centering alone cannot imply `SingularSeriesCentering`.  BBLR's
actual frequency \(\ell=0\) gcd/integral main term and its signed
singular-series recombination remain unconstructed.  The module asserts no
estimate and no identification with run 12's `c_{d,p}`, `e_{d,q}`, or
`F_{d,ell}`.  `SingularSeriesCentering` names only the zero-error special
case without assuming it.

`RH/Zeta85/Discharge/BBLRGCDAllocation.lean` separately proves the finite
source map that `HBDepthFour.splitCoeff` lacks.  For \(d>0\), allocation by
\(d_1=\gcd(A_0,d)\), \(d_2=d/d_1\) is an equivalence with the filtered
splits \(d_1d_2=d\), \((a,d_2)=1\).  Applying it on both sides proves the
condition \((am,bn)=1\), the converse gcd identity, the exact collapsed
coefficients, and the original-fiber kernel sum.  The unit-weight regression
at \(d=p=2\) is \(3\) canonical terms versus \(4\) terms for the unfiltered
`HBDepthFour.splitCoeff` pattern.  This discharges the gcd allocation and
multiplicity subproblem for supplied BBLR inputs; it does not construct the
smooth Heath--Brown grouping, any A1 estimate, or the frequency \(\ell=0\)
singular-series recombination.

`RH/Zeta85/Discharge/HBToBBLRSmoothGrouping.lean` finishes and kills the
fixed asymmetric **literal-slot** grouping claimed in run 12.  The legal
zero-based component `j = 1` block
\((43/200,43/200,2/5,3/5)\) has total exponent \(143/100\), its two
truncated Möbius slots give the requested outer exponent \(43/100\), and its
only literal smooth slots remain \(2/5,3/5\).  Their left-target gap is
exactly \(1/10\), while every right-target gap is at least \(33/100\), so no
\(T^{o(1)}\) cushion yields the prescribed \((1/2,1/2)\) and
\((7/100,93/100)\) pairs.  The module separately proves that collapsing two
coefficient-one slots produces the nonconstant divisor multiplicity
\(\zeta*\zeta\), rather than another literal smooth slot.  This changes no
axiom or rung status.  It leaves open an actual-scale all-block estimate, a
proved superposition identity with derivative and recombination control, or
a higher-dimensional divisor theorem retaining all factor variables.

`RH/Zeta85/Discharge/ActualScaleBBLR.lean` then audits the surviving exact
\((2/5,3/5)\) symmetric block without introducing a premise.  Direct BBLR
Proposition 3.1 has error exponents \(179/100\) and \(161/100\), exceeding
the trace exponent by \(9/25\) and \(9/50\).  Separately, the run-12
progression majorant applied after equation (14) has \(d=1\) lengths
\(P=Q=T^{83/100}\): its \(PQ\) term exceeds trace by \(23/100\), while its
\(PH\) term saves \(17/100\).  The physical Fourier scale
\(T^{-23/100}\) is exactly offset by the \(T^{23/100}\) nonzero-frequency
cutoff.  These results kill only those two displayed positive-majorant
method classes.  They do not bound the original signed remainder from below
or exclude simultaneous cancellation before the progression majorant, so
no frozen rung status or compiled headline axiom dependency changes.

The B-2 Rudnick--Sarnak audit likewise changes no compiled headline
dependency.  `RS1996ZetaInputs.theorem31` now records the published
unconditional smoothed Theorem 3.1 at \(m=1\), with a gauge-fixed zero-sum
test, multiplicities, strict support below two, and its explicit \(O(T)\)
error.  It is deliberately separate from `BlockMomentLimits`: the R1a
principal construction, complex Poisson identity at the actual
enlarged-window zeros, \(k=3,4\) finite-grid estimates, and simultaneous
height-smoothing limit are not derived from the published theorem.  No
`RS1996ZetaInputs` instance is constructed.

`RH/Zeta85/Discharge/RSReduction.lean` now discharges the deterministic
finite part of that reduction.  It enumerates the disjoint pairings for
\(k=1,2,3,4\) as \(0,1,3,6+3\), proves that every contraction vector is
zero-sum, machine-checks the binomial centering from formula (27) to formula
(18), and specializes the already formalized top-hat integrals to formula
(21).  It deliberately does not identify `rsMainTerm` with those scalar
contractions or identify either expression with an actual block.  Those
remaining analytic bridges stay in `BlockMomentLimits`; no instance or new
research axiom is introduced.

Phase B-1 is discharged without an input field.
`RH/Zeta85/Stability.lean` proves the exact quartic stability bound,
its isometric-compression form, and its principal-compression form from
finite-dimensional hypotheses alone.  No analytic assumption is imported
and no legacy hypothesis is used.  The dedicated CI audit
`comparator/PrintAxioms/Stability.lean` checks the standard dependency set
verbatim.

Phase A1.3 changes no headline dependency.  The exact one-shot
arbitrary-coefficient class \(\mathcal W_1\) is killed: independent
progression cells admit a phase-aligned countermodel, fixed-modulus Weil
completion misses by \(T^{9/50}\), and the applicable Bettin--Chandee and
BBLR bounds miss by fixed powers.  A simultaneous coefficient-sensitive
`(WG-HB)` estimate would close with net saving \(7/400\) under the
displayed candidate bound, but the repository lacks the proved source
identification of every signed depth-four block with supplied BBLR outer
sequences and inner smooth weights, together with the integrated Fourier
kernel estimates, frequency \(\ell=0\) formula, and signed Ramanujan
evaluation needed to apply that input faithfully.  The canonical gcd
allocation is now proved, but the sharp algebraic coefficient object and
reduced-residue centering do not supply those remaining equalities.
Therefore
`signedPair_traceGrade_lt_3_2` remains unchanged.

Phase A2.1 also changes no compiled dependency.  The claimed cycle-3
power-complementary identity is impossible in the exact finite
common-lattice, critical-channel PB/TDAC class: after removing an alias-free
distinguished window whose residual symbol is positive on every fiber, the
complement needs rank \(N\) but the cycle-3 count supplies at most
\(N-n_0\).  Certified rational-interval evaluation verifies the positive
residual for the file-15, R-8686, and R-9506 symbols.  This indicts the
construction premise, not the stability or moment algebra.
`RH/Zeta85/Discharge/AliasRankObstruction.lean` now proves the finite
linear-algebra core in Lean: each explicit residue channel has rank at most
its residue count, a nonvanishing diagonal residual has full rank, and the
three exact terminal count budgets are deficient.  Its public theorems print
only `[propext, Classical.choice, Quot.sound]`.  The transcendental
nonvanishing assertions for the two terminal Euler profiles remain certified
by `verify/a2_1_tdac_rank.py`, not by this algebraic module.
`PrincipalCyclicBlock` now names the exact replacement obligation, including
literal windows, critical grids, pointwise energy reconstruction, a mean-one
distinguished profile, and integrable translated-product limits; no instance
is constructed.  The frozen quartic rungs therefore remain conditional on
that structure and the other three exact per-support premises.

Phase A2.2 also changes no headline dependency.  In the base hat
normalization, a one-window-per-interval block with intrinsic mean one is
the literal compression \(C=H/\sigma\); the terminal cap \(r\leq V_\sigma\)
omits the required factor \(\sigma\).  The quadratic profile has
\(\sup V_\sigma=1200/1031<143/100\), so no mean-one block exists in the
stated class.  For the honest block, a positive rational five-atom law
matches the paper-derived closed moments through degree four below the
corrected threshold \(Y=\sigma-1\), making the sharp corrected tail value
zero.
RH/Zeta85/Discharge/AliasFallback.lean verifies the rational moment
reconstruction, weight positivity, support inequalities, scaling identity,
and zero tails for the paper-derived closed moment definitions, without
adding a field or primitive declaration.  Equality of those definitions
with Mathlib integrals and the RS specialization remains unformalized.
Every headline printed by
comparator/PrintAxioms/AliasFallback.lean depends exactly on
[propext, Classical.choice, Quot.sound].

---

## 1. `#print axioms` — verbatim

### 1.1 The 0.679 theorem (support 101/100)

```
'zeta85_rung_support_101_over_100' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_error_bound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated,
 RH.Zeta85.Hypotheses.windowCost_101]
'zeta85_rung_support_101_over_100_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_error_bound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated,
 RH.Zeta85.Hypotheses.windowCost_101]
```

### 1.2 The 0.797 theorem (support 5/4)

```
'zeta85_rung_support_5_over_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_error_bound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated,
 RH.Zeta85.Hypotheses.windowCost_125]
'zeta85_rung_support_5_over_4_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_error_bound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated,
 RH.Zeta85.Hypotheses.windowCost_125]
```

### 1.3 The 0.85 theorem (support 143/100) and its corollary

```
'zeta85_simple_on_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_poisson_blocks,
 RH.Zeta85.Hypotheses.shiu_majorant,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_simple_on_critical_line_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_poisson_blocks,
 RH.Zeta85.Hypotheses.shiu_majorant,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_eighty_five_percent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_poisson_blocks,
 RH.Zeta85.Hypotheses.shiu_majorant,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_eighty_five_percent_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_poisson_blocks,
 RH.Zeta85.Hypotheses.shiu_majorant,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
```

Reproduce with `lake env lean comparator/PrintAxioms/Zeta85.lean`.  The same eight lines with the
`RH.Zeta85.rung*` / `RH.Zeta85.eightyFive*` names (the solution-side theorems the comparator topic
delegates to) are identical.

### 1.4 What is proved outright inside the conditional layer

```
'RH.Zeta85.windowCost_143' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.jSat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.cPC_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.count_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.epsForm_of_twoTraceCert' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.shiftSum_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.sum_over_separated' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.nearInt_int_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.four_nearInt_le_norm_cexp_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.bdiffIter_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.budget_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.budget_primeDyadic_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.budget_dyadic_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.verdict_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.depth_three_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.depth_four_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.fixed_modulus_weil_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.wg_hb_candidate_saving' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.wg_hb_net_saving' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.bettin_chandee_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.bblr_endpoint_first_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.blomer_pascadi_range_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.mqw_range_excesses' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.power_beats_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.Exponents.bblr_blackbox_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.stability_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.tailExcessSq_isometricCompression_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.tailExcessSq_principalCompression_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.stability_inequality_isometricCompression' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.stability_inequality_principalCompression' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.QuarticWindowWitnesses.windowCost_14999' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.QuarticWindowWitnesses.windowCost_19999' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.TopHatMoments.formula21M2Integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.TopHatMoments.formula21M3Integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.TopHatMoments.formula21M4ReducedIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.TopHatMoments.crossingReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.TopHatMoments.formula21M4Integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.TrimmedMoment.finite_trimmed_quartic_dual' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.TrimmedMoment.Terminal9506.density_gt_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.TrimmedMoment.Terminal8686.density_gt_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.R9383ExactEndpoint.endpoint_box_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.EtaClosure.preliminary_with_log_is_o' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.EtaClosure.balanced_j2_K3_legal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.EtaClosure.balanced_j2_no_asymmetric_M1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.EtaClosure.balanced_signedShift_misses' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.EtaClosure.literal_log_budget_C1_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.stability_prebound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RobustStability.robust_stability_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RobustStability.robust_stability_inequality_withCountError' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RobustStability.robust_stability_inequality_principalCompression' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RobustStability.robust_stability_inequality_principalCompression_withCountError' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RobustStability.spectral_residualTail_eq_tailExcessSq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RobustStability.principal_spectral_headTrimmedMomentInputs_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.profileSaturatedCost_v8686' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.profileSaturatedCost_v9506' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.QuarticGramFamily.G_eq_A_add_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.StableZeroSide.block_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.core_count_le_dyadic_add_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.robustBlockTailBound_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSReduction.weightedCyclicSymbol_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSReduction.rsPairVector_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSReduction.rsMainTerm_k1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSReduction.rsMainTerm_k2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSReduction.rsMainTerm_k3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSReduction.rsMainTerm_k4' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSReduction.centeredContraction_eq_formula18' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSReduction.topHat_formula18_eq_formula21' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSReduction.topHat_centeredContraction_eq_formula21' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.integral_abs_mul_shift_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.distanceIntegral_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.onePairCoordinateIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.onePairIntegrand_integrable_of_continuous_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.distanceKernel_integrable_of_continuous_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_one_eq_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_one_eq_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.integral_fin_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_two_eq_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k2_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k3_01_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k3_02_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k3_12_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_01' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_02' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_03' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_12' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_23' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_01_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_02_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_03_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_12_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_13_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_23_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.normalized_k4_onePairSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_separated' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_nested' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_crossing' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_separated_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_nested_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_crossing_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.separatedTwoPairSection_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.separatedTwoPairCoordinateIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.nestedTwoPairSection_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.nestedTwoPairCoordinateIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.crossingTwoPairCoordinateIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.separatedTwoPairFubiniKernel_integrable_of_continuous_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.nestedTwoPairFubiniKernel_integrable_of_continuous_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.crossingRawKernel_integrable_of_continuous_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.nestedDistanceKernel_integrable_of_continuous_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_separated_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_nested_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_crossing_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k4' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k2_of_continuous_compactSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k3_of_continuous_compactSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k4_of_continuous_compactSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.BBLRGCDAllocation.sum_splitFiber_eq_divisorsAntidiagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.BBLRGCDAllocation.collapsedCoeff_eq_divisorSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.BBLRGCDAllocation.collapsedCoeff_two_two_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.BBLRGCDAllocation.rawCollapsedCoeff_two_two_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.BBLRGCDAllocation.collapsedKernelSum_eq_originalFibers' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.hb_component_one_inventory' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.hb_component_one_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.muCut_ne_coefficientOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.bblr_allocation_preserves_supplied_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.terminal_component_one_legal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.left_literal_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.right_short_literal_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.right_long_literal_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.no_left_literal_grouping' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.no_right_literal_grouping' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.no_asymmetric_literal_grouping' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.twoUnitSlotMultiplicity_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.twoUnitSlotMultiplicity_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.two_unit_slot_collapse_not_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBToBBLRSmoothGrouping.zeta_sq_eq_twoUnitSlotMultiplicity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.block_geometry_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.blackBox_exponents_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.blackBoxAB_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.blackBoxWatt_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.blackBox_not_traceGrade' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.blackBox_not_traceGrade_with_slack' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.source_fourier_exponents_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.source_lengths_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.progression_majorant_is_PQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.progressionPQ_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.progressionPH_saving' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.progression_majorant_not_traceGrade' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.ActualScaleBBLR.taylor_H_sq_saving' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.hbComponent_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.sum_hbComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.hbAtom_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.hbGrouped_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.empty_singleton_groupings_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.abs_muCut_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.muCut_tail_four_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.inDyadicBlock_iff_log_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.sum_dyadicPart_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.reducedCoeff_eq_convolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.abs_reducedCoeff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.abs_splitCoeff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.localizedSplitCoeff_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.abs_localizedSplitCoeff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.plannedLeftBlockCoeff_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.plannedRightBlockCoeff_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.abs_plannedLeftBlockCoeff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.abs_plannedRightBlockCoeff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.sum_centeredProgressionCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.sum_reducedCenteredProgressionCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.sum_plannedLeftReducedCenteredCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.sum_plannedLeftSignedReducedCenteredCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.allClass_zeroMode_ne_reduced_zeroMode' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.reducedCentering_alone_not_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.singularSeriesCentering_iff_error_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.zeta_mul_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.hb4_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.hb4_eq_vonMangoldt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.HBDepthFour.sum_hbComponent_eq_vonMangoldt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The 51 `RSPairIntegrals` lines are the exact normalized output of
`comparator/PrintAxioms/RSPairIntegrals.lean`.  They cover every one- and
two-pair contraction through degree four and the continuous compact-support
wrappers; all have the standard three dependencies.  This dependency status
does not construct `BlockMomentLimits` or discharge cyclic-symbol
admissibility, the actual theorem-3.1 instance, common height smoothing,
`log T` versus `ell(T) = log(T/2*pi)`, complex Poisson, the degree-three/four
finite-grid/end estimates, or the actual principal-block bridge.

### 1.5 Conditional quartic headlines

`comparator/PrintAxioms/QuarticMain.lean` prints the final dyadic and
cumulative theorem names:

```text
'RH.Zeta85.rung8657' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.rung8657_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.rung8686' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.rung8686_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.rung9383' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.rung9383_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.rung9506' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.rung9506_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This standard-three output means that the transfer and assembly add no Lean
axiom.  It does **not** make the results unconditional: every theorem takes
exactly `FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, and
`BlockMomentLimits` for its support family.  The 21 public transfer theorems
in `comparator/PrintAxioms/QuarticTransfer.lean` have the same standard-three
output.  The exact independent replay is `verify/quartic_transfer.py` with
committed hashes:

```text
dc99b510fdf1966f11535bf57a3dc53f4056c679e0275c8a649c01facf5f3bdf  verify/quartic_transfer.py
05615d7eb1727532cb81a5c04598630ebd9c29408b729770d34e4b282b533cce  verify/quartic_transfer.out
```

---

## 2. Axiom count per rung

| rung | constant | axioms it depends on | count |
|---|---|---:|---:|
| base (Zeta23, Theorem D) | 2 − 1/c₁* = 0.6725007… | — | **0** |
| 1 | 0.67924886307 | `bblr_error_bound`, `signedPair_traceGrade_lt_5_4`, `windowCost_101`, `traceTransfer_saturated` | **4** |
| 2 | 0.79721415286134 | `bblr_error_bound`, `signedPair_traceGrade_lt_5_4`, `windowCost_125`, `traceTransfer_saturated` | **4** |
| 3 | 1893603832049143/2227707598259143 = 0.8500235101… | `bblr_poisson_blocks`, `shiu_majorant`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated` | **4** |

The quartic headlines use no declared research axiom, but each is conditional
on four Prop-valued structures:

| rungs | family | explicit structure premises | declared research axioms | unconditional? |
|---|---|---|---:|---|
| R-8657, R-8686 | `Family14999` | `FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, `BlockMomentLimits` | **0** | no |
| R-9383, R-9506 | `Family19999` | `FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, `BlockMomentLimits` | **0** | no |

The pair-trace and published RS structures are upstream routes to the first
and fourth premises respectively.  They are deliberately not arguments of
the headline theorems, because the required derivation bridges have not been
proved.

The counts coincide but the **contents differ**, and that is the point:

* rungs 1 and 2 use the **published** BBLR error bound and the `η < 1/4` block closure, which is
  *power*-saving relative to trace scale.  They do **not** use `shiu_majorant` and do **not** use the
  cycle-5 claim `signedPair_traceGrade_lt_3_2`;
* rung 3 uses the cycle-5 route instead, which is only *polylogarithmically* saving, needs the Shiu
  majorant, and is the branch whose logarithmic budget does not close (see §3, Axiom 5, and
  `FINDINGS.md` §7);
* the only shared axioms are `traceTransfer_saturated` (used by all three) and — for rungs 1 and 2 —
  the published BBLR bound.  Rung 3's window cost is **not** an axiom: `RH.Zeta85.windowCost_143` is
  proved from the exact rational moments of `RH/Zeta85/Window.lean`.

Two of the eight axioms (`bblr_error_bound`, `bblr_poisson_blocks`) are published literature; three
(`shiu_majorant`, `signedPair_traceGrade_lt_5_4`, `signedPair_traceGrade_lt_3_2`) are the run's
arithmetic claims; two (`windowCost_101`, `windowCost_125`) are the run's numerical certificates for
transcendental windows; one (`traceTransfer_saturated`) is the support-beyond-one trace evaluation.

---

## 3. The eight axioms, with provenance

Full docstrings — exact mathematical statement, source, and why not discharged — are in
[`RH/Zeta85/Hypotheses.lean`](RH/Zeta85/Hypotheses.lean); they are reproduced here in condensed form.
No axiom below lacks a source.

### Axiom 1 — `bblr_error_bound : BBLRErrorBound`

*Status:* **[PUBLISHED LITERATURE: Bettin–Bui–Li–Radziwiłł, "A quadratic divisor problem and moments
of the Riemann zeta-function", J. Eur. Math. Soc. 22 (2020) 3953–3980, Proposition 3.1 (error
bound)]**, as quoted at `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` equation (3).

*Statement.*  For `A, B, M₁, M₂, N₁, N₂, H ≥ 1`, `M = M₁M₂`, `N = N₁N₂`, coefficients `α_a`, `β_b`
and smooth weights `W₁…W₄` supported in `(1,2)` satisfying `W_i^{(j)} ≪ (ABMN)^ε` (`0 ≤ j ≤ 4`),
`α_a ≪ A^ε`, `β_b ≪ B^ε`, `M₁ ≤ M₂(ABMN)^ε`, `N₁ ≤ N₂(ABMN)^ε`, and `H ≪ (AB)^{1/2+ε}`, the smoothly
`h`-averaged quadratic divisor sum
`S₊ = Σ_{am₁m₂ − bn₁n₂ = h ≠ 0} α_a β_b W₁(m₁/M₁)W₂(m₂/M₂)W₃(n₁/N₁)W₄(n₂/N₂) w(h/H)`
splits as `S₊ = M + E`, `M` the `(am₁,bn₁) = d` gcd main term, with
`E ≪_ε (ABMNH²)^{1/4+ε}·(AB + H^{1/4}(A+B)^{1/2}(ABMN)^{1/8})`.
**The first factor in the bracket is `AB`, not `(AB)^{1/2}`** — see `FINDINGS.md` §3.

*Why not discharged.*  Published; its proof is a dispersion argument plus Watt's spectral estimate
for sums of Kloosterman sums.  The task specification directs that it be taken verbatim.  The main
term is existentially quantified in the Lean rendering, which makes the axiom weaker than the
published statement.

### Axiom 2 — `bblr_poisson_blocks : BBLRPoissonBlocks`

*Status:* **[PUBLISHED LITERATURE: BBLR, ibid., the displayed equation (14) inside the proof of
Proposition 3.1]**, transcribed with the block scales at
`docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §1 (5)–(7), (9)–(11), and combined with §3
(16)–(17).

*Statement.*  After writing `d = (am₁,bn₁)`, `p = (a/d₁)(m₁/d₂)`, `q = (b/d₃)(n₁/d₄)`, Poisson
summation presents the nonzero-frequency part of `S₊` as a finite sum of blocks
`R_d = Σ_{ℓ≠0} Σ_{p≍P_d, q≍Q_d, (p,q)=1} c_{d,p} e_{d,q} F_{d,ℓ}(p,q) Σ_h w_d(h) e(∓ℓh p̄/q)`
with `P_d ≍ AM₁/d`, `Q_d ≍ BN₁/d`, `H_d = H/d`, `‖F_{d,ℓ}‖ ≪_J d(1+|ℓ|d)^{−J}(log T)^{C_J}`; the
per-block bound `|R_d| ≪ P_d(Q_d + H_d)(1+d)^{−2}(log T)^C` is what the Lean statement records.

*Why not discharged.*  The identity is published (as Axiom 1).  The per-block bound is a derived
statement of the run; the parts of that derivation that *could* be discharged here have been — the
signed-shift reciprocal lemma (12)–(13) is **proved** in `RH/Zeta85/Discharge/SignedShift.lean` and
every exponent comparison of §3 in `RH/Zeta85/Discharge/Exponents.lean`.  What survives is (14)
itself plus the claim that `c_{d,p}`, `e_{d,q}` are the actual fixed-depth convolution coefficients
with the stated majorants, which is not formalizable without the whole Heath–Brown apparatus.

### Axiom 3 — `shiu_majorant : ∀ η, 0 < η → η < 1/2 → ShiuMajorant η`

*Status:* **[RUN CLAIM: `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §2, equation (14),
undischarged]**; underlying published result P. Shiu, "A Brun–Titchmarsh theorem for multiplicative
functions", J. Reine Angew. Math. 313 (1980) 161–170.

*Statement.*  For the recombined divisor-bounded Heath–Brown coefficients `c_p`,
`Σ_{p ≍ P, p ≡ r (q), (r,q)=1} |c_p| ≪ (P/φ(q))·(log T)^C`, uniformly for `q ≤ P·T^{−η+o(1)}`.

*Why not discharged.*  A full proof along the route the source indicates does not close: Shiu's
theorem is not in Mathlib, and its hypotheses (a non-negative multiplicative majorant) do not apply
verbatim to the run's `c_p`, which are *signed* convolutions of Möbius and smooth factors.  The
source's "fix every short factor" reduction presupposes the factorization of the recombined
coefficients — the unformalized Heath–Brown apparatus again.

### Axiom 4 — `signedPair_traceGrade_lt_5_4 : BBLRErrorBound → ∀ σ, 1 < σ → σ < 5/4 → SignedPairTraceGrade σ`

*Status:* **[RUN CLAIM: `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §2 ("Theorem (fixed
support)" and its block closure, (T1)–(T5)), transported to the aggregate criterion (AS) of
`docs/run/01_arithmetic_cycle1.md` §4, undischarged]**.

*Statement.*  At `η = 1/4 − κ`, a Heath–Brown identity of depth `K` with `X^{1/K} < H·T^{−10ε}`
splits every block into (i) a Type-I block with a long smooth variable, handled by Poisson summation
plus the hybrid large sieve with `O_A(X log^{−A}X)`, and (ii) the terminal BBLR block with
`A, B = H·T^{O(ε)}`; "there is no third block".  Feeding (ii) into Axiom 1 gives power-saving errors,
so the signed aggregate criterion `(AS)` holds at every fixed `1 < σ < 5/4`.

*Why not discharged.*  Three obstacles, each attempted: (i) the finite-depth Heath–Brown identity and
factor-grouping dichotomy are not in Mathlib; (ii) the Type-I estimate needs Poisson summation plus
the hybrid large sieve in a uniform form not available; (iii) "there is no third block" cannot be
stated without (i).  What *was* discharged: all of the exponent bookkeeping
(`RH.Zeta85.Exponents.bblr_blackbox_ceiling`, `bblr_savings`, `EA_traceGrade_iff`,
`EW_traceGrade_iff`) and the fact that a fixed power beats every fixed logarithmic loss
(`RH.Zeta85.LogBudget.power_beats_log`).

### Axiom 5 — `signedPair_traceGrade_lt_3_2 : BBLRPoissonBlocks → (∀ η, …, ShiuMajorant η) → ∀ σ, 1 < σ → σ < 3/2 → SignedPairTraceGrade σ`

*Status:* **[RUN CLAIM: `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` equation (2) and
§5, undischarged — AND, on the evidence of `RH/Zeta85/Discharge/LogBudget.lean`, not established by
the run at all]**.  This is the single most load-bearing undischarged statement in the artifact.

*Statement.*  For every fixed `0 < η < 1/2`, `R_HB ≪ (T^{1+η} + T^{1/2+2η})(log T)^C`; consequently
the aggregate criterion `(AS)` holds at every fixed connected support `1 < σ = 1 + η < 3/2`.

*Why not discharged — two distinct reasons.*

1. The derivation of (2) needs Axioms 2 and 3 and the Heath–Brown recombination.  The two pieces that
   could be discharged were discharged: the signed-shift reciprocal lemma (12)–(13)
   (`RH/Zeta85/Discharge/SignedShift.lean`) and the exponent comparisons (18)–(19)
   (`RH.Zeta85.Exponents.cycle5_scales`, `cycle5_traceGrade`, `cycle5_gain`).
2. **Even granting (2) in full, it does not imply `(AS)`.**  `(AS)` demands a logarithmic *saving*
   `≪_A X(log X)^{−A}`; (2) supplies a logarithmic *loss* `(log T)^{+C}`.  The audit in
   `RH/Zeta85/Discharge/LogBudget.lean` computes the budget exactly: the free room for the error's
   logarithms is `(log T)^{<2}` in the most generous single-block reading
   (`LogBudget.budget_closes`/`budget_fails`), `(log T)^{<1}` under the literal `Y`-dyadic triangle
   sum displayed in `docs/run/02_certificate_cycle2.md` (14)
   (`budget_primeDyadic_closes`/`budget_primeDyadic_fails`), and `(log T)^{<0}` only in the fully
   triangle-summed model that also dyadicizes the direct `h`-sum
   (`budget_dyadic_closes`/`budget_dyadic_fails`), while the Heath–Brown depth forced at
   `η = 43/100` is `K ≥ 4` (`LogBudget.depth_at_85`), giving `C ≥ K − 1 ≥ 3`.  All three
   thresholds fail (`LogBudget.verdict_all`).  See `FINDINGS.md` §7.

   Per R2 the 85 % target is **not** weakened to accommodate this: the target stays
   `1893603832049143/2227707598259143`, and this axiom states exactly the blocking statement at the
   strength the transfer consumes.

### Axiom 6 — `windowCost_101 : SaturatedWindowCost (101/100) (2 − cRung101)`

*Status:* **[RUN CLAIM: `docs/run/07_root_gain_support_1p01.md`, "Explicit numerical certificate",
undischarged]**.

*Statement.*  At `λ = 101/100` with `v(s) = cos(√2 s)` on `[−1/2,1/2]` and `K_λ(s,t) = min(λ|s−t|,1)`:
`I₁ = 2sin(√2/2)/√2`, `I₂ = 1/2 + sin√2/(2√2)`, `J_λ = 2λ∫₀^{1/λ}d·A(d)dd + 2∫_{1/λ}^1 A(d)dd` with
`A(d) = ((1−d)/2)cos(√2 d) + sin(√2(1−d))/(2√2)`, and
`D_{1.01}(v) = (I₂ + λJ_λ)/(λI₁²) = 1.32075113693…`, so `2 − D = 0.67924886307…`.  The axiom asserts
the cost at the **truncated** decimal, which is the weaker assertion.

*Why not discharged.*  The window is transcendental; a rational bound to twelve significant figures
requires certified interval arithmetic on `sin`/`cos` at `√2`, which Mathlib's `norm_num` extensions
do not provide.  Verified numerically outside Lean (`FINDINGS.md` §4): the computed value is
`2 − D = 0.6792488630700078…`, so the truncation is on the safe side.

### Axiom 7 — `windowCost_125 : ∃ σ, 1 < σ ∧ σ < 5/4 ∧ SaturatedWindowCost σ (2 − cRung125)`

*Status:* **[RUN CLAIM: `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §3, equations
(11)–(16); same numbers at `docs/run/03_arithmetic_cycle3.md` §5 (32)–(37); undischarged]**.

*Statement.*  For `K(t) = min(|t|,1)` at `σ = 5/4`, the Euler equation
`u(x) + ∫min(|x−y|,1)u(y)dy = C` has the even solution `u(x) = cos(√2 x)` on `|x| ≤ 3/8`,
`u(x) = A₀cos(|x|−1/2) + B₀sin(√3(|x|−1/2))` on `3/8 ≤ |x| ≤ 5/8`, with `A₀ = 0.765651150533640…`,
`B₀ = −0.479300891051646…`; `∫u = 1.09716424928793…`, `C = 1.31965363103003…`,
`D*_{5/4} = 1.20278584713866…`, `2 − D*_{5/4} = 0.79721415286134…`.  Since `σ ↑ 5/4` is a limit, the
axiom asserts the cost at *some* fixed `σ ∈ (1, 5/4)` and at the truncated decimal.

*Why not discharged.*  As Axiom 6, plus: the profile is characterised as the solution of an integral
equation, so discharging it also requires proving that the displayed function *is* that solution.
Verified numerically outside Lean (`FINDINGS.md` §4): the Euler equation holds to `1·10⁻⁹` uniformly
on the support, and `2 − D = 0.7972141529233692…`, so the truncation is on the safe side.

### Axiom 8 — `traceTransfer_saturated : ∀ σ D, 1 < σ → σ < 3/2 → SaturatedWindowCost σ D → SignedPairTraceGrade σ → TwoTraceCert zetaZeroConfig D`

*Status:* **[RUN CLAIM: `docs/run/01_arithmetic_cycle1.md` §2 (5)–(9),
`docs/run/01_certificate_cycle1.md` (5)–(6), `docs/run/02_arithmetic_cycle2.md` §1,
`docs/run/02_certificate_cycle2.md` §2 (13)–(17), `docs/run/12` §5; undischarged for the
support-beyond-one part only]**.  The `σ ≤ 1` case is the base paper's Proposition 5.6 and is
**proved in this repository** (`Zeta23.ThmD.tracesBoundsD_concrete`).

*Statement.*  Given an achievable saturated-kernel cost `D` at support `σ ∈ (1, 3/2)` and the signed
aggregate criterion at that support, the zeros of `riemannZeta` carry a Gabor family whose hat-unit
Gram matrix satisfies Seam A `4·tr Ĝ − ‖Ĝ‖²_F − 2N − o(N) ≤ N₀ˢ`, `tr Ĝ = N(1+o(1))` and
`‖Ĝ‖²_F ≤ (D + o(1))N`.

*What is reused rather than assumed.*  The whole zero side.  `Zeta23.Assembly.seamA_mult2` is proved
in the base repository for an arbitrary `Zeta23.Params` family and carries **no** restriction
`λ ≤ 1`; the Poisson identity behind it (`Zeta23.Taper.hasSum_phiHatR_sq`) needs only
`TaperProfile ϱ`, `0 < w`, `2w ≤ L`.  The rank–trace inequality (`RHLinalg.rank_trace_ineq`), the
`c = 2` multiplicity-aware count (`Zeta23.ZeroSide.ZeroBlockData.mult_two`) and the fixed-`T` algebra
(`Zeta23.ThmD.N0star_lower_c`) are reused verbatim (`docs/REUSE_MAP.md` §5).

*Why not discharged.*  What fails past `λ = 1` is the base repository's error bookkeeping
`Zeta23.Params.calE = w/L + (l² + X)log l/(T l) + T^{λ/2−1}`: the summand `X·log l/(T·l)` with
`X = (T/2π)^λ` tends to `0` **iff** `λ ≤ 1`.  Rebuilding `Zeta23/PrimeSideA/`, `Zeta23/PrimeSideB/`
and `Zeta23/ThmD/Traces.lean` with the saturated kernel and the new pole/tail/zero-mode accounting is
a development of the same order as the base repository, and its analytic content — evaluating the
singular-series main term at frequencies `|α| > 1` with the exact kernel `K(t) = min(λ|t|,1)` — is
precisely the new mathematics of the run.  Only that genuinely new part is assumed.

---

## 4. What is **not** assumed

Explicitly proved, not axiomatized (all reported as depending only on the standard three, §1.4):

* the three exact window moments `A = 1031/1200`, `B = 1809683/2400000`,
  `J = 970487502160963/3017889594720000` and the quintic autocorrelation `g(u)`
  (`RH/Zeta85/Window.lean`, by Mathlib interval integration of polynomials);
* the certificate `c_pc = 2227707598259143/2561811364469143 > 20/23`,
  `2 − 1/c_pc = 1893603832049143/2227707598259143 > 17/20`, margin
  `1047470577429/44554151965182860` (`RH/Zeta85/Certificate.lean`);
* `SaturatedWindowCost (143/100) D_pc` (`RH.Zeta85.windowCost_143`);
* the count lemma of `docs/run/01_hybrid_cycle1.md` (1)–(3) and its `C = 23/20 − η` specialization;
* the two-trace ⇒ ε-form derivation (`RH/Zeta85/Transfer.lean`), which routes through the count
  lemma;
* the signed-shift reciprocal lemma (12) of `docs/run/12` §2, with the constant written out, and the
  spacing/multiplicity count behind (13) (`RH/Zeta85/Discharge/SignedShift.lean`);
* every exponent comparison of cycles 3, 4 and 5 (`RH/Zeta85/Discharge/Exponents.lean`);
* the logarithmic-power audit, including the two negative halves showing the budget does **not**
  close (`RH/Zeta85/Discharge/LogBudget.lean`);
* the dyadic → cumulative passage, reused verbatim from `Zeta23.cumulative_of_dyadic`.

The B-3 finite certificate layer also introduces no primitive assumption:

* `QuarticWindowWitnesses.lean` constructs rational-polynomial windows at
  supports `14999/10000` and `19999/10000`, proves their exact saturated
  costs below `1.13434643` and `1.06772567`, and proves the full pointwise
  top-hat caps;
* `TopHatMoments.lean` proves the sharp top-hat scalar and distance-potential
  integrals through degree four, including the determinant-one reduction of
  the original three-dimensional crossing functional and the original
  formula-(21) fourth moment;
* `TrimmedMoment.lean` proves finite weak duality, both global rational
  quartic inequalities, and the fixed arithmetic clearing the frozen
  R-8686 and R-9506 constants under explicit finite bridge data; and
* `R9383ExactEndpoint.lean` replays the rational endgame for the independently
  certified interval which lies strictly below the frozen R-9383 decimal.

The four isolated printers under `comparator/PrintAxioms/` audit every public
B-3 headline.  Each reports only `propext`, `Classical.choice`, and
`Quot.sound`.  These finite results do not assert the A1 pair trace, an R1a
principal block, the R1b Rudnick--Sarnak specialization, or a smooth
top-hat/grid limit.

Phase B-4 also introduces no primitive assumption.  `EtaClosure.lean` proves
the conditional asymmetric single-block exponent algebra and its positive
power margin, then gives a legal depth-three, `j=2` balanced block which the
literal relabel-only construction cannot put at lengths
`T^(1-eta)` and `T^eta`.  It also proves the balanced signed-shift estimate
misses trace scale and that every explicit literal log exponent `C >= 1`
fails.  The exact enlarged convolution identity needed to leave this killed
class remains an unasserted statement in
`docs/audit/eta_gt_half_factorization.md`.

The Phase-C robust stability bridge is likewise proved without a primitive
assumption.  `RobustStability.lean` separates ambient matrix dimension from
the real zero-count scale, proves the exact error term
`2*pTraceErr + 4*traceErr + frobErr + 2*countErr`, and constructs the uniform sorted-head
spectral trim as an explicit `TrimmedMomentInputs` object.  Its residual is
exactly the matrix tail energy divided by the block dimension.  The only
remaining analytic identification at this interface is the list of four
finite spectral-moment equalities; no theorem asserts those equalities.

`RH/Zeta85/Inputs95.lean` adds no primitive declaration.  It fixes the two
proved B-3 profiles in the types of the strict-support families, defines the
full Gram matrix `G`, the finite enlarged-window sum `A`, the tail `E`, and
the distinguished principal block from literal windows and zero sums, and
proves the finite core-plus-edge count and robust block-tail adapter.  Its
Prop-valued structures are an explicit boundary only; there is no instance.

`RH/Zeta85/Discharge/QuarticTransfer.lean` proves the finite dual scaling,
the exact edge coefficient three, the `NII=o(N)` passage, and the strict
R-8686/R-9506 arithmetic.  It obtains R-8657 monotonically from R-8686 and
R-9383 monotonically from R-9506.  `RH/Zeta85/QuarticMain.lean` exposes all
four frozen dyadic and cumulative statements with exactly the four premises
listed in §1.5.  No theorem consumes `PairTraceGrade95` or
`RS1996ZetaInputs`, and no theorem constructs any of the four required
structures; hence these are conditional headlines, not unconditional ones.

The complete bundle has eleven named top-level fields:

| field(s) | exact obligation |
|---|---|
| `pair14999`, `pair19999` | smooth signed pair trace with every logarithmic exponent explicit |
| `trace14999`, `trace19999` | trace and Frobenius limits for the same finite matrix `A` |
| `zeroSide14999`, `zeroSide19999` | actual `A=P+Q` decomposition, rank/trace/index bounds |
| `rs1996` | published smoothed RS Theorem 3.1, `m=1`, in gauge-fixed form |
| `r1a14999`, `r1a19999` | literal windows, grids, aliases, energy allocation, and translated products |
| `r1b14999`, `r1b19999` | complex alias identity at actual `ZIprime` zeros and block-moment limits |

`PairTraceGrade95` does not imply `FullTraceLimits` in the current code, and
`RS1996ZetaInputs` does not imply `BlockMomentLimits`; those derivation
bridges remain separate exact blockers.  The B-1 stability theorem, B-3
window costs, formula-(21) integrals, dual polynomials, and crossing reduction
are proved theorems and are not reintroduced as fields.
