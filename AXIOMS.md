# AXIOMS.md — what the 85 % layer assumes

**Correction, 2026-09-05:** A2 assumes a false predicate, so the legacy
axiom layer is mathematically inconsistent. Set `w = V = 1`, `IV = 0` in
`SignedPairTraceGrade σ`; Chebyshev and a block-pair inequality give
`≫ XH`, contradicting the claimed `O(X log⁻ᴬ T)` for every `σ > 1`.
See the [proof](docs/research/research_20260905.md).
This is an ordinary mathematical refutation, not a new Lean theorem;
the compiled dependency lists below are retained as provenance.

## Table of contents

- [Summary](#summary-table)
- [Toolchain and structure](#toolchain-and-structure)
- [Phase status](#phase-status)
- [1. `#print axioms`](#1-print-axioms)
- [2. Axiom count per rung](#2-axiom-count-per-rung)
- [3. The four axioms, with provenance](#3-the-four-axioms-with-provenance)
- [4. What is not assumed](#4-what-is-not-assumed)

## Summary table

| # | Name | One-line meaning | Status |
|---|---|---|---|
| A1 | `shiu_majorant₂` | Shiu-type majorant for multiplicative functions in progressions | **axiom** (proved for `eta >= 1/4`; open for `eta in (0,1/4)`) |
| A2 | `signedPair_traceGrade_lt_5_4` | Signed aggregate criterion `(AS)` at support `< 5/4` (cycle-4 BBLR route) | **REFUTED mathematically:** conclusion false; BBLR premise already proved |
| A3 | `signedPair_traceGrade_lt_3_2` | Signed aggregate criterion `(AS)` at support `< 3/2` (cycle-5 route) | **FALSE CONCLUSION:** uses the same refuted aggregate predicate |
| A4 | `traceTransfer_saturated` | Trace evaluation with saturated kernel at support `> 1` | **axiom** (proved for `sigma <= 1`; open beyond) |
| D1 | `bblrErrorBound_proved` | BBLR smoothed quadratic divisor sum error bound | **proved in Lean** |
| D2 | `bblrPoissonBlocks_proved` | BBLR Poisson block decomposition | **proved in Lean** |
| W1 | `windowCost_101_proved` | Window cost at support `101/100` | **proved in Lean** |
| W2 | `windowCost_125` | Window cost at support `5/4` | **proved in Lean** |

---

## Toolchain and structure

Toolchain: Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.

The base library `Zeta23/` is **unconditional**: `#print axioms` on each of
its 33 headline theorems reports only `propext`, `Classical.choice`, `Quot.sound` (re-verified --
see `VALIDATION.md` S2).  Nothing under `Zeta23/` imports anything under `RH/`.

`RH/` is the **conditional** layer.  It declares exactly **four** axioms, all in
[`RH/Zeta85/Hypotheses.lean`](RH/Zeta85/Hypotheses.lean): `shiu_majorant₂`,
`signedPair_traceGrade_lt_5_4`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated` (each
stated in S3).  No axiom is declared anywhere else; no `sorry` occurs in `Zeta23/` or `RH/` (the
only `sorry`s are in the trusted challenge files under `comparator/`).

An earlier revision collapsed this list to a single axiom, `shiu_majorant`, asserting the frozen
interface `ShiuMajorant` of `RH/Zeta85/Arith.lean` -- this repository proved that
interface **false**: `RH.Zeta85.not_shiuMajorant_quarter`
(`RH/Zeta85/Discharge/ShiuNoGo.lean`) refutes `ShiuMajorant (1/4)`, because the frozen statement
fixes `T` before quantifying `P`, so a `tau(3^m)`-spike beats any `(log T)^C` bound.  The current
`shiu_majorant₂` asserts the corrected `ShiuMajorant₂` (`RH/Zeta85/ShiuInterface.lean`), correcting
three defects: **D1** -- majorant scale `(log P)^C`, auxiliary `T` removed;
**D2** -- modulus range `q <= P^(1-eta)` (Shiu's own range);
**D3** -- class-uniform constants.
D1 and D2 are what the refutation exploits; D3 is a faithfulness correction (Shiu's published
theorem has implied constants depending only on the majorant class).  `ShiuNoGo` remains as the
proved refutation of the *old* interface.

**How much of `shiu_majorant₂` is now proved.**  `RH/Zeta85/Shiu/MajorantQuarter.lean` proves
`ShiuMajorant₂ eta` for **every `eta >= 1/4`** (`shiuMajorant₂_of_quarter_le`), unconditionally
via the Landreau/Lay route, gated by `comparator/PrintAxioms/ShiuMajorantQuarter.lean` (CI-checked).
`ShiuMajorant₂` is *antitone* in `eta`, so this does **not** discharge the axiom (asserted for all
`eta in (0, 1/2)`): the interval `eta in (0, 1/4)` remains assumed.  The proved range covers the
exponent the 85 % run exercises (`eta' = 43/93 ~ 0.462`).  A true majorant is necessary but not
sufficient for rung 3: `Discharge/LogBudget.lean` (`verdict_all`) needs `C < 2` where this route
gives `C = 2^{7k}`; see also `Discharge/ActualScaleBBLR.lean`.

---

## Phase status

### Phases 0b/0d

**Verdict: no change to axioms or rung status; CI now gates axiom output.**

Phase 0b added archived 95/100 analysis material only.  Phase C defines a Prop-valued `Inputs95`
boundary and proves conditional quartic transfer, but constructs no analytic instance.  The legacy
rung graph (SS1.1--1.3) is unchanged; quartic headlines are audited in S1.5.  Claims in ingested
files remain evidence, not assumptions; `docs/run/100/FINAL_100_RESULT.md` is withdrawn.
Phase 0d runs `verify/check_axioms.sh` on every push/PR, extracting SS1.1--1.3, diffing against
fresh `comparator/PrintAxioms/Zeta85.lean` output, and running all four base `PrintAxioms` files.
Changing a rung's dependency list without updating this audit fails CI.

### Phase A1.1

**Verdict: no change to axioms or rung status.**

Kills only the method class "published \(d_4\) progression mean value + residue norm +
absolute/Cauchy modulus aggregation"; does not discharge `signedPair_traceGrade_lt_3_2`.  The
remaining statement is the signed cross-residue progression estimate `(EDB)` and its blockwise
main-term identity (see `docs/audit/log_budget_routes.md`, Route 5).

### Phase A1.2 and associated discharge audits

**Verdict: no change to any compiled dependency. `signedPair_traceGrade_lt_3_2` remains unchanged throughout.**

Recombining prime scales before absolute values would close only for \(C<2\); the currently forced
\(C\ge3\) misses the trace budget by at least one logarithm.
`LogBudget.blockwise_triangle_sharp` constructs aligned errors saturating every bound.  The
surviving input is the coefficient-sensitive \(o(T(\log T)^2)\) estimate (14) in
`docs/audit/log_budget_routes.md`.  The repository constructs an exact depth-four Heath--Brown
expansion, arbitrary factor groupings, divisor-split candidates, and a shared
\((j,d,\ell,p,q)\) address with reduced-residue centering, but centering alone does not identify
BBLR's \(\ell=0\) gcd-weighted integral main term.

All discharge modules below introduce no premise; none changes an axiom or rung status.

**HBDepthFour** -- Proves exact remainder \(\Lambda-H_{4,Z}=(\mu-\mu_Z)^4*\zeta^3*\log\) and the
4-term identity (coefficients \(4,-6,4,-1\)) for \(n\le Z^4\) with eight literal factors.  Builds
\(d_1d_2=d_3d_4=d\) coefficient sums with exact triangle majorants; defines finite
nonzero-frequency candidate before absolute values.  Floor blocks are not a source partition; all-class
and reduced-class means provably differ (exact countermodels); reduced centering alone cannot imply
`SingularSeriesCentering`.  Centered cells sum to zero for signed four-component candidate.  Asserts
no estimate; \(\ell=0\) main term and singular-series recombination remain unconstructed.

**BBLRGCDAllocation** -- Proves gcd allocation \(d_1=\gcd(A_0,d)\), \(d_2=d/d_1\) equivalence with
filtered splits, coprimality \((am,bn)=1\), collapsed coefficients, original-fiber kernel sum.
Unit-weight regression at \(d=p=2\): 3 vs 4 terms.  Does not construct smooth HB grouping or
\(\ell=0\) recombination.

**HBToBBLRSmoothGrouping** -- Kills fixed asymmetric literal-slot grouping.  Legal \(j=1\) block
\((43/200,43/200,2/5,3/5)\): total exponent \(143/100\), outer \(43/100\), smooth slots \(2/5,3/5\).
Left-target gap exactly \(1/10\), all right gaps \(\ge 33/100\): no \(T^{o(1)}\) cushion yields
prescribed pairs.  Collapsing two coefficient-one slots gives \(\zeta*\zeta\), not a literal smooth
slot.  Leaves open actual-scale all-block estimate and higher-dimensional divisor theorem.

**ActualScaleBBLR** -- Audits surviving \((2/5,3/5)\) block.  Direct BBLR Prop 3.1: exponents
\(179/100\) and \(161/100\), exceeding trace by \(9/25\) and \(9/50\).  Run-12 progression majorant at
\(d=1\), \(P=Q=T^{83/100}\): \(PQ\) excess \(23/100\), \(PH\) saving \(17/100\); Fourier scale
\(T^{-23/100}\) exactly offset by \(T^{23/100}\) cutoff.  Kills two positive-majorant classes only.

**PreMajorantDI** -- Direct Drappeau one-shot: exponent \(179/100\), excess \(9/25\).  Literal
Pascadi map (\(r=a\)) structurally inapplicable: completion puts \(\bar a\) in first Kloosterman
argument; zero frequency outside dyadic variable.  Pascadi exponent substitution is conditional
arithmetic.  Source-faithful \((q,a)\)-reindex with zero-frequency term remains open.

**FourMuKloosterman** -- On four-Mobius-slot block: exact fixed-modulus/sqrt/triangle output
\(381/200\), misses target by \(49/200\).  Unproved candidate `(SQ4-HB)` at
\(149/100+\varepsilon\): two long log slots contribute \((\log T)^2\), normalized exponent 0; a proved
estimate would close at \(C=0\) with margin \(17/100\), but none is declared.  Smooth partition
identifying every HB block with four-slot block is absent.  Elementary non-primality theorem has
the smaller dependency set `[propext, Quot.sound]`, preserved by CI.

**SQ4SimultaneousRoutes** -- Kills six classes: char large sieve (\(58/25\)); norm chain
(\(381/200\)); additive large sieve (\(199/100\)); reciprocal Kuznetsov and moving-index divisor
switch (both structurally inapplicable); reciprocity+Poisson+Weil+triangle
(\(467/200+\eta+\varepsilon\)).  Poisson zero mode safe at \(149/100+\varepsilon\) but does not prove
`(SQ4-HB)`.  All routes: normalized log exponent 0, raw slots \((\log T)^2\).  Survivor: family (33)
in `docs/audit/sq4_simultaneous_routes.md`.

**SQ4GaussSquareTransform** -- Proves exact finite multiplicative transform: inverse-char Fourier of
\(S(k\bar v,r;q)\) = product of two shifted Gauss sums (all positive moduli including composite);
Dirichlet-char inversion proved.  Unit specialization to \(\chi(kr)^{-1}G_q(\chi;1)^2\) requires both
shifted args to be units.  CRT/conductor algebra discharged below.  Pre-completion target:
\(T^{48/25+\varepsilon}(\log T)^0\); this estimate and smooth source identification remain unproved.

**SQ4CRTConductor** -- Proves coprime CRT factorization (complementary twists, arbitrary shifts).
Primitive \(\chi^*\) mod \(f\), `changeLevel` to \(q=f\ell\): formal imprimitive formula
\(G_q(\chi;t)=G_f(\chi^*;1)\sum_{s\mid(\ell,t)}\mu(\ell/s)\chi^*(\ell/s)s\,\overline{\chi^*(t/s)}\)
with zero extension removing \((\ell/s,f)>1\) terms.  Also proves divisor-\(d\) form, conjugation
phase, conductor support, complementary reindex.  For squarefree \(u_1,u_2\):
\(u_1u_2=g^2ab\), Mobius sign cancellation, obstruction \(\mathbb Z/4\not\simeq\mathbb Z/2\times\mathbb Z/2\).
Shared prime stays coupled: four Mobius slots do not factor into local polynomials.  Survivor:
\(\lvert\mathfrak M_4\rvert\ll T^{48/25+\varepsilon}(\log T)^0\) + smooth bridge; neither proved nor assumed.

**SQ4CorrelatedMoment** -- Exact exponent/log bookkeeping.  Coeff-blind Cauchy: \(199/100\); ideal
\((k,r)\)-sqrt at fixed \((p,v)\): \(179/100\); both miss.  Blomer--Pascadi Thm 5.5 (July 2026
**preprint**): literal at fixed \((p,v)\) gives \(4111/1800\) after outer triangle.  KSWX Type-I:
\(421/200\) under favourable grants only.  Pascadi Cor 5.11: \(513/200\) after squarefree-\(v\)
Ramanujan lift; \(47/20\) conditional on unstated variant; nonsquarefree strata outside lift.
Method-class verdicts only.  Log exponents: coeff-blind/fixed/BP/KSWX: 0/2; literal/favourable
Pascadi: 1/3 and 2/4.

**SQ4PublishedLiterature** -- Normalizes to target \(48/25\).  Shparlinski 2019 Thm 2.1: \(2071/800\)
under favourable grants.  Thm 2.2 good part: \(1017/400+\varepsilon\), exceptional mass
uncontrolled.  Other classes: power gap or source mismatch.  No published theorem found with
literal LHS = full source moment (not universal nonexistence).

### B-2 Rudnick--Sarnak audit

**Verdict: no change to compiled headline dependency.**

`RS1996ZetaInputs.theorem31` records published smoothed Thm 3.1 (\(m=1\), gauge-fixed zero-sum test,
multiplicities, strict support below two, \(O(T)\) error), deliberately separate from
`BlockMomentLimits`.  No instance constructed.
`RSReduction.lean` discharges the deterministic finite part: pairings for \(k=1,2,3,4\) as
\(0,1,3,6+3\), zero-sum contraction vectors, machine-checked binomial centering (formula 27 to 18),
top-hat specialization to formula (21).  Does not identify `rsMainTerm` with contractions or actual blocks.
`RSBlockMomentBridge.lean` proves the actual-matrix centering adapter: normalized trace of
\((\operatorname{block}(T)-I)^k\) = binomial transform of uncentered traces for the literal block
through degree four.  With `UncenteredRSBlockLimits F` (degrees 0--4), gives centered formula-(21)
limits.  Degree-zero clause retains positive-dimension obligation; final constructor needs two
complex-alias clauses.  Does not derive raw limits from published RS, construct R1a, or discharge
`BlockMomentLimits`.

### Phase B-1

**Verdict: discharged without an input field; no new axiom.**

`RH/Zeta85/Stability.lean` proves the exact quartic stability bound, its isometric- and principal-compression
forms from finite-dimensional hypotheses alone.  CI audit `comparator/PrintAxioms/Stability.lean`
checks the standard dependency set.

### Phase A1.3

**Verdict: no change to headline dependency.**

One-shot class \(\mathcal W_1\) killed: independent progression cells admit a phase-aligned
countermodel; fixed-modulus Weil misses by \(T^{9/50}\); Bettin--Chandee and BBLR miss by fixed
powers.  Coefficient-sensitive `(WG-HB)` would close with saving \(7/400\), but repository lacks
proved source identification of every signed depth-four block with BBLR outer sequences and inner
smooth weights, plus Fourier kernel estimates, \(\ell=0\) formula, and signed Ramanujan evaluation.
Canonical gcd allocation proved; sharp coefficient object and centering do not supply remaining equalities.

### Phase A2.1

**Verdict: no change to compiled dependency. Quartic rungs remain conditional.**

Cycle-3 power-complementary identity impossible in exact finite PB/TDAC class: after removing alias-free
distinguished window (positive residual on every fiber), complement needs rank \(N\) but cycle-3
count gives at most \(N-n_0\).  Certified rational-interval evaluation verifies positive residual
for file-15, R-8686, R-9506 symbols.
`AliasRankObstruction.lean` proves: each residue channel has rank at most its count, nonvanishing
diagonal residual has full rank, three terminal count budgets are deficient (prints standard three
only).  Transcendental nonvanishing for two terminal Euler profiles certified by
`verify/a2_1_tdac_rank.py`.  `PrincipalCyclicBlock` names exact replacement obligation (literal
windows, grids, energy reconstruction, mean-one profile, translated-product limits); no instance
constructed.

### Phase A2.2

**Verdict: no change to headline dependency.**

In base hat normalization, terminal cap \(r\leq V_\sigma\) omits required factor \(\sigma\); quadratic
profile \(\sup V_\sigma=1200/1031<143/100\), so no mean-one block in stated class.  For honest block,
positive rational five-atom law matches paper-derived closed moments through degree four below
\(Y=\sigma-1\), giving sharp corrected tail zero.
`AliasFallback.lean` verifies rational moment reconstruction, weight positivity, support
inequalities, scaling identity, zero tails.  Equality with Mathlib integrals and RS specialization
unformalized.  All headlines print `[propext, Classical.choice, Quot.sound]`.

### Terminal R1a status

**Verdict: `PrincipalCyclicBlock` formally uninhabited for both frozen families.**

`R1aAllocationCapacity.lean` + `R1aAllocationNoGo.lean` prove `not PrincipalCyclicBlock F` for
`Family14999` and `Family19999`, using only current energy reconstruction, distinguished-period/energy-ratio
normalization, degree-one translated-product limit, and window integrability (no common lattice,
alias cancellation, grid count, or block dimension assumed).  Quartic implications retain their
statements and four premises, but one premise is uninhabited per frozen family.  No valid
construction exists; a new route must change at least one consumed semantic and rederive adapters.

---

## 1. `#print axioms`

### 1.1--1.3 Headline rung dependencies

Every theorem also depends on the standard three (`propext`, `Classical.choice`, `Quot.sound`);
the column below shows only additional research axioms.

| Rung | Lean theorem name | Additional axioms beyond standard 3 |
|---|---|---|
| 0.679 (101/100) | `zeta85_rung_support_101_over_100` | `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated` |
| 0.679 (101/100) | `zeta85_rung_support_101_over_100_cumulative` | (same) |
| 0.797 (5/4) | `zeta85_rung_support_5_over_4` | `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated` |
| 0.797 (5/4) | `zeta85_rung_support_5_over_4_cumulative` | (same) |
| 0.85 (143/100) | `zeta85_simple_on_critical_line` | `shiu_majorant₂`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated` |
| 0.85 (143/100) | `zeta85_simple_on_critical_line_cumulative` | (same) |
| 0.85 (143/100) | `zeta85_eighty_five_percent` | (same as above) |
| 0.85 (143/100) | `zeta85_eighty_five_percent_cumulative` | (same) |

The `RH.Zeta85.rung*` / `RH.Zeta85.eightyFive*` solution-side names are identical.
Full verbatim output is reproduced by `lake env lean comparator/PrintAxioms/Zeta85.lean` and checked by CI via `verify/check_axioms.sh`.

### 1.4 What is proved outright inside the conditional layer

The list below comes from the isolated `comparator/PrintAxioms/` printers in `verify/check_axioms.sh`.
It is **not** exhaustive: the four proved discharges of S3 (`bblrErrorBound_proved`,
`bblrPoissonBlocks_proved`, `Window101.windowCost_101_proved`, `RationalWindow125.windowCost_125`)
and the refutation `not_shiuMajorant_quarter` have no dedicated printer.

**All 289 theorems below depend only on `[propext, Classical.choice, Quot.sound]`.**
They are listed by module (all under `RH.Zeta85`).  Printer-by-printer scope (what each group
proves and what it does not assert) is covered in the Phase Status section above and S4 below.

*Root* (15): `windowCost_143`, `jSat_eq`, `cPC_eq`, `count_lemma`, `epsForm_of_twoTraceCert`, `stability_inequality`, `tailExcessSq_isometricCompression_le`, `tailExcessSq_principalCompression_le`, `stability_inequality_isometricCompression`, `stability_inequality_principalCompression`, `stability_prebound`, `profileSaturatedCost_v8686`, `profileSaturatedCost_v9506`, `core_count_le_dyadic_add_edge`, `robustBlockTailBound_eventually`

*SignedShift* (5): `shiftSum_decay`, `sum_over_separated`, `nearInt_int_div`, `four_nearInt_le_norm_cexp_sub_one`, `bdiffIter_le`

*LogBudget* (14): `budget_fails`, `budget_primeDyadic_fails`, `budget_dyadic_fails`, `verdict_all`, `depth_three_excess`, `depth_four_margin`, `fixed_modulus_weil_excess`, `wg_hb_candidate_saving`, `wg_hb_net_saving`, `bettin_chandee_excess`, `bblr_endpoint_first_excess`, `blomer_pascadi_range_excess`, `mqw_range_excesses`, `power_beats_log`

*Exponents* (1): `bblr_blackbox_ceiling`

*QuarticWindowWitnesses* (2): `windowCost_14999`, `windowCost_19999`

*TopHatMoments* (5): `formula21M2Integral_eq`, `formula21M3Integral_eq`, `formula21M4ReducedIntegral_eq`, `crossingReduction`, `formula21M4Integral_eq`

*TrimmedMoment* (3): `finite_trimmed_quartic_dual`, `Terminal9506.density_gt_frozen`, `Terminal8686.density_gt_frozen`

*R9383ExactEndpoint* (1): `endpoint_box_separation`

*R1aAllocationCapacity* (5): `v8686_active_le_center`, `v9506_active_le_center`, `no_finite_capacity_configuration`, `family14999_capacity_gap`, `family19999_capacity_gap`

*R1aAllocationNoGo* (2): `no_principal14999`, `no_principal19999`

*EtaClosure* (5): `preliminary_with_log_is_o`, `balanced_j2_K3_legal`, `balanced_j2_no_asymmetric_M1`, `balanced_signedShift_misses`, `literal_log_budget_C1_fails`

*EtaSuperpositionObstruction* (12): `convolutionCoeff_eq_zero_of_no_supported_divisor`, `no_prime_sq_divisor_between`, `pointIndicator_convolution_sq`, `no_primePointModel_finiteSuperposition`, `no_short_box_divisor`, `convolutionCoeff_899_eq_zero`, `finiteSuperposition_899_eq_zero`, `balancedBoxModelCoeff_899`, `no_balancedBoxModel_finiteSuperposition`, `balanced_progression_PQ_excess`, `balanced_progression_PH_excess`, `balanced_progression_requires_cancellation`

*RobustStability* (6): `robust_stability_inequality`, `robust_stability_inequality_withCountError`, `robust_stability_inequality_principalCompression`, `robust_stability_inequality_principalCompression_withCountError`, `spectral_residualTail_eq_tailExcessSq_div`, `principal_spectral_headTrimmedMomentInputs_of_moments`

*QuarticGramFamily* (1): `G_eq_A_add_E`

*StableZeroSide* (1): `block_isHermitian`

*RSReduction* (9): `weightedCyclicSymbol_zero`, `rsPairVector_sum`, `rsMainTerm_k1`, `rsMainTerm_k2`, `rsMainTerm_k3`, `rsMainTerm_k4`, `centeredContraction_eq_formula18`, `topHat_formula18_eq_formula21`, `topHat_centeredContraction_eq_formula21`

*RSBlockMomentBridge* (3): `centeredBlockMoment_eq_centeredTransform`, `centered_moment_limits`, `blockMomentLimits_of_uncenteredRS`

*RSPairIntegrals* (51): `integral_abs_mul_shift_div`, `distanceIntegral_comm`, `onePairCoordinateIntegral_eq`, `onePairIntegrand_integrable_of_continuous_compact`, `distanceKernel_integrable_of_continuous_compact`, `rsPairIntegral_one_eq_coordinate`, `rsPairIntegral_one_eq_distance`, `integral_fin_two`, `rsPairIntegral_two_eq_coordinate`, `rsPairIntegral_k2_distance`, `rsPairIntegral_k3_01_distance`, `rsPairIntegral_k3_02_distance`, `rsPairIntegral_k3_12_distance`, `weightedCyclicSymbol_k4_01`, `weightedCyclicSymbol_k4_02`, `weightedCyclicSymbol_k4_03`, `weightedCyclicSymbol_k4_12`, `weightedCyclicSymbol_k4_13`, `weightedCyclicSymbol_k4_23`, `rsPairIntegral_k4_01_distance`, `rsPairIntegral_k4_02_distance`, `rsPairIntegral_k4_03_distance`, `rsPairIntegral_k4_12_distance`, `rsPairIntegral_k4_13_distance`, `rsPairIntegral_k4_23_distance`, `normalized_k4_onePairSum`, `weightedCyclicSymbol_k4_separated`, `weightedCyclicSymbol_k4_nested`, `weightedCyclicSymbol_k4_crossing`, `rsPairIntegral_k4_separated_coordinate`, `rsPairIntegral_k4_nested_coordinate`, `rsPairIntegral_k4_crossing_coordinate`, `separatedTwoPairSection_eq`, `separatedTwoPairCoordinateIntegral_eq`, `nestedTwoPairSection_eq`, `nestedTwoPairCoordinateIntegral_eq`, `crossingTwoPairCoordinateIntegral_eq`, `separatedTwoPairFubiniKernel_integrable_of_continuous_compact`, `nestedTwoPairFubiniKernel_integrable_of_continuous_compact`, `crossingRawKernel_integrable_of_continuous_compact`, `nestedDistanceKernel_integrable_of_continuous_compact`, `rsPairIntegral_k4_separated_eq`, `rsPairIntegral_k4_nested_eq`, `rsPairIntegral_k4_crossing_eq`, `normalizedRSMainTerm_k1`, `normalizedRSMainTerm_k2`, `normalizedRSMainTerm_k3`, `normalizedRSMainTerm_k4`, `normalizedRSMainTerm_k2_of_continuous_compactSupport`, `normalizedRSMainTerm_k3_of_continuous_compactSupport`, `normalizedRSMainTerm_k4_of_continuous_compactSupport`

*BBLRGCDAllocation* (5): `sum_splitFiber_eq_divisorsAntidiagonal`, `collapsedCoeff_eq_divisorSum`, `collapsedCoeff_two_two_unit`, `rawCollapsedCoeff_two_two_unit`, `collapsedKernelSum_eq_originalFibers`

*HBToBBLRSmoothGrouping* (15): `hb_component_one_inventory`, `hb_component_one_scalar`, `muCut_ne_coefficientOne`, `bblr_allocation_preserves_supplied_smooth`, `terminal_component_one_legal`, `left_literal_gap`, `right_short_literal_gap`, `right_long_literal_gap`, `no_left_literal_grouping`, `no_right_literal_grouping`, `no_asymmetric_literal_grouping`, `twoUnitSlotMultiplicity_two`, `twoUnitSlotMultiplicity_four`, `two_unit_slot_collapse_not_constant`, `zeta_sq_eq_twoUnitSlotMultiplicity`

*ActualScaleBBLR* (13): `block_geometry_exact`, `blackBox_exponents_exact`, `blackBoxAB_excess`, `blackBoxWatt_excess`, `blackBox_not_traceGrade`, `blackBox_not_traceGrade_with_slack`, `source_fourier_exponents_exact`, `source_lengths_exact`, `progression_majorant_is_PQ`, `progressionPQ_excess`, `progressionPH_saving`, `progression_majorant_not_traceGrade`, `taylor_H_sq_saving`

*PreMajorantDI* (15): `source_scales_exact`, `collapsed_coefficient_L2_exact`, `drappeau_K_squared_terms_exact`, `drappeau_K_exact`, `drappeau_route_exact`, `zmod_five_literal_outer_mismatch`, `pascadi_completion_exact`, `pascadi_components_exact`, `pascadi_theta_inactive`, `pascadi_rational_factor_exact`, `pascadi_candidate_arithmetic_exact`, `pascadi_candidate_arithmetic_matches_direct`, `drappeau_oneShot_excess_exact`, `drappeau_oneShot_not_traceGrade`, `drappeau_oneShot_not_traceGrade_with_slack`

*SQ4SimultaneousRoutes* (13): `source_scales_exact`, `character_large_sieve_output_exact`, `character_large_sieve_integrated_excess_exact`, `norm_only_output_exact`, `norm_only_integrated_excess_exact`, `additive_large_sieve_output_exact`, `additive_large_sieve_integrated_excess_exact`, `reciprocal_profile_scales_exact`, `reciprocal_poisson_scales_exact`, `poisson_zero_mode_integrated_exact`, `poisson_weil_triangle_output_exact`, `poisson_weil_triangle_integrated_excess_exact`, `route_log_exponents_exact`

*SQ4GaussSquareTransform* (6): `correlation_transform_factorization`, `kloosterman_transform_eq_gauss_product`, `unitGaussSum_unit_scale`, `kloosterman_transform_eq_gauss_square`, `dirichlet_fourier_inversion`, `kloosterman_kernel_character_inversion`

*SQ4CRTConductor* (31): `unitGaussSum_prod`, `crt_unitCharacter_factor`, `crt_addChar_factor`, `unitGaussSum_crt`, `gauss_product_crt`, `unitGaussSum_eq_gaussSum`, `factorsThrough_of_unitGaussSum_ne_zero`, `conductor_dvd_of_unitGaussSum_ne_zero`, `standard_shift_killed`, `conductor_dvd_quotient_gcd_of_unitGaussSum_ne_zero`, `conductor_dvd_gcd_of_gauss_product_ne_zero`, `conductor_dvd_quotient_gcd_of_residue_gauss_ne_zero`, `conductor_dvd_gcd_of_residue_gauss_product_ne_zero`, `primitive_nonunit_shift_vanishes`, `sum_stdAddChar_shift`, `periodicSum_eq`, `induced_apply_eq_coprime_indicator`, `coprime_indicator_eq_moebius_sum`, `mobius_coprime_weighted_sum`, `stdAddChar_cancel_divisor`, `stdAddChar_cancel_divisor_of_dvd`, `sum_divisors_complement`, `gaussSum_changeLevel_eq_conductor_formula`, `gaussSum_changeLevel_eq_conductor_formula_conj`, `gaussSum_changeLevel_eq_conductor_formula_s`, `unitGaussSum_changeLevel_eq_conductor_formula_conj`, `unitGaussSum_changeLevel_eq_conductor_formula_s`, `squarefree_gcd_decomposition`, `moebius_pair_shared_gcd_cancellation`, `shared_moebius_prime_counterexample`, `zmod_four_not_crt_two_two`

*SQ4CorrelatedMoment* (15): `source_scales_exact`, `character_norms_exact`, `character_cauchy_output_exact`, `character_cauchy_integrated_exact`, `fixed_pv_square_root_output_exact`, `blomer_pascadi_fixed_pv_terms_exact`, `blomer_pascadi_fixed_pv_output_exact`, `kswx_type_i_delta_terms_exact`, `kswx_type_i_output_exact`, `pascadi_parameters_exact`, `pascadi_geometry_exact`, `pascadi_lifted_output_exact`, `pascadi_lifted_integrated_exact`, `literal_cor511_output_exact`, `correlated_route_log_exponents_exact`

*SQ4PublishedLiterature* (6): `precompletion_target_exact`, `existing_benchmark_precompletion_exact`, `shparlinski19_t21_terms_exact`, `shparlinski19_t22_good_part_exact`, `other_precompletion_outputs_exact`, `audited_log_exponents_exact`

*HBDepthFour* (29): `hbComponent_factorization`, `sum_hbComponent`, `hbAtom_product`, `hbGrouped_factorization`, `empty_singleton_groupings_distinct`, `abs_muCut_le_one`, `muCut_tail_four_zero`, `inDyadicBlock_iff_log_eq`, `sum_dyadicPart_apply`, `reducedCoeff_eq_convolution`, `abs_reducedCoeff_le`, `abs_splitCoeff_le`, `localizedSplitCoeff_support`, `abs_localizedSplitCoeff_le`, `plannedLeftBlockCoeff_support`, `plannedRightBlockCoeff_support`, `abs_plannedLeftBlockCoeff_le`, `abs_plannedRightBlockCoeff_le`, `sum_centeredProgressionCell`, `sum_reducedCenteredProgressionCell`, `sum_plannedLeftReducedCenteredCell`, `sum_plannedLeftSignedReducedCenteredCell`, `allClass_zeroMode_ne_reduced_zeroMode`, `reducedCentering_alone_not_sufficient`, `singularSeriesCentering_iff_error_zero`, `zeta_mul_injective`, `hb4_remainder`, `hb4_eq_vonMangoldt`, `sum_hbComponent_eq_vonMangoldt`

### 1.5 Conditional quartic headlines

`comparator/PrintAxioms/QuarticMain.lean` prints the eight final theorem names: `rung8657`,
`rung8657_cumulative`, `rung8686`, `rung8686_cumulative`, `rung9383`, `rung9383_cumulative`,
`rung9506`, `rung9506_cumulative`.  All depend only on `[propext, Classical.choice, Quot.sound]`.

This standard-three output means the transfer and assembly add no Lean axiom.  It does **not** make
the results unconditional: every theorem takes `FullTraceLimits`, `StableZeroSide`,
`PrincipalCyclicBlock`, and `BlockMomentLimits` for its support family.  The allocation no-go proves
`PrincipalCyclicBlock` is uninhabited for both families, so these are valid implications with no
valid current-interface construction.  The 21 public transfer theorems in
`comparator/PrintAxioms/QuarticTransfer.lean` have the same output.  Independent replay:

```text
dc99b510fdf1966f11535bf57a3dc53f4056c679e0275c8a649c01facf5f3bdf  verify/quartic_transfer.py
05615d7eb1727532cb81a5c04598630ebd9c29408b729770d34e4b282b533cce  verify/quartic_transfer.out
```

---

## 2. Axiom count per rung

This section maps each rung to its axiom set, showing how dependency grows with the target constant.

| rung | constant | axioms it depends on | count |
|---|---|---:|---:|
| base (Zeta23, Theorem D) | 2 - 1/c1* = 0.6725007... | -- | **0** |
| 1 | 0.67924886307 | `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated` | **2** |
| 2 | 0.79721415286134 | `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated` | **2** |
| 3 | 1893603832049143/2227707598259143 = 0.8500235101... | `shiu_majorant₂`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated` | **3** |

The quartic headlines use no declared research axiom, but each is conditional on four structures:

| rungs | family | explicit structure premises | research axioms | unconditional? |
|---|---|---|---:|---|
| R-8657, R-8686 | `Family14999` | `FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, `BlockMomentLimits` | **0** | no |
| R-9383, R-9506 | `Family19999` | (same four structures) | **0** | no |

**Historical note -- the removed contradiction.**  An intermediate revision replaced axioms 2--4 by
theorems from a `False` pivot: with `shiu_majorant` and the refutation both in scope,
`shiu_interface_contradiction : False` was derivable and eight headlines were `False.elim`s --
formally checked but vacuous.  That pivot and all vacuous headlines have been **removed**.

The counts are close, but the **contents are disjoint**:

* rungs 1--2 use `eta < 1/4` block closure (BBLR premise proved, error *power*-saving); they do
  **not** use `shiu_majorant₂` or `signedPair_traceGrade_lt_3_2`;
* rung 3 uses the cycle-5 route (only *polylog*-saving, needs Shiu majorant, log budget does not
  close -- see S3 Axiom 3 and `FINDINGS.md` S7);
* the only shared axiom is `traceTransfer_saturated`.  Both BBLR interfaces and all three window
  costs are proved.

---

## 3. The four axioms, with provenance

Full docstrings are in [`RH/Zeta85/Hypotheses.lean`](RH/Zeta85/Hypotheses.lean); condensed here.
No axiom lacks a source.

### Proved discharge -- `bblr_error_bound : BBLRErrorBound`

*Status:* **PROVED IN LEAN** by `RH.Zeta85.bblrErrorBound_proved`.

*Statement.*  For `A, B, M1, M2, N1, N2, H >= 1` with smooth weights in `(1,2)` and standard decay,
the smoothly `h`-averaged quadratic divisor sum `S+` splits as `S+ = M + E`, with
`E <<_eps (ABMNH^2)^{1/4+eps}*(AB + H^{1/4}(A+B)^{1/2}(ABMN)^{1/8})`.
**First bracket factor is `AB`, not `(AB)^{1/2}`** -- see `FINDINGS.md` S3.

*Lean construction.*  Lean chooses the complete finite `bblrSum` as `Mterm`, making the error zero.
Published error factor is nonneg on `BBLRHyps`, so bound holds with `Keps = 1`.

### Proved discharge -- `bblr_poisson_blocks : BBLRPoissonBlocks`

*Status:* **PROVED IN LEAN** by `RH.Zeta85.bblrPoissonBlocks_proved`.

*Statement.*  Poisson summation presents the nonzero-frequency part as blocks `R_d` with
`P_d ~ AM1/d`, `Q_d ~ BN1/d`, `H_d = H/d`, kernel decay `<<_J d(1+|l|d)^{-J}(log T)^{C_J}`,
and per-block bound `|R_d| << P_d(Q_d + H_d)(1+d)^{-2}(log T)^C`.

*Lean construction.*  Lean chooses `bblrSum` as `Mterm`, sets `Dmax = 0`, assigns zero to every
block.  Decomposition becomes `S = S + 0`; block estimate is vacuous (`Icc 1 0` empty).

### Axiom 1 -- `shiu_majorant₂`

*Status:* **[RUN CLAIM: `docs/run/12` S2, equation (14), undischarged]**; source: P. Shiu, J. Reine
Angew. Math. 313 (1980) 161--170.

*Statement* (`ShiuMajorant₂ eta`).  For every divisor-bound class `(Kc, k)` there are class-uniform
`C, K, P1` such that for `P >= P1`, every `c` divisor-bounded in that class, and every reduced
`r mod q` with `q <= P^(1-eta)`:
`Sum_{p ~ P, p = r (q)} |c_p| <= K*(P/phi(q))*(log P)^C`.

*Corrected interface.*  Frozen `ShiuMajorant` is **refuted** by `not_shiuMajorant_quarter`; intro
records corrections D1--D3.  Whether cycle-5 needs this exact form is not formalized: the consumer
axiom asserts its hypothesis.

*Why not discharged.*  Shiu's theorem is not in Mathlib; its hypotheses (non-negative multiplicative
majorant) do not apply to the run's signed Mobius/smooth convolutions.  The reduction presupposes
the unformalized Heath--Brown coefficient factorization.

### Axiom 2 -- `signedPair_traceGrade_lt_5_4`

*Status:* **[RUN CLAIM: `docs/run/08` S2, undischarged]**.

*Statement.*  At `eta = 1/4 - kappa`, a depth-`K` Heath--Brown identity splits every block into
(i) Type-I handled by Poisson + hybrid large sieve, and (ii) terminal BBLR block; feeding (ii) into
the proved error interface gives power-saving, so `(AS)` holds for `1 < sigma < 5/4`.

*Why not discharged.*  (i) HB identity and grouping dichotomy not in Mathlib; (ii) Type-I needs
uniform Poisson + hybrid large sieve; (iii) "no third block" requires (i).  Discharged: all exponent
bookkeeping and `power_beats_log`.

### Axiom 3 -- `signedPair_traceGrade_lt_3_2`

*Status:* **[RUN CLAIM: `docs/run/12` eqs. (2) and S5, undischarged -- AND not established by the
run]**.  Single most load-bearing undischarged statement.

*Statement.*  `R_HB << (T^{1+eta} + T^{1/2+2eta})(log T)^C` for fixed `0 < eta < 1/2`;
consequently `(AS)` holds for `1 < sigma < 3/2`.

*Why not discharged -- two reasons.*

1. Derivation needs proved block interface, Axiom 1, and HB recombination.  Discharged: signed-shift
   lemma (12)--(13) and exponent comparisons (18)--(19).
2. **Even granting (2), it does not imply `(AS)`.**  `(AS)` demands `<<_A X(log X)^{-A}`; (2) gives
   `(log T)^{+C}`.  Audit in `LogBudget.lean`: free room is `(log T)^{<2}` (single-block),
   `(log T)^{<1}` (Y-dyadic), `(log T)^{<0}` (fully dyadicized); forced depth `K >= 4` gives
   `C >= 3`.  All three thresholds fail (`verdict_all`).  See `FINDINGS.md` S7.
   Target **not** weakened: stays `1893603832049143/2227707598259143`.

### Proved discharge -- `windowCost_101`

*Status:* **PROVED IN LEAN** by `RH.Zeta85.Window101.windowCost_101_proved`.

Exact degree-six rational profile, strictly positive on window; Lean computes area, square integral,
saturated autocorrelation.  Cost defect changes sign between `d=0` and `d=1/100000`; IVT supplies
the exact frozen target.

### Proved discharge -- `windowCost_125`

*Status:* **PROVED IN LEAN** by `RH.Zeta85.RationalWindow125.windowCost_125`.

At `sigma = 5/4 - 10^{-12}`, degree-thirty polynomial proved nonneg by sixteen Bernstein
coefficients; unit mass, exact square integral, degree-sixty autocorrelation proved coefficient-by-coefficient.  Algebraic interpolation realizes cost `1.20278584713866 = 2 - 0.79721415286134`.

### Axiom 4 -- `traceTransfer_saturated`

*Status:* **[RUN CLAIM: `docs/run/01` S2, `docs/run/02` S2, `docs/run/12` S5; undischarged for
support > 1 only]**.  The `sigma <= 1` case is **proved** (`Zeta23.ThmD.tracesBoundsD_concrete`).

*Statement.*  Given saturated-kernel cost `D` at `sigma in (1, 3/2)` and `(AS)` at that support,
zeta zeros carry a Gabor family with `4*tr G_hat - ||G_hat||^2_F - 2N - o(N) <= N0_star`,
`tr G_hat = N(1+o(1))`, `||G_hat||^2_F <= (D + o(1))N`.

*What is reused.*  The whole zero side: `seamA_mult2` (no `lambda <= 1` restriction), Poisson identity,
rank-trace inequality, `c=2` multiplicity count, fixed-`T` algebra -- all reused verbatim.

*Why not discharged.*  Past `lambda = 1`, the error `X*log l/(T*l)` with `X = (T/2pi)^lambda` no
longer tends to 0.  Rebuilding the prime-side bookkeeping with the saturated kernel is a same-order
development; its content -- evaluating the singular-series main term at `|alpha| > 1` with
`K(t) = min(lambda|t|,1)` -- is the new mathematics of the run.

---

## 4. What is **not** assumed

Results explicitly proved (not axiomatized), all with standard-three dependencies only (S1.4):

* three exact window moments `A = 1031/1200`, `B = 1809683/2400000`,
  `J = 970487502160963/3017889594720000` and quintic autocorrelation (`RH/Zeta85/Window.lean`);
* certificate `c_pc = 2227707598259143/2561811364469143 > 20/23`,
  `2 - 1/c_pc > 17/20`, margin `1047470577429/44554151965182860` (`Certificate.lean`);
* `SaturatedWindowCost (143/100) D_pc` (`windowCost_143`);
* count lemma of `docs/run/01_hybrid_cycle1.md` (1)--(3) and `C = 23/20 - eta` specialization;
* two-trace => eps-form derivation (`Transfer.lean`) via the count lemma;
* signed-shift reciprocal lemma (12) and spacing/multiplicity count (13) (`SignedShift.lean`);
* every exponent comparison of cycles 3, 4, 5 (`Exponents.lean`);
* logarithmic-power audit including both negative halves showing budget does **not** close
  (`LogBudget.lean`);
* dyadic -> cumulative passage, reused from `Zeta23.cumulative_of_dyadic`.

**B-3 finite certificate layer** (no primitive assumption):
`QuarticWindowWitnesses.lean` constructs windows at supports `14999/10000` and `19999/10000` with
proved costs and pointwise top-hat caps.  `TopHatMoments.lean` proves sharp top-hat integrals through
degree four, including crossing reduction and formula-(21) fourth moment.  `TrimmedMoment.lean`
proves finite weak duality, global rational quartic inequalities, and fixed arithmetic clearing
R-8686/R-9506.  `R9383ExactEndpoint.lean` replays the R-9383 rational endgame.  Four isolated
printers audit every public B-3 headline (standard three only).

**Phase B-4** (no primitive assumption): `EtaClosure.lean` proves conditional asymmetric single-block
exponent algebra with positive power margin; gives a legal depth-three `j=2` balanced block the
literal construction cannot place at `T^{1-eta}` and `T^eta`; proves balanced signed-shift misses
trace scale and `C >= 1` fails.  `EtaSuperpositionObstruction.lean` proves exact finite
support-model obstruction: at `eta = 3/4`, `T = 625`, signed superpositions with first factors in
`[5,10]` vanish at 899, but balanced `[25,50]` box model has coefficient two.  Prime-square theorem
gives scale-free gap.  Does not identify balanced model with actual HB coefficient or disprove
`(EF_eta)`.  Survivor: per-outer-scale `|R_HD| <= C * Y * (log T)^C` with `C < 1` (unasserted).

**Phase-C robust stability bridge** (no primitive assumption): `RobustStability.lean` separates
ambient dimension from zero-count scale, proves exact error term
`2*pTraceErr + 4*traceErr + frobErr + 2*countErr`, constructs sorted-head spectral trim.  Residual
= matrix tail energy / block dimension.  Only remaining: four spectral-moment equalities (unasserted).

`Inputs95.lean` (no new declaration) fixes B-3 profiles, defines `G`, `A`, `E`, distinguished
principal block; proves finite core-plus-edge count and robust adapter.  Structures are boundary
only (no instance).

`QuarticTransfer.lean` proves dual scaling, exact edge coefficient three, `NII=o(N)` passage,
strict R-8686/R-9506 arithmetic; obtains R-8657 from R-8686 and R-9383 from R-9506 monotonically.
`QuarticMain.lean` exposes all four frozen dyadic and cumulative statements with the four S1.5
premises.  No theorem consumes `PairTraceGrade95` or `RS1996ZetaInputs`; no theorem constructs
the required structures: these are conditional headlines.

Complete bundle -- eleven named top-level fields:

| field(s) | exact obligation |
|---|---|
| `pair14999`, `pair19999` | smooth signed pair trace with every log exponent explicit |
| `trace14999`, `trace19999` | trace and Frobenius limits for finite matrix `A` |
| `zeroSide14999`, `zeroSide19999` | actual `A=P+Q` decomposition, rank/trace/index bounds |
| `rs1996` | published smoothed RS Theorem 3.1, `m=1`, gauge-fixed |
| `r1a14999`, `r1a19999` | literal windows, grids, aliases, energy, translated products |
| `r1b14999`, `r1b19999` | complex alias identity at `ZIprime` zeros and block-moment limits |

`PairTraceGrade95` does not imply `FullTraceLimits`; `RS1996ZetaInputs` does not imply
`BlockMomentLimits`; derivation bridges remain exact blockers.  B-1 stability, B-3 window costs,
formula-(21) integrals, dual polynomials, and crossing reduction are proved and not reintroduced.
