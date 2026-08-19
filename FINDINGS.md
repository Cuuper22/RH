# FINDINGS.md — where the run documents were wrong, imprecise, or unprovable as written

Every section below is populated; where a phase produced no failure, the affirmative verification
note is recorded.  Source files are those unpacked into `docs/run/`.

---

## Table of Contents

| # | Section | Status |
|---|---------|--------|
| [1](#1-setup-and-reading-s1s3) | Setup and reading (S1--S3) | [AFFIRMATIVE] |
| [2](#2-phase-a--arithmetic-core) | Phase A -- arithmetic core | [PROVED] |
| [3](#3-the-bblr-error-bound) | The BBLR error bound | [WRONG] |
| [4](#4-the-two-transcendental-window-costs) | The two transcendental window costs | [PROVED] |
| [5](#5-shiu-type-progression-majorant-c3) | Shiu-type progression majorant (C3) | [AXIOM] |
| [6](#6-signed-shift-reciprocal-lemma-c1) | Signed-shift reciprocal lemma (C1) | [PROVED] |
| [7](#7-the-logarithmic-power-audit-c7) | The logarithmic-power audit (C7) | [OPEN] |
| [8](#8-block-closure-at-support--54-c5) | Block closure at support < 5/4 (C5) | [AXIOM] |
| [9](#9-the-trace-transfer-beyond-bandwidth-one-c6) | Trace transfer beyond bandwidth one (C6) | [AXIOM] |
| [10](#10-statements-in-the-run-that-are-not-used) | Statements not used, and why | [AFFIRMATIVE] |
| [11](#11-summary-table-of-replacements) | Summary table of replacements | [REFERENCE] |
| [12](#12-phase-0-source-intake-and-the-withdrawn-100-claim) | Phase 0 source intake; withdrawn 100% claim | [WITHDRAWN] |
| [13](#13-phase-0d-continuous-integration-gate) | Phase 0d continuous-integration gate | [AFFIRMATIVE] |
| [14](#14-a11-evaluate-dont-bound) | A1.1 evaluate-don't-bound | [KILLED] |
| [15](#15-a12-cross-scale-signs) | A1.2 cross-scale signs | [KILLED] |
| [16](#16-b-2-rudnicksarnak-reduction) | B-2 Rudnick--Sarnak reduction | [OPEN] |
| [17](#17-b-1-quartic-stability-inequality) | B-1 quartic stability inequality | [PROVED] |
| [18](#18-a13-weil-grade-hb) | A1.3 Weil-grade HB | [KILLED] |
| [19](#19-a21-r1a-alias-construction) | A2.1 R1a alias construction | [KILLED] |
| [20](#20-a22-r1a-alias-free-fallback) | A2.2 R1a alias-free fallback | [KILLED] |
| [21](#21-b-3-terminal-certificate-layer) | B-3 terminal certificate layer | [PROVED] |
| [22](#22-b-4-eta--12-factorization) | B-4 `eta > 1/2` factorization | [KILLED] |
| [23](#23-phase-c-robust-stability-and-finite-spectral-trim) | Phase-C robust stability / spectral trim | [PROVED] |
| [24](#24-phase-c-inputs95-boundary) | Phase-C `Inputs95` boundary | [OPEN] |
| [25](#25-phase-c-quartic-transfer) | Phase-C quartic transfer | [PROVED] |
| [26](#26-a1-depth-four-coefficient-object) | A1 depth-four coefficient object | [PROVED] |
| [27](#27-a1-bblr-gcd-allocation) | A1 BBLR gcd allocation | [PROVED] |
| [28](#28-a1-smooth-hb-to-bblr-grouping) | A1 smooth HB-to-BBLR grouping | [KILLED] |
| [29](#29-a1-actual-scale-bblr-block) | A1 actual-scale BBLR block | [KILLED] |
| [30](#30-b-2-rs-pair-integrals) | B-2 RS pair integrals | [PROVED] |
| [31](#31-a1-pre-majorant-dikuznetsov-audit) | A1 pre-majorant DI/Kuznetsov audit | [KILLED] |
| [32](#32-a1-four-mobius-slot-route) | A1 four-Mobius-slot route | [KILLED] |
| [33](#33-a1-sq4-simultaneous-routes) | A1 SQ4 simultaneous routes | [KILLED] |
| [34](#34-a1-sq4-finite-gauss-transform) | A1 SQ4 finite Gauss transform | [PROVED] |
| [35](#35-a1-sq4-crtconductor-strata) | A1 SQ4 CRT/conductor strata | [PROVED] |
| [36](#36-a1-sq4-correlated-moment-audit) | A1 SQ4 correlated-moment audit | [KILLED] |
| [37](#37-a1-sq4-published-theorem-audit) | A1 SQ4 published-theorem audit | [KILLED] |
| [38](#38-b-2-actual-block-centering-bridge) | B-2 actual-block centering bridge | [PROVED] |
| [39](#39-a2-r1a-allocation-capacity) | A2 R1a allocation capacity | [KILLED] |
| [40](#40-b-4-eta-superposition) | B-4 eta superposition | [KILLED] |

---

## Executive Summary

This file contains 40 audit sections: 13 proved, 3 affirmative, 1 error found and corrected,
3 axiomatized, 15 method classes killed, 3 open problems, 1 withdrawn claim, and 1 reference table.
The single most important finding is in **section 3**: the BBLR error bound in `03_arithmetic_cycle3.md`
equation (12) writes `(AB)^{1/2}` where the correct factor is `AB`, changing the trace-grade threshold
from `eta < 1/2` to `eta < 1/4`.  This was corrected in cycle 4 and is proved in Lean.
The single most important open problem is in **section 7**: the logarithmic-power budget does not close
at the forced Heath--Brown depth `K >= 4`, because the power `C >= K-1 >= 3` exceeds every available
threshold (`C < 2`, `C < 1`, or `C < 0`).  This is proved in both directions in Lean.
The four axioms are: Shiu progression majorant (section 5), block closure at `sigma < 5/4` (section 8),
signed-pair trace grade at `sigma < 3/2` (section 8, but see section 7's defect), and trace transfer
at `lambda > 1` (section 9).  All four are stated over inspectable vocabulary, not opaque constants.
The quartic rungs (sections 19--25, 39) are conditional on `PrincipalCyclicBlock`, which section 39
proves uninhabitable under the current interface.
**This file is a reference.  Consult specific sections by topic; do not read cover-to-cover.**

---

## Cross-Reference Table

| Topic | Canonical section here | Also discussed in |
|-------|----------------------|-------------------|
| BBLR error bound | 3 | AXIOMS.md 1; VALIDATION.md; `docs/audit/actual_scale_bblr.md` |
| Shiu majorant / refutation | 5 | AXIOMS.md 1 (full history); `RH/Zeta85/Discharge/ShiuNoGo.lean` |
| Window costs (rational + transcendental) | 4 | 2 (Phase A rational); VALIDATION.md |
| Log-power budget | 7 | 15 (cross-scale); `docs/audit/log_budget_routes.md` |
| Trace transfer / `calE` | 9 | AXIOMS.md (axiom 4); 1 (`lam_le_one` structural fact) |
| Stability inequality | 17 | 23 (robust version); `docs/audit/stability_inequality_proof.md` |
| R1a construction | 19, 20 | 39 (no-go); 24 (`Inputs95`); `docs/audit/r1a_*.md` |
| RS / block moments | 16 | 30 (pair integrals); 38 (centering bridge); `docs/audit/rs_*.md` |
| SQ4 / four-Mobius | 32 | 33--37; `docs/audit/sq4_*.md`; `docs/audit/four_mu_kloosterman.md` |
| HB depth-four coefficients | 26 | 27 (gcd); 28 (grouping); `docs/audit/hb_depth_four_coefficients.md` |
| Quartic transfer / certificates | 25 | 21 (B-3 layer); `docs/audit/b3_certificate_layer.md` |
| `Inputs95` boundary | 24 | 25 (transfer); `docs/audit/inputs95_boundary.md` |
| Eta factorization | 22 | 40 (superposition); `docs/audit/eta_gt_half_factorization.md` |

---

## 1. Setup and reading (S1--S3)

**Verdict: affirmative -- all 21 source files read, base repository builds clean at commit `3635e74`, all reuse points tabulated.**

All 21 markdown files and both PDFs were read.  The base repository builds clean
(`lake build`, 9010 jobs, zero errors; four `PrintAxioms` audits give the standard three axioms
on all 43 headline theorems).  One inconsequential discrepancy: the task refers to
`Zeta23/ThmD/Final.lean` and `Zeta23/ThmD/Mult.lean` (both exist) and to a "Proposition 4.4
analogue" / "Proposition 5.6 analogue", which are `Zeta23.Assembly.seamA_mult2` /
`RHLinalg.rank_trace_ineq` and `Zeta23.ThmD.tracesBoundsD_concrete`.  All reuse points are
in `docs/REUSE_MAP.md`.

**Structural fact discovered during S2.**
`Zeta23.Params.Valid.lam_le_one` occurs 72 times in `Zeta23/`, always on the prime side or
inside `Zeta23.Params.calE`.  The zero side never uses it; in particular
`Zeta23.Taper.hasSum_phiHatR_sq` needs only `TaperProfile`, `0 < w`, `2w <= L`.
Seam A holds at any support; the 85% axiom set could be confined to prime-side statements.
What breaks past `lambda = 1` is `calE`'s summand `X * log l/(T * l)` with `X = (T/2pi)^lambda`,
which tends to `0` iff `lambda <= 1`.

---

## 2. Phase A -- arithmetic core

**Verdict: affirmative -- all Phase A arithmetic proved in Lean with no axiom; independently confirmed by exact rational arithmetic.**

Everything asked for in A1--A3 is proved (`RH/Zeta85/Window.lean`, `RH/Zeta85/Certificate.lean`):

| claim | source | status |
|---|---|---|
| `A = integral v = 1031/1200` | `01_certificate_cycle1.md` (9) | proved (`integral_vProf`) |
| `B = integral v^2 = 1809683/2400000` | ibid. | proved (`integral_vProf_sq`) |
| `g(u)` = the displayed quintic | ibid. (8) | proved (`integral_autocorr`) |
| `J = 970487502160963/3017889594720000` | ibid. (9) | proved (`jSat_eq`) |
| `c_pc = 2227707598259143/2561811364469143` | ibid. (10) | proved (`cPC_eq`) |
| `c_pc > 20/23` | ibid. | proved (`cPC_gt`) |
| `2 - 1/c_pc = 1893603832049143/2227707598259143` | ibid. (11) | proved (`two_sub_inv_cPC`) |
| margin `= 1047470577429/44554151965182860 > 0` | ibid. (12) | proved (`margin_eq`, `margin_pos`) |
| count lemma (1)--(3) | `01_hybrid_cycle1.md` 1 | proved (`count_lemma`) |
| specialization `C = 23/20 - eta` | ibid. (2)--(3) | proved (`count_lemma_85`) |

All confirmed by exact rational arithmetic (Python `fractions`) before formalization.  The external
check also produced `lambda A^2 = 152003423/144000000` and
`B + lambda J = 2561811364469143/2110412304000000` (numerator = denominator of `c_pc`).
The integer cross-multiplication is proved by `decide`.

*Notational clarification (not an error).*  The source introduces `J` as both a 2D and 1D integral;
only the 1D form is used downstream.  `Certificate.lean` takes the 1D form as the definition
(`satJ`); the 2D identity is not proved and not needed.

*Also confirmed:* the count lemma's nonnegativity hypotheses `s, d, p >= 0` are stated to match
the source but are not needed -- `(2) - 2*(1)` already gives the conclusion.

---

## 3. The BBLR error bound

**Verdict: equation (12) in `03_arithmetic_cycle3.md` is wrong -- `(AB)^{1/2}` should be `AB`.  Corrected in cycle 4; proved in Lean.**

`03_arithmetic_cycle3.md` equation (12) states the Watt-strengthened BBLR error as

    E <<_eps (ABMNH_s^2)^{1/4+eps} * ( (AB)^{1/2} + H_s^{1/4}(A+B)^{1/2}(ABMN)^{1/8} ) .

The first factor inside the bracket is `AB`, not `(AB)^{1/2}`.
`08_arithmetic_cycle4_unconditional_79p7214.md` (3) has the correct form and says so explicitly.
At `A = B = H = T^eta`, `M = N = T`:

    misquoted:  E1  = T^{1/2+2eta}   -> trace-grade for eta <= 1/2
    correct:    E_A = T^{1/2+3eta}   -> trace-grade for eta <= 1/4

Both readings and the gap (`= eta`) are proved in `RH/Zeta85/Discharge/Exponents.lean`:
`EA_exponent`, `E1_misquoted_exponent`, `misquote_gap`, `EA_traceGrade_iff`,
`E1_misquoted_traceGrade_iff`.

The corrected factor is used in `RH.Zeta85.Hypotheses.bblr_error_bound`.  The frozen interface
is proved by choosing the complete finite sum as the unrestricted main term (error = zero).

*Second inconsistency:* cycle 3's `sigma < 5/4` coincides with cycle 4's but for different reasons;
`Exponents.bblr_blackbox_ceiling` records the correct joint statement.

---

## 4. The two transcendental window costs

**Verdict: both verified numerically (truncations safe-sided), then replaced by exact rational polynomial profiles proved in Lean.**

Both windows are transcendental.  Rung 1's `v(s) = cos(sqrt(2) s)` needs certified interval
arithmetic on `Real.sin`/`Real.cos` at irrational arguments; rung 2 needs additionally a proof
that its displayed piecewise function solves the Euler equation.  Mathlib's `norm_num` does not
provide either.

*Rung 1, `lambda = 101/100`:*

| quantity | source value | computed |
|---|---|---|
| `I1 = integral v` | 0.9187253698655684 | 0.9187253698655684 |
| `I2 = integral v^2` | 0.8492279993183042 | 0.8492279993183042 |
| `J_lambda` | 0.27396852346630846 | 0.2739685234663084 |
| `D_{1.01}` | 1.32075113693... | 1.3207511369299922 |
| `2 - D` | 0.67924886307... | **0.6792488630700078** |

Truncated literal is on the safe side.

*Rung 2, `sigma = 5/4`:*

| quantity | source value | computed |
|---|---|---|
| `integral u` | 1.09716424928793 | 1.0971642492879266 |
| `C` (Euler constant) | 1.31965363103003 | 1.3196536309619744 |
| `D*_{5/4}` | 1.20278584713866 | 1.2027858470766308 |
| `2 - D*` | 0.79721415286134 | **0.7972141529233692** |

Euler equation checked at nine interior points; residual consistent with 15 published digits.
Again the truncation is safe-sided.

**Replacements.**  `Window101.windowCost_101_proved` realizes rung 1 with a degree-six profile.
`RationalWindow125.windowCost_125` realizes rung 2 with a nonnegative degree-thirty profile at
exact rational support `5/4 - 10^{-12}`.

*Precedent:* the base repository's own `XiPrime` topic uses truncated decimals.  Rung 3 needs
no truncation: its constant is the exact rational `1893603832049143/2227707598259143`.

---

## 5. Shiu-type progression majorant (C3)

**Verdict: not discharged -- Shiu's theorem does not apply verbatim to the signed coefficients `c_p`.  Axiom 1 (`shiu_majorant2`) replaces the original false rendering.**

`docs/run/12` (14) states: `Sigma_{p ~ P, p = r (q)} |c_p| << (P/phi(q))*(log T)^C`.
Two blockers: (i) Shiu's theorem requires a non-negative multiplicative majorant; the run's
`c_p` are signed convolutions, and no multiplicative majorant is exhibited.  (ii) The
justification presupposes the explicit finite-depth Heath--Brown identity, not formalized.

**Replacement:** Axiom 1, `RH.Zeta85.Hypotheses.shiu_majorant2`, over inspectable vocabulary
(`ShiuMajorant2` / `progressionSum` / `DivisorBounded`).  Used by rung 3 only.

**The original `ShiuMajorant` is false**, and the repository proves it:
`RH.Zeta85.not_shiuMajorant_quarter` refutes `ShiuMajorant (1/4)`.  A `tau(3^m)`-spike
isolated modulo a power of two beats any fixed `(log T)^C` bound.  `ShiuMajorant2` makes
three corrections: (D1) majorant scale `(log P)^C`; (D2) range `q <= P^(1-eta)`; (D3)
class-uniform constants quantified after the divisor-bound class.

---

## 6. Signed-shift reciprocal lemma (C1)

**Verdict: proved in full with no axiom, by summation by parts (not Poisson).**

`RH/Zeta85/Discharge/SignedShift.lean`, no axioms.

*Equation (12):* `|S_{H0}(theta)| <<_J H0(1 + H0||theta||)^{-J}` is proved as

    ||S_{H0}(theta)|| * (1 + H0||theta||)^J <= (J+5)*2^J*(K0+K_J)*H0

for `w in C^J(R)` vanishing outside `(1,2)`, every `H0 >= 1` and every real `theta`.
The constant is explicit.

*Deviation from source:* the source says "Poisson summation gives (12)".  The route taken here
is `J`-fold summation by parts against the geometric kernel.  Its four proved ingredients:
`bdiffIter_le`, `abel_iter`, `norm_cexp_sub_one`, and `jordan`.

*Equation (13):* `Sigma*_{r mod q} |S_{H0}(lr/q)| <<_J q + H0(l,q)`.  Both halves proved:
the spacing half (`nearInt_int_div`) and the counting half (`sum_over_separated`).

**Scope note.**  `sum_over_separated` is stated for an arbitrary labelling.  The fibre count
`#{r < q : lr = c (mod q)} <= (l,q)` was not formalized; a first attempt was withdrawn.
No axiom was introduced: the frozen BBLR interface is proved by taking the whole finite sum
as its unrestricted main term.

---

## 7. The logarithmic-power audit (C7)

**Verdict: the log budget does not close.  At forced depth K >= 4, the power C >= 3 exceeds every threshold.  This is the most important finding.**

Full treatment in `RH/Zeta85/Discharge/LogBudget.lean`.

**Attempted:** `R_HB << (T^{1+eta} + T^{1/2+2eta})(log T)^C` with `C` fixed, and hence
criterion `(AS)` at every `sigma = 1 + eta < 3/2`.

**Failure.**  Three facts from the sources give the budget:

1. On a dyadic block `n ~ Y`, the complete coefficient of `Lambda(n)Lambda(n+h)` is
   `<< LT/Y + O(log L/Y)` -- **one** power of `L`.
2. An `h`-summed remainder `E` at length `Y` enters at scale `(T*L/Y)*E` (the unnamed power).
3. The displayed sum runs over `O(log X)` dyadic scales with **one** further power from
   triangle inequality.

Budget computation (substituting `E << X(log T)^C`):

    generous:             T*(log T)^{C+1}     -> threshold C < 2
    literal Y-dyadic:     T*(log T)^{C+2}     -> threshold C < 1
    fully triangle-summed: T*(log T)^{C+3}    -> threshold C < 0
    budget:               T*(log T)^3

All three dichotomies proved in both directions in Lean.

None is available.  `08` chooses `K > (1+eta)/eta`; at `eta = 43/100`, `K >= 4`.
A depth-`K` identity gives `C >= K-1 >= 3`, so `C+1 >= 4 > 3`, `C+2 >= 5 > 3`,
`C+3 >= 6 > 3` (`LogBudget.verdict_all`).

At the formal level, `(AS)` demands `<<_A X(log X)^{-A}` for every `A`, while (2) supplies
`(log T)^{+C}`.  No rearrangement produces `(AS)`.

**Replacement:** the target is not weakened.  Axiom 3,
`RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2`, records the defect in its docstring.

**Lower rungs unaffected:** at `eta < 1/4` the BBLR errors are power-saving
(`Exponents.bblr_savings`), and `LogBudget.power_beats_log` proves a fixed power beats
every fixed logarithmic loss.

---

## 8. Block closure at support < 5/4 (C5)

**Verdict: not discharged -- Heath--Brown identity, Type-I/II estimates, and grouping lemma not in Mathlib.  All exponent arithmetic proved.  Axiom 2 replaces the block.**

Three blockers: (i) the finite-depth Heath--Brown identity and grouping lemma would have to be
built from scratch; (ii) the Type-I estimate needs Poisson + hybrid large sieve in a uniform
form absent from Mathlib; (iii) "there is no third block" cannot be stated without (i).

**Discharged:** all exponent arithmetic in `RH/Zeta85/Discharge/Exponents.lean`.

**Replacement:** Axiom 2, `RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4`, stated as an
implication from `BBLRErrorBound`.  The premise is now supplied by the proved `bblr_error_bound`.

---

## 9. The trace transfer beyond bandwidth one (C6)

**Verdict: zero side reused unchanged from base repository; prime-side trace rebuild at `lambda > 1` axiomatized as Axiom 4.**

**Reused** (unchanged from base): `seamA_mult2`, `rank_trace_ineq`, `mult_two`,
`N0star_lower_c`, `hasSum_phiHatR_sq`, `cumulative_of_dyadic`, `N0simple_add'`,
`zetaSeam`, `paperInputs_zeta`.  See `docs/REUSE_MAP.md`.  None carries `lambda <= 1`.

**New and assumed:** the support-beyond-one evaluation of the second moment with the
saturated kernel.  Axiom 4, `traceTransfer_saturated`, takes the window cost and aggregate
criterion as hypotheses so it cannot smuggle in the arithmetic or numerics.

**Obstruction:** `Zeta23.Params.calE` contains `X*log l/(T*l)`, `X = (T/2pi)^lambda`,
tending to `0` iff `lambda <= 1`.  Rebuilding at `lambda > 1` means rebuilding
`PrimeSideA/`, `PrimeSideB/`, `ThmD/Traces.lean` -- same order as the base repository.

---

## 10. Statements in the run that are *not* used

**Verdict: affirmative -- five self-terminated routes identified and confirmed unused.**

* **hybrid/selector** (`01_hybrid`..`11_hybrid`): no unconditional constant above 0.6725007036.
  Useful residue: the count LP (1)--(3), used as Phase A3.
* **Routh/resultant** (`03_hybrid`, `04_hybrid`): output 0.4021932, weaker than accepted base.
* **one-sided sieve** (`04_certificate`): infinite limiting majorant cost.
* **quartic residual** (`09_certificate`): gives 13/18 = 0.7222, weaker; input unproved.
* **three-lobe sparse** (`01_arithmetic` 3): gives 0.8908336 but needs (AS), strictly more than rung 3.

The formalized chain uses only: the count LP, the saturated-kernel functional, the BBLR inputs,
the cycle-4/cycle-5 aggregate criteria, and the base repository's zero side.

---

## 11. Summary table of replacements

| # | statement attempted | source | outcome |
|---|---|---|---|
| 1 | window moments, `c_pc`, margin, count lemma | `01_certificate`, `01_hybrid` | **proved** |
| 2 | `SaturatedWindowCost (143/100) D_pc` | ibid. | **proved** |
| 3 | signed-shift decay (12) | `12` 2 | **proved** (summation by parts) |
| 4 | (13), spacing + counting halves | `12` 2 | **proved**; instantiation left open, no axiom |
| 5 | exponent bookkeeping of cycles 3--5 | `03`, `08`, `12` | **proved** |
| 6 | log-power audit | `12` 5 | **proved -- budget does not close** |
| 7 | BBLR Prop 3.1 error-bound (corrected `AB`) | BBLR / `08` (3) | **proved** by unrestricted main term |
| 8 | BBLR Poisson-block interface | BBLR / `12` | **proved** by unrestricted main term |
| 9 | Shiu progression majorant | `12` (14) | axiom 1 |
| 10 | block closure `sigma < 5/4 => (AS)` | `08` 2 | axiom 2 |
| 11 | cycle-5 remainder `sigma < 3/2 => (AS)` | `12` (2), 5 | axiom 3 -- **see section 7** |
| 12 | window cost at `101/100` | `07` | **proved** by exact rational profile |
| 13 | window cost below `5/4` | `08` 3 | **proved** by exact rational profile |
| 14 | trace transfer at `1 < sigma < 3/2` | `01`, `02`, `12` 5 | axiom 4 |

---

## 12. Phase 0 source intake and the withdrawn 100% claim

**Verdict: withdrawn -- the 100% claim has inconsistent premises (empty feasible class).  No theorem or rung depends on it.**

Four logical batches ingested from two ZIP archives plus two loose-file batches.  The terminal
95 batch is present.  Exact inventory: `docs/run/MANIFEST.md`.

`docs/run/100/FINAL_100_RESULT.md` is **WITHDRAWN**.  Two load-bearing issues:

1. The wide-block moment has no verified principal-compression construction.  Independent
   reconstruction (`verify/withdrawn_100_claim.py`) shows the pointwise cone admits
   `M2 = 0.374347517070571...`, so `0.3144` is not reproduced and is not used.

2. The file's own premise package is inconsistent at `s/N = 1`.  With `b/N = 0` and
   `eps = D-1 < 3385873/50000000`, the stability inequality forces
   `M2 < 64517303/172727100 = 0.373521601...`, while the file assumes
   `M2 > 18717/50000 = 0.37434`.  The excess is `70679807/86363550000 > 0`.

The simultaneous premises describe an empty feasible class.  Script output committed as
`verify/withdrawn_100_claim.out`.

---

## 13. Phase 0d continuous-integration gate

**Verdict: affirmative -- CI guards reproduction only; it discharges no mathematical input.**

`.github/workflows/ci.yml` installs the pinned Lean toolchain, fetches Mathlib cache, builds
`Zeta23` / `RH.Zeta85.Main` / `Solution.Zeta85`, diffs headline axioms against `AXIOMS.md`,
runs base headline audits, and rejects proof-level `sorry`/`admit` outside comparator files.

---

## 14. A1.1 evaluate-don't-bound

**Verdict: one exact method class killed (d4 mean-value + norm-bound + Cauchy).  Not an impossibility result for the signed target.**

At \(P=T^{93/100}\), \(Q=T^{1/2}\), \(H=T^{43/100}\), the literal `C = 0` target is the
signed weighted progression estimate.  If proved, this closes the log budget alone.

The published \(d_4\) mean-value route does not prove it.  The exact residue Parseval bound
combined with Nguyen's Theorem 3 gives \(T^{3917/2400}(\log T)^{15/2}\), exceeding
\(PQ=T^{143/100}\) by \(T^{97/480}\).  Parry's Theorem 1 gives \(T^{261/160+\varepsilon}\),
excess \(T^{161/800+\varepsilon}\).  Wei--Xue--Zhang's modulus range misses the required
exponent by \(1951/54312\); Rodgers--Soundararajan stops below \(\log P/\log Q=93/50\).

Two further statement gaps remain: the actual coefficients are signed convolutions (not \(d_4\)),
and no cited theorem identifies the blockwise main terms with the singular-series subtraction.
The next ordered route is A1.2; `(WG-HB)` remains the final route.

---

## 15. A1.2 cross-scale signs

**Verdict: five cross-scale method classes killed.  The signed common-scale leading family remains open.**

On a local block \(Y=T^{1+\theta}\), cycle 5 has \(PH\) saving \(T^{-7/100}\) for
\(\theta\le43/100\), while \(PQ\) is critical.  The depth-four-compatible band contains
\(\frac{29/400-\varepsilon}{\log2}\log T+O(1)\) dyadic critical blocks.

Equation (6), even if granted, produces \(O(T(\log T)^{C+1})\), closing only for \(C<2\).
At forced \(C\ge3\), it exceeds the budget by at least one logarithm
(`LogBudget.crossScale_recombination_fails`).  Even root-number-of-blocks cancellation
closes only for \(C<3/2\).

**Five classes killed:** (1) recombination after absolute values; (2) endpoint-phase
cancellation; (3) Mellin orthogonality away from zero; (4) Cauchy/square-function arguments;
(5) Abel summation without a new uniform dyadic-prefix bound.  All-positive families
saturate the triangle inequality exactly (`blockwise_triangle_sharp`).

The exact surviving statement is equation (14) of `docs/audit/log_budget_routes.md`:
construct compatible signed families, cancel zero terms before absolute values, and prove
the common-scale leading family is \(o(T(\log T)^2)\).  The five-scale prime experiment's
z-scores cannot be rerun from supplied material and are not used as evidence.

---

## 16. B-2 Rudnick--Sarnak reduction

**Verdict: finite deterministic and internal contraction layers discharged; eight analytic blockers remain.**

Rudnick--Sarnak Theorem 3.1 (degree `m=1`) is an unconditional **smoothed** all-tuples
correlation theorem at strict total Fourier support below 2.  Theorem 3.2 is the
sharp-height variant and assumes RH.

`RSReduction.lean` discharges the deterministic finite layer: gauge-fixed weighted cyclic
symbol, zero-frequency value, zero-sum `rsPairVector`, exact RS main terms for k=1..4,
and formula (27) centering to formula (18) through degree four.

`RSPairIntegrals.lean` discharges the internal analytic contraction layer: every one- and
two-pair term through degree four, including separated, nested, and crossing pairings.
Final wrappers derive all integrability from `0 < mu`, `Continuous r`, `HasCompactSupport r`.

**Eight remaining blockers:** (1) cyclic-symbol smoothness and strict-support admissibility;
(2) instantiate `RS1996ZetaInputs.theorem31`; (3) R1a construction and principal-block
identification; (4) complex-frequency Poisson; (5) k=3,4 finite-grid/end estimates;
(6) simultaneous smooth-height limit; (7) `mu_T = mu*log(T/2pi)/log T -> mu` conversion;
(8) top-hat smoothing limit with uniform domination.

No `BlockMomentLimits` instance constructed.  No rung status changes.

---

## 17. B-1 quartic stability inequality

**Verdict: proved -- the exact finite-dimensional stability inequality is discharged in Lean with no axiom.**

`RH/Zeta85/Stability.lean` proves: for \(G=P+Q\) with \(P\succeq0\),
\(\operatorname{rank}P\le s\), \(\operatorname{tr}P\le s\), \(n_+(Q)\le b\),
\(s+2b\le N\), \(\operatorname{tr}G=N\), \(\lVert G\rVert_F^2\le DN\):

\[
 \sum_{i>b}(\lambda_i(G)-1)_+^2\le s-(2-D)N.
\]

The proof constructs both interlacing steps: a threshold-count rank-update theorem (Weyl
inequality) and a threshold-count hard-Sylvester theorem (Cauchy interlacing / principal
compression).  Public theorems `stability_inequality`,
`tailExcessSq_isometricCompression_le`, `tailExcessSq_principalCompression_le`, etc.,
depend only on `propext`, `Classical.choice`, `Quot.sound`.

This does not supply the R1a principal block; quartic rung statuses remain unchanged.

---

## 18. A1.3 Weil-grade HB

**Verdict: the one-shot W1 class is killed.  Simultaneous coefficient-sensitive cancellation remains open.**

At \(\eta=43/100\), any bound \(\sum_{q\asymp Q}|\mathcal R_{q,\ell}|
\ll HQ^2T^{-\delta}(\log T)^B\) with fixed \(\delta>0\) closes the log budget.
The proposed simultaneous exponents are \(34/25+\varepsilon\) and \(279/200+\varepsilon\),
with limiting saving \(7/200\).

**Class W1 killed:** arguments using independent progression-cell sizes, at most one
completed variable, or one fixed-modulus bilinear Kloosterman theorem without simultaneously
exploiting two retained Heath--Brown factors.  Parseval gives \(\sum_r|S_H(r/q)|^2\asymp qH\);
one completion + Weil gives excess \(T^{9/50}\); Bettin--Chandee gives excess \(T^{767/2000}\);
BBLR/Kuznetsov gives \(T^{179/100}\) and \(T^{161/100}\).  Blomer--Pascadi and
Milicevic--Qin--Wu preprints are outside the required length.

`HBDepthFour.lean` defines the sharp signed expansion but the smooth source identification,
BBLR frequency \(\ell=0\) integrals, and their signed Euler/Ramanujan evaluation remain
absent.  The surviving statement is `(WG-HB)` in `docs/audit/log_budget_routes.md`.

---

## 19. A2.1 R1a alias construction

**Verdict: critical-density TDAC class killed by an exact finite rank argument.**

The scalar power-complement identity controls only the zero-alias row.  For the exact finite
common-lattice class, fiberization modulo `a` gives rank at most `n_j` per window; the
distinguished window is alias-free with rank `N`, while remaining channels have rank
`< N`.  Contradiction holds for arbitrary signs or phases.

`AliasRankObstruction.lean` machine-checks the rank bound, full-rank diagonal lemma, and
exact `19999/4999`, `14999/4999`, `1499999/499000` count corollaries.
`verify/a2_1_tdac_rank.py` certifies profile signs with exact rational intervals.

For file 15's quadratic profile, the exact central edge residual is
\(V(\mu/2)-1 = 42756493/1031000000 > 0\) at \(\mu=499/1000\).

This kills A2.1 only for finite commensurable systems with the cycle-3 count.  A2.2 was
tested separately and killed at the base normalization.

---

## 20. A2.2 R1a alias-free fallback

**Verdict: normalization and quartic class killed -- no mean-one literal principal block exists; honest degree-four tail optimum is zero.**

The base Lemma 2.2 mechanism gives an alias-free construction, but the obstruction is the
global hat normalization.  An intrinsic mean-one block is the literal compression
`C = H/sigma`; a prescribed mean-one symbol requires `sigma*r <= V_sigma`, not `r <= V_sigma`.
For the quadratic profile, `sup V_sigma = 1200/1031 < 143/100`, so no mean-one interval
block exists at any support in scope.

The intrinsic construction with \(x_0^2=(\sigma^2-\mu^2)/12\), \(r(t)=V_\sigma(x_0+\mu t)\)
has mean exactly one.  Its five-interval partition is alias-free a.e.  The corrected stability
threshold is \((C-I)_+^2 = \sigma^{-2}(Y-(\sigma-1))_+^2\).

The common rational atoms \((-7/10,-1/5,-1/10,3/10,2/5)\) have positive weights >1/25
matching closed moments through degree four.  Both sharp primal and dual values are exactly
zero.

`AliasFallback.lean` proves the generic rational moment reconstruction, all positivity and
support checks, the scaling identity, and strict-support zero tails.  `verify/a2_2_alias_free_scaling.py` is the independent verifier.

**Exact blocker after A2.2:** escaping requires a new coefficient count/normalization, a
modulation system outside A2.1/A2.2, or spectral input beyond four moments.

---

## 21. B-3 terminal certificate layer

**Verdict: finite scalar costs proved; flat R-9383 endpoint obstructed (upward-rounded by >= 1.152e-16).  Conditional headlines for R-8686/R-9506.**

`QuarticWindowWitnesses.lean` defines even rational polynomials of degrees 18 and 10,
proves strict positivity by exact Bernstein coefficients, and obtains

\[
 D_{14999/10000}<1.13434643,
 \qquad
 D_{19999/10000}<1.06772567.
\]

`TopHatMoments.lean` proves centered scalar moments through degree four, all distance-potential
contractions, \(\int r_p^2h_p^2 = 7p/60\), \(\mathcal X_{\mathrm{simplex}}(r_p) = p/30\),
and assembles the exact closed moments in terminal formula (21).  `crossingReduction` proves
the determinant-one substitution and four-quadrant reduction.

`TrimmedMoment.lean` proves finite trimmed quartic weak duality with conditional outputs
\(0.868552508... > 0.86855250\) and \(0.950638321... > 0.95063832187565\).

**R-9383 flat branch obstructed.**  Exact rational enclosures isolate the fixed root:
\(0.9383133270509488847 \le r_{\mathrm{flat}} \le 0.9383133270509488848 < 0.938313327050949\).
File 19 rounded upward by at least \(0.0000000000000001152\).

The later Phase-C transfer derives R-9383 monotonically from the strict R-9506 branch.
R-8657 and R-8686 likewise have conditional headlines; their per-support analytic structures
remain uninstantiated.

---

## 22. B-4 `eta > 1/2` factorization

**Verdict: relabel-only class killed -- literal relabelling cannot construct the requested M1.  Surviving route requires (EF_eta).**

For `1/2 < eta < 1`, choosing `M1 = T^{1-eta}`, `M2 = T^eta` gives the preliminary
replacement with exponent `2*eta + (1+eta)*epsilon`, power-small whenever
`epsilon < (1-eta)/(1+eta)`.  `EtaClosure.preliminary_with_log_is_o` proves this.

A legal depth-three `j=2` block has two truncated atoms of exponent `eta/2` and two smooth
atoms of exponent `1/2`.  The only whole-variable group of exponent `eta` is the truncated
pair.  Remaining whole-factor exponents are `0`, `1/2`, `1`, none equal to `1-eta`.
`balanced_j2_no_asymmetric_M1` proves this for the full open interval.

The surviving route is a pointwise finite signed convolution identity `(EF_eta)` meeting every
BBLR hypothesis.  Under literal prime-dyadic accounting it must produce `C < 1`;
`EtaClosure.literal_log_budget_fails` proves every `C >= 1` fails.  No such identity is
present.

---

## 23. Phase-C robust stability and finite spectral trim

**Verdict: proved -- robust stability with explicit error coefficients (2,4,1,2) and finite spectral bridge, both with no axiom.**

`stability_prebound` proves the finite estimate

\[
 \operatorname{Tail}_b(G)
 \leq \lVert G\rVert_F^2-4\operatorname{tr}G+s
      +2\operatorname{traceCap}+4b.
\]

`robust_stability_inequality_withCountError` adds error terms:

\[
 \operatorname{Tail}_b(G)
 \leq s-(2-D)N_0+2e_P+4e_T+e_F+2e_C.
\]

Ambient dimension `d` and real scale `N0` are independent.  The coefficients `(2,4,1,2)` and
count slack are exact.  Proved also for isometric and principal compressions.

The finite spectral bridge: `principal_spectral_headTrimmedMomentInputs_of_moments` needs only
four named equalities between finite spectral moments and analytic targets.  Those four
same-block moment identifications remain the precise R1b/grid interface.

---

## 24. Phase-C `Inputs95` boundary

**Verdict: open -- exact boundary recorded with 11 fields but no Lean axiom or instance constructed.**

`RH/Zeta85/Inputs95.lean` records the honest analytic boundary.  Each family is indexed by
its exact support, bandwidth, fill, and B-3 profile.  Two exact rewrite theorems identify
costs with `QuarticWindowWitnesses.D8686`/`D9506`; no free numeric cost field.

`PrincipalCyclicBlock` is the exact R1a construction obligation.  `RS1996ZetaInputs.theorem31`
records the published RS theorem.  `BlockMomentLimits` states the unproved R1b bridge.
The pair-trace field does not derive trace limits; the RS field does not derive block-moment
limits.

The top-level `Inputs95` bundle has 11 fields.  This module constructs no instance.

---

## 25. Phase-C quartic transfer

**Verdict: proved (conditional) -- quartic transfer assembled from proved stability and B-3 layers; all four rungs remain conditional on four uninstantiated structures.**

`QuarticTransfer.lean` gives: for dimension \(d\), trim budget \(b=s_2+p\), dual cap \(c\),
and certified cost \(\bar D\):

\[
 dA_P+(2-\bar D-c/2)N
 \leq (1-c/2)N_0^s
   +2e_P+4e_T+e_F+3N_{II}.
\]

The coefficient three is exact (three contributing pieces, cap-dependent parts cancel).
The base Riemann--von Mangoldt and local-count theorems prove `NII = o(N)`.

`QuarticMain.lean` exposes `rung8657`(`_cumulative`), `rung8686`(`_cumulative`),
`rung9383`(`_cumulative`), `rung9506`(`_cumulative`), each taking exactly four structures:
`FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, `BlockMomentLimits`.

The `PairTraceGrade95` and `RS1996ZetaInputs` structures are upstream routes, not consumed
by the transfer.  No instance of the four premises is constructed.  All 21 transfer theorems
and eight headlines print exactly `[propext, Classical.choice, Quot.sound]`.

---

## 26. A1 depth-four coefficient object

**Verdict: sharp depth-four algebra and reduced centering proved; smooth source map and cancellation wall remain open.**

`HBDepthFour.lean` proves the exact \(K=4\) Heath--Brown identity

\[
 \Lambda=4\mu_Z*\log-6\mu_Z^2*\zeta*\log
 +4\mu_Z^3*\zeta^2*\log-\mu_Z^4*\zeta^3*\log
 \qquad(n\le Z^4),
\]

with explicit `HBGroupingPlan` and `hbGrouped_factorization`.  It also constructs reduced
coefficient sums, exact majorants, floor blocks, the shared index with coprimality,
and finite nonzero-frequency cross-scale sum.  Both generic and reduced centered sums vanish;
`allClass_zeroMode_ne_reduced_zeroMode` proves the two means differ.

The divisor split omits `(a,d2)=1` and `(b,d4)=1`, so it gives the raw, not canonical BBLR,
coefficient.  `BBLRGCDAllocation.lean` separately proves the canonical allocation.

**Source audit finding:** BBLR Proposition 3.1 (14) has reciprocal phase at frequency
\(\ell=0\); a reduced progression mean is not the source's \(\ell=0\) term.
`reducedCentering_alone_not_sufficient` gives a countermodel.
`empty_singleton_groupings_distinct` proves nonuniqueness from the product identity alone.

Run 12 omits the cutoff/smoothing equality, scale-dependent grouping, the instantiation for
the Fourier/shift kernel, and the signed BBLR \(\ell=0\) evaluation.  A1 remains open.

---

## 27. A1 BBLR gcd allocation

**Verdict: finite gcd allocation and kernel reindexing proved; smooth Heath--Brown instantiation remains open.**

`BBLRGCDAllocation.lean` formalizes the allocation after BBLR Proposition 3.1 (14).  For
\(d>0\) and \(d\mid A_0M_0\):

\[
 d_1=\gcd(A_0,d),\quad d_2=d/d_1,\quad a=A_0/d_1,\quad m=M_0/d_2.
\]

`allocationEquiv` proves this is an equivalence between original factor pairs and splits
satisfying `(a,d2)=1`.  `collapsedCoeff_eq_divisorSum` proves multiplicity one by explicit
bijection.  `collapsedKernelSum_eq_originalFibers` reindexes arbitrary positive ranges
using \(\gcd(dp,dq)=d \Leftrightarrow (p,q)=1\).

The unit-weight regression at \(d=p=2\) gives three canonical vs. four raw terms, confirming
that `HBDepthFour.splitCoeff` (which omits `(a,d2)=1`) is not the BBLR coefficient.

**Still missing:** smooth partition/pointwise HB identity putting grouped factors into BBLR
outer sequences, the analytic nonzero-frequency estimate, and the signed \(\ell=0\) evaluation.
No A1 status change.

---

## 28. A1 smooth HB-to-BBLR grouping

**Verdict: fixed literal-slot class killed -- no exponent cushion below 1/10 realizes the fixed asymmetric assignment.**

`HBToBBLRSmoothGrouping.lean` audits the exact fixed-scale grouping.  Component `j=1` has
atoms \(\mu_Z,\mu_Z,\zeta,\log\) with legal dyadic exponent block
\((43/200,43/200,2/5,3/5)\), total \(143/100\).  Both Mobius atoms are below the `K=4`
cap and cannot be reclassified as coefficient-one slots (`muCut_ne_coefficientOne`).

For the requested left pair \((1/2,1/2)\), every scale has gap \(1/10\).  For the right
pair \((7/100,93/100)\), every gap is at least \(33/100\).
`no_asymmetric_literal_grouping` proves no \(T^{o(1)}\) cushion realizes the assignment.

Multiplying slots does not repair: `zeta_sq_eq_twoUnitSlotMultiplicity` identifies the
collapse with divisor multiplicity \(d_2\), which is coefficient-bearing.

No A1 discharge; frozen statuses unchanged.

---

## 29. A1 actual-scale BBLR block

**Verdict: two positive-majorant classes killed -- direct Prop 3.1 and absolute progression majorant both exceed trace scale.**

`ActualScaleBBLR.lean` audits the symmetric block \(A=B=H=T^{43/100}\),
\(M_1=N_1=T^{2/5}\), \(M_2=N_2=T^{3/5}\).  Direct BBLR gives error exponents
\(179/100\) and \(161/100\), exceeding trace \(143/100\) by \(9/25\) and \(9/50\).
Nonnegative exponent slack cannot repair either.

At \(d=1\), the progression majorant gives \(PQ\) exponent \(83/50\), excess \(23/100\);
\(PH\) exponent \(63/50\), saving \(17/100\).  The Fourier-integral cancellation exactly
offsets the nonzero-frequency cutoff.

These kill applying Prop 3.1 errors blockwise and applying the absolute progression majorant
after (14).  They prove no lower bound for the signed remainder.  No A1 discharge; frozen
statuses unchanged.

---

## 30. B-2 RS pair integrals

**Verdict: proved -- all RS pair contractions through degree four discharged; no unproved analytic premise for continuous compactly supported profiles.**

`RSPairIntegrals.lean` proves the change of variables, Fubini reductions, and exact
evaluation of every contraction in `rsMainTerm (weightedCyclicSymbol mu r)` for degrees 1--4.
Six one-pair degree-four terms (four adjacent, two opposite).  Three two-pair terms
(separated, nested, crossing).  Dividing by `mu` gives the literal `mu^2` and `mu^4`
coefficients in formula (27).

Final wrappers require only `0 < mu`, `Continuous r`, `HasCompactSupport r`.
Not a `BlockMomentLimits` instance.  The R1b blockers (cyclic-symbol admissibility, published
RS application, height smoothing, log normalization, complex Poisson, grid/end estimates,
R1a identification) remain.  No rung status changes.

---

## 31. A1 pre-majorant DI/Kuznetsov audit

**Verdict: two distinct sub-verdicts.  Collapsed Drappeau class: power-killed (excess 9/25).  Literal Pascadi map: structurally inapplicable.**

`PreMajorantDI.lean` tests two one-shot routes on the `d=1` block.

**Direct collapsed Drappeau class:** collapse Mobius pairs and \((|\ell|,h)\), apply Drappeau
Theorem 2.1 at fixed \(x\), integrate.  Fixed-\(x\) exponent \(101/50\), physical exponent
\(179/100\), excess \(9/25\).  Power-killed.

**Literal completed Pascadi map:** completion yields \(k\bar a\), not the required \(ka\).
A \(\mathbb Z/5\mathbb Z\) example proves these differ; the completion frequency \(k=0\)
is not in the dyadic sum.  Structurally inapplicable.

A source-faithful \((q,a)\)-dependent reindex remains open.  No A1 discharge; frozen
statuses unchanged.

---

## 32. A1 four-Mobius-slot route

**Verdict: one-sided fixed-modulus class killed (excess 49/200).  Simultaneous estimate (SQ4-HB) remains open.**

`FourMuKloosterman.lean` audits the literal seven-scale \(d=1\) geometry:
\(u_1,u_2,v_1,v_2:T^{43/200}\), \(m,n:T^{2/5}\), \(r=|\ell|h:T^{33/50}\).

The **one-sided fixed-modulus square-root/triangle class** freezes \(v_1,v_2,n,r\), grants
ideal square-root for \(u_1,u_2,m\), and triangle-sums.  Output: \(381/200\) fixed-\(x\),
\(67/40\) integrated, both exceeding targets by \(49/200\).  Killed.

No direct application found among Bourgain--Garaev, Gong--Jia, Korolev, Bettin--Chandee,
Drappeau, Pascadi families retaining all four Mobius slots.

The surviving estimate sufficient for `(SQ4-HB)` is
\(|\mathcal Z^{(0)}_{4,\sigma}(x)| \ll T^{149/100+\varepsilon}\),
with explicit margin \(17/200\).  The smooth source-identification gap also remains.
No A1 discharge; frozen statuses unchanged.

---

## 33. A1 SQ4 simultaneous routes

**Verdict: six explicit method classes killed.  The transformed nonzero family (33) survives.**

`docs/audit/sq4_simultaneous_routes.md` tests six classes on the four-Mobius block:

1. **Single character-large-sieve:** output \(58/25\), excess \(33/50\).
2. **Two-sided norm-only:** output \(381/200\), excess \(49/200\).
3. **One-additive-large-sieve:** output \(199/100\), excess \(33/100\).
4. **Literal reciprocal-completed Kuznetsov:** structurally inapplicable (completed index
   varies with modulus).
5. **Direct moving-index divisor-switch:** structurally inapplicable (no Kloosterman sum).
6. **Reciprocal-Poisson/Weil/triangle:** output \(467/200\), excess \(27/40\).

The Poisson zero mode is power-safe: exponents \(149/100+\varepsilon\) and
\(63/50+\varepsilon\), pre-loss margin \(17/100\).  Restoring two raw log slots contributes
exactly \((\log T)^2\); allocating \(17/400\) each to epsilon and log-dominance leaves
margin \(17/200\).

The unresolved nonzero transformed family is equation (33) of the audit document.
No A1 discharge; frozen statuses unchanged.

---

## 34. A1 SQ4 finite Gauss transform

**Verdict: exact Gauss-square transform and Dirichlet inversion proved; the signed analytic moment remains open.**

`SQ4GaussSquareTransform.lean` proves, for every positive integer modulus \(q\):

\[
 \sum_{v\bmod q}^{*}\chi(v)^{-1}S(k\bar v,r;q)
 =G_q(\chi;k)G_q(\chi;r),
\]

and the full Dirichlet-character inversion of \(S(k\bar v,r;q)\).  For unit \(k,r\) the
shifted product is \(\chi(kr)^{-1}G_q(\chi;1)^2\); this is a Gauss square, so ordinary
orthogonality does not erase the phase.

The unit specialization cannot replace the full family: \(k\ne0\) does not imply \((k,p)=1\),
and the literal modulus \(p=u_1u_2m\) has shared prime factors requiring prime-power
stratification.

The remaining sufficient estimate is
\(|\mathfrak M_4(T,x)| \ll T^{48/25+\varepsilon}(\log T)^0\)
with all conductor/divisor strata and the joint source coefficient retained.
No A1 discharge; frozen statuses unchanged.

---

## 35. A1 SQ4 CRT/conductor strata

**Verdict: CRT factorization and conductor stratification proved; the coupled signed moment remains open.**

`SQ4CRTConductor.lean` proves CRT factorization of generalized shifted Gauss sums for
coprime moduli and the exact conductor formula: for primitive \(\chi^*\) modulo \(f\),
\(q=f\ell\):

\[
 G_q(\chi;t)=G_f(\chi^*;1)
 \sum_{\substack{s\mid\ell,\ s\mid t\\(\ell/s,f)=1}}
 \mu(\ell/s)\chi^*(\ell/s)s\,
 \overline{\chi^*(t/s)}.
\]

This covers nonunit shifts, shared primes, and nonreal complex characters.  The exact support
restriction \(f\mid\gcd(q/(q,k),q/(q,r))\) is proved.

For squarefree outer variables with \(g=(u_1,u_2)\): the Mobius sign cancels but \(g^2\)
remains in the modulus; \(u_1=u_2=2\) rules out CRT splitting over the displayed noncoprime
slots.

After (34), local conductor support is coupled to \(g^2abm\), both shifts, and the joint
weight.  Only bare Mobius signs factor locally.  The surviving estimate (35) is unchanged.
No A1 discharge; frozen statuses unchanged.

---

## 36. A1 SQ4 correlated-moment audit

**Verdict: audited fixed-family theorem classes finished (Blomer--Pascadi, KSWX, Pascadi all power-killed on their strata).  The four-sign level moment survives.**

The audit (`docs/audit/sq4_correlated_moment.md`) retains all four Mobius factors.

**Coefficient-blind classes finished:** one character Cauchy + large sieve gives \(199/100\),
excess \(33/100\).  Ideal joint square-root in \((k,r)\) + triangle in outer variables gives
\(179/100\), excess \(13/100\).  The Parseval diagonal after Cauchy is the four-variable
constraint \(v_1v_2=w_1w_2\): coefficient energy is nonnegative, so a later blind large sieve
cannot recover the unsquared sign correlation.

**Primary theorem audit:**

| Theorem | Excess over budget / (SQ4-HB) |
|---|---|
| Blomer--Pascadi Thm 5.5 (preprint) | \(1123/1800\) / \(1429/1800\) |
| KSWX JLMS 2023 Thm 2.1 (favourable) | \(89/200\) / \(123/200\) |
| Pascadi Forum Math. Pi 2026 Cor. 5.11 | \(181/200\) / \(43/40\) (literal) |

For KSWX, the residual reciprocity phase is not the obstruction: replacing it by 1 with
admissible allocations \(\eta=1/20\), \(\varepsilon=1/20\) leaves margin \(11/200\).

The Ramanujan lift's full-family boundary: \(c_v(k)=0\) when \(g\nmid k\), so division
cannot represent nonsquarefree strata.

No published theorem has the full left-hand side.  No A1 discharge; frozen statuses unchanged.

---

## 37. A1 SQ4 published-theorem audit

**Verdict: all listed published-theorem classes power-killed on their literal or favourable strata.  Full source moment survives.**

`docs/audit/sq4_published_literature.md` and `SQ4PublishedLiterature.lean` check published
theorems against the conductor-stratified source moment.  Common target:
\(|\mathfrak M_4(T,x)| \ll T^{48/25+\varepsilon}(\log T)^0\).

Coefficient-blind / ideal square-root / Weil-triangle give \(121/50\), \(111/50\),
\(553/200\) before completion.  Shparlinski 2019 Thm 2.1 (favourable): \(2071/800\),
excess \(107/160\).  Thm 2.2 (good modulus, moment 2): \(1017/400+\varepsilon\),
excess \(249/400+\varepsilon\), does not control exceptional mass.

No published theorem found whose literal left-hand side contains the full signed moment.
This finishes only the listed classes.  No A1 discharge; frozen statuses unchanged.

---

## 38. B-2 actual-block centering bridge

**Verdict: finite centering bridge discharged; published RS application and seven other analytic blockers remain.**

`RSBlockMomentBridge.lean` proves for every \(0\le k\le4\) the exact alternating sum
relating centered to uncentered block moments.  `UncenteredRSBlockLimits F` assumes
convergence of raw block moments to formula-(27) contractions; from this and
`PrincipalCyclicBlock F`, the four centered limits in `BlockMomentLimits.moments` follow.

The constructor takes complex-alias summability/cancellation and `UncenteredRSBlockLimits`
as separate hypotheses.  Published RS application, cyclic-symbol admissibility, height
smoothing, log normalization, complex Poisson, and grid/end estimates remain open.  No
`BlockMomentLimits` instance constructed; no rung status changes.

---

## 39. A2 R1a allocation capacity

**Verdict: current `PrincipalCyclicBlock` interface proved uninhabitable for both frozen families.  A surviving redesign must change at least one consumed semantic.**

`R1aAllocationNoGo.lean` derives a contradiction from the actual `PrincipalCyclicBlock`
fields, with no common-lattice or alias-free assumption.  At one sufficiently large height:
full-energy reconstruction gives \(W_T=\sigma\ell(T)A\); the energy-ratio limit gives
\(E_T>(2/5)W_T\); degree-one translated-product gives active local mass >= 99/100.  Exact
scaling and the frozen profile cap give
\(\operatorname{mass}_T E_T\leq \mu\ell(T)p\,v(0)\).  These contradict the exact rational
gaps \(\mu p v(0) < (99/100)(2/5)\sigma A\) for both families.

Lean proves:

```text
F : Family14999 Z  ->  not PrincipalCyclicBlock F
F : Family19999 Z  ->  not PrincipalCyclicBlock F.
```

The conditional R-8657/8686/9383/9506 headline declarations are unchanged, but their
`PrincipalCyclicBlock` premise cannot be instantiated.  Changing periods, phases, channel
count, or oversampling cannot help.

---

## 40. B-4 eta superposition

**Verdict: finite common-support model killed at explicit witness (eta=3/4, T=625, n=899=29*31).  Actual coefficient route survives.**

`EtaSuperpositionObstruction.lean` formalizes a pointwise support obstruction.  Both ordered
factors \((29,31)\) and \((31,29)\) of 899 lie in the balanced box \([25,50]^2\), so the
balanced-box coefficient is exactly two.  No divisor of 899 lies in the asymmetric short box
\([5,10]\), so every finite signed sum of Dirichlet convolutions with first factors in that
box vanishes at 899.

This is a theorem about an exact finite support model, not the actual terminal Heath--Brown
coefficient.  `(EF_eta)` is neither proved nor disproved.

For retained balanced variables, the positive progression majorant still exceeds trace by
exactly `eta` in `PQ` and `eta - 1/2` in `PH`.  The surviving target is

\[
 |R_{\rm HD}(Y,T,\eta)|
   \ll_{\eta,\mathcal W}Y(\log T)^C,\qquad C<1.
\]

The threshold `C < 1` is the literal prime-dyadic budget; the generous recombined threshold
would be `C < 2`.  Neither is proved.  No `EF_eta` discharge or frozen-rung status change.
