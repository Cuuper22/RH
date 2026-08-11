/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/PreMajorantDI.lean

Exact power-exponent audit for a narrowly defined one-shot treatment of the
actual-scale nonzero-frequency sum before the run-12 progression majorant.
On each side, first collapse the two Moebius slots into one arbitrary outer
coefficient.  Drappeau 2017, Theorem 2.1 then gives a direct one-shot route.
The module also records the arithmetic substitution that would result from a
proposed application of Pascadi 2025, Theorem 10.3 after completing the short
smooth variable.

The direct Drappeau route produces power exponent 179/100, exceeding the trace
exponent 143/100 by 9/25.  The Pascadi substitution has the same arithmetic
output, but it is not an analytic route: literal completion produces
`S(k*a^{-1}, signed-n; q)`, not the required `S(m*a, signed-n; q)`, and no
support-preserving reindex has been proved.  This file formalizes exponents
only, not either published analytic theorem or the missing reindex.
-/
import RH.Zeta85.Discharge.ActualScaleBBLR

noncomputable section

namespace RH.Zeta85.PreMajorantDI

/-! ## Source scales and the collapsed coefficient norm -/

/-- The target trace exponent `1 + 43/100`. -/
def traceExponent : ℝ := 143 / 100

/-- Exponent of each collapsed two-Moebius outer variable `a,b`. -/
def outerExponent : ℝ := 43 / 100

/-- Exponent of each short smooth variable `m1,n1`. -/
def innerShortExponent : ℝ := 2 / 5

/-- Exponent of each long smooth variable `m2,n2`. -/
def innerLongExponent : ℝ := 3 / 5

/-- Exponent of the shift variable `h`. -/
def shiftExponent : ℝ := 43 / 100

/-- Exponent of the nonzero-frequency cutoff `L`. -/
def frequencyExponent : ℝ := 23 / 100

/-- Exponent of the collapsed positive numerator `n = |ell|*h`. -/
def numeratorProductExponent : ℝ := frequencyExponent + shiftExponent

/-- Physical exponent of the source Fourier variable `x`. -/
def physicalXExponent : ℝ := -(23 / 100)

/-- Power part of the natural `L2` upper bound for the coefficient indexed by
`(n,r,s)`, after the three pair-products have been collapsed. -/
def oneOuterCoefficientL2Exponent : ℝ := outerExponent / 2

/-- Power part of the natural `L2` upper bound for `n = |ell|*h`. -/
def numeratorCoefficientL2Exponent : ℝ := numeratorProductExponent / 2

/-- Power part of the natural `L2` upper bound for the coefficient indexed by
`(n,r,s)`, after the three pair-products have been collapsed. -/
def collapsedCoefficientL2Exponent : ℝ :=
  numeratorCoefficientL2Exponent + 2 * oneOuterCoefficientL2Exponent

/-- The source scales agree with the already-audited actual-scale block. -/
theorem source_scales_exact :
    traceExponent = RH.Zeta85.ActualScaleBBLR.traceExponent ∧
      outerExponent = 43 / 100 ∧
      innerShortExponent = 2 / 5 ∧
      innerLongExponent = 3 / 5 ∧
      shiftExponent = 43 / 100 ∧
      frequencyExponent = 23 / 100 ∧
      numeratorProductExponent = 33 / 50 ∧
      physicalXExponent = -(23 / 100) := by
  norm_num [traceExponent, RH.Zeta85.ActualScaleBBLR.traceExponent,
    RH.Zeta85.ActualScaleBBLR.eta, outerExponent, innerShortExponent,
    innerLongExponent, shiftExponent, frequencyExponent,
    numeratorProductExponent, physicalXExponent]

/-- Exact power exponent of the natural collapsed coefficient `L2` bound.
Logarithmic factors and the theorem's positive epsilon loss are deliberately
separate from this power calculation. -/
theorem collapsed_coefficient_L2_exact :
    oneOuterCoefficientL2Exponent = 43 / 200 ∧
      numeratorCoefficientL2Exponent = 33 / 100 ∧
      collapsedCoefficientL2Exponent = 19 / 25 := by
  norm_num [oneOuterCoefficientL2Exponent, numeratorCoefficientL2Exponent,
    collapsedCoefficientL2Exponent, numeratorProductExponent,
    frequencyExponent, shiftExponent, outerExponent]

/-! ## Drappeau 2017, Theorem 2.1: direct incomplete-sum route -/

/-- Drappeau's smooth modulus variable `c=n1`. -/
def drappeauC : ℝ := innerShortExponent

/-- Drappeau's smooth inverse variable `d=m1`. -/
def drappeauD : ℝ := innerShortExponent

/-- Drappeau's coefficient numerator variable `n=|ell|h`. -/
def drappeauN : ℝ := numeratorProductExponent

/-- Drappeau's outer inverse factor `r=a`. -/
def drappeauR : ℝ := outerExponent

/-- Drappeau's outer modulus factor `s=b`. -/
def drappeauS : ℝ := outerExponent

/-- Power exponent of `CS(RS+N)(C+RD)`, the first term of `K^2` at `q=1`. -/
def drappeauKSquaredTermOne : ℝ :=
  drappeauC + drappeauS +
    max (drappeauR + drappeauS) drappeauN +
    max drappeauC (drappeauR + drappeauD)

/-- Power exponent of `C^2 D S sqrt((RS+N)R)`, the second term of `K^2`. -/
def drappeauKSquaredTermTwo : ℝ :=
  2 * drappeauC + drappeauD + drappeauS +
    (max (drappeauR + drappeauS) drappeauN + drappeauR) / 2

/-- Power exponent of `D^2 N R S^{-1}`, the third term of `K^2`. -/
def drappeauKSquaredTermThree : ℝ :=
  2 * drappeauD + drappeauN + drappeauR - drappeauS

/-- Power exponent of Drappeau's `K`. -/
def drappeauKExponent : ℝ :=
  max drappeauKSquaredTermOne
    (max drappeauKSquaredTermTwo drappeauKSquaredTermThree) / 2

/-- Fixed-`x` power exponent supplied by the direct theorem application. -/
def drappeauFixedXExponent : ℝ :=
  drappeauKExponent + collapsedCoefficientL2Exponent

/-- Power exponent after integrating the fixed-`x` absolute bound. -/
def drappeauIntegratedExponent : ℝ :=
  drappeauFixedXExponent + physicalXExponent

/-- The three exact terms in Drappeau's `K^2`. -/
theorem drappeau_K_squared_terms_exact :
    drappeauKSquaredTermOne = 63 / 25 ∧
      drappeauKSquaredTermTwo = 91 / 40 ∧
      drappeauKSquaredTermThree = 73 / 50 := by
  norm_num [drappeauKSquaredTermOne, drappeauKSquaredTermTwo,
    drappeauKSquaredTermThree, drappeauC, drappeauD, drappeauN,
    drappeauR, drappeauS, innerShortExponent, numeratorProductExponent,
    frequencyExponent, shiftExponent, outerExponent, max_eq_left]

/-- The first term dominates `K^2`, so `K` has exponent `63/50`. -/
theorem drappeau_K_exact : drappeauKExponent = 63 / 50 := by
  norm_num [drappeauKExponent, drappeauKSquaredTermOne,
    drappeauKSquaredTermTwo, drappeauKSquaredTermThree, drappeauC,
    drappeauD, drappeauN, drappeauR, drappeauS, innerShortExponent,
    numeratorProductExponent, frequencyExponent, shiftExponent, outerExponent,
    max_eq_left]

/-- The direct route gives `101/50` at fixed `x` and `179/100` after the
physical `x`-integration. -/
theorem drappeau_route_exact :
    drappeauFixedXExponent = 101 / 50 ∧
      drappeauIntegratedExponent = 179 / 100 := by
  norm_num [drappeauFixedXExponent, drappeauIntegratedExponent,
    drappeauKExponent, drappeauKSquaredTermOne,
    drappeauKSquaredTermTwo, drappeauKSquaredTermThree, drappeauC,
    drappeauD, drappeauN, drappeauR, drappeauS, innerShortExponent,
    collapsedCoefficientL2Exponent, oneOuterCoefficientL2Exponent,
    numeratorCoefficientL2Exponent, numeratorProductExponent,
    frequencyExponent, shiftExponent, outerExponent, physicalXExponent,
    max_eq_left]

/-! ## Pascadi 2025, Theorem 10.3: unresolved completion candidate -/

/-- A finite regression illustrating the literal outer-factor mismatch.  In
`ZMod 5`, the source completion places `a⁻¹ = 3` in the first Kloosterman
argument when `a = 2`, whereas the attempted direct Pascadi map uses `r=a=2`.
This example only refutes that literal identification; it says nothing about
a new modulus-dependent reindex or a different theorem. -/
theorem zmod_five_literal_outer_mismatch :
    (2 : ZMod 5)⁻¹ = 3 ∧ (2 : ZMod 5)⁻¹ ≠ 2 := by
  have hinv : (2 : ZMod 5)⁻¹ = 3 :=
    ZMod.inv_eq_of_mul_eq_one 5 2 3 (by reduce_mod_char)
  constructor
  · exact hinv
  · rw [hinv]
    intro h
    have hv := congrArg ZMod.val h
    have hthree : (3 : ZMod 5).val = 3 :=
      ZMod.val_natCast_of_lt (by norm_num)
    have htwo : (2 : ZMod 5).val = 2 :=
      ZMod.val_natCast_of_lt (by norm_num)
    rw [hthree, htwo] at hv
    norm_num at hv

/-- Pascadi's Kloosterman-modulus variable `c=n1`. -/
def pascadiC : ℝ := innerShortExponent

/-- Pascadi's Fourier-dual variable after completing `m1` modulo `b*n1`. -/
def pascadiM : ℝ := outerExponent + innerShortExponent - innerShortExponent

/-- Pascadi's coefficient numerator variable `n=|ell|h`. -/
def pascadiN : ℝ := numeratorProductExponent

/-- Pascadi's first outer variable `r=a`. -/
def pascadiR : ℝ := outerExponent

/-- Pascadi's second outer variable `s=b`. -/
def pascadiS : ℝ := outerExponent

/-- Power prefactor `D/(SC)` from completing the original `m1` sum. -/
def completionPrefactorExponent : ℝ :=
  innerShortExponent - pascadiS - pascadiC

/-- Exponent of `CS sqrt R`. -/
def pascadiCSsqrtRExponent : ℝ := pascadiC + pascadiS + pascadiR / 2

/-- Exponent of `sqrt(MN)`. -/
def pascadiSqrtMNExponent : ℝ := (pascadiM + pascadiN) / 2

/-- Exponent of `C sqrt(SM)`. -/
def pascadiCSqrtSMExponent : ℝ := pascadiC + (pascadiS + pascadiM) / 2

/-- Exponent of `C sqrt(SN)`. -/
def pascadiCSqrtSNExponent : ℝ := pascadiC + (pascadiS + pascadiN) / 2

/-- Denominator exponent inside Pascadi's exceptional-spectrum ratio. -/
def pascadiThetaDenominatorExponent : ℝ :=
  max pascadiM (pascadiR + pascadiS) +
    max pascadiN (pascadiR + pascadiS) / 2

/-- Power inside the parenthesis of the `theta_max` factor. -/
def pascadiThetaRatioExponent : ℝ :=
  pascadiCSsqrtRExponent - pascadiThetaDenominatorExponent

/-- Worst power contribution of the theta factor.  A negative inner ratio
gives a bounded `1 + T^ratio`, hence exponent zero. -/
def pascadiThetaContributionExponent : ℝ :=
  (7 / 32 : ℝ) * max 0 pascadiThetaRatioExponent

/-- Power exponent of the final rational factor in Theorem 10.3. -/
def pascadiRationalFactorExponent : ℝ :=
  max pascadiCSsqrtRExponent
      (max pascadiSqrtMNExponent pascadiCSqrtSMExponent) +
    max pascadiCSsqrtRExponent
      (max pascadiSqrtMNExponent pascadiCSqrtSNExponent) -
    max pascadiCSsqrtRExponent pascadiSqrtMNExponent

/-- Exponent of `sqrt(MRS)`. -/
def pascadiSqrtMRSExponent : ℝ :=
  (pascadiM + pascadiR + pascadiS) / 2

/-- Candidate complete-sum exponent before the completion prefactor.  This is
an arithmetic substitution only; the required Kloosterman form has not been
derived from the source completion. -/
def pascadiCandidateCompleteExponent : ℝ :=
  pascadiThetaContributionExponent + pascadiSqrtMRSExponent +
    collapsedCoefficientL2Exponent + pascadiRationalFactorExponent

/-- Candidate fixed-`x` exponent after the formal completion prefactor. -/
def pascadiCandidateFixedXExponent : ℝ :=
  completionPrefactorExponent + pascadiCandidateCompleteExponent

/-- Candidate exponent after the physical `x`-integration. -/
def pascadiCandidateIntegratedExponent : ℝ :=
  pascadiCandidateFixedXExponent + physicalXExponent

/-- The completed variable has exponent `43/100`, and completion costs the
prefactor `T^(-43/100)`. -/
theorem pascadi_completion_exact :
    pascadiM = 43 / 100 ∧
      completionPrefactorExponent = -(43 / 100) := by
  norm_num [pascadiM, completionPrefactorExponent, pascadiS, pascadiC,
    outerExponent, innerShortExponent]

/-- Exact components of Pascadi's optimized DI bound. -/
theorem pascadi_components_exact :
    pascadiCSsqrtRExponent = 209 / 200 ∧
      pascadiSqrtMNExponent = 109 / 200 ∧
      pascadiCSqrtSMExponent = 83 / 100 ∧
      pascadiCSqrtSNExponent = 189 / 200 ∧
      pascadiSqrtMRSExponent = 129 / 200 := by
  norm_num [pascadiCSsqrtRExponent, pascadiSqrtMNExponent,
    pascadiCSqrtSMExponent, pascadiCSqrtSNExponent,
    pascadiSqrtMRSExponent, pascadiC, pascadiM, pascadiN, pascadiR,
    pascadiS, innerShortExponent, numeratorProductExponent,
    frequencyExponent, shiftExponent, outerExponent]

/-- The theta ratio is `T^(-49/200)`, so the exceptional-spectrum factor is
bounded and contributes power exponent zero, including at `theta_max=7/32`. -/
theorem pascadi_theta_inactive :
    pascadiThetaDenominatorExponent = 129 / 100 ∧
      pascadiThetaRatioExponent = -(49 / 200) ∧
      pascadiThetaRatioExponent < 0 ∧
      pascadiThetaContributionExponent = 0 := by
  norm_num [pascadiThetaDenominatorExponent, pascadiThetaRatioExponent,
    pascadiThetaContributionExponent, pascadiCSsqrtRExponent, pascadiC,
    pascadiM, pascadiN, pascadiR, pascadiS, innerShortExponent,
    numeratorProductExponent, frequencyExponent, shiftExponent,
    outerExponent, max_eq_left, max_eq_right]

/-- Both numerator factors and the denominator are dominated by `CS sqrt R`,
so the rational factor has exponent `209/200`. -/
theorem pascadi_rational_factor_exact :
    pascadiRationalFactorExponent = 209 / 200 := by
  norm_num [pascadiRationalFactorExponent, pascadiCSsqrtRExponent,
    pascadiSqrtMNExponent, pascadiCSqrtSMExponent,
    pascadiCSqrtSNExponent, pascadiC, pascadiM, pascadiN, pascadiR,
    pascadiS, innerShortExponent, numeratorProductExponent,
    frequencyExponent, shiftExponent, outerExponent, max_eq_left]

/-- If the missing source-faithful reindex were supplied, the arithmetic
substitution into the published bound would give `49/20`, then `101/50`, then
`179/100`.  This theorem asserts no applicability of the analytic estimate. -/
theorem pascadi_candidate_arithmetic_exact :
    pascadiCandidateCompleteExponent = 49 / 20 ∧
      pascadiCandidateFixedXExponent = 101 / 50 ∧
      pascadiCandidateIntegratedExponent = 179 / 100 := by
  norm_num [pascadiCandidateCompleteExponent, pascadiCandidateFixedXExponent,
    pascadiCandidateIntegratedExponent, pascadiThetaContributionExponent,
    pascadiThetaRatioExponent, pascadiThetaDenominatorExponent,
    pascadiRationalFactorExponent, pascadiSqrtMRSExponent,
    pascadiCSsqrtRExponent, pascadiSqrtMNExponent,
    pascadiCSqrtSMExponent, pascadiCSqrtSNExponent,
    completionPrefactorExponent, collapsedCoefficientL2Exponent,
    oneOuterCoefficientL2Exponent, numeratorCoefficientL2Exponent, pascadiC,
    pascadiM, pascadiN, pascadiR, pascadiS, innerShortExponent,
    numeratorProductExponent, frequencyExponent, shiftExponent,
    outerExponent, physicalXExponent, max_eq_left, max_eq_right]

/-! ## Exact finish/kill statement for the direct one-shot class -/

/-- The unresolved Pascadi substitution happens to have the same arithmetic
output as the valid direct parameter substitution.  This is not an
applicability theorem. -/
theorem pascadi_candidate_arithmetic_matches_direct :
    drappeauIntegratedExponent = pascadiCandidateIntegratedExponent ∧
      drappeauIntegratedExponent = 179 / 100 := by
  obtain ⟨_, hd⟩ := drappeau_route_exact
  obtain ⟨_, _, hp⟩ := pascadi_candidate_arithmetic_exact
  constructor <;> linarith

/-- The direct Drappeau one-shot chain exceeds trace by exactly `9/25`. -/
theorem drappeau_oneShot_excess_exact :
    drappeauIntegratedExponent - traceExponent = 9 / 25 := by
  obtain ⟨_, hd⟩ := drappeau_route_exact
  norm_num [traceExponent] at hd ⊢
  linarith

/-- Therefore the direct upper-bound chain is not trace-grade, even before the
theorem's positive epsilon loss and before any logarithmic loss. -/
theorem drappeau_oneShot_not_traceGrade :
    traceExponent < drappeauIntegratedExponent := by
  have hd := drappeau_oneShot_excess_exact
  linarith

/-- Adding arbitrary nonnegative power slack cannot repair the direct route. -/
theorem drappeau_oneShot_not_traceGrade_with_slack
    {slack : ℝ} (hslack : 0 ≤ slack) :
    traceExponent < drappeauIntegratedExponent + slack := by
  have hd := drappeau_oneShot_not_traceGrade
  linarith

end RH.Zeta85.PreMajorantDI

end
