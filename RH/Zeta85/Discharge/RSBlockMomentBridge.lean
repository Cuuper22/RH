/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSPairIntegrals
import RH.Zeta85.Discharge.QuarticTransfer
import Zeta23.Poisson.ComplexDecay
import Zeta23.Poisson.Complex
import Zeta23.Poisson.ComplexAlias
import RH.Zeta85.Discharge.ComplexAliasBridge

/-!
# Actual-block centering bridge for the Rudnick--Sarnak route

The published Rudnick--Sarnak main term and the contraction calculations are
naturally uncentered, whereas `BlockMomentLimits` is stated for the centered
principal-block traces.  This file proves the finite binomial centering and
passes it through limits through degree four.

It does not prove any analytic passage from the actual block to the cyclic
main term.  That passage is retained verbatim in `UncenteredRSBlockLimits`,
together with eventual positivity of the block dimension.  The complex
Poisson clauses remain separate hypotheses of the final constructor.
-/

open Filter Matrix MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace RH.Zeta85.RSBlockMomentBridge

open Zeta23 RHLinalg RSReduction TrimmedMoment
open RSPairIntegrals TopHatMoments

/-- Normalized uncentered trace moment of the literal distinguished block. -/
def uncenteredBlockMoment {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (k : ℕ) (T : ℝ) : ℝ :=
  rtrace ((F.block T) ^ k) / (F.blockDim T : ℝ)

/-- The same normalized moment after all finite block indices have been
commuted inside each ordered zero tuple. -/
def zeroKernelBlockMoment {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (k : ℕ) (T : ℝ) : ℝ :=
  if k = 0 then uncenteredBlockMoment F 0 T
  else QuarticTransfer.zeroKernelRawTrace F k T / (F.blockDim T : ℝ)

/-- The literal block moment and the zero-tuple-first moment are exactly
equal in every active degree, at every height. -/
theorem uncenteredBlockMoment_eq_zeroKernelBlockMoment
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {k : ℕ}
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    uncenteredBlockMoment F k = zeroKernelBlockMoment F k := by
  funext T
  unfold uncenteredBlockMoment zeroKernelBlockMoment
  rw [if_neg (Nat.ne_of_gt hk1)]
  rw [QuarticTransfer.rtrace_block_pow_eq_zeroKernelRawTrace hk1 hk4]

/-- The exact analytic remainder after the cyclic contractions have been
evaluated: the actual uncentered block moments converge to formula (27).

This predicate deliberately does not include complex Poisson summability or
cancellation, which are independent fields of `BlockMomentLimits`. -/
structure UncenteredRSBlockLimits {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  moments : ∀ k : ℕ, k ≤ 4 →
    Tendsto (uncenteredBlockMoment F k) atTop
      (nhds (uncenteredContractionMoment (topHatR3Terms p) μ k))

/-- Analytically equivalent sum-first form of the actual-block limit.  Its
active degrees are now expressed directly as ordered zero-tuple kernels. -/
structure ZeroKernelRSBlockLimits
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  moments : ∀ k : ℕ, k ≤ 4 →
    Tendsto (zeroKernelBlockMoment F k) atTop
      (nhds (uncenteredContractionMoment (topHatR3Terms p) μ k))

theorem UncenteredRSBlockLimits.toZeroKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : UncenteredRSBlockLimits F) : ZeroKernelRSBlockLimits F where
  moments k hk4 := by
    by_cases hk0 : k = 0
    · subst k
      change Tendsto (uncenteredBlockMoment F 0) atTop
        (nhds (uncenteredContractionMoment (topHatR3Terms p) μ 0))
      exact h.moments 0 hk4
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      rw [← uncenteredBlockMoment_eq_zeroKernelBlockMoment hk1 hk4]
      exact h.moments k hk4

/-- Degree zero is definitional, so the zero-tuple-first limits reconstruct
the complete uncentered interface used by the centering bridge. -/
theorem UncenteredRSBlockLimits.ofZeroKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : ZeroKernelRSBlockLimits F) : UncenteredRSBlockLimits F where
  moments k hk4 := by
    by_cases hk0 : k = 0
    · subst k
      change Tendsto (zeroKernelBlockMoment F 0) atTop
        (nhds (uncenteredContractionMoment (topHatR3Terms p) μ 0))
      exact h.moments 0 hk4
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      rw [uncenteredBlockMoment_eq_zeroKernelBlockMoment hk1 hk4]
      exact h.moments k hk4

private theorem topHat_pow_integrable {p : ℝ} {k : ℕ}
    (hk : k ≠ 0) :
    Integrable (fun x : ℝ => topHat p x ^ k) := by
  have heq : (fun x : ℝ => topHat p x ^ k) =
      (topHatSupport p).indicator (fun _ => (1 / p) ^ k) := by
    funext x
    by_cases hx : x ∈ topHatSupport p
    · simp [topHat, hx]
    · simp [topHat, hx, hk]
  rw [heq]
  exact (integrableOn_const (s := topHatSupport p)
    (by simp [topHatSupport, Real.volume_Icc])).integrable_indicator
      measurableSet_Icc

theorem localProfile_power_integral_tendsto_topHat
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hblock : PrincipalCyclicBlock F)
    (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    Tendsto (fun T => ∫ x : ℝ, F.localProfile T x ^ k) atTop
      (nhds (∫ x : ℝ, topHat p x ^ k)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rw [← Filter.eventually_atTop]
  filter_upwards [hblock.windows_smooth,
    hblock.translated_products_locally_uniform k hk1 hk4 1 (ε / 2)
      (by norm_num) hε2] with T hsmooth hprod
  let shift : Fin k → ℝ := fun _ => 0
  have hshift : ∀ a, |shift a| ≤ (1 : ℝ) := by
    intro a
    simp [shift]
  have h := hprod shift hshift
  have hdiffInt : Integrable (fun x : ℝ =>
      F.localProfile T x ^ k - topHat p x ^ k) := by
    have hlocal : Continuous (F.localProfile T) := by
      unfold QuarticGramFamily.localProfile
      dsimp
      fun_prop
    have htop : AEStronglyMeasurable (fun x : ℝ => topHat p x ^ k) := by
      apply AEStronglyMeasurable.pow
      unfold topHat topHatSupport
      exact (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
    have hdiff : AEStronglyMeasurable (fun x : ℝ =>
        F.localProfile T x ^ k - topHat p x ^ k) :=
      (hlocal.aestronglyMeasurable.pow k).sub htop
    apply (integrable_norm_iff hdiff).mp
    have hfun : (fun x : ℝ =>
        |∏ a : Fin k, F.localProfile T (x + shift a) -
          ∏ a : Fin k, topHat p (x + shift a)|) =
        fun x : ℝ => |F.localProfile T x ^ k - topHat p x ^ k| := by
      funext x
      simp [shift, Finset.prod_const]
    simp only [Real.norm_eq_abs]
    rw [← hfun]
    exact h.1
  have htopInt := topHat_pow_integrable (p := p) (k := k)
    (Nat.ne_of_gt hk1)
  have hlocalInt : Integrable (fun x : ℝ => F.localProfile T x ^ k) := by
    have hadd := hdiffInt.add htopInt
    apply hadd.congr
    filter_upwards [] with x
    change (F.localProfile T x ^ k - topHat p x ^ k) +
      topHat p x ^ k = F.localProfile T x ^ k
    ring
  rw [Real.dist_eq, ← integral_sub hlocalInt htopInt]
  calc
    |∫ x : ℝ, F.localProfile T x ^ k - topHat p x ^ k| ≤
        ∫ x : ℝ, |F.localProfile T x ^ k - topHat p x ^ k| :=
      abs_integral_le_integral_abs
    _ ≤ ε / 2 := by
      simpa [shift, Finset.prod_const] using h.2
    _ < ε := by linarith

private theorem topHat_cyclicProduct_integrable
    {p : ℝ} (hp : 0 < p) {k : ℕ} (hk : 1 ≤ k)
    (mu : ℝ) (xi : Fin k → ℝ) :
    Integrable (fun x : ℝ =>
      ∏ a : Fin k, topHat p
        (x + cyclicPartialSum xi a / mu)) := by
  let a0 : Fin k := ⟨0, hk⟩
  let rest : Finset (Fin k) := Finset.univ.erase a0
  have htop : Integrable (topHat p) := by
    simpa only [pow_one] using
      (topHat_pow_integrable (p := p) (k := 1) (by norm_num))
  have hmeas (a : Fin k) : AEStronglyMeasurable (fun x : ℝ =>
      topHat p (x + cyclicPartialSum xi a / mu)) := by
    unfold topHat topHatSupport
    exact ((measurable_const.indicator measurableSet_Icc).comp
      (by fun_prop)).aestronglyMeasurable
  have hrestMeas : AEStronglyMeasurable (fun x : ℝ =>
      ∏ a ∈ rest, topHat p
        (x + cyclicPartialSum xi a / mu)) :=
    Finset.aestronglyMeasurable_fun_prod rest
      (fun a _ => hmeas a)
  have hfactor (z : ℝ) : ‖topHat p z‖ ≤ 1 / p := by
    by_cases hz : z ∈ topHatSupport p
    · simp [topHat, hz, abs_of_pos hp]
    · simp [topHat, hz, le_of_lt hp]
  have hrestBound : ∀ᵐ x : ℝ,
      ‖∏ a ∈ rest, topHat p
        (x + cyclicPartialSum xi a / mu)‖ ≤
          (1 / p) ^ rest.card := by
    filter_upwards [] with x
    rw [norm_prod]
    calc
      (∏ a ∈ rest, ‖topHat p
          (x + cyclicPartialSum xi a / mu)‖) ≤
          ∏ _a ∈ rest, (1 / p) := by
        apply Finset.prod_le_prod
        · intro a ha
          exact norm_nonneg _
        · intro a ha
          exact hfactor _
      _ = (1 / p) ^ rest.card := by simp
  have hmul := htop.bdd_mul hrestMeas hrestBound
  apply hmul.congr
  filter_upwards [] with x
  change (∏ a ∈ rest, topHat p
      (x + cyclicPartialSum xi a / mu)) * topHat p x = _
  rw [mul_comm]
  have ha0 : cyclicPartialSum xi a0 = 0 := by
    unfold cyclicPartialSum
    apply Finset.sum_eq_zero
    intro j hj
    have hjlt : j < a0 := (Finset.mem_filter.mp hj).2
    have : ¬j < a0 := by
      intro h
      change j.val < 0 at h
      omega
    exact (this hjlt).elim
  have herase := Finset.mul_prod_erase Finset.univ
    (fun a : Fin k => topHat p
      (x + cyclicPartialSum xi a / mu)) (Finset.mem_univ a0)
  rw [ha0, zero_div, add_zero] at herase
  simpa only [rest] using herase

theorem eventually_weightedCyclicSymbol_close_topHat
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hblock : PrincipalCyclicBlock F)
    (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ xi : Fin k → ℝ,
      (∀ a, |xi a| ≤ R) →
        ‖weightedCyclicSymbol μ (F.localProfile T) xi -
          weightedCyclicSymbol μ (topHat p) xi‖ ≤ ε := by
  have hmu : 0 < μ := hblock.bandwidth_pos
  let shiftRadius : ℝ := (k : ℝ) * R / μ + 1
  have hshiftRadius : 0 < shiftRadius := by
    dsimp [shiftRadius]
    positivity
  have hprofileEps : 0 < ε / μ := div_pos hε hmu
  filter_upwards [hblock.windows_smooth,
    hblock.translated_products_locally_uniform k hk1 hk4
      shiftRadius (ε / μ) hshiftRadius hprofileEps] with T hsmooth hprod
  intro xi hxi
  let shift : Fin k → ℝ := fun a => cyclicPartialSum xi a / μ
  have hpartial (a : Fin k) :
      |cyclicPartialSum xi a| ≤ (k : ℝ) * R := by
    let s : Finset (Fin k) := Finset.univ.filter fun j => j < a
    have hs : s ⊆ Finset.univ := Finset.filter_subset _ _
    have hcardNat : s.card ≤ k := by
      simpa [s] using Finset.card_le_card hs
    have hcard : (s.card : ℝ) ≤ k := by exact_mod_cast hcardNat
    unfold cyclicPartialSum
    change |∑ j ∈ s, xi j| ≤ (k : ℝ) * R
    calc
      |∑ j ∈ s, xi j| ≤ ∑ j ∈ s, |xi j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ s, R := by
        apply Finset.sum_le_sum
        intro j hj
        exact hxi j
      _ = (s.card : ℝ) * R := by simp [mul_comm]
      _ ≤ (k : ℝ) * R :=
        mul_le_mul_of_nonneg_right hcard hR
  have hshift : ∀ a, |shift a| ≤ shiftRadius := by
    intro a
    rw [show shift a = cyclicPartialSum xi a / μ by rfl,
      abs_div, abs_of_pos hmu]
    have hdiv := div_le_div_of_nonneg_right (hpartial a) (le_of_lt hmu)
    dsimp [shiftRadius]
    linarith
  have h := hprod shift hshift
  let localProduct : ℝ → ℝ := fun x =>
    ∏ a : Fin k, F.localProfile T (x + shift a)
  let sharpProduct : ℝ → ℝ := fun x =>
    ∏ a : Fin k, topHat p (x + shift a)
  have hsharpInt : Integrable sharpProduct := by
    simpa only [sharpProduct, shift] using
      (topHat_cyclicProduct_integrable hblock.fill_pos hk1 μ xi)
  have hdiffInt : Integrable (fun x => localProduct x - sharpProduct x) := by
    have hlocal : Continuous localProduct := by
      dsimp [localProduct]
      unfold QuarticGramFamily.localProfile
      dsimp
      fun_prop
    have hsharp : AEStronglyMeasurable sharpProduct := by
      dsimp [sharpProduct]
      apply Finset.aestronglyMeasurable_fun_prod Finset.univ
      intro a ha
      unfold topHat topHatSupport
      exact ((measurable_const.indicator measurableSet_Icc).comp
        (by fun_prop)).aestronglyMeasurable
    have hdiff : AEStronglyMeasurable
        (fun x => localProduct x - sharpProduct x) :=
      hlocal.aestronglyMeasurable.sub hsharp
    apply (integrable_norm_iff hdiff).mp
    simp only [Real.norm_eq_abs]
    simpa only [localProduct, sharpProduct] using h.1
  have hlocalInt : Integrable localProduct := by
    have hadd := hdiffInt.add hsharpInt
    apply hadd.congr
    filter_upwards [] with x
    change (localProduct x - sharpProduct x) + sharpProduct x = localProduct x
    ring
  have hintegral :
      |(∫ x, localProduct x) - ∫ x, sharpProduct x| ≤ ε / μ := by
    rw [← integral_sub hlocalInt hsharpInt]
    calc
      |∫ x, localProduct x - sharpProduct x| ≤
          ∫ x, |localProduct x - sharpProduct x| :=
        abs_integral_le_integral_abs
      _ ≤ ε / μ := by
        simpa only [localProduct, sharpProduct] using h.2
  unfold weightedCyclicSymbol
  change ‖((μ * ∫ x, localProduct x : ℝ) : ℂ) -
      ((μ * ∫ x, sharpProduct x : ℝ) : ℂ)‖ ≤ ε
  rw [← Complex.ofReal_sub, Complex.norm_real, ← mul_sub, Real.norm_eq_abs, abs_mul,
    abs_of_pos hmu]
  calc
    μ * |(∫ x, localProduct x) - ∫ x, sharpProduct x| ≤
        μ * (ε / μ) := mul_le_mul_of_nonneg_left hintegral (le_of_lt hmu)
    _ = ε := by field_simp [ne_of_gt hmu]

private theorem rtrace_one_fin {d : ℕ} :
    rtrace (1 : Matrix (Fin d) (Fin d) ℂ) = d := by
  simp [rtrace, Matrix.trace]

/-- At every positive block dimension, finite matrix centering is exactly the
scalar binomial transform used in formula (28). -/
theorem centeredBlockMoment_eq_centeredTransform
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (k : ℕ) (hk : k ≤ 4) :
    F.centeredBlockMoment k T =
      centeredTransform (fun a => uncenteredBlockMoment F a T) k := by
  simp only [QuarticGramFamily.centeredBlockMoment, centeredTransform,
    uncenteredBlockMoment]
  interval_cases k
  · simp
  · rw [show (F.block T - 1) ^ 1 = F.block T ^ 1 - 1 by noncomm_ring,
      rtrace_sub]
    norm_num [Finset.sum_range_succ, Nat.choose, rtrace_one_fin]
    ring
  · rw [show (F.block T - 1) ^ 2 =
        F.block T ^ 2 - (F.block T + F.block T) + 1 by noncomm_ring,
      rtrace_add, rtrace_sub, rtrace_add]
    norm_num [Finset.sum_range_succ, Nat.choose, rtrace_one_fin]
    ring
  · rw [show (F.block T - 1) ^ 3 =
        F.block T ^ 3 -
          (F.block T ^ 2 + F.block T ^ 2 + F.block T ^ 2) +
          (F.block T + F.block T + F.block T) - 1 by noncomm_ring,
      rtrace_sub, rtrace_add, rtrace_sub, rtrace_add, rtrace_add,
      rtrace_add, rtrace_add]
    norm_num [Finset.sum_range_succ, Nat.choose, rtrace_one_fin]
    ring
  · rw [show (F.block T - 1) ^ 4 =
        F.block T ^ 4 -
          (F.block T ^ 3 + F.block T ^ 3 + F.block T ^ 3 + F.block T ^ 3) +
          (F.block T ^ 2 + F.block T ^ 2 + F.block T ^ 2 +
            F.block T ^ 2 + F.block T ^ 2 + F.block T ^ 2) -
          (F.block T + F.block T + F.block T + F.block T) + 1 by noncomm_ring,
      rtrace_add, rtrace_sub, rtrace_add, rtrace_sub, rtrace_add,
      rtrace_add, rtrace_add, rtrace_add, rtrace_add, rtrace_add,
      rtrace_add, rtrace_add, rtrace_add, rtrace_add]
    norm_num [Finset.sum_range_succ, Nat.choose, rtrace_one_fin, rtrace_add]
    ring

/-- The uncentered formula-(27) limits imply all centered formula-(21)
limits.  This is the formal finite-sum/Tendsto step; no RS, Poisson, height,
or finite-grid estimate is hidden in the proof. -/
theorem centered_moment_limits_of_fillBounds
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hp : 0 < p) (hp1 : p ≤ 1) (hraw : UncenteredRSBlockLimits F) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      Tendsto (F.centeredBlockMoment k) atTop
        (nhds (formula21Moment k μ p)) := by
  intro k hk1 hk4
  have hcenter : ∀ T,
      F.centeredBlockMoment k T =
        centeredTransform (fun a => uncenteredBlockMoment F a T) k := by
    intro T
    exact centeredBlockMoment_eq_centeredTransform F T k hk4
  rw [funext hcenter]
  have hlim : Tendsto
      (fun T => centeredTransform (fun a => uncenteredBlockMoment F a T) k)
      atTop
      (nhds (centeredTransform
        (uncenteredContractionMoment (topHatR3Terms p) μ) k)) := by
    unfold centeredTransform
    apply tendsto_finsetSum
    intro a ha
    exact (hraw.moments a
      (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp ha)) hk4)).const_mul _
  rw [topHat_centeredContraction_eq_formula21
    hp hp1 k hk1 hk4] at hlim
  exact hlim

/-- Compatibility wrapper for the older physical-window interface. -/
theorem centered_moment_limits
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hr1a : PrincipalCyclicBlock F) (hraw : UncenteredRSBlockLimits F) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      Tendsto (F.centeredBlockMoment k) atTop
        (nhds (formula21Moment k μ p)) :=
  centered_moment_limits_of_fillBounds
    hr1a.fill_pos hr1a.fill_le_one hraw

/-- The minimal RS route to the sum-first terminal premise.  It uses only
the literal block-density limit, the scalar fill bounds, and the uncentered
actual-block moment limits; no alias or physical-window fields enter. -/
theorem quarticTraceLowerBound_of_uncenteredRS
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hdim : BlockDimensionLimit F) (hraw : UncenteredRSBlockLimits F)
    (q : Quartic) :
    QuarticTransfer.FactoredZeroKernelQuarticLowerBound q F := by
  have hmom : BlockMomentConvergence F :=
    ⟨centered_moment_limits_of_fillBounds hp hp1 hraw⟩
  have hscore : QuarticTransfer.QuarticScoreConvergence q F :=
    QuarticTransfer.quarticScoreConvergence_of_moments hmom q
  exact
    (QuarticTransfer.weightedQuarticLimit_of_separate hdim hscore).toLowerBound.toTraceLowerBound.toUncentered.toCyclic.toZeroCyclic.toTuple.toKernel.toFactored

/-- Constructor for the existing R1b interface from the exact uncentered
actual-block limit plus the two independent complex-Poisson clauses. -/
theorem blockMomentLimits_of_uncenteredRS
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hr1a : PrincipalCyclicBlock F)
    (haliasSummable : ∀ᶠ T in atTop,
      ∀ ρ ∈ Z.ZIprime T, ∀ ρ' ∈ Z.ZIprime T,
        Summable (F.complexAliasFamily T (gammaOf ρ) (gammaOf ρ')))
    (haliasZero : ∀ᶠ T in atTop,
      ∀ ρ ∈ Z.ZIprime T, ∀ ρ' ∈ Z.ZIprime T,
        ∑' a, F.complexAliasFamily T (gammaOf ρ) (gammaOf ρ') a = 0)
    (hraw : UncenteredRSBlockLimits F) :
    BlockMomentLimits F where
  complex_aliases_summable_at_zeros := haliasSummable
  offRH_complex_poisson_at_zeros := haliasZero
  moments := centered_moment_limits hr1a hraw

end RH.Zeta85.RSBlockMomentBridge

end
