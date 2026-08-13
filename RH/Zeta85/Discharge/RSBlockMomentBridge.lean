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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Floor

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
open scoped BigOperators ContDiff Topology

noncomputable section

namespace RH.Zeta85.RSBlockMomentBridge

open Zeta23 RHLinalg RSReduction RSPairIntegrals TrimmedMoment

/-- A slowly improving diagonal can respect an arbitrary convergence
threshold in every fixed row.  This is the quantifier-order bridge needed
when a fixed-test asymptotic is combined with a test profile that itself
converges. -/
theorem exists_tendsto_slow_diagonal
    {E : Type*} [PseudoMetricSpace E]
    (f : ℕ → ℝ → E) (a : ℕ → E) (A : E)
    (hrow : ∀ n, Tendsto (f n) atTop (nhds (a n)))
    (ha : Tendsto a atTop (nhds A)) :
    ∃ stage : ℝ → ℕ,
      Tendsto stage atTop atTop ∧
      Tendsto (fun T => f (stage T) T) atTop (nhds A) := by
  have hrowThreshold : ∀ n : ℕ, ∃ B : ℝ, ∀ T : ℝ, B ≤ T →
      dist (f n T) (a n) < 1 / ((n : ℝ) + 1) := by
    intro n
    exact (Metric.tendsto_atTop.1 (hrow n))
      (1 / ((n : ℝ) + 1)) (by positivity)
  choose B hB using hrowThreshold
  have hnatThreshold : ∀ n : ℕ, ∃ N : ℕ,
      max (B n) (n : ℝ) < (N : ℝ) := by
    intro n
    exact exists_nat_gt (max (B n) (n : ℝ))
  choose N hN using hnatThreshold
  let stage : ℝ → ℕ := fun T =>
    Nat.findGreatest (fun n => (N n : ℝ) ≤ T) ⌈max T 0⌉₊
  have hstage : Tendsto stage atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro k
    filter_upwards [eventually_ge_atTop (max (N k : ℝ) 0)] with T hT
    have hNkT : (N k : ℝ) ≤ T :=
      le_trans (le_max_left _ _) hT
    have hkT : (k : ℝ) ≤ max T 0 := by
      exact le_trans
        (le_trans (le_max_right (B k) (k : ℝ)) (hN k).le)
        (le_trans hNkT (le_max_left _ _))
    have hkceil : k ≤ ⌈max T 0⌉₊ := by
      simpa only [Nat.ceil_natCast] using Nat.ceil_mono hkT
    change k ≤
      Nat.findGreatest (fun n => (N n : ℝ) ≤ T) ⌈max T 0⌉₊
    exact Nat.le_findGreatest hkceil hNkT
  have hselected : ∀ᶠ T in atTop, (N (stage T) : ℝ) ≤ T := by
    filter_upwards [eventually_ge_atTop (N 0 : ℝ)] with T hT
    change
      (N (Nat.findGreatest (fun n => (N n : ℝ) ≤ T) ⌈max T 0⌉₊) : ℝ) ≤ T
    exact Nat.findGreatest_spec
      (P := fun n => (N n : ℝ) ≤ T) (Nat.zero_le _) hT
  have hrowDiagonal : ∀ᶠ T in atTop,
      dist (f (stage T) T) (a (stage T)) <
        1 / ((stage T : ℝ) + 1) := by
    filter_upwards [hselected] with T hT
    apply hB (stage T) T
    exact le_trans
      (le_trans (le_max_left _ _) (hN (stage T)).le) hT
  have hbound :
      Tendsto (fun T => 1 / ((stage T : ℝ) + 1))
        atTop (nhds 0) := by
    change Tendsto
      ((fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ∘ stage)
      atTop (nhds 0)
    exact
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hstage
  have hdistance :
      Tendsto (fun T => dist (f (stage T) T) (a (stage T)))
        atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => dist_nonneg
    · exact hrowDiagonal.mono fun _ h => h.le
    · exact hbound
  refine ⟨stage, hstage, ?_⟩
  have haDiagonal :
      Tendsto (fun T => a (stage T)) atTop (nhds A) :=
    ha.comp hstage
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hdistanceSmall : ∀ᶠ T in atTop,
      dist (f (stage T) T) (a (stage T)) < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg dist_nonneg] using
      (Metric.tendsto_nhds.1 hdistance (ε / 2) hhalf)
  have haSmall : ∀ᶠ T in atTop,
      dist (a (stage T)) A < ε / 2 :=
    Metric.tendsto_nhds.1 haDiagonal (ε / 2) hhalf
  filter_upwards [hdistanceSmall, haSmall] with T h₁ h₂
  calc
    dist (f (stage T) T) A ≤
        dist (f (stage T) T) (a (stage T)) +
          dist (a (stage T)) A :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h₁ h₂
    _ = ε := by ring

/-- The height scale in the smoothed four-point theorem. -/
def rsQuarticScale (T : ℝ) : ℝ :=
  T * Real.log T / (2 * Real.pi)

/-- An error bounded by a constant times height disappears after division
by the four-point scale, whose extra logarithm tends to infinity. -/
theorem tendsto_normalized_of_linear_error
    (S : ℝ → ℂ) (M : ℂ)
    (herror : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T ≥ T₀,
      ‖S T - (rsQuarticScale T : ℂ) * M‖ ≤ C * T) :
    Tendsto (fun T => S T / (rsQuarticScale T : ℂ))
      atTop (nhds M) := by
  obtain ⟨C, T₀, hC, herror⟩ := herror
  have hratioZero :
      Tendsto (fun T : ℝ => C * (2 * Real.pi) / Real.log T)
        atTop (nhds 0) := by
    simpa only using
      Real.tendsto_log_atTop.const_div_atTop (C * (2 * Real.pi))
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  filter_upwards [
    eventually_ge_atTop T₀,
    eventually_gt_atTop (1 : ℝ),
    (Metric.tendsto_nhds.1 hratioZero ε hε)
  ] with T hT hT1 hratio
  have hTpos : 0 < T := lt_trans zero_lt_one hT1
  have hlog : 0 < Real.log T := Real.log_pos hT1
  have hscale : 0 < rsQuarticScale T := by
    unfold rsQuarticScale
    positivity
  have hscaleC : (rsQuarticScale T : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hscale.ne'
  have hrewrite :
      S T / (rsQuarticScale T : ℂ) - M =
        (S T - (rsQuarticScale T : ℂ) * M) /
          (rsQuarticScale T : ℂ) := by
    field_simp [hscaleC]
  have hnormScale :
      ‖(rsQuarticScale T : ℂ)‖ = rsQuarticScale T := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale]
  have hratioEq :
      C * T / rsQuarticScale T =
        C * (2 * Real.pi) / Real.log T := by
    unfold rsQuarticScale
    field_simp [hTpos.ne', hlog.ne', Real.pi_ne_zero]
    <;> ring
  calc
    dist (S T / (rsQuarticScale T : ℂ)) M =
        ‖S T / (rsQuarticScale T : ℂ) - M‖ := dist_eq_norm _ _
    _ = ‖S T - (rsQuarticScale T : ℂ) * M‖ /
          rsQuarticScale T := by
      rw [hrewrite, norm_div, hnormScale]
    _ ≤ C * T / rsQuarticScale T :=
      (div_le_div_iff_of_pos_right hscale).2 (herror T hT)
    _ = C * (2 * Real.pi) / Real.log T := hratioEq
    _ < ε := by
      apply lt_of_le_of_lt (le_abs_self _)
      simpa only [Real.dist_eq, sub_zero] using hratio

/-- The normalized all-zero four-point statistic for one fixed smooth
profile. -/
def normalizedFrozenQuarticRSStatistic
    {Z : ZeroConfig} (r : ℝ → ℝ)
    (g : Fin 4 → ℝ → ℂ) (T : ℝ) : ℂ :=
  (∑' ρ, rsZeroTupleTerm Z g
      (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) T ρ) /
    (rsQuarticScale T : ℂ)

/-- The fixed-profile limit furnished by the evaluated RS main term. -/
def frozenQuarticRSMain
    (r : ℝ → ℝ) (g : Fin 4 → ℝ → ℂ) : ℂ :=
  rsHeightFactor g *
    (((4999 / 10000 : ℝ) *
      quarticRSScalar (4999 / 10000 : ℝ) r : ℝ) : ℂ)

/-- For every fixed smooth unit-interval profile, the published linear
error becomes a genuine normalized limit. -/
theorem RS1996ZetaInputs.tendsto_normalizedFrozenQuarticRSStatistic
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (r : ℝ → ℝ) (hrc : HasCompactSupport r)
    (hrSmooth : ContDiff ℝ 1 r)
    (hrSupport : ∀ x, r x ≠ 0 → (0 : ℝ) ≤ x ∧ x ≤ 1)
    (g : Fin 4 → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    Tendsto (normalizedFrozenQuarticRSStatistic (Z := Z) r g)
      atTop (nhds (frozenQuarticRSMain r g)) := by
  unfold normalizedFrozenQuarticRSStatistic
  apply tendsto_normalized_of_linear_error
  obtain ⟨C, T₀, hC, _hT₀, hRS⟩ :=
    RSPairIntegrals.RS1996ZetaInputs.frozenQuartic_evaluated
      hrs r hrc hrSmooth hrSupport g hg
  refine ⟨C, T₀, hC, ?_⟩
  intro T hT
  have hbound := (hRS T hT).2
  convert hbound using 1 <;>
    simp only [frozenQuarticRSMain, rsQuarticScale] <;>
    push_cast <;> ring

/-- A sequence of increasingly sharp smooth profiles may be selected slowly
enough that its fixed-test RS estimates and its limiting main term hold on
one common height diagonal. -/
theorem RS1996ZetaInputs.exists_tendsto_profile_diagonal
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (r : ℕ → ℝ → ℝ)
    (hrc : ∀ n, HasCompactSupport (r n))
    (hrSmooth : ∀ n, ContDiff ℝ 1 (r n))
    (hrSupport : ∀ n x, r n x ≠ 0 →
      (0 : ℝ) ≤ x ∧ x ≤ 1)
    (g : Fin 4 → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j))
    (A : ℂ)
    (hmain : Tendsto (fun n => frozenQuarticRSMain (r n) g)
      atTop (nhds A)) :
    ∃ stage : ℝ → ℕ,
      Tendsto stage atTop atTop ∧
      Tendsto
        (fun T =>
          normalizedFrozenQuarticRSStatistic (Z := Z) (r (stage T)) g T)
        atTop (nhds A) := by
  apply exists_tendsto_slow_diagonal
    (fun n T => normalizedFrozenQuarticRSStatistic (Z := Z) (r n) g T)
    (fun n => frozenQuarticRSMain (r n) g) A
  · intro n
    exact
      RS1996ZetaInputs.tendsto_normalizedFrozenQuarticRSStatistic
        (Z := Z) hrs (r n) (hrc n) (hrSmooth n)
          (hrSupport n) g hg
  · exact hmain

/-- Normalized uncentered trace moment of the literal distinguished block. -/
def uncenteredBlockMoment {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (k : ℕ) (T : ℝ) : ℝ :=
  rtrace ((F.block T) ^ k) / (F.blockDim T : ℝ)

/-- The exact analytic remainder after the cyclic contractions have been
evaluated: the actual uncentered block moments converge to formula (27).

This predicate deliberately does not include complex Poisson summability or
cancellation, which are independent fields of `BlockMomentLimits`. -/
structure UncenteredRSBlockLimits {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  moments : ∀ k : ℕ, k ≤ 4 →
    Tendsto (uncenteredBlockMoment F k) atTop
      (nhds (uncenteredContractionMoment (topHatR3Terms p) μ k))

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
