/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSSharpEvaluation

/-!
# Rudnick--Sarnak at fixed smoothing width

The quantifier order in this module is the analytic point: for each fixed
smooth top hat, Rudnick--Sarnak supplies its own constants and height
threshold.  Only the resulting main terms are then sent to the sharp limit.
No test function varies with height.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators Matrix ContDiff Convolution

noncomputable section

namespace RH.Zeta85.RSReduction

open TopHatMoments

/-- The Rudnick--Sarnak ordered-zero sum divided by its natural
`T log T / (2 pi)` scale. -/
def normalizedRSZeroTupleSum
    (Z : Zeta23.ZeroConfig) {n : ℕ}
    (g : Fin (n + 1) → ℝ → ℂ)
    (Φ : (Fin (n + 1) → ℝ) → ℂ) (T : ℝ) : ℂ :=
  ((2 * Real.pi / (T * Real.log T) : ℝ) : ℂ) *
    ∑' rho, rsZeroTupleTerm Z g Φ T rho

/-- Any linear remainder against the RS main scale vanishes after
normalization.  This is the quantitative limit step used after gauge repair. -/
theorem normalizedRSZeroTupleSum_tendsto_of_linear_error
    {Z : Zeta23.ZeroConfig} {n : ℕ}
    {g : Fin (n + 1) → ℝ → ℂ}
    {Φ : (Fin (n + 1) → ℝ) → ℂ}
    (herror : ∃ C T0 : ℝ, 0 ≤ C ∧ ∀ T ≥ T0,
      ‖(∑' rho, rsZeroTupleTerm Z g Φ T rho) -
          rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
            rsMainTerm Φ‖ ≤ C * T) :
    Tendsto (normalizedRSZeroTupleSum Z g Φ) atTop
      (𝓝 (rsHeightFactor g * rsMainTerm Φ)) := by
  obtain ⟨C, T0, hC, hbound⟩ := herror
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (g := fun T : ℝ => 2 * Real.pi * C / Real.log T)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      eventually_ge_atTop T0] with T hT hT0
    have hTpos : 0 < T := lt_trans zero_lt_one hT
    have hlogpos : 0 < Real.log T := Real.log_pos hT
    have hscale :
        ((2 * Real.pi / (T * Real.log T) : ℝ) : ℂ) *
            (rsHeightFactor g *
              (T * Real.log T / (2 * Real.pi)) * rsMainTerm Φ) =
          rsHeightFactor g * rsMainTerm Φ := by
      push_cast
      field_simp [hTpos.ne', hlogpos.ne', Real.pi_ne_zero]
    rw [normalizedRSZeroTupleSum, ← hscale, ← mul_sub]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (by positivity) (mul_pos hTpos hlogpos))]
    have herr := hbound T hT0
    calc
      2 * Real.pi / (T * Real.log T) *
          ‖(∑' rho, rsZeroTupleTerm Z g Φ T rho) -
            rsHeightFactor g *
              (T * Real.log T / (2 * Real.pi)) * rsMainTerm Φ‖
          ≤ 2 * Real.pi / (T * Real.log T) * (C * T) :=
        mul_le_mul_of_nonneg_left herr
          (div_nonneg (by positivity) (mul_nonneg hTpos.le hlogpos.le))
      _ = 2 * Real.pi * C / Real.log T := by
        field_simp [hTpos.ne', hlogpos.ne']
  · exact tendsto_const_nhds.div_atTop Real.tendsto_log_atTop

/-- For every fixed admissible test, the `O(T)` remainder in Theorem 3.1
vanishes after the natural `T log T` normalization. -/
theorem RS1996ZetaInputs.normalizedRSZeroTupleSum_tendsto
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (g : Fin (n + 1) → ℝ → ℂ)
    (Φ : (Fin (n + 1) → ℝ) → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j))
    (hΦsmooth : ContDiff ℝ 1 Φ)
    (hΦsupport : tsupport Φ ⊆
      {xi | ∑ j : Fin (n + 1), |xi j| < 2}) :
    Tendsto (normalizedRSZeroTupleSum Z g Φ) atTop
      (𝓝 (rsHeightFactor g * rsMainTerm Φ)) := by
  obtain ⟨C, T0, hC, _hT0, hbound⟩ :=
    hRS.theorem31 n g Φ hg hΦsmooth hΦsupport
  exact normalizedRSZeroTupleSum_tendsto_of_linear_error
    ⟨C, T0, hC, fun T hT => (hbound T hT).2⟩

/-- Rudnick--Sarnak applies separately at every canonical smoothing width,
while those fixed-test main terms converge to the sharp top-hat main term. -/
theorem RS1996ZetaInputs.theorem31_fixedSmoothTopHatFamily
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (g : Fin (n + 1) → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j))
    {p delta mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    (∀ m : ℕ, ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 ≤ T₀ ∧ ∀ T ≥ T₀,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m))) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := n + 1) mu
            (smoothTopHat p (topHatSmoothingWidth p m))) T rho) -
          rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
            rsMainTerm (weightedCyclicSymbol (k := n + 1) mu
              (smoothTopHat p (topHatSmoothingWidth p m)))‖ ≤ C * T) ∧
    Tendsto
      (fun m : ℕ => rsMainTerm
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m))))
      atTop
      (𝓝 (rsMainTerm
        (weightedCyclicSymbol (k := n + 1) mu (topHat p)))) := by
  constructor
  · intro m
    let w := topHatSmoothingWidth p m
    have hw : 0 < w := topHatSmoothingWidth_pos hp m
    have hwp : 2 * w ≤ p := two_mul_topHatSmoothingWidth_le hp m
    exact RS1996ZetaInputs.theorem31_weightedCyclicSymbol hRS n g hg
      (smoothTopHat p w) (smoothTopHat_contDiff hw hwp)
      (smoothTopHat_hasCompactSupport hw)
      ((smoothTopHat_support hw).trans
        (topHatSupport_subset_baseWindow hp1))
      hdelta hmu hbudget
  · exact rsMainTerm_smoothTopHat_tendsto_topHat hp hp1 hmu

/-- The same fixed-test family with its sharp limiting main term evaluated
as the frozen contraction formula through degree four. -/
theorem RS1996ZetaInputs.theorem31_fixedSmoothTopHatFamily_evaluated
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3) (g : Fin (n + 1) → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j))
    {p delta mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    (∀ m : ℕ, ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 ≤ T₀ ∧ ∀ T ≥ T₀,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m))) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := n + 1) mu
            (smoothTopHat p (topHatSmoothingWidth p m))) T rho) -
          rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
            rsMainTerm (weightedCyclicSymbol (k := n + 1) mu
              (smoothTopHat p (topHatSmoothingWidth p m)))‖ ≤ C * T) ∧
    Tendsto
      (fun m : ℕ => rsMainTerm
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m))))
      atTop
      (𝓝 ((mu : ℂ) *
        (uncenteredContractionMoment
          (topHatR3Terms p) mu (n + 1) : ℝ))) := by
  obtain ⟨hfixed, hlim⟩ :=
    RS1996ZetaInputs.theorem31_fixedSmoothTopHatFamily
      hRS n g hg hp hp1 hdelta hmu hbudget
  refine ⟨hfixed, ?_⟩
  simpa only [RSPairIntegrals.rsMainTerm_topHat_eq_uncenteredContractionMoment
    hn hp hp1 hmu] using hlim

/-- The fixed-width RS sums have genuine normalized limits, and those limits
then converge to the evaluated sharp contraction.  The height limit is taken
before the smoothing-width limit, so no test varies with height. -/
theorem RS1996ZetaInputs.normalized_fixedSmoothTopHatFamily_evaluated
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3) (g : Fin (n + 1) → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j))
    {p delta mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    (∀ m : ℕ, Tendsto
      (normalizedRSZeroTupleSum Z g
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m))))
      atTop
      (𝓝 (rsHeightFactor g *
        rsMainTerm (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m)))))) ∧
    Tendsto
      (fun m : ℕ => rsHeightFactor g *
        rsMainTerm (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m))))
      atTop
      (𝓝 (rsHeightFactor g *
        ((mu : ℂ) *
          (uncenteredContractionMoment
            (topHatR3Terms p) mu (n + 1) : ℝ)))) := by
  obtain ⟨hfixed, hsharp⟩ :=
    RS1996ZetaInputs.theorem31_fixedSmoothTopHatFamily_evaluated
      hRS n hn g hg hp hp1 hdelta hmu hbudget
  constructor
  · intro m
    obtain ⟨C, T0, hC, _hT0, hbound⟩ := hfixed m
    exact normalizedRSZeroTupleSum_tendsto_of_linear_error
      ⟨C, T0, hC, fun T hT => (hbound T hT).2⟩
  · exact hsharp.const_mul (rsHeightFactor g)

end RH.Zeta85.RSReduction
