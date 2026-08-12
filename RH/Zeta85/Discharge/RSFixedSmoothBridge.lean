/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSPairIntegrals
import RH.Zeta85.Discharge.RSSharpSmoothing

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

end RH.Zeta85.RSReduction
