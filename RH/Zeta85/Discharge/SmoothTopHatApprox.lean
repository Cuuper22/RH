/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSPairIntegrals
import RH.Zeta85.Discharge.TopHatMoments

/-!
# Smooth top-hat tests at the frozen quartic bandwidth

The sharp top hat used by formula (21) is not an admissible Rudnick--Sarnak
test.  This file constructs an explicit sequence of smooth profiles.  Every
member is supported in the unit interval and therefore enters the frozen
strict-support construction, while the sequence converges pointwise to the
translated sharp top hat.
-/

open MeasureTheory Filter Set Zeta23
open scoped BigOperators Matrix Convolution Topology ContDiff

noncomputable section

namespace RH.Zeta85.SmoothTopHatApprox

open RSReduction RSPairIntegrals

/-- A bump centered at one half.  Its inner radius is the desired top-hat
half-width and its transition shell shrinks with n. -/
def topHatApproxBump (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1) :
    ContDiffBump (1 / 2 : ℝ) where
  rIn := p / 2
  rOut := p / 2 + (1 - p) / (2 * ((n : ℝ) + 1))
  rIn_pos := by linarith
  rIn_lt_rOut := by
    have hnum : 0 < 1 - p := sub_pos.mpr hp1
    have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
    have hfrac : 0 < (1 - p) / (2 * ((n : ℝ) + 1)) :=
      div_pos hnum hden
    linarith

/-- The smooth approximation has the same height as the sharp top hat. -/
def topHatApproxProfile (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1)
    (x : ℝ) : ℝ :=
  (1 / p) * topHatApproxBump p n hp hp1 x

theorem topHatApproxProfile_contDiff
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1) :
    ContDiff ℝ ∞ (topHatApproxProfile p n hp hp1) := by
  unfold topHatApproxProfile
  exact contDiff_const.mul
    (topHatApproxBump p n hp hp1).contDiff

theorem topHatApproxProfile_hasCompactSupport
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1) :
    HasCompactSupport (topHatApproxProfile p n hp hp1) := by
  apply (topHatApproxBump p n hp hp1).hasCompactSupport.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hb
  apply hx
  simp [topHatApproxProfile, hb]

private theorem transitionWidth_le
    (p : ℝ) (n : ℕ) (hp1 : p < 1) :
    (1 - p) / (2 * ((n : ℝ) + 1)) ≤ (1 - p) / 2 := by
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * ((n : ℝ) + 1))
    (by norm_num : (0 : ℝ) < 2)]
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hp0 : 0 ≤ 1 - p := (sub_pos.mpr hp1).le
  nlinarith

theorem topHatApproxProfile_support
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1)
    (x : ℝ) (hx : topHatApproxProfile p n hp hp1 x ≠ 0) :
    (0 : ℝ) ≤ x ∧ x ≤ 1 := by
  have hb : topHatApproxBump p n hp hp1 x ≠ 0 := by
    intro hb
    apply hx
    simp [topHatApproxProfile, hb]
  have hxball :
      x ∈ Metric.ball (1 / 2 : ℝ) (topHatApproxBump p n hp hp1).rOut := by
    rw [← (topHatApproxBump p n hp hp1).support_eq]
    exact hb
  have habs :
      |x - 1 / 2| <
        p / 2 + (1 - p) / (2 * ((n : ℝ) + 1)) := by
    simpa [topHatApproxBump, Real.dist_eq] using hxball
  have hwidth := transitionWidth_le p n hp1
  have habs' := abs_lt.mp habs
  constructor <;> linarith

theorem topHatApproxProfile_bounds
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1) (x : ℝ) :
    0 ≤ topHatApproxProfile p n hp hp1 x ∧
      topHatApproxProfile p n hp hp1 x ≤ 1 / p := by
  unfold topHatApproxProfile
  constructor
  · exact mul_nonneg (one_div_nonneg.mpr hp.le)
      (topHatApproxBump p n hp hp1).nonneg
  · simpa only [mul_one] using
      mul_le_mul_of_nonneg_left
        (topHatApproxBump p n hp hp1).le_one
        (one_div_nonneg.mpr hp.le)

theorem topHatApproxProfile_eq_height
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1) (x : ℝ)
    (hx : |x - 1 / 2| ≤ p / 2) :
    topHatApproxProfile p n hp hp1 x = 1 / p := by
  have hxball :
      x ∈ Metric.closedBall (1 / 2 : ℝ)
        (topHatApproxBump p n hp hp1).rIn := by
    simpa [topHatApproxBump, Real.dist_eq] using hx
  rw [topHatApproxProfile,
    (topHatApproxBump p n hp hp1).one_of_mem_closedBall hxball]
  ring

/-- The translated sharp top hat occupying the centered interval about one half. -/
def shiftedTopHat (p x : ℝ) : ℝ :=
  TopHatMoments.topHat p (x - 1 / 2)

theorem shiftedTopHat_eq_height
    (p x : ℝ) (hx : |x - 1 / 2| ≤ p / 2) :
    shiftedTopHat p x = 1 / p := by
  have hmem : x - 1 / 2 ∈ TopHatMoments.topHatSupport p := by
    rw [TopHatMoments.topHatSupport, Set.mem_Icc]
    exact abs_le.mp hx
  unfold shiftedTopHat TopHatMoments.topHat
  rw [Set.indicator_of_mem hmem]

theorem shiftedTopHat_eq_zero
    (p x : ℝ) (hx : p / 2 < |x - 1 / 2|) :
    shiftedTopHat p x = 0 := by
  have hnot : x - 1 / 2 ∉ TopHatMoments.topHatSupport p := by
    intro hmem
    rw [TopHatMoments.topHatSupport, Set.mem_Icc] at hmem
    exact (not_le_of_gt hx) (abs_le.mpr hmem)
  unfold shiftedTopHat TopHatMoments.topHat
  rw [Set.indicator_of_not_mem hnot]

/-- Literal pointwise convergence of legal smooth profiles to the translated
sharp top hat, including the two boundary points. -/
theorem topHatApproxProfile_tendsto
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (x : ℝ) :
    Tendsto (fun n : ℕ => topHatApproxProfile p n hp hp1 x)
      atTop (nhds (shiftedTopHat p x)) := by
  by_cases hx : |x - 1 / 2| ≤ p / 2
  · have hlimit := shiftedTopHat_eq_height p x hx
    rw [Metric.tendsto_atTop]
    intro eps heps
    refine ⟨0, ?_⟩
    intro n hn
    rw [topHatApproxProfile_eq_height p n hp hp1 x hx, hlimit]
    simpa using heps
  · have hxlt : p / 2 < |x - 1 / 2| := lt_of_not_ge hx
    let d : ℝ := |x - 1 / 2| - p / 2
    have hd : 0 < d := by dsimp [d]; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 - p) / (2 * d))
    have hlimit := shiftedTopHat_eq_zero p x hxlt
    rw [Metric.tendsto_atTop]
    intro eps heps
    refine ⟨N, ?_⟩
    intro n hn
    have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2d : 0 < 2 * d := by positivity
    have hNm :
        1 - p < (N : ℝ) * (2 * d) :=
      (div_lt_iff₀ h2d).mp hN
    have hmul :
        (N : ℝ) * (2 * d) ≤ (n : ℝ) * (2 * d) :=
      mul_le_mul_of_nonneg_right hnR h2d.le
    have hnum :
        1 - p ≤ 2 * ((n : ℝ) + 1) * d := by
      nlinarith [lt_of_lt_of_le hNm hmul]
    have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
    have hfrac :
        (1 - p) / (2 * ((n : ℝ) + 1)) ≤ d :=
      (div_le_iff₀ hden).mpr (by
        nlinarith [hnum])
    have hrad :
        (topHatApproxBump p n hp hp1).rOut ≤
          dist x (1 / 2 : ℝ) := by
      dsimp [topHatApproxBump]
      rw [Real.dist_eq]
      dsimp [d] at hfrac
      linarith
    have hbzero : topHatApproxBump p n hp hp1 x = 0 :=
      (topHatApproxBump p n hp hp1).zero_of_le_dist hrad
    have hprof : topHatApproxProfile p n hp hp1 x = 0 := by
      simp [topHatApproxProfile, hbzero]
    rw [hprof, hlimit]
    simpa using heps

/-- Every member of the approximating family enters the frozen four-point
theorem, already with its main term reduced to the concrete scalar. -/
theorem RS1996ZetaInputs.topHatApproxQuartic_evaluated
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1)
    (g : Fin 4 -> ℝ -> ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T ≥ T0,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ)
          (topHatApproxProfile p n hp hp1)) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ)
            (topHatApproxProfile p n hp hp1)) T rho) -
        rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
          (((4999 / 10000 : ℝ) *
            quarticRSScalar (4999 / 10000 : ℝ)
              (topHatApproxProfile p n hp hp1) : ℝ) : ℂ)‖ ≤ C * T := by
  exact RSPairIntegrals.RS1996ZetaInputs.frozenQuartic_evaluated hrs
    (topHatApproxProfile p n hp hp1)
    (topHatApproxProfile_hasCompactSupport p n hp hp1)
    (topHatApproxProfile_contDiff p n hp hp1).of_le (by norm_num)
    (topHatApproxProfile_support p n hp hp1) g hg

end RH.Zeta85.SmoothTopHatApprox
