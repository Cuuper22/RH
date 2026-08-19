/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.AnnularEnergyBridge

/-!
# Post-contraction annular energy selection

The annular stage is selected only after the complete quartic zero contraction
has been formed.  The same selection is required to have nonzero total shell
mass, so normalization is automatic rather than a separate premise.
-/

open MeasureTheory Filter Matrix Finset Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace AnnularEnergyStage

open Zeta23
open SmoothRadialShell AnnularEnergyBridge

/-- At each height, one finite annular stage simultaneously approximates the
complete frozen-profile quartic contraction and has nonzero total energy. -/
theorem exists_shrinkingAnnularStage_dist_lt_and_mass_ne
    {Z : ZeroConfig} {σ μ p : ℝ} {w : ℝ → ℝ}
    (q : TrimmedMoment.Quartic)
    (F : QuarticGramFamily Z σ μ p w)
    (v : ℝ → ℝ) (L : ℝ → ℝ) (hL : ∀ T, 0 < L T)
    (hv : ContDiff ℝ ∞ v)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (hmass :
      ∀ T : ℝ,
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / L T)) ≠ 0)
    (T ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ,
      dist
          (shrinkingAnnularNormalizedQuarticNumerator
            q F v L hL T n)
          (supportedProfileNormalizedQuarticNumerator
            q F v L T) < ε ∧
        (∫ u : ℝ,
          shrinkingProfileShellWindow v (L T) n (hL T) u ^ 2) ≠ 0 := by
  have hquartic :=
    (tendsto_shrinkingAnnularNormalizedQuarticNumerator
      q F v L hL hv hposProfile hmass T).eventually
        (Metric.ball_mem_nhds _ hε)
  have hmassLimit :=
    tendsto_integral_shrinkingProfileShellWindow_sq
      v (L T) (hL T) hv hposProfile
  have hmassStage :
      ∀ᶠ n : ℕ in Filter.atTop,
        (∫ u : ℝ,
          shrinkingProfileShellWindow v (L T) n (hL T) u ^ 2) ≠ 0 :=
    hmassLimit.eventually_ne (hmass T)
  have hboth :
      ∀ᶠ n : ℕ in Filter.atTop,
        dist
            (shrinkingAnnularNormalizedQuarticNumerator
              q F v L hL T n)
            (supportedProfileNormalizedQuarticNumerator
              q F v L T) < ε ∧
          (∫ u : ℝ,
            shrinkingProfileShellWindow v (L T) n (hL T) u ^ 2) ≠ 0 := by
    filter_upwards [hquartic, hmassStage] with n hq hm
    exact ⟨by simpa only [Metric.mem_ball] using hq, hm⟩
  exact hboth.exists

/-- Choose the annular stage after the complete quartic contraction, with
nonzero mass included in the selection criterion. -/
noncomputable def diagonalAnnularEnergyStage
    {Z : ZeroConfig} {σ μ p : ℝ} {w : ℝ → ℝ}
    (q : TrimmedMoment.Quartic)
    (F : QuarticGramFamily Z σ μ p w)
    (v : ℝ → ℝ) (L : ℝ → ℝ) (hL : ∀ T, 0 < L T)
    (hv : ContDiff ℝ ∞ v)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (hmass :
      ∀ T : ℝ,
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / L T)) ≠ 0)
    (T : ℝ) : ℕ :=
  Classical.choose
    (exists_shrinkingAnnularStage_dist_lt_and_mass_ne
      q F v L hL hv hposProfile hmass T
      (Real.exp (-T)) (Real.exp_pos _))

/-- The jointly selected stage has exponentially small complete-quartic
error. -/
theorem diagonalAnnularEnergyStage_quartic_spec
    {Z : ZeroConfig} {σ μ p : ℝ} {w : ℝ → ℝ}
    (q : TrimmedMoment.Quartic)
    (F : QuarticGramFamily Z σ μ p w)
    (v : ℝ → ℝ) (L : ℝ → ℝ) (hL : ∀ T, 0 < L T)
    (hv : ContDiff ℝ ∞ v)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (hmass :
      ∀ T : ℝ,
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / L T)) ≠ 0)
    (T : ℝ) :
    dist
        (shrinkingAnnularNormalizedQuarticNumerator
          q F v L hL T
            (diagonalAnnularEnergyStage
              q F v L hL hv hposProfile hmass T))
        (supportedProfileNormalizedQuarticNumerator
          q F v L T) < Real.exp (-T) :=
  (Classical.choose_spec
    (exists_shrinkingAnnularStage_dist_lt_and_mass_ne
      q F v L hL hv hposProfile hmass T
      (Real.exp (-T)) (Real.exp_pos _))).1

/-- The jointly selected stage has nonzero real total shell energy. -/
theorem diagonalAnnularEnergyStage_real_mass_ne
    {Z : ZeroConfig} {σ μ p : ℝ} {w : ℝ → ℝ}
    (q : TrimmedMoment.Quartic)
    (F : QuarticGramFamily Z σ μ p w)
    (v : ℝ → ℝ) (L : ℝ → ℝ) (hL : ∀ T, 0 < L T)
    (hv : ContDiff ℝ ∞ v)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (hmass :
      ∀ T : ℝ,
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / L T)) ≠ 0)
    (T : ℝ) :
    (∫ u : ℝ,
      shrinkingProfileShellWindow v (L T)
        (diagonalAnnularEnergyStage
          q F v L hL hv hposProfile hmass T)
        (hL T) u ^ 2) ≠ 0 :=
  (Classical.choose_spec
    (exists_shrinkingAnnularStage_dist_lt_and_mass_ne
      q F v L hL hv hposProfile hmass T
      (Real.exp (-T)) (Real.exp_pos _))).2

/-- The same selected stage has nonzero complex total shell energy, exactly
the premise needed by the normalized routed-energy kernel. -/
theorem diagonalAnnularEnergyStage_complex_mass_ne
    {Z : ZeroConfig} {σ μ p : ℝ} {w : ℝ → ℝ}
    (q : TrimmedMoment.Quartic)
    (F : QuarticGramFamily Z σ μ p w)
    (v : ℝ → ℝ) (L : ℝ → ℝ) (hL : ∀ T, 0 < L T)
    (hv : ContDiff ℝ ∞ v)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (hmass :
      ∀ T : ℝ,
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / L T)) ≠ 0)
    (T : ℝ) :
    (∫ u : ℝ,
      (shrinkingProfileShellWindow v (L T)
        (diagonalAnnularEnergyStage
          q F v L hL hv hposProfile hmass T)
        (hL T) u ^ 2 : ℂ)) ≠ 0 := by
  have hcast :
      (∫ u : ℝ,
        ((shrinkingProfileShellWindow v (L T)
          (diagonalAnnularEnergyStage
            q F v L hL hv hposProfile hmass T)
          (hL T) u ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [integral_complex_ofReal]
    exact_mod_cast
      diagonalAnnularEnergyStage_real_mass_ne
        q F v L hL hv hposProfile hmass T
  simpa only [Complex.ofReal_pow] using hcast

end AnnularEnergyStage
end Zeta85
end RH

end
