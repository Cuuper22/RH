/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSAnnularDiagonal

/-!
# Convergence of annular Rudnick--Sarnak main terms

The annular profiles are dominated by the frozen supported profile on the
unit interval and converge to it almost everywhere.  This file begins the
componentwise dominated-convergence evaluation of the quartic RS scalar.
-/

open Filter MeasureTheory Set
open scoped ContDiff Topology

noncomputable section

namespace RH.Zeta85.RSMainTermConvergence

open Zeta23 SmoothRadialShell RSAnnularDiagonal RSPairIntegrals

/-- The frozen centered profile shifted onto the RS unit interval. -/
def frozenRSProfile (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Icc (0 : ℝ) 1).indicator (fun y => v (y - 1 / 2)) x

/-- The unit-interval profile is the centered supported profile after the
shift by one half. -/
theorem frozenRSProfile_eq_supported
    (v : ℝ → ℝ) (x : ℝ) :
    frozenRSProfile v x =
      @QuarticGramFamily.supportedFullProfile v (x - 1 / 2) := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have hcenter : x - 1 / 2 ∈
        Icc (-(1 : ℝ) / 2) (1 / 2) := by
      constructor <;> linarith [hx.1, hx.2]
    simp [frozenRSProfile, QuarticGramFamily.supportedFullProfile,
      hx, hcenter]
  · have hcenter : x - 1 / 2 ∉
        Icc (-(1 : ℝ) / 2) (1 / 2) := by
      intro h
      apply hx
      constructor <;> linarith [h.1, h.2]
    simp [frozenRSProfile, QuarticGramFamily.supportedFullProfile,
      hx, hcenter]

/-- Nonzero frozen-profile points lie in the unit interval. -/
theorem frozenRSProfile_support
    (v : ℝ → ℝ) (x : ℝ)
    (hx : frozenRSProfile v x ≠ 0) :
    x ∈ Icc (0 : ℝ) 1 := by
  by_contra hmem
  apply hx
  simp [frozenRSProfile, hmem]

/-- Positivity of the centered profile gives nonnegativity after truncation
and shifting. -/
theorem frozenRSProfile_nonneg
    (v : ℝ → ℝ)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (x : ℝ) :
    0 ≤ frozenRSProfile v x := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [frozenRSProfile, Set.indicator_of_mem hx]
    apply (hpos (x - 1 / 2) ?_).le
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  · simp [frozenRSProfile, hx]

/-- Every annular approximation lies pointwise between zero and the frozen
profile. -/
theorem annularRSProfile_le_frozen
    (v : ℝ → ℝ) (n : ℕ)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (x : ℝ) :
    0 ≤ annularRSProfile v n x ∧
      annularRSProfile v n x ≤ frozenRSProfile v x := by
  have hbound :=
    shrinkingProfileShellWindow_sq_le_supportedFullProfile
      v 1 n (by norm_num) hpos (x - 1 / 2)
  simpa [annularRSProfile, frozenRSProfile_eq_supported] using hbound

/-- The shifted annular profiles converge almost everywhere to the shifted
frozen profile. -/
theorem ae_tendsto_annularRSProfile
    (v : ℝ → ℝ)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => annularRSProfile v n x)
        atTop (nhds (frozenRSProfile v x)) := by
  filter_upwards [
    volume.ae_ne (0 : ℝ),
    volume.ae_ne (1 / 2 : ℝ),
    volume.ae_ne (1 : ℝ)
  ] with x hx0 hxmid hx1
  have hboundary : |x - 1 / 2| ≠ (1 : ℝ) / 2 := by
    intro h
    rcases (abs_eq (by norm_num : 0 ≤ (1 / 2 : ℝ))).mp h with h | h
    · apply hx1
      linarith
    · apply hx0
      linarith
  have ht :=
    tendsto_shrinkingProfileShellWindow_sq
      v 1 (by norm_num) hpos (x - 1 / 2)
        (sub_ne_zero.mpr hxmid) hboundary
  simpa [annularRSProfile, frozenRSProfile_eq_supported] using ht

/-- Every positive power of the frozen shifted profile is integrable. -/
theorem integrable_frozenRSProfile_pow
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (k : ℕ) :
    Integrable (fun x => frozenRSProfile v x ^ k) := by
  have heq :
      (fun x => frozenRSProfile v x ^ k) =
        (Icc (0 : ℝ) 1).indicator
          (fun x => v (x - 1 / 2) ^ k) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;>
      simp [frozenRSProfile, hx]
  rw [heq, integrable_indicator_iff measurableSet_Icc]
  have hcontinuous :
      Continuous (fun x : ℝ => v (x - 1 / 2) ^ k) :=
    ((hv.continuous.comp
      (continuous_id.sub continuous_const)).pow k)
  exact hcontinuous.continuousOn.integrableOn_compact isCompact_Icc

/-- The zeroth-contraction quartic integral converges to its literal frozen
profile value. -/
theorem tendsto_integral_annularRSProfile_pow_four
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n => ∫ x : ℝ, annularRSProfile v n x ^ 4)
      atTop
      (nhds (∫ x : ℝ, frozenRSProfile v x ^ 4)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => frozenRSProfile v x ^ 4)
  · intro n
    exact
      ((annularRSProfile_contDiff v n hv hpos).continuous.pow 4).aestronglyMeasurable
  · exact integrable_frozenRSProfile_pow v hv 4
  · intro n
    filter_upwards [] with x
    have hbound := annularRSProfile_le_frozen v n hpos x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hbound.1 4)]
    exact pow_le_pow_left₀ hbound.1 hbound.2 4
  · filter_upwards [ae_tendsto_annularRSProfile v hpos] with x hx
    exact hx.pow 4


/-- Frozen powered profiles give an integrable two-variable distance
kernel, despite the two endpoint jumps of the frozen cutoff. -/
theorem integrable_frozen_distanceKernel_pows
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (a b : ℕ) :
    Integrable
      (distanceKernel
        (fun x => frozenRSProfile v x ^ a)
        (fun y => frozenRSProfile v y ^ b)) := by
  have heq :
      distanceKernel
          (fun x => frozenRSProfile v x ^ a)
          (fun y => frozenRSProfile v y ^ b) =
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
          (fun z : ℝ × ℝ =>
            |z.2 - z.1| *
              v (z.1 - 1 / 2) ^ a *
              v (z.2 - 1 / 2) ^ b) := by
    funext z
    by_cases hx : z.1 ∈ Icc (0 : ℝ) 1 <;>
      by_cases hy : z.2 ∈ Icc (0 : ℝ) 1 <;>
      simp [distanceKernel, frozenRSProfile, hx, hy]
  rw [heq, integrable_indicator_iff
    (measurableSet_Icc.prod measurableSet_Icc)]
  have hc :
      Continuous (fun z : ℝ × ℝ =>
        |z.2 - z.1| *
          v (z.1 - 1 / 2) ^ a *
          v (z.2 - 1 / 2) ^ b) := by
    exact
      (((continuous_snd.sub continuous_fst).abs.mul
        ((hv.continuous.comp
          (continuous_fst.sub continuous_const)).pow a)).mul
        ((hv.continuous.comp
          (continuous_snd.sub continuous_const)).pow b))
  exact hc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- Fubini identifies the iterated distance functional with its literal
two-variable kernel whenever that kernel is integrable. -/
theorem distanceIntegral_eq_integral_distanceKernel
    (f g : ℝ → ℝ)
    (hint : Integrable (distanceKernel f g)) :
    distanceIntegral f g =
      ∫ z : ℝ × ℝ, distanceKernel f g z := by
  rw [distanceIntegral, Measure.volume_eq_prod, integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [distanceKernel]
  ring_nf

/-- Every powered distance kernel of the smooth annular profile converges
in integral to the corresponding frozen kernel. -/
theorem tendsto_integral_annular_distanceKernel_pows
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n =>
        ∫ z : ℝ × ℝ,
          distanceKernel
            (fun x => annularRSProfile v n x ^ a)
            (fun y => annularRSProfile v n y ^ b) z)
      atTop
      (nhds
        (∫ z : ℝ × ℝ,
          distanceKernel
            (fun x => frozenRSProfile v x ^ a)
            (fun y => frozenRSProfile v y ^ b) z)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (distanceKernel
      (fun x => frozenRSProfile v x ^ a)
      (fun y => frozenRSProfile v y ^ b))
  · intro n
    exact
      (distanceKernel_integrable_of_continuous_compact
        (fun x => annularRSProfile v n x ^ a)
        (fun y => annularRSProfile v n y ^ b)
        ((annularRSProfile_contDiff v n hv hpos).continuous.pow a)
        ((annularRSProfile_contDiff v n hv hpos).continuous.pow b)
        (positivePower_hasCompactSupport
          (annularRSProfile v n) a ha
          (annularRSProfile_hasCompactSupport v n))
        (positivePower_hasCompactSupport
          (annularRSProfile v n) b hb
          (annularRSProfile_hasCompactSupport v n))).aestronglyMeasurable
  · exact integrable_frozen_distanceKernel_pows v hv a b
  · intro n
    filter_upwards [] with z
    have hx := annularRSProfile_le_frozen v n hpos z.1
    have hy := annularRSProfile_le_frozen v n hpos z.2
    have hxpow : annularRSProfile v n z.1 ^ a ≤
        frozenRSProfile v z.1 ^ a :=
      pow_le_pow_left₀ hx.1 hx.2 a
    have hypow : annularRSProfile v n z.2 ^ b ≤
        frozenRSProfile v z.2 ^ b :=
      pow_le_pow_left₀ hy.1 hy.2 b
    have hkernelNonneg :
        0 ≤ distanceKernel
          (fun x => annularRSProfile v n x ^ a)
          (fun y => annularRSProfile v n y ^ b) z := by
      unfold distanceKernel
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hkernelNonneg]
    unfold distanceKernel
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hxpow abs_nonneg)
      hypow
      (pow_nonneg hy.1 b)
      (mul_nonneg abs_nonneg
        (pow_nonneg (frozenRSProfile_nonneg v hpos z.1) a))
  · have hae := ae_tendsto_annularRSProfile v hpos
    have hfst :
        ∀ᵐ z : ℝ × ℝ ∂volume,
          Tendsto (fun n => annularRSProfile v n z.1)
            atTop (nhds (frozenRSProfile v z.1)) := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae hae
    have hsnd :
        ∀ᵐ z : ℝ × ℝ ∂volume,
          Tendsto (fun n => annularRSProfile v n z.2)
            atTop (nhds (frozenRSProfile v z.2)) := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_snd.ae hae
    filter_upwards [hfst, hsnd] with z hx hy
    unfold distanceKernel
    exact (tendsto_const_nhds.mul (hx.pow a)).mul (hy.pow b)

/-- Consequently every positive powered term appearing in the
Rudnick--Sarnak one-pair main term converges to its frozen value. -/
theorem tendsto_distanceIntegral_annularRSProfile_pows
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n =>
        distanceIntegral
          (fun x => annularRSProfile v n x ^ a)
          (fun y => annularRSProfile v n y ^ b))
      atTop
      (nhds
        (distanceIntegral
          (fun x => frozenRSProfile v x ^ a)
          (fun y => frozenRSProfile v y ^ b))) := by
  have hann :
      (fun n =>
        distanceIntegral
          (fun x => annularRSProfile v n x ^ a)
          (fun y => annularRSProfile v n y ^ b)) =
      (fun n =>
        ∫ z : ℝ × ℝ,
          distanceKernel
            (fun x => annularRSProfile v n x ^ a)
            (fun y => annularRSProfile v n y ^ b) z) := by
    funext n
    apply distanceIntegral_eq_integral_distanceKernel
    exact distanceKernel_integrable_of_continuous_compact
      (fun x => annularRSProfile v n x ^ a)
      (fun y => annularRSProfile v n y ^ b)
      ((annularRSProfile_contDiff v n hv hpos).continuous.pow a)
      ((annularRSProfile_contDiff v n hv hpos).continuous.pow b)
      (positivePower_hasCompactSupport
        (annularRSProfile v n) a ha
        (annularRSProfile_hasCompactSupport v n))
      (positivePower_hasCompactSupport
        (annularRSProfile v n) b hb
        (annularRSProfile_hasCompactSupport v n))
  have hfrozen :
      distanceIntegral
          (fun x => frozenRSProfile v x ^ a)
          (fun y => frozenRSProfile v y ^ b) =
        ∫ z : ℝ × ℝ,
          distanceKernel
            (fun x => frozenRSProfile v x ^ a)
            (fun y => frozenRSProfile v y ^ b) z :=
    distanceIntegral_eq_integral_distanceKernel _ _
      (integrable_frozen_distanceKernel_pows v hv a b)
  rw [hann, hfrozen]
  exact
    tendsto_integral_annular_distanceKernel_pows
      v hv hpos a b ha hb

end RH.Zeta85.RSMainTermConvergence

end
