/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSAnnularDiagonal
import RH.Zeta85.Discharge.QuarticWindowWitnesses

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
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (k : ℕ) (hk : 0 < k) :
    Integrable (fun x => frozenRSProfile v x ^ k) := by
  have heq :
      (fun x => frozenRSProfile v x ^ k) =
        (Icc (0 : ℝ) 1).indicator
          (fun x => v (x - 1 / 2) ^ k) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;>
      simp [frozenRSProfile, hx, zero_pow hk]
  rw [heq, integrable_indicator_iff measurableSet_Icc]
  have hcontinuous :
      Continuous (fun x : ℝ => v (x - 1 / 2) ^ k) :=
    ((hv.continuous.comp
      (continuous_id.sub continuous_const)).pow k)
  exact hcontinuous.continuousOn.integrableOn_compact isCompact_Icc

/-- Every positive annular profile power converges in integral to its
literal frozen-profile value. -/
theorem tendsto_integral_annularRSProfile_pow
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun n => ∫ x : ℝ, annularRSProfile v n x ^ k)
      atTop
      (nhds (∫ x : ℝ, frozenRSProfile v x ^ k)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => frozenRSProfile v x ^ k)
  · intro n
    exact
      ((annularRSProfile_contDiff v n hv hpos).continuous.pow k).aestronglyMeasurable
  · exact integrable_frozenRSProfile_pow v hv k hk
  · intro n
    filter_upwards [] with x
    have hbound := annularRSProfile_le_frozen v n hpos x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hbound.1 k)]
    exact pow_le_pow_left₀ hbound.1 hbound.2 k
  · filter_upwards [ae_tendsto_annularRSProfile v hpos] with x hx
    exact hx.pow k

/-- The zeroth-contraction quartic integral is the fourth-power
specialization of the positive-power theorem. -/
theorem tendsto_integral_annularRSProfile_pow_four
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n => ∫ x : ℝ, annularRSProfile v n x ^ 4)
      atTop
      (nhds (∫ x : ℝ, frozenRSProfile v x ^ 4)) :=
  tendsto_integral_annularRSProfile_pow
    v hv hpos 4 (by norm_num)


/-- Frozen powered profiles give an integrable two-variable distance
kernel, despite the two endpoint jumps of the frozen cutoff. -/
theorem integrable_frozen_distanceKernel_pows
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
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
      simp [distanceKernel, frozenRSProfile, hx, hy,
        zero_pow ha, zero_pow hb]
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
  · exact integrable_frozen_distanceKernel_pows v hv a b ha hb
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
      (integrable_frozen_distanceKernel_pows v hv a b ha hb)
  rw [hann, hfrozen]
  exact
    tendsto_integral_annular_distanceKernel_pows
      v hv hpos a b ha hb


/-- On the unit support, the distance weight is uniformly controlled by
the distance of the external point from the origin. -/
theorem annular_distance_weight_le_frozen
    (v : ℝ → ℝ) (n : ℕ)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (x y : ℝ) :
    |y - x| * annularRSProfile v n y ≤
      (|x| + 1) * frozenRSProfile v y := by
  have hprofile := annularRSProfile_le_frozen v n hpos y
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · have hyabs : |y| ≤ 1 := by
      rw [abs_of_nonneg hy.1]
      exact hy.2
    have hdist : |y - x| ≤ |x| + 1 := by
      calc
        |y - x| ≤ |y| + |x| := abs_sub y x
        _ ≤ 1 + |x| := add_le_add_right hyabs _
        _ = |x| + 1 := by ring
    exact mul_le_mul hdist hprofile.2 hprofile.1 (by positivity)
  · have hfrozen : frozenRSProfile v y = 0 := by
      simp [frozenRSProfile, hy]
    have hannular : annularRSProfile v n y = 0 := by
      apply le_antisymm
      · simpa [hfrozen] using hprofile.2
      · exact hprofile.1
    simp [hannular, hfrozen]

/-- The annular distance potential converges pointwise to the frozen
distance potential. -/
theorem tendsto_pairDistancePotential_annular
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (x : ℝ) :
    Tendsto
      (fun n => pairDistancePotential (annularRSProfile v n) x)
      atTop
      (nhds (pairDistancePotential (frozenRSProfile v) x)) := by
  unfold pairDistancePotential
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun y => (|x| + 1) * frozenRSProfile v y)
  · intro n
    exact
      ((continuous_id.sub continuous_const).abs.mul
        (annularRSProfile_contDiff v n hv hpos).continuous).aestronglyMeasurable
  · simpa only [pow_one] using
      (integrable_frozenRSProfile_pow v hv 1 (by norm_num)).const_mul (|x| + 1)
  · intro n
    filter_upwards [] with y
    have hnonneg :
        0 ≤ |y - x| * annularRSProfile v n y :=
      mul_nonneg abs_nonneg
        (annularRSProfile_le_frozen v n hpos y).1
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact annular_distance_weight_le_frozen v n hpos x y
  · filter_upwards [ae_tendsto_annularRSProfile v hpos] with y hy
    exact tendsto_const_nhds.mul hy

/-- The same domination gives a quantitative bound for every finite-stage
distance potential. -/
theorem norm_pairDistancePotential_annular_le
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (n : ℕ) (x : ℝ) :
    ‖pairDistancePotential (annularRSProfile v n) x‖ ≤
      (|x| + 1) * ∫ y : ℝ, frozenRSProfile v y := by
  unfold pairDistancePotential
  have hdom :
      Integrable (fun y : ℝ =>
        (|x| + 1) * frozenRSProfile v y) := by
    simpa only [pow_one] using
      (integrable_frozenRSProfile_pow v hv 1 (by norm_num)).const_mul (|x| + 1)
  have hbound :=
    norm_integral_le_of_norm_le hdom
      (show ∀ᵐ y : ℝ ∂volume,
          ‖|y - x| * annularRSProfile v n y‖ ≤
            (|x| + 1) * frozenRSProfile v y by
        filter_upwards [] with y
        have hnonneg :
            0 ≤ |y - x| * annularRSProfile v n y :=
          mul_nonneg abs_nonneg
            (annularRSProfile_le_frozen v n hpos y).1
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact annular_distance_weight_le_frozen v n hpos x y)
  simpa only [integral_const_mul] using hbound

/-- Annular distance potentials are nonnegative. -/
theorem pairDistancePotential_annular_nonneg
    (v : ℝ → ℝ) (n : ℕ)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (x : ℝ) :
    0 ≤ pairDistancePotential (annularRSProfile v n) x := by
  unfold pairDistancePotential
  exact integral_nonneg fun y =>
    mul_nonneg abs_nonneg
      (annularRSProfile_le_frozen v n hpos y).1

/-- The annular distance potential is strongly measurable as a function
of its external point. -/
theorem aestronglyMeasurable_pairDistancePotential_annular
    (v : ℝ → ℝ) (n : ℕ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    AEStronglyMeasurable
      (pairDistancePotential (annularRSProfile v n)) := by
  have hk :
      StronglyMeasurable (fun z : ℝ × ℝ =>
        |z.2 - z.1| * annularRSProfile v n z.2) :=
    ((continuous_snd.sub continuous_fst).abs.mul
      ((annularRSProfile_contDiff v n hv hpos).continuous.comp
        continuous_snd)).stronglyMeasurable
  simpa only [pairDistancePotential] using
    hk.integral_prod_right'.aestronglyMeasurable

/-- The separated two-pair functional converges to its literal frozen
profile value. -/
theorem tendsto_pairSquaredPotentialIntegral_annular
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n =>
        pairSquaredPotentialIntegral (annularRSProfile v n))
      atTop
      (nhds
        (pairSquaredPotentialIntegral (frozenRSProfile v))) := by
  unfold pairSquaredPotentialIntegral
  let mass : ℝ := ∫ y : ℝ, frozenRSProfile v y
  have hmass : 0 ≤ mass := by
    dsimp only [mass]
    exact integral_nonneg fun y =>
      frozenRSProfile_nonneg v hpos y
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => frozenRSProfile v x ^ 2 * (2 * mass) ^ 2)
  · intro n
    exact
      ((annularRSProfile_contDiff v n hv hpos).continuous.pow 2
        |>.aestronglyMeasurable).mul
        ((aestronglyMeasurable_pairDistancePotential_annular
          v n hv hpos).pow 2)
  · exact
      (integrable_frozenRSProfile_pow v hv 2 (by norm_num)).mul_const
        ((2 * mass) ^ 2)
  · intro n
    filter_upwards [] with x
    by_cases hxzero : annularRSProfile v n x = 0
    · simp [hxzero]
    · have hsupport :=
        annularRSProfile_support v n x hxzero
      have hxabs : |x| ≤ 1 := by
        rw [abs_of_nonneg hsupport.1]
        exact hsupport.2
      have hprofile :=
        annularRSProfile_le_frozen v n hpos x
      have hprofilePow :
          annularRSProfile v n x ^ 2 ≤
            frozenRSProfile v x ^ 2 :=
        pow_le_pow_left₀ hprofile.1 hprofile.2 2
      have hpotentialNonneg :=
        pairDistancePotential_annular_nonneg
          v n hpos x
      have hpotentialBound :
          pairDistancePotential (annularRSProfile v n) x ≤
            2 * mass := by
        calc
          pairDistancePotential (annularRSProfile v n) x ≤
              ‖pairDistancePotential (annularRSProfile v n) x‖ :=
            le_norm_self _
          _ ≤ (|x| + 1) * mass := by
            simpa only [mass] using
              norm_pairDistancePotential_annular_le
                v hv hpos n x
          _ ≤ 2 * mass := by
            apply mul_le_mul_of_nonneg_right _ hmass
            linarith
      have hpotentialPow :
          pairDistancePotential (annularRSProfile v n) x ^ 2 ≤
            (2 * mass) ^ 2 :=
        pow_le_pow_left₀ hpotentialNonneg hpotentialBound 2
      have hintegrandNonneg :
          0 ≤ annularRSProfile v n x ^ 2 *
            pairDistancePotential (annularRSProfile v n) x ^ 2 :=
        mul_nonneg (pow_nonneg hprofile.1 2)
          (pow_nonneg hpotentialNonneg 2)
      rw [Real.norm_eq_abs, abs_of_nonneg hintegrandNonneg]
      exact mul_le_mul hprofilePow hpotentialPow
        (pow_nonneg hpotentialNonneg 2)
        (pow_nonneg (frozenRSProfile_nonneg v hpos x) 2)
  · filter_upwards [ae_tendsto_annularRSProfile v hpos] with x hx
    exact
      (hx.pow 2).mul
        ((tendsto_pairDistancePotential_annular
          v hv hpos x).pow 2)


/-- Pointwise annular convergence away from the three exceptional points. -/
theorem tendsto_annularRSProfile_of_ne
    (v : ℝ → ℝ)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (x : ℝ) (hx0 : x ≠ 0)
    (hxmid : x ≠ 1 / 2) (hx1 : x ≠ 1) :
    Tendsto (fun n => annularRSProfile v n x)
      atTop (nhds (frozenRSProfile v x)) := by
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

/-- Adding a continuous shift to the last coordinate preserves avoidance
of every single exceptional value almost everywhere. -/
theorem ae_ne_add_continuous_shift
    (s : ℝ × ℝ → ℝ) (hs : Continuous s) (c : ℝ) :
    ∀ᵐ p : (ℝ × ℝ) × ℝ ∂volume,
      p.2 + s p.1 ≠ c := by
  rw [Measure.volume_eq_prod]
  refine (Measure.ae_prod_iff_ae_ae ?_).2 ?_
  · change MeasurableSet
      ({p : (ℝ × ℝ) × ℝ | p.2 + s p.1 = c}ᶜ)
    exact
      (isClosed_eq
        (continuous_snd.add (hs.comp continuous_fst))
        continuous_const).measurableSet.compl
  · filter_upwards [] with uv
    filter_upwards [volume.ae_ne (c - s uv)] with x hx
    intro heq
    apply hx
    linarith

/-- Annular convergence may therefore be pulled through any such affine
coordinate of the three-variable crossing kernel. -/
theorem ae_tendsto_annularRSProfile_add_shift
    (v : ℝ → ℝ)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (s : ℝ × ℝ → ℝ) (hs : Continuous s) :
    ∀ᵐ p : (ℝ × ℝ) × ℝ ∂volume,
      Tendsto
        (fun n => annularRSProfile v n (p.2 + s p.1))
        atTop
        (nhds (frozenRSProfile v (p.2 + s p.1))) := by
  filter_upwards [
    ae_ne_add_continuous_shift s hs 0,
    ae_ne_add_continuous_shift s hs (1 / 2),
    ae_ne_add_continuous_shift s hs 1
  ] with p h0 hmid h1
  exact tendsto_annularRSProfile_of_ne
    v hpos (p.2 + s p.1) h0 hmid h1

/-- The frozen crossing kernel is integrable.  Its four cutoff conditions
form a closed subset of a compact box in the raw crossing coordinates. -/
theorem integrable_crossingRawKernel_one_frozen
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) :
    Integrable (crossingRawKernel 1 (frozenRSProfile v)) := by
  let A0 : Set ((ℝ × ℝ) × ℝ) :=
    (fun p => p.2) ⁻¹' Icc (0 : ℝ) 1
  let A1 : Set ((ℝ × ℝ) × ℝ) :=
    (fun p => p.2 + p.1.1) ⁻¹' Icc (0 : ℝ) 1
  let A2 : Set ((ℝ × ℝ) × ℝ) :=
    (fun p => p.2 + p.1.1 + p.1.2) ⁻¹' Icc (0 : ℝ) 1
  let A3 : Set ((ℝ × ℝ) × ℝ) :=
    (fun p => p.2 + p.1.2) ⁻¹' Icc (0 : ℝ) 1
  let K : Set ((ℝ × ℝ) × ℝ) := A0 ∩ A1 ∩ A2 ∩ A3
  have hKclosed : IsClosed K := by
    exact
      (((isClosed_Icc.preimage (by fun_prop)).inter
        (isClosed_Icc.preimage (by fun_prop))).inter
        (isClosed_Icc.preimage (by fun_prop))).inter
        (isClosed_Icc.preimage (by fun_prop))
  have hKsubset :
      K ⊆
        ((Icc (-(1 : ℝ)) 1 ×ˢ Icc (-(1 : ℝ)) 1) ×ˢ
          Icc (0 : ℝ) 1) := by
    intro p hp
    simp only [K, A0, A1, A2, A3, mem_inter_iff,
      mem_preimage, mem_Icc] at hp
    rcases hp with ⟨⟨⟨hx, hy⟩, hz⟩, hw⟩
    simp only [mem_prod, mem_Icc]
    refine ⟨⟨?_, ?_⟩, hx⟩
    · constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    · constructor <;> linarith [hx.1, hx.2, hw.1, hw.2]
  have hKcompact : IsCompact K :=
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).of_isClosed_subset
      hKclosed hKsubset
  have heq :
      crossingRawKernel 1 (frozenRSProfile v) =
        K.indicator
          (fun p : (ℝ × ℝ) × ℝ =>
            |p.1.1| * |p.1.2| *
              (v (p.2 - 1 / 2) *
                v (p.2 + p.1.1 - 1 / 2) *
                v (p.2 + p.1.1 + p.1.2 - 1 / 2) *
                v (p.2 + p.1.2 - 1 / 2))) := by
    funext p
    by_cases hx : p.2 ∈ Icc (0 : ℝ) 1 <;>
      by_cases hy : p.2 + p.1.1 ∈ Icc (0 : ℝ) 1 <;>
      by_cases hz : p.2 + p.1.1 + p.1.2 ∈ Icc (0 : ℝ) 1 <;>
      by_cases hw : p.2 + p.1.2 ∈ Icc (0 : ℝ) 1 <;>
      simp [crossingRawKernel, frozenRSProfile, K, A0, A1, A2, A3,
        hx, hy, hz, hw] <;> ring
  rw [heq, integrable_indicator_iff hKclosed.measurableSet]
  have hvcont : Continuous v := hv.continuous
  have hc :
      Continuous
        (fun p : (ℝ × ℝ) × ℝ =>
          |p.1.1| * |p.1.2| *
            (v (p.2 - 1 / 2) *
              v (p.2 + p.1.1 - 1 / 2) *
              v (p.2 + p.1.1 + p.1.2 - 1 / 2) *
              v (p.2 + p.1.2 - 1 / 2))) := by
    fun_prop
  exact hc.continuousOn.integrableOn_compact hKcompact

/-- The raw crossing kernel converges in integral from the smooth annular
profiles to the frozen cutoff profile. -/
theorem tendsto_integral_crossingRawKernel_annular
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n =>
        ∫ p : (ℝ × ℝ) × ℝ,
          crossingRawKernel 1 (annularRSProfile v n) p)
      atTop
      (nhds
        (∫ p : (ℝ × ℝ) × ℝ,
          crossingRawKernel 1 (frozenRSProfile v) p)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (crossingRawKernel 1 (frozenRSProfile v))
  · intro n
    exact
      (crossingRawKernel_integrable_of_continuous_compact
        1 (annularRSProfile v n) one_ne_zero
        (annularRSProfile_contDiff v n hv hpos).continuous
        (annularRSProfile_hasCompactSupport v n)).aestronglyMeasurable
  · exact integrable_crossingRawKernel_one_frozen v hv
  · intro n
    filter_upwards [] with p
    have hx :=
      annularRSProfile_le_frozen v n hpos p.2
    have hy :=
      annularRSProfile_le_frozen v n hpos (p.2 + p.1.1)
    have hz :=
      annularRSProfile_le_frozen v n hpos
        (p.2 + p.1.1 + p.1.2)
    have hw :=
      annularRSProfile_le_frozen v n hpos (p.2 + p.1.2)
    have hxy :
        annularRSProfile v n p.2 *
            annularRSProfile v n (p.2 + p.1.1) ≤
          frozenRSProfile v p.2 *
            frozenRSProfile v (p.2 + p.1.1) :=
      mul_le_mul hx.2 hy.2 hy.1
        (frozenRSProfile_nonneg v hpos p.2)
    have hxyz :
        annularRSProfile v n p.2 *
              annularRSProfile v n (p.2 + p.1.1) *
              annularRSProfile v n (p.2 + p.1.1 + p.1.2) ≤
          frozenRSProfile v p.2 *
              frozenRSProfile v (p.2 + p.1.1) *
              frozenRSProfile v (p.2 + p.1.1 + p.1.2) :=
      mul_le_mul hxy hz.2 hz.1
        (mul_nonneg
          (frozenRSProfile_nonneg v hpos p.2)
          (frozenRSProfile_nonneg v hpos (p.2 + p.1.1)))
    have hall :
        annularRSProfile v n p.2 *
              annularRSProfile v n (p.2 + p.1.1) *
              annularRSProfile v n (p.2 + p.1.1 + p.1.2) *
              annularRSProfile v n (p.2 + p.1.2) ≤
          frozenRSProfile v p.2 *
              frozenRSProfile v (p.2 + p.1.1) *
              frozenRSProfile v (p.2 + p.1.1 + p.1.2) *
              frozenRSProfile v (p.2 + p.1.2) :=
      mul_le_mul hxyz hw.2 hw.1
        (mul_nonneg
          (mul_nonneg
            (frozenRSProfile_nonneg v hpos p.2)
            (frozenRSProfile_nonneg v hpos (p.2 + p.1.1)))
          (frozenRSProfile_nonneg v hpos
            (p.2 + p.1.1 + p.1.2)))
    have hkernelNonneg :
        0 ≤ crossingRawKernel 1 (annularRSProfile v n) p := by
      simp only [crossingRawKernel, div_one, one_mul]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hkernelNonneg]
    simpa only [crossingRawKernel, div_one, one_mul] using
      mul_le_mul_of_nonneg_left hall
        (mul_nonneg abs_nonneg abs_nonneg)
  · have hx :=
      ae_tendsto_annularRSProfile_add_shift
        v hpos (fun _ => 0) (by fun_prop)
    have hy :=
      ae_tendsto_annularRSProfile_add_shift
        v hpos (fun uv => uv.1) (by fun_prop)
    have hz :=
      ae_tendsto_annularRSProfile_add_shift
        v hpos (fun uv => uv.1 + uv.2) (by fun_prop)
    have hw :=
      ae_tendsto_annularRSProfile_add_shift
        v hpos (fun uv => uv.2) (by fun_prop)
    filter_upwards [hx, hy, hz, hw] with p hx hy hz hw
    have hprod := ((hx.mul hy).mul hz).mul hw
    simpa only [crossingRawKernel, div_one, one_mul, add_zero] using
      (tendsto_const_nhds.mul hprod)

/-- For every integrable profile, the raw kernel at unit scale is exactly
the displayed crossing functional. -/
theorem integral_crossingRawKernel_one_eq_crossingFunctional
    (r : ℝ → ℝ)
    (hint : Integrable (crossingRawKernel 1 r)) :
    (∫ p : (ℝ × ℝ) × ℝ, crossingRawKernel 1 r p) =
      crossingFunctional r := by
  have hiter :
      (∫ p : (ℝ × ℝ) × ℝ, crossingRawKernel 1 r p) =
        ∫ uv : ℝ × ℝ, ∫ x : ℝ,
          crossingRawKernel 1 r (uv, x) := by
    rw [Measure.volume_eq_prod, integral_prod _ hint]
  have hcoordinate :
      twoPairCoordinateIntegral (crossingTwoPairCore 1 r) =
        ∫ uv : ℝ × ℝ, ∫ x : ℝ,
          crossingRawKernel 1 r (uv, x) := by
    unfold twoPairCoordinateIntegral crossingTwoPairCore
    apply integral_congr_ae
    filter_upwards [] with uv
    calc
      |uv.1| * |uv.2| *
            (1 * ∫ x : ℝ,
              r x * r (x + uv.1 / 1) *
                r (x + (uv.1 + uv.2) / 1) *
                r (x + uv.2 / 1)) =
          (|uv.1| * |uv.2| * 1) *
            ∫ x : ℝ,
              r x * r (x + uv.1 / 1) *
                r (x + (uv.1 + uv.2) / 1) *
                r (x + uv.2 / 1) := by ring
      _ = ∫ x : ℝ, (|uv.1| * |uv.2| * 1) *
            (r x * r (x + uv.1 / 1) *
              r (x + (uv.1 + uv.2) / 1) *
              r (x + uv.2 / 1)) := by
        rw [integral_const_mul]
      _ = ∫ x : ℝ, crossingRawKernel 1 r (uv, x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [crossingRawKernel]
        ring
  calc
    (∫ p : (ℝ × ℝ) × ℝ, crossingRawKernel 1 r p) =
        ∫ uv : ℝ × ℝ, ∫ x : ℝ,
          crossingRawKernel 1 r (uv, x) := hiter
    _ = twoPairCoordinateIntegral (crossingTwoPairCore 1 r) :=
      hcoordinate.symm
    _ = crossingFunctional r := by
      simpa using
        crossingTwoPairCoordinateIntegral_eq
          1 r zero_lt_one hint

/-- The crossing functional itself therefore converges to the literal
frozen-profile value. -/
theorem tendsto_crossingFunctional_annular
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n => crossingFunctional (annularRSProfile v n))
      atTop
      (nhds (crossingFunctional (frozenRSProfile v))) := by
  have hann :
      (fun n => crossingFunctional (annularRSProfile v n)) =
        (fun n =>
          ∫ p : (ℝ × ℝ) × ℝ,
            crossingRawKernel 1 (annularRSProfile v n) p) := by
    funext n
    symm
    exact integral_crossingRawKernel_one_eq_crossingFunctional
      (annularRSProfile v n)
      (crossingRawKernel_integrable_of_continuous_compact
        1 (annularRSProfile v n) one_ne_zero
        (annularRSProfile_contDiff v n hv hpos).continuous
        (annularRSProfile_hasCompactSupport v n))
  have hfrozen :
      crossingFunctional (frozenRSProfile v) =
        ∫ p : (ℝ × ℝ) × ℝ,
          crossingRawKernel 1 (frozenRSProfile v) p := by
    symm
    exact integral_crossingRawKernel_one_eq_crossingFunctional
      (frozenRSProfile v)
      (integrable_crossingRawKernel_one_frozen v hv)
  rw [hann, hfrozen]
  exact tendsto_integral_crossingRawKernel_annular v hv hpos


/-- All five component limits assemble into convergence of the complete
quartic Rudnick--Sarnak scalar. -/
theorem tendsto_quarticRSScalar_annular
    (mu : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n => quarticRSScalar mu (annularRSProfile v n))
      atTop
      (nhds (quarticRSScalar mu (frozenRSProfile v))) := by
  have hfour :=
    tendsto_integral_annularRSProfile_pow_four v hv hpos
  have h31 :=
    tendsto_distanceIntegral_annularRSProfile_pows
      v hv hpos 3 1 (by norm_num) (by norm_num)
  have h22 :=
    tendsto_distanceIntegral_annularRSProfile_pows
      v hv hpos 2 2 (by norm_num) (by norm_num)
  have hpair :=
    tendsto_pairSquaredPotentialIntegral_annular v hv hpos
  have hcross :=
    tendsto_crossingFunctional_annular v hv hpos
  unfold quarticRSScalar
  exact
    ((hfour.add
      (tendsto_const_nhds.mul
        ((tendsto_const_nhds.mul h31).add
          (tendsto_const_nhds.mul h22)))).add
      (tendsto_const_nhds.mul
        ((tendsto_const_nhds.mul hpair).add hcross)))

/-- The fixed-profile complex main term follows the same annular limit. -/
theorem tendsto_frozenQuarticRSMain_annular
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (g : Fin 4 → ℝ → ℂ) :
    Tendsto
      (fun n =>
        RSBlockMomentBridge.frozenQuarticRSMain
          (annularRSProfile v n) g)
      atTop
      (nhds
        (RSBlockMomentBridge.frozenQuarticRSMain
          (frozenRSProfile v) g)) := by
  have hscalar :=
    tendsto_quarticRSScalar_annular
      (4999 / 10000 : ℝ) v hv hpos
  have hreal :
      Tendsto
        (fun n =>
          (4999 / 10000 : ℝ) *
            quarticRSScalar (4999 / 10000 : ℝ)
              (annularRSProfile v n))
        atTop
        (nhds
          ((4999 / 10000 : ℝ) *
            quarticRSScalar (4999 / 10000 : ℝ)
              (frozenRSProfile v))) :=
    tendsto_const_nhds.mul hscalar
  have hcast :
      Tendsto
        (fun n =>
          (((4999 / 10000 : ℝ) *
            quarticRSScalar (4999 / 10000 : ℝ)
              (annularRSProfile v n) : ℝ) : ℂ))
        atTop
        (nhds
          ((((4999 / 10000 : ℝ) *
            quarticRSScalar (4999 / 10000 : ℝ)
              (frozenRSProfile v) : ℝ) : ℂ))) := by
    simpa only [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.continuous.tendsto _).comp hreal
  unfold RSBlockMomentBridge.frozenQuarticRSMain
  exact tendsto_const_nhds.mul hcast

/-- The scalar bridge required by the slow RS diagonal is now discharged
for the explicit annular profiles. -/
theorem RS1996ZetaInputs.exists_tendsto_annularProfile_diagonal_frozenMain
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (g : Fin 4 → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ stage : ℝ → ℕ,
      Tendsto stage atTop atTop ∧
      Tendsto
        (fun T =>
          RSBlockMomentBridge.normalizedFrozenQuarticRSStatistic
            (Z := Z) (annularRSProfile v (stage T)) g T)
        atTop
        (nhds
          (RSBlockMomentBridge.frozenQuarticRSMain
            (frozenRSProfile v) g)) := by
  apply
    RSAnnularDiagonal.RS1996ZetaInputs.exists_tendsto_annularProfile_diagonal
      hrs v hv hpos g hg
  exact tendsto_frozenQuarticRSMain_annular v hv hpos g


/-- Concrete R-9506 specialization: its rational profile supplies both
smoothness and strict positivity, so no profile regularity premise remains. -/
theorem RS1996ZetaInputs.exists_tendsto_v9506_annularQuarticMain
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (g : Fin 4 → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ stage : ℝ → ℕ,
      Tendsto stage atTop atTop ∧
      Tendsto
        (fun T =>
          RSBlockMomentBridge.normalizedFrozenQuarticRSStatistic
            (Z := Z) (annularRSProfile QuarticWindowWitnesses.v9506 (stage T))
            g T)
        atTop
        (nhds
          (RSBlockMomentBridge.frozenQuarticRSMain
            (frozenRSProfile QuarticWindowWitnesses.v9506) g)) := by
  exact
    RS1996ZetaInputs.exists_tendsto_annularProfile_diagonal_frozenMain
      hrs QuarticWindowWitnesses.v9506
        QuarticWindowWitnesses.v9506_contDiff
        (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)
        g hg

end RH.Zeta85.RSMainTermConvergence

end
