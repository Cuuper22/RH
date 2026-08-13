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
    rw [frozenRSProfile, Set.indicator_of_mem hx,
      QuarticGramFamily.supportedFullProfile,
      Set.indicator_of_mem hcenter]
  · have hcenter : x - 1 / 2 ∉
        Icc (-(1 : ℝ) / 2) (1 / 2) := by
      intro h
      apply hx
      constructor <;> linarith [h.1, h.2]
    rw [frozenRSProfile, Set.indicator_of_notMem hx,
      QuarticGramFamily.supportedFullProfile,
      Set.indicator_of_notMem hcenter]

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
      simp [frozenRSProfile, hx, zero_pow hk.ne']
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
    by_cases hx : z.1 ∈ Icc (0 : ℝ) 1
    · by_cases hy : z.2 ∈ Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem (show z ∈
            Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from ⟨hx, hy⟩)]
        simp [distanceKernel, frozenRSProfile, hx, hy]
      · rw [Set.indicator_of_notMem
            (show z ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 by
              intro hz
              exact hy hz.2)]
        simp [distanceKernel, frozenRSProfile, hx, hy,
          zero_pow hb.ne']
    · rw [Set.indicator_of_notMem
          (show z ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 by
            intro hz
            exact hx hz.1)]
      simp [distanceKernel, frozenRSProfile, hx,
        zero_pow ha.ne']
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
      exact
        mul_nonneg
          (mul_nonneg (abs_nonneg _)
            (pow_nonneg hx.1 a))
          (pow_nonneg hy.1 b)
    rw [Real.norm_eq_abs, abs_of_nonneg hkernelNonneg]
    unfold distanceKernel
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hxpow (abs_nonneg _))
      hypow
      (pow_nonneg hy.1 b)
      (mul_nonneg (abs_nonneg _)
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
        _ ≤ 1 + |x| := by linarith
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
      mul_nonneg (abs_nonneg _)
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
          mul_nonneg (abs_nonneg _)
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
    mul_nonneg (abs_nonneg _)
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
  change AEStronglyMeasurable
    (fun x : ℝ =>
      ∫ y : ℝ, |y - x| * annularRSProfile v n y)
  exact hk.integral_prod_right'.aestronglyMeasurable

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
    · simp only [hxzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        zero_mul, norm_zero]
      positivity
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
              ‖pairDistancePotential (annularRSProfile v n) x‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hpotentialNonneg]
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
    by_cases hx : p.2 ∈ Icc (0 : ℝ) 1
    · by_cases hy : p.2 + p.1.1 ∈ Icc (0 : ℝ) 1
      · by_cases hz : p.2 + p.1.1 + p.1.2 ∈ Icc (0 : ℝ) 1
        · by_cases hw : p.2 + p.1.2 ∈ Icc (0 : ℝ) 1
          · rw [Set.indicator_of_mem
                (show p ∈ K by
                  exact ⟨⟨⟨hx, hy⟩, hz⟩, hw⟩)]
            have hz' :
                p.2 + (p.1.1 + p.1.2) ∈ Icc (0 : ℝ) 1 := by
              simpa only [add_assoc] using hz
            simp only [crossingRawKernel, div_one, one_mul, frozenRSProfile]
            rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
              Set.indicator_of_mem hz', Set.indicator_of_mem hw]
            ring
          · rw [Set.indicator_of_notMem
                (show p ∉ K by
                  intro hp
                  exact hw hp.2)]
            simp [crossingRawKernel, frozenRSProfile, hx, hy, hz, hw]
        · rw [Set.indicator_of_notMem
              (show p ∉ K by
                intro hp
                exact hz hp.1.2)]
          have hz' :
              p.2 + (p.1.1 + p.1.2) ∉ Icc (0 : ℝ) 1 := by
            simpa only [add_assoc] using hz
          simp only [crossingRawKernel, div_one, one_mul, frozenRSProfile]
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
            Set.indicator_of_notMem hz']
          simp
      · rw [Set.indicator_of_notMem
            (show p ∉ K by
              intro hp
              exact hy hp.1.1.2)]
        simp [crossingRawKernel, frozenRSProfile, hx, hy]
    · rw [Set.indicator_of_notMem
          (show p ∉ K by
            intro hp
            exact hx hp.1.1.1)]
      simp [crossingRawKernel, frozenRSProfile, hx]
  rw [heq]
  rw [integrable_indicator_iff hKclosed.measurableSet]
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
      have hz' :
          0 ≤ annularRSProfile v n
            (p.2 + (p.1.1 + p.1.2)) := by
        simpa only [add_assoc] using hz.1
      exact
        mul_nonneg
          (mul_nonneg (abs_nonneg p.1.1) (abs_nonneg p.1.2))
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg hx.1 hy.1) hz')
            hw.1)
    rw [Real.norm_eq_abs, abs_of_nonneg hkernelNonneg]
    have hall' := mul_le_mul_of_nonneg_left hall
      (mul_nonneg (abs_nonneg p.1.1) (abs_nonneg p.1.2))
    simpa only [crossingRawKernel, div_one, one_mul, add_assoc] using hall'
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



/-- The evaluated degree-one RS scalar. -/
def linearRSScalar (mu : ℝ) (r : ℝ → ℝ) : ℝ :=
  mu * ∫ x : ℝ, r x

/-- The evaluated degree-two RS scalar at the frozen bandwidth. -/
def quadraticRSScalar (r : ℝ → ℝ) : ℝ :=
  (4999 / 10000 : ℝ) *
    ((∫ x : ℝ, r x ^ 2) +
      (4999 / 10000 : ℝ) ^ 2 * distanceIntegral r r)

/-- The evaluated degree-three RS scalar at the frozen bandwidth. -/
def cubicRSScalar (r : ℝ → ℝ) : ℝ :=
  (4999 / 10000 : ℝ) *
    ((∫ x : ℝ, r x ^ 3) +
      3 * (4999 / 10000 : ℝ) ^ 2 *
        distanceIntegral (fun x => r x ^ 2) r)

/-- Degree-one scalar convergence follows from the profile-mass limit. -/
theorem tendsto_linearRSScalar_annular
    (mu : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n => linearRSScalar mu (annularRSProfile v n))
      atTop
      (nhds (linearRSScalar mu (frozenRSProfile v))) := by
  have hmass :=
    tendsto_integral_annularRSProfile_pow
      v hv hpos 1 (by norm_num)
  have hscaled :
      Tendsto
        (fun n => mu * ∫ x : ℝ, annularRSProfile v n x ^ 1)
        atTop
        (nhds (mu * ∫ x : ℝ, frozenRSProfile v x ^ 1)) :=
    (show Tendsto (fun _ : ℕ => mu) atTop (nhds mu) from
      tendsto_const_nhds).mul hmass
  simpa only [linearRSScalar, pow_one] using hscaled

/-- Degree-two scalar convergence follows from the mass-square and one-pair
contraction limits. -/
theorem tendsto_quadraticRSScalar_annular
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n => quadraticRSScalar (annularRSProfile v n))
      atTop
      (nhds (quadraticRSScalar (frozenRSProfile v))) := by
  have hpow :=
    tendsto_integral_annularRSProfile_pow
      v hv hpos 2 (by norm_num)
  have hdist :=
    tendsto_distanceIntegral_annularRSProfile_pows
      v hv hpos 1 1 (by norm_num) (by norm_num)
  have hweighted :
      Tendsto
        (fun n =>
          (4999 / 10000 : ℝ) ^ 2 *
            distanceIntegral
              (fun x => annularRSProfile v n x ^ 1)
              (fun y => annularRSProfile v n y ^ 1))
        atTop
        (nhds
          ((4999 / 10000 : ℝ) ^ 2 *
            distanceIntegral
              (fun x => frozenRSProfile v x ^ 1)
              (fun y => frozenRSProfile v y ^ 1))) :=
    (show Tendsto
        (fun _ : ℕ => (4999 / 10000 : ℝ) ^ 2)
        atTop (nhds ((4999 / 10000 : ℝ) ^ 2)) from
      tendsto_const_nhds).mul hdist
  have hsum := hpow.add hweighted
  have hscaled :=
    (show Tendsto
        (fun _ : ℕ => (4999 / 10000 : ℝ))
        atTop (nhds (4999 / 10000 : ℝ)) from
      tendsto_const_nhds).mul hsum
  simpa only [quadraticRSScalar, pow_one] using hscaled

/-- Degree-three scalar convergence follows from the cube-mass and
two-one contraction limits. -/
theorem tendsto_cubicRSScalar_annular
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n => cubicRSScalar (annularRSProfile v n))
      atTop
      (nhds (cubicRSScalar (frozenRSProfile v))) := by
  have hpow :=
    tendsto_integral_annularRSProfile_pow
      v hv hpos 3 (by norm_num)
  have hdist :=
    tendsto_distanceIntegral_annularRSProfile_pows
      v hv hpos 2 1 (by norm_num) (by norm_num)
  have hweighted :
      Tendsto
        (fun n =>
          (3 * (4999 / 10000 : ℝ) ^ 2) *
            distanceIntegral
              (fun x => annularRSProfile v n x ^ 2)
              (fun y => annularRSProfile v n y ^ 1))
        atTop
        (nhds
          ((3 * (4999 / 10000 : ℝ) ^ 2) *
            distanceIntegral
              (fun x => frozenRSProfile v x ^ 2)
              (fun y => frozenRSProfile v y ^ 1))) :=
    (show Tendsto
        (fun _ : ℕ => 3 * (4999 / 10000 : ℝ) ^ 2)
        atTop (nhds (3 * (4999 / 10000 : ℝ) ^ 2)) from
      tendsto_const_nhds).mul hdist
  have hsum := hpow.add hweighted
  have hscaled :=
    (show Tendsto
        (fun _ : ℕ => (4999 / 10000 : ℝ))
        atTop (nhds (4999 / 10000 : ℝ)) from
      tendsto_const_nhds).mul hsum
  simpa only [cubicRSScalar, pow_one] using hscaled

/-- The literal evaluated degree-one complex main term. -/
def evaluatedLinearRSMain
    (mu : ℝ) (r : ℝ → ℝ) (g : Fin 1 → ℝ → ℂ) : ℂ :=
  rsHeightFactor g * ((linearRSScalar mu r : ℝ) : ℂ)

/-- The literal evaluated degree-two complex main term. -/
def evaluatedQuadraticRSMain
    (r : ℝ → ℝ) (g : Fin 2 → ℝ → ℂ) : ℂ :=
  rsHeightFactor g * ((quadraticRSScalar r : ℝ) : ℂ)

/-- The literal evaluated degree-three complex main term. -/
def evaluatedCubicRSMain
    (r : ℝ → ℝ) (g : Fin 3 → ℝ → ℂ) : ℂ :=
  rsHeightFactor g * ((cubicRSScalar r : ℝ) : ℂ)

/-- The unevaluated degree-one fixed RS main converges through the annular
profiles to its literal frozen value. -/
theorem tendsto_frozenLinearRSMain_annular
    (mu : ℝ) (hmu : 0 < mu)
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (g : Fin 1 → ℝ → ℂ) :
    Tendsto
      (fun n =>
        RSBlockMomentBridge.frozenLinearRSMain
          mu (annularRSProfile v n) g)
      atTop
      (nhds (evaluatedLinearRSMain mu (frozenRSProfile v) g)) := by
  have hscalar :=
    tendsto_linearRSScalar_annular mu v hv hpos
  have hcast :
      Tendsto
        (fun n =>
          ((linearRSScalar mu (annularRSProfile v n) : ℝ) : ℂ))
        atTop
        (nhds
          ((linearRSScalar mu (frozenRSProfile v) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.continuous.tendsto _).comp hscalar
  have hmain :
      Tendsto
        (fun n =>
          rsHeightFactor g *
            ((linearRSScalar mu (annularRSProfile v n) : ℝ) : ℂ))
        atTop
        (nhds
          (rsHeightFactor g *
            ((linearRSScalar mu (frozenRSProfile v) : ℝ) : ℂ))) :=
    (show Tendsto
        (fun _ : ℕ => rsHeightFactor g)
        atTop (nhds (rsHeightFactor g)) from
      tendsto_const_nhds).mul hcast
  have heval (n : ℕ) :
      RSBlockMomentBridge.frozenLinearRSMain
          mu (annularRSProfile v n) g =
        evaluatedLinearRSMain mu (annularRSProfile v n) g := by
    rw [RSBlockMomentBridge.frozenLinearRSMain_eq
      mu (annularRSProfile v n) g hmu]
    rfl
  rw [show
    (fun n =>
      RSBlockMomentBridge.frozenLinearRSMain
        mu (annularRSProfile v n) g) =
      (fun n => evaluatedLinearRSMain mu (annularRSProfile v n) g) by
        funext n
        exact heval n]
  simpa only [evaluatedLinearRSMain] using hmain

/-- The unevaluated degree-two fixed RS main converges through the annular
profiles to its literal frozen value. -/
theorem tendsto_frozenQuadraticRSMain_annular
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (g : Fin 2 → ℝ → ℂ) :
    Tendsto
      (fun n =>
        RSBlockMomentBridge.frozenQuadraticRSMain
          (annularRSProfile v n) g)
      atTop
      (nhds (evaluatedQuadraticRSMain (frozenRSProfile v) g)) := by
  have hscalar :=
    tendsto_quadraticRSScalar_annular v hv hpos
  have hcast :
      Tendsto
        (fun n =>
          ((quadraticRSScalar (annularRSProfile v n) : ℝ) : ℂ))
        atTop
        (nhds
          ((quadraticRSScalar (frozenRSProfile v) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.continuous.tendsto _).comp hscalar
  have hmain :
      Tendsto
        (fun n =>
          rsHeightFactor g *
            ((quadraticRSScalar (annularRSProfile v n) : ℝ) : ℂ))
        atTop
        (nhds
          (rsHeightFactor g *
            ((quadraticRSScalar (frozenRSProfile v) : ℝ) : ℂ))) :=
    (show Tendsto
        (fun _ : ℕ => rsHeightFactor g)
        atTop (nhds (rsHeightFactor g)) from
      tendsto_const_nhds).mul hcast
  have heval (n : ℕ) :
      RSBlockMomentBridge.frozenQuadraticRSMain
          (annularRSProfile v n) g =
        evaluatedQuadraticRSMain (annularRSProfile v n) g := by
    rw [RSBlockMomentBridge.frozenQuadraticRSMain_eq
      (annularRSProfile v n) g
      (annularRSProfile_contDiff v n hv hpos).continuous
      (annularRSProfile_hasCompactSupport v n)]
    rfl
  rw [show
    (fun n =>
      RSBlockMomentBridge.frozenQuadraticRSMain
        (annularRSProfile v n) g) =
      (fun n => evaluatedQuadraticRSMain (annularRSProfile v n) g) by
        funext n
        exact heval n]
  simpa only [evaluatedQuadraticRSMain] using hmain

/-- The unevaluated degree-three fixed RS main converges through the annular
profiles to its literal frozen value. -/
theorem tendsto_frozenCubicRSMain_annular
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (g : Fin 3 → ℝ → ℂ) :
    Tendsto
      (fun n =>
        RSBlockMomentBridge.frozenCubicRSMain
          (annularRSProfile v n) g)
      atTop
      (nhds (evaluatedCubicRSMain (frozenRSProfile v) g)) := by
  have hscalar :=
    tendsto_cubicRSScalar_annular v hv hpos
  have hcast :
      Tendsto
        (fun n =>
          ((cubicRSScalar (annularRSProfile v n) : ℝ) : ℂ))
        atTop
        (nhds
          ((cubicRSScalar (frozenRSProfile v) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.continuous.tendsto _).comp hscalar
  have hmain :
      Tendsto
        (fun n =>
          rsHeightFactor g *
            ((cubicRSScalar (annularRSProfile v n) : ℝ) : ℂ))
        atTop
        (nhds
          (rsHeightFactor g *
            ((cubicRSScalar (frozenRSProfile v) : ℝ) : ℂ))) :=
    (show Tendsto
        (fun _ : ℕ => rsHeightFactor g)
        atTop (nhds (rsHeightFactor g)) from
      tendsto_const_nhds).mul hcast
  have heval (n : ℕ) :
      RSBlockMomentBridge.frozenCubicRSMain
          (annularRSProfile v n) g =
        evaluatedCubicRSMain (annularRSProfile v n) g := by
    rw [RSBlockMomentBridge.frozenCubicRSMain_eq
      (annularRSProfile v n) g
      (annularRSProfile_contDiff v n hv hpos).continuous
      (annularRSProfile_hasCompactSupport v n)]
    rfl
  rw [show
    (fun n =>
      RSBlockMomentBridge.frozenCubicRSMain
        (annularRSProfile v n) g) =
      (fun n => evaluatedCubicRSMain (annularRSProfile v n) g) by
        funext n
        exact heval n]
  simpa only [evaluatedCubicRSMain] using hmain

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
  have h31w :
      Tendsto
        (fun n =>
          (4 : ℝ) *
            distanceIntegral
              (fun x => annularRSProfile v n x ^ 3)
              (fun y => annularRSProfile v n y ^ 1))
        atTop
        (nhds
          ((4 : ℝ) *
            distanceIntegral
              (fun x => frozenRSProfile v x ^ 3)
              (fun y => frozenRSProfile v y ^ 1))) :=
    (show Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds (4 : ℝ))
      from tendsto_const_nhds).mul h31
  have h22w :
      Tendsto
        (fun n =>
          (2 : ℝ) *
            distanceIntegral
              (fun x => annularRSProfile v n x ^ 2)
              (fun y => annularRSProfile v n y ^ 2))
        atTop
        (nhds
          ((2 : ℝ) *
            distanceIntegral
              (fun x => frozenRSProfile v x ^ 2)
              (fun y => frozenRSProfile v y ^ 2))) :=
    (show Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds (2 : ℝ))
      from tendsto_const_nhds).mul h22
  have hmu2 :
      Tendsto
        (fun n =>
          mu ^ 2 *
            ((4 : ℝ) *
                distanceIntegral
                  (fun x => annularRSProfile v n x ^ 3)
                  (fun y => annularRSProfile v n y ^ 1) +
              (2 : ℝ) *
                distanceIntegral
                  (fun x => annularRSProfile v n x ^ 2)
                  (fun y => annularRSProfile v n y ^ 2)))
        atTop
        (nhds
          (mu ^ 2 *
            ((4 : ℝ) *
                distanceIntegral
                  (fun x => frozenRSProfile v x ^ 3)
                  (fun y => frozenRSProfile v y ^ 1) +
              (2 : ℝ) *
                distanceIntegral
                  (fun x => frozenRSProfile v x ^ 2)
                  (fun y => frozenRSProfile v y ^ 2)))) :=
    (show Tendsto (fun _ : ℕ => mu ^ 2) atTop (nhds (mu ^ 2))
      from tendsto_const_nhds).mul (h31w.add h22w)
  have hpairw :
      Tendsto
        (fun n =>
          (2 : ℝ) *
            pairSquaredPotentialIntegral (annularRSProfile v n))
        atTop
        (nhds
          ((2 : ℝ) *
            pairSquaredPotentialIntegral (frozenRSProfile v))) :=
    (show Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds (2 : ℝ))
      from tendsto_const_nhds).mul hpair
  have hmu4 :
      Tendsto
        (fun n =>
          mu ^ 4 *
            ((2 : ℝ) *
                pairSquaredPotentialIntegral (annularRSProfile v n) +
              crossingFunctional (annularRSProfile v n)))
        atTop
        (nhds
          (mu ^ 4 *
            ((2 : ℝ) *
                pairSquaredPotentialIntegral (frozenRSProfile v) +
              crossingFunctional (frozenRSProfile v)))) :=
    (show Tendsto (fun _ : ℕ => mu ^ 4) atTop (nhds (mu ^ 4))
      from tendsto_const_nhds).mul (hpairw.add hcross)
  simpa only [pow_one] using (hfour.add hmu2).add hmu4

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
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.continuous.tendsto _).comp hreal
  unfold RSBlockMomentBridge.frozenQuarticRSMain
  exact tendsto_const_nhds.mul hcast


/-- The degree-one fixed-test estimates and the sharpening R-9506 profile
can be followed on one slow height diagonal. -/
theorem RS1996ZetaInputs.exists_tendsto_v9506_annularLinearMain
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (g : Fin 1 → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ stage : ℝ → ℕ,
      Tendsto stage atTop atTop ∧
      Tendsto
        (fun T =>
          RSBlockMomentBridge.normalizedFrozenLinearRSStatistic
            (Z := Z) (4999 / 10000 : ℝ)
            (annularRSProfile QuarticWindowWitnesses.v9506 (stage T))
            g T)
        atTop
        (nhds
          (evaluatedLinearRSMain (4999 / 10000 : ℝ)
            (frozenRSProfile QuarticWindowWitnesses.v9506) g)) := by
  apply RSBlockMomentBridge.exists_tendsto_slow_diagonal
    (fun n T =>
      RSBlockMomentBridge.normalizedFrozenLinearRSStatistic
        (Z := Z) (4999 / 10000 : ℝ)
        (annularRSProfile QuarticWindowWitnesses.v9506 n) g T)
    (fun n =>
      RSBlockMomentBridge.frozenLinearRSMain
        (4999 / 10000 : ℝ)
        (annularRSProfile QuarticWindowWitnesses.v9506 n) g)
    (evaluatedLinearRSMain (4999 / 10000 : ℝ)
      (frozenRSProfile QuarticWindowWitnesses.v9506) g)
  · intro n
    exact
      RSBlockMomentBridge.RS1996ZetaInputs.tendsto_normalizedFrozenLinearRSStatistic
        hrs (4999 / 10000 : ℝ)
        (annularRSProfile QuarticWindowWitnesses.v9506 n)
        (annularRSProfile_hasCompactSupport
          QuarticWindowWitnesses.v9506 n)
        ((annularRSProfile_contDiff
          QuarticWindowWitnesses.v9506 n
          QuarticWindowWitnesses.v9506_contDiff
          (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)).of_le
            (WithTop.coe_le_coe.2
              (show (1 : ℕ∞) ≤ ⊤ from le_top)))
        g hg
  · exact
      tendsto_frozenLinearRSMain_annular
        (4999 / 10000 : ℝ) (by norm_num)
        QuarticWindowWitnesses.v9506
        QuarticWindowWitnesses.v9506_contDiff
        (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)
        g

/-- The degree-two fixed-test estimates and the sharpening R-9506 profile
can be followed on one slow height diagonal. -/
theorem RS1996ZetaInputs.exists_tendsto_v9506_annularQuadraticMain
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (g : Fin 2 → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ stage : ℝ → ℕ,
      Tendsto stage atTop atTop ∧
      Tendsto
        (fun T =>
          RSBlockMomentBridge.normalizedFrozenQuadraticRSStatistic
            (Z := Z)
            (annularRSProfile QuarticWindowWitnesses.v9506 (stage T))
            g T)
        atTop
        (nhds
          (evaluatedQuadraticRSMain
            (frozenRSProfile QuarticWindowWitnesses.v9506) g)) := by
  apply RSBlockMomentBridge.exists_tendsto_slow_diagonal
    (fun n T =>
      RSBlockMomentBridge.normalizedFrozenQuadraticRSStatistic
        (Z := Z)
        (annularRSProfile QuarticWindowWitnesses.v9506 n) g T)
    (fun n =>
      RSBlockMomentBridge.frozenQuadraticRSMain
        (annularRSProfile QuarticWindowWitnesses.v9506 n) g)
    (evaluatedQuadraticRSMain
      (frozenRSProfile QuarticWindowWitnesses.v9506) g)
  · intro n
    exact
      RSBlockMomentBridge.RS1996ZetaInputs.tendsto_normalizedFrozenQuadraticRSStatistic
        hrs
        (annularRSProfile QuarticWindowWitnesses.v9506 n)
        (annularRSProfile_hasCompactSupport
          QuarticWindowWitnesses.v9506 n)
        ((annularRSProfile_contDiff
          QuarticWindowWitnesses.v9506 n
          QuarticWindowWitnesses.v9506_contDiff
          (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)).of_le
            (WithTop.coe_le_coe.2
              (show (1 : ℕ∞) ≤ ⊤ from le_top)))
        (fun x hx =>
          annularRSProfile_support
            QuarticWindowWitnesses.v9506 n x hx)
        g hg
  · exact
      tendsto_frozenQuadraticRSMain_annular
        QuarticWindowWitnesses.v9506
        QuarticWindowWitnesses.v9506_contDiff
        (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)
        g

/-- The degree-three fixed-test estimates and the sharpening R-9506 profile
can be followed on one slow height diagonal. -/
theorem RS1996ZetaInputs.exists_tendsto_v9506_annularCubicMain
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (g : Fin 3 → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ stage : ℝ → ℕ,
      Tendsto stage atTop atTop ∧
      Tendsto
        (fun T =>
          RSBlockMomentBridge.normalizedFrozenCubicRSStatistic
            (Z := Z)
            (annularRSProfile QuarticWindowWitnesses.v9506 (stage T))
            g T)
        atTop
        (nhds
          (evaluatedCubicRSMain
            (frozenRSProfile QuarticWindowWitnesses.v9506) g)) := by
  apply RSBlockMomentBridge.exists_tendsto_slow_diagonal
    (fun n T =>
      RSBlockMomentBridge.normalizedFrozenCubicRSStatistic
        (Z := Z)
        (annularRSProfile QuarticWindowWitnesses.v9506 n) g T)
    (fun n =>
      RSBlockMomentBridge.frozenCubicRSMain
        (annularRSProfile QuarticWindowWitnesses.v9506 n) g)
    (evaluatedCubicRSMain
      (frozenRSProfile QuarticWindowWitnesses.v9506) g)
  · intro n
    exact
      RSBlockMomentBridge.RS1996ZetaInputs.tendsto_normalizedFrozenCubicRSStatistic
        hrs
        (annularRSProfile QuarticWindowWitnesses.v9506 n)
        (annularRSProfile_hasCompactSupport
          QuarticWindowWitnesses.v9506 n)
        ((annularRSProfile_contDiff
          QuarticWindowWitnesses.v9506 n
          QuarticWindowWitnesses.v9506_contDiff
          (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)).of_le
            (WithTop.coe_le_coe.2
              (show (1 : ℕ∞) ≤ ⊤ from le_top)))
        (fun x hx =>
          annularRSProfile_support
            QuarticWindowWitnesses.v9506 n x hx)
        g hg
  · exact
      tendsto_frozenCubicRSMain_annular
        QuarticWindowWitnesses.v9506
        QuarticWindowWitnesses.v9506_contDiff
        (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)
        g

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


/-- Four complex coordinates carrying the positive-degree RS statistics on
one common profile and height. -/
abbrev PositiveDegreeRSBundle :=
  ℂ × (ℂ × (ℂ × ℂ))

/-- The four normalized positive-degree zero statistics, bundled before
taking the slow diagonal. -/
def normalizedPositiveDegreeRSBundle
    {Z : ZeroConfig} (r : ℝ → ℝ)
    (g1 : Fin 1 → ℝ → ℂ) (g2 : Fin 2 → ℝ → ℂ)
    (g3 : Fin 3 → ℝ → ℂ) (g4 : Fin 4 → ℝ → ℂ)
    (T : ℝ) : PositiveDegreeRSBundle :=
  (RSBlockMomentBridge.normalizedFrozenLinearRSStatistic
      (Z := Z) (4999 / 10000 : ℝ) r g1 T,
    (RSBlockMomentBridge.normalizedFrozenQuadraticRSStatistic
        (Z := Z) r g2 T,
      (RSBlockMomentBridge.normalizedFrozenCubicRSStatistic
          (Z := Z) r g3 T,
        RSBlockMomentBridge.normalizedFrozenQuarticRSStatistic
          (Z := Z) r g4 T)))

/-- The fixed-profile RS main terms before annular-shell evaluation. -/
def frozenPositiveDegreeRSMainBundle
    (r : ℝ → ℝ)
    (g1 : Fin 1 → ℝ → ℂ) (g2 : Fin 2 → ℝ → ℂ)
    (g3 : Fin 3 → ℝ → ℂ) (g4 : Fin 4 → ℝ → ℂ) :
    PositiveDegreeRSBundle :=
  (RSBlockMomentBridge.frozenLinearRSMain
      (4999 / 10000 : ℝ) r g1,
    (RSBlockMomentBridge.frozenQuadraticRSMain r g2,
      (RSBlockMomentBridge.frozenCubicRSMain r g3,
        RSBlockMomentBridge.frozenQuarticRSMain r g4)))

/-- The four literal frozen-profile positive-degree main terms. -/
def evaluatedPositiveDegreeRSMainBundle
    (r : ℝ → ℝ)
    (g1 : Fin 1 → ℝ → ℂ) (g2 : Fin 2 → ℝ → ℂ)
    (g3 : Fin 3 → ℝ → ℂ) (g4 : Fin 4 → ℝ → ℂ) :
    PositiveDegreeRSBundle :=
  (evaluatedLinearRSMain (4999 / 10000 : ℝ) r g1,
    (evaluatedQuadraticRSMain r g2,
      (evaluatedCubicRSMain r g3,
        RSBlockMomentBridge.frozenQuarticRSMain r g4)))

/-- One slow R-9506 schedule simultaneously carries all four positive
degrees.  This is stronger than four unrelated diagonal extractions and is
the form needed by one actual matrix block. -/
theorem RS1996ZetaInputs.exists_tendsto_v9506_annularPositiveDegreeBundle
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (g1 : Fin 1 → ℝ → ℂ) (g2 : Fin 2 → ℝ → ℂ)
    (g3 : Fin 3 → ℝ → ℂ) (g4 : Fin 4 → ℝ → ℂ)
    (hg1 : ∀ j, ContDiff ℝ ∞ (g1 j) ∧ HasCompactSupport (g1 j))
    (hg2 : ∀ j, ContDiff ℝ ∞ (g2 j) ∧ HasCompactSupport (g2 j))
    (hg3 : ∀ j, ContDiff ℝ ∞ (g3 j) ∧ HasCompactSupport (g3 j))
    (hg4 : ∀ j, ContDiff ℝ ∞ (g4 j) ∧ HasCompactSupport (g4 j)) :
    ∃ stage : ℝ → ℕ,
      Tendsto stage atTop atTop ∧
      Tendsto
        (fun T =>
          normalizedPositiveDegreeRSBundle
            (Z := Z)
            (annularRSProfile QuarticWindowWitnesses.v9506 (stage T))
            g1 g2 g3 g4 T)
        atTop
        (nhds
          (evaluatedPositiveDegreeRSMainBundle
            (frozenRSProfile QuarticWindowWitnesses.v9506)
            g1 g2 g3 g4)) := by
  apply RSBlockMomentBridge.exists_tendsto_slow_diagonal
    (fun n T =>
      normalizedPositiveDegreeRSBundle
        (Z := Z)
        (annularRSProfile QuarticWindowWitnesses.v9506 n)
        g1 g2 g3 g4 T)
    (fun n =>
      frozenPositiveDegreeRSMainBundle
        (annularRSProfile QuarticWindowWitnesses.v9506 n)
        g1 g2 g3 g4)
    (evaluatedPositiveDegreeRSMainBundle
      (frozenRSProfile QuarticWindowWitnesses.v9506)
      g1 g2 g3 g4)
  · intro n
    have hcompact :
        HasCompactSupport
          (annularRSProfile QuarticWindowWitnesses.v9506 n) :=
      annularRSProfile_hasCompactSupport
        QuarticWindowWitnesses.v9506 n
    have hsmooth :
        ContDiff ℝ 1
          (annularRSProfile QuarticWindowWitnesses.v9506 n) :=
      (annularRSProfile_contDiff
        QuarticWindowWitnesses.v9506 n
        QuarticWindowWitnesses.v9506_contDiff
        (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)).of_le
          (WithTop.coe_le_coe.2
            (show (1 : ℕ∞) ≤ ⊤ from le_top))
    have hsupport :
        ∀ x,
          annularRSProfile QuarticWindowWitnesses.v9506 n x ≠ 0 →
            (0 : ℝ) ≤ x ∧ x ≤ 1 :=
      fun x hx =>
        annularRSProfile_support
          QuarticWindowWitnesses.v9506 n x hx
    have h1 :=
      RSBlockMomentBridge.RS1996ZetaInputs.tendsto_normalizedFrozenLinearRSStatistic
        hrs (4999 / 10000 : ℝ)
        (annularRSProfile QuarticWindowWitnesses.v9506 n)
        hcompact hsmooth g1 hg1
    have h2 :=
      RSBlockMomentBridge.RS1996ZetaInputs.tendsto_normalizedFrozenQuadraticRSStatistic
        hrs (annularRSProfile QuarticWindowWitnesses.v9506 n)
        hcompact hsmooth hsupport g2 hg2
    have h3 :=
      RSBlockMomentBridge.RS1996ZetaInputs.tendsto_normalizedFrozenCubicRSStatistic
        hrs (annularRSProfile QuarticWindowWitnesses.v9506 n)
        hcompact hsmooth hsupport g3 hg3
    have h4 :=
      RSBlockMomentBridge.RS1996ZetaInputs.tendsto_normalizedFrozenQuarticRSStatistic
        hrs (annularRSProfile QuarticWindowWitnesses.v9506 n)
        hcompact hsmooth hsupport g4 hg4
    simpa only [normalizedPositiveDegreeRSBundle,
      frozenPositiveDegreeRSMainBundle] using
      h1.prodMk_nhds (h2.prodMk_nhds (h3.prodMk_nhds h4))
  · have h1 :=
      tendsto_frozenLinearRSMain_annular
        (4999 / 10000 : ℝ) (by norm_num)
        QuarticWindowWitnesses.v9506
        QuarticWindowWitnesses.v9506_contDiff
        (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)
        g1
    have h2 :=
      tendsto_frozenQuadraticRSMain_annular
        QuarticWindowWitnesses.v9506
        QuarticWindowWitnesses.v9506_contDiff
        (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)
        g2
    have h3 :=
      tendsto_frozenCubicRSMain_annular
        QuarticWindowWitnesses.v9506
        QuarticWindowWitnesses.v9506_contDiff
        (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)
        g3
    have h4 :=
      tendsto_frozenQuarticRSMain_annular
        QuarticWindowWitnesses.v9506
        QuarticWindowWitnesses.v9506_contDiff
        (fun _ hx => QuarticWindowWitnesses.v9506_pos hx)
        g4
    simpa only [frozenPositiveDegreeRSMainBundle,
      evaluatedPositiveDegreeRSMainBundle] using
      h1.prodMk_nhds (h2.prodMk_nhds (h3.prodMk_nhds h4))

end RH.Zeta85.RSMainTermConvergence

end
