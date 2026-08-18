/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSSharpMainTerm

/-!
# Exact sharp top-hat Rudnick--Sarnak main terms

This module discharges every literal Fubini and integrability premise for
the discontinuous top hat directly from compact rectangular support and
explicit pointwise bounds.  It then evaluates the complete Rudnick--Sarnak
main term through degree four as the frozen uncentered contraction formula.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators Matrix ContDiff Convolution

noncomputable section

namespace RH.Zeta85.RSPairIntegrals

open RSReduction TopHatMoments

private theorem integrable_of_stronglyMeasurable_bounded_support
    {α : Type*} [MeasureSpace α] {f : α → ℝ}
    (hf : StronglyMeasurable f) (s : Set α) (hs : MeasurableSet s)
    (hfinite : volume s < (⊤ : ENNReal)) {M : ℝ} (hM : 0 ≤ M)
    (hzero : ∀ x ∉ s, f x = 0)
    (hbound : ∀ x ∈ s, |f x| ≤ M) : Integrable f := by
  have hconst : Integrable (s.indicator fun _ => M) :=
    (integrableOn_const (s := s) hfinite.ne).integrable_indicator hs
  apply hconst.mono hf.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hM]
    exact hbound x hx
  · rw [hzero x hx, norm_zero, Set.indicator_of_notMem hx, norm_zero]

theorem onePairIntegrand_topHat_powers_integrable
    {mu p : ℝ} (hp : 0 < p) (hmu : mu ≠ 0)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (onePairIntegrand mu
      (fun x => topHat p x ^ a) (fun x => topHat p x ^ b)) := by
  let B : ℝ := max 1 (|mu| * p)
  let M : ℝ := B * |mu| * (1 / p) ^ (a + b)
  let box : Set (ℝ × ℝ) := Set.Icc (-p / 2, -B) (p / 2, B)
  have hB : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hpInv : 0 ≤ 1 / p := one_div_nonneg.mpr hp.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have htopBound (z : ℝ) : |topHat p z| ≤ 1 / p := by
    by_cases hz : z ∈ topHatSupport p
    · simp [topHat, hz, abs_of_pos hp]
    · simp [topHat, hz, hp.le]
  have hmeas : StronglyMeasurable (onePairIntegrand mu
      (fun x => topHat p x ^ a) (fun x => topHat p x ^ b)) := by
    apply Measurable.stronglyMeasurable
    have htop : Measurable (topHat p) :=
      (topHat_stronglyMeasurable p).measurable
    unfold onePairIntegrand
    fun_prop
  apply integrable_of_stronglyMeasurable_bounded_support hmeas box
    (by simp [box]) (measure_Icc_lt_top) hM
  · intro z hz
    by_cases hx : z.1 ∈ topHatSupport p
    · by_cases hy : z.1 + z.2 / mu ∈ topHatSupport p
      · exfalso
        apply hz
        rw [Set.mem_Icc]
        constructor
        · constructor
          · exact hx.1
          · have hxa := hx.1
            have hya := hy.1
            have habs : |z.2 / mu| ≤ p := by
              have hxb := hx.2
              have hyb := hy.2
              rw [abs_le]
              constructor <;> linarith [hxa, hxb, hya, hyb]
            rw [abs_div] at habs
            have hle : |z.2| ≤ |mu| * p := by
              have := (div_le_iff₀ (abs_pos.mpr hmu)).mp habs
              nlinarith [abs_nonneg mu]
            linarith [neg_abs_le z.2,
              le_max_right 1 (|mu| * p)]
        · constructor
          · exact hx.2
          · have hxb := hx.2
            have hyb := hy.2
            have habs : |z.2 / mu| ≤ p := by
              rw [abs_le]
              constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
            rw [abs_div] at habs
            have hle : |z.2| ≤ |mu| * p := by
              have := (div_le_iff₀ (abs_pos.mpr hmu)).mp habs
              nlinarith [abs_nonneg mu]
            exact (le_abs_self z.2).trans
              (hle.trans (le_max_right 1 (|mu| * p)))
      · simp [onePairIntegrand, topHat, Set.indicator_of_notMem hy, hb]
    · simp [onePairIntegrand, topHat, Set.indicator_of_notMem hx, ha]
  · intro z hz
    rw [Set.mem_Icc] at hz
    have hz2 : |z.2| ≤ B := abs_le.mpr ⟨hz.1.2, hz.2.2⟩
    simp only [onePairIntegrand, abs_mul, abs_abs, abs_pow]
    calc
      |z.2| * (|mu| *
          (|topHat p z.1| ^ a * |topHat p (z.1 + z.2 / mu)| ^ b)) ≤
          B * (|mu| * ((1 / p) ^ a * (1 / p) ^ b)) := by
        gcongr
        · exact htopBound _
        · exact htopBound _
      _ = M := by dsimp [M]; rw [← pow_add]; ring

theorem distanceKernel_topHat_powers_integrable
    {p : ℝ} (hp : 0 < p)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (distanceKernel
      (fun x => topHat p x ^ a) (fun x => topHat p x ^ b)) := by
  let M : ℝ := p * (1 / p) ^ (a + b)
  let box : Set (ℝ × ℝ) := Set.Icc (-p / 2, -p / 2) (p / 2, p / 2)
  have hpInv : 0 ≤ 1 / p := one_div_nonneg.mpr hp.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have htopBound (z : ℝ) : |topHat p z| ≤ 1 / p := by
    by_cases hz : z ∈ topHatSupport p
    · simp [topHat, hz, abs_of_pos hp]
    · simp [topHat, hz, hp.le]
  have hmeas : StronglyMeasurable (distanceKernel
      (fun x => topHat p x ^ a) (fun x => topHat p x ^ b)) := by
    apply Measurable.stronglyMeasurable
    have htop : Measurable (topHat p) :=
      (topHat_stronglyMeasurable p).measurable
    unfold distanceKernel
    fun_prop
  apply integrable_of_stronglyMeasurable_bounded_support hmeas box
    (by simp [box]) measure_Icc_lt_top hM
  · intro z hz
    by_cases hx : z.1 ∈ topHatSupport p
    · by_cases hy : z.2 ∈ topHatSupport p
      · exfalso
        apply hz
        exact ⟨⟨hx.1, hy.1⟩, ⟨hx.2, hy.2⟩⟩
      · simp [distanceKernel, topHat, Set.indicator_of_notMem hy, hb]
    · simp [distanceKernel, topHat, Set.indicator_of_notMem hx, ha]
  · intro z hz
    have hdist : |z.2 - z.1| ≤ p := by
      rw [Set.mem_Icc] at hz
      rw [abs_le]
      constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    simp only [distanceKernel, abs_mul, abs_abs, abs_pow]
    calc
      |z.2 - z.1| * |topHat p z.1| ^ a * |topHat p z.2| ^ b ≤
          p * (1 / p) ^ a * (1 / p) ^ b := by
        gcongr
        · exact htopBound _
        · exact htopBound _
      _ = M := by dsimp [M]; rw [pow_add]; ring

theorem separatedTwoPairFubiniKernel_topHat_integrable
    {mu p : ℝ} (hp : 0 < p) (hmu : mu ≠ 0) :
    Integrable (separatedTwoPairFubiniKernel mu (topHat p)) := by
  let B : ℝ := max 1 (|mu| * p)
  let M : ℝ := B ^ 2 * |mu| * (1 / p) ^ 4
  let box : Set ((ℝ × ℝ) × ℝ) :=
    Set.Icc ((-B, -B), -p / 2) ((B, B), p / 2)
  have hB : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have htopBound (z : ℝ) : |topHat p z| ≤ 1 / p := by
    by_cases hz : z ∈ topHatSupport p
    · simp [topHat, hz, abs_of_pos hp]
    · simp [topHat, hz, hp.le]
  have hmeas : StronglyMeasurable
      (separatedTwoPairFubiniKernel mu (topHat p)) := by
    apply Measurable.stronglyMeasurable
    have htop : Measurable (topHat p) :=
      (topHat_stronglyMeasurable p).measurable
    unfold separatedTwoPairFubiniKernel
    fun_prop
  apply integrable_of_stronglyMeasurable_bounded_support hmeas box
    (by simp [box]) measure_Icc_lt_top hM
  · intro z hz
    by_cases hx : z.2 ∈ topHatSupport p
    · by_cases hy : z.2 + z.1.1 / mu ∈ topHatSupport p
      · by_cases hw : z.2 + z.1.2 / mu ∈ topHatSupport p
        · exfalso
          apply hz
          rw [Set.mem_Icc]
          constructor
          · constructor
            · constructor
              · have habs : |z.1.1 / mu| ≤ p := by
                  rw [abs_le]
                  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
                rw [abs_div] at habs
                have hle : |z.1.1| ≤ |mu| * p := by
                  have := (div_le_iff₀ (abs_pos.mpr hmu)).mp habs
                  nlinarith [abs_nonneg mu]
                linarith [neg_abs_le z.1.1,
                  le_max_right 1 (|mu| * p)]
              · have habs : |z.1.2 / mu| ≤ p := by
                  rw [abs_le]
                  constructor <;> linarith [hx.1, hx.2, hw.1, hw.2]
                rw [abs_div] at habs
                have hle : |z.1.2| ≤ |mu| * p := by
                  have := (div_le_iff₀ (abs_pos.mpr hmu)).mp habs
                  nlinarith [abs_nonneg mu]
                linarith [neg_abs_le z.1.2,
                  le_max_right 1 (|mu| * p)]
            · exact hx.1
          · constructor
            · constructor
              · have habs : |z.1.1 / mu| ≤ p := by
                  rw [abs_le]
                  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
                rw [abs_div] at habs
                have hle : |z.1.1| ≤ |mu| * p := by
                  have := (div_le_iff₀ (abs_pos.mpr hmu)).mp habs
                  nlinarith [abs_nonneg mu]
                exact (le_abs_self z.1.1).trans
                  (hle.trans (le_max_right 1 (|mu| * p)))
              · have habs : |z.1.2 / mu| ≤ p := by
                  rw [abs_le]
                  constructor <;> linarith [hx.1, hx.2, hw.1, hw.2]
                rw [abs_div] at habs
                have hle : |z.1.2| ≤ |mu| * p := by
                  have := (div_le_iff₀ (abs_pos.mpr hmu)).mp habs
                  nlinarith [abs_nonneg mu]
                exact (le_abs_self z.1.2).trans
                  (hle.trans (le_max_right 1 (|mu| * p)))
            · exact hx.2
        · simp [separatedTwoPairFubiniKernel, topHat,
            Set.indicator_of_notMem hw]
      · simp [separatedTwoPairFubiniKernel, topHat,
          Set.indicator_of_notMem hy]
    · simp [separatedTwoPairFubiniKernel, topHat,
        Set.indicator_of_notMem hx]
  · intro z hz
    rw [Set.mem_Icc] at hz
    have hu : |z.1.1| ≤ B := abs_le.mpr ⟨hz.1.1.1, hz.2.1.1⟩
    have hv : |z.1.2| ≤ B := abs_le.mpr ⟨hz.1.1.2, hz.2.1.2⟩
    simp only [separatedTwoPairFubiniKernel, abs_mul, abs_abs, abs_pow]
    calc
      |z.1.1| * |z.1.2| *
          (|mu| * (|topHat p z.2| ^ 2 *
            |topHat p (z.2 + z.1.1 / mu)| *
            |topHat p (z.2 + z.1.2 / mu)|)) ≤
          B * B * (|mu| * ((1 / p) ^ 2 * (1 / p) * (1 / p))) := by
        gcongr
        · exact htopBound _
        · exact htopBound _
        · exact htopBound _
      _ = M := by dsimp [M]; ring

theorem nestedTwoPairFubiniKernel_topHat_integrable
    {mu p : ℝ} (hp : 0 < p) (hmu : mu ≠ 0) :
    Integrable (nestedTwoPairFubiniKernel mu (topHat p)) := by
  let B : ℝ := max 1 (2 * |mu| * p)
  let M : ℝ := B ^ 2 * |mu| * (1 / p) ^ 4
  let box : Set ((ℝ × ℝ) × ℝ) :=
    Set.Icc ((-B, -B), -p / 2) ((B, B), p / 2)
  have hB : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have htopBound (z : ℝ) : |topHat p z| ≤ 1 / p := by
    by_cases hz : z ∈ topHatSupport p
    · simp [topHat, hz, abs_of_pos hp]
    · simp [topHat, hz, hp.le]
  have hmeas : StronglyMeasurable
      (nestedTwoPairFubiniKernel mu (topHat p)) := by
    apply Measurable.stronglyMeasurable
    have htop : Measurable (topHat p) :=
      (topHat_stronglyMeasurable p).measurable
    unfold nestedTwoPairFubiniKernel
    fun_prop
  apply integrable_of_stronglyMeasurable_bounded_support hmeas box
    (by simp [box]) measure_Icc_lt_top hM
  · intro z hz
    by_cases hx : z.2 ∈ topHatSupport p
    · by_cases hy : z.2 + z.1.1 / mu ∈ topHatSupport p
      · by_cases hw : z.2 + (z.1.1 + z.1.2) / mu ∈ topHatSupport p
        · exfalso
          apply hz
          rw [Set.mem_Icc]
          have huDiv : |z.1.1 / mu| ≤ p := by
            rw [abs_le]
            constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
          have huvDiv : |(z.1.1 + z.1.2) / mu| ≤ p := by
            rw [abs_le]
            constructor <;> linarith [hx.1, hx.2, hw.1, hw.2]
          rw [abs_div] at huDiv huvDiv
          have hu : |z.1.1| ≤ |mu| * p := by
            have := (div_le_iff₀ (abs_pos.mpr hmu)).mp huDiv
            nlinarith [abs_nonneg mu]
          have huv : |z.1.1 + z.1.2| ≤ |mu| * p := by
            have := (div_le_iff₀ (abs_pos.mpr hmu)).mp huvDiv
            nlinarith [abs_nonneg mu]
          have hv : |z.1.2| ≤ 2 * |mu| * p := by
            calc
              |z.1.2| = |(z.1.1 + z.1.2) - z.1.1| := by ring_nf
              _ ≤ |z.1.1 + z.1.2| + |z.1.1| := abs_sub _ _
              _ ≤ |mu| * p + |mu| * p := add_le_add huv hu
              _ = 2 * |mu| * p := by ring
          constructor
          · constructor
            · constructor
              · linarith [neg_abs_le z.1.1,
                  le_max_right 1 (2 * |mu| * p)]
              · linarith [neg_abs_le z.1.2,
                  le_max_right 1 (2 * |mu| * p)]
            · exact hx.1
          · constructor
            · constructor
              · exact (le_abs_self z.1.1).trans
                  (hu.trans (by
                    calc
                      |mu| * p ≤ 2 * |mu| * p := by
                        nlinarith [abs_nonneg mu]
                      _ ≤ B := le_max_right _ _))
              · exact (le_abs_self z.1.2).trans
                  (hv.trans (le_max_right _ _))
            · exact hx.2
        · simp [nestedTwoPairFubiniKernel, topHat,
            Set.indicator_of_notMem hw]
      · simp [nestedTwoPairFubiniKernel, topHat,
          Set.indicator_of_notMem hy]
    · simp [nestedTwoPairFubiniKernel, topHat,
        Set.indicator_of_notMem hx]
  · intro z hz
    rw [Set.mem_Icc] at hz
    have hu : |z.1.1| ≤ B := abs_le.mpr ⟨hz.1.1.1, hz.2.1.1⟩
    have hv : |z.1.2| ≤ B := abs_le.mpr ⟨hz.1.1.2, hz.2.1.2⟩
    simp only [nestedTwoPairFubiniKernel, abs_mul, abs_abs, abs_pow]
    calc
      |z.1.1| * |z.1.2| *
          (|mu| * (|topHat p z.2| *
            |topHat p (z.2 + z.1.1 / mu)| ^ 2 *
            |topHat p (z.2 + (z.1.1 + z.1.2) / mu)|)) ≤
          B * B * (|mu| * ((1 / p) * (1 / p) ^ 2 * (1 / p))) := by
        gcongr
        · exact htopBound _
        · exact htopBound _
        · exact htopBound _
      _ = M := by dsimp [M]; ring

theorem crossingRawKernel_topHat_integrable
    {mu p : ℝ} (hp : 0 < p) (hmu : mu ≠ 0) :
    Integrable (crossingRawKernel mu (topHat p)) := by
  let B : ℝ := max 1 (|mu| * p)
  let M : ℝ := B ^ 2 * |mu| * (1 / p) ^ 4
  let box : Set ((ℝ × ℝ) × ℝ) :=
    Set.Icc ((-B, -B), -p / 2) ((B, B), p / 2)
  have hB : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have htopBound (z : ℝ) : |topHat p z| ≤ 1 / p := by
    by_cases hz : z ∈ topHatSupport p
    · simp [topHat, hz, abs_of_pos hp]
    · simp [topHat, hz, hp.le]
  have hmeas : StronglyMeasurable
      (crossingRawKernel mu (topHat p)) := by
    apply Measurable.stronglyMeasurable
    have htop : Measurable (topHat p) :=
      (topHat_stronglyMeasurable p).measurable
    unfold crossingRawKernel
    fun_prop
  apply integrable_of_stronglyMeasurable_bounded_support hmeas box
    (by simp [box]) measure_Icc_lt_top hM
  · intro z hz
    by_cases hx : z.2 ∈ topHatSupport p
    · by_cases hy : z.2 + z.1.1 / mu ∈ topHatSupport p
      · by_cases hw : z.2 + z.1.2 / mu ∈ topHatSupport p
        · exfalso
          apply hz
          rw [Set.mem_Icc]
          have huDiv : |z.1.1 / mu| ≤ p := by
            rw [abs_le]
            constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
          have hvDiv : |z.1.2 / mu| ≤ p := by
            rw [abs_le]
            constructor <;> linarith [hx.1, hx.2, hw.1, hw.2]
          rw [abs_div] at huDiv hvDiv
          have hu : |z.1.1| ≤ |mu| * p := by
            have := (div_le_iff₀ (abs_pos.mpr hmu)).mp huDiv
            nlinarith [abs_nonneg mu]
          have hv : |z.1.2| ≤ |mu| * p := by
            have := (div_le_iff₀ (abs_pos.mpr hmu)).mp hvDiv
            nlinarith [abs_nonneg mu]
          constructor
          · constructor
            · constructor
              · linarith [neg_abs_le z.1.1,
                  le_max_right 1 (|mu| * p)]
              · linarith [neg_abs_le z.1.2,
                  le_max_right 1 (|mu| * p)]
            · exact hx.1
          · constructor
            · constructor
              · exact (le_abs_self z.1.1).trans
                  (hu.trans (le_max_right _ _))
              · exact (le_abs_self z.1.2).trans
                  (hv.trans (le_max_right _ _))
            · exact hx.2
        · simp [crossingRawKernel, topHat,
            Set.indicator_of_notMem hw]
      · simp [crossingRawKernel, topHat,
          Set.indicator_of_notMem hy]
    · simp [crossingRawKernel, topHat,
        Set.indicator_of_notMem hx]
  · intro z hz
    rw [Set.mem_Icc] at hz
    have hu : |z.1.1| ≤ B := abs_le.mpr ⟨hz.1.1.1, hz.2.1.1⟩
    have hv : |z.1.2| ≤ B := abs_le.mpr ⟨hz.1.1.2, hz.2.1.2⟩
    simp only [crossingRawKernel, abs_mul, abs_abs]
    calc
      |z.1.1| * |z.1.2| *
          (|mu| * (|topHat p z.2| *
            |topHat p (z.2 + z.1.1 / mu)| *
            |topHat p (z.2 + (z.1.1 + z.1.2) / mu)| *
            |topHat p (z.2 + z.1.2 / mu)|)) ≤
          B * B * (|mu| * ((1 / p) * (1 / p) *
            (1 / p) * (1 / p))) := by
        gcongr
        · exact htopBound _
        · exact htopBound _
        · exact htopBound _
        · exact htopBound _
      _ = M := by dsimp [M]; ring

theorem nestedAuxProfile_topHat_eq {p : ℝ} (hp : 0 < p) (y : ℝ) :
    nestedAuxProfile (topHat p) y =
      topHat p y ^ 2 * (y ^ 2 / p + p / 4) := by
  unfold nestedAuxProfile
  rw [pairDistancePotential_topHat hp]
  by_cases hy : y ∈ topHatSupport p
  · rw [distancePotential_eq hp hy.1 hy.2]
  · simp [topHat, Set.indicator_of_notMem hy]

theorem nestedDistanceKernel_topHat_integrable
    {p : ℝ} (hp : 0 < p) :
    Integrable (distanceKernel (topHat p)
      (nestedAuxProfile (topHat p))) := by
  let A : ℝ := (1 / p) ^ 2 * p
  let M : ℝ := p * (1 / p) * A
  let box : Set (ℝ × ℝ) := Set.Icc (-p / 2, -p / 2) (p / 2, p / 2)
  have hpInv : 0 ≤ 1 / p := one_div_nonneg.mpr hp.le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hM : 0 ≤ M := by dsimp [M, A]; positivity
  have htopBound (z : ℝ) : |topHat p z| ≤ 1 / p := by
    by_cases hz : z ∈ topHatSupport p
    · simp [topHat, hz, abs_of_pos hp]
    · simp [topHat, hz, hp.le]
  have hauxBound (y : ℝ) (hy : y ∈ topHatSupport p) :
      |nestedAuxProfile (topHat p) y| ≤ A := by
    change -p / 2 ≤ y ∧ y ≤ p / 2 at hy
    have hyabs : |y| ≤ p / 2 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    have hysq : y ^ 2 ≤ (p / 2) ^ 2 := by
      simpa only [sq_abs] using
        ((sq_le_sq₀ (abs_nonneg y) (by positivity)).2 hyabs)
    have hpot0 : 0 ≤ y ^ 2 / p + p / 4 := by positivity
    have hpot : y ^ 2 / p + p / 4 ≤ p := by
      have hsquare : y ^ 2 ≤ p ^ 2 / 4 := by nlinarith
      have hdiv : y ^ 2 / p ≤ p / 4 := by
        apply (div_le_iff₀ hp).2
        nlinarith
      linarith
    rw [nestedAuxProfile_topHat_eq hp, abs_mul, abs_pow,
      abs_of_nonneg hpot0]
    calc
      |topHat p y| ^ 2 * (y ^ 2 / p + p / 4) ≤
          (1 / p) ^ 2 * p := by gcongr; exact htopBound _
      _ = A := rfl
  have hmeas : StronglyMeasurable
      (distanceKernel (topHat p) (nestedAuxProfile (topHat p))) := by
    apply Measurable.stronglyMeasurable
    have htop : Measurable (topHat p) :=
      (topHat_stronglyMeasurable p).measurable
    rw [show nestedAuxProfile (topHat p) =
        fun y => topHat p y ^ 2 * (y ^ 2 / p + p / 4) by
      funext y
      exact nestedAuxProfile_topHat_eq hp y]
    unfold distanceKernel
    fun_prop
  apply integrable_of_stronglyMeasurable_bounded_support hmeas box
    (by simp [box]) measure_Icc_lt_top hM
  · intro z hz
    by_cases hx : z.1 ∈ topHatSupport p
    · by_cases hy : z.2 ∈ topHatSupport p
      · exfalso
        apply hz
        exact ⟨⟨hx.1, hy.1⟩, ⟨hx.2, hy.2⟩⟩
      · have haux : nestedAuxProfile (topHat p) z.2 = 0 := by
          rw [nestedAuxProfile_topHat_eq hp]
          simp [topHat, Set.indicator_of_notMem hy]
        simp [distanceKernel, haux]
    · simp [distanceKernel, topHat, Set.indicator_of_notMem hx]
  · intro z hz
    rw [Set.mem_Icc] at hz
    have hxmem : z.1 ∈ topHatSupport p := ⟨hz.1.1, hz.2.1⟩
    have hymem : z.2 ∈ topHatSupport p := ⟨hz.1.2, hz.2.2⟩
    have hdist : |z.2 - z.1| ≤ p := by
      rw [abs_le]
      constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    simp only [distanceKernel, abs_mul, abs_abs]
    calc
      |z.2 - z.1| * |topHat p z.1| *
          |nestedAuxProfile (topHat p) z.2| ≤
          p * (1 / p) * A := by
        gcongr
        · exact htopBound _
        · exact hauxBound _ hymem
      _ = M := rfl

theorem normalizedRSMainTerm_topHat_eq_cyclicUncenteredMoment
    {n : ℕ} (hn : n ≤ 3) {p mu : ℝ} (hp : 0 < p) (hmu : 0 < mu) :
    normalizedRSMainTerm mu
        (weightedCyclicSymbol (k := n + 1) mu (topHat p)) =
      (cyclicUncenteredMoment mu (topHat p) (n + 1) : ℝ) := by
  interval_cases n
  · exact normalizedRSMainTerm_k1 mu (topHat p) hmu
  · apply normalizedRSMainTerm_k2 mu (topHat p) hmu
    simpa only [pow_one] using
      (onePairIntegrand_topHat_powers_integrable hp hmu.ne'
        (a := 1) (b := 1) (by norm_num) (by norm_num))
  · apply normalizedRSMainTerm_k3 mu (topHat p) hmu
    · simpa only [pow_one] using
        (onePairIntegrand_topHat_powers_integrable hp hmu.ne'
          (a := 2) (b := 1) (by norm_num) (by norm_num))
    · simpa only [pow_one] using
        (onePairIntegrand_topHat_powers_integrable hp hmu.ne'
          (a := 1) (b := 2) (by norm_num) (by norm_num))
    · simpa only [pow_one] using
        (distanceKernel_topHat_powers_integrable hp
          (a := 2) (b := 1) (by norm_num) (by norm_num))
  · apply normalizedRSMainTerm_k4 mu (topHat p) hmu
    · simpa only [pow_one] using
        (onePairIntegrand_topHat_powers_integrable hp hmu.ne'
          (a := 3) (b := 1) (by norm_num) (by norm_num))
    · simpa only [pow_one] using
        (onePairIntegrand_topHat_powers_integrable hp hmu.ne'
          (a := 1) (b := 3) (by norm_num) (by norm_num))
    · exact onePairIntegrand_topHat_powers_integrable hp hmu.ne'
        (a := 2) (b := 2) (by norm_num) (by norm_num)
    · simpa only [pow_one] using
        (distanceKernel_topHat_powers_integrable hp
          (a := 3) (b := 1) (by norm_num) (by norm_num))
    · exact separatedTwoPairFubiniKernel_topHat_integrable hp hmu.ne'
    · exact nestedTwoPairFubiniKernel_topHat_integrable hp hmu.ne'
    · exact nestedDistanceKernel_topHat_integrable hp
    · exact crossingRawKernel_topHat_integrable hp hmu.ne'

theorem normalizedRSMainTerm_topHat_eq_uncenteredContractionMoment
    {n : ℕ} (hn : n ≤ 3) {p mu : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hmu : 0 < mu) :
    normalizedRSMainTerm mu
        (weightedCyclicSymbol (k := n + 1) mu (topHat p)) =
      (uncenteredContractionMoment (topHatR3Terms p) mu (n + 1) : ℝ) := by
  rw [normalizedRSMainTerm_topHat_eq_cyclicUncenteredMoment hn hp hmu]
  exact_mod_cast cyclicUncenteredMoment_topHat_eq_uncenteredContractionMoment
    hp hp1 (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (by omega)

theorem rsMainTerm_topHat_eq_uncenteredContractionMoment
    {n : ℕ} (hn : n ≤ 3) {p mu : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hmu : 0 < mu) :
    rsMainTerm (weightedCyclicSymbol (k := n + 1) mu (topHat p)) =
      (mu : ℂ) *
        (uncenteredContractionMoment (topHatR3Terms p) mu (n + 1) : ℝ) := by
  have hnorm := normalizedRSMainTerm_topHat_eq_uncenteredContractionMoment
    hn hp hp1 hmu
  unfold normalizedRSMainTerm at hnorm
  have h := (div_eq_iff (Complex.ofReal_ne_zero.mpr hmu.ne')).mp hnorm
  rw [h]
  ring

end RH.Zeta85.RSPairIntegrals
