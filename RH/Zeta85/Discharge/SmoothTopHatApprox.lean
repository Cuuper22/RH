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
  fun_prop

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
    simpa [TopHatMoments.topHatSupport, Set.mem_Icc] using (abs_le.mp hx)
  simp [shiftedTopHat, TopHatMoments.topHat, hmem]

theorem shiftedTopHat_eq_zero
    (p x : ℝ) (hx : p / 2 < |x - 1 / 2|) :
    shiftedTopHat p x = 0 := by
  have hnot : x - 1 / 2 ∉ TopHatMoments.topHatSupport p := by
    intro hmem
    have hle : |x - 1 / 2| ≤ p / 2 := by
      exact abs_le.mpr (by
        simpa [TopHatMoments.topHatSupport, Set.mem_Icc] using hmem)
    linarith
  simp [shiftedTopHat, TopHatMoments.topHat, hnot]

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
  exact hrs.frozenQuartic_evaluated
    (topHatApproxProfile p n hp hp1)
    (topHatApproxProfile_hasCompactSupport p n hp hp1)
    (topHatApproxProfile_contDiff p n hp hp1).of_le (by norm_num)
    (topHatApproxProfile_support p n hp hp1) g hg


/-! ## Quantitative sharp-profile convergence -/


theorem shiftedTopHat_measurable (p : ℝ) :
    Measurable (shiftedTopHat p) := by
  unfold shiftedTopHat TopHatMoments.topHat
  exact
    (measurable_const.indicator measurableSet_Icc).comp
      (measurable_id.sub measurable_const)

theorem shiftedTopHat_bounds
    (p : ℝ) (hp : 0 < p) (x : ℝ) :
    0 ≤ shiftedTopHat p x ∧ shiftedTopHat p x ≤ 1 / p := by
  unfold shiftedTopHat TopHatMoments.topHat
  by_cases hx :
      x - 1 / 2 ∈ TopHatMoments.topHatSupport p
  · simp [hx, one_div_nonneg.mpr hp.le]
  · simp [hx, one_div_nonneg.mpr hp.le]

theorem shiftedTopHat_support
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (x : ℝ) (hx : shiftedTopHat p x ≠ 0) :
    (0 : ℝ) ≤ x ∧ x ≤ 1 := by
  have hmem :
      x - 1 / 2 ∈ TopHatMoments.topHatSupport p := by
    by_contra hnot
    apply hx
    simp [shiftedTopHat, TopHatMoments.topHat, hnot]
  rw [TopHatMoments.topHatSupport, Set.mem_Icc] at hmem
  constructor <;> linarith

/-- The smooth profiles converge to the sharp profile in L1.  This is the
quantitative topology needed to pass each compact quartic contraction to the
sharp formula while keeping every RS test smooth. -/
theorem topHatApproxProfile_tendsto_L1
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto
      (fun n : ℕ =>
        ∫ x : ℝ,
          |topHatApproxProfile p n hp hp1 x - shiftedTopHat p x|)
      atTop (nhds 0) := by
  let bound : ℝ -> ℝ :=
    (Set.Icc (0 : ℝ) 1).indicator (fun _ => 1 / p)
  have hbound : Integrable bound := by
    apply
      (MeasureTheory.integrableOn_const
        (s := Set.Icc (0 : ℝ) 1)
        (by simp [Real.volume_Icc])).integrable_indicator
    exact measurableSet_Icc
  apply tendsto_integral_of_dominated_convergence bound
  · intro n
    exact
      (((topHatApproxProfile_contDiff p n hp hp1).continuous.measurable.sub
        (shiftedTopHat_measurable p)).abs).aestronglyMeasurable
  · exact hbound
  · intro n
    filter_upwards [] with x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      obtain ⟨hr0, hr1⟩ :=
        topHatApproxProfile_bounds p n hp hp1 x
      obtain ⟨hs0, hs1⟩ := shiftedTopHat_bounds p hp x
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    · rw [Set.indicator_of_not_mem hx]
      have hr : topHatApproxProfile p n hp hp1 x = 0 := by
        by_contra hrne
        exact hx (topHatApproxProfile_support p n hp hp1 x hrne)
      have hs : shiftedTopHat p x = 0 := by
        by_contra hsne
        exact hx (shiftedTopHat_support p hp hp1 x hsne)
      simp [hr, hs]
  · filter_upwards [] with x
    have h :=
      (topHatApproxProfile_tendsto p hp hp1 x).sub tendsto_const_nhds
    simpa only [sub_self, abs_zero, Real.norm_eq_abs] using h.abs


private theorem abs_finset_prod_sub_prod_le
    {ι : Type*} (s : Finset ι) (f g : ι -> ℝ) (M : ℝ)
    (hM : 1 ≤ M)
    (hf : ∀ i ∈ s, |f i| ≤ M)
    (hg : ∀ i ∈ s, |g i| ≤ M) :
    |(∏ i in s, f i) - ∏ i in s, g i| ≤
      M ^ s.card * ∑ i in s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hM0 : 0 ≤ M := le_trans (by norm_num) hM
      have hga : |g a| ≤ M := hg a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, |f i| ≤ M := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hgs : ∀ i ∈ s, |g i| ≤ M := by
        intro i hi
        exact hg i (Finset.mem_insert_of_mem hi)
      have hprod :
          |∏ i in s, f i| ≤ M ^ s.card := by
        calc
          |∏ i in s, f i| = ∏ i in s, |f i| := by
            simp only [abs_prod]
          _ ≤ ∏ _i in s, M := by
            exact Finset.prod_le_prod
              (fun i _hi => abs_nonneg (f i)) hfs
          _ = M ^ s.card := by simp
      have hdiff :
          |(∏ i in s, f i) - ∏ i in s, g i| ≤
            M ^ s.card * ∑ i in s, |f i - g i| :=
        ih hfs hgs
      have hpow : M ^ s.card ≤ M ^ s.card * M := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hM (pow_nonneg hM0 s.card)
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      calc
        |f a * (∏ i in s, f i) - g a * ∏ i in s, g i| =
            |(f a - g a) * (∏ i in s, f i) +
              g a * ((∏ i in s, f i) - ∏ i in s, g i)| := by
                congr 1
                ring
        _ ≤ |f a - g a| * |∏ i in s, f i| +
              |g a| * |(∏ i in s, f i) - ∏ i in s, g i| := by
                simpa only [abs_mul] using
                  abs_add_le
                    ((f a - g a) * (∏ i in s, f i))
                    (g a * ((∏ i in s, f i) - ∏ i in s, g i))
        _ ≤ |f a - g a| * M ^ s.card +
              M * (M ^ s.card * ∑ i in s, |f i - g i|) := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left hprod
                    (abs_nonneg (f a - g a))
                · exact mul_le_mul hga hdiff
                    (abs_nonneg _) hM0
        _ ≤ |f a - g a| * (M ^ s.card * M) +
              (M ^ s.card * M) * ∑ i in s, |f i - g i| := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left hpow
                    (abs_nonneg (f a - g a))
                · ring_nf
        _ = M ^ (s.card + 1) *
              (|f a - g a| + ∑ i in s, |f i - g i|) := by
                rw [pow_succ]
                ring

/-- A degree-independent telescoping bound for translated smooth products.
The constant is uniform in every translation vector, which is the key input
for passing the cyclic contractions to the sharp top hat after the T-limit. -/
theorem topHatApprox_product_error_bound
    {k : ℕ} (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1)
    (shift : Fin k -> ℝ) (x : ℝ) :
    |(∏ a : Fin k,
        topHatApproxProfile p n hp hp1 (x + shift a)) -
      ∏ a : Fin k, shiftedTopHat p (x + shift a)| ≤
      (1 / p) ^ k *
        ∑ a : Fin k,
          |topHatApproxProfile p n hp hp1 (x + shift a) -
            shiftedTopHat p (x + shift a)| := by
  have hM : (1 : ℝ) ≤ 1 / p := by
    rw [le_div_iff₀ hp]
    linarith
  have hbound := abs_finset_prod_sub_prod_le
    (Finset.univ : Finset (Fin k))
    (fun a => topHatApproxProfile p n hp hp1 (x + shift a))
    (fun a => shiftedTopHat p (x + shift a)) (1 / p) hM
    (by
      intro a _ha
      rw [abs_of_nonneg
        (topHatApproxProfile_bounds p n hp hp1 (x + shift a)).1]
      exact (topHatApproxProfile_bounds p n hp hp1 (x + shift a)).2)
    (by
      intro a _ha
      rw [abs_of_nonneg (shiftedTopHat_bounds p hp (x + shift a)).1]
      exact (shiftedTopHat_bounds p hp (x + shift a)).2)
  simpa using hbound


/-- At every fixed frequency vector, the legal smooth cyclic symbols converge
to the sharp translated top-hat symbol.  The integral is dominated on the
single fixed interval [0,1] by the factor at cyclic position zero. -/
theorem weightedCyclicSymbol_topHatApprox_tendsto
    {k : ℕ} [NeZero k] (mu p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (xi : Fin k -> ℝ) :
    Tendsto
      (fun n : ℕ =>
        weightedCyclicSymbol (k := k) mu
          (topHatApproxProfile p n hp hp1) xi)
      atTop
      (nhds (weightedCyclicSymbol (k := k) mu (shiftedTopHat p) xi)) := by
  let bound : ℝ -> ℝ :=
    (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 / p) ^ k)
  have hbound : Integrable bound := by
    apply
      (MeasureTheory.integrableOn_const
        (s := Set.Icc (0 : ℝ) 1)
        (by simp [Real.volume_Icc])).integrable_indicator
    exact measurableSet_Icc
  have hint :
      Tendsto
        (fun n : ℕ =>
          ∫ x : ℝ, ∏ j : Fin k,
            topHatApproxProfile p n hp hp1
              (x + cyclicPartialSum xi j / mu))
        atTop
        (nhds
          (∫ x : ℝ, ∏ j : Fin k,
            shiftedTopHat p (x + cyclicPartialSum xi j / mu))) := by
    apply tendsto_integral_of_dominated_convergence bound
    · intro n
      exact
        (by
          fun_prop :
          Continuous (fun x : ℝ =>
            ∏ j : Fin k,
              topHatApproxProfile p n hp hp1
                (x + cyclicPartialSum xi j / mu))).measurable.aestronglyMeasurable
    · exact hbound
    · intro n
      filter_upwards [] with x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_prod]
        calc
          (∏ j : Fin k,
              |topHatApproxProfile p n hp hp1
                (x + cyclicPartialSum xi j / mu)|) ≤
              ∏ _j : Fin k, (1 / p) := by
                apply Finset.prod_le_prod
                · intro j _hj
                  exact abs_nonneg _
                · intro j _hj
                  rw [abs_of_nonneg
                    (topHatApproxProfile_bounds p n hp hp1
                      (x + cyclicPartialSum xi j / mu)).1]
                  exact (topHatApproxProfile_bounds p n hp hp1
                    (x + cyclicPartialSum xi j / mu)).2
          _ = (1 / p) ^ k := by simp
      · rw [Set.indicator_of_not_mem hx]
        have hz : topHatApproxProfile p n hp hp1 x = 0 := by
          by_contra hne
          exact hx (topHatApproxProfile_support p n hp hp1 x hne)
        have hprod :
            (∏ j : Fin k,
              topHatApproxProfile p n hp hp1
                (x + cyclicPartialSum xi j / mu)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin k))
          simpa [cyclicPartialSum] using hz
        simp [hprod]
    · filter_upwards [] with x
      apply tendsto_finset_prod
      intro j _hj
      exact topHatApproxProfile_tendsto p hp hp1
        (x + cyclicPartialSum xi j / mu)
  have hreal :
      Tendsto
        (fun n : ℕ =>
          mu * ∫ x : ℝ, ∏ j : Fin k,
            topHatApproxProfile p n hp hp1
              (x + cyclicPartialSum xi j / mu))
        atTop
        (nhds
          (mu * ∫ x : ℝ, ∏ j : Fin k,
            shiftedTopHat p (x + cyclicPartialSum xi j / mu))) :=
    tendsto_const_nhds.mul hint
  have hcomplex :=
    Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hreal
  simpa only [weightedCyclicSymbol] using hcomplex


/-- Every smooth approximant supplies the evaluated one-point contraction. -/
theorem RS1996ZetaInputs.topHatApproxLinear_evaluated
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1)
    (g : Fin 1 -> ℝ -> ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T ≥ T0,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := 1) (4999 / 10000 : ℝ)
          (topHatApproxProfile p n hp hp1)) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 1) (4999 / 10000 : ℝ)
            (topHatApproxProfile p n hp hp1)) T rho) -
        rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
          (((4999 / 10000 : ℝ) *
            cyclicRSScalarMoment (4999 / 10000 : ℝ)
              (topHatApproxProfile p n hp hp1) 1 : ℝ) : ℂ)‖ ≤ C * T := by
  exact hrs.frozenLinear_evaluated
    (topHatApproxProfile p n hp hp1)
    (topHatApproxProfile_hasCompactSupport p n hp hp1)
    (topHatApproxProfile_contDiff p n hp hp1).of_le (by norm_num)
    g hg

/-- Every smooth approximant supplies the evaluated two-point contraction. -/
theorem RS1996ZetaInputs.topHatApproxQuadratic_evaluated
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1)
    (g : Fin 2 -> ℝ -> ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T ≥ T0,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := 2) (4999 / 10000 : ℝ)
          (topHatApproxProfile p n hp hp1)) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 2) (4999 / 10000 : ℝ)
            (topHatApproxProfile p n hp hp1)) T rho) -
        rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
          (((4999 / 10000 : ℝ) *
            cyclicRSScalarMoment (4999 / 10000 : ℝ)
              (topHatApproxProfile p n hp hp1) 2 : ℝ) : ℂ)‖ ≤ C * T := by
  exact hrs.frozenQuadratic_evaluated
    (topHatApproxProfile p n hp hp1)
    (topHatApproxProfile_hasCompactSupport p n hp hp1)
    (topHatApproxProfile_contDiff p n hp hp1).of_le (by norm_num)
    (topHatApproxProfile_support p n hp hp1) g hg

/-- Every smooth approximant supplies the evaluated three-point contraction. -/
theorem RS1996ZetaInputs.topHatApproxCubic_evaluated
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1)
    (g : Fin 3 -> ℝ -> ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T ≥ T0,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := 3) (4999 / 10000 : ℝ)
          (topHatApproxProfile p n hp hp1)) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 3) (4999 / 10000 : ℝ)
            (topHatApproxProfile p n hp hp1)) T rho) -
        rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
          (((4999 / 10000 : ℝ) *
            cyclicRSScalarMoment (4999 / 10000 : ℝ)
              (topHatApproxProfile p n hp hp1) 3 : ℝ) : ℂ)‖ ≤ C * T := by
  exact hrs.frozenCubic_evaluated
    (topHatApproxProfile p n hp hp1)
    (topHatApproxProfile_hasCompactSupport p n hp hp1)
    (topHatApproxProfile_contDiff p n hp hp1).of_le (by norm_num)
    (topHatApproxProfile_support p n hp hp1) g hg

end RH.Zeta85.SmoothTopHatApprox
