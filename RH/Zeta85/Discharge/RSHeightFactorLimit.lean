import RH.Zeta85.Discharge.RSHeightWindowAverage

/-!
# Height-factor convergence for the averaged RS selector

The averaged selector is a convolution of the smooth dyadic window with a
positive probability kernel.  This gives exact conservation of its integral
and, together with pointwise convergence, `L1` convergence by the minimum
identity.  Powers therefore converge in `L1` as well.  These are the shared
height factors appearing in the Rudnick--Sarnak tuple formula through every
degree used by the frozen quartic ladder.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def scaledBaseHeightKernel (R y : ℝ) : ℝ :=
  (R / baseHeightKernelMass) * baseHeightKernel (R * y)

theorem scaledBaseHeightKernel_nonneg {R : ℝ} (hR : 0 ≤ R) (y : ℝ) :
    0 ≤ scaledBaseHeightKernel R y := by
  unfold scaledBaseHeightKernel
  exact mul_nonneg (div_nonneg hR baseHeightKernelMass_pos.le)
    (baseHeightKernel_nonneg _)

theorem scaledBaseHeightKernel_integrable {R : ℝ} (hR : 0 < R) :
    Integrable (scaledBaseHeightKernel R) := by
  unfold scaledBaseHeightKernel
  exact (baseHeightKernel_integrable.comp_mul_left' hR.ne').const_mul _

theorem integral_scaledBaseHeightKernel {R : ℝ} (hR : 0 < R) :
    ∫ y, scaledBaseHeightKernel R y = 1 := by
  unfold scaledBaseHeightKernel
  rw [integral_const_mul]
  have hscale := Measure.integral_comp_mul_left baseHeightKernel R
  rw [abs_of_pos (inv_pos.mpr hR), smul_eq_mul, integral_baseHeightKernel] at hscale
  rw [hscale, div_eq_mul_inv]
  calc
    R * baseHeightKernelMass⁻¹ * (R⁻¹ * baseHeightKernelMass) =
        (R * R⁻¹) * (baseHeightKernelMass⁻¹ * baseHeightKernelMass) := by ring
    _ = 1 := by rw [mul_inv_cancel₀ hR.ne',
      inv_mul_cancel₀ baseHeightKernelMass_pos.ne', one_mul]

theorem smoothHeightWindow_integrable {w : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    Integrable (smoothHeightWindow w) :=
  (smoothHeightWindow_contDiff hw hw1).continuous.integrable_of_hasCompactSupport
    (smoothHeightWindow_hasCompactSupport hw)

theorem windowAveragedHeightWeight_eq_convolution
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (x : ℝ) :
    windowAveragedHeightWeight R w x =
      convolution (smoothHeightWindow w) (scaledBaseHeightKernel R)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  rw [windowAveragedHeightWeight,
    paperFT_windowAveragedHeightTest_real_formula hR hw hw1]
  simp only [Complex.ofReal_re, convolution_def, ContinuousLinearMap.mul_apply']
  unfold scaledBaseHeightKernel
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with c
  ring

theorem windowAveragedHeightWeight_integrable
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    Integrable (windowAveragedHeightWeight R w) := by
  rw [funext (windowAveragedHeightWeight_eq_convolution hR hw hw1)]
  exact (smoothHeightWindow_integrable hw hw1).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (scaledBaseHeightKernel_integrable hR)

theorem integral_windowAveragedHeightWeight
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    ∫ x, windowAveragedHeightWeight R w x = ∫ x, smoothHeightWindow w x := by
  rw [funext (windowAveragedHeightWeight_eq_convolution hR hw hw1)]
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (smoothHeightWindow_integrable hw hw1) (scaledBaseHeightKernel_integrable hR)]
  rw [ContinuousLinearMap.mul_apply', integral_scaledBaseHeightKernel hR, mul_one]

theorem windowAveragedHeightWeight_continuous
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    Continuous (windowAveragedHeightWeight R w) := by
  unfold windowAveragedHeightWeight
  exact (Zeta23.Taper.contDiff_re_paperFT_ofReal
    (windowAveragedHeightTest_contDiff hR hw hw1).continuous
    (windowAveragedHeightTest_hasCompactSupport hR) 0).continuous

theorem integral_min_windowAveragedHeightWeight_tendsto
    {w : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    Tendsto (fun R : ℝ => ∫ x, min (windowAveragedHeightWeight R w x)
      (smoothHeightWindow w x)) atTop
      (𝓝 (∫ x, smoothHeightWindow w x)) := by
  let F : ℝ → ℝ → ℝ := fun R x =>
    min (windowAveragedHeightWeight R w x) (smoothHeightWindow w x)
  have hHcont := (smoothHeightWindow_contDiff hw hw1).continuous
  have hHint := smoothHeightWindow_integrable hw hw1
  have hFmeas : ∀ᶠ R : ℝ in atTop, AEStronglyMeasurable (F R) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact ((windowAveragedHeightWeight_continuous hR hw hw1).min
      hHcont).aestronglyMeasurable
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ᵐ x : ℝ,
      ‖F R x‖ ≤ smoothHeightWindow w x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    filter_upwards [] with x
    have hW : 0 ≤ windowAveragedHeightWeight R w x :=
      (paperFT_windowAveragedHeightTest_real_mem_Icc hR hw hw1 x).1
    have hH : 0 ≤ smoothHeightWindow w x := smoothHeightWindow_nonneg
    change |min (windowAveragedHeightWeight R w x)
      (smoothHeightWindow w x)| ≤ smoothHeightWindow w x
    rw [abs_of_nonneg (le_min hW hH)]
    exact min_le_right _ _
  have hpoint : ∀ᵐ x : ℝ, Tendsto (fun R : ℝ => F R x) atTop
      (𝓝 (smoothHeightWindow w x)) := by
    filter_upwards [] with x
    have hW := windowAveragedHeightWeight_tendsto hw hw1 x
    have hconst : Tendsto (fun _ : ℝ => smoothHeightWindow w x) atTop
        (𝓝 (smoothHeightWindow w x)) := tendsto_const_nhds
    simpa only [F, min_self] using hW.min hconst
  exact tendsto_integral_filter_of_dominated_convergence
    (smoothHeightWindow w) hFmeas hbound hHint hpoint

theorem abs_sub_eq_add_sub_two_mul_min {a b : ℝ} :
    |a - b| = a + b - 2 * min a b := by
  by_cases hab : a ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), min_eq_left hab]
    ring
  · have hba : b ≤ a := le_of_not_ge hab
    rw [abs_of_nonneg (sub_nonneg.mpr hba), min_eq_right hba]
    ring

theorem integral_abs_windowAveragedHeightWeight_sub_tendsto_zero
    {w : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    Tendsto (fun R : ℝ => ∫ x, |windowAveragedHeightWeight R w x -
      smoothHeightWindow w x|) atTop (𝓝 0) := by
  let M : ℝ → ℝ := fun R => ∫ x,
    min (windowAveragedHeightWeight R w x) (smoothHeightWindow w x)
  let I : ℝ := ∫ x, smoothHeightWindow w x
  have hM : Tendsto M atTop (𝓝 I) := by
    simpa only [M, I] using integral_min_windowAveragedHeightWeight_tendsto hw hw1
  have hmodel : Tendsto (fun R : ℝ => 2 * I - 2 * M R) atTop (𝓝 0) := by
    have htwoI : Tendsto (fun _ : ℝ => 2 * I) atTop (𝓝 (2 * I)) := tendsto_const_nhds
    have htwoM := (show Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2)
      from tendsto_const_nhds).mul hM
    simpa only [sub_self] using htwoI.sub htwoM
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hWint := windowAveragedHeightWeight_integrable hR hw hw1
  have hHint := smoothHeightWindow_integrable hw hw1
  have hminInt : Integrable (fun x => min (windowAveragedHeightWeight R w x)
      (smoothHeightWindow w x)) := by
    refine Integrable.mono' hHint
      ((windowAveragedHeightWeight_continuous hR hw hw1).min
        (smoothHeightWindow_contDiff hw hw1).continuous).aestronglyMeasurable ?_
    filter_upwards [] with x
    have hWIcc : 0 ≤ windowAveragedHeightWeight R w x :=
      (paperFT_windowAveragedHeightTest_real_mem_Icc hR hw hw1 x).1
    have hmin0 : 0 ≤ min (windowAveragedHeightWeight R w x)
        (smoothHeightWindow w x) := le_min hWIcc smoothHeightWindow_nonneg
    have hle : min (windowAveragedHeightWeight R w x)
        (smoothHeightWindow w x) ≤ smoothHeightWindow w x := min_le_right _ _
    simpa [Real.norm_eq_abs, abs_of_nonneg hmin0,
      abs_of_nonneg smoothHeightWindow_nonneg] using hle
  have hfun : (fun x => |windowAveragedHeightWeight R w x -
      smoothHeightWindow w x|) = fun x =>
      windowAveragedHeightWeight R w x + smoothHeightWindow w x -
        2 * min (windowAveragedHeightWeight R w x) (smoothHeightWindow w x) := by
    funext x
    exact abs_sub_eq_add_sub_two_mul_min
  have hIntegral : (∫ x, |windowAveragedHeightWeight R w x -
      smoothHeightWindow w x|) =
      (∫ x, windowAveragedHeightWeight R w x) +
        (∫ x, smoothHeightWindow w x) -
          2 * ∫ x, min (windowAveragedHeightWeight R w x)
            (smoothHeightWindow w x) := by
    rw [hfun]
    change (∫ x, (windowAveragedHeightWeight R w + smoothHeightWindow w) x -
      (fun x => 2 * min (windowAveragedHeightWeight R w x)
        (smoothHeightWindow w x)) x) = _
    rw [integral_sub (hWint.add hHint) (hminInt.const_mul 2)]
    have hadd := integral_add hWint hHint
    have hmul := integral_const_mul (μ := volume) (2 : ℝ)
      (fun x => min (windowAveragedHeightWeight R w x) (smoothHeightWindow w x))
    change (∫ a : ℝ, windowAveragedHeightWeight R w a +
      smoothHeightWindow w a) -
        (∫ a : ℝ, 2 * min (windowAveragedHeightWeight R w a)
          (smoothHeightWindow w a)) = _
    rw [hadd, hmul]
  rw [hIntegral, integral_windowAveragedHeightWeight hR hw hw1]
  unfold I M
  ring

theorem abs_pow_sub_pow_le_nat_mul_abs_sub
    {a b : ℝ} {k : ℕ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |a ^ k - b ^ k| ≤ (k : ℝ) * |a - b| := by
  have hmax0 : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg a)
  have hmax1 : max |a| |b| ≤ 1 := by
    rw [max_le_iff, abs_of_nonneg ha0, abs_of_nonneg hb0]
    exact ⟨ha1, hb1⟩
  calc
    |a ^ k - b ^ k| ≤ |a - b| * (k : ℝ) * max |a| |b| ^ (k - 1) :=
      abs_pow_sub_pow_le a b k
    _ ≤ |a - b| * (k : ℝ) * 1 := by
      gcongr
      exact pow_le_one₀ hmax0 hmax1
    _ = (k : ℝ) * |a - b| := by ring

theorem windowAveragedHeightWeight_pow_integrable
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (n : ℕ) :
    Integrable (fun x => windowAveragedHeightWeight R w x ^ (n + 1)) := by
  have hWint := windowAveragedHeightWeight_integrable hR hw hw1
  have hWcont := windowAveragedHeightWeight_continuous hR hw hw1
  have hprod : Integrable (fun x => windowAveragedHeightWeight R w x *
      windowAveragedHeightWeight R w x ^ n) := by
    refine hWint.mul_bdd (c := 1) (hWcont.pow n).aestronglyMeasurable ?_
    filter_upwards [] with x
    have hIcc : windowAveragedHeightWeight R w x ∈ Set.Icc 0 1 :=
      paperFT_windowAveragedHeightTest_real_mem_Icc hR hw hw1 x
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hIcc.1]
    exact pow_le_one₀ hIcc.1 hIcc.2
  simpa only [pow_succ'] using hprod

theorem smoothHeightWindow_pow_integrable
    {w : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) (n : ℕ) :
    Integrable (fun x => smoothHeightWindow w x ^ (n + 1)) := by
  have hHint := smoothHeightWindow_integrable hw hw1
  have hHcont := (smoothHeightWindow_contDiff hw hw1).continuous
  have hprod : Integrable (fun x => smoothHeightWindow w x *
      smoothHeightWindow w x ^ n) := by
    refine hHint.mul_bdd (c := 1) (hHcont.pow n).aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg smoothHeightWindow_nonneg]
    exact pow_le_one₀ smoothHeightWindow_nonneg smoothHeightWindow_le_one
  simpa only [pow_succ'] using hprod

theorem integral_windowAveragedHeightWeight_pow_tendsto
    {w : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) (n : ℕ) :
    Tendsto (fun R : ℝ => ∫ x, windowAveragedHeightWeight R w x ^ (n + 1))
      atTop (𝓝 (∫ x, smoothHeightWindow w x ^ (n + 1))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let U : ℝ → ℝ := fun R => (n + 1 : ℝ) *
    ∫ x, |windowAveragedHeightWeight R w x - smoothHeightWindow w x|
  apply squeeze_zero' (g := U)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hWpow := windowAveragedHeightWeight_pow_integrable hR hw hw1 n
    have hHpow := smoothHeightWindow_pow_integrable hw hw1 n
    rw [← integral_sub hWpow hHpow]
    have hdiff := (windowAveragedHeightWeight_integrable hR hw hw1).sub
      (smoothHeightWindow_integrable hw hw1)
    have hmajor : Integrable (fun x => (n + 1 : ℝ) *
        |windowAveragedHeightWeight R w x - smoothHeightWindow w x|) :=
      hdiff.abs.const_mul _
    have hle : ‖∫ a : ℝ, windowAveragedHeightWeight R w a ^ (n + 1) -
        smoothHeightWindow w a ^ (n + 1)‖ ≤
        ∫ x, (n + 1 : ℝ) *
          |windowAveragedHeightWeight R w x - smoothHeightWindow w x| := by
      apply norm_integral_le_of_norm_le hmajor
      filter_upwards [] with x
      rw [Real.norm_eq_abs]
      have hIcc : windowAveragedHeightWeight R w x ∈ Set.Icc 0 1 :=
        paperFT_windowAveragedHeightTest_real_mem_Icc hR hw hw1 x
      simpa only [Nat.cast_add, Nat.cast_one] using
        (abs_pow_sub_pow_le_nat_mul_abs_sub (k := n + 1)
          hIcc.1 hIcc.2
          (smoothHeightWindow_nonneg (w := w) (x := x))
          (smoothHeightWindow_le_one (w := w) (x := x)))
    have hconst := integral_const_mul (μ := volume) (n + 1 : ℝ)
      (fun x => |windowAveragedHeightWeight R w x - smoothHeightWindow w x|)
    change _ ≤ (n + 1 : ℝ) *
      ∫ x, |windowAveragedHeightWeight R w x - smoothHeightWindow w x|
    rw [← hconst]
    exact hle
  · have h := (show Tendsto (fun _ : ℝ => (n + 1 : ℝ)) atTop
        (𝓝 (n + 1 : ℝ)) from tendsto_const_nhds).mul
      (integral_abs_windowAveragedHeightWeight_sub_tendsto_zero hw hw1)
    simpa only [mul_zero, U] using h

def windowAveragedHeightFamily {n : ℕ} (R w : ℝ) :
    Fin (n + 1) → ℝ → ℂ :=
  fun _ => windowAveragedHeightTest R w

theorem paperFT_windowAveragedHeightTest_real
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (x : ℝ) :
    paperFT (windowAveragedHeightTest R w) (x : ℂ) =
      (windowAveragedHeightWeight R w x : ℂ) := by
  rw [windowAveragedHeightWeight,
    paperFT_windowAveragedHeightTest_real_formula hR hw hw1]
  rfl

theorem rsHeightFactor_windowAveragedHeightFamily
    {n : ℕ} {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    RH.Zeta85.rsHeightFactor
      (windowAveragedHeightFamily (n := n) R w) =
      ((∫ x, windowAveragedHeightWeight R w x ^ (n + 1) : ℝ) : ℂ) := by
  unfold RH.Zeta85.rsHeightFactor windowAveragedHeightFamily
  simp_rw [paperFT_windowAveragedHeightTest_real hR hw hw1]
  have hprod : ∀ x : ℝ,
      (∏ _j : Fin (n + 1), (windowAveragedHeightWeight R w x : ℂ)) =
        ((windowAveragedHeightWeight R w x ^ (n + 1) : ℝ) : ℂ) := by
    intro x
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rfl
  simp_rw [hprod]
  exact Zeta23.integral_ofReal_C _

theorem rsHeightFactor_windowAveragedHeightFamily_tendsto
    {n : ℕ} {w : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    Tendsto (fun R : ℝ => RH.Zeta85.rsHeightFactor
      (windowAveragedHeightFamily (n := n) R w)) atTop
      (𝓝 ((∫ x, smoothHeightWindow w x ^ (n + 1) : ℝ) : ℂ)) := by
  have hreal := integral_windowAveragedHeightWeight_pow_tendsto hw hw1 n
  have hcast := Complex.continuous_ofReal.tendsto
    ((∫ x, smoothHeightWindow w x ^ (n + 1) : ℝ))
  have hcomp := hcast.comp hreal
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Function.comp_apply,
    rsHeightFactor_windowAveragedHeightFamily (n := n) hR hw hw1]

def closedDyadicHeightIndicator (x : ℝ) : ℝ :=
  (Set.Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) x

theorem closedDyadicHeightIndicator_integrable :
    Integrable closedDyadicHeightIndicator := by
  unfold closedDyadicHeightIndicator
  exact (integrableOn_const (s := Set.Icc (1 : ℝ) 2)
    (by simp [Real.volume_Icc])).integrable_indicator
    measurableSet_Icc

theorem norm_smoothHeightWindow_pow_le_closedIndicator
    {w : ℝ} (hw : 0 < w) (k : ℕ) (hk : k ≠ 0) (x : ℝ) :
    ‖smoothHeightWindow w x ^ k‖ ≤ closedDyadicHeightIndicator x := by
  by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
  · rw [closedDyadicHeightIndicator]
    simp only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_pow,
      abs_of_nonneg smoothHeightWindow_nonneg]
    exact pow_le_one₀ smoothHeightWindow_nonneg smoothHeightWindow_le_one
  · have houter : 1 / 2 ≤ |x - 3 / 2| := by
      simp only [Set.mem_Icc, not_and_or] at hx
      rcases hx with hx | hx
      · have hx' : x < 1 := lt_of_not_ge hx
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hx' : 2 < x := lt_of_not_ge hx
        rw [abs_of_nonneg (by linarith)]
        linarith
    rw [smoothHeightWindow_eq_zero_of_outer hw houter, zero_pow]
    · simp [closedDyadicHeightIndicator, hx]
    · exact hk

theorem integral_smoothHeightWindow_pow_tendsto_one (n : ℕ) :
    Tendsto (fun m : ℕ => ∫ x, smoothHeightWindow
      (RH.Zeta85.RSReduction.topHatSmoothingWidth 1 m) x ^ (n + 1))
      atTop (𝓝 1) := by
  let F : ℕ → ℝ → ℝ := fun m x => smoothHeightWindow
    (RH.Zeta85.RSReduction.topHatSmoothingWidth 1 m) x ^ (n + 1)
  have hmeas : ∀ m : ℕ, AEStronglyMeasurable (F m) := by
    intro m
    have hw := RH.Zeta85.RSReduction.topHatSmoothingWidth_pos
      (show (0 : ℝ) < 1 by norm_num) m
    have hw1 := RH.Zeta85.RSReduction.two_mul_topHatSmoothingWidth_le
      (show (0 : ℝ) < 1 by norm_num) m
    exact ((smoothHeightWindow_contDiff hw hw1).continuous.pow (n + 1)).aestronglyMeasurable
  have hbound : ∀ m : ℕ, ∀ᵐ x : ℝ, ‖F m x‖ ≤ closedDyadicHeightIndicator x := by
    intro m
    filter_upwards [] with x
    exact norm_smoothHeightWindow_pow_le_closedIndicator
      (RH.Zeta85.RSReduction.topHatSmoothingWidth_pos
        (show (0 : ℝ) < 1 by norm_num) m)
      (n + 1) (Nat.succ_ne_zero n) x
  have hpoint : ∀ᵐ x : ℝ, Tendsto (fun m : ℕ => F m x) atTop
      (𝓝 (openDyadicHeightIndicator x)) := by
    filter_upwards [] with x
    have h := (smoothHeightWindow_tendsto_openDyadicHeightIndicator x).pow (n + 1)
    have hidem : openDyadicHeightIndicator x ^ (n + 1) =
        openDyadicHeightIndicator x := by
      by_cases hx : x ∈ Set.Ioo (1 : ℝ) 2 <;>
        simp [openDyadicHeightIndicator, hx]
    rw [hidem] at h
    exact h
  have hlim := tendsto_integral_of_dominated_convergence
    closedDyadicHeightIndicator hmeas closedDyadicHeightIndicator_integrable
      hbound hpoint
  have htarget : ∫ x, openDyadicHeightIndicator x = 1 := by
    unfold openDyadicHeightIndicator
    rw [integral_indicator_const _ measurableSet_Ioo, measureReal_def,
      Real.volume_Ioo, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
    norm_num
  rw [htarget] at hlim
  exact hlim

theorem rsHeightFactor_windowAveragedHeightFamily_iterated_tendsto_one
    (n : ℕ) :
    (∀ m : ℕ,
      Tendsto (fun R : ℝ => RH.Zeta85.rsHeightFactor
        (windowAveragedHeightFamily (n := n) R
          (RH.Zeta85.RSReduction.topHatSmoothingWidth 1 m))) atTop
        (𝓝 ((∫ x, smoothHeightWindow
          (RH.Zeta85.RSReduction.topHatSmoothingWidth 1 m) x ^ (n + 1) : ℝ) : ℂ))) ∧
    Tendsto (fun m : ℕ => Complex.ofReal
      (∫ x, smoothHeightWindow
        (RH.Zeta85.RSReduction.topHatSmoothingWidth 1 m) x ^ (n + 1)))
      atTop (𝓝 (1 : ℂ)) := by
  constructor
  · intro m
    exact rsHeightFactor_windowAveragedHeightFamily_tendsto
      (RH.Zeta85.RSReduction.topHatSmoothingWidth_pos
        (show (0 : ℝ) < 1 by norm_num) m)
      (RH.Zeta85.RSReduction.two_mul_topHatSmoothingWidth_le
        (show (0 : ℝ) < 1 by norm_num) m)
  · have hcast := Complex.continuous_ofReal.tendsto (1 : ℝ)
    have hcomp := hcast.comp (integral_smoothHeightWindow_pow_tendsto_one n)
    refine hcomp.congr' ?_
    filter_upwards [] with m
    rfl

end RH.Zeta85.RSPoissonCyclicBridge
