import RH.Zeta85.Discharge.RSFiniteHeightSplit

open Complex MeasureTheory Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

def baseHeightKernelTail (A : ℝ) : ℝ :=
  ∫ y in {y : ℝ | A ≤ |y|}, baseHeightKernel y

theorem baseHeightKernelTail_nonneg (A : ℝ) :
    0 ≤ baseHeightKernelTail A := by
  unfold baseHeightKernelTail
  exact integral_nonneg fun y => baseHeightKernel_nonneg y

theorem baseHeightKernelTail_tendsto_zero :
    Tendsto baseHeightKernelTail atTop (𝓝 0) := by
  let F : ℝ → ℝ → ℝ := fun A y =>
    {y : ℝ | A ≤ |y|}.indicator baseHeightKernel y
  have hmeas : ∀ A : ℝ, AEStronglyMeasurable (F A) := by
    intro A
    exact baseHeightKernel_continuous.aestronglyMeasurable.indicator
      (measurableSet_le measurable_const continuous_abs.measurable)
  have hbound : ∀ A : ℝ, ∀ᵐ y : ℝ, ‖F A y‖ ≤ baseHeightKernel y := by
    intro A
    filter_upwards [] with y
    by_cases hy : A ≤ |y|
    · simp [F, hy, Real.norm_eq_abs, abs_of_nonneg (baseHeightKernel_nonneg y)]
    · simp [F, hy, baseHeightKernel_nonneg y]
  have hpoint : ∀ᵐ y : ℝ, Tendsto (fun A : ℝ => F A y) atTop (𝓝 0) := by
    filter_upwards [] with y
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop |y|] with A hA
    simp [F, not_le_of_gt hA]
  have hlim := tendsto_integral_filter_of_dominated_convergence
    baseHeightKernel (Eventually.of_forall hmeas)
      (Eventually.of_forall hbound) baseHeightKernel_integrable hpoint
  have hlim' : Tendsto (fun A => ∫ y, F A y) atTop (𝓝 0) := by
    simpa only [integral_zero] using hlim
  apply hlim'.congr'
  filter_upwards [] with A
  unfold baseHeightKernelTail F
  exact MeasureTheory.integral_indicator
    (measurableSet_le measurable_const continuous_abs.measurable)

theorem one_sub_windowAveragedHeightWeight_le_tail
    {R w eta x : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (heta : 0 < eta) (hxlo : 1 + w + eta ≤ x)
    (hxhi : x ≤ 2 - w - eta) :
    1 - windowAveragedHeightWeight R w x ≤
      baseHeightKernelMass⁻¹ * baseHeightKernelTail (R * eta) := by
  let H : ℝ → ℝ := fun y => smoothHeightWindow w (x - y / R)
  let S : Set ℝ := {y : ℝ | R * eta ≤ |y|}
  have hSmeas : MeasurableSet S :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hprodInt : Integrable (fun y => H y * baseHeightKernel y) := by
    refine Integrable.mono' baseHeightKernel_integrable
      (((smoothHeightWindow_contDiff hw hw1).continuous.comp
        (by fun_prop)).mul baseHeightKernel_continuous).aestronglyMeasurable ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (smoothHeightWindow_nonneg (w := w) (x := x - y / R)),
      abs_of_nonneg (baseHeightKernel_nonneg y)]
    exact mul_le_of_le_one_left (baseHeightKernel_nonneg y)
      (smoothHeightWindow_le_one (w := w) (x := x - y / R))
  have hdiffInt : Integrable (fun y =>
      baseHeightKernel y - H y * baseHeightKernel y) :=
    baseHeightKernel_integrable.sub hprodInt
  have htailInt : Integrable (S.indicator baseHeightKernel) :=
    (baseHeightKernel_integrable.integrableOn).integrable_indicator hSmeas
  have hpoint : ∀ y : ℝ,
      baseHeightKernel y - H y * baseHeightKernel y ≤
        S.indicator baseHeightKernel y := by
    intro y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
      have hH0 : 0 ≤ H y := smoothHeightWindow_nonneg
      have hK0 : 0 ≤ baseHeightKernel y := baseHeightKernel_nonneg y
      nlinarith [smoothHeightWindow_le_one (w := w) (x := x - y / R)]
    · rw [Set.indicator_of_notMem hy]
      have hylt : |y| < R * eta := lt_of_not_ge hy
      have hydiv : |y / R| < eta := by
        rw [abs_div, abs_of_pos hR]
        exact (div_lt_iff₀ hR).2 (by simpa [mul_comm] using hylt)
      have hinner : |(x - y / R) - 3 / 2| ≤ 1 / 2 - w := by
        rw [abs_le]
        constructor <;> linarith [neg_abs_le (y / R), le_abs_self (y / R)]
      have hH : H y = 1 := smoothHeightWindow_eq_one_of_inner hw hinner
      rw [hH]
      simp
  have hintLe : (∫ y, baseHeightKernel y - H y * baseHeightKernel y) ≤
      ∫ y, S.indicator baseHeightKernel y :=
    integral_mono hdiffInt htailInt hpoint
  rw [windowAveragedHeightWeight_eq_kernelIntegral hR hw hw1]
  change 1 - baseHeightKernelMass⁻¹ *
      (∫ y, H y * baseHeightKernel y) ≤ _
  have hmass := integral_baseHeightKernel
  have hM : baseHeightKernelMass ≠ 0 := baseHeightKernelMass_pos.ne'
  calc
    1 - baseHeightKernelMass⁻¹ * (∫ y, H y * baseHeightKernel y) =
        baseHeightKernelMass⁻¹ *
          ((∫ y, baseHeightKernel y) -
            ∫ y, H y * baseHeightKernel y) := by rw [hmass]; field_simp
    _ = baseHeightKernelMass⁻¹ *
        (∫ y, baseHeightKernel y - H y * baseHeightKernel y) := by
          rw [integral_sub baseHeightKernel_integrable hprodInt]
    _ ≤ baseHeightKernelMass⁻¹ *
        (∫ y, S.indicator baseHeightKernel y) := by
          exact mul_le_mul_of_nonneg_left hintLe
            (inv_nonneg.mpr baseHeightKernelMass_pos.le)
    _ = baseHeightKernelMass⁻¹ * baseHeightKernelTail (R * eta) := by
      rw [baseHeightKernelTail, MeasureTheory.integral_indicator hSmeas]

theorem windowAveragedHeightWeight_uniform_on_inner_core
    {w eta : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) (heta : 0 < eta) :
    ∀ epsilon > 0, ∀ᶠ R : ℝ in atTop, ∀ x : ℝ,
      1 + w + eta ≤ x → x ≤ 2 - w - eta →
        |windowAveragedHeightWeight R w x - 1| < epsilon := by
  intro epsilon hepsilon
  have hscale : Tendsto (fun R : ℝ => R * eta) atTop atTop :=
    tendsto_id.atTop_mul_const heta
  have htail : Tendsto (fun R : ℝ => baseHeightKernelTail (R * eta))
      atTop (𝓝 0) := baseHeightKernelTail_tendsto_zero.comp hscale
  have hboundLim : Tendsto (fun R : ℝ =>
      baseHeightKernelMass⁻¹ * baseHeightKernelTail (R * eta))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (show Tendsto (fun _ : ℝ => baseHeightKernelMass⁻¹) atTop
        (𝓝 baseHeightKernelMass⁻¹) from tendsto_const_nhds).mul htail
  filter_upwards [hboundLim.eventually (Iio_mem_nhds hepsilon),
    eventually_gt_atTop (0 : ℝ)] with R hsmall hR x hxlo hxhi
  have hIcc := paperFT_windowAveragedHeightTest_real_mem_Icc hR hw hw1 x
  have hWle : windowAveragedHeightWeight R w x ≤ 1 := by
    exact hIcc.2
  rw [abs_of_nonpos (sub_nonpos.mpr hWle)]
  simpa only [neg_sub] using
    (one_sub_windowAveragedHeightWeight_le_tail
      hR hw hw1 heta hxlo hxhi).trans_lt hsmall

end RH.Zeta85.RSPoissonCyclicBridge
