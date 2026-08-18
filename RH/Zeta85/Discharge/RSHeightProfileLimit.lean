import RH.Zeta85.Discharge.RSHeightProfiles

/-!
# Mixed compact-profile height-factor limits

Every nonnegative compact profile bounded by one is recovered in `L1` by
the averaged height selector.  Finite products therefore converge in `L1`,
which evaluates the Rudnick--Sarnak height factor for coordinate-dependent
profiles.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

theorem integral_min_averagedHeightWeightOf_tendsto
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    (hH0 : ∀ x, 0 ≤ H x) (hH1 : ∀ x, H x ≤ 1) :
    Tendsto (fun R : ℝ => ∫ x, min (averagedHeightWeightOf H R x) (H x))
      atTop (𝓝 (∫ x, H x)) := by
  let F : ℝ → ℝ → ℝ := fun R x => min (averagedHeightWeightOf H R x) (H x)
  have hHint : Integrable H := hH.integrable_of_hasCompactSupport hHc
  have hFmeas : ∀ᶠ R : ℝ in atTop, AEStronglyMeasurable (F R) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact ((averagedHeightWeightOf_continuous hH hHc hR).min hH).aestronglyMeasurable
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ᵐ x : ℝ, ‖F R x‖ ≤ H x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    filter_upwards [] with x
    have hW : 0 ≤ averagedHeightWeightOf H R x :=
      (paperFT_averagedHeightTestOf_real_mem_Icc hH hHc hH0 hH1 hR x).1
    change |min (averagedHeightWeightOf H R x) (H x)| ≤ H x
    rw [abs_of_nonneg (le_min hW (hH0 x))]
    exact min_le_right _ _
  have hpoint : ∀ᵐ x : ℝ, Tendsto (fun R : ℝ => F R x) atTop (𝓝 (H x)) := by
    filter_upwards [] with x
    have hW := averagedHeightWeightOf_tendsto hH hHc hH0 hH1 x
    have hconst : Tendsto (fun _ : ℝ => H x) atTop (𝓝 (H x)) :=
      tendsto_const_nhds
    simpa only [F, min_self] using hW.min hconst
  exact tendsto_integral_filter_of_dominated_convergence H hFmeas hbound hHint hpoint

theorem integral_abs_averagedHeightWeightOf_sub_tendsto_zero
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    (hH0 : ∀ x, 0 ≤ H x) (hH1 : ∀ x, H x ≤ 1) :
    Tendsto (fun R : ℝ => ∫ x, |averagedHeightWeightOf H R x - H x|)
      atTop (𝓝 0) := by
  let M : ℝ → ℝ := fun R => ∫ x, min (averagedHeightWeightOf H R x) (H x)
  let I : ℝ := ∫ x, H x
  have hM : Tendsto M atTop (𝓝 I) := by
    simpa only [M, I] using
      integral_min_averagedHeightWeightOf_tendsto hH hHc hH0 hH1
  have hmodel : Tendsto (fun R : ℝ => 2 * I - 2 * M R) atTop (𝓝 0) := by
    have htwoM := (show Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2)
      from tendsto_const_nhds).mul hM
    simpa only [sub_self] using
      (show Tendsto (fun _ : ℝ => 2 * I) atTop (𝓝 (2 * I))
        from tendsto_const_nhds).sub htwoM
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hWint := averagedHeightWeightOf_integrable hH hHc hR
  have hHint : Integrable H := hH.integrable_of_hasCompactSupport hHc
  have hminInt : Integrable (fun x => min (averagedHeightWeightOf H R x) (H x)) := by
    refine Integrable.mono' hHint
      ((averagedHeightWeightOf_continuous hH hHc hR).min hH).aestronglyMeasurable ?_
    filter_upwards [] with x
    have hW0 : 0 ≤ averagedHeightWeightOf H R x :=
      (paperFT_averagedHeightTestOf_real_mem_Icc hH hHc hH0 hH1 hR x).1
    have hmin0 : 0 ≤ min (averagedHeightWeightOf H R x) (H x) :=
      le_min hW0 (hH0 x)
    have hle : min (averagedHeightWeightOf H R x) (H x) ≤ H x := min_le_right _ _
    simpa [Real.norm_eq_abs, abs_of_nonneg hmin0, abs_of_nonneg (hH0 x)] using hle
  have hfun : (fun x => |averagedHeightWeightOf H R x - H x|) = fun x =>
      averagedHeightWeightOf H R x + H x -
        2 * min (averagedHeightWeightOf H R x) (H x) := by
    funext x
    exact abs_sub_eq_add_sub_two_mul_min
  have hIntegral : (∫ x, |averagedHeightWeightOf H R x - H x|) =
      (∫ x, averagedHeightWeightOf H R x) + (∫ x, H x) -
        2 * ∫ x, min (averagedHeightWeightOf H R x) (H x) := by
    rw [hfun]
    change (∫ x, (averagedHeightWeightOf H R + H) x -
      (fun x => 2 * min (averagedHeightWeightOf H R x) (H x)) x) = _
    rw [integral_sub (hWint.add hHint) (hminInt.const_mul 2)]
    have hadd := integral_add hWint hHint
    have hmul := integral_const_mul (μ := volume) (2 : ℝ)
      (fun x => min (averagedHeightWeightOf H R x) (H x))
    change (∫ x, averagedHeightWeightOf H R x + H x) -
      (∫ x, 2 * min (averagedHeightWeightOf H R x) (H x)) = _
    rw [hadd, hmul]
  rw [hIntegral, integral_averagedHeightWeightOf hH hHc hR]
  unfold I M
  ring

theorem abs_finset_prod_sub_prod_le_sum_abs_of_Icc
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf0 i (Finset.mem_insert_of_mem hi)
      have hfs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi => hf1 i (Finset.mem_insert_of_mem hi)
      have hgs0 : ∀ i ∈ s, 0 ≤ g i := fun i hi => hg0 i (Finset.mem_insert_of_mem hi)
      have hgs1 : ∀ i ∈ s, g i ≤ 1 := fun i hi => hg1 i (Finset.mem_insert_of_mem hi)
      have hprodf : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hfs0
      have hprodg : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg hgs0
      have hprodg1 : (∏ i ∈ s, g i) ≤ 1 := Finset.prod_le_one hgs0 hgs1
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha]
      calc
        |f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i| =
            |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
              (f a - g a) * ∏ i ∈ s, g i| := by
                congr 1
                ring
        _ ≤ |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| +
              |(f a - g a) * ∏ i ∈ s, g i| := abs_add_le _ _
        _ = f a * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| +
              |f a - g a| * (∏ i ∈ s, g i) := by
                rw [abs_mul, abs_mul, abs_of_nonneg (hf0 a (Finset.mem_insert_self a s)),
                  abs_of_nonneg hprodg]
        _ ≤ 1 * (∑ i ∈ s, |f i - g i|) + |f a - g a| * 1 := by
          gcongr
          · exact hf1 a (Finset.mem_insert_self a s)
          · exact ih hfs0 hfs1 hgs0 hgs1
        _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring

theorem integral_prod_averagedHeightWeightOf_tendsto
    {n : ℕ} {H : Fin (n + 1) → ℝ → ℝ}
    (hH : ∀ j, Continuous (H j)) (hHc : ∀ j, HasCompactSupport (H j))
    (hH0 : ∀ j x, 0 ≤ H j x) (hH1 : ∀ j x, H j x ≤ 1) :
    Tendsto
      (fun R : ℝ => ∫ x, ∏ j, averagedHeightWeightOf (H j) R x)
      atTop (𝓝 (∫ x, ∏ j, H j x)) := by
  let i0 : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let W : ℝ → Fin (n + 1) → ℝ → ℝ :=
    fun R j x => averagedHeightWeightOf (H j) R x
  have hdiff (j : Fin (n + 1)) : Tendsto
      (fun R : ℝ => ∫ x, |W R j x - H j x|) atTop (𝓝 0) := by
    simpa only [W] using integral_abs_averagedHeightWeightOf_sub_tendsto_zero
      (hH j) (hHc j) (hH0 j) (hH1 j)
  have hsumlim : Tendsto
      (fun R : ℝ => ∑ j, ∫ x, |W R j x - H j x|) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun j _ => hdiff j)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
    (g := fun R : ℝ => ∑ j, ∫ x, |W R j x - H j x|)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hWIcc : ∀ j x, W R j x ∈ Set.Icc (0 : ℝ) 1 := by
      intro j x
      simpa only [W, averagedHeightWeightOf] using
        paperFT_averagedHeightTestOf_real_mem_Icc
          (hH j) (hHc j) (hH0 j) (hH1 j) hR x
    have hWprodInt : Integrable (fun x => ∏ j, W R j x) := by
      let rest := Finset.univ.erase i0
      have hrestCont : Continuous (fun x => ∏ j ∈ rest, W R j x) := by
        apply continuous_finsetProd
        intro j hj
        simpa only [W] using averagedHeightWeightOf_continuous (hH j) (hHc j) hR
      have hrestBound : ∀ᵐ x : ℝ, ‖∏ j ∈ rest, W R j x‖ ≤ 1 := by
        filter_upwards [] with x
        rw [norm_prod]
        apply Finset.prod_le_one
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          rw [Real.norm_eq_abs, abs_of_nonneg (hWIcc j x).1]
          exact (hWIcc j x).2
      have hmul := (averagedHeightWeightOf_integrable (hH i0) (hHc i0) hR).mul_bdd
        hrestCont.aestronglyMeasurable hrestBound
      apply hmul.congr
      filter_upwards [] with x
      exact Finset.mul_prod_erase Finset.univ (fun j => W R j x) (Finset.mem_univ i0)
    have hHprodInt : Integrable (fun x => ∏ j, H j x) := by
      let rest := Finset.univ.erase i0
      have hrestCont : Continuous (fun x => ∏ j ∈ rest, H j x) := by
        apply continuous_finsetProd
        intro j hj
        exact hH j
      have hrestBound : ∀ᵐ x : ℝ, ‖∏ j ∈ rest, H j x‖ ≤ 1 := by
        filter_upwards [] with x
        rw [norm_prod]
        apply Finset.prod_le_one
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          rw [Real.norm_eq_abs, abs_of_nonneg (hH0 j x)]
          exact hH1 j x
      have hmul := (hH i0).integrable_of_hasCompactSupport (hHc i0) |>.mul_bdd
        hrestCont.aestronglyMeasurable hrestBound
      apply hmul.congr
      filter_upwards [] with x
      exact Finset.mul_prod_erase Finset.univ (fun j => H j x) (Finset.mem_univ i0)
    rw [← integral_sub hWprodInt hHprodInt]
    have hcomponent : ∀ j ∈ Finset.univ,
        Integrable (fun x => |W R j x - H j x|) := by
      intro j hj
      exact ((averagedHeightWeightOf_integrable (hH j) (hHc j) hR).sub
        ((hH j).integrable_of_hasCompactSupport (hHc j))).abs
    have hmajor : Integrable (fun x => ∑ j, |W R j x - H j x|) := by
      exact integrable_finsetSum Finset.univ hcomponent
    have hle := norm_integral_le_of_norm_le hmajor
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact abs_finset_prod_sub_prod_le_sum_abs_of_Icc Finset.univ
          (fun j => W R j x) (fun j => H j x)
          (fun j _ => (hWIcc j x).1) (fun j _ => (hWIcc j x).2)
          (fun j _ => hH0 j x) (fun j _ => hH1 j x))
    rw [integral_finsetSum Finset.univ hcomponent] at hle
    exact hle
  · exact hsumlim

theorem rsHeightFactor_averagedHeightFamilyOf_tendsto
    {n : ℕ} {H : Fin (n + 1) → ℝ → ℝ}
    (hH : ∀ j, Continuous (H j)) (hHc : ∀ j, HasCompactSupport (H j))
    (hH0 : ∀ j x, 0 ≤ H j x) (hH1 : ∀ j x, H j x ≤ 1) :
    Tendsto (fun R : ℝ => RH.Zeta85.rsHeightFactor (averagedHeightFamilyOf H R))
      atTop (𝓝 ((∫ x, ∏ j, H j x : ℝ) : ℂ)) := by
  have hreal := integral_prod_averagedHeightWeightOf_tendsto hH hHc hH0 hH1
  have hcomp := Complex.continuous_ofReal.tendsto
    (∫ x, ∏ j, H j x) |>.comp hreal
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Function.comp_apply, rsHeightFactor_averagedHeightFamilyOf hH hHc hR]

end RH.Zeta85.RSPoissonCyclicBridge
