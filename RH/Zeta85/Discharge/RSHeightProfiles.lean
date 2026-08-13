import RH.Zeta85.Discharge.RSHeightEdgeCount

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def dualHeightProfile (H : ℝ → ℝ) (u : ℝ) : ℂ :=
  paperFT (fun x => (H x : ℂ)) (-u : ℂ)

theorem dualHeightProfile_contDiff
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H) :
    ContDiff ℝ ∞ (dualHeightProfile H) := by
  have hHC : Continuous (fun x => (H x : ℂ)) :=
    Complex.continuous_ofReal.comp hH
  have hHCc : HasCompactSupport (fun x => (H x : ℂ)) :=
    hHc.comp_left Complex.ofReal_zero
  have hFT := Zeta23.Taper.contDiff_paperFT_ofReal hHC hHCc (⊤ : ℕ∞)
  have heq : dualHeightProfile H = fun u : ℝ =>
      paperFT (fun x => (H x : ℂ)) ((-u : ℝ) : ℂ) := by
    funext u
    simp only [dualHeightProfile, Complex.ofReal_neg]
  rw [heq]
  exact hFT.comp contDiff_neg

def averagedHeightTestOf (H : ℝ → ℝ) (R u : ℝ) : ℂ :=
  ((R / baseHeightKernelMass : ℝ) : ℂ) *
    autocorrHeightTest (dilatedHeightBump R) 0 u * dualHeightProfile H u

theorem averagedHeightTestOf_contDiff
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (averagedHeightTestOf H R) := by
  unfold averagedHeightTestOf
  exact (contDiff_const.mul
    (autocorrHeightTest_contDiff (dilatedHeightBump_even R)
      (dilatedHeightBump_contDiff R)
      (dilatedHeightBump_hasCompactSupport hR.ne') 0)).mul
        (dualHeightProfile_contDiff hH hHc)

theorem averagedHeightTestOf_hasCompactSupport
    (H : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (averagedHeightTestOf H R) := by
  unfold averagedHeightTestOf
  exact ((autocorrHeightTest_hasCompactSupport (dilatedHeightBump_even R)
    (dilatedHeightBump_hasCompactSupport hR.ne') 0).mul_left).mul_right

theorem paperFT_averagedHeightTestOf
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    {R : ℝ} (hR : 0 < R) (z : ℂ) :
    paperFT (averagedHeightTestOf H R) z =
      ((R / baseHeightKernelMass : ℝ) : ℂ) *
        ∫ c : ℝ, (H c : ℂ) *
          paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
            (z - (c : ℂ)) := by
  let A : ℝ → ℂ := autocorrHeightTest (dilatedHeightBump R) 0
  let F : ℝ → ℝ → ℂ := fun c u =>
    (H c : ℂ) * A u * Complex.exp (Complex.I * (z - (c : ℂ)) * (u : ℂ))
  have hAcont : Continuous A :=
    (autocorrHeightTest_contDiff (dilatedHeightBump_even R)
      (dilatedHeightBump_contDiff R)
      (dilatedHeightBump_hasCompactSupport hR.ne') 0).continuous
  have hAc : HasCompactSupport A :=
    autocorrHeightTest_hasCompactSupport (dilatedHeightBump_even R)
      (dilatedHeightBump_hasCompactSupport hR.ne') 0
  have hFcont : Continuous (Function.uncurry F) := by
    exact (((Complex.continuous_ofReal.comp hH).comp continuous_fst).mul
      (hAcont.comp continuous_snd)).mul (by fun_prop)
  have hFcompact : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hHc.isCompact.prod hAc.isCompact) ?_
    intro p hp
    simp only [Function.mem_support] at hp
    have hHne : H p.1 ≠ 0 := by
      intro hz
      apply hp
      change (H p.1 : ℂ) * A p.2 *
        Complex.exp (Complex.I * (z - (p.1 : ℂ)) * (p.2 : ℂ)) = 0
      rw [hz, Complex.ofReal_zero, zero_mul, zero_mul]
    have hAne : A p.2 ≠ 0 := by
      intro hz
      apply hp
      change (H p.1 : ℂ) * A p.2 *
        Complex.exp (Complex.I * (z - (p.1 : ℂ)) * (p.2 : ℂ)) = 0
      rw [hz, mul_zero, zero_mul]
    exact ⟨subset_tsupport H hHne, subset_tsupport A hAne⟩
  have hswap : (∫ u : ℝ, ∫ c : ℝ, F c u) =
      ∫ c : ℝ, ∫ u : ℝ, F c u :=
    (MeasureTheory.integral_integral_swap_of_hasCompactSupport hFcont hFcompact).symm
  rw [paperFT_def]
  unfold averagedHeightTestOf
  rw [show (fun u : ℝ =>
      ((R / baseHeightKernelMass : ℝ) : ℂ) *
          autocorrHeightTest (dilatedHeightBump R) 0 u *
            dualHeightProfile H u * Complex.exp (Complex.I * z * (u : ℂ))) =
      fun u : ℝ => ((R / baseHeightKernelMass : ℝ) : ℂ) *
        (autocorrHeightTest (dilatedHeightBump R) 0 u *
          dualHeightProfile H u * Complex.exp (Complex.I * z * (u : ℂ))) by
        funext u
        ring]
  rw [integral_const_mul_C]
  congr 1
  calc
    (∫ u : ℝ, autocorrHeightTest (dilatedHeightBump R) 0 u *
          dualHeightProfile H u * Complex.exp (Complex.I * z * (u : ℂ))) =
        ∫ u : ℝ, ∫ c : ℝ, F c u := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [dualHeightProfile, paperFT_def]
      rw [← integral_const_mul_C, ← integral_mul_const_C]
      apply integral_congr_ae
      filter_upwards [] with c
      simp only [F, A]
      have hexp : Complex.exp (Complex.I * (-((u : ℝ) : ℂ)) * (c : ℂ)) *
          Complex.exp (Complex.I * z * (u : ℂ)) =
          Complex.exp (Complex.I * (z - (c : ℂ)) * (u : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      calc
        autocorrHeightTest (dilatedHeightBump R) 0 u *
              ((H c : ℂ) *
                Complex.exp (Complex.I * (-((u : ℝ) : ℂ)) * (c : ℂ))) *
              Complex.exp (Complex.I * z * (u : ℂ)) =
            (H c : ℂ) * autocorrHeightTest (dilatedHeightBump R) 0 u *
              (Complex.exp (Complex.I * (-((u : ℝ) : ℂ)) * (c : ℂ)) *
                Complex.exp (Complex.I * z * (u : ℂ))) := by ring
        _ = (H c : ℂ) * autocorrHeightTest (dilatedHeightBump R) 0 u *
              Complex.exp (Complex.I * (z - (c : ℂ)) * (u : ℂ)) := by rw [hexp]
    _ = ∫ c : ℝ, ∫ u : ℝ, F c u := hswap
    _ = ∫ c : ℝ, (H c : ℂ) *
          paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
            (z - (c : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with c
      rw [paperFT_def, ← integral_const_mul_C]
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [F, A]
      ring

theorem paperFT_averagedHeightTestOf_real_formula
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    {R : ℝ} (hR : 0 < R) (x : ℝ) :
    paperFT (averagedHeightTestOf H R) (x : ℂ) =
      (((R / baseHeightKernelMass) *
        ∫ c : ℝ, H c * baseHeightKernel (R * (x - c)) : ℝ) : ℂ) := by
  rw [paperFT_averagedHeightTestOf hH hHc hR]
  have hpoint : ∀ c : ℝ,
      paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
          ((x : ℂ) - (c : ℂ)) =
        (baseHeightKernel (R * (x - c)) : ℂ) := by
    intro c
    have h := paperFT_dilated_autocorrHeightTest_real_formula hR 0 (x - c)
    have harg : ((x : ℂ) - (c : ℂ)) = ((x - c : ℝ) : ℂ) := by
      exact (Complex.ofReal_sub x c).symm
    rw [harg]
    simpa [baseHeightKernel] using h
  simp_rw [hpoint]
  let rfun : ℝ → ℝ := fun c => H c * baseHeightKernel (R * (x - c))
  have hfun : (fun c : ℝ => (H c : ℂ) *
      (baseHeightKernel (R * (x - c)) : ℂ)) =
      fun c => (rfun c : ℂ) := by
    funext c
    exact (Complex.ofReal_mul _ _).symm
  let J : ℝ := ∫ c : ℝ, H c * baseHeightKernel (R * (x - c))
  have hint : (∫ c : ℝ, (H c : ℂ) *
      (baseHeightKernel (R * (x - c)) : ℂ)) = (J : ℂ) := by
    rw [hfun, Zeta23.integral_ofReal_C]
  calc
    ((R / baseHeightKernelMass : ℝ) : ℂ) *
        (∫ c : ℝ, (H c : ℂ) *
          (baseHeightKernel (R * (x - c)) : ℂ)) =
        ((R / baseHeightKernelMass : ℝ) : ℂ) * (J : ℂ) := by rw [hint]
    _ = (((R / baseHeightKernelMass) * J : ℝ) : ℂ) :=
      (Complex.ofReal_mul (R / baseHeightKernelMass) J).symm
    _ = (((R / baseHeightKernelMass) *
        ∫ c : ℝ, H c * baseHeightKernel (R * (x - c)) : ℝ) : ℂ) := by rfl

def averagedHeightWeightOf (H : ℝ → ℝ) (R x : ℝ) : ℝ :=
  (paperFT (averagedHeightTestOf H R) (x : ℂ)).re

theorem averagedHeightWeightOf_eq_kernelIntegral
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    {R : ℝ} (hR : 0 < R) (x : ℝ) :
    averagedHeightWeightOf H R x =
      baseHeightKernelMass⁻¹ *
        ∫ y : ℝ, H (x - y / R) * baseHeightKernel y := by
  rw [averagedHeightWeightOf,
    paperFT_averagedHeightTestOf_real_formula hH hHc hR]
  simp only [Complex.ofReal_re]
  let f : ℝ → ℝ := fun d => H (x - d) * baseHeightKernel (R * d)
  let g : ℝ → ℝ := fun y => H (x - y / R) * baseHeightKernel y
  have hshift : (∫ c : ℝ, H c * baseHeightKernel (R * (x - c))) =
      ∫ d : ℝ, f d := by
    have h := MeasureTheory.integral_sub_left_eq_self f volume x
    calc
      (∫ c : ℝ, H c * baseHeightKernel (R * (x - c))) =
          ∫ c : ℝ, f (x - c) := by
            apply integral_congr_ae
            filter_upwards [] with c
            simp only [f]
            ring
      _ = ∫ d : ℝ, f d := h
  have hscale := Measure.integral_comp_mul_left g R
  have hfg : (fun d : ℝ => g (R * d)) = f := by
    funext d
    simp only [g, f]
    congr 2
    rw [mul_div_cancel_left₀ d hR.ne']
  rw [hfg, abs_of_pos (inv_pos.mpr hR), smul_eq_mul] at hscale
  rw [hshift, hscale]
  simp only [g]
  rw [div_eq_mul_inv]
  calc
    R * baseHeightKernelMass⁻¹ *
        (R⁻¹ * ∫ y, H (x - y / R) * baseHeightKernel y) =
        baseHeightKernelMass⁻¹ *
          ((R * R⁻¹) * ∫ y, H (x - y / R) * baseHeightKernel y) := by
            ring
    _ = baseHeightKernelMass⁻¹ *
        ∫ y, H (x - y / R) * baseHeightKernel y := by
      rw [mul_inv_cancel₀ hR.ne', one_mul]

theorem paperFT_averagedHeightTestOf_real_mem_Icc
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    (hH0 : ∀ x, 0 ≤ H x) (hH1 : ∀ x, H x ≤ 1)
    {R : ℝ} (hR : 0 < R) (x : ℝ) :
    (paperFT (averagedHeightTestOf H R) (x : ℂ)).re ∈ Set.Icc 0 1 := by
  rw [paperFT_averagedHeightTestOf_real_formula hH hHc hR]
  simp only [Complex.ofReal_re]
  have hM : 0 < baseHeightKernelMass := baseHeightKernelMass_pos
  have hscale : 0 ≤ R / baseHeightKernelMass := (div_pos hR hM).le
  let q : ℝ → ℝ := fun c => baseHeightKernel (R * (x - c))
  have hqint : Integrable q := by
    unfold q
    exact (baseHeightKernel_integrable.comp_mul_left' hR.ne').comp_sub_left x
  have hHint : Integrable (fun c => q c * H c) := by
    refine hqint.mul_bdd (c := 1) hH.aestronglyMeasurable ?_
    filter_upwards [] with c
    rw [Real.norm_eq_abs, abs_of_nonneg (hH0 c)]
    exact hH1 c
  have hprodint : Integrable (fun c => H c * q c) := by
    convert hHint using 1
    funext c
    ring
  have hI0 : 0 ≤ ∫ c, H c * q c :=
    integral_nonneg fun c => mul_nonneg (hH0 c) (baseHeightKernel_nonneg _)
  have hIle : (∫ c, H c * q c) ≤ ∫ c, q c := by
    apply integral_mono hprodint hqint
    intro c
    calc
      H c * q c ≤ 1 * q c := by
        exact mul_le_mul_of_nonneg_right (hH1 c) (baseHeightKernel_nonneg _)
      _ = q c := one_mul _
  constructor
  · exact mul_nonneg hscale hI0
  · have hq : ∫ c, q c = baseHeightKernelMass / R :=
      integral_baseHeightKernel_scaled_sub hR x
    calc
      (R / baseHeightKernelMass) *
          (∫ c, H c * baseHeightKernel (R * (x - c))) =
          (R / baseHeightKernelMass) * (∫ c, H c * q c) := by rfl
      _ ≤ (R / baseHeightKernelMass) * ∫ c, q c := by gcongr
      _ = 1 := by
        rw [hq, div_eq_mul_inv]
        calc
          R * baseHeightKernelMass⁻¹ * (baseHeightKernelMass * R⁻¹) =
              (baseHeightKernelMass⁻¹ * baseHeightKernelMass) *
                (R * R⁻¹) := by ring
          _ = 1 := by
            rw [inv_mul_cancel₀ hM.ne', mul_inv_cancel₀ hR.ne', one_mul]

theorem averagedHeightWeightOf_tendsto
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    (hH0 : ∀ x, 0 ≤ H x) (hH1 : ∀ x, H x ≤ 1) (x : ℝ) :
    Tendsto (fun R : ℝ => averagedHeightWeightOf H R x) atTop (𝓝 (H x)) := by
  let F : ℝ → ℝ → ℝ := fun R y => H (x - y / R) * baseHeightKernel y
  let f : ℝ → ℝ := fun y => H x * baseHeightKernel y
  have hFmeas : ∀ᶠ R : ℝ in atTop, AEStronglyMeasurable (F R) := by
    filter_upwards [] with R
    exact ((hH.comp (by fun_prop)).mul baseHeightKernel_continuous).aestronglyMeasurable
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ᵐ y : ℝ,
      ‖F R y‖ ≤ baseHeightKernel y := by
    filter_upwards [] with R
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hH0 _) (baseHeightKernel_nonneg y))]
    calc
      H (x - y / R) * baseHeightKernel y ≤ 1 * baseHeightKernel y :=
        mul_le_mul_of_nonneg_right (hH1 _) (baseHeightKernel_nonneg y)
      _ = baseHeightKernel y := one_mul _
  have hpoint : ∀ᵐ y : ℝ, Tendsto (fun R : ℝ => F R y) atTop (𝓝 (f y)) := by
    filter_upwards [] with y
    have hy : Tendsto (fun R : ℝ => y / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hx : Tendsto (fun R : ℝ => x - y / R) atTop (𝓝 x) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hy
    have hHL : Tendsto (fun R : ℝ => H (x - y / R)) atTop (𝓝 (H x)) :=
      hH.continuousAt.tendsto.comp hx
    exact hHL.mul tendsto_const_nhds
  have hlim := tendsto_integral_filter_of_dominated_convergence
    baseHeightKernel hFmeas hbound baseHeightKernel_integrable hpoint
  have hscaled : Tendsto (fun R : ℝ => baseHeightKernelMass⁻¹ * ∫ y, F R y)
      atTop (𝓝 (H x)) := by
    have hmul := (show Tendsto (fun _ : ℝ => baseHeightKernelMass⁻¹) atTop
      (𝓝 baseHeightKernelMass⁻¹) from tendsto_const_nhds).mul hlim
    have hfintegral : ∫ y, f y = H x * baseHeightKernelMass := by
      unfold f
      rw [integral_const_mul, integral_baseHeightKernel]
    rw [hfintegral] at hmul
    have hcancel : baseHeightKernelMass⁻¹ * (H x * baseHeightKernelMass) = H x := by
      calc
        baseHeightKernelMass⁻¹ * (H x * baseHeightKernelMass) =
            H x * (baseHeightKernelMass⁻¹ * baseHeightKernelMass) := by ring
        _ = H x := by rw [inv_mul_cancel₀ baseHeightKernelMass_pos.ne', mul_one]
    rw [hcancel] at hmul
    exact hmul
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [averagedHeightWeightOf_eq_kernelIntegral hH hHc hR]

end RH.Zeta85.RSPoissonCyclicBridge
