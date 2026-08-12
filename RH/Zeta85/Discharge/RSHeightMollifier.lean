import RH.Zeta85.Discharge.RSLogFullTraceDegrees

/-!
# Height mollifier bridge for the Rudnick--Sarnak tuple sum

The RS input evaluates the Fourier transform of each physical-space height
test at the complex ordinate `gammaOf rho / T`.  This file begins the passage
to a real-axis height mollifier by controlling the vertical displacement
uniformly from compact support.  The bound is linear in that displacement,
which becomes `O(1 / T)` for zeros in the critical strip.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

/-- A compactly supported physical-space height test has a Fourier transform
that is Lipschitz in a small vertical strip.  The constant is explicit in the
support radius and the `L1` mass of the test. -/
theorem norm_paperFT_vertical_sub_le
    {g : ℝ → ℂ} {Λ : ℝ} (hg : Continuous g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    {x y : ℝ} (hsmall : |y| * Λ ≤ 1) :
    ‖paperFT g ((x : ℂ) + (y : ℂ) * I) - paperFT g (x : ℂ)‖ ≤
      2 * |y| * Λ * ∫ u, ‖g u‖ := by
  by_cases hgzero : g = 0
  · subst g
    simp [paperFT_def]
  have hΛ : 0 ≤ Λ := by
    by_contra hΛ
    have hneg : Λ < 0 := lt_of_not_ge hΛ
    have hzero : g = 0 := by
      funext u
      by_contra hu
      have := hsupp u hu
      linarith [abs_nonneg u]
    exact hgzero hzero
  have hcs : HasCompactSupport g :=
    Zeta23.hasCompactSupport_of_support_subset_abs hsupp
  have hzcont : Continuous (fun u : ℝ =>
      g u * cexp (I * ((x : ℂ) + (y : ℂ) * I) * (u : ℂ))) := by
    fun_prop
  have hxcont : Continuous (fun u : ℝ =>
      g u * cexp (I * (x : ℂ) * (u : ℂ))) := by
    fun_prop
  have hzint : Integrable (fun u : ℝ =>
      g u * cexp (I * ((x : ℂ) + (y : ℂ) * I) * (u : ℂ))) :=
    hzcont.integrable_of_hasCompactSupport hcs.mul_right
  have hxint : Integrable (fun u : ℝ =>
      g u * cexp (I * (x : ℂ) * (u : ℂ))) :=
    hxcont.integrable_of_hasCompactSupport hcs.mul_right
  rw [paperFT_def, paperFT_def, ← integral_sub hzint hxint]
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le
    ((hg.integrable_of_hasCompactSupport hcs).norm.const_mul (2 * |y| * Λ))
    (Eventually.of_forall fun u => ?_)
  by_cases hu : g u = 0
  · simp [hu]
  have huΛ := hsupp u hu
  have hyu : ‖((-(y * u) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left huΛ (abs_nonneg y)) hsmall
  have hexp :
      cexp (I * ((x : ℂ) + (y : ℂ) * I) * (u : ℂ)) =
        cexp (I * (x : ℂ) * (u : ℂ)) * cexp ((-(y * u) : ℝ) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    calc
      I * ((x : ℂ) + (y : ℂ) * I) * (u : ℂ) =
          I * (x : ℂ) * (u : ℂ) + I ^ 2 * ((y : ℂ) * (u : ℂ)) := by
        ring
      _ = I * (x : ℂ) * (u : ℂ) + -((y : ℂ) * (u : ℂ)) := by
        rw [I_sq]
        ring
  rw [hexp]
  have hunit : ‖cexp (I * (x : ℂ) * (u : ℂ))‖ = 1 := by
    rw [Zeta23.norm_cexp_I_mul]
    simp
  have hdiff := Complex.norm_exp_sub_one_le hyu
  rw [show g u *
      (cexp (I * (x : ℂ) * (u : ℂ)) * cexp ((-(y * u) : ℝ) : ℂ)) -
        g u * cexp (I * (x : ℂ) * (u : ℂ)) =
      (g u * cexp (I * (x : ℂ) * (u : ℂ))) *
        (cexp ((-(y * u) : ℝ) : ℂ) - 1) by ring]
  rw [norm_mul, norm_mul, hunit, mul_one]
  calc
    ‖g u‖ * ‖cexp ((-(y * u) : ℝ) : ℂ) - 1‖
        ≤ ‖g u‖ * (2 * ‖((-(y * u) : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
    _ = 2 * |y| * |u| * ‖g u‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul]
      ring
    _ ≤ (2 * |y| * Λ) * ‖g u‖ := by
      gcongr

/-- For a zero in the critical strip, replacing its complex normalized
ordinate by the real normalized height costs at most `Λ / T` times the `L1`
mass of the physical-space test. -/
theorem norm_paperFT_zero_height_sub_real_le
    {Z : ZeroConfig} {g : ℝ → ℂ} {Λ T : ℝ}
    (hg : Continuous g) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hT : 0 < T) (hΛT : Λ ≤ 2 * T) (rho : Z.carrier) :
    ‖paperFT g (gammaOf (rho : ℂ) / T) -
        paperFT g (((rho : ℂ).im / T : ℝ) : ℂ)‖ ≤
      (Λ / T) * ∫ u, ‖g u‖ := by
  by_cases hgzero : g = 0
  · subst g
    simp [paperFT_def]
  have hΛ : 0 ≤ Λ := by
    by_contra hΛ
    have hneg : Λ < 0 := lt_of_not_ge hΛ
    have hzero : g = 0 := by
      funext u
      by_contra hu
      have := hsupp u hu
      linarith [abs_nonneg u]
    exact hgzero hzero
  have hstrip : 0 ≤ (rho : ℂ).re ∧ (rho : ℂ).re ≤ 1 :=
    Z.strip (rho : ℂ) rho.property
  have him : |(gammaOf (rho : ℂ)).im| ≤ 1 / 2 := by
    have hgamma : (gammaOf (rho : ℂ)).im = 1 / 2 - (rho : ℂ).re := by
      simp [gammaOf, Complex.div_I]
    rw [hgamma, abs_le]
    constructor <;> linarith
  have harg : gammaOf (rho : ℂ) / T =
      (((rho : ℂ).im / T : ℝ) : ℂ) +
        (((gammaOf (rho : ℂ)).im / T : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [gammaOf, Complex.div_I]
    · simp [gammaOf, Complex.div_I]
  have hy : |(gammaOf (rho : ℂ)).im / T| ≤ 1 / (2 * T) := by
    rw [abs_div, abs_of_pos hT]
    calc
      |(gammaOf (rho : ℂ)).im| / T ≤ (1 / 2) / T :=
        div_le_div_of_nonneg_right him (le_of_lt hT)
      _ = 1 / (2 * T) := by ring
  have hsmall : |(gammaOf (rho : ℂ)).im / T| * Λ ≤ 1 := by
    calc
      |(gammaOf (rho : ℂ)).im / T| * Λ ≤ (1 / (2 * T)) * Λ := by
        gcongr
      _ ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one (by positivity)]
        linarith
  rw [harg]
  have hvertical := norm_paperFT_vertical_sub_le hg hsupp
    (x := (rho : ℂ).im / T) (y := (gammaOf (rho : ℂ)).im / T) hsmall
  refine hvertical.trans ?_
  have hmass : 0 ≤ ∫ u, ‖g u‖ := integral_nonneg fun _ => norm_nonneg _
  apply mul_le_mul_of_nonneg_right _ hmass
  calc
    2 * |(gammaOf (rho : ℂ)).im / T| * Λ ≤
        2 * (1 / (2 * T)) * Λ := by
      gcongr
    _ = Λ / T := by field_simp

/-! ## An admissible nonnegative real-axis height weight -/

/-- Smoothness of autocorrelation, obtained from smooth convolution. -/
theorem autocorr_contDiff_top
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hv : ContDiff ℝ ∞ v) (hcompact : HasCompactSupport v) :
    ContDiff ℝ ∞ (Zeta23.Params.autocorr v) := by
  let V : ℝ → ℂ := fun u => (v u : ℂ)
  have hVC : ContDiff ℝ ∞ V := by
    convert Complex.ofRealCLM.contDiff.comp hv using 1
    funext u
    rfl
  have hVcompact : HasCompactSupport V :=
    hcompact.comp_left Complex.ofReal_zero
  have hVloc : LocallyIntegrable V volume :=
    hVC.continuous.integrable_of_hasCompactSupport hVcompact |>.locallyIntegrable
  have heq : (fun y => (Zeta23.Params.autocorr v y : ℂ)) =
      (V ⋆[ContinuousLinearMap.mul ℝ ℂ] V) := by
    rw [Zeta23.Taper.ofReal_autocorr_eq_convolution heven]
    ext y
    simp only [convolution_def, V, ContinuousLinearMap.mul_apply']
  have hconv : ContDiff ℝ ∞
      (V ⋆[ContinuousLinearMap.mul ℝ ℂ] V) :=
    hVcompact.contDiff_convolution_left
      (ContinuousLinearMap.mul ℝ ℂ) hVC hVloc
  rw [← heq] at hconv
  have hre := Complex.reCLM.contDiff.comp hconv
  convert hre using 1
  funext u
  rfl

/-- Compact support of autocorrelation. -/
theorem autocorr_hasCompactSupport
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hcompact : HasCompactSupport v) :
    HasCompactSupport (Zeta23.Params.autocorr v) := by
  let V : ℝ → ℂ := fun u => (v u : ℂ)
  have hVcompact : HasCompactSupport V :=
    hcompact.comp_left Complex.ofReal_zero
  have hconv : HasCompactSupport
      (V ⋆[ContinuousLinearMap.mul ℂ ℂ] V) :=
    hVcompact.convolution (ContinuousLinearMap.mul ℂ ℂ) hVcompact
  rw [← Zeta23.Taper.ofReal_autocorr_eq_convolution heven] at hconv
  have hre := hconv.comp_left (show Complex.re (0 : ℂ) = 0 by simp)
  convert hre using 1
  funext u
  rfl

/-- The normalized autocorrelation, modulated to a chosen center height.
Its Fourier transform is a normalized square on the real axis. -/
def autocorrHeightTest (v : ℝ → ℝ) (c u : ℝ) : ℂ :=
  ((Zeta23.Params.autocorr v u / (∫ x, v x) ^ 2 : ℝ) : ℂ) *
    cexp (-I * (c : ℂ) * (u : ℂ))

theorem autocorrHeightTest_contDiff
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hv : ContDiff ℝ ∞ v) (hcompact : HasCompactSupport v) (c : ℝ) :
    ContDiff ℝ ∞ (autocorrHeightTest v c) := by
  unfold autocorrHeightTest
  have hA := autocorr_contDiff_top heven hv hcompact
  have hAdiv : ContDiff ℝ ∞ (fun u =>
      Zeta23.Params.autocorr v u / (∫ x, v x) ^ 2) :=
    hA.div_const _
  have hAcomplex : ContDiff ℝ ∞ (fun u =>
      ((Zeta23.Params.autocorr v u / (∫ x, v x) ^ 2 : ℝ) : ℂ)) := by
    convert Complex.ofRealCLM.contDiff.comp hAdiv using 1
    funext u
    rfl
  have huC : ContDiff ℝ ∞ (fun u : ℝ => (u : ℂ)) := by
    convert (Complex.ofRealCLM.contDiff : ContDiff ℝ ∞
      (Complex.ofRealCLM : ℝ → ℂ)) using 1
    funext u
    rfl
  have harg : ContDiff ℝ ∞ (fun u : ℝ => -I * (c : ℂ) * (u : ℂ)) :=
    (contDiff_const.mul huC)
  exact hAcomplex.mul harg.cexp

theorem autocorrHeightTest_hasCompactSupport
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hcompact : HasCompactSupport v) (c : ℝ) :
    HasCompactSupport (autocorrHeightTest v c) := by
  unfold autocorrHeightTest
  have hA := autocorr_hasCompactSupport heven hcompact
  have hscaled : HasCompactSupport (fun u =>
      ((Zeta23.Params.autocorr v u / (∫ x, v x) ^ 2 : ℝ) : ℂ)) :=
    hA.comp_left (g := fun a : ℝ => ((a / (∫ x, v x) ^ 2 : ℝ) : ℂ)) (by simp)
  exact hscaled.mul_right

/-- Exact complex-frequency transform of the normalized autocorrelation
height test. -/
theorem paperFT_autocorrHeightTest
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hv : Continuous v) (hcompact : HasCompactSupport v)
    (c : ℝ) (z : ℂ) :
    paperFT (autocorrHeightTest v c) z =
      (((∫ x, v x) ^ 2 : ℝ) : ℂ)⁻¹ *
        paperFT (fun u => (v u : ℂ)) (z - c) ^ 2 := by
  rw [paperFT_def]
  have hintegrand : (fun u : ℝ =>
      autocorrHeightTest v c u * cexp (I * z * (u : ℂ))) =
      fun u => (((∫ x, v x) ^ 2 : ℝ) : ℂ)⁻¹ *
        ((Zeta23.Params.autocorr v u : ℂ) *
          cexp (I * (z - c) * (u : ℂ))) := by
    funext u
    unfold autocorrHeightTest
    push_cast
    have hexp : cexp (-I * (c : ℂ) * (u : ℂ)) *
        cexp (I * z * (u : ℂ)) = cexp (I * (z - c) * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [mul_assoc, hexp]
    ring
  rw [hintegrand, integral_const_mul_C, ← paperFT_def,
    RH.Zeta85.RSReduction.paperFT_autocorr_complex heven hv hcompact]

theorem paperFT_autocorrHeightTest_real_formula
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hv : Continuous v) (hcompact : HasCompactSupport v)
    (c x : ℝ) :
    paperFT (autocorrHeightTest v c) (x : ℂ) =
      (((((∫ u, v u) ^ 2)⁻¹) *
        (paperFT (fun u => (v u : ℂ)) (x - c : ℝ)).re ^ 2 : ℝ) : ℂ) := by
  rw [paperFT_autocorrHeightTest heven hv hcompact]
  have harg : (x : ℂ) - (c : ℂ) = ((x - c : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [harg, Zeta23.Taper.paperFT_ofReal_eq_re heven]
  simp only [Complex.ofReal_re]
  push_cast
  rfl

theorem norm_paperFT_of_nonneg_real_le_mass
    {v : ℝ → ℝ} (hnonneg : ∀ u, 0 ≤ v u) (x : ℝ) :
    ‖paperFT (fun u => (v u : ℂ)) (x : ℂ)‖ ≤ ∫ u, v u := by
  rw [paperFT_def]
  calc
    ‖∫ u : ℝ, (v u : ℂ) * cexp (I * (x : ℂ) * (u : ℂ))‖
        ≤ ∫ u : ℝ, ‖(v u : ℂ) * cexp (I * (x : ℂ) * (u : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, v u := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [norm_mul, Zeta23.norm_cexp_I_mul]
      simp [abs_of_nonneg (hnonneg u)]

/-- The real-axis height weight lies in `[0,1]`, so it can be compared
directly with an unweighted zero count after the remote-height leakage is
removed. -/
theorem autocorrHeightTest_real_mem_Icc
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hv : Continuous v) (hcompact : HasCompactSupport v)
    (hnonneg : ∀ u, 0 ≤ v u) (hm : 0 < ∫ u, v u)
    (c x : ℝ) :
    (paperFT (autocorrHeightTest v c) (x : ℂ)).re ∈ Set.Icc 0 1 := by
  rw [paperFT_autocorrHeightTest_real_formula heven hv hcompact]
  simp only [Complex.ofReal_re]
  constructor
  · positivity
  · have hreal := Zeta23.Taper.paperFT_ofReal_eq_re heven (x - c)
    have hnorm := norm_paperFT_of_nonneg_real_le_mass hnonneg (x - c)
    rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hnorm
    have habs := abs_le.mp hnorm
    have hsq : (paperFT (fun u => (v u : ℂ)) (x - c : ℝ)).re ^ 2 ≤
        (∫ u, v u) ^ 2 := by
      nlinarith
    calc
      ((∫ u, v u) ^ 2)⁻¹ *
          (paperFT (fun u => (v u : ℂ)) (x - c : ℝ)).re ^ 2
          ≤ ((∫ u, v u) ^ 2)⁻¹ * (∫ u, v u) ^ 2 := by
            gcongr
      _ = 1 := by field_simp

theorem autocorrHeightTest_real
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hv : Continuous v) (hcompact : HasCompactSupport v)
    (c x : ℝ) :
    paperFT (autocorrHeightTest v c) (x : ℂ) =
      ((paperFT (autocorrHeightTest v c) (x : ℂ)).re : ℂ) := by
  refine (Complex.conj_eq_iff_re.mp ?_).symm
  rw [paperFT_autocorrHeightTest heven hv hcompact]
  have harg : (x : ℂ) - (c : ℂ) = ((x - c : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [harg, Zeta23.Taper.paperFT_ofReal_eq_re heven]
  simp

end RH.Zeta85.RSPoissonCyclicBridge
