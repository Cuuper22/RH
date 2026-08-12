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
open scoped ComplexConjugate

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

end RH.Zeta85.RSPoissonCyclicBridge
