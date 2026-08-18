import RH.Zeta85.Discharge.RSHeightMollifier

/-!
# A concrete concentrating height mollifier

This module instantiates the autocorrelation height test with a fixed smooth
nonnegative bump and then widens its physical support by `R`.  The resulting
real-axis Fourier weight is bounded by one, concentrates at the chosen center,
has fourth-power remote decay, and has an exact `L1` normalization.  For zeta
zeros its complex-to-real ordinate error is therefore exactly bounded by
`R / T`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

/-- A fixed smooth, even, nonnegative bump supported in `[-1/2,1/2]`. -/
def baseHeightBump : ℝ → ℝ :=
  RH.Zeta85.RSReduction.smoothTopHat 1 (1 / 4)

theorem baseHeightBump_contDiff : ContDiff ℝ ∞ baseHeightBump := by
  exact RH.Zeta85.RSReduction.smoothTopHat_contDiff (by norm_num) (by norm_num)

theorem baseHeightBump_hasCompactSupport : HasCompactSupport baseHeightBump := by
  exact RH.Zeta85.RSReduction.smoothTopHat_hasCompactSupport (by norm_num)

theorem baseHeightBump_even (u : ℝ) : baseHeightBump (-u) = baseHeightBump u := by
  unfold baseHeightBump RH.Zeta85.RSReduction.smoothTopHat
  rw [Zeta23.Taper.phi_even]

theorem baseHeightBump_nonneg (u : ℝ) : 0 ≤ baseHeightBump u := by
  exact RH.Zeta85.RSReduction.smoothTopHat_nonneg (by norm_num)

theorem baseHeightBump_zero : baseHeightBump 0 = 1 := by
  rw [baseHeightBump]
  rw [RH.Zeta85.RSReduction.smoothTopHat_eq_topHat_of_inner
    (by norm_num) (by norm_num) (by norm_num)]
  simp [RH.Zeta85.TopHatMoments.topHat,
    RH.Zeta85.TopHatMoments.topHatSupport]

theorem baseHeightBump_integral_pos : 0 < ∫ u, baseHeightBump u := by
  apply baseHeightBump_contDiff.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    baseHeightBump_hasCompactSupport baseHeightBump_nonneg
  exact baseHeightBump_zero.trans_ne one_ne_zero

theorem baseHeightBump_eq_zero_of_outer {u : ℝ} (hu : 1 / 2 ≤ |u|) :
    baseHeightBump u = 0 := by
  exact RH.Zeta85.RSReduction.smoothTopHat_eq_zero_of_outer (by norm_num) hu

/-- Widen the physical bump by `R`; its Fourier transform contracts by the
reciprocal factor. -/
def dilatedHeightBump (R u : ℝ) : ℝ := baseHeightBump (u / R)

theorem dilatedHeightBump_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (dilatedHeightBump R) := by
  unfold dilatedHeightBump
  exact baseHeightBump_contDiff.comp (contDiff_id.div_const R)

theorem dilatedHeightBump_hasCompactSupport {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (dilatedHeightBump R) := by
  have h := baseHeightBump_hasCompactSupport.comp_smul (inv_ne_zero hR)
  change HasCompactSupport (fun u => baseHeightBump (u / R))
  simpa only [smul_eq_mul, inv_mul_eq_div] using h

theorem dilatedHeightBump_even (R u : ℝ) :
    dilatedHeightBump R (-u) = dilatedHeightBump R u := by
  unfold dilatedHeightBump
  rw [neg_div, baseHeightBump_even]

theorem dilatedHeightBump_nonneg (R u : ℝ) :
    0 ≤ dilatedHeightBump R u := baseHeightBump_nonneg _

theorem integral_dilatedHeightBump {R : ℝ} (hR : 0 < R) :
    ∫ u, dilatedHeightBump R u = R * ∫ u, baseHeightBump u := by
  have h := Measure.integral_comp_mul_left baseHeightBump R⁻¹
  rw [inv_inv, abs_of_pos hR] at h
  change (∫ u, baseHeightBump (u / R)) = _
  simpa only [div_eq_inv_mul, smul_eq_mul] using h

theorem dilatedHeightBump_integral_pos {R : ℝ} (hR : 0 < R) :
    0 < ∫ u, dilatedHeightBump R u := by
  rw [integral_dilatedHeightBump hR]
  exact mul_pos hR baseHeightBump_integral_pos

theorem dilatedHeightBump_eq_zero_of_outer {R u : ℝ} (hR : 0 < R)
    (hu : R / 2 ≤ |u|) : dilatedHeightBump R u = 0 := by
  apply baseHeightBump_eq_zero_of_outer
  rw [abs_div, abs_of_pos hR]
  rw [le_div_iff₀ hR]
  linarith

theorem paperFT_dilatedHeightBump {R : ℝ} (hR : 0 < R) (z : ℂ) :
    paperFT (fun u => (dilatedHeightBump R u : ℂ)) z =
      (R : ℂ) * paperFT (fun u => (baseHeightBump u : ℂ)) ((R : ℂ) * z) := by
  let f : ℝ → ℂ := fun u =>
    (baseHeightBump u : ℂ) * cexp (I * ((R : ℂ) * z) * (u : ℂ))
  have hchange := Measure.integral_comp_mul_left f R⁻¹
  rw [inv_inv, abs_of_pos hR] at hchange
  unfold paperFT
  calc
    (∫ u : ℝ, (dilatedHeightBump R u : ℂ) * cexp (I * z * (u : ℂ))) =
        ∫ u : ℝ, f (R⁻¹ * u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [f, dilatedHeightBump]
      congr 1
      · congr 1
        field_simp
      · congr 1
        push_cast
        field_simp [hR.ne']
    _ = R • ∫ u : ℝ, f u := hchange
    _ = (R : ℂ) * ∫ u : ℝ, f u := by rw [Complex.real_smul]
    _ = (R : ℂ) * ∫ u : ℝ,
        (baseHeightBump u : ℂ) * cexp (I * ((R : ℂ) * z) * (u : ℂ)) := by
      rfl

/-- The normalized autocorrelation test has physical support radius `R`. -/
theorem autocorrHeightTest_dilated_support {R c u : ℝ} (hR : 0 < R)
    (hu : R ≤ |u|) :
    autocorrHeightTest (dilatedHeightBump R) c u = 0 := by
  unfold autocorrHeightTest
  rw [Zeta23.Taper.autocorr_eq_zero_of_support
    (dilatedHeightBump R) (M := R / 2)
    (fun x hx => dilatedHeightBump_eq_zero_of_outer hR hx) (by linarith),
    zero_div, Complex.ofReal_zero, zero_mul]

/-- Exact cancellation of the dilation factors in the real-axis height
weight. -/
theorem paperFT_dilated_autocorrHeightTest_real_formula
    {R : ℝ} (hR : 0 < R) (c x : ℝ) :
    paperFT (autocorrHeightTest (dilatedHeightBump R) c) (x : ℂ) =
      (((((∫ u, baseHeightBump u) ^ 2)⁻¹) *
        (paperFT (fun u => (baseHeightBump u : ℂ))
          ((R * (x - c) : ℝ) : ℂ)).re ^ 2 : ℝ) : ℂ) := by
  rw [paperFT_autocorrHeightTest_real_formula
    (dilatedHeightBump_even R)
    (dilatedHeightBump_contDiff R).continuous
    (dilatedHeightBump_hasCompactSupport hR.ne')]
  rw [integral_dilatedHeightBump hR,
    paperFT_dilatedHeightBump hR]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have harg : (R : ℂ) * ((x - c : ℝ) : ℂ) =
      ((R * (x - c) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [harg]
  push_cast
  field_simp [hR.ne']

/-- Fourth-power horizontal decay of the concentrating real-axis weight. -/
theorem dilatedHeightWeight_mul_four_le {R : ℝ} (hR : 0 < R) (c x : ℝ) :
    (paperFT (autocorrHeightTest (dilatedHeightBump R) c) (x : ℂ)).re *
        (R * |x - c|) ^ 4 ≤
      ((∫ u, baseHeightBump u) ^ 2)⁻¹ *
        (∫ u, ‖deriv (deriv (fun t => (baseHeightBump t : ℂ))) u‖) ^ 2 := by
  rw [paperFT_dilated_autocorrHeightTest_real_formula hR]
  simp only [Complex.ofReal_re]
  have hsupport : ∀ u, (baseHeightBump u : ℂ) ≠ 0 → |u| ≤ (1 : ℝ) / 2 := by
    intro u hu
    by_contra hout
    have houter : (1 : ℝ) / 2 ≤ |u| := le_of_not_ge hout
    have hz := baseHeightBump_eq_zero_of_outer houter
    exact hu (by simp [hz])
  have hC2 : ContDiff ℝ 2 (fun u => (baseHeightBump u : ℂ)) := by
    have hreal : ContDiff ℝ 2 baseHeightBump :=
      baseHeightBump_contDiff.of_le
        (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
          change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
    convert Complex.ofRealCLM.contDiff.comp hreal using 1
    funext u
    rfl
  have hdecay := Zeta23.norm_paperFT_mul_sq_le
    hC2 hsupport (((R * (x - c) : ℝ) : ℂ))
  have hnormz : ‖(((R * (x - c) : ℝ) : ℂ))‖ = R * |x - c| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hR]
  rw [hnormz] at hdecay
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] at hdecay
  let a : ℝ := (paperFT (fun u => (baseHeightBump u : ℂ))
    ((R * (x - c) : ℝ) : ℂ)).re
  let A : ℝ := ‖paperFT (fun u => (baseHeightBump u : ℂ))
    ((R * (x - c) : ℝ) : ℂ)‖
  let q : ℝ := R * |x - c|
  let C : ℝ := ∫ u, ‖deriv (deriv (fun t => (baseHeightBump t : ℂ))) u‖
  have ha : |a| ≤ A := Complex.abs_re_le_norm _
  have hA : 0 ≤ A := norm_nonneg _
  have hq : 0 ≤ q := mul_nonneg hR.le (abs_nonneg _)
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hdecay' : A * q ^ 2 ≤ C := by
    simpa only [A, q, C] using hdecay
  have hasq : a ^ 2 ≤ A ^ 2 :=
    sq_le_sq' (abs_le.mp ha).1 (abs_le.mp ha).2
  have hprod : A ^ 2 * q ^ 4 ≤ C ^ 2 := by
    have hsquared : (A * q ^ 2) ^ 2 ≤ C ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hA (sq_nonneg q)) hC).2 hdecay'
    calc
      A ^ 2 * q ^ 4 = (A * q ^ 2) ^ 2 := by ring
      _ ≤ C ^ 2 := hsquared
  have hcore : a ^ 2 * q ^ 4 ≤ C ^ 2 := by
    calc
      a ^ 2 * q ^ 4 ≤ A ^ 2 * q ^ 4 := by gcongr
      _ ≤ C ^ 2 := hprod
  have hmass : 0 < ∫ u, baseHeightBump u := baseHeightBump_integral_pos
  calc
    ((∫ u, baseHeightBump u) ^ 2)⁻¹ * a ^ 2 * q ^ 4 =
        ((∫ u, baseHeightBump u) ^ 2)⁻¹ * (a ^ 2 * q ^ 4) := by ring
    _ ≤ ((∫ u, baseHeightBump u) ^ 2)⁻¹ * C ^ 2 := by gcongr

theorem autocorr_nonneg_of_nonneg {v : ℝ → ℝ} (hv : ∀ u, 0 ≤ v u) (y : ℝ) :
    0 ≤ Zeta23.Params.autocorr v y := by
  unfold Zeta23.Params.autocorr
  exact integral_nonneg fun u => mul_nonneg (hv u) (hv (u + y))

theorem integral_autocorr_eq_sq
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hv : Continuous v) (hcompact : HasCompactSupport v) :
    ∫ y, Zeta23.Params.autocorr v y = (∫ u, v u) ^ 2 := by
  have h := RH.Zeta85.RSReduction.paperFT_autocorr_complex
    heven hv hcompact 0
  simp only [paperFT_def, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h
  rw [Zeta23.integral_ofReal_C, Zeta23.integral_ofReal_C] at h
  exact_mod_cast h

/-- The normalized physical-space height test has exact `L1` mass one. -/
theorem integral_norm_autocorrHeightTest_eq_one
    {v : ℝ → ℝ} (heven : ∀ u, v (-u) = v u)
    (hv : Continuous v) (hcompact : HasCompactSupport v)
    (hnonneg : ∀ u, 0 ≤ v u) (hm : 0 < ∫ u, v u) (c : ℝ) :
    ∫ u, ‖autocorrHeightTest v c u‖ = 1 := by
  have hA : ∀ u, 0 ≤ Zeta23.Params.autocorr v u :=
    autocorr_nonneg_of_nonneg hnonneg
  have hm2 : 0 < (∫ u, v u) ^ 2 := sq_pos_of_pos hm
  calc
    (∫ u, ‖autocorrHeightTest v c u‖) =
        ∫ u, Zeta23.Params.autocorr v u / (∫ x, v x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold autocorrHeightTest
      have hexp : ‖cexp (-I * (c : ℂ) * (u : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re]
      rw [norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (div_nonneg (hA u) hm2.le)]
    _ = (∫ u, Zeta23.Params.autocorr v u) / (∫ x, v x) ^ 2 := by
      rw [integral_div]
    _ = 1 := by
      rw [integral_autocorr_eq_sq heven hv hcompact]
      field_simp

/-- The concrete complex-to-real zero-height error has no hidden mass
constant: it is at most `R / T`. -/
theorem norm_paperFT_dilated_height_zero_sub_real_le
    {Z : ZeroConfig} {R T c : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hRT : R ≤ 2 * T) (rho : Z.carrier) :
    ‖paperFT (autocorrHeightTest (dilatedHeightBump R) c)
          (gammaOf (rho : ℂ) / T) -
        paperFT (autocorrHeightTest (dilatedHeightBump R) c)
          (((rho : ℂ).im / T : ℝ) : ℂ)‖ ≤ R / T := by
  have hgcont : Continuous (autocorrHeightTest (dilatedHeightBump R) c) :=
    (autocorrHeightTest_contDiff (dilatedHeightBump_even R)
      (dilatedHeightBump_contDiff R)
      (dilatedHeightBump_hasCompactSupport hR.ne') c).continuous
  have hgsupp : ∀ u,
      autocorrHeightTest (dilatedHeightBump R) c u ≠ 0 → |u| ≤ R := by
    intro u hu
    by_contra hout
    exact hu (autocorrHeightTest_dilated_support hR (le_of_not_ge hout))
  have hbound := norm_paperFT_zero_height_sub_real_le
    hgcont hgsupp hT hRT rho
  rw [integral_norm_autocorrHeightTest_eq_one
    (dilatedHeightBump_even R)
    (dilatedHeightBump_contDiff R).continuous
    (dilatedHeightBump_hasCompactSupport hR.ne')
    (dilatedHeightBump_nonneg R)
    (dilatedHeightBump_integral_pos hR) c, mul_one] at hbound
  exact hbound

end RH.Zeta85.RSPoissonCyclicBridge
