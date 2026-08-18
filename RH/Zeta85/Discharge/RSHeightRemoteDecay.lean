import RH.Zeta85.Discharge.RSHeightRemoteMajorant

/-!
# Fourth-order decay of the averaged dyadic height selector

The autocorrelation packet has an exact dilation formula at complex
frequencies.  Applying the second-derivative Fourier bound before averaging
over the dyadic center gives a scale-sharp fourth-order estimate away from
`[1,2]`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def baseHeightBumpDerivTwoMass : ℝ :=
  ∫ u, ‖deriv (deriv (fun t => (baseHeightBump t : ℂ))) u‖

def baseHeightRemoteDecayConstant : ℝ :=
  ((∫ u, baseHeightBump u) ^ 2)⁻¹ *
    (Real.exp (1 / 2) * baseHeightBumpDerivTwoMass) ^ 2

theorem baseHeightBumpDerivTwoMass_nonneg :
    0 ≤ baseHeightBumpDerivTwoMass := by
  unfold baseHeightBumpDerivTwoMass
  exact integral_nonneg fun _ => norm_nonneg _

theorem baseHeightRemoteDecayConstant_nonneg :
    0 ≤ baseHeightRemoteDecayConstant := by
  unfold baseHeightRemoteDecayConstant
  positivity

theorem paperFT_dilated_autocorrHeightTest_complex
    {R : ℝ} (hR : 0 < R) (z : ℂ) :
    paperFT (autocorrHeightTest (dilatedHeightBump R) 0) z =
      ((((∫ u, baseHeightBump u) ^ 2)⁻¹ : ℝ) : ℂ) *
        paperFT (fun u => (baseHeightBump u : ℂ)) ((R : ℂ) * z) ^ 2 := by
  rw [paperFT_autocorrHeightTest
    (dilatedHeightBump_even R)
    (dilatedHeightBump_contDiff R).continuous
    (dilatedHeightBump_hasCompactSupport hR.ne')]
  rw [integral_dilatedHeightBump hR,
    paperFT_dilatedHeightBump hR]
  have hm : (∫ u, baseHeightBump u) ≠ 0 := baseHeightBump_integral_pos.ne'
  push_cast
  field_simp [hR.ne', hm]
  simp

theorem norm_baseHeightBump_paperFT_mul_sq_le (z : ℂ) :
    ‖paperFT (fun u => (baseHeightBump u : ℂ)) z‖ * ‖z‖ ^ 2 ≤
      Real.exp (|z.im| / 2) * baseHeightBumpDerivTwoMass := by
  have hC2 : ContDiff ℝ 2 (fun u => (baseHeightBump u : ℂ)) := by
    have hreal : ContDiff ℝ 2 baseHeightBump :=
      baseHeightBump_contDiff.of_le
        (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
          change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
    convert Complex.ofRealCLM.contDiff.comp
      hreal using 1
    funext u
    rfl
  have hsupp : ∀ u, (baseHeightBump u : ℂ) ≠ 0 → |u| ≤ (1 : ℝ) / 2 := by
    intro u hu
    by_contra hout
    have hz := baseHeightBump_eq_zero_of_outer (le_of_not_ge hout)
    exact hu (by simp [hz])
  have h := Zeta23.norm_paperFT_mul_sq_le hC2 hsupp z
  simpa only [baseHeightBumpDerivTwoMass, div_eq_mul_inv, one_mul] using h

theorem norm_paperFT_dilated_autocorr_mul_four_le
    {R : ℝ} (hR : 0 < R) (z : ℂ) (him : |((R : ℂ) * z).im| ≤ 1) :
    ‖paperFT (autocorrHeightTest (dilatedHeightBump R) 0) z‖ *
        ‖(R : ℂ) * z‖ ^ 4 ≤ baseHeightRemoteDecayConstant := by
  rw [paperFT_dilated_autocorrHeightTest_complex hR, norm_mul,
    norm_pow]
  have hm : 0 < ∫ u, baseHeightBump u := baseHeightBump_integral_pos
  have hcoef :
      ‖((((∫ u, baseHeightBump u) ^ 2)⁻¹ : ℝ) : ℂ)‖ =
        ((∫ u, baseHeightBump u) ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  rw [hcoef]
  let A : ℝ := ‖paperFT (fun u => (baseHeightBump u : ℂ)) ((R : ℂ) * z)‖
  let W : ℝ := ‖(R : ℂ) * z‖ ^ 2
  let C : ℝ := Real.exp (1 / 2) * baseHeightBumpDerivTwoMass
  have hraw := norm_baseHeightBump_paperFT_mul_sq_le ((R : ℂ) * z)
  have hexp : Real.exp (|((R : ℂ) * z).im| / 2) ≤ Real.exp (1 / 2) := by
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right him (by norm_num))
  have hmass0 : 0 ≤ baseHeightBumpDerivTwoMass :=
    baseHeightBumpDerivTwoMass_nonneg
  have hAW : A * W ≤ C := by
    exact hraw.trans (mul_le_mul_of_nonneg_right hexp hmass0)
  have hA0 : 0 ≤ A := norm_nonneg _
  have hW0 : 0 ≤ W := sq_nonneg _
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hsq : (A * W) ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hA0 hW0) hC0).2 hAW
  unfold baseHeightRemoteDecayConstant
  dsimp only [A, W, C] at hsq ⊢
  calc
    ((∫ u, baseHeightBump u) ^ 2)⁻¹ *
          ‖paperFT (fun u => (baseHeightBump u : ℂ)) ((R : ℂ) * z)‖ ^ 2 *
          ‖(R : ℂ) * z‖ ^ 4 =
        ((∫ u, baseHeightBump u) ^ 2)⁻¹ *
          (‖paperFT (fun u => (baseHeightBump u : ℂ)) ((R : ℂ) * z)‖ *
            ‖(R : ℂ) * z‖ ^ 2) ^ 2 := by ring
    _ ≤ ((∫ u, baseHeightBump u) ^ 2)⁻¹ *
          (Real.exp (1 / 2) * baseHeightBumpDerivTwoMass) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq
        (inv_nonneg.mpr (sq_nonneg _))

theorem smoothHeightWindow_support_Icc
    {w x : ℝ} (hw : 0 < w) (hx : smoothHeightWindow w x ≠ 0) :
    x ∈ Set.Icc (1 : ℝ) 2 := by
  have hs := RH.Zeta85.RSReduction.smoothTopHat_support
    (p := (1 : ℝ)) hw hx
  simp only [RH.Zeta85.TopHatMoments.topHatSupport, Set.mem_Icc] at hs ⊢
  constructor <;> linarith [hs.1, hs.2]

theorem distI_one_le_abs_sub_of_mem_Icc
    {x c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    Tail.distI 1 x ≤ |x - c| := by
  by_cases hlo : x ≤ 1
  · rw [Tail.distI_of_le (by norm_num) hlo,
      abs_of_nonpos (by linarith [hc.1])]
    linarith [hc.1]
  by_cases hhi : 2 ≤ x
  · have hhi' : 2 * (1 : ℝ) ≤ x := by norm_num at ⊢; exact hhi
    rw [Tail.distI_of_ge (by norm_num) hhi',
      abs_of_nonneg (by linarith [hc.2])]
    linarith [hc.2]
  · have hx : x ∈ Set.Icc (1 : ℝ) 2 :=
      ⟨le_of_not_ge hlo, le_of_not_ge hhi⟩
    have hin : max ((1 : ℝ) - x) (x - 2 * 1) ≤ 0 := by
      exact max_le (by linarith [hx.1]) (by linarith [hx.2])
    have hzero : Tail.distI 1 x = 0 := by
      unfold Tail.distI
      rw [max_eq_left hin]
    rw [hzero]
    exact abs_nonneg _

theorem norm_paperFT_windowAveraged_mul_dist_four_le
    {Z : ZeroConfig} {R w T : ℝ}
    (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hT : 0 < T) (hRT : R ≤ 2 * T) (rho : Z.carrier) :
    ‖paperFT (windowAveragedHeightTest R w) (gammaOf (rho : ℂ) / T)‖ *
        (R * Tail.distI 1 ((rho : ℂ).im / T)) ^ 4 ≤
      (R / baseHeightKernelMass) * baseHeightRemoteDecayConstant := by
  rw [paperFT_windowAveragedHeightTest hR hw hw1]
  have hstrip : 0 ≤ (rho : ℂ).re ∧ (rho : ℂ).re ≤ 1 :=
    Z.strip (rho : ℂ) rho.property
  have himGamma : |(gammaOf (rho : ℂ)).im| ≤ 1 / 2 := by
    have hgamma : (gammaOf (rho : ℂ)).im = 1 / 2 - (rho : ℂ).re := by
      simp [gammaOf, Complex.div_I]
    rw [hgamma, abs_le]
    constructor <;> linarith
  have him : ∀ c : ℝ,
      |((R : ℂ) * (gammaOf (rho : ℂ) / T - (c : ℂ))).im| ≤ 1 := by
    intro c
    have hdivim : (gammaOf (rho : ℂ) / (T : ℂ)).im =
        (gammaOf (rho : ℂ)).im / T := by
      rw [Complex.div_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.normSq_ofReal]
      field_simp [hT.ne']
      ring
    have himEq :
        ((R : ℂ) * (gammaOf (rho : ℂ) / T - (c : ℂ))).im =
          R * ((gammaOf (rho : ℂ)).im / T) := by
      rw [Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Complex.sub_im, hdivim]
      ring
    rw [himEq, abs_mul, abs_of_pos hR, abs_div, abs_of_pos hT]
    calc
      R * (|(gammaOf (rho : ℂ)).im| / T) ≤ R * ((1 / 2) / T) := by
        gcongr
      _ ≤ 1 := by
        rw [show R * ((1 / 2) / T) = R / (2 * T) by ring]
        exact (div_le_one (by positivity)).2 hRT
  have hscale0 : 0 ≤ R / baseHeightKernelMass :=
    div_nonneg hR.le baseHeightKernelMass_pos.le
  have hHintegrable : Integrable (smoothHeightWindow w) :=
    smoothHeightWindow_integrable hw hw1
  have hmajorInt : Integrable
      (fun c => smoothHeightWindow w c * baseHeightRemoteDecayConstant) :=
    hHintegrable.mul_const _
  calc
    ‖((R / baseHeightKernelMass : ℝ) : ℂ) *
          ∫ c : ℝ, (smoothHeightWindow w c : ℂ) *
            paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
              (gammaOf (rho : ℂ) / T - (c : ℂ))‖ *
        (R * Tail.distI 1 ((rho : ℂ).im / T)) ^ 4 ≤
        (R / baseHeightKernelMass) *
          (∫ c : ℝ, smoothHeightWindow w c *
            baseHeightRemoteDecayConstant) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hscale0]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hscale0
      calc
        ‖∫ c : ℝ, (smoothHeightWindow w c : ℂ) *
              paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
                (gammaOf (rho : ℂ) / T - (c : ℂ))‖ *
              (R * Tail.distI 1 ((rho : ℂ).im / T)) ^ 4 ≤
            (∫ c : ℝ,
              ‖(smoothHeightWindow w c : ℂ) *
                paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
                  (gammaOf (rho : ℂ) / T - (c : ℂ))‖) *
              (R * Tail.distI 1 ((rho : ℂ).im / T)) ^ 4 := by
          gcongr
          exact norm_integral_le_integral_norm _
        _ = ∫ c : ℝ,
              ‖(smoothHeightWindow w c : ℂ) *
                paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
                  (gammaOf (rho : ℂ) / T - (c : ℂ))‖ *
                (R * Tail.distI 1 ((rho : ℂ).im / T)) ^ 4 := by
          rw [integral_mul_const]
        _ ≤ ∫ c : ℝ, smoothHeightWindow w c *
              baseHeightRemoteDecayConstant := by
          apply integral_mono_of_nonneg
          · exact Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (by positivity)
          · exact hmajorInt
          · apply Eventually.of_forall
            intro c
            by_cases hc0 : smoothHeightWindow w c = 0
            · simp [hc0, baseHeightRemoteDecayConstant_nonneg]
            have hc := smoothHeightWindow_support_Icc hw hc0
            have hdist := distI_one_le_abs_sub_of_mem_Icc
              (x := (rho : ℂ).im / T) hc
            have hpacket := norm_paperFT_dilated_autocorr_mul_four_le hR
              (gammaOf (rho : ℂ) / T - (c : ℂ)) (him c)
            change
              ‖(smoothHeightWindow w c : ℂ) *
                  paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
                    (gammaOf (rho : ℂ) / T - (c : ℂ))‖ *
                  (R * Tail.distI 1 ((rho : ℂ).im / T)) ^ 4 ≤
                smoothHeightWindow w c * baseHeightRemoteDecayConstant
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg smoothHeightWindow_nonneg]
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ smoothHeightWindow_nonneg
            have hRd0 :
                0 ≤ R * Tail.distI 1 ((rho : ℂ).im / T) :=
              mul_nonneg hR.le (Tail.distI_nonneg _ _)
            apply (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hRd0
                (mul_le_mul_of_nonneg_left hdist hR.le) 4)
              (norm_nonneg _)).trans
            have hre :
                R * |(rho : ℂ).im / T - c| ≤
                  ‖(R : ℂ) * (gammaOf (rho : ℂ) / T - (c : ℂ))‖ := by
              rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos hR]
              apply mul_le_mul_of_nonneg_left _ hR.le
              have hreal :
                  (gammaOf (rho : ℂ) / T - (c : ℂ)).re =
                    (rho : ℂ).im / T - c := by
                simp [gammaOf, Complex.div_I]
              rw [← hreal]
              exact Complex.abs_re_le_norm _
            exact (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg hR.le (abs_nonneg _)) hre 4)
              (norm_nonneg _)).trans hpacket
    _ = (R / baseHeightKernelMass) *
          (baseHeightRemoteDecayConstant * ∫ c, smoothHeightWindow w c) := by
      rw [integral_mul_const]
      ring
    _ ≤ (R / baseHeightKernelMass) * baseHeightRemoteDecayConstant := by
      apply mul_le_mul_of_nonneg_left _ hscale0
      calc
        baseHeightRemoteDecayConstant * ∫ c, smoothHeightWindow w c ≤
            baseHeightRemoteDecayConstant * 1 := by
          exact mul_le_mul_of_nonneg_left
            (integral_smoothHeightWindow_le_one hw hw1)
            baseHeightRemoteDecayConstant_nonneg
        _ = baseHeightRemoteDecayConstant := mul_one _

end RH.Zeta85.RSPoissonCyclicBridge
