import RH.Zeta85.Discharge.RSHeightMollifierConcrete
import RH.Zeta85.Discharge.RSFixedSmoothBridge

/-!
# A compactly supported height test converging to the dyadic window

This module changes the order of smoothing.  It averages the concrete
autocorrelation packet over a smooth approximation to `[1,2]` before taking
the Fourier transform.  The resulting physical-space test remains smooth and
compactly supported.  On the real Fourier axis it is a positive convolution
with an explicitly normalized approximate identity.

For each fixed smoothing width the selector converges pointwise to the smooth
dyadic window as the concentration parameter tends to infinity.  Sending the
width to zero afterwards gives the open dyadic indicator.  This is the
fixed-test quantifier order required by the Rudnick--Sarnak input.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def smoothHeightWindow (w x : ℝ) : ℝ :=
  RH.Zeta85.RSReduction.smoothTopHat 1 w (x - 3 / 2)

theorem smoothHeightWindow_contDiff {w : ℝ} (hw : 0 < w)
    (hw1 : 2 * w ≤ 1) : ContDiff ℝ ∞ (smoothHeightWindow w) := by
  unfold smoothHeightWindow
  exact (RH.Zeta85.RSReduction.smoothTopHat_contDiff hw hw1).comp
    (contDiff_id.sub contDiff_const)

theorem smoothHeightWindow_hasCompactSupport {w : ℝ} (hw : 0 < w) :
    HasCompactSupport (smoothHeightWindow w) := by
  apply Zeta23.hasCompactSupport_of_support_subset_abs (Λ := 2)
  intro x hx
  have hs := RH.Zeta85.RSReduction.smoothTopHat_support (p := (1 : ℝ)) hw hx
  simp only [RH.Zeta85.TopHatMoments.topHatSupport, Set.mem_Icc] at hs
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2]

theorem smoothHeightWindow_nonneg {w x : ℝ} :
    0 ≤ smoothHeightWindow w x := by
  exact RH.Zeta85.RSReduction.smoothTopHat_nonneg (p := (1 : ℝ)) (by norm_num)

theorem smoothHeightWindow_le_one {w x : ℝ} : smoothHeightWindow w x ≤ 1 := by
  unfold smoothHeightWindow
  have h := RH.Zeta85.RSReduction.smoothTopHat_le (p := (1 : ℝ))
    (w := w) (x := x - 3 / 2) (by norm_num)
  norm_num at h ⊢
  exact h

theorem smoothHeightWindow_eq_one_of_inner {w x : ℝ}
    (hw : 0 < w) (hx : |x - 3 / 2| ≤ 1 / 2 - w) :
    smoothHeightWindow w x = 1 := by
  rw [smoothHeightWindow,
    RH.Zeta85.RSReduction.smoothTopHat_eq_topHat_of_inner
      (p := (1 : ℝ)) (by norm_num) hw hx]
  have hs : x - 3 / 2 ∈ RH.Zeta85.TopHatMoments.topHatSupport 1 := by
    simp only [RH.Zeta85.TopHatMoments.topHatSupport, Set.mem_Icc]
    rw [abs_le] at hx
    constructor <;> linarith [hx.1, hx.2]
  simp [RH.Zeta85.TopHatMoments.topHat, hs]

theorem smoothHeightWindow_eq_zero_of_outer {w x : ℝ}
    (hw : 0 < w) (hx : 1 / 2 ≤ |x - 3 / 2|) :
    smoothHeightWindow w x = 0 := by
  exact RH.Zeta85.RSReduction.smoothTopHat_eq_zero_of_outer hw hx

def openDyadicHeightIndicator (x : ℝ) : ℝ :=
  (Set.Ioo (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) x

theorem smoothHeightWindow_tendsto_openDyadicHeightIndicator (x : ℝ) :
    Tendsto (fun m : ℕ => smoothHeightWindow
      (RH.Zeta85.RSReduction.topHatSmoothingWidth 1 m) x) atTop
      (𝓝 (openDyadicHeightIndicator x)) := by
  by_cases hx : x ∈ Set.Ioo (1 : ℝ) 2
  · have hinner : |x - 3 / 2| < 1 / 2 := by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    let eps : ℝ := 1 / 2 - |x - 3 / 2|
    have heps : 0 < eps := by unfold eps; linarith
    have hwlim := RH.Zeta85.RSReduction.topHatSmoothingWidth_tendsto_zero 1
    have hevent : ∀ᶠ m : ℕ in atTop,
        RH.Zeta85.RSReduction.topHatSmoothingWidth 1 m < eps :=
      (tendsto_order.1 hwlim).2 eps heps
    have heq : (fun m : ℕ => smoothHeightWindow
        (RH.Zeta85.RSReduction.topHatSmoothingWidth 1 m) x) =ᶠ[atTop]
        fun _ => (1 : ℝ) := by
      filter_upwards [hevent] with m hm
      apply smoothHeightWindow_eq_one_of_inner
        (RH.Zeta85.RSReduction.topHatSmoothingWidth_pos (by norm_num) m)
      unfold eps at hm
      linarith
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hind : openDyadicHeightIndicator x = 1 := by
      simp [openDyadicHeightIndicator, hx]
    rw [hind]
    exact hconst.congr' heq.symm
  · have houter : 1 / 2 ≤ |x - 3 / 2| := by
      simp only [Set.mem_Ioo, not_and_or] at hx
      rcases hx with hx | hx
      · have hx' : x ≤ 1 := le_of_not_gt hx
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hx' : 2 ≤ x := le_of_not_gt hx
        rw [abs_of_nonneg (by linarith)]
        linarith
    have heq : (fun m : ℕ => smoothHeightWindow
        (RH.Zeta85.RSReduction.topHatSmoothingWidth 1 m) x) =ᶠ[atTop]
        fun _ => (0 : ℝ) := by
      filter_upwards [] with m
      exact smoothHeightWindow_eq_zero_of_outer
        (RH.Zeta85.RSReduction.topHatSmoothingWidth_pos (by norm_num) m) houter
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have hind : openDyadicHeightIndicator x = 0 := by
      simp [openDyadicHeightIndicator, hx]
    rw [hind]
    exact hconst.congr' heq.symm

theorem smoothHeightWindow_support_bound {w x : ℝ} (hw : 0 < w)
    (hx : smoothHeightWindow w x ≠ 0) : |x| ≤ 2 := by
  have hs := RH.Zeta85.RSReduction.smoothTopHat_support (p := (1 : ℝ)) hw hx
  simp only [RH.Zeta85.TopHatMoments.topHatSupport, Set.mem_Icc] at hs
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2]

def dualSmoothHeightWindow (w u : ℝ) : ℂ :=
  paperFT (fun x => (smoothHeightWindow w x : ℂ)) (-u : ℂ)

theorem dualSmoothHeightWindow_contDiff {w : ℝ} (hw : 0 < w)
    (hw1 : 2 * w ≤ 1) : ContDiff ℝ ∞ (dualSmoothHeightWindow w) := by
  have hH : Continuous (fun x => (smoothHeightWindow w x : ℂ)) :=
    Complex.continuous_ofReal.comp (smoothHeightWindow_contDiff hw hw1).continuous
  have hHc : HasCompactSupport (fun x => (smoothHeightWindow w x : ℂ)) :=
    (smoothHeightWindow_hasCompactSupport hw).comp_left Complex.ofReal_zero
  have hFT := Zeta23.Taper.contDiff_paperFT_ofReal hH hHc (⊤ : ℕ∞)
  have heq : dualSmoothHeightWindow w = fun u : ℝ =>
      paperFT (fun x => (smoothHeightWindow w x : ℂ)) ((-u : ℝ) : ℂ) := by
    funext u
    simp only [dualSmoothHeightWindow, Complex.ofReal_neg]
  rw [heq]
  exact hFT.comp contDiff_neg

def baseHeightKernelMass : ℝ :=
  2 * Real.pi * (∫ u, baseHeightBump u ^ 2) /
    (∫ u, baseHeightBump u) ^ 2

set_option maxHeartbeats 800000 in
theorem integral_baseHeightBump_sq_pos : 0 < ∫ u, baseHeightBump u ^ 2 := by
  let q : ℝ → ℝ := fun u => baseHeightBump u ^ 2
  have hqcont : Continuous q := baseHeightBump_contDiff.continuous.pow 2
  have hqcompact : HasCompactSupport q :=
    baseHeightBump_hasCompactSupport.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  change 0 < ∫ u, q u
  apply hqcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hqcompact
    (fun _ => sq_nonneg _)
  show q 0 ≠ 0
  simp [q, baseHeightBump_zero]

theorem baseHeightKernelMass_pos : 0 < baseHeightKernelMass := by
  unfold baseHeightKernelMass
  exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    integral_baseHeightBump_sq_pos) (sq_pos_of_pos baseHeightBump_integral_pos)

def baseHeightKernel (x : ℝ) : ℝ :=
  ((∫ u, baseHeightBump u) ^ 2)⁻¹ *
    (paperFT (fun u => (baseHeightBump u : ℂ)) (x : ℂ)).re ^ 2

theorem baseHeightKernel_nonneg (x : ℝ) : 0 ≤ baseHeightKernel x := by
  unfold baseHeightKernel
  positivity

theorem baseHeightKernel_continuous : Continuous baseHeightKernel := by
  unfold baseHeightKernel
  have hbaseC : Continuous (fun u => (baseHeightBump u : ℂ)) :=
    Complex.continuous_ofReal.comp baseHeightBump_contDiff.continuous
  have hbaseCs : HasCompactSupport (fun u => (baseHeightBump u : ℂ)) :=
    baseHeightBump_hasCompactSupport.comp_left Complex.ofReal_zero
  exact continuous_const.mul
    ((Zeta23.Taper.contDiff_re_paperFT_ofReal hbaseC hbaseCs 0).continuous.pow 2)

theorem baseHeightKernel_integrable : Integrable baseHeightKernel := by
  have hbaseC2 : ContDiff ℝ 2 (fun u => (baseHeightBump u : ℂ)) := by
    have hreal : ContDiff ℝ 2 baseHeightBump :=
      baseHeightBump_contDiff.of_le
        (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
          change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
    convert Complex.ofRealCLM.contDiff.comp hreal using 1
    funext u
    rfl
  have hsupp : ∀ u, (baseHeightBump u : ℂ) ≠ 0 → |u| ≤ (1 : ℝ) / 2 := by
    intro u hu
    by_contra hout
    have hz := baseHeightBump_eq_zero_of_outer (le_of_not_ge hout)
    exact hu (by simp [hz])
  have hi := (Zeta23.Taper.integrable_re_paperFT_sq_and hbaseC2 hsupp).1
  change Integrable (fun x : ℝ => ((∫ u, baseHeightBump u) ^ 2)⁻¹ *
    (paperFT (fun u => (baseHeightBump u : ℂ)) (x : ℂ)).re ^ 2)
  exact hi.const_mul (((∫ u, baseHeightBump u) ^ 2)⁻¹)

theorem integral_baseHeightKernel : ∫ x, baseHeightKernel x = baseHeightKernelMass := by
  let A : ℝ → ℝ := fun u =>
    Zeta23.Params.autocorr baseHeightBump u / (∫ x, baseHeightBump x) ^ 2
  have hAcont : Continuous A :=
    (Zeta23.Taper.autocorr_continuous_of_even baseHeightBump_even
      baseHeightBump_contDiff.continuous baseHeightBump_hasCompactSupport).div_const _
  have hAint : Integrable A :=
    (Zeta23.Taper.autocorr_integrable_of_even baseHeightBump_even
      baseHeightBump_contDiff.continuous baseHeightBump_hasCompactSupport).div_const _
  have hFT : ∀ r : ℝ,
      paperFT (fun u => (A u : ℂ)) r = (baseHeightKernel r : ℂ) := by
    intro r
    have hAeq : (fun u => (A u : ℂ)) = autocorrHeightTest baseHeightBump 0 := by
      funext u
      unfold A autocorrHeightTest
      simp
    have h := paperFT_autocorrHeightTest_real_formula baseHeightBump_even
      baseHeightBump_contDiff.continuous baseHeightBump_hasCompactSupport 0 r
    rw [hAeq]
    simpa only [sub_zero, baseHeightKernel] using h
  have hinv := Zeta23.Taper.integral_mul_cos_of_paperFT_eq
    hAcont hAint baseHeightKernel_integrable hFT 0
  simp only [mul_zero, Real.cos_zero, mul_one] at hinv
  rw [hinv]
  unfold A baseHeightKernelMass Zeta23.Params.autocorr
  simp only [add_zero]
  ring

def windowAveragedHeightTest (R w u : ℝ) : ℂ :=
  ((R / baseHeightKernelMass : ℝ) : ℂ) *
    autocorrHeightTest (dilatedHeightBump R) 0 u *
      dualSmoothHeightWindow w u

theorem windowAveragedHeightTest_contDiff {R w : ℝ} (hR : 0 < R)
    (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    ContDiff ℝ ∞ (windowAveragedHeightTest R w) := by
  unfold windowAveragedHeightTest
  exact (contDiff_const.mul
    (autocorrHeightTest_contDiff (dilatedHeightBump_even R)
      (dilatedHeightBump_contDiff R)
      (dilatedHeightBump_hasCompactSupport hR.ne') 0)).mul
        (dualSmoothHeightWindow_contDiff hw hw1)

theorem windowAveragedHeightTest_hasCompactSupport {R w : ℝ} (hR : 0 < R) :
    HasCompactSupport (windowAveragedHeightTest R w) := by
  unfold windowAveragedHeightTest
  exact ((autocorrHeightTest_hasCompactSupport (dilatedHeightBump_even R)
    (dilatedHeightBump_hasCompactSupport hR.ne') 0).mul_left).mul_right

theorem paperFT_windowAveragedHeightTest
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (z : ℂ) :
    paperFT (windowAveragedHeightTest R w) z =
      ((R / baseHeightKernelMass : ℝ) : ℂ) *
        ∫ c : ℝ, (smoothHeightWindow w c : ℂ) *
          paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
            (z - (c : ℂ)) := by
  let H : ℝ → ℂ := fun c => (smoothHeightWindow w c : ℂ)
  let A : ℝ → ℂ := autocorrHeightTest (dilatedHeightBump R) 0
  let F : ℝ → ℝ → ℂ := fun c u =>
    H c * A u * cexp (I * (z - (c : ℂ)) * (u : ℂ))
  have hHcont : Continuous H :=
    Complex.continuous_ofReal.comp (smoothHeightWindow_contDiff hw hw1).continuous
  have hAcont : Continuous A :=
    (autocorrHeightTest_contDiff (dilatedHeightBump_even R)
      (dilatedHeightBump_contDiff R)
      (dilatedHeightBump_hasCompactSupport hR.ne') 0).continuous
  have hFcont : Continuous (Function.uncurry F) := by
    exact ((hHcont.comp continuous_fst).mul
      (hAcont.comp continuous_snd)).mul (by fun_prop)
  have hFcompact : HasCompactSupport (Function.uncurry F) := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_Icc (a := (-2 : ℝ)) (b := 2)).prod
        (isCompact_Icc (a := -R) (b := R)))
    intro p hp
    simp only [Function.mem_support] at hp
    have hH : H p.1 ≠ 0 := by
      intro hzH
      apply hp
      change H p.1 * A p.2 * cexp (I * (z - (p.1 : ℂ)) * (p.2 : ℂ)) = 0
      rw [hzH, zero_mul, zero_mul]
    have hA : A p.2 ≠ 0 := by
      intro hzA
      apply hp
      change H p.1 * A p.2 * cexp (I * (z - (p.1 : ℂ)) * (p.2 : ℂ)) = 0
      rw [hzA, mul_zero, zero_mul]
    have hc := smoothHeightWindow_support_bound hw (by simpa [H] using hH)
    have hu : |p.2| ≤ R := by
      by_contra hout
      have hz := autocorrHeightTest_dilated_support (c := 0) hR (le_of_not_ge hout)
      exact hA (by simpa [A] using hz)
    exact ⟨abs_le.mp hc, abs_le.mp hu⟩
  have hswap : (∫ u : ℝ, ∫ c : ℝ, F c u) =
      ∫ c : ℝ, ∫ u : ℝ, F c u :=
    (MeasureTheory.integral_integral_swap_of_hasCompactSupport hFcont hFcompact).symm
  rw [paperFT_def]
  unfold windowAveragedHeightTest
  rw [show (fun u : ℝ =>
      ((R / baseHeightKernelMass : ℝ) : ℂ) *
          autocorrHeightTest (dilatedHeightBump R) 0 u *
            dualSmoothHeightWindow w u * cexp (I * z * (u : ℂ))) =
      fun u : ℝ => ((R / baseHeightKernelMass : ℝ) : ℂ) *
        (autocorrHeightTest (dilatedHeightBump R) 0 u *
          dualSmoothHeightWindow w u * cexp (I * z * (u : ℂ))) by
        funext u
        ring]
  rw [integral_const_mul_C]
  congr 1
  calc
    (∫ u : ℝ, autocorrHeightTest (dilatedHeightBump R) 0 u *
          dualSmoothHeightWindow w u * cexp (I * z * (u : ℂ))) =
        ∫ u : ℝ, ∫ c : ℝ, F c u := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [dualSmoothHeightWindow, paperFT_def]
      rw [← integral_const_mul_C, ← integral_mul_const_C]
      apply integral_congr_ae
      filter_upwards [] with c
      simp only [F, H, A]
      have hexp : cexp (I * (-((u : ℝ) : ℂ)) * (c : ℂ)) *
          cexp (I * z * (u : ℂ)) =
          cexp (I * (z - (c : ℂ)) * (u : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      calc
        autocorrHeightTest (dilatedHeightBump R) 0 u *
              ((smoothHeightWindow w c : ℂ) *
                cexp (I * (-((u : ℝ) : ℂ)) * (c : ℂ))) *
              cexp (I * z * (u : ℂ)) =
            (smoothHeightWindow w c : ℂ) *
              autocorrHeightTest (dilatedHeightBump R) 0 u *
                (cexp (I * (-((u : ℝ) : ℂ)) * (c : ℂ)) *
                  cexp (I * z * (u : ℂ))) := by ring
        _ = (smoothHeightWindow w c : ℂ) *
              autocorrHeightTest (dilatedHeightBump R) 0 u *
                cexp (I * (z - (c : ℂ)) * (u : ℂ)) := by rw [hexp]
    _ = ∫ c : ℝ, ∫ u : ℝ, F c u := hswap
    _ = ∫ c : ℝ, (smoothHeightWindow w c : ℂ) *
          paperFT (autocorrHeightTest (dilatedHeightBump R) 0)
            (z - (c : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with c
      rw [paperFT_def, ← integral_const_mul_C]
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [F, H, A]
      ring

theorem paperFT_windowAveragedHeightTest_real_formula
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (x : ℝ) :
    paperFT (windowAveragedHeightTest R w) (x : ℂ) =
      (((R / baseHeightKernelMass) *
        ∫ c : ℝ, smoothHeightWindow w c *
          baseHeightKernel (R * (x - c)) : ℝ) : ℂ) := by
  rw [paperFT_windowAveragedHeightTest hR hw hw1]
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
  let rfun : ℝ → ℝ := fun c => smoothHeightWindow w c *
    baseHeightKernel (R * (x - c))
  have hfun : (fun c : ℝ => (smoothHeightWindow w c : ℂ) *
      (baseHeightKernel (R * (x - c)) : ℂ)) =
      fun c => (rfun c : ℂ) := by
    funext c
    exact (Complex.ofReal_mul _ _).symm
  let J : ℝ := ∫ c : ℝ, smoothHeightWindow w c *
    baseHeightKernel (R * (x - c))
  have hint : (∫ c : ℝ, (smoothHeightWindow w c : ℂ) *
      (baseHeightKernel (R * (x - c)) : ℂ)) =
      (J : ℂ) := by
    rw [hfun, Zeta23.integral_ofReal_C]
  calc
    ((R / baseHeightKernelMass : ℝ) : ℂ) *
        (∫ c : ℝ, (smoothHeightWindow w c : ℂ) *
          (baseHeightKernel (R * (x - c)) : ℂ)) =
        ((R / baseHeightKernelMass : ℝ) : ℂ) * (J : ℂ) := by rw [hint]
    _ = (((R / baseHeightKernelMass) * J : ℝ) : ℂ) :=
      (Complex.ofReal_mul (R / baseHeightKernelMass) J).symm
    _ = (((R / baseHeightKernelMass) *
        ∫ c : ℝ, smoothHeightWindow w c *
          baseHeightKernel (R * (x - c)) : ℝ) : ℂ) := by rfl

theorem integral_baseHeightKernel_scaled_sub {R : ℝ} (hR : 0 < R) (x : ℝ) :
    ∫ c : ℝ, baseHeightKernel (R * (x - c)) = baseHeightKernelMass / R := by
  have htrans := MeasureTheory.integral_sub_left_eq_self
    (fun y : ℝ => baseHeightKernel (R * y)) volume x
  have hscale := Measure.integral_comp_mul_left baseHeightKernel R
  calc
    (∫ c : ℝ, baseHeightKernel (R * (x - c))) =
        ∫ y : ℝ, baseHeightKernel (R * y) := htrans
    _ = |R⁻¹| • ∫ y : ℝ, baseHeightKernel y := hscale
    _ = baseHeightKernelMass / R := by
      rw [integral_baseHeightKernel, abs_of_pos (inv_pos.mpr hR)]
      simp only [smul_eq_mul]
      ring

theorem paperFT_windowAveragedHeightTest_real_mem_Icc
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (x : ℝ) :
    (paperFT (windowAveragedHeightTest R w) (x : ℂ)).re ∈ Set.Icc 0 1 := by
  rw [paperFT_windowAveragedHeightTest_real_formula hR hw hw1]
  simp only [Complex.ofReal_re]
  have hM : 0 < baseHeightKernelMass := baseHeightKernelMass_pos
  have hscale : 0 ≤ R / baseHeightKernelMass := (div_pos hR hM).le
  let q : ℝ → ℝ := fun c => baseHeightKernel (R * (x - c))
  have hqint : Integrable q := by
    unfold q
    exact (baseHeightKernel_integrable.comp_mul_left' hR.ne').comp_sub_left x
  have hHint : Integrable (fun c => q c * smoothHeightWindow w c) := by
    refine hqint.mul_bdd (c := 1)
      (smoothHeightWindow_contDiff hw hw1).continuous.aestronglyMeasurable ?_
    filter_upwards [] with c
    rw [Real.norm_eq_abs, abs_of_nonneg smoothHeightWindow_nonneg]
    exact smoothHeightWindow_le_one
  have hprodint : Integrable (fun c => smoothHeightWindow w c * q c) := by
    convert hHint using 1
    funext c
    ring
  have hI0 : 0 ≤ ∫ c, smoothHeightWindow w c * q c :=
    integral_nonneg fun c => mul_nonneg smoothHeightWindow_nonneg (baseHeightKernel_nonneg _)
  have hIle : (∫ c, smoothHeightWindow w c * q c) ≤ ∫ c, q c := by
    apply integral_mono hprodint hqint
    intro c
    calc
      smoothHeightWindow w c * q c ≤ 1 * q c := by
        exact mul_le_mul_of_nonneg_right smoothHeightWindow_le_one
          (baseHeightKernel_nonneg _)
      _ = q c := one_mul _
  constructor
  · exact mul_nonneg hscale hI0
  · have hq : ∫ c, q c = baseHeightKernelMass / R :=
      integral_baseHeightKernel_scaled_sub hR x
    calc
      (R / baseHeightKernelMass) *
          (∫ c, smoothHeightWindow w c * baseHeightKernel (R * (x - c))) =
          (R / baseHeightKernelMass) *
            (∫ c, smoothHeightWindow w c * q c) := by rfl
      _ ≤ (R / baseHeightKernelMass) * ∫ c, q c := by gcongr
      _ = 1 := by
        rw [hq, div_eq_mul_inv]
        calc
          R * baseHeightKernelMass⁻¹ *
              (baseHeightKernelMass * R⁻¹) =
              (baseHeightKernelMass⁻¹ * baseHeightKernelMass) *
                (R * R⁻¹) := by ring
          _ = 1 := by
            rw [inv_mul_cancel₀ hM.ne', mul_inv_cancel₀ hR.ne', one_mul]

def windowAveragedHeightWeight (R w x : ℝ) : ℝ :=
  (paperFT (windowAveragedHeightTest R w) (x : ℂ)).re

theorem windowAveragedHeightWeight_eq_kernelIntegral
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (x : ℝ) :
    windowAveragedHeightWeight R w x =
      baseHeightKernelMass⁻¹ *
        ∫ y : ℝ, smoothHeightWindow w (x - y / R) * baseHeightKernel y := by
  rw [windowAveragedHeightWeight,
    paperFT_windowAveragedHeightTest_real_formula hR hw hw1]
  simp only [Complex.ofReal_re]
  let f : ℝ → ℝ := fun d =>
    smoothHeightWindow w (x - d) * baseHeightKernel (R * d)
  let g : ℝ → ℝ := fun y =>
    smoothHeightWindow w (x - y / R) * baseHeightKernel y
  have hshift : (∫ c : ℝ, smoothHeightWindow w c *
      baseHeightKernel (R * (x - c))) = ∫ d : ℝ, f d := by
    have h := MeasureTheory.integral_sub_left_eq_self f volume x
    calc
      (∫ c : ℝ, smoothHeightWindow w c *
          baseHeightKernel (R * (x - c))) = ∫ c : ℝ, f (x - c) := by
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
        (R⁻¹ * ∫ y, smoothHeightWindow w (x - y / R) * baseHeightKernel y) =
        baseHeightKernelMass⁻¹ *
          ((R * R⁻¹) * ∫ y, smoothHeightWindow w (x - y / R) * baseHeightKernel y) := by
            ring
    _ = baseHeightKernelMass⁻¹ *
        ∫ y, smoothHeightWindow w (x - y / R) * baseHeightKernel y := by
      rw [mul_inv_cancel₀ hR.ne', one_mul]

theorem windowAveragedHeightWeight_tendsto
    {w : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) (x : ℝ) :
    Tendsto (fun R : ℝ => windowAveragedHeightWeight R w x) atTop
      (𝓝 (smoothHeightWindow w x)) := by
  let F : ℝ → ℝ → ℝ := fun R y =>
    smoothHeightWindow w (x - y / R) * baseHeightKernel y
  let f : ℝ → ℝ := fun y => smoothHeightWindow w x * baseHeightKernel y
  have hHcont := (smoothHeightWindow_contDiff hw hw1).continuous
  have hFmeas : ∀ᶠ R : ℝ in atTop, AEStronglyMeasurable (F R) := by
    filter_upwards [] with R
    exact ((hHcont.comp (by fun_prop)).mul baseHeightKernel_continuous).aestronglyMeasurable
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ᵐ y : ℝ,
      ‖F R y‖ ≤ baseHeightKernel y := by
    filter_upwards [] with R
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg smoothHeightWindow_nonneg (baseHeightKernel_nonneg y))]
    calc
      smoothHeightWindow w (x - y / R) * baseHeightKernel y ≤
          1 * baseHeightKernel y :=
        mul_le_mul_of_nonneg_right smoothHeightWindow_le_one
          (baseHeightKernel_nonneg y)
      _ = baseHeightKernel y := one_mul _
  have hpoint : ∀ᵐ y : ℝ, Tendsto (fun R : ℝ => F R y) atTop (𝓝 (f y)) := by
    filter_upwards [] with y
    have hy : Tendsto (fun R : ℝ => y / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hx : Tendsto (fun R : ℝ => x - y / R) atTop (𝓝 x) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hy
    have hH : Tendsto (fun R : ℝ => smoothHeightWindow w (x - y / R))
        atTop (𝓝 (smoothHeightWindow w x)) := hHcont.continuousAt.tendsto.comp hx
    exact hH.mul tendsto_const_nhds
  have hlim := tendsto_integral_filter_of_dominated_convergence
    baseHeightKernel hFmeas hbound baseHeightKernel_integrable hpoint
  have hscaled : Tendsto (fun R : ℝ => baseHeightKernelMass⁻¹ * ∫ y, F R y)
      atTop (𝓝 (smoothHeightWindow w x)) := by
    have hconst : Tendsto (fun _ : ℝ => baseHeightKernelMass⁻¹) atTop
        (𝓝 baseHeightKernelMass⁻¹) := tendsto_const_nhds
    have hmul := hconst.mul hlim
    have hfintegral : ∫ y, f y = smoothHeightWindow w x * baseHeightKernelMass := by
      unfold f
      rw [integral_const_mul, integral_baseHeightKernel]
    rw [hfintegral] at hmul
    have hcancel : baseHeightKernelMass⁻¹ *
        (smoothHeightWindow w x * baseHeightKernelMass) = smoothHeightWindow w x := by
      calc
        baseHeightKernelMass⁻¹ *
            (smoothHeightWindow w x * baseHeightKernelMass) =
            smoothHeightWindow w x *
              (baseHeightKernelMass⁻¹ * baseHeightKernelMass) := by ring
        _ = smoothHeightWindow w x := by
          rw [inv_mul_cancel₀ baseHeightKernelMass_pos.ne', mul_one]
    rw [hcancel] at hmul
    exact hmul
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [windowAveragedHeightWeight_eq_kernelIntegral hR hw hw1]

end RH.Zeta85.RSPoissonCyclicBridge
