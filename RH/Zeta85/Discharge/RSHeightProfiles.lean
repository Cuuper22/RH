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

end RH.Zeta85.RSPoissonCyclicBridge
