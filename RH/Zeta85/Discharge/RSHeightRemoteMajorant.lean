import RH.Zeta85.Discharge.RSHeightPartitionMain

/-!
# Quantitative inner-height leakage

The inner dyadic selector vanishes outside `[1,2]`.  Its averaged real-axis
weight is therefore controlled by the tail of the positive base kernel away
from that interval.  The compact physical test also gives an explicit
off-critical-line correction.  These are the scalar estimates needed before
summing the complementary zero tuples.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

theorem integral_smoothHeightWindow_le_one
    {w : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    (∫ x, smoothHeightWindow w x) ≤ 1 := by
  let I : ℝ → ℝ :=
    (Set.Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ))
  have hIint : Integrable I := by
    unfold I
    exact (integrableOn_const (s := Set.Icc (1 : ℝ) 2)
      (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  have hpoint : ∀ x, smoothHeightWindow w x ≤ I x := by
    intro x
    by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
    · simp only [I, Set.indicator_of_mem hx]
      exact smoothHeightWindow_le_one
    · simp only [I, Set.indicator_of_notMem hx]
      have hout : 1 / 2 ≤ |x - 3 / 2| := by
        simp only [Set.mem_Icc, not_and_or] at hx
        rcases hx with hx | hx
        · have hx' : x < 1 := lt_of_not_ge hx
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hx' : 2 < x := lt_of_not_ge hx
          rw [abs_of_nonneg (by linarith)]
          linarith
      rw [smoothHeightWindow_eq_zero_of_outer hw hout]
  have hmono := integral_mono (smoothHeightWindow_integrable hw hw1) hIint hpoint
  have hI : ∫ x, I x = 1 := by
    unfold I
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
    norm_num
  rwa [hI] at hmono

theorem windowAveragedHeightWeight_le_tail_of_outside
    {R w eta x : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (heta : 0 < eta) (hx : x ≤ 1 - eta ∨ 2 + eta ≤ x) :
    windowAveragedHeightWeight R w x ≤
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
  have htailInt : Integrable (S.indicator baseHeightKernel) :=
    (baseHeightKernel_integrable.integrableOn).integrable_indicator hSmeas
  have hpoint : ∀ y : ℝ,
      H y * baseHeightKernel y ≤ S.indicator baseHeightKernel y := by
    intro y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
      exact mul_le_of_le_one_left (baseHeightKernel_nonneg y)
        (smoothHeightWindow_le_one (w := w) (x := x - y / R))
    · rw [Set.indicator_of_notMem hy]
      have hylt : |y| < R * eta := lt_of_not_ge hy
      have hydiv : |y / R| < eta := by
        rw [abs_div, abs_of_pos hR]
        exact (div_lt_iff₀ hR).2 (by simpa [mul_comm] using hylt)
      have houter : 1 / 2 ≤ |(x - y / R) - 3 / 2| := by
        rcases hx with hlo | hhi
        · have hz : x - y / R < 1 := by
            linarith [neg_abs_le (y / R), le_abs_self (y / R)]
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hz : 2 < x - y / R := by
            linarith [neg_abs_le (y / R), le_abs_self (y / R)]
          rw [abs_of_nonneg (by linarith)]
          linarith
      rw [show H y = 0 by
        exact smoothHeightWindow_eq_zero_of_outer hw houter]
      simp
  rw [windowAveragedHeightWeight_eq_kernelIntegral hR hw hw1]
  calc
    baseHeightKernelMass⁻¹ *
          (∫ y : ℝ, smoothHeightWindow w (x - y / R) * baseHeightKernel y) ≤
        baseHeightKernelMass⁻¹ *
          (∫ y : ℝ, S.indicator baseHeightKernel y) := by
      exact mul_le_mul_of_nonneg_left
        (integral_mono hprodInt htailInt hpoint)
        (inv_nonneg.mpr baseHeightKernelMass_pos.le)
    _ = baseHeightKernelMass⁻¹ * baseHeightKernelTail (R * eta) := by
      rw [baseHeightKernelTail, MeasureTheory.integral_indicator hSmeas]

theorem norm_dualSmoothHeightWindow_le_one
    {w u : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    ‖dualSmoothHeightWindow w u‖ ≤ 1 := by
  have h := norm_paperFT_of_nonneg_real_le_mass
    (fun x => smoothHeightWindow_nonneg (w := w) (x := x)) (-u)
  simpa only [dualSmoothHeightWindow, Complex.ofReal_neg] using
    h.trans (integral_smoothHeightWindow_le_one hw hw1)

theorem integral_norm_windowAveragedHeightTest_le
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    (∫ u, ‖windowAveragedHeightTest R w u‖) ≤
      R / baseHeightKernelMass := by
  let A : ℝ → ℂ := autocorrHeightTest (dilatedHeightBump R) 0
  have hAcont : Continuous A :=
    (autocorrHeightTest_contDiff (dilatedHeightBump_even R)
      (dilatedHeightBump_contDiff R)
      (dilatedHeightBump_hasCompactSupport hR.ne') 0).continuous
  have hAc : HasCompactSupport A :=
    autocorrHeightTest_hasCompactSupport (dilatedHeightBump_even R)
      (dilatedHeightBump_hasCompactSupport hR.ne') 0
  have hAint : Integrable (fun u => ‖A u‖) :=
    (hAcont.integrable_of_hasCompactSupport hAc).norm
  have hscale : 0 ≤ R / baseHeightKernelMass :=
    div_nonneg hR.le baseHeightKernelMass_pos.le
  have hmajor : Integrable (fun u => (R / baseHeightKernelMass) * ‖A u‖) :=
    hAint.const_mul _
  calc
    (∫ u, ‖windowAveragedHeightTest R w u‖) ≤
        ∫ u, (R / baseHeightKernelMass) * ‖A u‖ := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun u => norm_nonneg _
      · exact hmajor
      · apply Eventually.of_forall
        intro u
        unfold windowAveragedHeightTest
        change ‖((R / baseHeightKernelMass : ℝ) : ℂ) * A u *
            dualSmoothHeightWindow w u‖ ≤
          (R / baseHeightKernelMass) * ‖A u‖
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hscale]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right (norm_nonneg (A u))
            (norm_dualSmoothHeightWindow_le_one (u := u) hw hw1)) hscale
    _ = (R / baseHeightKernelMass) * (∫ u, ‖A u‖) := by
      rw [integral_const_mul]
    _ = R / baseHeightKernelMass := by
      rw [integral_norm_autocorrHeightTest_eq_one
        (dilatedHeightBump_even R)
        (dilatedHeightBump_contDiff R).continuous
        (dilatedHeightBump_hasCompactSupport hR.ne')
        (dilatedHeightBump_nonneg R)
        (dilatedHeightBump_integral_pos hR) 0, mul_one]

theorem windowAveragedHeightTest_support_radius
    {R w u : ℝ} (hR : 0 < R)
    (hu : windowAveragedHeightTest R w u ≠ 0) : |u| ≤ R := by
  by_contra hout
  apply hu
  unfold windowAveragedHeightTest
  rw [autocorrHeightTest_dilated_support hR (le_of_not_ge hout), mul_zero,
    zero_mul]

theorem norm_windowAveragedHeight_zero_sub_real_le
    {Z : ZeroConfig} {R w T : ℝ}
    (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hT : 0 < T) (hRT : R ≤ 2 * T) (rho : Z.carrier) :
    ‖paperFT (windowAveragedHeightTest R w) (gammaOf (rho : ℂ) / T) -
        paperFT (windowAveragedHeightTest R w)
          ((((rho : ℂ).im / T : ℝ) : ℂ))‖ ≤
      (R / T) * (R / baseHeightKernelMass) := by
  have h := norm_paperFT_zero_height_sub_real_le
    (windowAveragedHeightTest_contDiff hR hw hw1).continuous
    (fun u hu => windowAveragedHeightTest_support_radius hR hu)
    hT hRT rho
  exact h.trans (mul_le_mul_of_nonneg_left
    (integral_norm_windowAveragedHeightTest_le hR hw hw1)
    (div_nonneg hR.le hT.le))

theorem norm_windowAveragedHeight_of_zero_outside_le
    {Z : ZeroConfig} {R w T eta : ℝ}
    (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hT : 0 < T) (hRT : R ≤ 2 * T) (heta : 0 < eta)
    (rho : Z.carrier)
    (hout : (rho : ℂ).im / T ≤ 1 - eta ∨
      2 + eta ≤ (rho : ℂ).im / T) :
    ‖paperFT (windowAveragedHeightTest R w) (gammaOf (rho : ℂ) / T)‖ ≤
      (R / T) * (R / baseHeightKernelMass) +
        baseHeightKernelMass⁻¹ * baseHeightKernelTail (R * eta) := by
  let z := paperFT (windowAveragedHeightTest R w) (gammaOf (rho : ℂ) / T)
  let r := paperFT (windowAveragedHeightTest R w)
    ((((rho : ℂ).im / T : ℝ) : ℂ))
  have htri : ‖z‖ ≤ ‖z - r‖ + ‖r‖ := by
    calc
      ‖z‖ = ‖(z - r) + r‖ := by ring_nf
      _ ≤ ‖z - r‖ + ‖r‖ := norm_add_le _ _
  have hvertical : ‖z - r‖ ≤ (R / T) * (R / baseHeightKernelMass) := by
    exact norm_windowAveragedHeight_zero_sub_real_le hR hw hw1 hT hRT rho
  have hrreal : r = ((windowAveragedHeightWeight R w
      ((rho : ℂ).im / T) : ℝ) : ℂ) := by
    dsimp only [r]
    rw [windowAveragedHeightWeight,
      paperFT_windowAveragedHeightTest_real_formula hR hw hw1]
    simp
  have hreal : ‖r‖ ≤
      baseHeightKernelMass⁻¹ * baseHeightKernelTail (R * eta) := by
    rw [hrreal, Complex.norm_real, Real.norm_eq_abs]
    have hW0 : 0 ≤ windowAveragedHeightWeight R w ((rho : ℂ).im / T) := by
      change 0 ≤ (paperFT (windowAveragedHeightTest R w)
        ((((rho : ℂ).im / T : ℝ) : ℂ))).re
      exact (paperFT_windowAveragedHeightTest_real_mem_Icc hR hw hw1 _).1
    rw [abs_of_nonneg hW0]
    exact windowAveragedHeightWeight_le_tail_of_outside
      hR hw hw1 heta hout
  exact htri.trans (add_le_add hvertical hreal)

def dyadicRemoteHeightGap (q : ℕ) : ℝ :=
  1 / Real.sqrt ((q : ℝ) + 1)

def dyadicRemoteHeightLeakageBound (q : ℕ) : ℝ :=
  baseHeightKernelMass⁻¹ * (((q : ℝ) + 1) ^ 2)⁻¹ +
    baseHeightKernelMass⁻¹ *
      baseHeightKernelTail (Real.sqrt ((q : ℝ) + 1))

theorem dyadicRemoteHeightGap_pos (q : ℕ) :
    0 < dyadicRemoteHeightGap q := by
  unfold dyadicRemoteHeightGap
  positivity

theorem dyadicRemoteHeightLeakageBound_tendsto_zero :
    Tendsto dyadicRemoteHeightLeakageBound atTop (nhds 0) := by
  have hbase : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun q : ℕ => ((q : ℝ) + 1) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hbase
  have hinv : Tendsto (fun q : ℕ => (((q : ℝ) + 1) ^ 2)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsq
  have hfirst : Tendsto
      (fun q : ℕ => baseHeightKernelMass⁻¹ * (((q : ℝ) + 1) ^ 2)⁻¹)
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (show Tendsto (fun _ : ℕ => baseHeightKernelMass⁻¹) atTop
        (nhds baseHeightKernelMass⁻¹) from tendsto_const_nhds).mul hinv
  have hsqrt : Tendsto (fun q : ℕ => Real.sqrt ((q : ℝ) + 1))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hbase
  have htail : Tendsto
      (fun q : ℕ => baseHeightKernelTail (Real.sqrt ((q : ℝ) + 1)))
      atTop (nhds 0) := baseHeightKernelTail_tendsto_zero.comp hsqrt
  have hsecond : Tendsto
      (fun q : ℕ => baseHeightKernelMass⁻¹ *
        baseHeightKernelTail (Real.sqrt ((q : ℝ) + 1)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (show Tendsto (fun _ : ℕ => baseHeightKernelMass⁻¹) atTop
        (nhds baseHeightKernelMass⁻¹) from tendsto_const_nhds).mul htail
  change Tendsto
    (fun q : ℕ => baseHeightKernelMass⁻¹ * (((q : ℝ) + 1) ^ 2)⁻¹ +
      baseHeightKernelMass⁻¹ *
        baseHeightKernelTail (Real.sqrt ((q : ℝ) + 1))) atTop (nhds 0)
  simpa only [zero_add] using hfirst.add hsecond

theorem norm_windowAveragedHeight_of_far_zero_le_dyadicLeakage
    {Z : ZeroConfig} {w T : ℝ} (q : ℕ)
    (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hTpower : ((q : ℝ) + 1) ^ 4 ≤ T) (rho : Z.carrier)
    (hout : (rho : ℂ).im / T ≤ 1 - dyadicRemoteHeightGap q ∨
      2 + dyadicRemoteHeightGap q ≤ (rho : ℂ).im / T) :
    ‖paperFT (windowAveragedHeightTest ((q : ℝ) + 1) w)
        (gammaOf (rho : ℂ) / T)‖ ≤
      dyadicRemoteHeightLeakageBound q := by
  let X : ℝ := (q : ℝ) + 1
  have hX : 0 < X := by dsimp [X]; positivity
  have hX1 : 1 ≤ X := by
    dsimp [X]
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hXpow : X ≤ X ^ 4 := by
    nlinarith [sq_nonneg (X - 1), mul_nonneg (sq_nonneg X) (sq_nonneg (X - 1))]
  have hT : 0 < T := lt_of_lt_of_le (pow_pos hX 4) hTpower
  have hXT : X ≤ 2 * T := by linarith
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hgap : X * dyadicRemoteHeightGap q = Real.sqrt X := by
    unfold dyadicRemoteHeightGap
    dsimp only [X]
    field_simp [hsqrt.ne']
    exact (Real.sq_sqrt hX.le).symm
  have hfirst : (X / T) * (X / baseHeightKernelMass) ≤
      baseHeightKernelMass⁻¹ * (X ^ 2)⁻¹ := by
    have hM : 0 < baseHeightKernelMass := baseHeightKernelMass_pos
    calc
      (X / T) * (X / baseHeightKernelMass) =
          X ^ 2 / (baseHeightKernelMass * T) := by field_simp
      _ ≤ X ^ 2 / (baseHeightKernelMass * X ^ 4) := by
        exact div_le_div_of_nonneg_left (sq_nonneg X)
          (mul_pos hM (pow_pos hX 4))
          (mul_le_mul_of_nonneg_left hTpower hM.le)
      _ = baseHeightKernelMass⁻¹ * (X ^ 2)⁻¹ := by
        field_simp [hM.ne', hX.ne']
  have hraw := norm_windowAveragedHeight_of_zero_outside_le
    (Z := Z) hX hw hw1 hT hXT (dyadicRemoteHeightGap_pos q) rho hout
  apply hraw.trans
  unfold dyadicRemoteHeightLeakageBound
  dsimp only [X] at hfirst hgap ⊢
  rw [hgap]
  exact add_le_add hfirst le_rfl

end RH.Zeta85.RSPoissonCyclicBridge
