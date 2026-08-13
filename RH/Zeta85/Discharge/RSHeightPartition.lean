import RH.Zeta85.Discharge.RSHeightProfileLimit

/-!
# Inner/edge/outer height partition

An outer compact profile is exactly one on the closed dyadic interval and
has a shrinking collar outside it.  Subtracting the usual inner dyadic
profile gives a nonnegative two-edge remainder with mass at most
`4*d + 2*w`.  This is the exact algebraic partition used to isolate the
height boundary without weakening the frozen dyadic window.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def outerHeightProfile (d x : ℝ) : ℝ :=
  (1 + 4 * d) * RH.Zeta85.RSReduction.smoothTopHat
    (1 + 4 * d) d (x - 3 / 2)

theorem outerHeightProfile_contDiff {d : ℝ} (hd : 0 < d) :
    ContDiff ℝ ∞ (outerHeightProfile d) := by
  unfold outerHeightProfile
  exact contDiff_const.mul
    ((RH.Zeta85.RSReduction.smoothTopHat_contDiff hd (by linarith)).comp
      (contDiff_id.sub contDiff_const))

theorem outerHeightProfile_support {d : ℝ} (hd : 0 < d) :
    Function.support (outerHeightProfile d) ⊆ Set.Icc (1 - 2 * d) (2 + 2 * d) := by
  intro x hx
  have hsmooth : RH.Zeta85.RSReduction.smoothTopHat
      (1 + 4 * d) d (x - 3 / 2) ≠ 0 := by
    intro hz
    apply hx
    simp [outerHeightProfile, hz]
  have hs := RH.Zeta85.RSReduction.smoothTopHat_support hd hsmooth
  simp only [RH.Zeta85.TopHatMoments.topHatSupport, Set.mem_Icc] at hs ⊢
  constructor <;> linarith [hs.1, hs.2]

theorem outerHeightProfile_hasCompactSupport {d : ℝ} (hd : 0 < d) :
    HasCompactSupport (outerHeightProfile d) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (outerHeightProfile_support hd)

theorem outerHeightProfile_nonneg {d x : ℝ} (hd : 0 < d) :
    0 ≤ outerHeightProfile d x := by
  unfold outerHeightProfile
  exact mul_nonneg (by linarith)
    (RH.Zeta85.RSReduction.smoothTopHat_nonneg (by linarith))

theorem outerHeightProfile_le_one {d x : ℝ} (hd : 0 < d) :
    outerHeightProfile d x ≤ 1 := by
  unfold outerHeightProfile
  have hs := RH.Zeta85.RSReduction.smoothTopHat_le
    (p := 1 + 4 * d) (w := d) (x := x - 3 / 2) (by linarith)
  calc
    (1 + 4 * d) * RH.Zeta85.RSReduction.smoothTopHat
        (1 + 4 * d) d (x - 3 / 2) ≤
      (1 + 4 * d) * (1 / (1 + 4 * d)) :=
        mul_le_mul_of_nonneg_left hs (by linarith)
    _ = 1 := by
      have hden : 1 + 4 * d ≠ 0 := by linarith
      field_simp [hden]

theorem outerHeightProfile_eq_one_of_mem_dyadic
    {d x : ℝ} (hd : 0 < d) (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    outerHeightProfile d x = 1 := by
  have habs : |x - 3 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  rw [outerHeightProfile,
    RH.Zeta85.RSReduction.smoothTopHat_eq_topHat_of_inner
      (p := 1 + 4 * d) (by linarith) hd (by
        apply habs.trans
        linarith)]
  have hsupp : x - 3 / 2 ∈
      RH.Zeta85.TopHatMoments.topHatSupport (1 + 4 * d) := by
    simp only [RH.Zeta85.TopHatMoments.topHatSupport, Set.mem_Icc]
    rw [abs_le] at habs
    constructor <;> linarith [habs.1, habs.2]
  simp [RH.Zeta85.TopHatMoments.topHat, hsupp]
  have hden : 1 + 4 * d ≠ 0 := by linarith
  field_simp [hden]

theorem outerHeightProfile_integrable {d : ℝ} (hd : 0 < d) :
    Integrable (outerHeightProfile d) :=
  (outerHeightProfile_contDiff hd).continuous.integrable_of_hasCompactSupport
    (outerHeightProfile_hasCompactSupport hd)

theorem integral_outerHeightProfile_le {d : ℝ} (hd : 0 < d) :
    (∫ x, outerHeightProfile d x) ≤ 1 + 4 * d := by
  let I : ℝ → ℝ :=
    (Set.Icc (1 - 2 * d) (2 + 2 * d)).indicator (fun _ => (1 : ℝ))
  have hIint : Integrable I := by
    unfold I
    exact (integrableOn_const (s := Set.Icc (1 - 2 * d) (2 + 2 * d))
      (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  have hpoint : ∀ x, outerHeightProfile d x ≤ I x := by
    intro x
    by_cases hx : x ∈ Set.Icc (1 - 2 * d) (2 + 2 * d)
    · simp only [I, Set.indicator_of_mem hx]
      exact outerHeightProfile_le_one hd
    · simp only [I, Set.indicator_of_notMem hx]
      have hz : outerHeightProfile d x = 0 := by
        by_contra hne
        exact hx (outerHeightProfile_support hd hne)
      rw [hz]
  have hmono := integral_mono (outerHeightProfile_integrable hd) hIint hpoint
  have hI : ∫ x, I x = 1 + 4 * d := by
    unfold I
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rwa [hI] at hmono

theorem integral_smoothHeightWindow_ge
    {w : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    1 - 2 * w ≤ ∫ x, smoothHeightWindow w x := by
  let I : ℝ → ℝ :=
    (Set.Icc (1 + w) (2 - w)).indicator (fun _ => (1 : ℝ))
  have hIint : Integrable I := by
    unfold I
    exact (integrableOn_const (s := Set.Icc (1 + w) (2 - w))
      (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  have hHint := smoothHeightWindow_integrable hw hw1
  have hpoint : ∀ x, I x ≤ smoothHeightWindow w x := by
    intro x
    by_cases hx : x ∈ Set.Icc (1 + w) (2 - w)
    · simp only [I, Set.indicator_of_mem hx]
      have hinner : |x - 3 / 2| ≤ 1 / 2 - w := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      rw [smoothHeightWindow_eq_one_of_inner hw hinner]
    · simp only [I, Set.indicator_of_notMem hx]
      exact smoothHeightWindow_nonneg
  have hmono := integral_mono hIint hHint hpoint
  have hI : ∫ x, I x = 1 - 2 * w := by
    unfold I
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rwa [hI] at hmono

def dyadicEdgeRemainder (d w x : ℝ) : ℝ :=
  outerHeightProfile d x - smoothHeightWindow w x

theorem outerHeightProfile_eq_smooth_add_edge (d w x : ℝ) :
    outerHeightProfile d x = smoothHeightWindow w x + dyadicEdgeRemainder d w x := by
  unfold dyadicEdgeRemainder
  ring

theorem dualHeightProfile_add
    {H K : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    (hK : Continuous K) (hKc : HasCompactSupport K) (u : ℝ) :
    dualHeightProfile (H + K) u = dualHeightProfile H u + dualHeightProfile K u := by
  unfold dualHeightProfile paperFT
  have hHi : Integrable (fun x : ℝ => (H x : ℂ) *
      Complex.exp (Complex.I * (-u : ℂ) * (x : ℂ))) :=
    ((Complex.continuous_ofReal.comp hH).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hHc.comp_left Complex.ofReal_zero).mul_right)
  have hKi : Integrable (fun x : ℝ => (K x : ℂ) *
      Complex.exp (Complex.I * (-u : ℂ) * (x : ℂ))) :=
    ((Complex.continuous_ofReal.comp hK).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hKc.comp_left Complex.ofReal_zero).mul_right)
  rw [show (fun x : ℝ => ((H + K) x : ℂ) *
      Complex.exp (Complex.I * (-u : ℂ) * (x : ℂ))) =
      fun x => (H x : ℂ) * Complex.exp (Complex.I * (-u : ℂ) * (x : ℂ)) +
        (K x : ℂ) * Complex.exp (Complex.I * (-u : ℂ) * (x : ℂ)) by
        funext x
        simp only [Pi.add_apply]
        push_cast
        ring]
  exact integral_add hHi hKi

theorem averagedHeightTestOf_add
    {H K : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    (hK : Continuous K) (hKc : HasCompactSupport K) (R u : ℝ) :
    averagedHeightTestOf (H + K) R u =
      averagedHeightTestOf H R u + averagedHeightTestOf K R u := by
  unfold averagedHeightTestOf
  rw [dualHeightProfile_add hH hHc hK hKc]
  ring

theorem dyadicEdgeRemainder_continuous
    {d w : ℝ} (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    Continuous (dyadicEdgeRemainder d w) :=
  (outerHeightProfile_contDiff hd).continuous.sub
    (smoothHeightWindow_contDiff hw hw1).continuous

theorem dyadicEdgeRemainder_hasCompactSupport
    {d w : ℝ} (hd : 0 < d) (hw : 0 < w) :
    HasCompactSupport (dyadicEdgeRemainder d w) := by
  unfold dyadicEdgeRemainder
  exact (outerHeightProfile_hasCompactSupport hd).sub
    (smoothHeightWindow_hasCompactSupport hw)

theorem averagedHeightTestOf_outer_eq_core_add_edge
    {d w : ℝ} (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (R u : ℝ) :
    averagedHeightTestOf (outerHeightProfile d) R u =
      averagedHeightTestOf (smoothHeightWindow w) R u +
        averagedHeightTestOf (dyadicEdgeRemainder d w) R u := by
  have hfun : outerHeightProfile d =
      smoothHeightWindow w + dyadicEdgeRemainder d w := by
    funext x
    exact outerHeightProfile_eq_smooth_add_edge d w x
  rw [hfun, averagedHeightTestOf_add
    (smoothHeightWindow_contDiff hw hw1).continuous
    (smoothHeightWindow_hasCompactSupport hw)
    (dyadicEdgeRemainder_continuous hd hw hw1)
    (dyadicEdgeRemainder_hasCompactSupport hd hw)]

theorem paperFT_add_of_continuous_compact
    {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (f + g) z = paperFT f z + paperFT g z := by
  unfold paperFT
  have hfi : Integrable (fun x : ℝ => f x *
      Complex.exp (Complex.I * z * (x : ℂ))) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hgi : Integrable (fun x : ℝ => g x *
      Complex.exp (Complex.I * z * (x : ℂ))) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  rw [show (fun x : ℝ => (f + g) x *
      Complex.exp (Complex.I * z * (x : ℂ))) =
      fun x => f x * Complex.exp (Complex.I * z * (x : ℂ)) +
        g x * Complex.exp (Complex.I * z * (x : ℂ)) by
        funext x
        simp only [Pi.add_apply]
        ring]
  exact integral_add hfi hgi

theorem paperFT_averagedHeightTestOf_outer_eq_core_add_edge
    {d w R : ℝ} (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hR : 0 < R) (z : ℂ) :
    paperFT (averagedHeightTestOf (outerHeightProfile d) R) z =
      paperFT (averagedHeightTestOf (smoothHeightWindow w) R) z +
        paperFT (averagedHeightTestOf (dyadicEdgeRemainder d w) R) z := by
  have heq : averagedHeightTestOf (outerHeightProfile d) R =
      averagedHeightTestOf (smoothHeightWindow w) R +
        averagedHeightTestOf (dyadicEdgeRemainder d w) R := by
    funext u
    exact averagedHeightTestOf_outer_eq_core_add_edge hd hw hw1 R u
  rw [heq]
  exact paperFT_add_of_continuous_compact
    (averagedHeightTestOf_contDiff
      (smoothHeightWindow_contDiff hw hw1).continuous
      (smoothHeightWindow_hasCompactSupport hw) hR).continuous
    (averagedHeightTestOf_hasCompactSupport _ hR)
    (averagedHeightTestOf_contDiff
      (dyadicEdgeRemainder_continuous hd hw hw1)
      (dyadicEdgeRemainder_hasCompactSupport hd hw) hR).continuous
    (averagedHeightTestOf_hasCompactSupport _ hR) z

def replaceHeightProfile {n : ℕ} (B : Fin (n + 1) → ℝ → ℝ)
    (i : Fin (n + 1)) (K : ℝ → ℝ) : Fin (n + 1) → ℝ → ℝ :=
  fun j => if j = i then K else B j

theorem rsZeroTupleTerm_replace_outer_eq_core_add_edge
    {Z : ZeroConfig} {n : ℕ} {B : Fin (n + 1) → ℝ → ℝ}
    (i : Fin (n + 1)) {d w R T : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (hR : 0 < R)
    (Phi : (Fin (n + 1) → ℝ) → ℂ)
    (rho : Fin (n + 1) → Z.carrier) :
    rsZeroTupleTerm Z
        (averagedHeightFamilyOf
          (replaceHeightProfile B i (outerHeightProfile d)) R) Phi T rho =
      rsZeroTupleTerm Z
        (averagedHeightFamilyOf
          (replaceHeightProfile B i (smoothHeightWindow w)) R) Phi T rho +
      rsZeroTupleTerm Z
        (averagedHeightFamilyOf
          (replaceHeightProfile B i (dyadicEdgeRemainder d w)) R) Phi T rho := by
  unfold rsZeroTupleTerm averagedHeightFamilyOf replaceHeightProfile
  let f : Fin (n + 1) → ℂ := fun j =>
    (Z.mult (rho j) : ℂ) * paperFT
      (averagedHeightTestOf (if j = i then outerHeightProfile d else B j) R)
      (gammaOf (rho j) / T)
  let g : Fin (n + 1) → ℂ := fun j =>
    (Z.mult (rho j) : ℂ) * paperFT
      (averagedHeightTestOf (if j = i then smoothHeightWindow w else B j) R)
      (gammaOf (rho j) / T)
  let h : Fin (n + 1) → ℂ := fun j =>
    (Z.mult (rho j) : ℂ) * paperFT
      (averagedHeightTestOf (if j = i then dyadicEdgeRemainder d w else B j) R)
      (gammaOf (rho j) / T)
  have hi : g i + h i = f i := by
    simp only [f, g, h, if_pos]
    rw [paperFT_averagedHeightTestOf_outer_eq_core_add_edge
      hd hw hw1 hR]
    ring
  have hg : ∀ j ∈ Finset.univ, j ≠ i → g j = f j := by
    intro j hj hji
    simp only [f, g, if_neg hji]
  have hh : ∀ j ∈ Finset.univ, j ≠ i → h j = f j := by
    intro j hj hji
    simp only [f, h, if_neg hji]
  have hprod := Finset.prod_add_prod_eq (s := Finset.univ) (i := i)
    (f := f) (g := g) (h := h) (Finset.mem_univ i) hi hg hh
  change (∏ j, f j) * _ = (∏ j, g j) * _ + (∏ j, h j) * _
  rw [← add_mul, hprod]

theorem dyadicEdgeRemainder_nonneg
    {d w x : ℝ} (hd : 0 < d) (hw : 0 < w) :
    0 ≤ dyadicEdgeRemainder d w x := by
  unfold dyadicEdgeRemainder
  by_cases hzero : smoothHeightWindow w x = 0
  · rw [hzero, sub_zero]
    exact outerHeightProfile_nonneg hd
  · have hs := RH.Zeta85.RSReduction.smoothTopHat_support
      (p := (1 : ℝ)) hw hzero
    have hx : x ∈ Set.Icc (1 : ℝ) 2 := by
      simp only [RH.Zeta85.TopHatMoments.topHatSupport, Set.mem_Icc] at hs ⊢
      constructor <;> linarith [hs.1, hs.2]
    rw [outerHeightProfile_eq_one_of_mem_dyadic hd hx]
    linarith [smoothHeightWindow_le_one (w := w) (x := x)]

theorem dyadicEdgeRemainder_le_one
    {d w x : ℝ} (hd : 0 < d) :
    dyadicEdgeRemainder d w x ≤ 1 := by
  unfold dyadicEdgeRemainder
  linarith [outerHeightProfile_le_one (x := x) hd,
    smoothHeightWindow_nonneg (w := w) (x := x)]

theorem integral_dyadicEdgeRemainder_le
    {d w : ℝ} (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    (∫ x, dyadicEdgeRemainder d w x) ≤ 4 * d + 2 * w := by
  unfold dyadicEdgeRemainder
  rw [integral_sub
    (outerHeightProfile_integrable hd) (smoothHeightWindow_integrable hw hw1)]
  linarith [integral_outerHeightProfile_le hd,
    integral_smoothHeightWindow_ge hw hw1]

def mixedDyadicEdgeRemainderProfiles {n : ℕ} (i : Fin (n + 1))
    (d w : ℝ) : Fin (n + 1) → ℝ → ℝ :=
  fun j => if j = i then dyadicEdgeRemainder d w else smoothHeightWindow w

theorem norm_rsHeightFactor_mixedDyadicEdgeRemainderProfiles_le
    {n : ℕ} {i : Fin (n + 1)} {d w R : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (hR : 0 < R) :
    ‖RH.Zeta85.rsHeightFactor
      (averagedHeightFamilyOf (mixedDyadicEdgeRemainderProfiles i d w) R)‖ ≤
        4 * d + 2 * w := by
  let H := mixedDyadicEdgeRemainderProfiles i d w
  have hH : ∀ j, Continuous (H j) := by
    intro j
    by_cases hji : j = i
    · simp only [H, mixedDyadicEdgeRemainderProfiles, hji, if_true]
      exact dyadicEdgeRemainder_continuous hd hw hw1
    · simp only [H, mixedDyadicEdgeRemainderProfiles, hji, if_false]
      exact (smoothHeightWindow_contDiff hw hw1).continuous
  have hHc : ∀ j, HasCompactSupport (H j) := by
    intro j
    by_cases hji : j = i
    · simp only [H, mixedDyadicEdgeRemainderProfiles, hji, if_true]
      exact dyadicEdgeRemainder_hasCompactSupport hd hw
    · simp only [H, mixedDyadicEdgeRemainderProfiles, hji, if_false]
      exact smoothHeightWindow_hasCompactSupport hw
  have hH0 : ∀ j x, 0 ≤ H j x := by
    intro j x
    by_cases hji : j = i
    · simp only [H, mixedDyadicEdgeRemainderProfiles, hji, if_true]
      exact dyadicEdgeRemainder_nonneg hd hw
    · simp only [H, mixedDyadicEdgeRemainderProfiles, hji, if_false]
      exact smoothHeightWindow_nonneg
  have hH1 : ∀ j x, H j x ≤ 1 := by
    intro j x
    by_cases hji : j = i
    · simp only [H, mixedDyadicEdgeRemainderProfiles, hji, if_true]
      exact dyadicEdgeRemainder_le_one hd
    · simp only [H, mixedDyadicEdgeRemainderProfiles, hji, if_false]
      exact smoothHeightWindow_le_one
  refine (norm_rsHeightFactor_averagedHeightFamilyOf_le_integral
    hH hHc hH0 hH1 hR i).trans ?_
  simpa only [H, mixedDyadicEdgeRemainderProfiles, if_pos] using
    integral_dyadicEdgeRemainder_le hd hw hw1

end RH.Zeta85.RSPoissonCyclicBridge
