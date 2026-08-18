import RH.Zeta85.Discharge.RSHeightProfiles

/-!
# Coordinate-localized height profiles

A narrow nonnegative profile is placed at either dyadic edge.  Its value is
one on the prescribed edge band, while its total mass is at most four times
the band width.  The mixed-profile height-factor bound then makes every
Rudnick--Sarnak tuple family carrying that coordinate uniformly small.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def edgeHeightProfile (d c x : ℝ) : ℝ :=
  (4 * d) * RH.Zeta85.RSReduction.smoothTopHat (4 * d) d (x - c)

theorem edgeHeightProfile_contDiff {d c : ℝ} (hd : 0 < d) :
    ContDiff ℝ ∞ (edgeHeightProfile d c) := by
  unfold edgeHeightProfile
  exact contDiff_const.mul
    ((RH.Zeta85.RSReduction.smoothTopHat_contDiff
      (p := 4 * d) hd (by linarith)).comp (contDiff_id.sub contDiff_const))

theorem edgeHeightProfile_support {d c : ℝ} (hd : 0 < d) :
    Function.support (edgeHeightProfile d c) ⊆ Set.Icc (c - 2 * d) (c + 2 * d) := by
  intro x hx
  have hsmooth : RH.Zeta85.RSReduction.smoothTopHat (4 * d) d (x - c) ≠ 0 := by
    intro hz
    apply hx
    simp [edgeHeightProfile, hz]
  have hs := RH.Zeta85.RSReduction.smoothTopHat_support
    (p := 4 * d) hd hsmooth
  simp only [RH.Zeta85.TopHatMoments.topHatSupport, Set.mem_Icc] at hs ⊢
  constructor <;> linarith [hs.1, hs.2]

theorem edgeHeightProfile_hasCompactSupport {d c : ℝ} (hd : 0 < d) :
    HasCompactSupport (edgeHeightProfile d c) := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (edgeHeightProfile_support hd)

theorem edgeHeightProfile_nonneg {d c x : ℝ} (hd : 0 < d) :
    0 ≤ edgeHeightProfile d c x := by
  unfold edgeHeightProfile
  exact mul_nonneg (by positivity)
    (RH.Zeta85.RSReduction.smoothTopHat_nonneg (p := 4 * d) (by positivity))

theorem edgeHeightProfile_le_one {d c x : ℝ} (hd : 0 < d) :
    edgeHeightProfile d c x ≤ 1 := by
  unfold edgeHeightProfile
  have hs := RH.Zeta85.RSReduction.smoothTopHat_le
    (p := 4 * d) (w := d) (x := x - c) (by positivity)
  calc
    (4 * d) * RH.Zeta85.RSReduction.smoothTopHat (4 * d) d (x - c) ≤
        (4 * d) * (1 / (4 * d)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 1 := by field_simp

theorem edgeHeightProfile_eq_one_of_mem_band
    {d c x : ℝ} (hd : 0 < d) (hx : |x - c| ≤ d) :
    edgeHeightProfile d c x = 1 := by
  rw [edgeHeightProfile,
    RH.Zeta85.RSReduction.smoothTopHat_eq_topHat_of_inner
      (p := 4 * d) (by positivity) hd (by convert hx using 1 <;> ring)]
  have hsupp : x - c ∈ RH.Zeta85.TopHatMoments.topHatSupport (4 * d) := by
    simp only [RH.Zeta85.TopHatMoments.topHatSupport, Set.mem_Icc]
    rw [abs_le] at hx
    constructor <;> linarith [hx.1, hx.2]
  simp [RH.Zeta85.TopHatMoments.topHat, hsupp]
  field_simp

theorem edgeHeightProfile_integrable {d c : ℝ} (hd : 0 < d) :
    Integrable (edgeHeightProfile d c) :=
  (edgeHeightProfile_contDiff hd).continuous.integrable_of_hasCompactSupport
    (edgeHeightProfile_hasCompactSupport hd)

theorem integral_edgeHeightProfile_le {d c : ℝ} (hd : 0 < d) :
    (∫ x, edgeHeightProfile d c x) ≤ 4 * d := by
  let I : ℝ → ℝ :=
    (Set.Icc (c - 2 * d) (c + 2 * d)).indicator (fun _ => (1 : ℝ))
  have hIint : Integrable I := by
    unfold I
    exact (integrableOn_const (s := Set.Icc (c - 2 * d) (c + 2 * d))
      (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  have hpoint : ∀ x, edgeHeightProfile d c x ≤ I x := by
    intro x
    by_cases hx : x ∈ Set.Icc (c - 2 * d) (c + 2 * d)
    · simp only [I, Set.indicator_of_mem hx]
      exact edgeHeightProfile_le_one hd
    · simp only [I, Set.indicator_of_notMem hx]
      have hzero : edgeHeightProfile d c x = 0 := by
        by_contra hne
        exact hx (edgeHeightProfile_support hd hne)
      rw [hzero]
  have hmono := integral_mono (edgeHeightProfile_integrable hd) hIint hpoint
  have hI : ∫ x, I x = 4 * d := by
    unfold I
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rwa [hI] at hmono

def mixedEdgeHeightProfiles {n : ℕ} (i : Fin (n + 1))
    (d c w : ℝ) : Fin (n + 1) → ℝ → ℝ :=
  fun j => if j = i then edgeHeightProfile d c else smoothHeightWindow w

theorem mixedEdgeHeightProfiles_continuous
    {n : ℕ} {i : Fin (n + 1)} {d c w : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (j : Fin (n + 1)) :
    Continuous (mixedEdgeHeightProfiles i d c w j) := by
  by_cases hji : j = i
  · simp only [mixedEdgeHeightProfiles, hji, if_true]
    exact (edgeHeightProfile_contDiff hd).continuous
  · simp only [mixedEdgeHeightProfiles, hji, if_false]
    exact (smoothHeightWindow_contDiff hw hw1).continuous

theorem mixedEdgeHeightProfiles_hasCompactSupport
    {n : ℕ} {i : Fin (n + 1)} {d c w : ℝ}
    (hd : 0 < d) (hw : 0 < w) (j : Fin (n + 1)) :
    HasCompactSupport (mixedEdgeHeightProfiles i d c w j) := by
  by_cases hji : j = i
  · simp only [mixedEdgeHeightProfiles, hji, if_true]
    exact edgeHeightProfile_hasCompactSupport hd
  · simp only [mixedEdgeHeightProfiles, hji, if_false]
    exact smoothHeightWindow_hasCompactSupport hw

theorem mixedEdgeHeightProfiles_nonneg
    {n : ℕ} {i : Fin (n + 1)} {d c w : ℝ}
    (hd : 0 < d) (j : Fin (n + 1)) (x : ℝ) :
    0 ≤ mixedEdgeHeightProfiles i d c w j x := by
  by_cases hji : j = i
  · simp only [mixedEdgeHeightProfiles, hji, if_true]
    exact edgeHeightProfile_nonneg hd
  · simp only [mixedEdgeHeightProfiles, hji, if_false]
    exact smoothHeightWindow_nonneg

theorem mixedEdgeHeightProfiles_le_one
    {n : ℕ} {i : Fin (n + 1)} {d c w : ℝ}
    (hd : 0 < d) (j : Fin (n + 1)) (x : ℝ) :
    mixedEdgeHeightProfiles i d c w j x ≤ 1 := by
  by_cases hji : j = i
  · simp only [mixedEdgeHeightProfiles, hji, if_true]
    exact edgeHeightProfile_le_one hd
  · simp only [mixedEdgeHeightProfiles, hji, if_false]
    exact smoothHeightWindow_le_one

theorem norm_rsHeightFactor_mixedEdgeHeightProfiles_le
    {n : ℕ} {i : Fin (n + 1)} {d c w R : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (hR : 0 < R) :
    ‖RH.Zeta85.rsHeightFactor
      (averagedHeightFamilyOf (mixedEdgeHeightProfiles i d c w) R)‖ ≤ 4 * d := by
  refine (norm_rsHeightFactor_averagedHeightFamilyOf_le_integral
    (fun j => mixedEdgeHeightProfiles_continuous hd hw hw1 j)
    (fun j => mixedEdgeHeightProfiles_hasCompactSupport hd hw j)
    (fun j x => mixedEdgeHeightProfiles_nonneg hd j x)
    (fun j x => mixedEdgeHeightProfiles_le_one hd j x) hR i).trans ?_
  simpa [mixedEdgeHeightProfiles] using integral_edgeHeightProfile_le (d := d) (c := c) hd

end RH.Zeta85.RSPoissonCyclicBridge
