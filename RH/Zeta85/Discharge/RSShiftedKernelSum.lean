import RH.Zeta85.Discharge.RSCyclicRemoteLift

/-!
# Shifted zero-count sums for the cyclic Fourier kernel

The cyclic row estimate is centered at the ordinate of an arbitrary zero,
not at an endpoint of the physical height window.  This file groups the two
tails into unit ordinate windows around that moving center.
-/

open Filter Topology Finset Real MeasureTheory
open scoped BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def shiftedTailCubicWindowBound (x : ℝ) : ℝ :=
  (3 / 8 : ℝ) * Real.log (|x| + 5) + 1 / (|x| + 5)

theorem shifted_tail_cubic_sum_le
    {ι : Type*} {gamma : ι → ℝ} {mult : ι → ℕ} {A0 x : ℝ}
    (hcount : Tail.LocalCount gamma mult A0)
    (s : Finset ι)
    (hs : ∀ rho ∈ s,
      gamma rho ≤ x - 2 ∨ x + 2 ≤ gamma rho) :
    ∑ rho ∈ s, (mult rho : ℝ) * |gamma rho - x| ^ (-3 : ℤ) ≤
      2 * A0 * shiftedTailCubicWindowBound x := by
  classical
  have hA0 : 0 ≤ A0 := hcount.A₀_pos.le
  let B : ℝ := |x| + 5
  have hB : 1 ≤ B := by dsimp only [B]; linarith [abs_nonneg x]
  let slo : Finset ι := s.filter fun rho => gamma rho ≤ x - 2
  let shi : Finset ι := s.filter fun rho => ¬ gamma rho ≤ x - 2
  have hhiMem : ∀ rho ∈ shi, x + 2 ≤ gamma rho := by
    intro rho hrho
    simp only [shi, Finset.mem_filter] at hrho
    rcases hs rho hrho.1 with hlo | hhi
    · exact absurd hlo hrho.2
    · exact hhi
  have hlogmono : ∀ (t : ℝ) (j : ℕ), |t| + 3 ≤ B + j →
      A0 * Real.log (|t| + 3) ≤ A0 * Real.log (B + j) := by
    intro t j ht
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) ht) hA0
  have hlo :
      ∑ rho ∈ slo, (mult rho : ℝ) * |gamma rho - x| ^ (-3 : ℤ) ≤
        A0 * shiftedTailCubicWindowBound x := by
    have hmem : ∀ rho ∈ slo, gamma rho ≤ x - 2 := by
      intro rho hrho
      exact (Finset.mem_filter.mp hrho).2
    have heq : ∀ rho ∈ slo,
        (mult rho : ℝ) * |gamma rho - x| ^ (-3 : ℤ) =
          (mult rho : ℝ) * ((x - gamma rho) ^ 3)⁻¹ := by
      intro rho hrho
      rw [abs_of_nonpos (by linarith [hmem rho hrho])]
      norm_num [zpow_neg]
    rw [Finset.sum_congr rfl heq]
    unfold shiftedTailCubicWindowBound
    have hraw := Tail.one_side_sum_le slo
      (fun rho => x - gamma rho) mult
      (fun rho => ⌊x - gamma rho⌋₊)
      (D₀ := (2 : ℝ)) hA0 hB (by norm_num)
      (by
        intro rho hrho
        linarith [hmem rho hrho])
      (by
        intro rho hrho
        exact Nat.floor_le (by linarith [hmem rho hrho]))
      (by
        intro rho hrho
        exact (Nat.lt_floor_add_one _).le)
      (by
        intro j
        refine (hcount.window (x - j - 1) _ ?_).trans
          (hlogmono (x - j - 1) j ?_)
        · intro rho hrho
          rw [Finset.mem_filter] at hrho
          obtain ⟨hrhos, hrhoj⟩ := hrho
          have hnonneg : 0 ≤ x - gamma rho := by
            linarith [hmem rho hrhos]
          have hj := (Nat.floor_eq_iff hnonneg).mp hrhoj
          constructor <;> linarith [hj.1, hj.2]
        · have habs : |x - j - 1| ≤ |x| + j + 1 := by
            calc
              |x - j - 1| = |x + (-((j : ℝ) + 1))| := by
                congr 1
                ring
              _ ≤ |x| + |-((j : ℝ) + 1)| := abs_add_le _ _
              _ = |x| + |(j : ℝ) + 1| := by rw [abs_neg]
              _ = |x| + j + 1 := by
                have hj0 : 0 ≤ (j : ℝ) + 1 := by positivity
                rw [abs_of_nonneg hj0]
                ring
          dsimp only [B]
          push_cast
          linarith)
    dsimp only [B] at hraw
    norm_num at hraw ⊢
    exact hraw
  have hhi :
      ∑ rho ∈ shi, (mult rho : ℝ) * |gamma rho - x| ^ (-3 : ℤ) ≤
        A0 * shiftedTailCubicWindowBound x := by
    have heq : ∀ rho ∈ shi,
        (mult rho : ℝ) * |gamma rho - x| ^ (-3 : ℤ) =
          (mult rho : ℝ) * ((gamma rho - x) ^ 3)⁻¹ := by
      intro rho hrho
      rw [abs_of_nonneg (by linarith [hhiMem rho hrho])]
      norm_num [zpow_neg]
    rw [Finset.sum_congr rfl heq]
    have hceil1 : ∀ rho ∈ shi, 1 ≤ ⌈gamma rho - x⌉₊ := by
      intro rho hrho
      exact Nat.one_le_ceil_iff.mpr (by linarith [hhiMem rho hrho])
    have hcast : ∀ rho ∈ shi,
        (((⌈gamma rho - x⌉₊ - 1 : ℕ) : ℝ)) =
          ⌈gamma rho - x⌉₊ - 1 := by
      intro rho hrho
      rw [Nat.cast_sub (hceil1 rho hrho)]
      simp
    unfold shiftedTailCubicWindowBound
    have hraw := Tail.one_side_sum_le shi
      (fun rho => gamma rho - x) mult
      (fun rho => ⌈gamma rho - x⌉₊ - 1)
      (D₀ := (2 : ℝ)) hA0 hB (by norm_num)
      (by
        intro rho hrho
        linarith [hhiMem rho hrho])
      (by
        intro rho hrho
        rw [hcast rho hrho]
        have hc := Nat.ceil_lt_add_one
          (show 0 ≤ gamma rho - x by linarith [hhiMem rho hrho])
        linarith)
      (by
        intro rho hrho
        rw [hcast rho hrho]
        have hc := Nat.le_ceil (gamma rho - x)
        linarith)
      (by
        intro j
        refine (hcount.window (x + j) _ ?_).trans
          (hlogmono (x + j) j ?_)
        · intro rho hrho
          rw [Finset.mem_filter] at hrho
          obtain ⟨hrhos, hrhoj⟩ := hrho
          have hc : ⌈gamma rho - x⌉₊ = j + 1 := by
            have hone := hceil1 rho hrhos
            omega
          have hj := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
          push_cast at hj
          constructor <;> linarith [hj.1, hj.2]
        · have habs : |x + j| ≤ |x| + j := by
            calc
              |x + j| ≤ |x| + |(j : ℝ)| := abs_add_le _ _
              _ = |x| + j := by
                have hj0 : 0 ≤ (j : ℝ) := by positivity
                rw [abs_of_nonneg hj0]
          dsimp only [B]
          push_cast
          linarith)
    dsimp only [B] at hraw
    norm_num at hraw ⊢
    exact hraw
  rw [← Finset.sum_filter_add_sum_filter_not s
    (fun rho => gamma rho ≤ x - 2)]
  simpa only [slo, shi] using
    (add_le_add hlo hhi).trans_eq (by ring)

theorem shifted_tail_quartic_kernel_sum_le
    {ι : Type*} {gamma : ι → ℝ} {mult : ι → ℕ}
    {A0 x L : ℝ}
    (hcount : Tail.LocalCount gamma mult A0) (hL : 1 ≤ L)
    (s : Finset ι)
    (hs : ∀ rho ∈ s,
      gamma rho ≤ x - 2 ∨ x + 2 ≤ gamma rho) :
    ∑ rho ∈ s, (mult rho : ℝ) *
        (1 + (L * (gamma rho - x)) ^ 4)⁻¹ ≤
      2 * A0 * shiftedTailCubicWindowBound x := by
  have hpoint : ∀ rho ∈ s,
      (1 + (L * (gamma rho - x)) ^ 4)⁻¹ ≤
        |gamma rho - x| ^ (-3 : ℤ) := by
    intro rho hrho
    have hd : 2 ≤ |gamma rho - x| := by
      rcases hs rho hrho with hlo | hhi
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith
    have hdpos : 0 < |gamma rho - x| := by linarith
    have hLabs : |gamma rho - x| ≤ |L * (gamma rho - x)| := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ L)]
      nlinarith [abs_nonneg (gamma rho - x)]
    have hfour : |gamma rho - x| ^ 4 ≤
        (L * (gamma rho - x)) ^ 4 := by
      calc
        |gamma rho - x| ^ 4 ≤ |L * (gamma rho - x)| ^ 4 :=
          pow_le_pow_left₀ (abs_nonneg _) hLabs 4
        _ = (L * (gamma rho - x)) ^ 4 := by
          rw [show |L * (gamma rho - x)| ^ 4 =
            (L * (gamma rho - x)) ^ 4 by
              calc
                |L * (gamma rho - x)| ^ 4 =
                    (|L * (gamma rho - x)| ^ 2) ^ 2 := by ring
                _ = ((L * (gamma rho - x)) ^ 2) ^ 2 := by rw [sq_abs]
                _ = (L * (gamma rho - x)) ^ 4 := by ring]
    have hcubic : |gamma rho - x| ^ 3 ≤
        1 + (L * (gamma rho - x)) ^ 4 := by
      have h34 : |gamma rho - x| ^ 3 ≤ |gamma rho - x| ^ 4 := by
        nlinarith [mul_nonneg (pow_nonneg hdpos.le 3)
          (sub_nonneg.mpr (by linarith : 1 ≤ |gamma rho - x|))]
      linarith [h34, hfour]
    exact inv_anti₀ (pow_pos hdpos 3) hcubic
  calc
    ∑ rho ∈ s, (mult rho : ℝ) *
          (1 + (L * (gamma rho - x)) ^ 4)⁻¹ ≤
        ∑ rho ∈ s, (mult rho : ℝ) *
          |gamma rho - x| ^ (-3 : ℤ) := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact mul_le_mul_of_nonneg_left (hpoint rho hrho) (Nat.cast_nonneg _)
    _ ≤ 2 * A0 * shiftedTailCubicWindowBound x :=
      shifted_tail_cubic_sum_le hcount s hs

theorem shifted_central_count_le
    {ι : Type*} {gamma : ι → ℝ} {mult : ι → ℕ}
    {A0 x : ℝ}
    (hcount : Tail.LocalCount gamma mult A0)
    (s : Finset ι)
    (hs : ∀ rho ∈ s, x - 2 < gamma rho ∧ gamma rho ≤ x + 2) :
    ∑ rho ∈ s, (mult rho : ℝ) ≤
      4 * A0 * Real.log (|x| + 5) := by
  classical
  have hA0 : 0 ≤ A0 := hcount.A₀_pos.le
  let B : ℝ := |x| + 5
  have hBpos : 0 < B := by dsimp only [B]; linarith [abs_nonneg x]
  have hlogmono : ∀ t : ℝ, |t - x| ≤ 2 →
      A0 * Real.log (|t| + 3) ≤ A0 * Real.log B := by
    intro t ht
    have habs : |t| ≤ |x| + 2 := by
      calc
        |t| = |x + (t - x)| := by congr 1 <;> ring
        _ ≤ |x| + |t - x| := abs_add_le _ _
        _ ≤ |x| + 2 := by linarith
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (by dsimp only [B]; linarith)) hA0
  let s0 : Finset ι := s.filter fun rho => gamma rho ≤ x - 1
  let r0 : Finset ι := s.filter fun rho => ¬ gamma rho ≤ x - 1
  let s1 : Finset ι := r0.filter fun rho => gamma rho ≤ x
  let r1 : Finset ι := r0.filter fun rho => ¬ gamma rho ≤ x
  let s2 : Finset ι := r1.filter fun rho => gamma rho ≤ x + 1
  let s3 : Finset ι := r1.filter fun rho => ¬ gamma rho ≤ x + 1
  have h0 : ∑ rho ∈ s0, (mult rho : ℝ) ≤
      A0 * Real.log B := by
    refine (hcount.window (x - 2) s0 ?_).trans
      (hlogmono (x - 2) (by rw [abs_of_nonpos (by norm_num)]; norm_num))
    intro rho hrho
    have hr := (Finset.mem_filter.mp hrho)
    have hsr := hs rho hr.1
    constructor <;> linarith [hr.2, hsr.1]
  have h1 : ∑ rho ∈ s1, (mult rho : ℝ) ≤
      A0 * Real.log B := by
    refine (hcount.window (x - 1) s1 ?_).trans
      (hlogmono (x - 1) (by rw [abs_of_nonpos (by norm_num)]; norm_num))
    intro rho hrho
    simp only [s1, r0, Finset.mem_filter] at hrho
    constructor <;> linarith [hrho.1.2, hrho.2]
  have h2 : ∑ rho ∈ s2, (mult rho : ℝ) ≤
      A0 * Real.log B := by
    refine (hcount.window x s2 ?_).trans
      (hlogmono x (by simp))
    intro rho hrho
    simp only [s2, r1, r0, Finset.mem_filter] at hrho
    constructor <;> linarith [hrho.1.2, hrho.2]
  have h3 : ∑ rho ∈ s3, (mult rho : ℝ) ≤
      A0 * Real.log B := by
    refine (hcount.window (x + 1) s3 ?_).trans
      (hlogmono (x + 1) (by rw [abs_of_nonneg (by norm_num)]; norm_num))
    intro rho hrho
    simp only [s3, r1, r0, Finset.mem_filter] at hrho
    have hsr := hs rho hrho.1.1.1
    constructor <;> linarith [hrho.2, hsr.2]
  have hsplit0 :
      (∑ rho ∈ s, (mult rho : ℝ)) =
        (∑ rho ∈ s0, (mult rho : ℝ)) +
          ∑ rho ∈ r0, (mult rho : ℝ) := by
    simpa only [s0, r0] using
      (Finset.sum_filter_add_sum_filter_not s
        (fun rho => gamma rho ≤ x - 1) (fun rho => (mult rho : ℝ))).symm
  have hsplit1 :
      (∑ rho ∈ r0, (mult rho : ℝ)) =
        (∑ rho ∈ s1, (mult rho : ℝ)) +
          ∑ rho ∈ r1, (mult rho : ℝ) := by
    simpa only [s1, r1] using
      (Finset.sum_filter_add_sum_filter_not r0
        (fun rho => gamma rho ≤ x) (fun rho => (mult rho : ℝ))).symm
  have hsplit2 :
      (∑ rho ∈ r1, (mult rho : ℝ)) =
        (∑ rho ∈ s2, (mult rho : ℝ)) +
          ∑ rho ∈ s3, (mult rho : ℝ) := by
    simpa only [s2, s3] using
      (Finset.sum_filter_add_sum_filter_not r1
        (fun rho => gamma rho ≤ x + 1) (fun rho => (mult rho : ℝ))).symm
  rw [hsplit0, hsplit1, hsplit2]
  linarith

theorem shifted_quartic_kernel_sum_le
    {ι : Type*} {gamma : ι → ℝ} {mult : ι → ℕ}
    {A0 x L : ℝ}
    (hcount : Tail.LocalCount gamma mult A0) (hL : 1 ≤ L)
    (s : Finset ι) :
    ∑ rho ∈ s, (mult rho : ℝ) *
        (1 + (L * (gamma rho - x)) ^ 4)⁻¹ ≤
      6 * A0 * Real.log (|x| + 5) := by
  classical
  let remote : ι → Prop := fun rho =>
    gamma rho ≤ x - 2 ∨ x + 2 ≤ gamma rho
  let stail : Finset ι := s.filter remote
  let scenter : Finset ι := s.filter fun rho => ¬ remote rho
  have htailMem : ∀ rho ∈ stail,
      gamma rho ≤ x - 2 ∨ x + 2 ≤ gamma rho := by
    intro rho hrho
    exact (Finset.mem_filter.mp hrho).2
  have hcenterMem : ∀ rho ∈ scenter,
      x - 2 < gamma rho ∧ gamma rho ≤ x + 2 := by
    intro rho hrho
    have hn := (Finset.mem_filter.mp hrho).2
    simp only [remote, not_or, not_le] at hn
    exact ⟨hn.1, hn.2.le⟩
  have htail := shifted_tail_quartic_kernel_sum_le
    hcount hL stail htailMem
  have hcenterCount := shifted_central_count_le hcount scenter hcenterMem
  have hcenter :
      ∑ rho ∈ scenter, (mult rho : ℝ) *
          (1 + (L * (gamma rho - x)) ^ 4)⁻¹ ≤
        4 * A0 * Real.log (|x| + 5) := by
    refine (Finset.sum_le_sum fun rho hrho => ?_).trans hcenterCount
    have hden : 1 ≤ 1 + (L * (gamma rho - x)) ^ 4 := by
      nlinarith [sq_nonneg ((L * (gamma rho - x)) ^ 2)]
    have hinv : (1 + (L * (gamma rho - x)) ^ 4)⁻¹ ≤ 1 := by
      simpa only [inv_one] using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hden
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) hinv
  have hsplit :
      (∑ rho ∈ s, (mult rho : ℝ) *
        (1 + (L * (gamma rho - x)) ^ 4)⁻¹) =
      (∑ rho ∈ stail, (mult rho : ℝ) *
        (1 + (L * (gamma rho - x)) ^ 4)⁻¹) +
      ∑ rho ∈ scenter, (mult rho : ℝ) *
        (1 + (L * (gamma rho - x)) ^ 4)⁻¹ := by
    simpa only [stail, scenter, remote] using
      (Finset.sum_filter_add_sum_filter_not s remote
        (fun rho => (mult rho : ℝ) *
          (1 + (L * (gamma rho - x)) ^ 4)⁻¹)).symm
  have hA0 : 0 ≤ A0 := hcount.A₀_pos.le
  let B : ℝ := |x| + 5
  have hB5 : 5 ≤ B := by dsimp only [B]; linarith [abs_nonneg x]
  have hlog1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hinvB : B⁻¹ ≤ (1 / 5 : ℝ) * Real.log B := by
    have hinv5 : B⁻¹ ≤ (1 / 5 : ℝ) := by
      simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 5) hB5
    nlinarith
  have hwindow : shiftedTailCubicWindowBound x ≤
      (3 / 8 + 1 / 5 : ℝ) * Real.log B := by
    unfold shiftedTailCubicWindowBound
    dsimp only [B] at hinvB ⊢
    norm_num [one_div] at hinvB ⊢
    linarith
  rw [hsplit]
  calc
    (∑ rho ∈ stail, (mult rho : ℝ) *
          (1 + (L * (gamma rho - x)) ^ 4)⁻¹) +
        ∑ rho ∈ scenter, (mult rho : ℝ) *
          (1 + (L * (gamma rho - x)) ^ 4)⁻¹ ≤
      2 * A0 * shiftedTailCubicWindowBound x +
        4 * A0 * Real.log (|x| + 5) := add_le_add htail hcenter
    _ ≤ 6 * A0 * Real.log (|x| + 5) := by
      dsimp only [B] at hwindow ⊢
      nlinarith [mul_le_mul_of_nonneg_left hwindow (by positivity : 0 ≤ 2 * A0)]

theorem rsCyclicFourKernel_smoothTopHat_row_sum_le_of_local_count
    {Z : ZeroConfig} {A0 mu p w T : ℝ}
    (hcount : Tail.LocalCount
      (fun rho : Z.carrier => (rho : ℂ).im)
      (fun rho : Z.carrier => Z.mult (rho : ℂ)) A0)
    (hmu : 0 < mu) (hT : 1 ≤ T)
    (hscale : 1 ≤ mu * Real.log T)
    (hw : 0 < w) (hwp : 2 * w ≤ p)
    (s : Finset Z.carrier) (rho : Z.carrier) :
    ∑ rho' ∈ s, (Z.mult rho' : ℝ) *
        rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
          (rho : ℂ) (rho' : ℂ) ≤
      (Real.exp ((mu * Real.log T) * (p / 2)) *
        smoothTopHatSobolevMassFour p w) *
        (6 * A0 * Real.log (|(rho : ℂ).im| + 5)) := by
  let M : ℝ := Real.exp ((mu * Real.log T) * (p / 2)) *
    smoothTopHatSobolevMassFour p w
  have hM0 : 0 ≤ M := by
    dsimp only [M, smoothTopHatSobolevMassFour]
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
        (integral_nonneg fun _ => norm_nonneg _))
  have hpoint : ∀ rho' ∈ s,
      rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
          (rho : ℂ) (rho' : ℂ) ≤
        M * (1 + ((mu * Real.log T) *
          ((rho' : ℂ).im - (rho : ℂ).im)) ^ 4)⁻¹ := by
    intro rho' hrho'
    have hweighted := rsCyclicFourKernel_smoothTopHat_weighted_gap_le
      hmu hT hw hwp rho rho'
    have hden : 0 < 1 + ((mu * Real.log T) *
        ((rho' : ℂ).im - (rho : ℂ).im)) ^ 4 := by positivity
    rw [show M = Real.exp ((mu * Real.log T) * (p / 2)) *
      smoothTopHatSobolevMassFour p w by rfl]
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hden).2 hweighted
  have hkernel := shifted_quartic_kernel_sum_le
    (gamma := fun rho' : Z.carrier => (rho' : ℂ).im)
    (mult := fun rho' : Z.carrier => Z.mult (rho' : ℂ))
    (x := (rho : ℂ).im) hcount hscale s
  calc
    ∑ rho' ∈ s, (Z.mult rho' : ℝ) *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ) ≤
        ∑ rho' ∈ s, (Z.mult rho' : ℝ) *
          (M * (1 + ((mu * Real.log T) *
            ((rho' : ℂ).im - (rho : ℂ).im)) ^ 4)⁻¹) := by
      apply Finset.sum_le_sum
      intro rho' hrho'
      exact mul_le_mul_of_nonneg_left (hpoint rho' hrho')
        (Nat.cast_nonneg _)
    _ = M * (∑ rho' ∈ s, (Z.mult rho' : ℝ) *
          (1 + ((mu * Real.log T) *
            ((rho' : ℂ).im - (rho : ℂ).im)) ^ 4)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho' hrho'
      ring
    _ ≤ M * (6 * A0 * Real.log (|(rho : ℂ).im| + 5)) :=
      mul_le_mul_of_nonneg_left hkernel hM0
    _ = (Real.exp ((mu * Real.log T) * (p / 2)) *
          smoothTopHatSobolevMassFour p w) *
        (6 * A0 * Real.log (|(rho : ℂ).im| + 5)) := by rfl

theorem norm_paperFT_windowAveragedHeightTest_at_zero_le
    {Z : ZeroConfig} {R w T : ℝ}
    (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hT : 0 < T) (hRT : R ≤ 2 * T)
    (rho : Z.carrier) :
    ‖paperFT (windowAveragedHeightTest R w)
        (gammaOf (rho : ℂ) / T)‖ ≤
      1 + (R / T) * (R / baseHeightKernelMass) := by
  let z := paperFT (windowAveragedHeightTest R w)
    (gammaOf (rho : ℂ) / T)
  let r := paperFT (windowAveragedHeightTest R w)
    ((((rho : ℂ).im / T : ℝ) : ℂ))
  have hvertical : ‖z - r‖ ≤
      (R / T) * (R / baseHeightKernelMass) := by
    exact norm_windowAveragedHeight_zero_sub_real_le
      hR hw hw1 hT hRT rho
  have hreal := paperFT_windowAveragedHeightTest_real
    hR hw hw1 ((rho : ℂ).im / T)
  have hIcc := paperFT_windowAveragedHeightTest_real_mem_Icc
    hR hw hw1 ((rho : ℂ).im / T)
  rw [hreal] at hIcc
  simp only [Complex.ofReal_re] at hIcc
  have hr : ‖r‖ ≤ 1 := by
    dsimp only [r]
    rw [hreal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hIcc.1]
    exact hIcc.2
  calc
    ‖paperFT (windowAveragedHeightTest R w)
        (gammaOf (rho : ℂ) / T)‖ = ‖z‖ := by rfl
    _ ≤ ‖z - r‖ + ‖r‖ := by
      calc
        ‖z‖ = ‖(z - r) + r‖ := by ring_nf
        _ ≤ ‖z - r‖ + ‖r‖ := norm_add_le _ _
    _ ≤ (R / T) * (R / baseHeightKernelMass) + 1 :=
      add_le_add hvertical hr
    _ = 1 + (R / T) * (R / baseHeightKernelMass) := by ring

theorem rsHeightCyclicFourKernel_row_sum_le_of_local_count
    {Z : ZeroConfig} {A0 mu p w R h T Y : ℝ}
    (hcount : Tail.LocalCount
      (fun rho : Z.carrier => (rho : ℂ).im)
      (fun rho : Z.carrier => Z.mult (rho : ℂ)) A0)
    (hmu : 0 < mu) (hT1 : 1 ≤ T)
    (hscale : 1 ≤ mu * Real.log T)
    (hpw : 0 < w) (hpwp : 2 * w ≤ p)
    (hR : 0 < R) (hh : 0 < h) (hh1 : 2 * h ≤ 1)
    (hRT : R ≤ 2 * T) (hY : 0 ≤ Y)
    (s : Finset Z.carrier)
    (hsY : ∀ rho ∈ s, |(rho : ℂ).im| ≤ Y)
    (rho : Z.carrier) (hrho : rho ∈ s) :
    ∑ rho' ∈ s, rsHeightVertexWeight Z R h T rho' *
        rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
          (rho : ℂ) (rho' : ℂ) ≤
      (1 + (R / T) * (R / baseHeightKernelMass)) *
        (Real.exp ((mu * Real.log T) * (p / 2)) *
          smoothTopHatSobolevMassFour p w) *
          (6 * A0 * Real.log (Y + 5)) := by
  let H : ℝ := 1 + (R / T) * (R / baseHeightKernelMass)
  let M : ℝ := Real.exp ((mu * Real.log T) * (p / 2)) *
    smoothTopHatSobolevMassFour p w
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact add_nonneg (by norm_num)
      (mul_nonneg (div_nonneg hR.le hT.le)
        (div_nonneg hR.le baseHeightKernelMass_pos.le))
  have hM0 : 0 ≤ M := by
    dsimp only [M, smoothTopHatSobolevMassFour]
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
        (integral_nonneg fun _ => norm_nonneg _))
  have hpoint : ∀ rho' ∈ s,
      rsHeightVertexWeight Z R h T rho' *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ) ≤
        H * ((Z.mult rho' : ℝ) *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ)) := by
    intro rho' hrho'
    have hheight := norm_paperFT_windowAveragedHeightTest_at_zero_le
      hR hh hh1 hT hRT rho'
    have hkernel : 0 ≤ rsCyclicFourKernel mu T
        (RSReduction.smoothTopHat p w) (rho : ℂ) (rho' : ℂ) :=
      norm_nonneg _
    unfold rsHeightVertexWeight
    calc
      (Z.mult rho' : ℝ) *
            ‖paperFT (windowAveragedHeightTest R h)
              (gammaOf (rho' : ℂ) / T)‖ *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ) ≤
        (Z.mult rho' : ℝ) * H *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ) := by
          gcongr
      _ = H * ((Z.mult rho' : ℝ) *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ)) := by ring
  have hrow := rsCyclicFourKernel_smoothTopHat_row_sum_le_of_local_count
    hcount hmu hT1 hscale hpw hpwp s rho
  have hlog : Real.log (|(rho : ℂ).im| + 5) ≤ Real.log (Y + 5) := by
    exact Real.log_le_log (by positivity) (by linarith [hsY rho hrho])
  have hA0 : 0 ≤ A0 := hcount.A₀_pos.le
  have hrowY :
      ∑ rho' ∈ s, (Z.mult rho' : ℝ) *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ) ≤
        M * (6 * A0 * Real.log (Y + 5)) := by
    calc
      ∑ rho' ∈ s, (Z.mult rho' : ℝ) *
            rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
              (rho : ℂ) (rho' : ℂ) ≤
          M * (6 * A0 * Real.log (|(rho : ℂ).im| + 5)) := by
            simpa only [M] using hrow
      _ ≤ M * (6 * A0 * Real.log (Y + 5)) := by
        gcongr
  calc
    ∑ rho' ∈ s, rsHeightVertexWeight Z R h T rho' *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ) ≤
        ∑ rho' ∈ s, H * ((Z.mult rho' : ℝ) *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ)) := Finset.sum_le_sum hpoint
    _ = H * (∑ rho' ∈ s, (Z.mult rho' : ℝ) *
          rsCyclicFourKernel mu T (RSReduction.smoothTopHat p w)
            (rho : ℂ) (rho' : ℂ)) := by rw [Finset.mul_sum]
    _ ≤ H * (M * (6 * A0 * Real.log (Y + 5))) :=
      mul_le_mul_of_nonneg_left hrowY hH0
    _ = (1 + (R / T) * (R / baseHeightKernelMass)) *
        (Real.exp ((mu * Real.log T) * (p / 2)) *
          smoothTopHatSobolevMassFour p w) *
          (6 * A0 * Real.log (Y + 5)) := by
      dsimp only [H, M]
      ring

def smoothTopHatCyclicEntryBound (mu p w T : ℝ) : ℝ :=
  Real.exp ((mu * Real.log T) * (p / 2)) *
    smoothTopHatSobolevMassFour p w

def smoothTopHatHeightCyclicRowBound
    (A0 mu p w R h T Y : ℝ) : ℝ :=
  (1 + (R / T) * (R / baseHeightKernelMass)) *
    smoothTopHatCyclicEntryBound mu p w T *
      (6 * A0 * Real.log (Y + 5))

theorem remoteRSCyclicFourNormSum_smoothTopHat_le_of_local_count
    {Z : ZeroConfig} {A0 mu p w R h T Y : ℝ}
    (hcount : Tail.LocalCount
      (fun rho : Z.carrier => (rho : ℂ).im)
      (fun rho : Z.carrier => Z.mult (rho : ℂ)) A0)
    (hmu : 0 < mu) (hT1 : 1 ≤ T)
    (hscale : 1 ≤ mu * Real.log T)
    (hpw : 0 < w) (hpwp : 2 * w ≤ p)
    (hR : 0 < R) (hh : 0 < h) (hh1 : 2 * h ≤ 1)
    (hRT : R ≤ 2 * T) (hY : 0 ≤ Y)
    (s : Finset Z.carrier)
    (hsY : ∀ rho ∈ s, |(rho : ℂ).im| ≤ Y)
    (remote : Z.carrier → Prop) [DecidablePred remote] :
    remoteRSCyclicFourNormSum Z s remote mu R h T
        (RSReduction.smoothTopHat p w) ≤
      mu ^ 4 *
        (4 * smoothTopHatCyclicEntryBound mu p w T *
          (smoothTopHatHeightCyclicRowBound
            A0 mu p w R h T Y) ^ 3 *
          ∑ rho ∈ s.filter remote, rsHeightVertexWeight Z R h T rho) := by
  let B : ℝ := smoothTopHatCyclicEntryBound mu p w T
  let C : ℝ := smoothTopHatHeightCyclicRowBound
    A0 mu p w R h T Y
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hB0 : 0 ≤ B := by
    dsimp only [B, smoothTopHatCyclicEntryBound,
      smoothTopHatSobolevMassFour]
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
        (integral_nonneg fun _ => norm_nonneg _))
  have hH0 : 0 ≤ 1 + (R / T) * (R / baseHeightKernelMass) :=
    add_nonneg (by norm_num)
      (mul_nonneg (div_nonneg hR.le hT.le)
        (div_nonneg hR.le baseHeightKernelMass_pos.le))
  have hlog0 : 0 ≤ Real.log (Y + 5) :=
    Real.log_nonneg (by linarith)
  have hC0 : 0 ≤ C := by
    dsimp only [C, smoothTopHatHeightCyclicRowBound]
    exact mul_nonneg (mul_nonneg hH0 hB0)
      (mul_nonneg (mul_nonneg (by norm_num) hcount.A₀_pos.le) hlog0)
  apply remoteRSCyclicFourNormSum_le s remote
    (RSReduction.smoothTopHat p w) hmu
    (RSReduction.smoothTopHat_contDiff hpw hpwp).continuous
    (RSReduction.smoothTopHat_hasCompactSupport hpw)
    hB0 hC0
  · intro rho hrho rho' hrho'
    simpa only [B, smoothTopHatCyclicEntryBound] using
      rsCyclicFourKernel_smoothTopHat_le hmu hT1 hpw hpwp rho rho'
  · intro rho hrho
    simpa only [C, smoothTopHatHeightCyclicRowBound,
      smoothTopHatCyclicEntryBound] using
      rsHeightCyclicFourKernel_row_sum_le_of_local_count
        hcount hmu hT1 hscale hpw hpwp hR hh hh1 hRT hY
        s hsY rho hrho

end RH.Zeta85.RSPoissonCyclicBridge
