import RH.Zeta85.Discharge.RSHeightUniformCore
import Zeta23.Tail

open Filter Topology Finset Real
open scoped BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

theorem interval_mult_count_le
    {ι : Type*} {gamma : ι → ℝ} {mult : ι → ℕ} {A0 a L B : ℝ}
    (hcount : Tail.LocalCount gamma mult A0) (_hL : 0 < L)
    (s : Finset ι) (hs : ∀ rho ∈ s, a < gamma rho ∧ gamma rho ≤ a + L)
    (hB : ∀ j : ℕ, j < ⌈L⌉₊ → |a + j| + 3 ≤ B) :
    ∑ rho ∈ s, (mult rho : ℝ) ≤
      (⌈L⌉₊ : ℝ) * (A0 * Real.log B) := by
  let K : ℕ := ⌈L⌉₊
  let key : ι → ℕ := fun rho => ⌈gamma rho - a⌉₊ - 1
  have hceil1 : ∀ rho ∈ s, 1 ≤ ⌈gamma rho - a⌉₊ := by
    intro rho hrho
    exact Nat.one_le_ceil_iff.mpr (by linarith [(hs rho hrho).1])
  apply Tail.sum_mult_le_of_windows s mult key K
  · intro rho hrho
    have hceil : ⌈gamma rho - a⌉₊ ≤ K := by
      exact Nat.ceil_mono (by linarith [(hs rho hrho).2])
    have hone := hceil1 rho hrho
    dsimp only [key]
    omega
  · intro j hj
    refine (hcount.window (a + j) _ ?_).trans ?_
    · intro rho hrho
      rw [Finset.mem_filter] at hrho
      obtain ⟨hrhos, hrhoj⟩ := hrho
      have hc : ⌈gamma rho - a⌉₊ = j + 1 := by
        have hone := hceil1 rho hrhos
        dsimp only [key] at hrhoj
        omega
      have hcell := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
      push_cast at hcell
      constructor <;> linarith [hcell.1, hcell.2]
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) (hB j hj))
        hcount.A₀_pos.le

theorem rvm_two_edge_band_count_le
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z)
    {d T : ℝ} (hd : 0 < d) (hd1 : d ≤ 1 / 2) (hT : 6 ≤ T)
    (s : Finset Z.carrier)
    (hs : ∀ rho ∈ s,
      (((1 - d) * T < (rho : ℂ).im ∧ (rho : ℂ).im ≤ (1 + d) * T) ∨
       ((2 - d) * T < (rho : ℂ).im ∧ (rho : ℂ).im ≤ (2 + d) * T))) :
    ∃ A0 : ℝ, 1 ≤ A0 ∧
      ∑ rho ∈ s, (Z.mult rho : ℝ) ≤
        2 * (⌈2 * d * T⌉₊ : ℝ) * A0 * Real.log (4 * T) := by
  obtain ⟨A0, hA0, hlocal⟩ := hRvM.local_count
  refine ⟨A0, hA0, ?_⟩
  have hLC := Tail.LocalCount.ofWindowCount Z hA0 hlocal
  let slo : Finset Z.carrier :=
    s.filter fun rho : Z.carrier => (rho : ℂ).im ≤ (1 + d) * T
  let shi : Finset Z.carrier :=
    s.filter fun rho : Z.carrier => ¬(rho : ℂ).im ≤ (1 + d) * T
  have hTpos : 0 < T := by linarith
  have hLen : 0 < 2 * d * T := by positivity
  have hceilLt : (⌈2 * d * T⌉₊ : ℝ) < 2 * d * T + 1 :=
    Nat.ceil_lt_add_one hLen.le
  have hloMem : ∀ rho ∈ slo,
      (1 - d) * T < (rho : ℂ).im ∧
        (rho : ℂ).im ≤ (1 - d) * T + 2 * d * T := by
    intro rho hrho
    simp only [slo, Finset.mem_filter] at hrho
    rcases hs rho hrho.1 with hlo | hhi
    · exact ⟨hlo.1, by nlinarith [hlo.2]⟩
    · exact absurd hrho.2 (by nlinarith [hhi.1])
  have hhiMem : ∀ rho ∈ shi,
      (2 - d) * T < (rho : ℂ).im ∧
        (rho : ℂ).im ≤ (2 - d) * T + 2 * d * T := by
    intro rho hrho
    simp only [shi, Finset.mem_filter] at hrho
    rcases hs rho hrho.1 with hlo | hhi
    · exact absurd hlo.2 hrho.2
    · exact ⟨hhi.1, by nlinarith [hhi.2]⟩
  have hLowerBase : 0 ≤ (1 - d) * T :=
    mul_nonneg (by linarith) hTpos.le
  have hUpperBase : 0 ≤ (2 - d) * T :=
    mul_nonneg (by linarith) hTpos.le
  have hloB : ∀ j : ℕ, j < ⌈2 * d * T⌉₊ →
      |(1 - d) * T + j| + 3 ≤ 4 * T := by
    intro j hj
    have hjcast : (j : ℝ) < 2 * d * T + 1 :=
      lt_trans (by exact_mod_cast hj) hceilLt
    rw [abs_of_nonneg (add_nonneg hLowerBase (Nat.cast_nonneg j))]
    nlinarith
  have hhiB : ∀ j : ℕ, j < ⌈2 * d * T⌉₊ →
      |(2 - d) * T + j| + 3 ≤ 4 * T := by
    intro j hj
    have hjcast : (j : ℝ) < 2 * d * T + 1 :=
      lt_trans (by exact_mod_cast hj) hceilLt
    rw [abs_of_nonneg (add_nonneg hUpperBase (Nat.cast_nonneg j))]
    nlinarith
  have hlo := interval_mult_count_le hLC hLen slo hloMem hloB
  have hhi := interval_mult_count_le hLC hLen shi hhiMem hhiB
  rw [← sum_filter_add_sum_filter_not s
    (fun rho => (rho : ℂ).im ≤ (1 + d) * T)]
  simp only [slo] at hlo
  simp only [shi] at hhi
  nlinarith

theorem rvm_two_edge_band_normalized_le
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z)
    {d T : ℝ} (hd : 0 < d) (hd1 : d ≤ 1 / 2) (hT : 6 ≤ T)
    (s : Finset Z.carrier)
    (hs : ∀ rho ∈ s,
      (((1 - d) * T < (rho : ℂ).im ∧ (rho : ℂ).im ≤ (1 + d) * T) ∨
       ((2 - d) * T < (rho : ℂ).im ∧ (rho : ℂ).im ≤ (2 + d) * T))) :
    ∃ A0 : ℝ, 1 ≤ A0 ∧
      (∑ rho ∈ s, (Z.mult rho : ℝ)) / (T * Real.log T) ≤
        8 * A0 * d + 4 * A0 / T := by
  obtain ⟨A0, hA0, hraw⟩ :=
    rvm_two_edge_band_count_le hRvM hd hd1 hT s hs
  refine ⟨A0, hA0, ?_⟩
  have hTpos : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hceil : (⌈2 * d * T⌉₊ : ℝ) ≤ 2 * d * T + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * d * T)).le
  have hlog : Real.log (4 * T) ≤ 2 * Real.log T := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hTpos.ne']
    have hfour : Real.log 4 ≤ Real.log T :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  rw [div_le_iff₀ (mul_pos hTpos hlogT)]
  calc
    ∑ rho ∈ s, (Z.mult rho : ℝ) ≤
        2 * (⌈2 * d * T⌉₊ : ℝ) * A0 * Real.log (4 * T) := hraw
    _ ≤ 2 * (2 * d * T + 1) * A0 * (2 * Real.log T) := by
      gcongr
      exact Real.log_nonneg (by nlinarith)
    _ = (8 * A0 * d + 4 * A0 / T) * (T * Real.log T) := by
      field_simp [hTpos.ne']
      ring

end RH.Zeta85.RSPoissonCyclicBridge
