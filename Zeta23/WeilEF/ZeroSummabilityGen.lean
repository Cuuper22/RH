/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/ZeroSummabilityGen.lean — ZeroSummability for ANY zero configuration with a log(|t|+3) local count: the ζ theorems of Zeta23/WeilEF/ZeroSummability.lean with the local count as a hypothesis, so that
L(s,χ) (Zeta23/ThmE, via localCountChi) is an instance.  Proof text identical to the ζ case.
-/
import Zeta23.WeilEF.ZeroSummability

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set Filter MeasureTheory

/-- **Σ_ρ m_ρ/(1+|γ_ρ|²) converges** (dyadic/unit-window summation of the local count). -/
theorem zero_sum_inv_sq_gen (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc' : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  classical
  have hLC := Tail.LocalCount.ofWindowCount Z hA₀ hloc'
  have hW := summable_weight
  refine summable_of_sum_le (c := 4 * A₀ * totalWeight) (fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))])) fun s => ?_
  -- group by the window key of Im ρ
  set κ : Z.carrier → ℤ := fun ρ => key (ρ : ℂ).im with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ) (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ n ∈ s.image κ,
      ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
    intro n _
    have hwin := hLC.window n (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
      simp only [Finset.mem_filter] at hρ
      rw [← hρ.2]; exact ⟨key_lt _, le_key_add_one _⟩)
    have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
        (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          ≤ (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have h1 : (n : ℝ) < (ρ : ℂ).im := by rw [← hρ.2]; exact key_lt _
      have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := by rw [← hρ.2]; exact le_key_add_one _
      have hge := one_add_sq_ge h1 h2
      have hnorm : 1 + ((ρ : ℂ).im) ^ 2 ≤ 1 + Complex.normSq (gammaOf ρ) := by
        rw [Complex.normSq_apply, gammaOf_re]; nlinarith [sq_nonneg ((gammaOf (ρ:ℂ)).im)]
      have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
      have hN0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
        linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
      have hinv : 1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤ 4 / (1 + (n : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith [hge, hnorm]
      calc (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          = (Z.mult (ρ : ℂ) : ℝ) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by ring
        _ ≤ (Z.mult (ρ : ℂ) : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hinv hm
        _ = (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by ring
    calc ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ ∑ ρ ∈ s with κ ρ = n, (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) :=
          Finset.sum_le_sum hpt
      _ = (4 / (1 + (n : ℝ) ^ 2)) * ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (4 / (1 + (n : ℝ) ^ 2)) * (A₀ * Real.log (|(n:ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by ring
  calc ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
      ≤ ∑ n ∈ s.image κ, 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) :=
        Finset.sum_le_sum hfiber
    _ = 4 * A₀ * ∑ n ∈ s.image κ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * A₀ * totalWeight := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact hW.sum_le_tsum _ fun n _ =>
          div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)

/-! ### EF_zero_sum_summable -/

/-- The EF zero-side sum converges absolutely for every k ∈ C_c²(ℝ)
(via [eq:hfbound]: ‖h(γ_ρ)‖ ≤ e^{Λ/2}‖k''‖₁/‖γ_ρ‖², |Im γ_ρ| < 1/2) — EF_lit's Summable clause. -/
theorem EF_zero_sum_summable_gen (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc' : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) := by
  classical
  -- support bound
  obtain ⟨r, hr⟩ := hkc.isCompact.isBounded.subset_closedBall 0
  set Λ : ℝ := max r 0 with hΛ
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ Metric.closedBall (0:ℝ) r := hr (subset_tsupport _ (Function.mem_support.mpr hu))
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set C₂ : ℝ := ∫ u, ‖deriv (deriv k) u‖ with hC₂
  have hC₂0 : 0 ≤ C₂ := integral_nonneg fun _ => norm_nonneg _
  set C : ℝ := 2 * Real.exp (Λ / 2) * C₂ with hC
  -- comparison series
  have hg := (zero_sum_inv_sq_gen Z hA₀ hloc').mul_left C
  refine Summable.of_norm_bounded_eventually hg ?_
  -- exceptional finite set: |Im ρ| < 1 (then possibly ‖γ_ρ‖ < 1)
  have hfin : (Z.window (-1) 1).Finite := Z.finite_window _ _
  have hSfin : ((fun ρ : Z.carrier => (ρ : ℂ)) ⁻¹' (Z.window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, ZeroConfig.window, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_le] at hρ
  have hρmem : (ρ : ℂ) ∈ Z.carrier := ρ.2
  -- ‖γ_ρ‖ ≥ |Im ρ| ≥ 1
  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ hρmem h.1) (not_lt.mpr h.2.le)
  have hz1 : 1 ≤ ‖gammaOf (ρ : ℂ)‖ := him.trans (abs_im_le_norm_gammaOf _)
  have hz0 : gammaOf (ρ : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  have hstrip := Z.strip _ hρmem
  have himγ : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := abs_gammaOf_im_le hstrip
  have hFT := norm_paperFT_le_div hk hsupp hz0
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  -- assemble
  rw [norm_mul, Complex.norm_natCast]
  have hm : (0:ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hkey : ‖paperFT k (gammaOf (ρ : ℂ))‖ ≤ C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    have hexp : Real.exp (|(gammaOf (ρ:ℂ)).im| * Λ) ≤ Real.exp (Λ / 2) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have hnsq : Complex.normSq (gammaOf (ρ : ℂ)) = ‖gammaOf (ρ : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have h2 : 1 / ‖gammaOf (ρ : ℂ)‖ ^ 2 ≤ 2 * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
      rw [hnsq, div_le_iff₀ (by positivity)]
      have : 0 < 1 + ‖gammaOf (ρ:ℂ)‖ ^ 2 := by positivity
      rw [show 2 * (1 / (1 + ‖gammaOf (ρ:ℂ)‖ ^ 2)) * ‖gammaOf (ρ:ℂ)‖ ^ 2
          = 2 * ‖gammaOf (ρ:ℂ)‖ ^ 2 / (1 + ‖gammaOf (ρ:ℂ)‖ ^ 2) by ring, le_div_iff₀ this]
      nlinarith
    calc ‖paperFT k (gammaOf (ρ : ℂ))‖
        ≤ Real.exp (|(gammaOf (ρ:ℂ)).im| * Λ) * C₂ / ‖gammaOf (ρ : ℂ)‖ ^ 2 := hFT
      _ = Real.exp (|(gammaOf (ρ:ℂ)).im| * Λ) * C₂ * (1 / ‖gammaOf (ρ : ℂ)‖ ^ 2) := by ring
      _ ≤ Real.exp (Λ / 2) * C₂ * (2 * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hexp hC₂0) h2 (by positivity) (by positivity)
      _ = C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by rw [hC]; ring
  calc (Z.mult ρ : ℝ) * ‖paperFT k (gammaOf (ρ : ℂ))‖
      ≤ (Z.mult ρ : ℝ) * (C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
        mul_le_mul_of_nonneg_left hkey hm
    _ = C * ((Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
        ring

end WeilEF
end Zeta23
