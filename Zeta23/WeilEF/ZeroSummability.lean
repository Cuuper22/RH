/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/ZeroSummability.lean
Convergence of the zero sums from the local count:
  * zero_sum_inv_sq      : Σ_ρ m_ρ/(1+|γ_ρ|²) < ∞  — unit-window decomposition of the ordinates + the
                           two-sided local count N(t,t+1] ≤ A₀ log(|t|+3) (Zeta23.RvM.zeta_local_zero_count)
                           + Σ_{n∈ℤ} log(|n|+3)/(1+n²) < ∞;
  * EF_zero_sum_summable : Σ_ρ m_ρ h(γ_ρ) converges absolutely for every k ∈ C_c²(ℝ), h = paperFT k, via
                           [eq:hfbound] ‖h(z)‖ ≤ e^{|Im z|Λ}‖k″‖₁/‖z‖² (Zeta23.norm_paperFT_le_div) and
                           |Im γ_ρ| = |½ − Re ρ| < ½.
These statements are consumed by WeilEF/Main.lean.
-/
import Zeta23.Tail
import Zeta23.RvM.LocalCount
import Zeta23.ExplicitFormula
import Zeta23.Poisson.PaperFT

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set Filter MeasureTheory

/-! ### γ_ρ bookkeeping -/

lemma gammaOf_re (ρ : ℂ) : (gammaOf ρ).re = ρ.im := by
  simp [gammaOf, Complex.div_I]

lemma gammaOf_im (ρ : ℂ) : (gammaOf ρ).im = 1 / 2 - ρ.re := by
  simp [gammaOf, Complex.div_I]

lemma abs_im_le_norm_gammaOf (ρ : ℂ) : |ρ.im| ≤ ‖gammaOf ρ‖ := by
  rw [← gammaOf_re]; exact Complex.abs_re_le_norm _

/-- For a point of the open strip, |Im γ_ρ| < 1/2. -/
lemma abs_gammaOf_im_lt {ρ : ℂ} (h : 0 < ρ.re ∧ ρ.re < 1) : |(gammaOf ρ).im| < 1 / 2 := by
  rw [gammaOf_im, abs_lt]; constructor <;> linarith [h.1, h.2]

/-- For a point of the closed strip, |Im γ_ρ| ≤ 1/2. -/
lemma abs_gammaOf_im_le {ρ : ℂ} (h : 0 ≤ ρ.re ∧ ρ.re ≤ 1) : |(gammaOf ρ).im| ≤ 1 / 2 := by
  rw [gammaOf_im, abs_le]; constructor <;> linarith [h.1, h.2]

/-! ### The weight series Σ_{n∈ℤ} log(|n|+3)/(1+n²) -/

/-- log(|n| + 3)/(1 + n²) ≤ 4 |n|^{−3/2} for n ≠ 0. -/
lemma weight_le (n : ℤ) (hn : n ≠ 0) :
    Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) ≤ 4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hn0 : (0 : ℝ) < |(n : ℝ)| := by linarith
  -- log y ≤ 2 √y and |n| + 3 ≤ 4|n|, so log(|n|+3) ≤ 2√(4|n|) = 4√|n|
  have h1 := Real.log_le_rpow_div (show (0:ℝ) ≤ |(n:ℝ)| + 3 by positivity)
    (show (0:ℝ) < 1/2 by norm_num)
  have h2 : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) ≤ (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3 : (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) = 2 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hn0.le, show (4:ℝ) ^ (1/2:ℝ) = 2 by
      rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
  have hA : Real.log (|(n : ℝ)| + 3) ≤ 4 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    have : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) := by ring
    rw [this] at h1; rw [h3] at h2; linarith
  have hB : 1 / (1 + (n : ℝ) ^ 2) ≤ |(n : ℝ)| ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hn0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs,
      one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  calc Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)
      = Real.log (|(n : ℝ)| + 3) * (1 / (1 + (n : ℝ) ^ 2)) := by ring
    _ ≤ (4 * |(n : ℝ)| ^ (1 / 2 : ℝ)) * |(n : ℝ)| ^ (-2 : ℝ) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = 4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hn0]; norm_num

lemma summable_weight :
    Summable (fun n : ℤ => Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (show (1:ℝ) < 3/2 by norm_num)).mul_left 4) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have h0 : 0 ≤ Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) :=
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact weight_le n hn

/-- The total weight W := Σ'_{n∈ℤ} log(|n|+3)/(1+n²). -/
def totalWeight : ℝ := ∑' n : ℤ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)

/-! ### zero_sum_inv_sq -/

/-- unit-window key of an ordinate: n := ⌈y⌉ − 1, so that n < y ≤ n + 1. -/
def key (y : ℝ) : ℤ := ⌈y⌉ - 1

lemma key_lt (y : ℝ) : (key y : ℝ) < y := by
  have := Int.ceil_lt_add_one y; unfold key; push_cast; linarith

lemma le_key_add_one (y : ℝ) : y ≤ (key y : ℝ) + 1 := by
  have := Int.le_ceil y; unfold key; push_cast; linarith

/-- if n < y ≤ n+1 then 1 + y² ≥ (1 + n²)/4. -/
lemma one_add_sq_ge {y : ℝ} {n : ℤ} (h1 : (n : ℝ) < y) (h2 : y ≤ (n : ℝ) + 1) :
    (1 + (n : ℝ) ^ 2) / 4 ≤ 1 + y ^ 2 := by
  rcases le_or_gt 0 (n : ℝ) with hn | hn
  · nlinarith
  · have hn' : n < 0 := by exact_mod_cast hn
    have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hy : ((n : ℝ) + 1) ^ 2 ≤ y ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0:ℝ) ≤ -(y + ((n : ℝ) + 1)))]
    nlinarith [hy, sq_nonneg ((n : ℝ) + 4 / 3)]

/-- **Σ_ρ m_ρ/(1+|γ_ρ|²) converges** (dyadic/unit-window summation of the local count). -/
theorem zero_sum_inv_sq (hs : ZetaSeam) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      (zeroMult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  have hloc' : ∀ t : ℝ, ((zetaZeros hs).N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
    intro t; rw [zetaZeros_N]; exact hloc t
  have hLC := Tail.LocalCount.ofWindowCount (zetaZeros hs) hA₀ hloc'
  have hW := summable_weight
  refine summable_of_sum_le (c := 4 * A₀ * totalWeight) (fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))])) fun s => ?_
  -- group by the window key of Im ρ
  set κ : (zetaZeros hs).carrier → ℤ := fun ρ => key (ρ : ℂ).im with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ) (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ n ∈ s.image κ,
      ∑ ρ ∈ s with κ ρ = n, (zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
    intro n _
    have hwin := hLC.window n (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
      simp only [Finset.mem_filter] at hρ
      rw [← hρ.2]; exact ⟨key_lt _, le_key_add_one _⟩)
    have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
        (zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          ≤ (4 / (1 + (n : ℝ) ^ 2)) * ((zetaZeros hs).mult ρ : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have h1 : (n : ℝ) < (ρ : ℂ).im := by rw [← hρ.2]; exact key_lt _
      have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := by rw [← hρ.2]; exact le_key_add_one _
      have hge := one_add_sq_ge h1 h2
      have hnorm : 1 + ((ρ : ℂ).im) ^ 2 ≤ 1 + Complex.normSq (gammaOf ρ) := by
        rw [Complex.normSq_apply, gammaOf_re]; nlinarith [sq_nonneg ((gammaOf (ρ:ℂ)).im)]
      have hm : (0 : ℝ) ≤ zeroMult (ρ : ℂ) := Nat.cast_nonneg _
      have hN0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
        linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
      have hinv : 1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤ 4 / (1 + (n : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith [hge, hnorm]
      calc (zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          = (zeroMult (ρ : ℂ) : ℝ) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by ring
        _ ≤ (zeroMult (ρ : ℂ) : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hinv hm
        _ = (4 / (1 + (n : ℝ) ^ 2)) * ((zetaZeros hs).mult ρ : ℝ) := by rw [zetaZeros_mult]; ring
    calc ∑ ρ ∈ s with κ ρ = n, (zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ ∑ ρ ∈ s with κ ρ = n, (4 / (1 + (n : ℝ) ^ 2)) * ((zetaZeros hs).mult ρ : ℝ) :=
          Finset.sum_le_sum hpt
      _ = (4 / (1 + (n : ℝ) ^ 2)) * ∑ ρ ∈ s with κ ρ = n, ((zetaZeros hs).mult ρ : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (4 / (1 + (n : ℝ) ^ 2)) * (A₀ * Real.log (|(n:ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by ring
  calc ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n, (zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
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
theorem EF_zero_sum_summable (hs : ZetaSeam) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) * paperFT k (gammaOf ρ)) := by
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
  have hg := (zero_sum_inv_sq hs).mul_left C
  refine Summable.of_norm_bounded_eventually hg ?_
  -- exceptional finite set: |Im ρ| < 1 (then possibly ‖γ_ρ‖ < 1)
  have hfin : ((zetaZeros hs).window (-1) 1).Finite := (zetaZeros hs).finite_window _ _
  have hSfin : ((fun ρ : (zetaZeros hs).carrier => (ρ : ℂ)) ⁻¹' ((zetaZeros hs).window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, ZeroConfig.window, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_le] at hρ
  have hρmem : (ρ : ℂ) ∈ (zetaZeros hs).carrier := ρ.2
  -- ‖γ_ρ‖ ≥ |Im ρ| ≥ 1
  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ hρmem h.1) (not_lt.mpr h.2.le)
  have hz1 : 1 ≤ ‖gammaOf (ρ : ℂ)‖ := him.trans (abs_im_le_norm_gammaOf _)
  have hz0 : gammaOf (ρ : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  have hstrip := (zetaZeros hs).strip _ hρmem
  have himγ : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := abs_gammaOf_im_le hstrip
  have hFT := norm_paperFT_le_div hk hsupp hz0
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  -- assemble
  rw [norm_mul, Complex.norm_natCast]
  have hm : (0:ℝ) ≤ (zetaZeros hs).mult ρ := Nat.cast_nonneg _
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
  calc ((zetaZeros hs).mult ρ : ℝ) * ‖paperFT k (gammaOf (ρ : ℂ))‖
      ≤ ((zetaZeros hs).mult ρ : ℝ) * (C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
        mul_le_mul_of_nonneg_left hkey hm
    _ = C * ((zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
        rw [zetaZeros_mult]; ring

end WeilEF
end Zeta23
