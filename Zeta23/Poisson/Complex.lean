/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Zeta23.Poisson.ComplexDecay

/-!
# Complex-frequency Poisson summation

This is the compact-window Poisson identity with both spectral frequencies
allowed off the real axis.  Compact support controls the exponential growth
in the imaginary directions, while horizontal quadratic decay supplies
absolute summability on the frequency lattice.
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

noncomputable section

namespace Zeta23
namespace Poisson

variable (φ : ℝ → ℂ) (L T : ℝ) (z z' : ℂ)

/-- Compactly supported auxiliary integrand for the complex-frequency
Poisson identity. -/
def complexGIntegrand (ξ u : ℝ) : ℂ :=
  (L : ℂ) * (φ u * φ (L * ξ - u) *
    cexp (I * (z * (u : ℂ) +
      z' * ((L * ξ - u : ℝ) : ℂ) - (T * L * ξ : ℝ))))

/-- Auxiliary compact function to which real Poisson summation is applied. -/
def complexGaux (ξ : ℝ) : ℂ :=
  ∫ u, complexGIntegrand φ L T z z' ξ u

variable {φ L T z z'}

theorem complexGIntegrand_eq_zero_of_not_mem
    (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    {ξ u : ℝ} (h : ¬ (|ξ| < 1 ∧ |u| < L / 2)) :
    complexGIntegrand φ L T z z' ξ u = 0 := by
  unfold complexGIntegrand
  by_cases hu : |u| < L / 2
  · have hξ : 1 ≤ |ξ| := by
      by_contra h'
      exact h ⟨not_le.mp h', hu⟩
    have : L / 2 ≤ |L * ξ - u| := by
      have h4 : |L * ξ| - |u| ≤ |L * ξ - u| :=
        abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos hL] at h4
      nlinarith
    rw [hsupp _ this]
    simp
  · rw [hsupp u (not_lt.mp hu)]
    simp

theorem complexGIntegrand_continuous (hφc : Continuous φ) :
    Continuous
      (Function.uncurry (complexGIntegrand φ L T z z')) := by
  unfold complexGIntegrand Function.uncurry
  fun_prop

theorem complexGIntegrand_hasCompactSupport
    (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) :
    HasCompactSupport
      (Function.uncurry (complexGIntegrand φ L T z z')) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod
      (isCompact_Icc (a := -(L / 2)) (b := L / 2))) ?_
  rintro ⟨ξ, u⟩ hne
  rw [Function.mem_support, Function.uncurry_apply_pair] at hne
  by_contra hmem
  apply hne (complexGIntegrand_eq_zero_of_not_mem hL hsupp _)
  rintro ⟨h1, h2⟩
  apply hmem
  rw [mem_prod, mem_Icc, mem_Icc]
  exact
    ⟨⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩,
     ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩

theorem complexGIntegrand_integrable_prod
    (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) :
    Integrable
      (Function.uncurry (complexGIntegrand φ L T z z'))
      (volume.prod volume) :=
  (complexGIntegrand_continuous hφc).integrable_of_hasCompactSupport
    (complexGIntegrand_hasCompactSupport hL hsupp)

theorem complexGaux_continuous
    (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) :
    Continuous (complexGaux φ L T z z') := by
  have hrestrict :
      complexGaux φ L T z z' =
        fun ξ => ∫ u in Icc (-(L / 2)) (L / 2),
          complexGIntegrand φ L T z z' ξ u := by
    funext ξ
    unfold complexGaux
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    apply complexGIntegrand_eq_zero_of_not_mem hL hsupp
    rintro ⟨-, h2⟩
    apply hu
    rw [mem_Icc]
    exact
      ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  rw [hrestrict]
  exact continuous_parametric_integral_of_continuous
    (complexGIntegrand_continuous hφc) isCompact_Icc

theorem complexGaux_eq_zero
    (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    {ξ : ℝ} (hξ : 1 ≤ |ξ|) :
    complexGaux φ L T z z' ξ = 0 := by
  unfold complexGaux
  rw [← integral_zero]
  congr 1 with u
  apply complexGIntegrand_eq_zero_of_not_mem hL hsupp
  rintro ⟨h1, -⟩
  linarith

theorem complexGaux_zero (heven : ∀ u, φ (-u) = φ u) :
    complexGaux φ L T z z' 0 =
      L * paperFT (fun u => φ u * φ u) (z - z') := by
  unfold complexGaux complexGIntegrand
  rw [paperFT_def, integral_const_mul_C]
  congr 1
  congr 1 with u
  simp only [mul_zero, zero_sub, heven]
  ring_nf

/-- Exponential bookkeeping with two genuinely complex frequencies. -/
theorem complex_cexp_bookkeeping
    (hL : L ≠ 0) (ξ u w : ℝ) :
    cexp (I * (z * (u : ℂ) +
      z' * ((L * ξ - u : ℝ) : ℂ) - (T * L * ξ : ℝ))) *
        cexp ((-2 * Real.pi * ξ * w : ℝ) * I) =
      cexp (I * (z - (T + w * (2 * Real.pi / L) : ℝ)) * (u : ℂ)) *
        cexp (I * (z' - (T + w * (2 * Real.pi / L) : ℝ)) *
          ((L * ξ - u : ℝ) : ℂ)) := by
  have hL' : (L : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- Fourier transform of the auxiliary function at every real frequency. -/
theorem fourier_complexGaux
    (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (w : ℝ) :
    𝓕 (complexGaux φ L T z z') w =
      paperFT φ (z - (T + w * (2 * Real.pi / L) : ℝ)) *
        paperFT φ (z' - (T + w * (2 * Real.pi / L) : ℝ)) := by
  set α : ℂ := z - (T + w * (2 * Real.pi / L) : ℝ) with hα
  set β : ℂ := z' - (T + w * (2 * Real.pi / L) : ℝ) with hβ
  set J : ℝ → ℝ → ℂ :=
    fun ξ u =>
      cexp ((-2 * Real.pi * ξ * w : ℝ) * I) *
        complexGIntegrand φ L T z z' ξ u with hJ
  have hJint : Integrable (Function.uncurry J) (volume.prod volume) := by
    have hc : Continuous (Function.uncurry J) := by
      have hcont :=
        complexGIntegrand_continuous
          (L := L) (T := T) (z := z) (z' := z') hφc
      simp only [hJ]
      apply Continuous.mul _ hcont
      fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply
      (complexGIntegrand_hasCompactSupport
        (T := T) (z := z) (z' := z') hL hsupp).mono
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro h0
    apply hp
    simp only [hJ, Function.uncurry] at h0 ⊢
    rw [show p = (p.1, p.2) from rfl] at h0
    simp only at h0
    rw [h0, mul_zero]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have step1 :
      (fun ξ : ℝ =>
        cexp ((-2 * Real.pi * ξ * w : ℝ) * I) •
          complexGaux φ L T z z' ξ) =
        fun ξ => ∫ u, J ξ u := by
    funext ξ
    rw [smul_eq_mul, complexGaux, hJ]
    beta_reduce
    rw [integral_const_mul_C]
  rw [step1]
  rw [integral_integral_swap hJint]
  have step3 : ∀ u : ℝ, ∫ ξ, J ξ u =
      φ u * cexp (I * α * (u : ℂ)) * paperFT φ β := by
    intro u
    set F0 : ℝ → ℂ :=
      fun v => φ v * cexp (I * β * (v : ℂ)) with hF0
    have hpt : ∀ ξ : ℝ, J ξ u =
        φ u * cexp (I * α * (u : ℂ)) *
          ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * ξ))) := by
      intro ξ
      simp only [hJ, complexGIntegrand, hF0]
      have hbook :=
        complex_cexp_bookkeeping
          (L := L) (T := T) (z := z) (z' := z') hL.ne' ξ u w
      rw [← hα, ← hβ] at hbook
      calc
        cexp ((-2 * Real.pi * ξ * w : ℝ) * I) *
            ((L : ℂ) * (φ u * φ (L * ξ - u) *
              cexp (I * (z * (u : ℂ) +
                z' * ((L * ξ - u : ℝ) : ℂ) -
                  (T * L * ξ : ℝ))))) =
          (L : ℂ) * φ u * φ (L * ξ - u) *
            (cexp (I * (z * (u : ℂ) +
              z' * ((L * ξ - u : ℝ) : ℂ) -
                (T * L * ξ : ℝ))) *
              cexp ((-2 * Real.pi * ξ * w : ℝ) * I)) := by ring
        _ = (L : ℂ) * φ u * φ (L * ξ - u) *
            (cexp (I * α * (u : ℂ)) *
              cexp (I * β * ((L * ξ - u : ℝ) : ℂ))) := by
              rw [hbook]
        _ = _ := by ring
    have hint :
        ∫ ξ, J ξ u =
          ∫ ξ, φ u * cexp (I * α * (u : ℂ)) *
            ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * ξ))) := by
      congr 1 with ξ
      exact hpt ξ
    rw [hint, integral_const_mul_C, integral_const_mul_C,
      Measure.integral_comp_mul_left
        (fun y : ℝ => F0 (y - u)) L,
      integral_sub_right_eq_self F0 u, paperFT_def,
      abs_of_pos (inv_pos.mpr hL)]
    congr 1
    rw [← Complex.coe_smul, smul_eq_mul, ← mul_assoc, ofReal_inv,
      mul_inv_cancel₀ (ofReal_ne_zero.mpr hL.ne'), one_mul]
  simp_rw [step3]
  rw [integral_mul_const_C, paperFT_def, paperFT_def]

/-- Poisson summation for a compact C2 window at two arbitrary complex
frequencies. -/
theorem hasSum_paperFT_mul_paperFT_complex
    {φ : ℝ → ℂ} {L T : ℝ}
    (hL : 0 < L) (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (heven : ∀ u, φ (-u) = φ u)
    (z z' : ℂ) :
    HasSum
      (fun k : ℤ =>
        paperFT φ (z - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)) *
          paperFT φ (z' - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)))
      (L * paperFT (fun u => φ u * φ u) (z - z')) := by
  have hsuppAbs : ∀ u, φ u ≠ 0 → |u| ≤ L / 2 := by
    intro u hu
    by_contra hnot
    exact hu (hsupp u (not_le.mp hnot).le)
  obtain ⟨C1, hC1⟩ := paperFT_horizontal_decay hφ hsuppAbs z
  obtain ⟨C2, hC2⟩ := paperFT_horizontal_decay hφ hsuppAbs z'
  have hC1non : 0 ≤ C1 := by
    exact
      (mul_nonneg (norm_nonneg _)
        (by positivity : 0 ≤ 1 + (z.re - 0) ^ 2)).trans (hC1 0)
  have hC2non : 0 ≤ C2 := by
    exact
      (mul_nonneg (norm_nonneg _)
        (by positivity : 0 ≤ 1 + (z'.re - 0) ^ 2)).trans (hC2 0)
  have hbound2 : ∀ s : ℝ, ‖paperFT φ (z' - s)‖ ≤ C2 := by
    intro s
    calc
      ‖paperFT φ (z' - s)‖ =
          ‖paperFT φ (z' - s)‖ * 1 := by ring
      _ ≤ ‖paperFT φ (z' - s)‖ *
          (1 + (z'.re - s) ^ 2) := by
            gcongr
            nlinarith [sq_nonneg (z'.re - s)]
      _ ≤ C2 := hC2 s
  let h : ℝ := 2 * Real.pi / L
  have hh : h ≠ 0 := by
    dsimp only [h]
    positivity
  have hproduct : ∀ w : ℝ,
      ‖paperFT φ (z - (T + w * h : ℝ)) *
          paperFT φ (z' - (T + w * h : ℝ))‖ *
          (1 + ((z.re - T) - w * h) ^ 2) ≤ C1 * C2 := by
    intro w
    have h1 := hC1 (T + w * h)
    have h2 := hbound2 (T + w * h)
    have h1' :
        ‖paperFT φ (z - (T + w * h : ℝ))‖ *
            (1 + ((z.re - T) - w * h) ^ 2) ≤ C1 := by
      convert h1 using 1 <;> ring
    rw [norm_mul]
    calc
      (‖paperFT φ (z - (T + w * h : ℝ))‖ *
          ‖paperFT φ (z' - (T + w * h : ℝ))‖) *
          (1 + ((z.re - T) - w * h) ^ 2) =
        (‖paperFT φ (z - (T + w * h : ℝ))‖ *
          (1 + ((z.re - T) - w * h) ^ 2)) *
            ‖paperFT φ (z' - (T + w * h : ℝ))‖ := by ring
      _ ≤ C1 * C2 :=
        mul_le_mul h1' h2 (norm_nonneg _) hC1non
  set G := complexGaux φ L T z z' with hG
  have hGc : Continuous G :=
    complexGaux_continuous hL hφ.continuous hsupp
  have hGO : G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ x : ℝ in cocompact ℝ, (1 : ℝ) ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with x hx
    rw [hG, complexGaux_eq_zero hL hsupp (by simpa using hx)]
    simp
  have hFO : 𝓕 G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    apply isBigO_of_decay
      (c := z.re - T) (h := h) (C := C1 * C2) hh
    intro w
    rw [hG, fourier_complexGaux hL hφ.continuous hsupp]
    exact hproduct w
  have hsum : Summable fun n : ℤ => 𝓕 G n :=
    summable_of_isBigO
      (Real.summable_abs_int_rpow one_lt_two)
      (hFO.comp_tendsto Int.tendsto_coe_cofinite)
  have key :=
    Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
      hGc one_lt_two hGO hsum 0
  have lhs : ∑' n : ℤ, G (0 + n) = G 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      rw [zero_add, hG, complexGaux_eq_zero hL hsupp]
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
  have rhs :
      ∑' n : ℤ, 𝓕 G n *
          fourier n ((0 : ℝ) : UnitAddCircle) =
        ∑' n : ℤ, 𝓕 G n := by
    congr 1 with n
    rw [fourier_coe_apply]
    simp
  rw [lhs, rhs] at key
  have hhas : HasSum (fun n : ℤ => 𝓕 G n) (G 0) := by
    rw [key]
    exact hsum.hasSum
  rw [hG, complexGaux_zero heven] at hhas
  convert hhas using 1
  funext k
  rw [fourier_complexGaux hL hφ.continuous hsupp]

end Poisson
end Zeta23

end
