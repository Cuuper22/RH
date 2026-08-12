/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Zeta23.Poisson.Complex

/-!
# Complex Poisson summation with the full alias sum

The half-period support theorem retains only the zero spatial translate.
Here the support may cross several periods.  Poisson summation then returns
the complete finite family of translated overlap integrals, which is the
alias expression used by the quartic construction.
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

noncomputable section

namespace Zeta23
namespace Poisson

/-- The spatial translate produced at one integer point of the compact
Poisson auxiliary function. -/
def complexPoissonAliasTerm
    (φ : ℝ → ℂ) (L T : ℝ) (z z' : ℂ) (m : ℤ) : ℂ :=
  (L : ℂ) *
    cexp (I * (z' - (T : ℂ)) * ((m : ℝ) * L : ℝ)) *
      ∫ u : ℝ, φ u * φ ((m : ℝ) * L - u) *
        cexp (I * (z - z') * (u : ℂ))

/-- At every integer, the compact auxiliary function is exactly the
corresponding spatial alias. -/
theorem complexGaux_int_eq_alias
    (φ : ℝ → ℂ) (L T : ℝ) (z z' : ℂ) (m : ℤ) :
    complexGaux φ L T z z' (m : ℝ) =
      complexPoissonAliasTerm φ L T z z' m := by
  unfold complexGaux complexPoissonAliasTerm
  calc
    (∫ u, complexGIntegrand φ L T z z' (m : ℝ) u) =
        ∫ u, ((L : ℂ) *
          cexp (I * (z' - (T : ℂ)) * ((m : ℝ) * L : ℝ))) *
            (φ u * φ ((m : ℝ) * L - u) *
              cexp (I * (z - z') * (u : ℂ))) := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold complexGIntegrand
      have hexp :
          cexp (I * (z * (u : ℂ) +
            z' * ((L * (m : ℝ) - u : ℝ) : ℂ) -
              (T * L * (m : ℝ) : ℝ))) =
            cexp (I * (z' - (T : ℂ)) * ((m : ℝ) * L : ℝ)) *
              cexp (I * (z - z') * (u : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      rw [hexp]
      push_cast
      ring
    _ = ((L : ℂ) *
          cexp (I * (z' - (T : ℂ)) * ((m : ℝ) * L : ℝ))) *
        ∫ u, φ u * φ ((m : ℝ) * L - u) *
          cexp (I * (z - z') * (u : ℂ)) :=
      integral_const_mul_C _ _
    _ = _ := by ring

/-- A compactly supported window makes the auxiliary function vanish beyond
twice the physical support radius divided by the period. -/
theorem complexGaux_eq_zero_of_abs_gt
    {φ : ℝ → ℂ} {L T Λ : ℝ} {z z' : ℂ}
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsupp : ∀ u, Λ < |u| → φ u = 0)
    {ξ : ℝ} (hξ : 2 * Λ / L < |ξ|) :
    complexGaux φ L T z z' ξ = 0 := by
  unfold complexGaux
  rw [← integral_zero]
  congr 1 with u
  unfold complexGIntegrand
  by_cases hu : |u| ≤ Λ
  · have hscale : 2 * Λ < L * |ξ| := by
      have hmul := (div_lt_iff₀ hL).mp hξ
      nlinarith
    have htri : |L * ξ| - |u| ≤ |L * ξ - u| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_mul, abs_of_pos hL] at htri
    have hfar : Λ < |L * ξ - u| := by
      nlinarith
    rw [hsupp _ hfar]
    simp
  · have hfar : Λ < |u| := lt_of_not_ge hu
    rw [hsupp u hfar]
    simp

/-- The two-variable auxiliary integrand is compactly supported whenever
the window is compactly supported. -/
theorem complexGIntegrand_eq_zero_of_general_not_mem
    {φ : ℝ → ℂ} {L T Λ : ℝ} {z z' : ℂ}
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsupp : ∀ u, Λ < |u| → φ u = 0)
    {ξ u : ℝ}
    (h : ¬ (|ξ| ≤ 2 * Λ / L ∧ |u| ≤ Λ)) :
    complexGIntegrand φ L T z z' ξ u = 0 := by
  unfold complexGIntegrand
  by_cases hu : |u| ≤ Λ
  · have hxi : 2 * Λ / L < |ξ| := by
      by_contra hnot
      exact h ⟨not_lt.mp hnot, hu⟩
    have hscale : 2 * Λ < L * |ξ| := by
      have hmul := (div_lt_iff₀ hL).mp hxi
      nlinarith
    have htri : |L * ξ| - |u| ≤ |L * ξ - u| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_mul, abs_of_pos hL] at htri
    have hfar : Λ < |L * ξ - u| := by
      nlinarith
    rw [hsupp _ hfar]
    simp
  · have hfar : Λ < |u| := lt_of_not_ge hu
    rw [hsupp u hfar]
    simp

theorem complexGIntegrand_hasCompactSupport_general
    {φ : ℝ → ℂ} {L T Λ : ℝ} {z z' : ℂ}
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsupp : ∀ u, Λ < |u| → φ u = 0) :
    HasCompactSupport
      (Function.uncurry (complexGIntegrand φ L T z z')) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc (a := -(2 * Λ / L)) (b := 2 * Λ / L)).prod
      (isCompact_Icc (a := -Λ) (b := Λ))) ?_
  rintro ⟨ξ, u⟩ hne
  rw [Function.mem_support, Function.uncurry_apply_pair] at hne
  by_contra hmem
  apply hne
    (complexGIntegrand_eq_zero_of_general_not_mem hL hΛ hsupp ?_)
  rintro ⟨hξ, hu⟩
  apply hmem
  rw [mem_prod, mem_Icc, mem_Icc]
  exact
    ⟨⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩,
     ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩

/-- The complex auxiliary function is compactly supported for every compact
window; no half-period support restriction is needed. -/
theorem complexGaux_hasCompactSupport_general
    {φ : ℝ → ℂ} {L T Λ : ℝ} {z z' : ℂ}
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsupp : ∀ u, Λ < |u| → φ u = 0) :
    HasCompactSupport (complexGaux φ L T z z') := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -(2 * Λ / L)) (b := 2 * Λ / L)) ?_
  intro ξ hmem
  rw [Function.mem_support] at hmem
  have hle : |ξ| ≤ 2 * Λ / L := by
    by_contra hnot
    exact hmem
      (complexGaux_eq_zero_of_abs_gt hL hΛ hsupp (not_le.mp hnot))
  exact abs_le.mp hle

/-- Compact support in an arbitrary interval is enough for continuity of the
complex auxiliary function.  No comparison between the support radius and
the modulation period is required. -/
theorem complexGaux_continuous_general
    {φ : ℝ → ℂ} {L T Λ : ℝ} {z z' : ℂ}
    (hφc : Continuous φ)
    (hsupp : ∀ u, Λ < |u| → φ u = 0) :
    Continuous (complexGaux φ L T z z') := by
  have hrestrict :
      complexGaux φ L T z z' =
        fun ξ => ∫ u in Icc (-Λ) Λ,
          complexGIntegrand φ L T z z' ξ u := by
    funext ξ
    unfold complexGaux
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    have hfar : Λ < |u| := by
      by_contra hnot
      apply hu
      rw [mem_Icc]
      have habs : |u| ≤ Λ := le_of_not_gt hnot
      exact
        ⟨by linarith [neg_abs_le u],
         by linarith [le_abs_self u]⟩
    unfold complexGIntegrand
    rw [hsupp u hfar]
    simp
  rw [hrestrict]
  exact continuous_parametric_integral_of_continuous
    (complexGIntegrand_continuous hφc) isCompact_Icc

theorem fourier_complexGaux_general
    (hL : 0 < L) (hΛ : 0 ≤ Λ) (hφc : Continuous φ)
    (hsupp : ∀ u, Λ < |u| → φ u = 0)
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
      (complexGIntegrand_hasCompactSupport_general
        (T := T) (z := z) (z' := z') hL hΛ hsupp).mono
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

/-- Full complex-frequency Poisson summation.  The right side is the
summable family of all spatial aliases, rather than only its zero term. -/
theorem hasSum_paperFT_mul_paperFT_alias
    {φ : ℝ → ℂ} {L T Λ : ℝ}
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, Λ < |u| → φ u = 0)
    (z z' : ℂ) :
    Summable (complexPoissonAliasTerm φ L T z z') ∧
      HasSum
        (fun k : ℤ =>
          paperFT φ
              (z - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)) *
            paperFT φ
              (z' - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)))
        (∑' m : ℤ, complexPoissonAliasTerm φ L T z z' m) := by
  have hsuppAbs : ∀ u, φ u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    by_contra hnot
    exact hu (hsupp u (not_le.mp hnot))
  obtain ⟨C1, hC1⟩ := paperFT_horizontal_decay hφ hsuppAbs z
  obtain ⟨C2, hC2⟩ := paperFT_horizontal_decay hφ hsuppAbs z'
  have hC1non : 0 ≤ C1 := by
    exact
      (mul_nonneg (norm_nonneg _)
        (by positivity : 0 ≤ 1 + (z.re - 0) ^ 2)).trans (hC1 0)
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
    complexGaux_continuous_general hφ.continuous hsupp
  have hGO : G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ x : ℝ in cocompact ℝ,
        max 1 (2 * Λ / L + 1) ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with x hx
    rw [Real.norm_eq_abs] at hx
    have hfar : 2 * Λ / L < |x| := by
      have hstep :
          2 * Λ / L + 1 ≤ |x| :=
        le_trans (le_max_right _ _) hx
      linarith
    rw [hG, complexGaux_eq_zero_of_abs_gt hL hΛ hsupp hfar]
    simp
  have hFO : 𝓕 G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    apply isBigO_of_decay
      (c := z.re - T) (h := h) (C := C1 * C2) hh
    intro w
    rw [hG]
    rw [fourier_complexGaux_general hL hΛ hφ.continuous hsupp]
    exact hproduct w
  have hFourierSum : Summable fun n : ℤ => 𝓕 G n :=
    summable_of_isBigO
      (Real.summable_abs_int_rpow one_lt_two)
      (hFO.comp_tendsto Int.tendsto_coe_cofinite)
  have hGSum : Summable fun n : ℤ => G n :=
    summable_of_isBigO
      (Real.summable_abs_int_rpow one_lt_two)
      (hGO.comp_tendsto Int.tendsto_coe_cofinite)
  have hkey :=
    Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
      hGc one_lt_two hGO hFourierSum 0
  have hlhs : ∑' n : ℤ, G (0 + n) = ∑' n : ℤ, G n := by
    simp
  have hrhs :
      ∑' n : ℤ, 𝓕 G n *
          fourier n ((0 : ℝ) : UnitAddCircle) =
        ∑' n : ℤ, 𝓕 G n := by
    congr 1 with n
    rw [fourier_coe_apply]
    simp
  rw [hlhs, hrhs] at hkey
  have haliasSum : Summable (complexPoissonAliasTerm φ L T z z') := by
    apply hGSum.congr
    intro m
    rw [hG, complexGaux_int_eq_alias]
  refine ⟨haliasSum, ?_⟩
  have hhas :
      HasSum (fun n : ℤ => 𝓕 G n)
        (∑' m : ℤ, complexPoissonAliasTerm φ L T z z' m) := by
    have hbase : HasSum (fun n : ℤ => 𝓕 G n) (∑' n : ℤ, G n) := by
      rw [hkey]
      exact hFourierSum.hasSum
    have halias :
        (∑' n : ℤ, G n) =
          ∑' m : ℤ, complexPoissonAliasTerm φ L T z z' m := by
      apply tsum_congr
      intro m
      rw [hG, complexGaux_int_eq_alias]
    rw [halias] at hbase
    exact hbase
  convert hhas using 1
  funext k
  rw [hG]
  rw [fourier_complexGaux_general hL hΛ hφ.continuous hsupp]

/-- Every compactly supported complex window admits a nonnegative symmetric
support radius.  This removes an arbitrary radius witness from downstream
Poisson applications. -/
theorem exists_nonneg_support_abs_bound
    {φ : ℝ → ℂ} (hcompact : HasCompactSupport φ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ u, Λ < |u| → φ u = 0 := by
  obtain ⟨r, hr⟩ := hcompact.isCompact.isBounded.subset_closedBall 0
  refine ⟨max r 0, le_max_right _ _, ?_⟩
  intro u hu
  apply image_eq_zero_of_notMem_tsupport
  intro hut
  have hur := hr hut
  rw [Metric.mem_closedBall, Real.dist_0_eq_abs] at hur
  have hle : |u| ≤ max r 0 := hur.trans (le_max_left _ _)
  exact (not_lt_of_ge hle) hu

/-- Compact-support form of the fourth-order two-factor horizontal decay
bound, with the support radius eliminated from the statement. -/
theorem paperFT_mul_horizontal_decay_of_hasCompactSupport
    {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ)
    (hcompact : HasCompactSupport φ)
    (z z' : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ,
      ‖paperFT φ (z - s) * paperFT φ (z' - s)‖ *
          ((1 + (z.re - s) ^ 2) * (1 + (z'.re - s) ^ 2)) ≤ C := by
  obtain ⟨Λ, _, hsupp⟩ := exists_nonneg_support_abs_bound hcompact
  exact paperFT_mul_horizontal_decay hφ (fun u hu => by
    by_contra hnot
    exact hu (hsupp u (not_le.mp hnot))) z z'

/-- Compact support also supplies one fourth-order constant for every pair
of frequencies in a fixed vertical strip. -/
theorem exists_paperFT_mul_horizontal_decay_uniform_of_hasCompactSupport
    {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ)
    (hcompact : HasCompactSupport φ)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z z' : ℂ,
      |z.im| ≤ B → |z'.im| ≤ B → ∀ s : ℝ,
        ‖paperFT φ (z - s) * paperFT φ (z' - s)‖ *
            ((1 + (z.re - s) ^ 2) * (1 + (z'.re - s) ^ 2)) ≤ C := by
  obtain ⟨Λ, hΛ, hsuppZero⟩ := exists_nonneg_support_abs_bound hcompact
  have hsupp : ∀ u, φ u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    by_contra hnot
    exact hu (hsuppZero u (not_le.mp hnot))
  let C : ℝ := (Real.exp (B * Λ) *
    ((∫ u, ‖φ u‖) + (∫ u, ‖deriv (deriv φ) u‖))) ^ 2
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro z z' hz hz' s
  exact paperFT_mul_horizontal_decay_uniform
    hφ hsupp hΛ hB z z' hz hz' s

/-- Full complex Poisson summation stated directly for a compactly supported
window, with the support radius chosen internally. -/
theorem hasSum_paperFT_mul_paperFT_alias_of_hasCompactSupport
    {φ : ℝ → ℂ} {L T : ℝ}
    (hL : 0 < L)
    (hφ : ContDiff ℝ 2 φ)
    (hcompact : HasCompactSupport φ)
    (z z' : ℂ) :
    Summable (complexPoissonAliasTerm φ L T z z') ∧
      HasSum
        (fun k : ℤ =>
          paperFT φ
              (z - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)) *
            paperFT φ
              (z' - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)))
        (∑' m : ℤ, complexPoissonAliasTerm φ L T z z' m) := by
  obtain ⟨Λ, hΛ, hsupp⟩ := exists_nonneg_support_abs_bound hcompact
  exact hasSum_paperFT_mul_paperFT_alias hL hΛ hφ hsupp z z'

end Poisson
end Zeta23

end
