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
        ring
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
    complexGaux_continuous hL hφ.continuous
      (fun u hu => hsupp u (lt_of_le_of_lt hu (by linarith)))
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
    have hzeroHalf : ∀ u, L / 2 ≤ |u| → φ u = 0 := by
      intro u hu
      by_cases hrad : Λ < |u|
      · exact hsupp u hrad
      · have hsmall : |u| ≤ Λ := not_lt.mp hrad
        exact False.elim (by
          have : L / 2 ≤ Λ := le_trans hu hsmall
          have hLamb : Λ < L / 2 := by
            nlinarith [hΛ, hL]
          linarith)
    rw [fourier_complexGaux hL hφ.continuous hzeroHalf]
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
  have hzeroHalf : ∀ u, L / 2 ≤ |u| → φ u = 0 := by
    intro u hu
    by_cases hrad : Λ < |u|
    · exact hsupp u hrad
    · have hsmall : |u| ≤ Λ := not_lt.mp hrad
      exact False.elim (by
        have : L / 2 ≤ Λ := le_trans hu hsmall
        have hLamb : Λ < L / 2 := by
          nlinarith [hΛ, hL]
        linarith)
  rw [fourier_complexGaux hL hφ.continuous hzeroHalf]

end Poisson
end Zeta23

end
