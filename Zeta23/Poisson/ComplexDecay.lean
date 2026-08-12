/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Zeta23.Poisson

/-!
# Horizontal complex decay for Poisson summation

The real-frequency Poisson theorem already controls the paper Fourier
transform on the real axis.  This file supplies the corresponding decay on
an arbitrary fixed horizontal line in the complex plane.  Compact support
keeps the exponential factor uniform, while two integrations by parts give
quadratic decay in the real direction.
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

noncomputable section

namespace Zeta23
namespace Poisson

/-- A compact twice continuously differentiable window has a uniform
quadratic Fourier bound on every fixed horizontal complex line. -/
theorem paperFT_horizontal_decay
    {f : ℝ → ℂ} {Λ : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (z : ℂ) :
    ∃ C : ℝ, ∀ s : ℝ,
      ‖paperFT f (z - s)‖ * (1 + (z.re - s) ^ 2) ≤ C := by
  have hcompact : HasCompactSupport f :=
    hasCompactSupport_of_support_subset_abs hsupp
  have hfi : Integrable f :=
    hf.continuous.integrable_of_hasCompactSupport hcompact
  refine ⟨
    Real.exp (|z.im| * Λ) * (∫ u, ‖f u‖) +
      Real.exp (|z.im| * Λ) * (∫ u, ‖deriv (deriv f) u‖),
    ?_⟩
  intro s
  let w : ℂ := z - s
  have h0 := norm_paperFT_le hfi hsupp w
  have h2 := norm_paperFT_mul_sq_le hf hsupp w
  have him : w.im = z.im := by
    simp [w]
  rw [him] at h0 h2
  have hre : (z.re - s) ^ 2 ≤ ‖w‖ ^ 2 := by
    have hsq := Complex.sq_norm_sub_sq_re w
    have hwre : w.re = z.re - s := by
      simp [w]
    rw [hwre] at hsq
    nlinarith [sq_nonneg w.im]
  have h2re :
      ‖paperFT f w‖ * (z.re - s) ^ 2 ≤
        Real.exp (|z.im| * Λ) * ∫ u, ‖deriv (deriv f) u‖ := by
    exact
      (mul_le_mul_of_nonneg_left hre (norm_nonneg _)).trans h2
  change
    ‖paperFT f w‖ * (1 + (z.re - s) ^ 2) ≤
      Real.exp (|z.im| * Λ) * (∫ u, ‖f u‖) +
        Real.exp (|z.im| * Λ) * (∫ u, ‖deriv (deriv f) u‖)
  calc
    ‖paperFT f w‖ * (1 + (z.re - s) ^ 2) =
        ‖paperFT f w‖ +
          ‖paperFT f w‖ * (z.re - s) ^ 2 := by ring
    _ ≤ Real.exp (|z.im| * Λ) * (∫ u, ‖f u‖) +
          Real.exp (|z.im| * Λ) * (∫ u, ‖deriv (deriv f) u‖) :=
      add_le_add h0 h2re

/-- Two Fourier factors on the same horizontal frequency line have a
fourth-order product majorant.  Keeping both quadratic weights, rather than
discarding one factor as in the bare summability proof, is what makes the
two omitted Poisson tails quantitatively controllable. -/
theorem paperFT_mul_horizontal_decay
    {f : ℝ → ℂ} {Λ : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (z z' : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ,
      ‖paperFT f (z - s) * paperFT f (z' - s)‖ *
          ((1 + (z.re - s) ^ 2) * (1 + (z'.re - s) ^ 2)) ≤ C := by
  obtain ⟨C, hC⟩ := paperFT_horizontal_decay hf hsupp z
  obtain ⟨C', hC'⟩ := paperFT_horizontal_decay hf hsupp z'
  have hC0 : 0 ≤ C := by
    exact
      (mul_nonneg (norm_nonneg _)
        (by positivity : 0 ≤ 1 + (z.re - 0) ^ 2)).trans (hC 0)
  have hC'0 : 0 ≤ C' := by
    exact
      (mul_nonneg (norm_nonneg _)
        (by positivity : 0 ≤ 1 + (z'.re - 0) ^ 2)).trans (hC' 0)
  refine ⟨C * C', mul_nonneg hC0 hC'0, ?_⟩
  intro s
  rw [norm_mul]
  calc
    (‖paperFT f (z - s)‖ * ‖paperFT f (z' - s)‖) *
          ((1 + (z.re - s) ^ 2) * (1 + (z'.re - s) ^ 2)) =
        (‖paperFT f (z - s)‖ * (1 + (z.re - s) ^ 2)) *
          (‖paperFT f (z' - s)‖ * (1 + (z'.re - s) ^ 2)) := by ring
    _ ≤ C * C' := mul_le_mul (hC s) (hC' s) (by positivity) hC0

/-- A single quadratic Fourier majorant works simultaneously on a bounded
vertical strip.  This is the uniform form needed when the horizontal
frequency varies over all zeros in a finite height window. -/
theorem paperFT_horizontal_decay_uniform
    {f : ℝ → ℂ} {Λ B : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B)
    (z : ℂ) (hz : |z.im| ≤ B) (s : ℝ) :
    ‖paperFT f (z - s)‖ * (1 + (z.re - s) ^ 2) ≤
      Real.exp (B * Λ) *
        ((∫ u, ‖f u‖) + (∫ u, ‖deriv (deriv f) u‖)) := by
  have hcompact : HasCompactSupport f :=
    hasCompactSupport_of_support_subset_abs hsupp
  have hfi : Integrable f :=
    hf.continuous.integrable_of_hasCompactSupport hcompact
  let w : ℂ := z - s
  have h0 := norm_paperFT_le hfi hsupp w
  have h2 := norm_paperFT_mul_sq_le hf hsupp w
  have him : w.im = z.im := by simp [w]
  rw [him] at h0 h2
  have hre : (z.re - s) ^ 2 ≤ ‖w‖ ^ 2 := by
    have hsq := Complex.sq_norm_sub_sq_re w
    have hwre : w.re = z.re - s := by simp [w]
    rw [hwre] at hsq
    nlinarith [sq_nonneg w.im]
  have h2re :
      ‖paperFT f w‖ * (z.re - s) ^ 2 ≤
        Real.exp (|z.im| * Λ) * ∫ u, ‖deriv (deriv f) u‖ :=
    (mul_le_mul_of_nonneg_left hre (norm_nonneg _)).trans h2
  have hexp : Real.exp (|z.im| * Λ) ≤ Real.exp (B * Λ) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz hΛ)
  have hfInt : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
  have hdInt : 0 ≤ ∫ u, ‖deriv (deriv f) u‖ :=
    integral_nonneg fun _ => norm_nonneg _
  change ‖paperFT f w‖ * (1 + (z.re - s) ^ 2) ≤ _
  calc
    ‖paperFT f w‖ * (1 + (z.re - s) ^ 2) =
        ‖paperFT f w‖ +
          ‖paperFT f w‖ * (z.re - s) ^ 2 := by ring
    _ ≤ Real.exp (|z.im| * Λ) * (∫ u, ‖f u‖) +
          Real.exp (|z.im| * Λ) *
            (∫ u, ‖deriv (deriv f) u‖) := add_le_add h0 h2re
    _ ≤ Real.exp (B * Λ) * (∫ u, ‖f u‖) +
          Real.exp (B * Λ) *
            (∫ u, ‖deriv (deriv f) u‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hexp hfInt)
        (mul_le_mul_of_nonneg_right hexp hdInt)
    _ = Real.exp (B * Λ) *
          ((∫ u, ‖f u‖) + (∫ u, ‖deriv (deriv f) u‖)) := by ring

/-- Consequently the same fourth-order product constant works for every
pair of complex frequencies in a bounded vertical strip. -/
theorem paperFT_mul_horizontal_decay_uniform
    {f : ℝ → ℂ} {Λ B : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B)
    (z z' : ℂ) (hz : |z.im| ≤ B) (hz' : |z'.im| ≤ B)
    (s : ℝ) :
    ‖paperFT f (z - s) * paperFT f (z' - s)‖ *
        ((1 + (z.re - s) ^ 2) * (1 + (z'.re - s) ^ 2)) ≤
      (Real.exp (B * Λ) *
        ((∫ u, ‖f u‖) + (∫ u, ‖deriv (deriv f) u‖))) ^ 2 := by
  let C : ℝ := Real.exp (B * Λ) *
    ((∫ u, ‖f u‖) + (∫ u, ‖deriv (deriv f) u‖))
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hzBound := paperFT_horizontal_decay_uniform
    hf hsupp hΛ hB z hz s
  have hz'Bound := paperFT_horizontal_decay_uniform
    hf hsupp hΛ hB z' hz' s
  rw [norm_mul]
  change
    (‖paperFT f (z - s)‖ * ‖paperFT f (z' - s)‖) *
        ((1 + (z.re - s) ^ 2) * (1 + (z'.re - s) ^ 2)) ≤ C ^ 2
  calc
    (‖paperFT f (z - s)‖ * ‖paperFT f (z' - s)‖) *
          ((1 + (z.re - s) ^ 2) * (1 + (z'.re - s) ^ 2)) =
        (‖paperFT f (z - s)‖ * (1 + (z.re - s) ^ 2)) *
          (‖paperFT f (z' - s)‖ * (1 + (z'.re - s) ^ 2)) := by ring
    _ ≤ C * C := mul_le_mul hzBound hz'Bound (by positivity) hC0
    _ = C ^ 2 := by ring

/-- Along any nondegenerate affine real lattice, the complex-frequency
Fourier samples are quadratically small at infinity. -/
theorem paperFT_affine_horizontal_isBigO
    {f : ℝ → ℂ} {Λ T h : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (z : ℂ) (hh : h ≠ 0) :
    (fun w : ℝ => paperFT f (z - (T + w * h : ℝ))) =O[cocompact ℝ]
      fun w : ℝ => |w| ^ (-2 : ℝ) := by
  obtain ⟨C, hC⟩ := paperFT_horizontal_decay hf hsupp z
  apply isBigO_of_decay (c := z.re - T) (h := h) (C := C) hh
  intro w
  have hw := hC (T + w * h)
  convert hw using 1 <;> ring

/-- Therefore the complex-frequency samples on an integer affine lattice
form an absolutely summable family. -/
theorem summable_paperFT_affine_int
    {f : ℝ → ℂ} {Λ T h : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (z : ℂ) (hh : h ≠ 0) :
    Summable (fun k : ℤ =>
      paperFT f (z - (T + (k : ℝ) * h : ℝ))) := by
  have hO := paperFT_affine_horizontal_isBigO
    (T := T) (h := h) hf hsupp z hh
  exact
    (@summable_of_isBigO ℤ ℂ
      Complex.instNormedAddCommGroup.toSeminormedAddCommGroup
      Complex.instCompleteSpace _ _
      (Real.summable_abs_int_rpow one_lt_two)
      (hO.comp_tendsto Int.tendsto_coe_cofinite))

end Poisson
end Zeta23

end
