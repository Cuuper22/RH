/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Certificate
import RH.Zeta85.Statement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Algebraic rational-moment windows for the lower support rungs

The support-`101/100` frozen decimal does not require a transcendental
Montgomery--Taylor profile.  A quadratic profile with one algebraic
coefficient realizes the exact rational cost.  All moments reduce to
polynomial interval integrals, while the coefficient itself is the explicit
root of a rational quadratic equation.
-/

open intervalIntegral MeasureTheory

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindowCosts

def quadProfile (a s : ℝ) : ℝ := 1 - a * s ^ 2

def quadG (a u : ℝ) : ℝ :=
  (1 - a / 6 + a ^ 2 / 80)
    + (-1 + a / 2 - a ^ 2 / 16) * u
    + (-a + a ^ 2 / 12) * u ^ 2
    + (2 * a / 3) * u ^ 3
    - (a ^ 2 / 30) * u ^ 5

theorem integral_quadProfile (a : ℝ) :
    (∫ s in (-(1:ℝ)/2)..(1/2), quadProfile a s) = 1 - a / 12 := by
  simp only [quadProfile]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((intervalIntegral.intervalIntegrable_pow 2).const_mul _)]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem integral_quadProfile_sq (a : ℝ) :
    (∫ s in (-(1:ℝ)/2)..(1/2), quadProfile a s ^ 2) =
      1 - a / 6 + a ^ 2 / 80 := by
  have hrw : ∀ s : ℝ, quadProfile a s ^ 2 =
      1 - (2 * a) * s ^ 2 + a ^ 2 * s ^ 4 := by
    intro s
    simp only [quadProfile]
    ring
  simp only [hrw]
  rw [intervalIntegral.integral_add
      ((intervalIntegrable_const.sub
        ((intervalIntegral.intervalIntegrable_pow 2).const_mul _)))
      ((intervalIntegral.intervalIntegrable_pow 4).const_mul _),
    intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegral.intervalIntegrable_pow 2).const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem integral_quad_autocorr (a u : ℝ) :
    (∫ s in (-(1:ℝ)/2)..(1/2 - u),
      quadProfile a s * quadProfile a (s + u)) = quadG a u := by
  have hrw : ∀ s : ℝ, quadProfile a s * quadProfile a (s + u) =
      (1 - a * u ^ 2)
        + (-2 * a * u) * s ^ 1
        + (-2 * a + a ^ 2 * u ^ 2) * s ^ 2
        + (2 * a ^ 2 * u) * s ^ 3
        + a ^ 2 * s ^ 4 := by
    intro s
    simp only [quadProfile]
    ring
  simp only [hrw]
  have hint : ∀ (c : ℝ) (n : ℕ),
      IntervalIntegrable (fun s : ℝ => c * s ^ n) volume
        (-(1:ℝ)/2) (1/2 - u) :=
    fun c n => (intervalIntegral.intervalIntegrable_pow n).const_mul c
  rw [intervalIntegral.integral_add
        (((intervalIntegrable_const.add (hint _ 1)).add (hint _ 2)).add (hint _ 3)) (hint _ 4),
      intervalIntegral.integral_add
        ((intervalIntegrable_const.add (hint _ 1)).add (hint _ 2)) (hint _ 3),
      intervalIntegral.integral_add (intervalIntegrable_const.add (hint _ 1)) (hint _ 2),
      intervalIntegral.integral_add intervalIntegrable_const (hint _ 1)]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul, quadG]
  ring

def quadGAnti (a u : ℝ) : ℝ :=
  (1 - a / 6 + a ^ 2 / 80) * u
    + (-1 + a / 2 - a ^ 2 / 16) * u ^ 2 / 2
    + (-a + a ^ 2 / 12) * u ^ 3 / 3
    + (2 * a / 3) * u ^ 4 / 4
    - (a ^ 2 / 30) * u ^ 6 / 6

def uQuadGAnti (a u : ℝ) : ℝ :=
  (1 - a / 6 + a ^ 2 / 80) * u ^ 2 / 2
    + (-1 + a / 2 - a ^ 2 / 16) * u ^ 3 / 3
    + (-a + a ^ 2 / 12) * u ^ 4 / 4
    + (2 * a / 3) * u ^ 5 / 5
    - (a ^ 2 / 30) * u ^ 7 / 7

theorem integral_quadG (a x y : ℝ) :
    (∫ u in x..y, quadG a u) = quadGAnti a y - quadGAnti a x := by
  have hint : ∀ (c : ℝ) (n : ℕ),
      IntervalIntegrable (fun u : ℝ => c * u ^ n) volume x y :=
    fun c n => (intervalIntegral.intervalIntegrable_pow n).const_mul c
  have hrw : ∀ u : ℝ, quadG a u =
      (1 - a / 6 + a ^ 2 / 80)
        + (-1 + a / 2 - a ^ 2 / 16) * u ^ 1
        + (-a + a ^ 2 / 12) * u ^ 2
        + (2 * a / 3) * u ^ 3
        + (-(a ^ 2 / 30)) * u ^ 5 := by
    intro u
    simp only [quadG]
    ring
  simp only [hrw]
  rw [intervalIntegral.integral_add
      (((intervalIntegrable_const.add (hint _ 1)).add (hint _ 2)).add (hint _ 3)) (hint _ 5),
    intervalIntegral.integral_add
      ((intervalIntegrable_const.add (hint _ 1)).add (hint _ 2)) (hint _ 3),
    intervalIntegral.integral_add (intervalIntegrable_const.add (hint _ 1)) (hint _ 2),
    intervalIntegral.integral_add intervalIntegrable_const (hint _ 1)]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul, quadGAnti]
  ring

theorem integral_u_quadG (a x y : ℝ) :
    (∫ u in x..y, u * quadG a u) = uQuadGAnti a y - uQuadGAnti a x := by
  have hint : ∀ (c : ℝ) (n : ℕ),
      IntervalIntegrable (fun u : ℝ => c * u ^ n) volume x y :=
    fun c n => (intervalIntegral.intervalIntegrable_pow n).const_mul c
  have hrw : ∀ u : ℝ, u * quadG a u =
      (1 - a / 6 + a ^ 2 / 80) * u ^ 1
        + (-1 + a / 2 - a ^ 2 / 16) * u ^ 2
        + (-a + a ^ 2 / 12) * u ^ 3
        + (2 * a / 3) * u ^ 4
        + (-(a ^ 2 / 30)) * u ^ 6 := by
    intro u
    simp only [quadG]
    ring
  simp only [hrw]
  rw [intervalIntegral.integral_add
      ((((hint _ 1).add (hint _ 2)).add (hint _ 3)).add (hint _ 4)) (hint _ 6),
    intervalIntegral.integral_add
      (((hint _ 1).add (hint _ 2)).add (hint _ 3)) (hint _ 4),
    intervalIntegral.integral_add ((hint _ 1).add (hint _ 2)) (hint _ 3),
    intervalIntegral.integral_add (hint _ 1) (hint _ 2)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, uQuadGAnti]
  ring

theorem satJ_quad_101 (a : ℝ) :
    satJ (101 / 100) (quadProfile a) =
      10303 / 30603 - (42040301 / 624362406) * a
        + (3216384632947 / 1070012311805808) * a ^ 2 := by
  simp only [satJ, integral_quad_autocorr]
  rw [integral_u_quadG, integral_quadG]
  simp only [quadGAnti, uQuadGAnti]
  ring

def qA101 : ℝ :=
  664508364374437099043549 / 105941813050080000000000000

def qB101 : ℝ := -763250806985829107 / 61818060000000000000

def qC101 : ℝ := 18405295653121 / 3030000000000000

def qDisc101 : ℝ := qB101 ^ 2 - 4 * qA101 * qC101

def a101 : ℝ := (-qB101 - Real.sqrt qDisc101) / (2 * qA101)

lemma qA101_pos : 0 < qA101 := by norm_num [qA101]

lemma qDisc101_pos : 0 < qDisc101 := by
  norm_num [qDisc101, qA101, qB101, qC101]

lemma a101_root : qA101 * a101 ^ 2 + qB101 * a101 + qC101 = 0 := by
  have hs : (Real.sqrt qDisc101) ^ 2 = qDisc101 :=
    Real.sq_sqrt (le_of_lt qDisc101_pos)
  rw [a101]
  field_simp [ne_of_gt qA101_pos]
  rw [qDisc101] at hs ⊢
  ring_nf at hs ⊢
  nlinarith

lemma a101_lt_one : a101 < 1 := by
  have hs0 : 0 ≤ Real.sqrt qDisc101 := Real.sqrt_nonneg _
  rw [a101]
  have hden : 0 < 2 * qA101 := mul_pos (by norm_num) qA101_pos
  apply (div_lt_iff₀ hden).2
  have hBA : -qB101 < 2 * qA101 := by norm_num [qA101, qB101]
  linarith

/-- Exact algebraic replacement for the support-`101/100` transcendental
window axiom. -/
theorem windowCost_101 :
    SaturatedWindowCost (101 / 100) (2 - cRung101) := by
  refine ⟨quadProfile a101, ?_, ?_, ?_⟩
  · intro s hs
    have hs2 : s ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      have habs := abs_le.mp hs
      nlinarith [habs.1, habs.2]
    have hnonneg : 0 ≤ (1 - a101) * s ^ 2 :=
      mul_nonneg (sub_nonneg.mpr a101_lt_one.le) (sq_nonneg s)
    simp only [quadProfile]
    nlinarith
  · rw [integral_quadProfile]
    linarith [a101_lt_one]
  · rw [integral_quadProfile, integral_quadProfile_sq, satJ_quad_101]
    have hroot := a101_root
    norm_num [cRung101, qA101, qB101, qC101] at hroot ⊢
    nlinarith

end RationalWindowCosts
end Zeta85
end RH

end
