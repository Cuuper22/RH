/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125BaseDefs

open scoped BigOperators
open Set intervalIntegral MeasureTheory

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

def shiftedBaseCoeff125 (a : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range evenCoeff125.length,
    evenCoeff125.getD i 0 * ((2 * i).choose k : ℝ) * a ^ (2 * i - k)

def centeredCoeffFormula125 (u : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
    shiftedBaseCoeff125 (-u / 2) p.1 * shiftedBaseCoeff125 (u / 2) p.2

theorem evenPoly125_shift (c : List ℝ) (a x : ℝ) :
    evenPoly125 c (x + a) =
      ∑ k ∈ Finset.range (2 * c.length),
        (∑ i ∈ Finset.range c.length,
          c.getD i 0 * ((2 * i).choose k : ℝ) * a ^ (2 * i - k)) * x ^ k := by
  unfold evenPoly125
  calc
    _ = ∑ i ∈ Finset.range c.length, ∑ k ∈ Finset.range (2 * c.length),
        c.getD i 0 * ((2 * i).choose k : ℝ) * x ^ k * a ^ (2 * i - k) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        c.getD i 0 * (x + a) ^ (2 * i) =
            ∑ k ∈ Finset.range (2 * i + 1),
              c.getD i 0 * ((2 * i).choose k : ℝ) * x ^ k *
                a ^ (2 * i - k) := by
          rw [add_pow, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = ∑ k ∈ Finset.range (2 * c.length),
              c.getD i 0 * ((2 * i).choose k : ℝ) * x ^ k *
                a ^ (2 * i - k) := by
          apply Finset.sum_subset
          · intro k hk
            simp only [Finset.mem_range] at hi hk ⊢
            omega
          · intro k hk hkn
            simp only [Finset.mem_range] at hk
            have hik : 2 * i < k := by
              simp only [Finset.mem_range, not_lt] at hkn
              omega
            rw [Nat.choose_eq_zero_of_lt hik]
            norm_num
    _ = ∑ k ∈ Finset.range (2 * c.length),
        (∑ i ∈ Finset.range c.length,
          c.getD i 0 * ((2 * i).choose k : ℝ) * a ^ (2 * i - k)) * x ^ k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem base125_shift (a x : ℝ) :
    base125 (x + a) =
      ∑ k ∈ Finset.range 32, shiftedBaseCoeff125 a k * x ^ k := by
  rw [base125_eq_evenPoly, evenPoly125_shift]
  norm_num [shiftedBaseCoeff125, evenCoeff125]

theorem coeff_comp_neg_X125 (p : Polynomial ℝ) (n : ℕ) :
    (p.comp (-Polynomial.X)).coeff n = (-1 : ℝ) ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq]
      ring
  | monomial m a =>
      have hpow : (-Polynomial.X : Polynomial ℝ) ^ m =
          Polynomial.C ((-1 : ℝ) ^ m) * Polynomial.X ^ m := by
        calc
          _ = (Polynomial.C (-1 : ℝ) * Polynomial.X) ^ m := by
            congr 1
            simp
          _ = Polynomial.C (-1 : ℝ) ^ m * Polynomial.X ^ m := by
            rw [mul_pow]
          _ = _ := by simp
      rw [Polynomial.monomial_comp, hpow, ← mul_assoc, ← Polynomial.C_mul,
        Polynomial.C_mul_X_pow_eq_monomial]
      by_cases h : m = n
      · subst n
        simp [Polynomial.coeff_monomial, mul_comm]
      · simp [Polynomial.coeff_monomial, h]

theorem shiftedBaseCoeff125_eq_zero {a : ℝ} {k : ℕ} (hk : 31 ≤ k) :
    shiftedBaseCoeff125 a k = 0 := by
  unfold shiftedBaseCoeff125
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < 16 := by
    simpa [evenCoeff125] using hi
  have hik : 2 * i < k := by omega
  rw [Nat.choose_eq_zero_of_lt hik]
  norm_num

def shiftedPolynomial125 (a : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range 63,
    Polynomial.C (shiftedBaseCoeff125 a k) * Polynomial.X ^ k

theorem shiftedPolynomial125_coeff {a : ℝ} {k : ℕ} (hk : k < 63) :
    (shiftedPolynomial125 a).coeff k = shiftedBaseCoeff125 a k := by
  classical
  simp [shiftedPolynomial125, hk]

theorem shiftedPolynomial125_coeff_eq_zero {a : ℝ} {k : ℕ} (hk : 63 ≤ k) :
    (shiftedPolynomial125 a).coeff k = 0 := by
  classical
  simp [shiftedPolynomial125, hk]

theorem shiftedPolynomial125_coeff_eq_zero_of_ge31 {a : ℝ} {k : ℕ}
    (hk : 31 ≤ k) :
    (shiftedPolynomial125 a).coeff k = 0 := by
  by_cases hk63 : k < 63
  · rw [shiftedPolynomial125_coeff hk63,
      shiftedBaseCoeff125_eq_zero hk]
  · exact shiftedPolynomial125_coeff_eq_zero (by omega)

theorem eval_shiftedPolynomial125 (a x : ℝ) :
    (shiftedPolynomial125 a).eval x = base125 (x + a) := by
  rw [base125_shift]
  simp only [shiftedPolynomial125, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hkn
    simp only [Finset.mem_range, not_lt] at hkn
    rw [shiftedBaseCoeff125_eq_zero (by omega)]
    norm_num

def centeredPolynomial125 (u : ℝ) : Polynomial ℝ :=
  shiftedPolynomial125 (-u / 2) * shiftedPolynomial125 (u / 2)

theorem centeredPolynomial125_coeff {u : ℝ} {n : ℕ} (hn : n < 63) :
    (centeredPolynomial125 u).coeff n = centeredCoeffFormula125 u n := by
  classical
  rw [centeredPolynomial125, Polynomial.coeff_mul]
  unfold centeredCoeffFormula125
  apply Finset.sum_congr rfl
  intro p hp
  have hpadd : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [shiftedPolynomial125_coeff (by omega),
    shiftedPolynomial125_coeff (by omega)]

theorem eval_centeredPolynomial125 (u x : ℝ) :
    (centeredPolynomial125 u).eval x =
      base125 (x - u / 2) * base125 (x + u / 2) := by
  simp only [centeredPolynomial125, Polynomial.eval_mul,
    eval_shiftedPolynomial125]
  rw [show x + -u / 2 = x - u / 2 by ring]

theorem base125_even (x : ℝ) : base125 (-x) = base125 x := by
  rw [base125_eq_evenPoly]
  unfold evenPoly125
  apply Finset.sum_congr rfl
  intro i hi
  rw [Even.neg_pow (even_two_mul i)]

theorem centeredPolynomial125_even (u : ℝ) :
    (centeredPolynomial125 u).comp (-Polynomial.X) = centeredPolynomial125 u := by
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_neg, Polynomial.eval_X]
  rw [eval_centeredPolynomial125, eval_centeredPolynomial125]
  have h₁ : base125 (-x - u / 2) = base125 (x + u / 2) := by
    rw [← base125_even (x + u / 2)]
    congr 1
    ring
  have h₂ : base125 (-x + u / 2) = base125 (x - u / 2) := by
    rw [← base125_even (x - u / 2)]
    congr 1
    ring
  rw [h₁, h₂]
  ring

theorem centeredPolynomial125_coeff_odd {u : ℝ} {n : ℕ} (hn : Odd n) :
    (centeredPolynomial125 u).coeff n = 0 := by
  have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff n)
    (centeredPolynomial125_even u)
  rw [coeff_comp_neg_X125, hn.neg_one_pow] at hcoeff
  linarith

theorem centeredPolynomial125_coeff_eq_zero_of_ge61 {u : ℝ} {n : ℕ}
    (hn : 61 ≤ n) :
    (centeredPolynomial125 u).coeff n = 0 := by
  rw [centeredPolynomial125, Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hpadd : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rcases le_or_gt 31 p.1 with hp₁ | hp₁
  · rw [shiftedPolynomial125_coeff_eq_zero_of_ge31 hp₁, zero_mul]
  · have hp₂ : 31 ≤ p.2 := by omega
    rw [shiftedPolynomial125_coeff_eq_zero_of_ge31 hp₂, mul_zero]

end RationalWindow125
end Zeta85
end RH
