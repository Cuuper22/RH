/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Certificate
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
open Set intervalIntegral MeasureTheory

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

def polyEval125 (c : List ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range c.length, c.getD k 0 * x ^ k

def polyInt125 (c : List ℝ) (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.range c.length,
    c.getD k 0 * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1))

theorem integral_polyEval125 (c : List ℝ) (a b : ℝ) :
    ∫ x in a..b, polyEval125 c x = polyInt125 c a b := by
  unfold polyEval125 polyInt125
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
  · intro k _
    exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _

def evenPoly125 (c : List ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range c.length, c.getD i 0 * x ^ (2 * i)

def evenSquareInt125 (c : List ℝ) (a b : ℝ) : ℝ :=
  ∑ i ∈ Finset.range c.length, ∑ j ∈ Finset.range c.length,
    c.getD i 0 * c.getD j 0 *
      ((b ^ (2 * i + 2 * j + 1) - a ^ (2 * i + 2 * j + 1)) /
        (2 * i + 2 * j + 1))

theorem integral_evenPoly125_sq (c : List ℝ) (a b : ℝ) :
    (∫ x in a..b, evenPoly125 c x ^ 2) = evenSquareInt125 c a b := by
  have hrw : (fun x : ℝ => evenPoly125 c x ^ 2) = fun x =>
      ∑ i ∈ Finset.range c.length, ∑ j ∈ Finset.range c.length,
        (c.getD i 0 * c.getD j 0) * x ^ (2 * i + 2 * j) := by
    funext x
    simp only [evenPoly125, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    ring
  rw [hrw]
  unfold evenSquareInt125
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    · intro j hj
      exact (continuous_const.mul (continuous_pow (2 * i + 2 * j))).intervalIntegrable _ _
  · intro i hi
    exact (continuous_finset_sum _ fun j _ =>
      continuous_const.mul (continuous_pow (2 * i + 2 * j))).intervalIntegrable _ _

def bernsteinEval125 (n : ℕ) (c : List ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    c.getD k 0 * (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)

lemma bernsteinEval125_lower_bound (n : ℕ) (c : List ℝ) (m x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hc : ∀ k ∈ Finset.range (n + 1), m ≤ c.getD k 0) :
    m ≤ bernsteinEval125 n c x := by
  have hpart : ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k) = 1 := by
    calc
      _ = (x + (1 - x)) ^ n := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = 1 := by ring
  calc
    m = ∑ k ∈ Finset.range (n + 1),
        m * ((n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)) := by
          rw [← Finset.mul_sum, hpart, mul_one]
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        c.getD k 0 * ((n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)) := by
          apply Finset.sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_right (hc k hk)
          positivity
    _ = bernsteinEval125 n c x := by
          unfold bernsteinEval125
          apply Finset.sum_congr rfl
          intro k hk
          ring

def sigma125 : ℝ := 1249999999999 / 1000000000000
def target125 : ℝ := 120278584713866 / 100000000000000

def base125 (s : ℝ) : ℝ :=
  7645688113687 / 6710886400000 - (595570450419 / 335544320000) * s ^ 2 - (75186895609 / 83886080000) * s ^ 4 + (2595118391481 / 20971520000) * s ^ 6 - (25291958737617 / 5242880000) * s ^ 8 + (400307634879581 / 6553600000) * s ^ 10 + (2555348686469943 / 1638400000) * s ^ 12 - (1258945831244799 / 16384000) * s ^ 14 + (30261158955250641 / 20480000) * s ^ 16 - (17356714360724277 / 1024000) * s ^ 18 + (163320987777848901 / 1280000) * s ^ 20 - (207489038793037989 / 320000) * s ^ 22 + (35379168476765841 / 16000) * s ^ 24 - (486062152105760433 / 100000) * s ^ 26 + (31168414198098793 / 5000) * s ^ 28 - (22174609043411517 / 6250) * s ^ 30

def coeff125 : List ℝ :=
[
    7645688113687 / 6710886400000,
    0,
    -595570450419 / 335544320000,
    0,
    -75186895609 / 83886080000,
    0,
    2595118391481 / 20971520000,
    0,
    -25291958737617 / 5242880000,
    0,
    400307634879581 / 6553600000,
    0,
    2555348686469943 / 1638400000,
    0,
    -1258945831244799 / 16384000,
    0,
    30261158955250641 / 20480000,
    0,
    -17356714360724277 / 1024000,
    0,
    163320987777848901 / 1280000,
    0,
    -207489038793037989 / 320000,
    0,
    35379168476765841 / 16000,
    0,
    -486062152105760433 / 100000,
    0,
    31168414198098793 / 5000,
    0,
    -22174609043411517 / 6250
  ]

def evenCoeff125 : List ℝ :=
[
    7645688113687 / 6710886400000,
    -595570450419 / 335544320000,
    -75186895609 / 83886080000,
    2595118391481 / 20971520000,
    -25291958737617 / 5242880000,
    400307634879581 / 6553600000,
    2555348686469943 / 1638400000,
    -1258945831244799 / 16384000,
    30261158955250641 / 20480000,
    -17356714360724277 / 1024000,
    163320987777848901 / 1280000,
    -207489038793037989 / 320000,
    35379168476765841 / 16000,
    -486062152105760433 / 100000,
    31168414198098793 / 5000,
    -22174609043411517 / 6250
  ]

set_option maxRecDepth 100000 in
theorem base125_eq_polyEval :
    base125 = polyEval125 coeff125 := by
  funext s
  simp [base125, polyEval125, coeff125, Finset.sum_range_succ]
  ring

set_option maxRecDepth 100000 in
theorem base125_eq_evenPoly :
    base125 = evenPoly125 evenCoeff125 := by
  funext s
  simp [base125, evenPoly125, evenCoeff125, Finset.sum_range_succ]
  ring

theorem integral_base125 :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), base125 s) = 1 := by
  rw [base125_eq_polyEval, integral_polyEval125]
  norm_num [polyInt125, coeff125, Finset.sum_range_succ]


end RationalWindow125
end Zeta85
end RH
