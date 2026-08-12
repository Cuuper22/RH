/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125Coeff30
import RH.Zeta85.Discharge.RationalWindow125AutocorrBaseData

open scoped BigOperators Polynomial

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

def polynomialOfList125 (c : List ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range c.length,
    Polynomial.C (c.getD k 0) * Polynomial.X ^ k

theorem polynomialOfList125_coeff {c : List ℝ} {k : ℕ} (hk : k < c.length) :
    (polynomialOfList125 c).coeff k = c.getD k 0 := by
  classical
  simp [polynomialOfList125, hk]

theorem polynomialOfList125_coeff_eq_zero {c : List ℝ} {k : ℕ}
    (hk : c.length ≤ k) :
    (polynomialOfList125 c).coeff k = 0 := by
  classical
  simp [polynomialOfList125, hk]

def listedCenteredPolynomial125 (u : ℝ) : Polynomial ℝ :=
  polynomialOfList125 (centeredCoeffBase125 u)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem centeredPolynomial125_eq_listed (u : ℝ) :
    centeredPolynomial125 u = listedCenteredPolynomial125 u := by
  ext n
  by_cases hn : n < 61
  · have hn63 : n < 63 := by omega
    unfold listedCenteredPolynomial125
    interval_cases n
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_0 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 1),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_2 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 3),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_4 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 5),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_6 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 7),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_8 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 9),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_10 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 11),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_12 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 13),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_14 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 15),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_16 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 17),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_18 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 19),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_20 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 21),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_22 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 23),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_24 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 25),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_26 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 27),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_28 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 29),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_30 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 31),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_32 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 33),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_34 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 35),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_36 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 37),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_38 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 39),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_40 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 41),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_42 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 43),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_44 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 45),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_46 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 47),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_48 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 49),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_50 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 51),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_52 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 53),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_54 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 55),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_56 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 57),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_58 u
    · rw [centeredPolynomial125_coeff_odd (by norm_num : Odd 59),
        polynomialOfList125_coeff hn]
      rfl
    · rw [centeredPolynomial125_coeff hn63,
        polynomialOfList125_coeff hn]
      simpa [centeredCoeffBase125, centeredCoeffBase125Part0,
        centeredCoeffBase125Part1, centeredCoeffBase125Part2,
        centeredCoeffBase125Part3, centeredCoeffBase125Part4,
        centeredCoeffBase125Part5, centeredCoeffBase125Part6,
        centeredCoeffBase125Part7] using centeredCoeffFormula125_60 u
  · rw [centeredPolynomial125_coeff_eq_zero_of_ge61 (by omega)]
    unfold listedCenteredPolynomial125
    symm
    apply polynomialOfList125_coeff_eq_zero
    norm_num [centeredCoeffBase125, centeredCoeffBase125Part0,
      centeredCoeffBase125Part1, centeredCoeffBase125Part2,
      centeredCoeffBase125Part3, centeredCoeffBase125Part4,
      centeredCoeffBase125Part5, centeredCoeffBase125Part6,
      centeredCoeffBase125Part7]
    omega

theorem centered_product_base125_certified (u x : ℝ) :
    base125 (x - u / 2) * base125 (x + u / 2) =
      polyEval125 (centeredCoeffBase125 u) x := by
  rw [← eval_centeredPolynomial125, centeredPolynomial125_eq_listed]
  unfold listedCenteredPolynomial125 polynomialOfList125 polyEval125
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp

end RationalWindow125
end Zeta85
end RH
