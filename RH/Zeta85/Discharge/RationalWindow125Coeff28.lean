/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125Coeff27

open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem centeredCoeffFormula125_56 (u : ℝ) :
    centeredCoeffFormula125 u 56 =
      45843227478095079894576398371634947 / 625000000 + (18660979782340850366210091239972487 / 62500000) * u ^ 2 + (42779055901848861473459125316992143 / 125000000) * u ^ 4 := by
  rw [centeredCoeffFormula125]
  norm_num (config := { maxSteps := 1000000 })
    [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]
  simp only [shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 31),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 32),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 33),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 34),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 35),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 36),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 37),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 38),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 39),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 40),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 41),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 42),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 43),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 44),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 45),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 46),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 47),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 48),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 49),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 50),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 51),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 52),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 53),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 54),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 55),
    shiftedBaseCoeff125_eq_zero (by norm_num : 31 ≤ 56),
    zero_mul, mul_zero, zero_add, add_zero]
  norm_num (config := { maxSteps := 1000000 })
    [shiftedBaseCoeff125, evenCoeff125, Finset.sum_range_succ, Nat.choose]
  ring

end RationalWindow125
end Zeta85
end RH
