/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125Coeff24

open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem centeredCoeffFormula125_50 (u : ℝ) :
    centeredCoeffFormula125 u 50 =
      -121939474413536986869844519828274967 / 4000000000 - (5414407053148372982782223044107242217 / 20000000000) * u ^ 2 - (2129563512140130642314361949106964183 / 2000000000) * u ^ 4 - (23533893652692072916424117880730102293 / 10000000000) * u ^ 6 - (11887044121351121683275828119862474219 / 4000000000) * u ^ 8 - (35036046783614217546763023634616565117 / 20000000000) * u ^ 10 := by
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
    zero_mul, mul_zero, zero_add, add_zero]
  norm_num (config := { maxSteps := 1000000 })
    [shiftedBaseCoeff125, evenCoeff125, Finset.sum_range_succ, Nat.choose]
  ring

end RationalWindow125
end Zeta85
end RH
