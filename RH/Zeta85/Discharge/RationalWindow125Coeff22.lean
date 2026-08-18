/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125Coeff21

open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem centeredCoeffFormula125_44 (u : ℝ) :
    centeredCoeffFormula125 u 44 =
      23929682090102444635408141090477641 / 20480000000 + (191767288553095528425725066284176897 / 12800000000) * u ^ 2 + (460039539383897019444529897802642343 / 5120000000) * u ^ 4 + (4315194839532809498464990407360284631 / 12800000000) * u ^ 6 + (45158820513685178563062346073799921831 / 51200000000) * u ^ 8 + (4295744562351364347133733181216462603 / 2560000000) * u ^ 10 + (2370838954378148611812041788446592347 / 1024000000) * u ^ 12 + (5579632954919914259496817280751773613 / 2560000000) * u ^ 14 + (115118439431875286225078506228025856813 / 102400000000) * u ^ 16 := by
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
    zero_mul, mul_zero, zero_add, add_zero]
  norm_num (config := { maxSteps := 1000000 })
    [shiftedBaseCoeff125, evenCoeff125, Finset.sum_range_succ, Nat.choose]
  ring

end RationalWindow125
end Zeta85
end RH
