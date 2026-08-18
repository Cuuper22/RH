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

def baseL2 : ℝ := 596368779793682202819677 / 587889540424265625000000

theorem integral_base125_sq :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), base125 s ^ 2) = baseL2 := by
  rw [base125_eq_evenPoly, integral_evenPoly125_sq]
  norm_num [evenSquareInt125, evenCoeff125, baseL2, Finset.sum_range_succ]


end RationalWindow125
end Zeta85
end RH
