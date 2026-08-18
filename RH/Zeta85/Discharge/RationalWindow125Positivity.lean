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

def bern125 : List ℝ :=
  [7645688113687 / 6710886400000,
   3723582315107 / 3355443200000,
   679224451723 / 629145600000,
   2871332125473 / 2726297600000,
   2435507936441 / 2385510400000,
   333761042577 / 340787200000,
   16842764776151 / 16400384000000,
   1891768286261 / 2342912000000,
   472269133067 / 439296000000,
   54318265531 / 73216000000,
   1745090257 / 1830400000,
   13877282411 / 17472000000,
   46429281 / 56000000,
   4414069 / 5600000,
   2310763 / 3000000,
   37407 / 50000]

set_option maxRecDepth 100000 in
theorem base125_eq_bernstein (s : ℝ) :
    base125 s = bernsteinEval125 15 bern125 (4 * s ^ 2) := by
  simp [base125, bernsteinEval125, bern125, Finset.sum_range_succ]
  norm_num [Nat.choose]
  ring

theorem bern125_lower (k : ℕ) (hk : k ∈ Finset.range 16) :
    (54318265531 / 73216000000 : ℝ) ≤ bern125.getD k 0 := by
  simp only [Finset.mem_range] at hk
  interval_cases k <;> norm_num [bern125]

theorem base125_pos {s : ℝ} (hs : |s| ≤ 1 / 2) : 0 < base125 s := by
  rw [base125_eq_bernstein]
  have hs' := abs_le.mp hs
  have hs2 : s ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hlower := bernsteinEval125_lower_bound 15 bern125
    (54318265531 / 73216000000) (4 * s ^ 2) (by positivity) (by nlinarith)
      bern125_lower
  exact lt_of_lt_of_le (by norm_num) hlower

end RationalWindow125
end Zeta85
end RH
