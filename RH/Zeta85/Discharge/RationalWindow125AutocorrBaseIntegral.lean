/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125CenteredCertificate

open scoped BigOperators
open Set intervalIntegral MeasureTheory
noncomputable section
namespace RH
namespace Zeta85
namespace RationalWindow125

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem centered_integral_base125 (u : ℝ) :
    (∫ x in (-(1 - u) / 2)..((1 - u) / 2),
      base125 (x - u / 2) * base125 (x + u / 2)) = autocorrBase125 u := by
  rw [intervalIntegral.integral_congr
      (fun x _ => centered_product_base125_certified u x),
    integral_polyEval125]
  simp [polyInt125, centeredCoeffBase125, centeredCoeffBase125Part0,
    centeredCoeffBase125Part1, centeredCoeffBase125Part2,
    centeredCoeffBase125Part3, centeredCoeffBase125Part4,
    centeredCoeffBase125Part5, centeredCoeffBase125Part6,
    centeredCoeffBase125Part7, autocorrBase125,
    polyEval125, autocorrCoeffBase125, Finset.sum_range_succ]
  ring

theorem integral_autocorr_base125 (u : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u), base125 s * base125 (s + u)) =
      autocorrBase125 u := by
  calc
    _ = ∫ x in (-(1 : ℝ) / 2 + u / 2)..(1 / 2 - u + u / 2),
        base125 (x - u / 2) * base125 (x + u / 2) := by
      rw [← intervalIntegral.integral_comp_add_right
        (f := fun x => base125 (x - u / 2) * base125 (x + u / 2)) (u / 2)]
      apply intervalIntegral.integral_congr
      intro s hs
      congr 1 <;> ring
    _ = ∫ x in (-(1 - u) / 2)..((1 - u) / 2),
        base125 (x - u / 2) * base125 (x + u / 2) := by
      rw [show (-(1 : ℝ) / 2 + u / 2) = -(1 - u) / 2 by ring,
        show (1 / 2 - u + u / 2 : ℝ) = (1 - u) / 2 by ring]
    _ = autocorrBase125 u := centered_integral_base125 u

end RationalWindow125
end Zeta85
end RH
