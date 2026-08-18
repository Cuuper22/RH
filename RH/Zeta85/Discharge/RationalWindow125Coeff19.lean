/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125Coeff18

open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem centeredCoeffFormula125_38 (u : ℝ) :
    centeredCoeffFormula125 u 38 =
      -270162795543718061464877785002165967 / 40960000000000 - (192551828869769195157863062587170751 / 1638400000000) * u ^ 2 - (7537260590082275916516264571779508689 / 8192000000000) * u ^ 4 - (1471349125872110694469187813899342329 / 327680000000) * u ^ 6 - (12891368697652571442610536909215319771 / 819200000000) * u ^ 8 - (174475293349033731769897215685345861167 / 4096000000000) * u ^ 10 - (75931693141961617058694862396154773749 / 819200000000) * u ^ 12 - (135472384243765862587055839764034601253 / 819200000000) * u ^ 14 - (397592582719942387987822001871180605907 / 1638400000000) * u ^ 16 - (472174346823408966624752894419802751339 / 1638400000000) * u ^ 18 - (429631737528833397981254930617886568201 / 1638400000000) * u ^ 20 - (268609692007709001191849847865393665897 / 1638400000000) * u ^ 22 := by
  norm_num (config := { maxSteps := 1000000 })
    [centeredCoeffFormula125, shiftedBaseCoeff125, evenCoeff125,
      Finset.sum_range_succ, Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, Nat.choose]
  ring

end RationalWindow125
end Zeta85
end RH
