/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125Coeff19

open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem centeredCoeffFormula125_40 (u : ℝ) :
    centeredCoeffFormula125 u 40 =
      1866204285629482131052682486606571111 / 40960000000000 + (14729403605506605744691192912303071219 / 20480000000000) * u ^ 2 + (8487158583974704064192117138254817499 / 1638400000000) * u ^ 4 + (24049685352681566881365845844032513157 / 1024000000000) * u ^ 6 + (312536923466881237654083992288194001427 / 4096000000000) * u ^ 8 + (388125344867857009848335206171675823013 / 2048000000000) * u ^ 10 + (1521680182962859170111863142468832186683 / 4096000000000) * u ^ 12 + (118747152595029968621636581630302422193 / 204800000000) * u ^ 14 + (5809352639856603919241259629347549258527 / 8192000000000) * u ^ 16 + (525105456979685264199311581866305805579 / 819200000000) * u ^ 18 + (2954706612084799013110348326519330324867 / 8192000000000) * u ^ 20 := by
  norm_num (config := { maxSteps := 1000000 })
    [centeredCoeffFormula125, shiftedBaseCoeff125, evenCoeff125,
      Finset.sum_range_succ, Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, Nat.choose]
  ring

end RationalWindow125
end Zeta85
end RH
