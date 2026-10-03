/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Hypotheses
import RH.Zeta85.Discharge.SignedPairNoGo

/-!
# The legacy signed-pair axioms are inconsistent

`RH.Zeta85.not_signedPairTraceGrade` (`RH/Zeta85/Discharge/SignedPairNoGo.lean`)
proves `¬ SignedPairTraceGrade σ` for every `σ > 1`, using only Mathlib and the
three standard Lean axioms.

The two theorems below record what that means for the frozen axiom layer.
Their `#print axioms` output deliberately contains the named axioms they use:
they are proofs of `False` *from those axioms*, not unconditional results.

* Axiom 2 (`signedPair_traceGrade_lt_5_4`) is inconsistent on its own, because
  its only premise `BBLRErrorBound` is proved in
  `RH/Zeta85/Discharge/BBLRErrorBound.lean`.
* Axiom 3 (`signedPair_traceGrade_lt_3_2`) is inconsistent together with
  Axiom 1 (`shiu_majorant₂`); its other premise `BBLRPoissonBlocks` is proved.

Every conditional headline that consumes either axiom is therefore a
`False`-elimination and carries no evidence about zeros of zeta.
-/

namespace RH
namespace Zeta85
namespace SignedPairInconsistency

/-- Axiom 2 together with the proved BBLR error interface yields `False`. -/
theorem axiom_lt_5_4_inconsistent : False :=
  not_signedPairTraceGrade (σ := 9 / 8) (by norm_num)
    (Hypotheses.signedPair_traceGrade_lt_5_4 bblrErrorBound_proved (9 / 8)
      (by norm_num) (by norm_num))

/-- Axiom 3, with Axiom 1 and the proved Poisson-block interface, yields `False`. -/
theorem axiom_lt_3_2_inconsistent : False :=
  not_signedPairTraceGrade (σ := 5 / 4) (by norm_num)
    (Hypotheses.signedPair_traceGrade_lt_3_2 bblrPoissonBlocks_proved
      Hypotheses.shiu_majorant₂ (5 / 4) (by norm_num) (by norm_num))

end SignedPairInconsistency
end Zeta85
end RH
