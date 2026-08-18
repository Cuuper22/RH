/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Shiu/MajorantQuarter.lean — the corrected majorant, proved on the upper half of its
range.

`RH/Zeta85/ShiuInterface.lean` defines `ShiuMajorant₂ η`, the corrected progression-majorant
interface, and `RH/Zeta85/Hypotheses.lean` ASSUMES it for every `η ∈ (0, 1/2)` (the axiom
`shiu_majorant₂`).  This file proves it outright for every `η ≥ 1/4`:

    theorem shiuMajorant₂_of_quarter_le : 1/4 ≤ η → ShiuMajorant₂ η

The proof is one application of `progRoute2_shiu_shape`, whose conclusion is the body of
`ShiuMajorant₂` verbatim.  Everything behind it is unconditional: Lay's explicit Landreau
inequality raised to the `k`-th power, the Chinese-remainder count of a residue class inside a
multiples class, the `τ_K` summatory ladder, and the quartic-root cutoff `q^4 ≤ N^3` that absorbs
the error terms.

**Range.**  `ShiuMajorant₂` is antitone in `η`: a smaller `η` admits a WIDER band of moduli
(`q ≤ P^{1-η}`) and is therefore a stronger statement.  The route behind this file reaches
`q ≤ P^{3/4}`, i.e. exactly `η ≥ 1/4`.  The interval `η ∈ (0, 1/4)` — moduli beyond `P^{3/4}` —
is NOT covered, so the axiom is not discharged by this file.  What is covered is the half of the
range that the 85 % run actually exercises (`η' = 43/93 ≈ 0.462`, `docs/research/shiu_routes_20260818.md` §2).

**What this does not buy.**  `RH/Zeta85/Discharge/LogBudget.lean` proves that the rung-3 route
needs an effective log exponent `C < 2`, while the constant delivered here is `C = 2^{7k}`.  A
true majorant is necessary but not sufficient for the rung; see `verdict_all` there and
`ActualScaleBBLR.progression_majorant_not_traceGrade` for the second, independent obstruction.
-/
import RH.Zeta85.ShiuInterface
import RH.Zeta85.Shiu.ProgressionRoute2

noncomputable section

namespace RH
namespace Zeta85
namespace Shiu

/-- **The corrected Shiu majorant holds for every `η ≥ 1/4`.**

This is the statement the axiom `RH.Zeta85.Hypotheses.shiu_majorant₂` assumes, restricted to the
upper half of its range, and here it is a theorem: unconditional, with explicit constants
(`C = 2^{7k}`, `K = Kc · (6 · 8^k) · 2^{2^{7k}}`, `P₁ = e^3`) supplied by
`progRoute2_shiu_shape`.

The axiom remains for `η ∈ (0, 1/4)`, where the modulus band `q ≤ P^{1-η}` runs past `P^{3/4}`
and this route does not reach. -/
theorem shiuMajorant₂_of_quarter_le {η : ℝ} (hη : 1 / 4 ≤ η) : ShiuMajorant₂ η :=
  fun Kc k => progRoute2_shiu_shape Kc k hη

/-- The instance at the endpoint `η = 1/4`, the widest modulus band this route reaches
(`q ≤ P^{3/4}`). -/
theorem shiuMajorant₂_quarter : ShiuMajorant₂ (1 / 4 : ℝ) :=
  shiuMajorant₂_of_quarter_le le_rfl

/-- The instance at the exponent the 85 % run exercises, `η' = 43/93 ≈ 0.462`. -/
theorem shiuMajorant₂_run_exponent : ShiuMajorant₂ (43 / 93 : ℝ) :=
  shiuMajorant₂_of_quarter_le (by norm_num)

end Shiu
end Zeta85
end RH

end

/-!
Axiom audit: the corrected majorant is proved on `η ≥ 1/4` from the standard three axioms only —
in particular it does NOT depend on `RH.Zeta85.Hypotheses.shiu_majorant₂`.
-/
#print axioms RH.Zeta85.Shiu.shiuMajorant₂_of_quarter_le
#print axioms RH.Zeta85.Shiu.shiuMajorant₂_quarter
#print axioms RH.Zeta85.Shiu.shiuMajorant₂_run_exponent
