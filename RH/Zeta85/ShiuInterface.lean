/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/ShiuInterface.lean — the corrected Shiu-type progression-majorant interface.

**Definition only**: no axiom is declared here.  The axiom asserting this interface is
`RH.Zeta85.Hypotheses.shiu_majorant₂`, in `RH/Zeta85/Hypotheses.lean` — the single file of the
conditional layer that declares axioms.

The frozen interface `RH.Zeta85.ShiuMajorant` (`RH/Zeta85/Arith.lean`) is **refuted in this
repository**: `RH.Zeta85.not_shiuMajorant_quarter` (`RH/Zeta85/Discharge/ShiuNoGo.lean`) proves
`¬ ShiuMajorant (1/4)`.  The frozen statement fixes `T` — and with it the scale `(log T)^C` of its
right-hand side — *before* quantifying the interval scale `P`, so a `τ(3^m)`-spike isolated by a
power-of-two modulus beats any `(log T)^C` bound.  `ShiuMajorant₂` below corrects three defects of
that rendering:

* **D1 — the majorant scale.**  The right-hand side is `(log P)^C`, the logarithm of the interval
  scale itself; the auxiliary parameter `T` is gone entirely.  (Frozen: `(log T)^C` with `T`
  quantified before `P`.)
* **D2 — the modulus range.**  The uniformity range is `q ≤ P^(1−η)`, the range of Shiu's theorem;
  the mixed range `q ≤ P·T^(−η)` is gone with `T`.
* **D3 — class-uniform constants.**  The constants `C, K` and the threshold `P₁` depend only on the
  divisor-bound class `(Kc, k)`: the quantifier `∃ C K P₁` comes *after* `(Kc, k)` but *before* the
  coefficient family `c`.  (Frozen: constants chosen per coefficient family.)

**Which defect the refutation actually exploits, and which is a faithfulness fix.**  D1 and D2 are
the defects `not_shiuMajorant_quarter` turns into a contradiction: it fixes a single family
`c = σ₀` up front and then drives `P = q·T` far past `T`, so the `(log T)^C` right-hand side (D1)
cannot follow the growing left-hand side while the mixed range `q ≤ P·T^(−η)` (D2) still allows the
modulus.  Either correction alone defeats that construction; the no-go never varies `c` against
frozen constants, so it does **not** exploit the per-`c` freeze.  D3 is therefore not a repair of
the refutation but a separate faithfulness correction: Shiu's published theorem has implied
constants depending only on the majorant class, and a downstream argument that ranges over many
coefficient families needs that uniformity.  Note the direction honestly — quantifying the
constants before `c` makes `ShiuMajorant₂` **stronger** on this axis, not weaker, and so departs
from the "state the weaker thing" convention of `RH/Zeta85/Arith.lean`; it is adopted because it is
what Shiu's theorem says, not because it is safer.

The vocabulary (`DivisorBounded`, `progressionSum`) is that of `RH/Zeta85/Arith.lean`,
definitions only.
-/
import RH.Zeta85.Arith

noncomputable section

namespace RH
namespace Zeta85

/-- The corrected Shiu-type majorant at exponent `η`, repairing the refuted frozen interface
(defects D1–D3 in the module docstring): for every divisor-bound class `(Kc, k)` there are
class-uniform constants `C, K` and a threshold `P₁` such that for every scale `P ≥ P₁`, every
coefficient family `c` that is divisor-bounded in that class, and every reduced residue class
`r mod q` with `q ≤ P^(1−η)`,

  `Σ_{p ≍ P, p ≡ r (mod q)} |c_p| ≤ K·(P/φ(q))·(log P)^C`. -/
def ShiuMajorant₂ (η : ℝ) : Prop :=
  ∀ (Kc : ℝ) (k : ℕ), ∃ C K P₁ : ℝ, ∀ P ≥ P₁, ∀ c : ℕ → ℝ, DivisorBounded c Kc k →
    ∀ q r : ℕ, 0 < q → Nat.Coprime r q → (q : ℝ) ≤ P ^ (1 - η) →
      progressionSum c P q r ≤ K * (P / (Nat.totient q : ℝ)) * (Real.log P) ^ C

end Zeta85
end RH

end
