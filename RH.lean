/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH.lean — root of the conditional layer of this repository.

`Zeta23` (the base library, in `Zeta23/`) is unconditional: it declares no axiom and its headline
theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.  `RH/` is the **conditional**
layer added on top of it: the 85 % result and its two lower rungs, each resting on the named axioms
of `RH/Zeta85/Hypotheses.lean`.  Nothing under `Zeta23/` imports anything under `RH/`.

See `AXIOMS.md` (what is assumed), `FINDINGS.md` (where the source documents were wrong or
incomplete), `VALIDATION.md` (build and comparator output) and `docs/REUSE_MAP.md` (what is reused
from `Zeta23`).
-/
import RH.Zeta85
