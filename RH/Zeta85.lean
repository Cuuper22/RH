/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85.lean — the root module of the conditional 85 % layer.

Import graph:

  Window       — Phase A1: the three exact window moments at support 143/100
  Certificate  — Phase A2/A3: c_pc, the count lemma, `SaturatedWindowCost`, `windowCost_143`
  Transfer     — the two-trace certificate interface and its (proved) conversion to the ε-form
  Statement    — Phase B1: the three rungs and the 85 % corollary, as Props
  Arith        — the arithmetic vocabulary of the hypotheses layer (definitions only)
  Discharge/*  — what could be proved of Phase C: the signed-shift lemma (C1), the exponent
                 bookkeeping, the logarithmic-power audit (C7)
  Hypotheses   — the six axioms, with provenance (THE ONLY FILE IN `RH/` DECLARING AN AXIOM)
  Main         — Phase D: the three rungs, assembled

See `AXIOMS.md`, `FINDINGS.md`, `VALIDATION.md` and `docs/REUSE_MAP.md`.
-/
import RH.Zeta85.Window
import RH.Zeta85.Certificate
import RH.Zeta85.Transfer
import RH.Zeta85.Statement
import RH.Zeta85.Arith
import RH.Zeta85.Discharge.SignedShift
import RH.Zeta85.Discharge.Exponents
import RH.Zeta85.Discharge.LogBudget
import RH.Zeta85.Hypotheses
import RH.Zeta85.Main
