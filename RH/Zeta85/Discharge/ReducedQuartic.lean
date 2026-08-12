/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.BlockDensity
import RH.Zeta85.QuarticMain

/-!
# Three-premise frozen quartic transfer

Canonical floor reblocking derives its density from the ambient trace and
zero-side packages.  The terminal rungs therefore require only those two
ambient packages and the four centered moments of the canonical block.
-/

noncomputable section

namespace RH.Zeta85.ReducedQuartic

open Zeta23
open BlockDensity

/-! ## Support `1.9999` -/

theorem zeta_eps_transfer_9506
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((95063832187565 / 100000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  exact QuarticTransfer.zeta_eps_transfer_9506
    (fullTraceLimits_reblock hfull) (stableZeroSide_reblock hzero)
    (reblock_densityLimit_9506 (RvM.riemannVonMangoldt gammaFacts) hfull hzero)
    hmom

theorem rung9506
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    Rung9506_statement := by
  simpa only [Rung9506_statement, cRung9506] using
    zeta_eps_transfer_9506 hfull hzero hmom

theorem rung9506_cumulative
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    Rung9506_cumulative_statement :=
  RH.Zeta85.rung9506_cumulative
    (fullTraceLimits_reblock hfull) (stableZeroSide_reblock hzero)
    (reblock_densityLimit_9506 (RvM.riemannVonMangoldt gammaFacts) hfull hzero)
    hmom

theorem rung9383
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    Rung9383_statement :=
  RH.Zeta85.rung9383
    (fullTraceLimits_reblock hfull) (stableZeroSide_reblock hzero)
    (reblock_densityLimit_9506 (RvM.riemannVonMangoldt gammaFacts) hfull hzero)
    hmom

theorem rung9383_cumulative
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    Rung9383_cumulative_statement :=
  RH.Zeta85.rung9383_cumulative
    (fullTraceLimits_reblock hfull) (stableZeroSide_reblock hzero)
    (reblock_densityLimit_9506 (RvM.riemannVonMangoldt gammaFacts) hfull hzero)
    hmom

/-! ## Support `1.4999` -/

theorem zeta_eps_transfer_8686
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((86855250 / 100000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  exact QuarticTransfer.zeta_eps_transfer_8686
    (fullTraceLimits_reblock hfull) (stableZeroSide_reblock hzero)
    (reblock_densityLimit_8686 (RvM.riemannVonMangoldt gammaFacts) hfull hzero)
    hmom

theorem rung8686
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    Rung8686_statement := by
  simpa only [Rung8686_statement, cRung8686] using
    zeta_eps_transfer_8686 hfull hzero hmom

theorem rung8686_cumulative
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    Rung8686_cumulative_statement :=
  RH.Zeta85.rung8686_cumulative
    (fullTraceLimits_reblock hfull) (stableZeroSide_reblock hzero)
    (reblock_densityLimit_8686 (RvM.riemannVonMangoldt gammaFacts) hfull hzero)
    hmom

theorem rung8657
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    Rung8657_statement :=
  RH.Zeta85.rung8657
    (fullTraceLimits_reblock hfull) (stableZeroSide_reblock hzero)
    (reblock_densityLimit_8686 (RvM.riemannVonMangoldt gammaFacts) hfull hzero)
    hmom

theorem rung8657_cumulative
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hmom : BlockMomentConvergence (reblock F)) :
    Rung8657_cumulative_statement :=
  RH.Zeta85.rung8657_cumulative
    (fullTraceLimits_reblock hfull) (stableZeroSide_reblock hzero)
    (reblock_densityLimit_8686 (RvM.riemannVonMangoldt gammaFacts) hfull hzero)
    hmom

end RH.Zeta85.ReducedQuartic

end
