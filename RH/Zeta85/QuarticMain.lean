/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.QuarticTransfer
import RH.Zeta85.Discharge.IsometricBlock
import RH.Zeta85.Discharge.IsometricKernel
import RH.Zeta85.Discharge.BalancedMixer
import RH.Zeta85.Discharge.VirtualChannelMixer
import RH.Zeta85.Discharge.RepeatedChannelCompression
import RH.Zeta85.Discharge.AlignedIsometricLayout
import RH.Zeta85.Discharge.AlignedChannelScales
import RH.Zeta85.Statement

/-!
# Conditional frozen quartic rungs

Each headline has exactly three explicit per-support premises.  The base
repository discharges the zeta Riemann--von Mangoldt and dyadic-to-cumulative
steps.  No signed-pair or Rudnick--Sarnak structure is accepted here as a
substitute for the trace, zero-side, or one-sided factorized zero-pair-kernel bound.
-/

open Filter Topology

noncomputable section

namespace RH
namespace Zeta85

open Zeta23

private theorem quarticCumulative {c : ℝ}
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (c - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (c - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (fun _ _ _ => N0simple_add' zetaSeam) h

/-! ## Support `14999/10000` -/

/-- Frozen R-8657, conditional on exactly the three support-`14999/10000`
analytic structures. -/
theorem rung8657
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : QuarticTransfer.FactoredZeroKernelQuarticLowerBound TrimmedMoment.Terminal8686.dual F) :
    Rung8657_statement := by
  simpa only [Rung8657_statement, cRung8657] using
    QuarticTransfer.zeta_eps_transfer_8657 hfull hzero hweighted

/-- Cumulative frozen R-8657 under the same three premises. -/
theorem rung8657_cumulative
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : QuarticTransfer.FactoredZeroKernelQuarticLowerBound TrimmedMoment.Terminal8686.dual F) :
    Rung8657_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung8657 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa only [Rung8657_statement] using rung8657 hfull hzero hweighted
  simpa only [Rung8657_cumulative_statement] using quarticCumulative hdyadic

/-- Frozen R-8686, conditional on exactly the three support-`14999/10000`
analytic structures. -/
theorem rung8686
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : QuarticTransfer.FactoredZeroKernelQuarticLowerBound TrimmedMoment.Terminal8686.dual F) :
    Rung8686_statement := by
  simpa only [Rung8686_statement, cRung8686] using
    QuarticTransfer.zeta_eps_transfer_8686 hfull hzero hweighted

/-- Cumulative frozen R-8686 under the same three premises. -/
theorem rung8686_cumulative
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : QuarticTransfer.FactoredZeroKernelQuarticLowerBound TrimmedMoment.Terminal8686.dual F) :
    Rung8686_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung8686 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa only [Rung8686_statement] using rung8686 hfull hzero hweighted
  simpa only [Rung8686_cumulative_statement] using quarticCumulative hdyadic

/-! ## Support `19999/10000` -/

/-- Frozen R-9383, conditional on exactly the three support-`19999/10000`
analytic structures. -/
theorem rung9383
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : QuarticTransfer.FactoredZeroKernelQuarticLowerBound TrimmedMoment.Terminal9506.dual F) :
    Rung9383_statement := by
  simpa only [Rung9383_statement, cRung9383] using
    QuarticTransfer.zeta_eps_transfer_9383 hfull hzero hweighted

/-- Cumulative frozen R-9383 under the same three premises. -/
theorem rung9383_cumulative
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : QuarticTransfer.FactoredZeroKernelQuarticLowerBound TrimmedMoment.Terminal9506.dual F) :
    Rung9383_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung9383 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa only [Rung9383_statement] using rung9383 hfull hzero hweighted
  simpa only [Rung9383_cumulative_statement] using quarticCumulative hdyadic

/-- Frozen R-9506, conditional on exactly the three support-`19999/10000`
analytic structures. -/
theorem rung9506
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : QuarticTransfer.FactoredZeroKernelQuarticLowerBound TrimmedMoment.Terminal9506.dual F) :
    Rung9506_statement := by
  simpa only [Rung9506_statement, cRung9506] using
    QuarticTransfer.zeta_eps_transfer_9506 hfull hzero hweighted

/-- Cumulative frozen R-9506 under the same three premises. -/
theorem rung9506_cumulative
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : QuarticTransfer.FactoredZeroKernelQuarticLowerBound TrimmedMoment.Terminal9506.dual F) :
    Rung9506_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung9506 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa only [Rung9506_statement] using rung9506 hfull hzero hweighted
  simpa only [Rung9506_cumulative_statement] using quarticCumulative hdyadic


/-! ## Mixed-channel isometric route -/

/-- Frozen R-8657 from an exact mixed-channel compression and its one-sided
terminal statistic.  No coordinate principal-block allocation is used. -/
theorem rung8657_isometric
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : IsometricBlock.Data F)
    (hweighted :
      IsometricBlock.WeightedQuarticLowerBound
        TrimmedMoment.Terminal8686.dual C) :
    Rung8657_statement := by
  simpa only [Rung8657_statement, cRung8657] using
    IsometricBlock.zeta_eps_transfer_8657
      hfull hzero C hweighted

theorem rung8657_cumulative_isometric
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : IsometricBlock.Data F)
    (hweighted :
      IsometricBlock.WeightedQuarticLowerBound
        TrimmedMoment.Terminal8686.dual C) :
    Rung8657_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung8657 - ε) * (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
    simpa only [Rung8657_statement] using
      rung8657_isometric hfull hzero C hweighted
  simpa only [Rung8657_cumulative_statement] using
    quarticCumulative hdyadic

/-- Frozen R-8686 from the mixed-channel compression. -/
theorem rung8686_isometric
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : IsometricBlock.Data F)
    (hweighted :
      IsometricBlock.WeightedQuarticLowerBound
        TrimmedMoment.Terminal8686.dual C) :
    Rung8686_statement := by
  simpa only [Rung8686_statement, cRung8686] using
    IsometricBlock.zeta_eps_transfer_8686
      hfull hzero C hweighted

theorem rung8686_cumulative_isometric
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : IsometricBlock.Data F)
    (hweighted :
      IsometricBlock.WeightedQuarticLowerBound
        TrimmedMoment.Terminal8686.dual C) :
    Rung8686_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung8686 - ε) * (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
    simpa only [Rung8686_statement] using
      rung8686_isometric hfull hzero C hweighted
  simpa only [Rung8686_cumulative_statement] using
    quarticCumulative hdyadic

/-- Frozen R-9383 from the mixed-channel compression. -/
theorem rung9383_isometric
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : IsometricBlock.Data F)
    (hweighted :
      IsometricBlock.WeightedQuarticLowerBound
        TrimmedMoment.Terminal9506.dual C) :
    Rung9383_statement := by
  simpa only [Rung9383_statement, cRung9383] using
    IsometricBlock.zeta_eps_transfer_9383
      hfull hzero C hweighted

theorem rung9383_cumulative_isometric
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : IsometricBlock.Data F)
    (hweighted :
      IsometricBlock.WeightedQuarticLowerBound
        TrimmedMoment.Terminal9506.dual C) :
    Rung9383_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung9383 - ε) * (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
    simpa only [Rung9383_statement] using
      rung9383_isometric hfull hzero C hweighted
  simpa only [Rung9383_cumulative_statement] using
    quarticCumulative hdyadic

/-- Frozen R-9506 from the mixed-channel compression. -/
theorem rung9506_isometric
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : IsometricBlock.Data F)
    (hweighted :
      IsometricBlock.WeightedQuarticLowerBound
        TrimmedMoment.Terminal9506.dual C) :
    Rung9506_statement := by
  simpa only [Rung9506_statement, cRung9506] using
    IsometricBlock.zeta_eps_transfer_9506
      hfull hzero C hweighted

theorem rung9506_cumulative_isometric
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : IsometricBlock.Data F)
    (hweighted :
      IsometricBlock.WeightedQuarticLowerBound
        TrimmedMoment.Terminal9506.dual C) :
    Rung9506_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung9506 - ε) * (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
    simpa only [Rung9506_statement] using
      rung9506_isometric hfull hzero C hweighted
  simpa only [Rung9506_cumulative_statement] using
    quarticCumulative hdyadic

/-! ## Routed virtual-channel route -/

/-- Frozen R-8686 from the routed virtual-atom quartic lower bound. -/
theorem rung8686_aligned_virtual
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : AlignedIsometricLayout.Layout F ι)
    (A : AlignedIsometricLayout.AtomFactorization L)
    (hvirtual :
      AlignedIsometricLayout.SelectedVirtualQuarticLowerBound
        TrimmedMoment.Terminal8686.dual A) :
    Rung8686_statement :=
  rung8686_isometric hfull hzero
    (AlignedIsometricLayout.toIsometricData L)
    hvirtual.toIsometric

/-- Cumulative R-8686 from the same routed virtual construction. -/
theorem rung8686_cumulative_aligned_virtual
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : AlignedIsometricLayout.Layout F ι)
    (A : AlignedIsometricLayout.AtomFactorization L)
    (hvirtual :
      AlignedIsometricLayout.SelectedVirtualQuarticLowerBound
        TrimmedMoment.Terminal8686.dual A) :
    Rung8686_cumulative_statement :=
  rung8686_cumulative_isometric hfull hzero
    (AlignedIsometricLayout.toIsometricData L)
    hvirtual.toIsometric

/-- Frozen R-9506 from the routed virtual-atom quartic lower bound. -/
theorem rung9506_aligned_virtual
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : AlignedIsometricLayout.Layout F ι)
    (A : AlignedIsometricLayout.AtomFactorization L)
    (hvirtual :
      AlignedIsometricLayout.SelectedVirtualQuarticLowerBound
        TrimmedMoment.Terminal9506.dual A) :
    Rung9506_statement :=
  rung9506_isometric hfull hzero
    (AlignedIsometricLayout.toIsometricData L)
    hvirtual.toIsometric

/-- Cumulative R-9506 from the same routed virtual construction. -/
theorem rung9506_cumulative_aligned_virtual
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : AlignedIsometricLayout.Layout F ι)
    (A : AlignedIsometricLayout.AtomFactorization L)
    (hvirtual :
      AlignedIsometricLayout.SelectedVirtualQuarticLowerBound
        TrimmedMoment.Terminal9506.dual A) :
    Rung9506_cumulative_statement :=
  rung9506_cumulative_isometric hfull hzero
    (AlignedIsometricLayout.toIsometricData L)
    hvirtual.toIsometric

end Zeta85
end RH

end
