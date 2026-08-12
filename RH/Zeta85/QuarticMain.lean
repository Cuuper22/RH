/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.QuarticTransfer
import RH.Zeta85.Statement

/-!
# Conditional frozen quartic rungs

Each headline has exactly four explicit per-support premises.  The base
repository discharges the zeta Riemann--von Mangoldt and dyadic-to-cumulative
steps.  No signed-pair or Rudnick--Sarnak structure is accepted here as a
substitute for the trace, zero-side, construction, or moment premise.
-/

open Filter Topology

noncomputable section

namespace RH
namespace Zeta85

open Zeta23

private theorem tendsto_Ncount_zero_atTop_quartic :
    Tendsto (fun T => (Ncount 0 T : ℝ)) atTop atTop := by
  have h1 : Tendsto
      (fun T : ℝ => ((zetaZeros zetaSeam).N (T / 2) (2 * (T / 2)) : ℝ))
      atTop atTop :=
    (Assembly.tendsto_N_atTop (zetaZeros zetaSeam)
      (RvM.riemannVonMangoldt gammaFacts)).comp
        (tendsto_id.atTop_div_const two_pos)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop 0] with T hT
  have hsplit := Assembly.N_add (zetaZeros zetaSeam)
    (a := 0) (b := T / 2) (c := T) (by linarith) (by linarith)
  have hTtwo : 2 * (T / 2) = T := by ring
  rw [hTtwo]
  simp only [zetaZeros_N] at hsplit ⊢
  exact_mod_cast hsplit ▸ Nat.le_add_left _ _

private theorem quarticCumulative {c : ℝ}
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (c - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (c - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  refine Assembly.dyadic
    (f := fun a b => (N0simple a b : ℝ))
    (g := fun a b => (Ncount a b : ℝ)) (c := c)
    ?_ ?_ (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    tendsto_Ncount_zero_atTop_quartic h
  · intro a b d hab hbd
    exact_mod_cast Assembly.N0s_add (zetaZeros zetaSeam) hab hbd
  · intro a b d hab hbd
    have hN := Assembly.N_add (zetaZeros zetaSeam) hab hbd
    simp only [zetaZeros_N] at hN
    exact_mod_cast hN

/-! ## Support `14999/10000` -/

/-- Frozen R-8657, conditional on exactly the four support-`14999/10000`
analytic structures. -/
theorem rung8657
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hr1a : BlockDensityLimit F) (hmom : BlockMomentConvergence F) :
    Rung8657_statement := by
  simpa only [Rung8657_statement, cRung8657] using
    QuarticTransfer.zeta_eps_transfer_8657 hfull hzero hr1a hmom

/-- Cumulative frozen R-8657 under the same four premises. -/
theorem rung8657_cumulative
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hr1a : BlockDensityLimit F) (hmom : BlockMomentConvergence F) :
    Rung8657_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung8657 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa only [Rung8657_statement] using rung8657 hfull hzero hr1a hmom
  simpa only [Rung8657_cumulative_statement] using quarticCumulative hdyadic

/-- Frozen R-8686, conditional on exactly the four support-`14999/10000`
analytic structures. -/
theorem rung8686
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hr1a : BlockDensityLimit F) (hmom : BlockMomentConvergence F) :
    Rung8686_statement := by
  simpa only [Rung8686_statement, cRung8686] using
    QuarticTransfer.zeta_eps_transfer_8686 hfull hzero hr1a hmom

/-- Cumulative frozen R-8686 under the same four premises. -/
theorem rung8686_cumulative
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hr1a : BlockDensityLimit F) (hmom : BlockMomentConvergence F) :
    Rung8686_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung8686 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa only [Rung8686_statement] using rung8686 hfull hzero hr1a hmom
  simpa only [Rung8686_cumulative_statement] using quarticCumulative hdyadic

/-! ## Support `19999/10000` -/

/-- Frozen R-9383, conditional on exactly the four support-`19999/10000`
analytic structures. -/
theorem rung9383
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hr1a : BlockDensityLimit F) (hmom : BlockMomentConvergence F) :
    Rung9383_statement := by
  simpa only [Rung9383_statement, cRung9383] using
    QuarticTransfer.zeta_eps_transfer_9383 hfull hzero hr1a hmom

/-- Cumulative frozen R-9383 under the same four premises. -/
theorem rung9383_cumulative
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hr1a : BlockDensityLimit F) (hmom : BlockMomentConvergence F) :
    Rung9383_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung9383 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa only [Rung9383_statement] using rung9383 hfull hzero hr1a hmom
  simpa only [Rung9383_cumulative_statement] using quarticCumulative hdyadic

/-- Frozen R-9506, conditional on exactly the four support-`19999/10000`
analytic structures. -/
theorem rung9506
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hr1a : BlockDensityLimit F) (hmom : BlockMomentConvergence F) :
    Rung9506_statement := by
  simpa only [Rung9506_statement, cRung9506] using
    QuarticTransfer.zeta_eps_transfer_9506 hfull hzero hr1a hmom

/-- Cumulative frozen R-9506 under the same four premises. -/
theorem rung9506_cumulative
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hr1a : BlockDensityLimit F) (hmom : BlockMomentConvergence F) :
    Rung9506_cumulative_statement := by
  have hdyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cRung9506 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa only [Rung9506_statement] using rung9506 hfull hzero hr1a hmom
  simpa only [Rung9506_cumulative_statement] using quarticCumulative hdyadic

end Zeta85
end RH

end
