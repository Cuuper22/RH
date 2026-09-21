/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.LiteralEnergyTailEquivalence
import RH.Zeta85.Discharge.RSBlockMomentBridge

/-!
# Collective literal energy-tail route

The channelwise support route is impossible for the frozen families, but the
nonzero aliases cancel after all physical channels are summed.  This module
identifies that collective literal energy-tail coordinate with the weighted
centered-quartic coordinate and connects the actual uncentered
Rudnick--Sarnak block limits directly to frozen R-9506.
-/

open Filter

noncomputable section

namespace RH
namespace Zeta85
namespace AggregateSynthesisBridge

open Zeta23
open AggregateCoordinateFrame

/-- Collective alias cancellation identifies the literal energy-tail boundary
with the weighted centered-quartic boundary after all channels are summed. -/
theorem literalEnergyTailQuarticLowerBound_of_weighted_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : CollectiveWindowRegularity F)
    (h : QuarticTransfer.WeightedQuarticLowerBound q F) :
    LiteralEnergyTailQuarticLowerBound (F := F) q := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx, h.block_dimension_pos]
      with T hT hm
  rw [QuarticTransfer.weightedQuarticScore_eq_traceNumerator hm,
    quarticTraceNumerator_eq_literalEnergyTail_collective hreg T] at hT
  exact hT

/-- Reverse collective identification. -/
theorem LiteralEnergyTailQuarticLowerBound.toWeightedCollective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : CollectiveWindowRegularity F)
    (h : LiteralEnergyTailQuarticLowerBound (F := F) q) :
    QuarticTransfer.WeightedQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx, h.block_dimension_pos]
      with T hT hm
  rw [QuarticTransfer.weightedQuarticScore_eq_traceNumerator hm,
    quarticTraceNumerator_eq_literalEnergyTail_collective hreg T]
  exact hT

/-- Exact collective equivalence of the two terminal analytic coordinates. -/
theorem literalEnergyTailQuarticLowerBound_iff_weighted_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : CollectiveWindowRegularity F) :
    LiteralEnergyTailQuarticLowerBound (F := F) q ↔
      QuarticTransfer.WeightedQuarticLowerBound q F :=
  ⟨fun h => LiteralEnergyTailQuarticLowerBound.toWeightedCollective hreg h,
    fun h => literalEnergyTailQuarticLowerBound_of_weighted_collective hreg h⟩

/-- Density and the four centered moments construct the collective
energy-minus-tail boundary directly. -/
theorem literalEnergyTailQuarticLowerBound_of_moments_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : CollectiveWindowRegularity F)
    (hdim : BlockDimensionLimit F)
    (hmom : BlockMomentConvergence F) :
    LiteralEnergyTailQuarticLowerBound (F := F) q :=
  literalEnergyTailQuarticLowerBound_of_weighted_collective hreg
    (QuarticTransfer.WeightedQuarticLimit.toLowerBound
      (QuarticTransfer.weightedQuarticLimit_of_separate hdim
        (QuarticTransfer.quarticScoreConvergence_of_moments hmom q)))

/-- The actual uncentered Rudnick--Sarnak limits feed the collective literal
energy-tail coordinate directly.  No principal-channel allocation or
channelwise half-period support premise is reintroduced. -/
theorem literalEnergyTailQuarticLowerBound_of_uncenteredRS_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : CollectiveWindowRegularity F)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hdim : BlockDimensionLimit F)
    (hraw : RSBlockMomentBridge.UncenteredRSBlockLimits F) :
    LiteralEnergyTailQuarticLowerBound (F := F) q :=
  literalEnergyTailQuarticLowerBound_of_moments_collective hreg hdim
    ⟨RSBlockMomentBridge.centered_moment_limits_of_fillBounds hp hp1 hraw⟩

end AggregateSynthesisBridge

/-- Frozen R-9506 through collective cancellation from density and the four
centered literal-block moments. -/
theorem rung9506_collective_of_moments
    {F : Family19999 Zeta23.zetaZeroConfig}
    (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (hreg : AggregateSynthesisBridge.CollectiveWindowRegularity F)
    (hdim : BlockDimensionLimit F)
    (hmom : BlockMomentConvergence F) :
    Rung9506_statement :=
  rung9506_collective_energyTail hfull hzero hreg
    (AggregateSynthesisBridge.literalEnergyTailQuarticLowerBound_of_moments_collective
      hreg hdim hmom)

/-- Cumulative frozen R-9506 through the same collective moment route. -/
theorem rung9506_cumulative_collective_of_moments
    {F : Family19999 Zeta23.zetaZeroConfig}
    (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (hreg : AggregateSynthesisBridge.CollectiveWindowRegularity F)
    (hdim : BlockDimensionLimit F)
    (hmom : BlockMomentConvergence F) :
    Rung9506_cumulative_statement :=
  rung9506_cumulative_collective_energyTail hfull hzero hreg
    (AggregateSynthesisBridge.literalEnergyTailQuarticLowerBound_of_moments_collective
      hreg hdim hmom)

/-- Frozen R-9506 from the actual uncentered Rudnick--Sarnak block moments,
block density, and collective cancellation. -/
theorem rung9506_collective_of_uncenteredRS
    {F : Family19999 Zeta23.zetaZeroConfig}
    (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (hreg : AggregateSynthesisBridge.CollectiveWindowRegularity F)
    (hdim : BlockDimensionLimit F)
    (hraw : RSBlockMomentBridge.UncenteredRSBlockLimits F) :
    Rung9506_statement :=
  rung9506_collective_energyTail hfull hzero hreg
    (AggregateSynthesisBridge.literalEnergyTailQuarticLowerBound_of_uncenteredRS_collective
      hreg (by norm_num) (by norm_num) hdim hraw)

/-- Cumulative frozen R-9506 through the same uncentered RS route. -/
theorem rung9506_cumulative_collective_of_uncenteredRS
    {F : Family19999 Zeta23.zetaZeroConfig}
    (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (hreg : AggregateSynthesisBridge.CollectiveWindowRegularity F)
    (hdim : BlockDimensionLimit F)
    (hraw : RSBlockMomentBridge.UncenteredRSBlockLimits F) :
    Rung9506_cumulative_statement :=
  rung9506_cumulative_collective_energyTail hfull hzero hreg
    (AggregateSynthesisBridge.literalEnergyTailQuarticLowerBound_of_uncenteredRS_collective
      hreg (by norm_num) (by norm_num) hdim hraw)

end Zeta85
end RH

end
