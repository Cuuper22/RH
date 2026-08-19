/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.QuarticMain
import Zeta23.Final

/-!
# Literal energy-tail equivalence

For a physically regular frozen family, the aggregate energy-minus-tail
quartic lower bound is not an additional analytic hypothesis.  Exact finite
identities identify it with the existing weighted centered-quartic boundary.
This module proves both directions, supplies the construction from separate
block-density and moment limits, and plugs that construction directly into the
highest frozen rung.
-/

open Filter

noncomputable section

namespace RH
namespace Zeta85
namespace AggregateCoordinateFrame

open Zeta23

/-- Once the complete physical frequency lattices have been evaluated, the
normalized literal energy-tail numerator is exactly the weighted centered
quartic score.  Hence the existing weighted lower bound supplies the terminal
aggregate coordinate without any additional analytic premise. -/
theorem literalEnergyTailQuarticLowerBound_of_weighted
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : PhysicalWindowRegularity F)
    (h : QuarticTransfer.WeightedQuarticLowerBound q F) :
    LiteralEnergyTailQuarticLowerBound (F := F) q := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx, h.block_dimension_pos]
      with T hT hm
  rw [QuarticTransfer.weightedQuarticScore_eq_traceNumerator hm,
    quarticTraceNumerator_eq_literalEnergyTail hreg T] at hT
  exact hT

/-- Conversely, the literal energy-tail lower bound is the weighted centered
quartic lower bound after the same exact finite identities. -/
theorem LiteralEnergyTailQuarticLowerBound.toWeighted
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : PhysicalWindowRegularity F)
    (h : LiteralEnergyTailQuarticLowerBound (F := F) q) :
    QuarticTransfer.WeightedQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx, h.block_dimension_pos]
      with T hT hm
  rw [QuarticTransfer.weightedQuarticScore_eq_traceNumerator hm,
    quarticTraceNumerator_eq_literalEnergyTail hreg T]
  exact hT

/-- Exact equivalence of the weighted-score and literal energy-tail analytic
boundaries under physical-window regularity. -/
theorem literalEnergyTailQuarticLowerBound_iff_weighted
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : PhysicalWindowRegularity F) :
    LiteralEnergyTailQuarticLowerBound (F := F) q ↔
      QuarticTransfer.WeightedQuarticLowerBound q F :=
  ⟨fun h => LiteralEnergyTailQuarticLowerBound.toWeighted hreg h,
    fun h => literalEnergyTailQuarticLowerBound_of_weighted hreg h⟩

/-- The earlier separate block-density and four-moment construction therefore
lands directly in the sole literal energy-tail coordinate. -/
theorem literalEnergyTailQuarticLowerBound_of_moments
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : PhysicalWindowRegularity F)
    (hdim : BlockDimensionLimit F)
    (hmom : BlockMomentConvergence F) :
    LiteralEnergyTailQuarticLowerBound (F := F) q :=
  literalEnergyTailQuarticLowerBound_of_weighted hreg
    (QuarticTransfer.WeightedQuarticLimit.toLowerBound
      (QuarticTransfer.weightedQuarticLimit_of_separate hdim
        (QuarticTransfer.quarticScoreConvergence_of_moments hmom q)))

end AggregateCoordinateFrame

/-- The highest frozen dyadic rung now follows directly from physical-window
regularity, block density, and the four literal centered-moment limits.  The
impossible fixed principal-channel allocation is absent. -/
theorem rung9506_literal_of_moments
    {F : Family19999 Zeta23.zetaZeroConfig}
    (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (hreg : AggregateCoordinateFrame.PhysicalWindowRegularity F)
    (hdim : BlockDimensionLimit F)
    (hmom : BlockMomentConvergence F) :
    Rung9506_statement :=
  rung9506_literal_energyTail hfull hzero hreg
    (AggregateCoordinateFrame.literalEnergyTailQuarticLowerBound_of_moments
      hreg hdim hmom)

/-- Cumulative frozen R-9506 through the same allocation-free moment route. -/
theorem rung9506_cumulative_literal_of_moments
    {F : Family19999 Zeta23.zetaZeroConfig}
    (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (hreg : AggregateCoordinateFrame.PhysicalWindowRegularity F)
    (hdim : BlockDimensionLimit F)
    (hmom : BlockMomentConvergence F) :
    Rung9506_cumulative_statement :=
  rung9506_cumulative_literal_energyTail hfull hzero hreg
    (AggregateCoordinateFrame.literalEnergyTailQuarticLowerBound_of_moments
      hreg hdim hmom)

end Zeta85
end RH

end
