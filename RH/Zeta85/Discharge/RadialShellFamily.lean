/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.AggregateSynthesisBridge
import RH.Zeta85.Discharge.RadialShellAlias

/-!
# Radial-shell physical-family bridge

This combines the shell nonaliasing theorem with the exact literal coordinate
frame.  It packages the shell data needed at each height and derives the
collective window regularity consumed by the frozen quartic route.
-/

open Filter Matrix Finset Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace RadialShellFamily

open Zeta23
open AggregateCoordinateFrame

/-- A physical family whose channels are smooth even radial shells in one
common modulation period. -/
structure Data
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  commonPeriod : ℝ → ℝ
  supportRadius :
    ∀ T : ℝ, Fin (F.channelCount T) → ℝ
  shell :
    ∀ T : ℝ, Fin (F.channelCount T) → ℕ
  innerRadius :
    ∀ T : ℝ, Fin (F.channelCount T) → ℝ
  outerRadius :
    ∀ T : ℝ, Fin (F.channelCount T) → ℝ
  period_eq :
    ∀ T j, F.period T j = commonPeriod T
  period_pos :
    ∀ T, 0 < commonPeriod T
  supportRadius_nonneg :
    ∀ T j, 0 ≤ supportRadius T j
  smooth :
    ∀ T j, ContDiff ℝ 2 (fun u => (F.window T j u : ℂ))
  support :
    ∀ T j u, supportRadius T j < |u| → F.window T j u = 0
  even :
    ∀ T j u, F.window T j (-u) = F.window T j u
  shell_support :
    ∀ T j u, F.window T j u ≠ 0 →
      innerRadius T j < |u| ∧ |u| < outerRadius T j
  shell_inner :
    ∀ T j,
      (shell T j : ℝ) * commonPeriod T / 2 <
        innerRadius T j
  shell_outer :
    ∀ T j,
      outerRadius T j <
        (((shell T j) + 1 : ℕ) : ℝ) *
          commonPeriod T / 2

/-- Radial shells derive the collective alias-cancellation regularity with no
additional analytic premise. -/
theorem Data.toCollectiveWindowRegularity
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : Data F) :
    AggregateSynthesisBridge.CollectiveWindowRegularity F := by
  refine
    { commonPeriod := h.commonPeriod
      supportRadius := h.supportRadius
      period_eq := h.period_eq
      period_pos := h.period_pos
      supportRadius_nonneg := h.supportRadius_nonneg
      smooth := h.smooth
      support := h.support
      even := h.even
      aggregate_aliases_cancel := ?_ }
  intro T
  exact RadialShellAlias.aggregateAliasCancellation_of_radialShells
    T (h.commonPeriod T) (h.supportRadius T) (F.window T)
    (h.shell T) (h.innerRadius T) (h.outerRadius T)
    (h.period_pos T) (h.supportRadius_nonneg T)
    (h.smooth T) (h.support T) (h.even T)
    (h.shell_support T) (h.shell_inner T) (h.shell_outer T)

/-- A literal terminal energy-tail estimate under radial-shell data hands
directly to the isometric quartic lower bound. -/
theorem literalEnergyTailLowerBound_toIsometric
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hshell : Data F)
    (htail :
      LiteralEnergyTailQuarticLowerBound (F := F) q) :
    IsometricBlock.WeightedQuarticLowerBound q
      (coordinateData (literalBlockSelection F)) :=
  AggregateSynthesisBridge.literalEnergyTailLowerBound_toIsometricCollective
    hshell.toCollectiveWindowRegularity htail

end RadialShellFamily
end Zeta85
end RH

end
