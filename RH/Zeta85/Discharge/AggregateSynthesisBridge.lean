/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.AggregateCoordinateFrame
import RH.Zeta85.Discharge.AggregateComplexAlias

/-!
# Collective synthesis bridge

This module evaluates the complete physical-channel frequency lattice after
summing the channels.  Individual channels need not be alias-free.  The only
cancellation premise is that the total nonzero alias contribution vanishes.
-/

open Filter Matrix Finset Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace AggregateSynthesisBridge

open Zeta23
open AggregateCoordinateFrame

/-- Physical-window regularity for a common-period collective synthesis.
Unlike PhysicalWindowRegularity, this imposes no channelwise half-period
support.  Nonzero aliases are allowed and cancel only after channel summation. -/
structure CollectiveWindowRegularity
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  commonPeriod : ℝ → ℝ
  supportRadius :
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
  aggregate_aliases_cancel :
    ∀ T,
      AggregateComplexAlias.AggregateAliasCancellation
        T (commonPeriod T) (F.window T)

/-- Collective nonzero-alias cancellation evaluates the same full frequency
lattice used by the literal coordinate frame. -/
theorem coordinateFullFrequencyLattice_eq_energySum_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : CollectiveWindowRegularity F)
    (T : ℝ) (ρ ρ' : ℂ) :
    coordinateFullFrequencyLattice F T ρ ρ' =
      coordinateEnergySum F T ρ ρ' := by
  unfold coordinateFullFrequencyLattice coordinateEnergySum
  simp_rw [h.period_eq T]
  calc
    (∑ j : Fin (F.channelCount T),
      ((Real.sqrt
          (F.fullLength T / h.commonPeriod T) : ℂ) ^ 2) *
        ComplexAliasBridge.virtualFrequencyPairSum
          T (h.commonPeriod T) (F.window T j)
          (gammaOf ρ) (gammaOf ρ')) =
        ((Real.sqrt
            (F.fullLength T / h.commonPeriod T) : ℂ) ^ 2) *
          AggregateComplexAlias.aggregateVirtualFrequencyPairSum
            T (h.commonPeriod T) (F.window T)
            (gammaOf ρ) (gammaOf ρ') := by
      unfold AggregateComplexAlias.aggregateVirtualFrequencyPairSum
      rw [Finset.mul_sum]
    _ =
        ((Real.sqrt
            (F.fullLength T / h.commonPeriod T) : ℂ) ^ 2) *
          ((h.commonPeriod T : ℂ) *
            AggregateComplexAlias.aggregateVirtualEnergyIntegral
              (F.window T) (gammaOf ρ) (gammaOf ρ')) := by
      rw [AggregateComplexAlias.aggregateVirtualFrequencyPairSum_eq_energyIntegral
        T (h.commonPeriod T) (h.supportRadius T) (F.window T)
        (h.period_pos T) (h.supportRadius_nonneg T)
        (h.smooth T) (h.support T) (h.even T)
        (h.aggregate_aliases_cancel T) (gammaOf ρ) (gammaOf ρ')]
    _ =
        ∑ j : Fin (F.channelCount T),
          ((Real.sqrt
              (F.fullLength T / h.commonPeriod T) : ℂ) ^ 2) *
            (h.commonPeriod T : ℂ) *
            ∫ u : ℝ,
              (F.window T j u : ℂ) * F.window T j u *
                Complex.exp
                  (Complex.I *
                    (gammaOf ρ - gammaOf ρ') * (u : ℂ)) := by
      unfold AggregateComplexAlias.aggregateVirtualEnergyIntegral
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring


/-- A common positive period cancels every square-root modulation
normalization after the channels are summed.  Thus collective synthesis
depends only on the total physical window-energy profile. -/
theorem coordinateEnergySum_eq_fullLength_windowEnergy_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : CollectiveWindowRegularity F)
    (T : ℝ) (hfull : 0 ≤ F.fullLength T)
    (ρ ρ' : ℂ) :
    coordinateEnergySum F T ρ ρ' =
      (F.fullLength T : ℂ) *
        ∫ u : ℝ,
          (F.windowEnergy T u : ℂ) *
            Complex.exp
              (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) := by
  unfold coordinateEnergySum
  calc
    (∑ j : Fin (F.channelCount T),
      ((Real.sqrt (F.fullLength T / F.period T j) : ℂ) ^ 2) *
        (F.period T j : ℂ) *
        ∫ u : ℝ,
          (F.window T j u : ℂ) * F.window T j u *
            Complex.exp
              (Complex.I *
                (gammaOf ρ - gammaOf ρ') * (u : ℂ))) =
        ∑ j : Fin (F.channelCount T),
          (F.fullLength T : ℂ) *
            ∫ u : ℝ,
              (F.window T j u : ℂ) * F.window T j u *
                Complex.exp
                  (Complex.I *
                    (gammaOf ρ - gammaOf ρ') * (u : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hperiod : 0 < F.period T j := by
        rw [h.period_eq T j]
        exact h.period_pos T
      have hquot : 0 ≤ F.fullLength T / F.period T j :=
        div_nonneg hfull hperiod.le
      have hreal :
          Real.sqrt (F.fullLength T / F.period T j) ^ 2 *
              F.period T j =
            F.fullLength T := by
        rw [Real.sq_sqrt hquot]
        exact div_mul_cancel₀ _ hperiod.ne'
      have hcomplex :=
        congrArg (fun x : ℝ => (x : ℂ)) hreal
      push_cast at hcomplex
      rw [hcomplex]
    _ = (F.fullLength T : ℂ) *
        ∑ j : Fin (F.channelCount T),
          ∫ u : ℝ,
            (F.window T j u : ℂ) * F.window T j u *
              Complex.exp
                (Complex.I *
                  (gammaOf ρ - gammaOf ρ') * (u : ℂ)) := by
      rw [Finset.mul_sum]
    _ = (F.fullLength T : ℂ) *
        ∫ u : ℝ,
          (F.windowEnergy T u : ℂ) *
            Complex.exp
              (Complex.I *
                (gammaOf ρ - gammaOf ρ') * (u : ℂ)) := by
      congr 1
      calc
        (∑ j : Fin (F.channelCount T),
          ∫ u : ℝ,
            (F.window T j u : ℂ) * F.window T j u *
              Complex.exp
                (Complex.I *
                  (gammaOf ρ - gammaOf ρ') * (u : ℂ))) =
            ∑ j : Fin (F.channelCount T),
              F.complexAliasTerm T
                (gammaOf ρ) (gammaOf ρ') j 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (ComplexAliasBridge.complexAliasTerm_zero
            F T j (gammaOf ρ) (gammaOf ρ')).symm
        _ = _ :=
          ComplexAliasBridge.sum_complexAliasTerm_zero_eq_integral_windowEnergy
            F T (gammaOf ρ) (gammaOf ρ')
            (fun j =>
              ComplexAliasBridge.integrable_zeroAliasIntegrand
                F T j (h.supportRadius T j)
                (h.supportRadius_nonneg T j)
                (h.smooth T j) (h.support T j)
                (gammaOf ρ) (gammaOf ρ'))

/-- Under collective cancellation, the literal energy-tail kernel is the
normalized Fourier transform of total physical energy minus the single
finite frequency tail. -/
theorem literalCoordinateEnergyTailPairKernel_eq_windowEnergy_sub_tail_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : CollectiveWindowRegularity F)
    (T : ℝ) (hfull : 0 ≤ F.fullLength T)
    (ρ ρ' : ℂ) :
    literalCoordinateEnergyTailPairKernel F T ρ ρ' =
      ((F.hatDenominator T)⁻¹ : ℂ) *
        ((F.fullLength T : ℂ) *
            ∫ u : ℝ,
              (F.windowEnergy T u : ℂ) *
                Complex.exp
                  (Complex.I *
                    (gammaOf ρ - gammaOf ρ') * (u : ℂ)) -
          coordinateFrequencyTail
            (literalBlockSelection F) T ρ ρ') := by
  unfold literalCoordinateEnergyTailPairKernel
  rw [coordinateEnergySum_eq_fullLength_windowEnergy_collective
    h T hfull]

/-- The selected finite physical grid is the collectively evaluated energy
minus the same one aggregate frequency tail. -/
theorem coordinateSelectedFrequencyGrid_eq_energy_sub_tail_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (h : CollectiveWindowRegularity F)
    (T : ℝ) (ρ ρ' : ℂ) :
    coordinateSelectedFrequencyGrid S T ρ ρ' =
      coordinateEnergySum F T ρ ρ' -
        coordinateFrequencyTail S T ρ ρ' := by
  rw [← coordinateFullFrequencyLattice_eq_energySum_collective h]
  unfold coordinateFrequencyTail
  ring

/-- Coordinate compression now has an exact collective energy-minus-tail
kernel without any channelwise support-gap premise. -/
theorem mixedPairKernel_coordinate_eq_energy_sub_tail_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (h : CollectiveWindowRegularity F)
    (T : ℝ) (ρ ρ' : ℂ) :
    IsometricKernel.mixedPairKernel
        (coordinateRealData S) T ρ ρ' =
      ((F.hatDenominator T)⁻¹ : ℂ) *
        (coordinateEnergySum F T ρ ρ' -
          coordinateFrequencyTail S T ρ ρ') := by
  rw [mixedPairKernel_coordinate_eq_finitePairSum,
    coordinateFinitePairSum_eq_selectedFrequencyGrid,
    coordinateSelectedFrequencyGrid_eq_energy_sub_tail_collective S h]

/-- The literal frozen block's mixed kernel is exactly the collective
energy-minus-tail kernel. -/
theorem mixedPairKernel_literal_eq_energyTail_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : CollectiveWindowRegularity F)
    (T : ℝ) (ρ ρ' : ℂ) :
    IsometricKernel.mixedPairKernel
        (coordinateRealData (literalBlockSelection F)) T ρ ρ' =
      literalCoordinateEnergyTailPairKernel F T ρ ρ' := by
  unfold literalCoordinateEnergyTailPairKernel
  exact mixedPairKernel_coordinate_eq_energy_sub_tail_collective
    (literalBlockSelection F) h T ρ ρ'

/-- The literal centered quartic numerator is the finite zero contraction of
the collectively evaluated energy-minus-tail kernel. -/
theorem quarticTraceNumerator_eq_literalEnergyTail_collective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : TrimmedMoment.Quartic}
    {F : QuarticGramFamily Z σ μ p v}
    (h : CollectiveWindowRegularity F)
    (T : ℝ) :
    QuarticTransfer.quarticTraceNumerator q F T =
      QuarticTransfer.pairKernelQuarticNumerator q F T
        (literalCoordinateEnergyTailPairKernel F T) := by
  rw [quarticTraceNumerator_eq_literalCoordinatePairKernel F T]
  unfold IsometricKernel.mixedPairKernelQuarticNumerator
  apply QuarticTransfer.pairKernelQuarticNumerator_congr
  intro ρ hρ ρ' hρ'
  exact mixedPairKernel_literal_eq_energyTail_collective h T ρ ρ'

/-- The literal energy-tail lower bound supplies the mixed pair-kernel
boundary under collective, rather than channelwise, alias cancellation. -/
theorem literalEnergyTailLowerBound_toMixedCollective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : CollectiveWindowRegularity F)
    (h : LiteralEnergyTailQuarticLowerBound (F := F) q) :
    IsometricKernel.MixedPairKernelQuarticLowerBound q
      (coordinateRealData (literalBlockSelection F)) := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  have heq :
      IsometricKernel.mixedPairKernelQuarticNumerator q
          (coordinateRealData (literalBlockSelection F)) T =
        QuarticTransfer.pairKernelQuarticNumerator q F T
          (literalCoordinateEnergyTailPairKernel F T) := by
    rw [← quarticTraceNumerator_eq_literalCoordinatePairKernel F T,
      quarticTraceNumerator_eq_literalEnergyTail_collective hreg T]
  rw [heq]
  exact hT

/-- Direct collective handoff to the isometric quartic transfer consumed by
the frozen rungs. -/
theorem literalEnergyTailLowerBound_toIsometricCollective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic}
    (hreg : CollectiveWindowRegularity F)
    (h : LiteralEnergyTailQuarticLowerBound (F := F) q) :
    IsometricBlock.WeightedQuarticLowerBound q
      (coordinateData (literalBlockSelection F)) :=
  (literalEnergyTailLowerBound_toMixedCollective hreg h).toIsometric

end AggregateSynthesisBridge
end Zeta85
end RH

end
