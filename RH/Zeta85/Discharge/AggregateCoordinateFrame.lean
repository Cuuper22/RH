/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.ComplexAliasBridge
import RH.Zeta85.Discharge.IsometricKernel

/-!
# Aggregate coordinate frames

A fixed product decomposition of the physical column space forces divisibility
relations that the height-dependent finite grids do not naturally satisfy.
This module instead selects the retained coordinates directly, sums each
complete physical-channel frequency lattice first, and subtracts the actual
finite selected grid only afterward.

The resulting remainder is one aggregate tail.  All identities below are
exact finite or Poisson identities; no limiting assertion is assumed.
-/

open Filter Matrix Finset Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace AggregateCoordinateFrame

open Zeta23

/-- A height-dependent choice of retained physical coordinates. -/
structure CoordinateSelection
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) where
  embedding :
    ∀ T : ℝ, Fin (F.blockDim T) ↪ Fin (F.dim T)

/-- Coordinate inclusion matrix attached to a selected finite grid. -/
def coordinateCompression
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F) (T : ℝ) :
    Matrix (Fin (F.dim T)) (Fin (F.blockDim T)) ℂ :=
  fun i a => if i = S.embedding T a then 1 else 0

/-- Coordinate inclusion has orthonormal columns. -/
theorem coordinateCompression_isometry
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F) (T : ℝ) :
    (coordinateCompression S T)ᴴ *
        coordinateCompression S T = 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    coordinateCompression]
  by_cases hab : a = b
  · subst b
    simp
  · have he : S.embedding T a ≠ S.embedding T b :=
      fun h => hab ((S.embedding T).injective h)
    simp [he, hab]

/-- Every coordinate selection is an isometric compression. -/
def coordinateData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F) : IsometricBlock.Data F where
  compression := coordinateCompression S
  isometry := coordinateCompression_isometry S

/-- Coordinate inclusions are real, so they may be mixed before the zero
contraction. -/
def coordinateRealData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F) : IsometricKernel.RealData F where
  toData := coordinateData S
  real_entries := by
    intro T i a
    simp [coordinateData, coordinateCompression]

/-- Mixing by a coordinate inclusion simply selects the corresponding
physical Fourier atom. -/
theorem mixedAtom_coordinate
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (T : ℝ) (a : Fin (F.blockDim T)) (ρ : ℂ) :
    IsometricKernel.mixedAtom (coordinateRealData S) T a ρ =
      F.atom T (S.embedding T a) ρ := by
  classical
  unfold IsometricKernel.mixedAtom
  change
    (∑ i : Fin (F.dim T),
      (if i = S.embedding T a then 1 else 0) * F.atom T i ρ) =
        F.atom T (S.embedding T a) ρ
  simp

/-- The exact finite pair sum on the selected physical columns. -/
def coordinateFinitePairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑ a : Fin (F.blockDim T),
    F.atom T (S.embedding T a) ρ *
      F.atom T (S.embedding T a) ρ'

/-- Coordinate compression turns the mixed pair kernel into the selected
finite physical-column sum. -/
theorem mixedPairKernel_coordinate_eq_finitePairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (T : ℝ) (ρ ρ' : ℂ) :
    IsometricKernel.mixedPairKernel
        (coordinateRealData S) T ρ ρ' =
      ((F.hatDenominator T)⁻¹ : ℂ) *
        coordinateFinitePairSum S T ρ ρ' := by
  unfold IsometricKernel.mixedPairKernel coordinateFinitePairSum
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mixedAtom_coordinate, mixedAtom_coordinate]

/-- The same selected finite grid with every physical address and modulation
frequency exposed. -/
def coordinateSelectedFrequencyGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑ a : Fin (F.blockDim T),
    let address := F.columnAddress T (S.embedding T a)
    let j := address.1
    let Lj := F.period T j
    let τ : ℝ := T + 2 * Real.pi * (address.2 : ℕ) / Lj
    ((Real.sqrt (F.fullLength T / Lj) : ℂ) ^ 2) *
      paperFT (fun u => (F.window T j u : ℂ)) (gammaOf ρ - τ) *
      paperFT (fun u => (F.window T j u : ℂ)) (gammaOf ρ' - τ)

/-- Expanding the literal atoms identifies the finite pair sum with the
actual selected modulation grid. -/
theorem coordinateFinitePairSum_eq_selectedFrequencyGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (T : ℝ) (ρ ρ' : ℂ) :
    coordinateFinitePairSum S T ρ ρ' =
      coordinateSelectedFrequencyGrid S T ρ ρ' := by
  unfold coordinateFinitePairSum coordinateSelectedFrequencyGrid
    QuarticGramFamily.atom
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  ring

/-- Sum every complete physical-channel frequency lattice before comparing it
with the selected finite grid. -/
def coordinateFullFrequencyLattice
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑ j : Fin (F.channelCount T),
    ((Real.sqrt (F.fullLength T / F.period T j) : ℂ) ^ 2) *
      ComplexAliasBridge.virtualFrequencyPairSum
        T (F.period T j) (F.window T j)
        (gammaOf ρ) (gammaOf ρ')

/-- One aggregate remainder: all complete channel lattices minus the actual
finite selected columns. -/
def coordinateFrequencyTail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  coordinateFullFrequencyLattice F T ρ ρ' -
    coordinateSelectedFrequencyGrid S T ρ ρ'

/-- Regularity required to evaluate every complete physical-channel lattice. -/
structure PhysicalWindowRegularity
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  supportRadius :
    ∀ T : ℝ, Fin (F.channelCount T) → ℝ
  period_pos :
    ∀ T j, 0 < F.period T j
  supportRadius_nonneg :
    ∀ T j, 0 ≤ supportRadius T j
  smooth :
    ∀ T j, ContDiff ℝ 2 (fun u => (F.window T j u : ℂ))
  support :
    ∀ T j u, supportRadius T j < |u| → F.window T j u = 0
  even :
    ∀ T j u, F.window T j (-u) = F.window T j u
  half_support :
    ∀ T j,
      tsupport (F.window T j) ⊆
        Icc (-F.period T j / 2) (F.period T j / 2)

/-- The energy expression obtained after evaluating every complete channel
lattice.  The square-root normalization is retained exactly, so the identity
holds at every real height without a hidden positivity convention. -/
def coordinateEnergySum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑ j : Fin (F.channelCount T),
    ((Real.sqrt (F.fullLength T / F.period T j) : ℂ) ^ 2) *
      (F.period T j : ℂ) *
      ∫ u : ℝ,
        (F.window T j u : ℂ) * F.window T j u *
          Complex.exp
            (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))

/-- Closed-half-period support evaluates the aggregate full lattice exactly. -/
theorem coordinateFullFrequencyLattice_eq_energySum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : PhysicalWindowRegularity F)
    (T : ℝ) (ρ ρ' : ℂ) :
    coordinateFullFrequencyLattice F T ρ ρ' =
      coordinateEnergySum F T ρ ρ' := by
  unfold coordinateFullFrequencyLattice coordinateEnergySum
  apply Finset.sum_congr rfl
  intro j _
  rw [ComplexAliasBridge.virtualFrequencyPairSum_eq_energyIntegral
    T (F.period T j) (h.supportRadius T j) (F.window T j)
    (h.period_pos T j) (h.supportRadius_nonneg T j)
    (h.smooth T j) (h.support T j) (h.even T j)
    (h.half_support T j) (gammaOf ρ) (gammaOf ρ')]
  ring

/-- The actual selected finite grid is the evaluated aggregate energy minus
the single aggregate frequency tail. -/
theorem coordinateSelectedFrequencyGrid_eq_energy_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (h : PhysicalWindowRegularity F)
    (T : ℝ) (ρ ρ' : ℂ) :
    coordinateSelectedFrequencyGrid S T ρ ρ' =
      coordinateEnergySum F T ρ ρ' -
        coordinateFrequencyTail S T ρ ρ' := by
  rw [← coordinateFullFrequencyLattice_eq_energySum h]
  unfold coordinateFrequencyTail
  ring

/-- Final aggregate identity: an arbitrary coordinate-compressed physical
kernel equals the evaluated total channel energy minus one explicit finite
selection tail.  No fixed product layout or equal fiber size occurs. -/
theorem mixedPairKernel_coordinate_eq_energy_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (S : CoordinateSelection F)
    (h : PhysicalWindowRegularity F)
    (T : ℝ) (ρ ρ' : ℂ) :
    IsometricKernel.mixedPairKernel
        (coordinateRealData S) T ρ ρ' =
      ((F.hatDenominator T)⁻¹ : ℂ) *
        (coordinateEnergySum F T ρ ρ' -
          coordinateFrequencyTail S T ρ ρ') := by
  rw [mixedPairKernel_coordinate_eq_finitePairSum,
    coordinateFinitePairSum_eq_selectedFrequencyGrid,
    coordinateSelectedFrequencyGrid_eq_energy_sub_tail S h]

end AggregateCoordinateFrame
end Zeta85
end RH

end
