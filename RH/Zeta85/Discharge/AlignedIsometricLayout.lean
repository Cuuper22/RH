/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RepeatedChannelCompression
import RH.Zeta85.Discharge.ComplexAliasBridge

/-!
# Aligned finite-frame layouts inside the quartic block

A row equivalence identifies the physical column space with channel-label
pairs.  A label-dependent virtual channel then gives an exact real isometric
compression into the retained block.  If the physical Fourier atoms are the
corresponding synthesized virtual atoms, mixing first recovers the selected
virtual atom exactly.
-/

open Matrix Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace AlignedIsometricLayout

open Zeta23
open VirtualChannelMixer RepeatedChannelCompression

/-- Finite channel-label coordinates for one quartic Gram family. -/
structure Layout
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  frame : VirtualChannelMixer.Data ι
  selected : ∀ T : ℝ, Fin (F.blockDim T) → ι
  rowEquiv : ∀ T : ℝ,
    Fin (F.dim T) ≃ ι × Fin (F.blockDim T)

/-- Transport the routed channel compression across the physical row
equivalence. -/
def compression
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) (T : ℝ) :
    Matrix (Fin (F.dim T)) (Fin (F.blockDim T)) ℂ :=
  fun i a =>
    routedMatrix L.frame (L.selected T) (L.rowEquiv T i) a

/-- The transported routed compression is an exact isometry. -/
theorem compression_isometry
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) (T : ℝ) :
    (compression L T)ᴴ * compression L T = 1 := by
  classical
  ext a b
  change
    (∑ i : Fin (F.dim T),
      star (routedMatrix L.frame (L.selected T)
        (L.rowEquiv T i) a) *
      routedMatrix L.frame (L.selected T)
        (L.rowEquiv T i) b) =
      (1 : Matrix (Fin (F.blockDim T))
        (Fin (F.blockDim T)) ℂ) a b
  have hsum :
      (∑ i : Fin (F.dim T),
        (fun jk =>
          star (routedMatrix L.frame (L.selected T) jk a) *
            routedMatrix L.frame (L.selected T) jk b)
          (L.rowEquiv T i)) =
        ∑ jk : ι × Fin (F.blockDim T),
          (fun jk =>
            star (routedMatrix L.frame (L.selected T) jk a) *
              routedMatrix L.frame (L.selected T) jk b) jk :=
    Equiv.sum_comp (L.rowEquiv T)
      (fun jk =>
        star (routedMatrix L.frame (L.selected T) jk a) *
          routedMatrix L.frame (L.selected T) jk b)
  rw [hsum]
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using
    congrFun (congrFun
      (routed_isometry L.frame (L.selected T)) a) b

/-- The aligned layout as data for the isometric quartic transfer. -/
def toIsometricData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) : IsometricBlock.Data F where
  compression := compression L
  isometry := compression_isometry L

/-- Routed mixer coefficients are real, so the layout is accepted by the
mix-first pair-kernel factorization. -/
def toRealData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) : IsometricKernel.RealData F where
  toData := toIsometricData L
  real_entries := by
    intro T i a
    change
      star (routedMatrix L.frame (L.selected T)
        (L.rowEquiv T i) a) =
      routedMatrix L.frame (L.selected T)
        (L.rowEquiv T i) a
    exact routed_real_entries
      L.frame (L.selected T) (L.rowEquiv T i) a

/-- The exact atom factorization requested from a physical family. -/
structure AtomFactorization
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) where
  virtualAtom :
    ∀ T : ℝ, ι → Fin (F.blockDim T) → ℂ → ℂ
  atom_eq :
    ∀ (T : ℝ) (i : Fin (F.dim T)) (ρ : ℂ),
      F.atom T i ρ =
        physicalAtom L.frame
          (fun r k => virtualAtom T r k ρ)
          (L.rowEquiv T i)

/-- Mixing the physical atoms before any zero contraction recovers the
label-selected virtual atom exactly. -/
theorem mixedAtom_eq_selected
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (A : AtomFactorization L)
    (T : ℝ) (a : Fin (F.blockDim T)) (ρ : ℂ) :
    IsometricKernel.mixedAtom (toRealData L) T a ρ =
      A.virtualAtom T (L.selected T a) a ρ := by
  unfold IsometricKernel.mixedAtom
  change
    (∑ i : Fin (F.dim T),
      routedMatrix L.frame (L.selected T)
        (L.rowEquiv T i) a * F.atom T i ρ) =
      A.virtualAtom T (L.selected T a) a ρ
  simp_rw [A.atom_eq T]
  have hsum :
      (∑ i : Fin (F.dim T),
        (fun jk =>
          routedMatrix L.frame (L.selected T) jk a *
            physicalAtom L.frame
              (fun r k => A.virtualAtom T r k ρ) jk)
          (L.rowEquiv T i)) =
        ∑ jk : ι × Fin (F.blockDim T),
          (fun jk =>
            routedMatrix L.frame (L.selected T) jk a *
              physicalAtom L.frame
                (fun r k => A.virtualAtom T r k ρ) jk) jk :=
    Equiv.sum_comp (L.rowEquiv T)
      (fun jk =>
        routedMatrix L.frame (L.selected T) jk a *
          physicalAtom L.frame
            (fun r k => A.virtualAtom T r k ρ) jk)
  rw [hsum]
  exact recover_routed_virtual_atom
    L.frame (L.selected T)
      (fun r k => A.virtualAtom T r k ρ) a

/-- Pair contraction written solely in the recovered virtual atoms. -/
def selectedVirtualPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (A : AtomFactorization L)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) *
    ∑ a : Fin (F.blockDim T),
      A.virtualAtom T (L.selected T a) a ρ *
        A.virtualAtom T (L.selected T a) a ρ'

/-- Exact mix-first reduction from the physical family to its routed virtual
pair kernel. -/
theorem mixedPairKernel_eq_selectedVirtualPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (A : AtomFactorization L)
    (T : ℝ) (ρ ρ' : ℂ) :
    IsometricKernel.mixedPairKernel (toRealData L) T ρ ρ' =
      selectedVirtualPairKernel A T ρ ρ' := by
  unfold IsometricKernel.mixedPairKernel selectedVirtualPairKernel
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mixedAtom_eq_selected A, mixedAtom_eq_selected A]

/-- The terminal quartic numerator after every physical channel and
compression coefficient has been eliminated. -/
def selectedVirtualQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (q : TrimmedMoment.Quartic)
    (A : AtomFactorization L) (T : ℝ) : ℝ :=
  QuarticTransfer.pairKernelQuarticNumerator q F T
    (selectedVirtualPairKernel A T)

theorem mixedPairKernelQuarticNumerator_eq_selectedVirtual
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (q : TrimmedMoment.Quartic)
    (A : AtomFactorization L) (T : ℝ) :
    IsometricKernel.mixedPairKernelQuarticNumerator
        q (toRealData L) T =
      selectedVirtualQuarticNumerator q A T := by
  unfold IsometricKernel.mixedPairKernelQuarticNumerator
    selectedVirtualQuarticNumerator
  rw [mixedPairKernel_eq_selectedVirtualPairKernel A]

/-- The sole remaining analytic statement in routed virtual coordinates. -/
structure SelectedVirtualQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (q : TrimmedMoment.Quartic)
    (A : AtomFactorization L) : Prop where
  block_dimension_pos :
    ∀ᶠ T in Filter.atTop, 0 < F.blockDim T
  eventually_gt :
    ∀ x : ℝ,
      x < μ * QuarticTransfer.limitQuarticScore q μ p →
      ∀ᶠ T in Filter.atTop,
        x < selectedVirtualQuarticNumerator q A T /
          (Z.N T (2 * T) : ℝ)

/-- A virtual-coordinate lower bound is exactly the mixed pair-kernel lower
bound required by the finite quartic algebra. -/
theorem SelectedVirtualQuarticLowerBound.toMixed
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {q : TrimmedMoment.Quartic}
    {A : AtomFactorization L}
    (h : SelectedVirtualQuarticLowerBound q A) :
    IsometricKernel.MixedPairKernelQuarticLowerBound
      q (toRealData L) := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  simpa only [mixedPairKernelQuarticNumerator_eq_selectedVirtual] using
    h.eventually_gt x hx

/-- Direct handoff from routed virtual atoms to the isometric terminal
statistic consumed by every frozen rung. -/
theorem SelectedVirtualQuarticLowerBound.toIsometric
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {q : TrimmedMoment.Quartic}
    {A : AtomFactorization L}
    (h : SelectedVirtualQuarticLowerBound q A) :
    IsometricBlock.WeightedQuarticLowerBound
      q (toIsometricData L) :=
  h.toMixed.toIsometric


/-! ## Balanced routing across every virtual channel -/

/-- A routed block grid: every retained block label is exactly one virtual
channel together with one modulation label.  This replaces the impossible
single-principal-channel allocation by a bijective distribution across all
virtual tiles. -/
structure RoutedGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) where
  labelCount : ℝ → ℕ
  labelEquiv : ∀ T : ℝ,
    Fin (F.blockDim T) ≃ ι × Fin (labelCount T)
  selected_eq : ∀ (T : ℝ) (a : Fin (F.blockDim T)),
    L.selected T a = (labelEquiv T a).1

/-- The virtual atom addressed by a virtual-channel/modulation pair. -/
def routedVirtualAtom
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (G : RoutedGrid L)
    (A : AtomFactorization L) (T : ℝ)
    (r : ι) (k : Fin (G.labelCount T)) (ρ : ℂ) : ℂ :=
  A.virtualAtom T r ((G.labelEquiv T).symm (r, k)) ρ

/-- Pair sum after the routed block has been reindexed as the full virtual
channel-by-label product. -/
def routedVirtualPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (G : RoutedGrid L)
    (A : AtomFactorization L) (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑ r : ι, ∑ k : Fin (G.labelCount T),
    routedVirtualAtom G A T r k ρ *
      routedVirtualAtom G A T r k ρ'

/-- Every channel-label pair is selected by its own inverse grid address. -/
theorem RoutedGrid.selected_symm
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (G : RoutedGrid L)
    (T : ℝ) (r : ι) (k : Fin (G.labelCount T)) :
    L.selected T ((G.labelEquiv T).symm (r, k)) = r := by
  rw [G.selected_eq]
  simp

/-- Exact allocation redesign: the selected virtual pair kernel is the
complete sum over every virtual tile and every modulation label.  No
distinguished physical channel occurs in the statement. -/
theorem selectedVirtualPairKernel_eq_routedGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (G : RoutedGrid L)
    (A : AtomFactorization L) (T : ℝ) (ρ ρ' : ℂ) :
    selectedVirtualPairKernel A T ρ ρ' =
      ((F.hatDenominator T)⁻¹ : ℂ) *
        routedVirtualPairSum G A T ρ ρ' := by
  unfold selectedVirtualPairKernel routedVirtualPairSum
  apply congrArg (fun w : ℂ =>
    ((F.hatDenominator T)⁻¹ : ℂ) * w)
  calc
    (∑ a : Fin (F.blockDim T),
      A.virtualAtom T (L.selected T a) a ρ *
        A.virtualAtom T (L.selected T a) a ρ') =
      ∑ a : Fin (F.blockDim T),
        A.virtualAtom T ((G.labelEquiv T a).1) a ρ *
          A.virtualAtom T ((G.labelEquiv T a).1) a ρ' := by
      apply Finset.sum_congr rfl
      intro a _
      rw [G.selected_eq]
    _ = ∑ rk : ι × Fin (G.labelCount T),
        A.virtualAtom T rk.1 ((G.labelEquiv T).symm rk) ρ *
          A.virtualAtom T rk.1 ((G.labelEquiv T).symm rk) ρ' := by
      simpa using
        (Equiv.sum_comp (G.labelEquiv T)
          (fun rk : ι × Fin (G.labelCount T) =>
            A.virtualAtom T rk.1 ((G.labelEquiv T).symm rk) ρ *
              A.virtualAtom T rk.1
                ((G.labelEquiv T).symm rk) ρ'))
    _ = ∑ r : ι, ∑ k : Fin (G.labelCount T),
        routedVirtualAtom G A T r k ρ *
          routedVirtualAtom G A T r k ρ' := by
      simp only [Fintype.sum_prod_type, routedVirtualAtom]


/-! ## Exact finite-grid tail in routed virtual coordinates -/

/-- Fourier realization of every routed virtual label.  The defining field is
the product identity actually consumed by the pair kernel, so the square-root
normalization is discharged once at construction time. -/
structure RoutedFourierGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (G : RoutedGrid L)
    (A : AtomFactorization L) where
  period : ℝ → ι → ℝ
  supportRadius : ℝ → ι → ℝ
  window : ℝ → ι → ℝ → ℝ
  frequency : ∀ T : ℝ, Fin (G.labelCount T) → ℤ
  product_eq :
    ∀ (T : ℝ) (r : ι) (k : Fin (G.labelCount T))
      (ρ ρ' : ℂ),
      routedVirtualAtom G A T r k ρ *
          routedVirtualAtom G A T r k ρ' =
        ((F.fullLength T : ℂ) / (period T r : ℂ)) *
          (paperFT (fun u => (window T r u : ℂ))
              (gammaOf ρ -
                (T + (frequency T k : ℝ) *
                  (2 * Real.pi / period T r) : ℝ)) *
            paperFT (fun u => (window T r u : ℂ))
              (gammaOf ρ' -
                (T + (frequency T k : ℝ) *
                  (2 * Real.pi / period T r) : ℝ)))

/-- The regularity and closed-half-period support needed by the standalone
complex Poisson theorem, imposed channel by channel on the routed windows. -/
structure RoutedWindowRegularity
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    {A : AtomFactorization L}
    (H : RoutedFourierGrid G A) : Prop where
  period_pos : ∀ T r, 0 < H.period T r
  supportRadius_nonneg : ∀ T r, 0 ≤ H.supportRadius T r
  smooth : ∀ T r,
    ContDiff ℝ 2 (fun u => (H.window T r u : ℂ))
  support : ∀ T r u,
    H.supportRadius T r < |u| → H.window T r u = 0
  even : ∀ T r u, H.window T r (-u) = H.window T r u
  half_support : ∀ T r,
    tsupport (H.window T r) ⊆
      Icc (-H.period T r / 2) (H.period T r / 2)

/-- The omitted part of the integer frequency lattice.  It is defined as the
complete Poisson lattice minus the finite routed labels, so subsequent
estimates target one explicit object. -/
def routedVirtualFrequencyTail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    {A : AtomFactorization L}
    (H : RoutedFourierGrid G A)
    (T : ℝ) (r : ι) (ρ ρ' : ℂ) : ℂ :=
  ComplexAliasBridge.virtualFrequencyPairSum
      T (H.period T r) (H.window T r)
      (gammaOf ρ) (gammaOf ρ') -
    ∑ k : Fin (G.labelCount T),
      paperFT (fun u => (H.window T r u : ℂ))
          (gammaOf ρ -
            (T + (H.frequency T k : ℝ) *
              (2 * Real.pi / H.period T r) : ℝ)) *
        paperFT (fun u => (H.window T r u : ℂ))
          (gammaOf ρ' -
            (T + (H.frequency T k : ℝ) *
              (2 * Real.pi / H.period T r) : ℝ))

/-- The routed pair sum is exactly the normalized finite Fourier grid. -/
theorem routedVirtualPairSum_eq_frequencyGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    {A : AtomFactorization L}
    (H : RoutedFourierGrid G A)
    (T : ℝ) (ρ ρ' : ℂ) :
    routedVirtualPairSum G A T ρ ρ' =
      ∑ r : ι,
        ((F.fullLength T : ℂ) / (H.period T r : ℂ)) *
          ∑ k : Fin (G.labelCount T),
            paperFT (fun u => (H.window T r u : ℂ))
                (gammaOf ρ -
                  (T + (H.frequency T k : ℝ) *
                    (2 * Real.pi / H.period T r) : ℝ)) *
              paperFT (fun u => (H.window T r u : ℂ))
                (gammaOf ρ' -
                  (T + (H.frequency T k : ℝ) *
                    (2 * Real.pi / H.period T r) : ℝ)) := by
  unfold routedVirtualPairSum
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [H.product_eq T r]
  rw [← Finset.mul_sum]

/-- Exact full-lattice decomposition: the only difference between the routed
finite grid and the Poisson lattice is the named frequency tail. -/
theorem routedVirtualPairSum_eq_fullLattice_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    {A : AtomFactorization L}
    (H : RoutedFourierGrid G A)
    (T : ℝ) (ρ ρ' : ℂ) :
    routedVirtualPairSum G A T ρ ρ' =
      ∑ r : ι,
        ((F.fullLength T : ℂ) / (H.period T r : ℂ)) *
          (ComplexAliasBridge.virtualFrequencyPairSum
              T (H.period T r) (H.window T r)
              (gammaOf ρ) (gammaOf ρ') -
            routedVirtualFrequencyTail H T r ρ ρ') := by
  rw [routedVirtualPairSum_eq_frequencyGrid H]
  apply Finset.sum_congr rfl
  intro r _
  unfold routedVirtualFrequencyTail
  ring

/-- Closed half-period support evaluates the complete lattice before the
finite-grid tail is subtracted. -/
theorem routedVirtualPairSum_eq_energy_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    {A : AtomFactorization L}
    (H : RoutedFourierGrid G A)
    (h : RoutedWindowRegularity H)
    (T : ℝ) (ρ ρ' : ℂ) :
    routedVirtualPairSum G A T ρ ρ' =
      ∑ r : ι,
        (F.fullLength T : ℂ) *
            ∫ u : ℝ,
              (H.window T r u : ℂ) * H.window T r u *
                Complex.exp
                  (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) -
          ((F.fullLength T : ℂ) / (H.period T r : ℂ)) *
            routedVirtualFrequencyTail H T r ρ ρ' := by
  rw [routedVirtualPairSum_eq_fullLattice_sub_tail H]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_sub]
  rw [ComplexAliasBridge.virtualNormalizedFrequencyPairSum_eq_energyIntegral
    (F.fullLength T) T (H.period T r) (H.supportRadius T r)
    (H.window T r) (h.period_pos T r)
    (h.supportRadius_nonneg T r) (h.smooth T r)
    (h.support T r) (h.even T r) (h.half_support T r)
    (gammaOf ρ) (gammaOf ρ')]

/-- The selected block kernel is now an evaluated energy transform minus the
single explicit finite-grid tail, with no principal physical channel. -/
theorem selectedVirtualPairKernel_eq_energy_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    {A : AtomFactorization L}
    (H : RoutedFourierGrid G A)
    (h : RoutedWindowRegularity H)
    (T : ℝ) (ρ ρ' : ℂ) :
    selectedVirtualPairKernel A T ρ ρ' =
      ((F.hatDenominator T)⁻¹ : ℂ) *
        ∑ r : ι,
          (F.fullLength T : ℂ) *
              ∫ u : ℝ,
                (H.window T r u : ℂ) * H.window T r u *
                  Complex.exp
                    (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) -
            ((F.fullLength T : ℂ) / (H.period T r : ℂ)) *
              routedVirtualFrequencyTail H T r ρ ρ' := by
  rw [selectedVirtualPairKernel_eq_routedGrid G]
  rw [routedVirtualPairSum_eq_energy_sub_tail H h]

end AlignedIsometricLayout
end Zeta85
end RH

end
