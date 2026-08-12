/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RepeatedChannelCompression
import RH.Zeta85.Discharge.ComplexAliasBridge
import RH.Zeta85.Discharge.SmoothRadialShell

/-!
# Aligned finite-frame layouts inside the quartic block

A row equivalence identifies the physical column space with channel-label
pairs.  A label-dependent virtual channel then gives an exact real isometric
compression into the retained block.  If the physical Fourier atoms are the
corresponding synthesized virtual atoms, mixing first recovers the selected
virtual atom exactly.
-/

open Matrix Finset Set
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


/-! ## Factor only where the quartic actually samples -/

/-- A virtual factorization on the actual finite enlarged-window zero set.
The quartic contractions never evaluate atoms away from this set. -/
structure SampledAtomFactorization
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) where
  virtualAtom :
    ∀ T : ℝ, ι → Fin (F.blockDim T) → ℂ → ℂ
  atom_eq_on_zero :
    ∀ (T : ℝ) (i : Fin (F.dim T)) (ρ : ℂ),
      ρ ∈ ZeroSide.ZI Z T →
        F.atom T i ρ =
          physicalAtom L.frame
            (fun r k => virtualAtom T r k ρ)
            (L.rowEquiv T i)

/-- On every zero used by the finite quartic contraction, mixing recovers
the selected sampled virtual atom exactly. -/
theorem mixedAtom_eq_selected_on_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (A : SampledAtomFactorization L)
    (T : ℝ) (a : Fin (F.blockDim T)) (ρ : ℂ)
    (hρ : ρ ∈ ZeroSide.ZI Z T) :
    IsometricKernel.mixedAtom (toRealData L) T a ρ =
      A.virtualAtom T (L.selected T a) a ρ := by
  unfold IsometricKernel.mixedAtom
  change
    (∑ i : Fin (F.dim T),
      routedMatrix L.frame (L.selected T)
        (L.rowEquiv T i) a * F.atom T i ρ) =
      A.virtualAtom T (L.selected T a) a ρ
  have hatom (i : Fin (F.dim T)) :
      F.atom T i ρ =
        physicalAtom L.frame
          (fun r k => A.virtualAtom T r k ρ)
          (L.rowEquiv T i) :=
    A.atom_eq_on_zero T i ρ hρ
  simp_rw [hatom]
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

/-- Pair contraction formed from the sampled virtual atoms.  Values away
from the finite zero set are irrelevant and may be chosen freely. -/
def sampledVirtualPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (A : SampledAtomFactorization L)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) *
    ∑ a : Fin (F.blockDim T),
      A.virtualAtom T (L.selected T a) a ρ *
        A.virtualAtom T (L.selected T a) a ρ'

/-- The physical and sampled virtual pair kernels agree at every pair of
points used by the quartic zero cycles. -/
theorem mixedPairKernel_eq_sampledVirtualPairKernel_on_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (A : SampledAtomFactorization L)
    (T : ℝ) (ρ ρ' : ℂ)
    (hρ : ρ ∈ ZeroSide.ZI Z T)
    (hρ' : ρ' ∈ ZeroSide.ZI Z T) :
    IsometricKernel.mixedPairKernel (toRealData L) T ρ ρ' =
      sampledVirtualPairKernel A T ρ ρ' := by
  unfold IsometricKernel.mixedPairKernel sampledVirtualPairKernel
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mixedAtom_eq_selected_on_zero A T a ρ hρ,
    mixedAtom_eq_selected_on_zero A T a ρ' hρ']

/-- Quartic numerator generated by the sampled virtual pair kernel. -/
def sampledVirtualQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (q : TrimmedMoment.Quartic)
    (A : SampledAtomFactorization L) (T : ℝ) : ℝ :=
  QuarticTransfer.pairKernelQuarticNumerator q F T
    (sampledVirtualPairKernel A T)

/-- Finite-set congruence removes the obsolete global atom identity from the
entire quartic numerator. -/
theorem mixedPairKernelQuarticNumerator_eq_sampledVirtual
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (q : TrimmedMoment.Quartic)
    (A : SampledAtomFactorization L) (T : ℝ) :
    IsometricKernel.mixedPairKernelQuarticNumerator
        q (toRealData L) T =
      sampledVirtualQuarticNumerator q A T := by
  unfold IsometricKernel.mixedPairKernelQuarticNumerator
    sampledVirtualQuarticNumerator
  apply QuarticTransfer.pairKernelQuarticNumerator_congr
  intro ρ hρ ρ' hρ'
  exact mixedPairKernel_eq_sampledVirtualPairKernel_on_zero
    A T ρ ρ' hρ hρ'

/-- The analytic lower bound after the factorization has been restricted to
the exact finite sample used by the target. -/
structure SampledVirtualQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} (q : TrimmedMoment.Quartic)
    (A : SampledAtomFactorization L) : Prop where
  block_dimension_pos :
    ∀ᶠ T in Filter.atTop, 0 < F.blockDim T
  eventually_gt :
    ∀ x : ℝ,
      x < μ * QuarticTransfer.limitQuarticScore q μ p →
      ∀ᶠ T in Filter.atTop,
        x < sampledVirtualQuarticNumerator q A T /
          (Z.N T (2 * T) : ℝ)

/-- A sampled virtual lower bound supplies the exact isometric terminal
statistic used by the frozen rungs. -/
theorem SampledVirtualQuarticLowerBound.toIsometric
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {q : TrimmedMoment.Quartic}
    {A : SampledAtomFactorization L}
    (h : SampledVirtualQuarticLowerBound q A) :
    IsometricBlock.WeightedQuarticLowerBound
      q (toIsometricData L) := by
  apply IsometricKernel.MixedPairKernelQuarticLowerBound.toIsometric
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  simpa only [mixedPairKernelQuarticNumerator_eq_sampledVirtual] using
    h.eventually_gt x hx


/-! ## Canonical virtual analysis of every aligned physical family -/

/-- Every aligned layout admits an atom factorization automatically: analyze
the physical atom vector at each modulation label against the orthogonal
mixer.  No independent entire-function identity is required. -/
def canonicalAtomFactorization
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) : AtomFactorization L where
  virtualAtom := fun T r k ρ =>
    analyzeComplex L.frame
      (fun j =>
        F.atom T ((L.rowEquiv T).symm (j, k)) ρ) r
  atom_eq := by
    intro T i ρ
    unfold physicalAtom
    change
      F.atom T i ρ =
        synthesizeComplex L.frame
          (fun r =>
            analyzeComplex L.frame
              (fun j =>
                F.atom T
                  ((L.rowEquiv T).symm
                    (j, (L.rowEquiv T i).2)) ρ) r)
          (L.rowEquiv T i).1
    rw [synthesizeComplex_analyzeComplex]
    simp


/-- With the canonical virtual analysis, the selected virtual pair kernel is
definitionally the actual mixed pair kernel. -/
theorem selectedVirtualPairKernel_canonical_eq_mixedPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) (T : ℝ) (ρ ρ' : ℂ) :
    selectedVirtualPairKernel
        (canonicalAtomFactorization L) T ρ ρ' =
      IsometricKernel.mixedPairKernel (toRealData L) T ρ ρ' := by
  symm
  exact mixedPairKernel_eq_selectedVirtualPairKernel
    (canonicalAtomFactorization L) T ρ ρ'

/-- Consequently the canonical selected virtual quartic numerator is exactly
the physical mixed-block quartic numerator, with no atom-factorization
hypothesis remaining. -/
theorem selectedVirtualQuarticNumerator_canonical_eq_mixed
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : TrimmedMoment.Quartic)
    (L : Layout F ι) (T : ℝ) :
    selectedVirtualQuarticNumerator q
        (canonicalAtomFactorization L) T =
      IsometricKernel.mixedPairKernelQuarticNumerator
        q (toRealData L) T := by
  symm
  exact mixedPairKernelQuarticNumerator_eq_selectedVirtual
    q (canonicalAtomFactorization L) T
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
  frequency : ∀ T : ℝ, ι → Fin (G.labelCount T) → ℤ
  product_eq :
    ∀ (T : ℝ) (r : ι) (k : Fin (G.labelCount T))
      (ρ ρ' : ℂ),
      routedVirtualAtom G A T r k ρ *
          routedVirtualAtom G A T r k ρ' =
        ((F.fullLength T : ℂ) / (period T r : ℂ)) *
          (paperFT (fun u => (window T r u : ℂ))
              (gammaOf ρ -
                (T + (frequency T r k : ℝ) *
                  (2 * Real.pi / period T r) : ℝ)) *
            paperFT (fun u => (window T r u : ℂ))
              (gammaOf ρ' -
                (T + (frequency T r k : ℝ) *
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
            (T + (H.frequency T r k : ℝ) *
              (2 * Real.pi / H.period T r) : ℝ)) *
        paperFT (fun u => (H.window T r u : ℂ))
          (gammaOf ρ' -
            (T + (H.frequency T r k : ℝ) *
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
                  (T + (H.frequency T r k : ℝ) *
                    (2 * Real.pi / H.period T r) : ℝ)) *
              paperFT (fun u => (H.window T r u : ℂ))
                (gammaOf ρ' -
                  (T + (H.frequency T r k : ℝ) *
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

/-! ## Canonical physical kernel as an evaluated energy minus one tail -/

/-- Analyze the physical atoms first, route every retained label, and only
then apply Poisson summation.  The actual mixed physical kernel is exactly
the evaluated channel energy transforms minus the explicit finite-grid
frequency tails.  No external atom-factorization premise remains. -/
theorem mixedPairKernel_canonical_eq_energy_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) (G : RoutedGrid L)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T : ℝ) (ρ ρ' : ℂ) :
    IsometricKernel.mixedPairKernel (toRealData L) T ρ ρ' =
      ((F.hatDenominator T)⁻¹ : ℂ) *
        ∑ r : ι,
          (F.fullLength T : ℂ) *
              ∫ u : ℝ,
                (H.window T r u : ℂ) * H.window T r u *
                  Complex.exp
                    (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) -
            ((F.fullLength T : ℂ) / (H.period T r : ℂ)) *
              routedVirtualFrequencyTail H T r ρ ρ' := by
  calc
    IsometricKernel.mixedPairKernel (toRealData L) T ρ ρ' =
        selectedVirtualPairKernel
          (canonicalAtomFactorization L) T ρ ρ' :=
      (selectedVirtualPairKernel_canonical_eq_mixedPairKernel
        L T ρ ρ').symm
    _ = _ :=
      selectedVirtualPairKernel_eq_energy_sub_tail H h T ρ ρ'

/-- The evaluated energy-minus-tail expression, isolated as the kernel now
consumed by the finite quartic zero contraction. -/
def canonicalRoutedEnergyTailKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) *
    ∑ r : ι,
      (F.fullLength T : ℂ) *
          ∫ u : ℝ,
            (H.window T r u : ℂ) * H.window T r u *
              Complex.exp
                (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) -
        ((F.fullLength T : ℂ) / (H.period T r : ℂ)) *
          routedVirtualFrequencyTail H T r ρ ρ'

/-- The physical mixed kernel equals the named canonical energy-tail kernel
at every pair of complex frequencies. -/
theorem mixedPairKernel_canonical_eq_energyTailKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) (G : RoutedGrid L)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T : ℝ) (ρ ρ' : ℂ) :
    IsometricKernel.mixedPairKernel (toRealData L) T ρ ρ' =
      canonicalRoutedEnergyTailKernel H T ρ ρ' := by
  unfold canonicalRoutedEnergyTailKernel
  exact mixedPairKernel_canonical_eq_energy_sub_tail
    L G H h T ρ ρ'

/-- Quartic numerator formed directly from the canonical evaluated
energy-minus-tail kernel. -/
def canonicalRoutedEnergyTailQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (q : TrimmedMoment.Quartic)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (T : ℝ) : ℝ :=
  QuarticTransfer.pairKernelQuarticNumerator q F T
    (canonicalRoutedEnergyTailKernel H T)

/-- The complete physical mixed-block quartic numerator is exactly the
finite zero contraction of the evaluated energy-minus-tail kernel. -/
theorem mixedPairKernelQuarticNumerator_canonical_eq_energyTail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : TrimmedMoment.Quartic)
    (L : Layout F ι) (G : RoutedGrid L)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T : ℝ) :
    IsometricKernel.mixedPairKernelQuarticNumerator
        q (toRealData L) T =
      canonicalRoutedEnergyTailQuarticNumerator q H T := by
  unfold IsometricKernel.mixedPairKernelQuarticNumerator
    canonicalRoutedEnergyTailQuarticNumerator
  apply QuarticTransfer.pairKernelQuarticNumerator_congr
  intro ρ _ ρ' _
  exact mixedPairKernel_canonical_eq_energyTailKernel
    L G H h T ρ ρ'


/-! ## Symmetric exhaustion before the quartic contraction -/

/-- The common symmetric cutoff applied to every routed virtual channel.
The finite channel sum is formed before the finite zero contraction. -/
def symmetricRoutedPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (T : ℝ) (n : ℕ) (ρ ρ' : ℂ) : ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) *
    ∑ r : ι,
      ((F.fullLength T : ℂ) / (H.period T r : ℂ)) *
        ComplexAliasBridge.virtualSymmetricFrequencyPartialSum
          T (H.period T r) (H.window T r)
          (gammaOf ρ) (gammaOf ρ') n

/-- The evaluated routed energy kernel reached when the common symmetric
cutoff tends to infinity. -/
def routedEnergyPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) *
    ∑ r : ι,
      (F.fullLength T : ℂ) *
        ∫ u : ℝ,
          (H.window T r u : ℂ) * H.window T r u *
            Complex.exp
              (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))

/-- Summing the channels first preserves convergence of the common symmetric
frequency cutoff to the complete evaluated energy kernel. -/
theorem tendsto_symmetricRoutedPairKernel_energy
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T : ℝ) (ρ ρ' : ℂ) :
    Tendsto
      (fun n => symmetricRoutedPairKernel H T n ρ ρ')
      Filter.atTop
      (nhds (routedEnergyPairKernel H T ρ ρ')) := by
  unfold symmetricRoutedPairKernel routedEnergyPairKernel
  apply tendsto_const_nhds.mul
  apply tendsto_finsetSum
  intro r hr
  exact
    ComplexAliasBridge.tendsto_virtualNormalizedSymmetricFrequencyPartialSum_energy
      (F.fullLength T) T (H.period T r) (H.supportRadius T r)
      (H.window T r) (h.period_pos T r)
      (h.supportRadius_nonneg T r) (h.smooth T r)
      (h.support T r) (h.even T r) (h.half_support T r)
      (gammaOf ρ) (gammaOf ρ')

/-- Quartic numerator of the common finite symmetric routed grid. -/
def symmetricRoutedQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (q : TrimmedMoment.Quartic)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (T : ℝ) (n : ℕ) : ℝ :=
  QuarticTransfer.pairKernelQuarticNumerator q F T
    (symmetricRoutedPairKernel H T n)

/-- Quartic numerator of the complete evaluated routed energy kernel. -/
def routedEnergyQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (q : TrimmedMoment.Quartic)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (T : ℝ) : ℝ :=
  QuarticTransfer.pairKernelQuarticNumerator q F T
    (routedEnergyPairKernel H T)

/-- The whole finite quartic zero contraction converges after the channel sum
has already been formed. -/
theorem tendsto_symmetricRoutedQuarticNumerator_energy
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : TrimmedMoment.Quartic}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T : ℝ) :
    Tendsto
      (symmetricRoutedQuarticNumerator q H T)
      Filter.atTop
      (nhds (routedEnergyQuarticNumerator q H T)) := by
  apply QuarticTransfer.tendsto_pairKernelQuarticNumerator
  intro ρ hρ ρ' hρ'
  exact tendsto_symmetricRoutedPairKernel_energy H h T ρ ρ'

/-- At every fixed height, any strict lower bound for the evaluated energy
quartic numerator is already attained by one finite symmetric grid. -/
theorem exists_symmetricRoutedQuarticNumerator_gt
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : TrimmedMoment.Quartic}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T x : ℝ)
    (hx : x < routedEnergyQuarticNumerator q H T) :
    ∃ n : ℕ, x < symmetricRoutedQuarticNumerator q H T n := by
  have he :=
    (tendsto_symmetricRoutedQuarticNumerator_energy H h T).eventually
      (Ioi_mem_nhds hx)
  exact he.exists


/-- At every fixed height, the finite symmetric grid can approximate the
complete energy quartic numerator to any prescribed positive accuracy. -/
theorem exists_symmetricRoutedQuarticNumerator_dist_lt
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : TrimmedMoment.Quartic}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ,
      dist (symmetricRoutedQuarticNumerator q H T n)
        (routedEnergyQuarticNumerator q H T) < ε := by
  have he :=
    (tendsto_symmetricRoutedQuarticNumerator_energy H h T).eventually
      (Metric.ball_mem_nhds _ hε)
  simpa only [Metric.mem_ball] using he.exists

/-- Choose the common symmetric cutoff only after the complete quartic
contraction at each height.  The requested error is exponentially small in
the height, so no uniform-in-height Fourier estimate is needed. -/
noncomputable def diagonalSymmetricCutoff
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (q : TrimmedMoment.Quartic)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T : ℝ) : ℕ :=
  Classical.choose
    (exists_symmetricRoutedQuarticNumerator_dist_lt
      (q := q) H h T (Real.exp (-T)) (Real.exp_pos _))

/-- The chosen diagonal cutoff has the promised exponential error at every
height. -/
theorem diagonalSymmetricCutoff_spec
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (q : TrimmedMoment.Quartic)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T : ℝ) :
    dist
        (symmetricRoutedQuarticNumerator q H T
          (diagonalSymmetricCutoff q H h T))
        (routedEnergyQuarticNumerator q H T) <
      Real.exp (-T) :=
  Classical.choose_spec
    (exists_symmetricRoutedQuarticNumerator_dist_lt
      (q := q) H h T (Real.exp (-T)) (Real.exp_pos _))

/-- Diagonal selection converts the fixed-height symmetric-grid convergence
into an actual height-asymptotic statement. -/
theorem tendsto_diagonalSymmetricQuarticNumerator_sub_energy
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (q : TrimmedMoment.Quartic)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H) :
    Tendsto
      (fun T : ℝ =>
        symmetricRoutedQuarticNumerator q H T
            (diagonalSymmetricCutoff q H h T) -
          routedEnergyQuarticNumerator q H T)
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero
  · intro T
    exact norm_nonneg _
  · intro T
    have hs := diagonalSymmetricCutoff_spec q H h T
    simpa only [Real.norm_eq_abs, Real.dist_eq] using hs.le
  · exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

/-- Exact certificate that the routed finite labels are one of the symmetric
frequency grids.  It is stated at the already-summed level consumed by the
pair kernel, so no ordering convention for the finite labels survives. -/
structure SymmetricFrequencyExhaustion
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L)) where
  cutoff : ℝ → ℕ
  finite_sum_eq :
    ∀ (T : ℝ) (r : ι) (ρ ρ' : ℂ),
      (∑ k : Fin (G.labelCount T),
        paperFT (fun u => (H.window T r u : ℂ))
            (gammaOf ρ -
              (T + (H.frequency T r k : ℝ) *
                (2 * Real.pi / H.period T r) : ℝ)) *
          paperFT (fun u => (H.window T r u : ℂ))
            (gammaOf ρ' -
              (T + (H.frequency T r k : ℝ) *
                (2 * Real.pi / H.period T r) : ℝ))) =
        ComplexAliasBridge.virtualSymmetricFrequencyPartialSum
          T (H.period T r) (H.window T r)
          (gammaOf ρ) (gammaOf ρ') (cutoff T)

/-- Under a symmetric exhaustion certificate, the named routed tail is
literally the canonical symmetric lattice tail. -/
theorem routedVirtualFrequencyTail_eq_symmetricFrequencyTail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    {H : RoutedFourierGrid G (canonicalAtomFactorization L)}
    (S : SymmetricFrequencyExhaustion H)
    (T : ℝ) (r : ι) (ρ ρ' : ℂ) :
    routedVirtualFrequencyTail H T r ρ ρ' =
      ComplexAliasBridge.virtualSymmetricFrequencyTail
        T (H.period T r) (H.window T r)
        (gammaOf ρ) (gammaOf ρ') (S.cutoff T) := by
  unfold routedVirtualFrequencyTail
    ComplexAliasBridge.virtualSymmetricFrequencyTail
  rw [S.finite_sum_eq]

/-- A routed physical kernel whose finite labels exhaust a symmetric grid is
exactly that finite symmetric routed kernel. -/
theorem mixedPairKernel_canonical_eq_symmetricRoutedPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) (G : RoutedGrid L)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (S : SymmetricFrequencyExhaustion H)
    (T : ℝ) (ρ ρ' : ℂ) :
    IsometricKernel.mixedPairKernel (toRealData L) T ρ ρ' =
      symmetricRoutedPairKernel H T (S.cutoff T) ρ ρ' := by
  calc
    IsometricKernel.mixedPairKernel (toRealData L) T ρ ρ' =
        selectedVirtualPairKernel
          (canonicalAtomFactorization L) T ρ ρ' :=
      (selectedVirtualPairKernel_canonical_eq_mixedPairKernel
        L T ρ ρ').symm
    _ = ((F.hatDenominator T)⁻¹ : ℂ) *
        routedVirtualPairSum G (canonicalAtomFactorization L)
          T ρ ρ' :=
      selectedVirtualPairKernel_eq_routedGrid
        G (canonicalAtomFactorization L) T ρ ρ'
    _ = symmetricRoutedPairKernel H T (S.cutoff T) ρ ρ' := by
      unfold symmetricRoutedPairKernel
      rw [routedVirtualPairSum_eq_frequencyGrid H]
      apply congrArg
        (fun w : ℂ => ((F.hatDenominator T)⁻¹ : ℂ) * w)
      apply Finset.sum_congr rfl
      intro r hr
      rw [S.finite_sum_eq]

/-- Consequently the actual mixed physical quartic numerator is the chosen
finite symmetric routed numerator. -/
theorem mixedPairKernelQuarticNumerator_canonical_eq_symmetricRouted
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : TrimmedMoment.Quartic}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Layout F ι) (G : RoutedGrid L)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (S : SymmetricFrequencyExhaustion H)
    (T : ℝ) :
    IsometricKernel.mixedPairKernelQuarticNumerator
        q (toRealData L) T =
      symmetricRoutedQuarticNumerator q H T (S.cutoff T) := by
  unfold IsometricKernel.mixedPairKernelQuarticNumerator
    symmetricRoutedQuarticNumerator
  apply QuarticTransfer.pairKernelQuarticNumerator_congr
  intro ρ hρ ρ' hρ'
  exact mixedPairKernel_canonical_eq_symmetricRoutedPairKernel
    L G H S T ρ ρ'


/-- Lower bound for the complete routed energy kernel, before replacing its
infinite frequency lattice by a finite routed grid. -/
structure RoutedEnergyQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (q : TrimmedMoment.Quartic)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L)) : Prop where
  block_dimension_pos :
    ∀ᶠ T in Filter.atTop, 0 < F.blockDim T
  zero_count_pos :
    ∀ᶠ T in Filter.atTop, 0 < Z.N T (2 * T)
  eventually_gt :
    ∀ x : ℝ,
      x < μ * QuarticTransfer.limitQuarticScore q μ p →
      ∀ᶠ T in Filter.atTop,
        x < routedEnergyQuarticNumerator q H T /
          (Z.N T (2 * T) : ℝ)

/-- A finite routed grid realizes the common cutoff selected only after the
complete quartic contraction has been formed. -/
structure DiagonalSymmetricFrequencyExhaustion
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (q : TrimmedMoment.Quartic)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    extends SymmetricFrequencyExhaustion H where
  cutoff_eq :
    ∀ T : ℝ, cutoff T = diagonalSymmetricCutoff q H h T

/-- The exponentially accurate diagonal cutoff transfers every strict
energy-kernel lower bound to the actual finite routed virtual statistic. -/
theorem RoutedEnergyQuarticLowerBound.toSelectedVirtual
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    {q : TrimmedMoment.Quartic}
    {H : RoutedFourierGrid G (canonicalAtomFactorization L)}
    {h : RoutedWindowRegularity H}
    (hE : RoutedEnergyQuarticLowerBound q H)
    (S : DiagonalSymmetricFrequencyExhaustion q H h) :
    SelectedVirtualQuarticLowerBound q
      (canonicalAtomFactorization L) := by
  refine ⟨hE.block_dimension_pos, ?_⟩
  intro x hx
  let y : ℝ :=
    (x + μ * QuarticTransfer.limitQuarticScore q μ p) / 2
  have hxy : x < y := by
    dsimp [y]
    linarith
  have hyTarget :
      y < μ * QuarticTransfer.limitQuarticScore q μ p := by
    dsimp [y]
    linarith
  have hgap : 0 < y - x := sub_pos.mpr hxy
  have hclose' :=
    (tendsto_diagonalSymmetricQuarticNumerator_sub_energy q H h).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hgap)
  have hclose :
      ∀ᶠ T in Filter.atTop,
        dist
            (symmetricRoutedQuarticNumerator q H T
                (diagonalSymmetricCutoff q H h T) -
              routedEnergyQuarticNumerator q H T)
            0 < y - x := by
    simpa only [Metric.mem_ball] using hclose'
  filter_upwards
      [hE.eventually_gt y hyTarget, hE.zero_count_pos, hclose] with
      T hEnergy hN hClose
  have hSelected :
      selectedVirtualQuarticNumerator q
          (canonicalAtomFactorization L) T =
        symmetricRoutedQuarticNumerator q H T
          (diagonalSymmetricCutoff q H h T) := by
    calc
      selectedVirtualQuarticNumerator q
          (canonicalAtomFactorization L) T =
          IsometricKernel.mixedPairKernelQuarticNumerator
            q (toRealData L) T :=
        selectedVirtualQuarticNumerator_canonical_eq_mixed q L T
      _ = symmetricRoutedQuarticNumerator q H T (S.cutoff T) :=
        mixedPairKernelQuarticNumerator_canonical_eq_symmetricRouted
          L G H S.toSymmetricFrequencyExhaustion T
      _ = symmetricRoutedQuarticNumerator q H T
          (diagonalSymmetricCutoff q H h T) := by
        rw [S.cutoff_eq]
  rw [hSelected]
  have hNreal : (0 : ℝ) < (Z.N T (2 * T) : ℝ) := by
    exact_mod_cast hN
  have hNone : (1 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hEnergy' :
      y * (Z.N T (2 * T) : ℝ) <
        routedEnergyQuarticNumerator q H T :=
    (lt_div_iff₀ hNreal).mp hEnergy
  have hClose' :
      |symmetricRoutedQuarticNumerator q H T
          (diagonalSymmetricCutoff q H h T) -
        routedEnergyQuarticNumerator q H T| < y - x := by
    simpa only [Real.dist_eq, sub_zero] using hClose
  have hLower :
      routedEnergyQuarticNumerator q H T - (y - x) <
        symmetricRoutedQuarticNumerator q H T
          (diagonalSymmetricCutoff q H h T) := by
    have hNeg :=
      neg_abs_le
        (symmetricRoutedQuarticNumerator q H T
            (diagonalSymmetricCutoff q H h T) -
          routedEnergyQuarticNumerator q H T)
    linarith
  have hProduct :
      0 ≤ (y - x) * ((Z.N T (2 * T) : ℝ) - 1) :=
    mul_nonneg (le_of_lt hgap) (sub_nonneg.mpr hNone)
  apply (lt_div_iff₀ hNreal).2
  nlinarith

/-- Direct terminal handoff: the complete routed energy lower bound supplies
the weighted isometric lower bound consumed by every frozen rung. -/
theorem RoutedEnergyQuarticLowerBound.toIsometric
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    {q : TrimmedMoment.Quartic}
    {H : RoutedFourierGrid G (canonicalAtomFactorization L)}
    {h : RoutedWindowRegularity H}
    (hE : RoutedEnergyQuarticLowerBound q H)
    (S : DiagonalSymmetricFrequencyExhaustion q H h) :
    IsometricBlock.WeightedQuarticLowerBound q (toIsometricData L) :=
  (hE.toSelectedVirtual S).toIsometric


/-- Exact identification of the summed routed-window energy with the literal
physical energy used by the hat normalization. -/
structure RoutedEnergyNormalization
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L)) : Prop where
  window_energy_eq :
    ∀ (T u : ℝ),
      (∑ r : ι, H.window T r u ^ 2) = F.windowEnergy T u

/-- Compact support and smoothness give integrability of every routed energy
Fourier integrand at every pair of complex frequencies. -/
theorem integrable_routedEnergyIntegrand
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (T : ℝ) (r : ι) (ρ ρ' : ℂ) :
    MeasureTheory.Integrable (fun u : ℝ =>
      (H.window T r u : ℂ) * H.window T r u *
        Complex.exp
          (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))) := by
  have hcontinuous :
      Continuous (fun u : ℝ =>
        (H.window T r u : ℂ) * H.window T r u *
          Complex.exp
            (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))) :=
    ((h.smooth T r).continuous.mul (h.smooth T r).continuous).mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))
  have hcompactWindow :
      HasCompactSupport (fun u : ℝ => (H.window T r u : ℂ)) := by
    refine HasCompactSupport.intro
      (K := Icc (-H.supportRadius T r) (H.supportRadius T r))
      isCompact_Icc ?_
    intro u hu
    have habs : H.supportRadius T r < |u| := by
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu
      · rw [abs_of_neg
          (lt_of_lt_of_le hu
            (neg_nonpos.mpr (h.supportRadius_nonneg T r)))]
        linarith
      · rw [abs_of_pos
          (lt_of_le_of_lt (h.supportRadius_nonneg T r) hu)]
        exact hu
    simp [h.support T r u habs]
  have hcompact :
      HasCompactSupport (fun u : ℝ =>
        (H.window T r u : ℂ) * H.window T r u *
          Complex.exp
            (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))) := by
    apply hcompactWindow.mono
    intro u hu
    change
      (H.window T r u : ℂ) * H.window T r u *
        Complex.exp
          (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) ≠ 0 at hu
    change (H.window T r u : ℂ) ≠ 0
    intro hzero
    apply hu
    simp [hzero]
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

/-- The complete physical window-energy Fourier kernel with the repository's
literal hat normalization left intact. -/
def physicalWindowEnergyPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) *
    (F.fullLength T : ℂ) *
      ∫ u : ℝ,
        (F.windowEnergy T u : ℂ) *
          Complex.exp
            (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))

/-- After the channel sum is formed, routed energy is exactly the literal
physical window-energy Fourier kernel. -/
theorem routedEnergyPairKernel_eq_physicalWindowEnergyPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Layout F ι} {G : RoutedGrid L}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L))
    (h : RoutedWindowRegularity H)
    (hE : RoutedEnergyNormalization H)
    (T : ℝ) (ρ ρ' : ℂ) :
    routedEnergyPairKernel H T ρ ρ' =
      physicalWindowEnergyPairKernel F T ρ ρ' := by
  unfold routedEnergyPairKernel physicalWindowEnergyPairKernel
  rw [← mul_assoc]
  apply congrArg
    (fun w : ℂ => ((F.hatDenominator T)⁻¹ : ℂ) * w)
  rw [← Finset.mul_sum]
  apply congrArg (fun w : ℂ => (F.fullLength T : ℂ) * w)
  let f : ι → ℝ → ℂ := fun r u =>
    (H.window T r u : ℂ) * H.window T r u *
      Complex.exp
        (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))
  have hInt : ∀ r : ι, MeasureTheory.Integrable (f r) := by
    intro r
    exact integrable_routedEnergyIntegrand H h T r ρ ρ'
  calc
    (∑ r : ι, ∫ u : ℝ, f r u) =
        ∫ u : ℝ, ∑ r : ι, f r u := by
      symm
      simpa using
        (MeasureTheory.integral_finset_sum
          (Finset.univ : Finset ι)
          (fun r _ => hInt r))
    _ = ∫ u : ℝ,
        (F.windowEnergy T u : ℂ) *
          Complex.exp
            (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with u
      have hcast :=
        congrArg (fun x : ℝ => (x : ℂ)) (hE.window_energy_eq T u)
      push_cast at hcast
      rw [← hcast, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      dsimp [f]
      push_cast
      ring


/-- Literal normalized Fourier transform of the total physical window energy. -/
def normalizedPhysicalWindowEnergyPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((∫ u : ℝ, F.windowEnergy T u : ℂ)⁻¹) *
    ∫ u : ℝ,
      (F.windowEnergy T u : ℂ) *
        Complex.exp
          (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))

/-- Once the two literal normalization factors are nonzero, the full support
length cancels exactly and the routed energy kernel is the normalized Fourier
transform of total physical energy. -/
theorem physicalWindowEnergyPairKernel_eq_normalized
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ)
    (hfull : F.fullLength T ≠ 0)
    (hmass : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (ρ ρ' : ℂ) :
    physicalWindowEnergyPairKernel F T ρ ρ' =
      normalizedPhysicalWindowEnergyPairKernel F T ρ ρ' := by
  unfold physicalWindowEnergyPairKernel
    normalizedPhysicalWindowEnergyPairKernel
    QuarticGramFamily.hatDenominator
  have hfullC : (F.fullLength T : ℂ) ≠ 0 := by
    exact_mod_cast hfull
  have hmassC :
      (∫ u : ℝ, F.windowEnergy T u : ℂ) ≠ 0 := by
    exact_mod_cast hmass
  push_cast
  field_simp [hfullC, hmassC]


/-! ## Frozen-profile handoff through both post-contraction diagonals -/

/-- Exact realization of total physical window energy by the annular stage
selected only after the complete quartic zero contraction has been formed. -/
structure DiagonalAnnularWindowEnergyRealization
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (q : TrimmedMoment.Quartic)
    (L : ℝ → ℝ) (hL : ∀ T, 0 < L T)
    (hv : ContDiff ℝ ∞ v)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (hmass :
      ∀ T : ℝ,
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / L T)) ≠ 0) :
    Prop where
  stage : ℝ → ℕ
  window_energy_eq :
    ∀ (T u : ℝ),
      F.windowEnergy T u =
        SmoothRadialShell.shrinkingProfileShellWindow
          v (L T) (stage T) (hL T) u ^ 2
  stage_eq :
    ∀ T : ℝ,
      stage T =
        SmoothRadialShell.diagonalAnnularProfileStage
          q F v L hL hv hposProfile hmass T
  full_length_ne :
    ∀ᶠ T in Filter.atTop, F.fullLength T ≠ 0
  window_energy_mass_ne :
    ∀ᶠ T in Filter.atTop,
      (∫ u : ℝ, F.windowEnergy T u) ≠ 0

/-- The only lower bound left after both diagonal selections: the complete
zero contraction of the literal frozen supported profile. -/
structure SupportedProfileQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : TrimmedMoment.Quartic)
    (F : QuarticGramFamily Z σ μ p v)
    (L : ℝ → ℝ) : Prop where
  block_dimension_pos :
    ∀ᶠ T in Filter.atTop, 0 < F.blockDim T
  zero_count_pos :
    ∀ᶠ T in Filter.atTop, 0 < Z.N T (2 * T)
  eventually_gt :
    ∀ x : ℝ,
      x < μ * QuarticTransfer.limitQuarticScore q μ p →
      ∀ᶠ T in Filter.atTop,
        x <
          SmoothRadialShell.supportedProfileNormalizedQuarticNumerator
            q F v L T / (Z.N T (2 * T) : ℝ)

/-- Under exact annular energy realization, the routed energy numerator is
literally the normalized annular numerator at the realized stage. -/
theorem routedEnergyQuarticNumerator_eq_shrinkingAnnular
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Lyt : Layout F ι} {G : RoutedGrid Lyt}
    {q : TrimmedMoment.Quartic}
    {H : RoutedFourierGrid G (canonicalAtomFactorization Lyt)}
    (hH : RoutedWindowRegularity H)
    (hEnergy : RoutedEnergyNormalization H)
    {period : ℝ → ℝ} {hperiod : ∀ T, 0 < period T}
    {hv : ContDiff ℝ ∞ v}
    {hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x}
    {hmass :
      ∀ T : ℝ,
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / period T)) ≠ 0}
    (R : DiagonalAnnularWindowEnergyRealization
      F q period hperiod hv hposProfile hmass)
    (T : ℝ)
    (hfull : F.fullLength T ≠ 0)
    (hphysicalMass : (∫ u : ℝ, F.windowEnergy T u) ≠ 0) :
    routedEnergyQuarticNumerator q H T =
      SmoothRadialShell.shrinkingAnnularNormalizedQuarticNumerator
        q F v period hperiod T (R.stage T) := by
  unfold routedEnergyQuarticNumerator
    SmoothRadialShell.shrinkingAnnularNormalizedQuarticNumerator
  apply QuarticTransfer.pairKernelQuarticNumerator_congr
  intro ρ hρ ρ' hρ'
  calc
    routedEnergyPairKernel H T ρ ρ' =
        physicalWindowEnergyPairKernel F T ρ ρ' :=
      routedEnergyPairKernel_eq_physicalWindowEnergyPairKernel
        H hH hEnergy T ρ ρ'
    _ = normalizedPhysicalWindowEnergyPairKernel F T ρ ρ' :=
      physicalWindowEnergyPairKernel_eq_normalized
        F T hfull hphysicalMass ρ ρ'
    _ = SmoothRadialShell.shrinkingProfileShellNormalizedPairKernel
        v (period T) (R.stage T) (hperiod T) ρ ρ' := by
      unfold normalizedPhysicalWindowEnergyPairKernel
        SmoothRadialShell.shrinkingProfileShellNormalizedPairKernel
      simp_rw [R.window_energy_eq T]

/-- The annular post-contraction diagonal transfers a frozen-profile lower
bound to the complete routed energy kernel. -/
theorem SupportedProfileQuarticLowerBound.toRoutedEnergy
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Lyt : Layout F ι} {G : RoutedGrid Lyt}
    {q : TrimmedMoment.Quartic}
    {H : RoutedFourierGrid G (canonicalAtomFactorization Lyt)}
    {hH : RoutedWindowRegularity H}
    {hEnergy : RoutedEnergyNormalization H}
    {period : ℝ → ℝ} {hperiod : ∀ T, 0 < period T}
    {hv : ContDiff ℝ ∞ v}
    {hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x}
    {hmass :
      ∀ T : ℝ,
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / period T)) ≠ 0}
    (hProfile : SupportedProfileQuarticLowerBound q F period)
    (R : DiagonalAnnularWindowEnergyRealization
      F q period hperiod hv hposProfile hmass) :
    RoutedEnergyQuarticLowerBound q H := by
  refine
    { block_dimension_pos := hProfile.block_dimension_pos
      zero_count_pos := hProfile.zero_count_pos
      eventually_gt := ?_ }
  intro x hx
  let y : ℝ :=
    (x + μ * QuarticTransfer.limitQuarticScore q μ p) / 2
  have hxy : x < y := by
    dsimp [y]
    linarith
  have hyTarget :
      y < μ * QuarticTransfer.limitQuarticScore q μ p := by
    dsimp [y]
    linarith
  have hgap : 0 < y - x := sub_pos.mpr hxy
  have hclose' :=
    (SmoothRadialShell
      .tendsto_diagonalAnnularNormalizedQuarticNumerator_sub_profile
        q F v period hperiod hv hposProfile hmass).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hgap)
  have hclose :
      ∀ᶠ T in Filter.atTop,
        dist
            (SmoothRadialShell
                .shrinkingAnnularNormalizedQuarticNumerator
                  q F v period hperiod T
                    (SmoothRadialShell.diagonalAnnularProfileStage
                      q F v period hperiod hv hposProfile hmass T) -
              SmoothRadialShell
                .supportedProfileNormalizedQuarticNumerator
                  q F v period T)
            0 < y - x := by
    simpa only [Metric.mem_ball] using hclose'
  filter_upwards
      [hProfile.eventually_gt y hyTarget,
        hProfile.zero_count_pos,
        R.full_length_ne,
        R.window_energy_mass_ne,
        hclose] with
      T hFrozen hN hfull hphysicalMass hClose
  have hExact :
      routedEnergyQuarticNumerator q H T =
        SmoothRadialShell.shrinkingAnnularNormalizedQuarticNumerator
          q F v period hperiod T
            (SmoothRadialShell.diagonalAnnularProfileStage
              q F v period hperiod hv hposProfile hmass T) := by
    rw [routedEnergyQuarticNumerator_eq_shrinkingAnnular
      hH hEnergy R T hfull hphysicalMass, R.stage_eq T]
  rw [hExact]
  have hNreal : (0 : ℝ) < (Z.N T (2 * T) : ℝ) := by
    exact_mod_cast hN
  have hNone : (1 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hFrozen' :
      y * (Z.N T (2 * T) : ℝ) <
        SmoothRadialShell.supportedProfileNormalizedQuarticNumerator
          q F v period T :=
    (lt_div_iff₀ hNreal).mp hFrozen
  have hClose' :
      |SmoothRadialShell.shrinkingAnnularNormalizedQuarticNumerator
            q F v period hperiod T
              (SmoothRadialShell.diagonalAnnularProfileStage
                q F v period hperiod hv hposProfile hmass T) -
          SmoothRadialShell.supportedProfileNormalizedQuarticNumerator
            q F v period T| < y - x := by
    simpa only [Real.dist_eq, sub_zero] using hClose
  have hLower :
      SmoothRadialShell.supportedProfileNormalizedQuarticNumerator
            q F v period T - (y - x) <
        SmoothRadialShell.shrinkingAnnularNormalizedQuarticNumerator
          q F v period hperiod T
            (SmoothRadialShell.diagonalAnnularProfileStage
              q F v period hperiod hv hposProfile hmass T) := by
    have hNeg :=
      neg_abs_le
        (SmoothRadialShell.shrinkingAnnularNormalizedQuarticNumerator
            q F v period hperiod T
              (SmoothRadialShell.diagonalAnnularProfileStage
                q F v period hperiod hv hposProfile hmass T) -
          SmoothRadialShell.supportedProfileNormalizedQuarticNumerator
            q F v period T)
    linarith
  have hProduct :
      0 ≤ (y - x) * ((Z.N T (2 * T) : ℝ) - 1) :=
    mul_nonneg (le_of_lt hgap) (sub_nonneg.mpr hNone)
  apply (lt_div_iff₀ hNreal).2
  nlinarith

/-- Both diagonal selections compose directly into the weighted isometric
lower bound consumed by every frozen rung. -/
theorem SupportedProfileQuarticLowerBound.toIsometric
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Lyt : Layout F ι} {G : RoutedGrid Lyt}
    {q : TrimmedMoment.Quartic}
    {H : RoutedFourierGrid G (canonicalAtomFactorization Lyt)}
    {hH : RoutedWindowRegularity H}
    {hEnergy : RoutedEnergyNormalization H}
    {period : ℝ → ℝ} {hperiod : ∀ T, 0 < period T}
    {hv : ContDiff ℝ ∞ v}
    {hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x}
    {hmass :
      ∀ T : ℝ,
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / period T)) ≠ 0}
    (hProfile : SupportedProfileQuarticLowerBound q F period)
    (R : DiagonalAnnularWindowEnergyRealization
      F q period hperiod hv hposProfile hmass)
    (S : DiagonalSymmetricFrequencyExhaustion q H hH) :
    IsometricBlock.WeightedQuarticLowerBound
      q (toIsometricData Lyt) :=
  ((hProfile.toRoutedEnergy R).toSelectedVirtual S).toIsometric

end AlignedIsometricLayout
end Zeta85
end RH

end