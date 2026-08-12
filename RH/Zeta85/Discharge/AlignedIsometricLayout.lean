/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RepeatedChannelCompression

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

end AlignedIsometricLayout
end Zeta85
end RH

end
