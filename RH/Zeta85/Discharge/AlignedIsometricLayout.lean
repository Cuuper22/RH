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
  rw [Equiv.sum_comp (L.rowEquiv T)
    (fun jk =>
      star (routedMatrix L.frame (L.selected T) jk a) *
        routedMatrix L.frame (L.selected T) jk b)]
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
  rw [Equiv.sum_comp (L.rowEquiv T)
    (fun jk =>
      routedMatrix L.frame (L.selected T) jk a *
        physicalAtom L.frame
          (fun r k => A.virtualAtom T r k ρ) jk)]
  exact recover_routed_virtual_atom
    L.frame (L.selected T)
      (fun r k => A.virtualAtom T r k ρ) a

end AlignedIsometricLayout
end Zeta85
end RH

end
