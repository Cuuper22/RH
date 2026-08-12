/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Inputs95
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Canonical density blocks

The quartic transfer only needs a literal principal compression whose size is
asymptotic to `μ N(T,2T)`.  This file makes that indexing choice exact: take
the natural floor of `μ N(T,2T)` and embed those coordinates into the ambient
family.  The floor error disappears because the zero count tends to infinity.
-/

open Filter Topology

noncomputable section

namespace RH.Zeta85.BlockDensity

open Zeta23

/-- The canonical integral size of a block occupying density `μ` of the
dyadic zero count. -/
def floorBlockDim (Z : ZeroConfig) (μ T : ℝ) : ℕ :=
  ⌊μ * (Z.N T (2 * T) : ℝ)⌋₊

/-- Replace only the nested principal compression of a Gram family by the
first `⌊μ N(T,2T)⌋` coordinates.  The ambient matrix, physical windows, and
all error terms are unchanged. -/
def reblock
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) :
    QuarticGramFamily Z σ μ p v :=
  { F with
    blockDim := floorBlockDim Z μ
    blockEmbedding := fun T => Fin.castLEEmb (hfit T) }

@[simp] theorem reblock_blockDim
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) (T : ℝ) :
    (reblock F hfit).blockDim T = floorBlockDim Z μ T := rfl

@[simp] theorem reblock_dim
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) (T : ℝ) :
    (reblock F hfit).dim T = F.dim T := rfl

@[simp] theorem reblock_pTraceError
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) (T : ℝ) :
    (reblock F hfit).pTraceError T = F.pTraceError T := rfl

@[simp] theorem reblock_traceError
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) (T : ℝ) :
    (reblock F hfit).traceError T = F.traceError T := rfl

@[simp] theorem reblock_frobError
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) (T : ℝ) :
    (reblock F hfit).frobError T = F.frobError T := rfl

@[simp] theorem reblock_A
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) (T : ℝ) :
    (reblock F hfit).A T = F.A T := rfl

@[simp] theorem reblock_P
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) (T : ℝ) :
    (reblock F hfit).P T = F.P T := rfl

@[simp] theorem reblock_Q
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) (T : ℝ) :
    (reblock F hfit).Q T = F.Q T := rfl

/-- Riemann--von Mangoldt turns the exact floor construction into the density
limit consumed by every frozen quartic rung. -/
theorem reblock_densityLimit
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (hRvM : RiemannVonMangoldt Z) (hμ : 0 < μ)
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ T, floorBlockDim Z μ T ≤ F.dim T) :
    BlockDensityLimit (reblock F hfit) where
  bandwidth_pos := hμ
  block_dimension := by
    have hfloor : Tendsto
        (fun x : ℝ => (⌊μ * x⌋₊ : ℝ) / x) atTop (nhds μ) :=
      tendsto_nat_floor_mul_div_atTop hμ.le
    change Tendsto
      ((fun x : ℝ => (⌊μ * x⌋₊ : ℝ) / x) ∘
        fun T => (Z.N T (2 * T) : ℝ)) atTop (nhds μ)
    exact hfloor.comp (Assembly.tendsto_N_atTop Z hRvM)

end RH.Zeta85.BlockDensity

end
