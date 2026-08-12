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
open scoped ComplexOrder

noncomputable section

namespace RH.Zeta85.BlockDensity

open Zeta23

/-- The canonical integral size of a block occupying density `μ` of the
dyadic zero count. -/
def floorBlockDim (Z : ZeroConfig) (μ T : ℝ) : ℕ :=
  ⌊μ * (Z.N T (2 * T) : ℝ)⌋₊

/-- The requested floor density, capped only when the ambient family is too
small. -/
def cappedBlockDim
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℕ :=
  min (floorBlockDim Z μ T) (F.dim T)

/-- Replace only the nested principal compression of a Gram family by the
first available coordinates, up to `⌊μ N(T,2T)⌋`.  The ambient matrix,
physical windows, and all error terms are unchanged. -/
def reblock
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) :
    QuarticGramFamily Z σ μ p v :=
  { F with
    blockDim := cappedBlockDim F
    blockEmbedding := fun _T => Fin.castLEEmb (Nat.min_le_right _ _) }

@[simp] theorem reblock_blockDim
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    (reblock F).blockDim T = cappedBlockDim F T := rfl

@[simp] theorem reblock_dim
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    (reblock F).dim T = F.dim T := rfl

@[simp] theorem reblock_pTraceError
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    (reblock F).pTraceError T = F.pTraceError T := rfl

@[simp] theorem reblock_traceError
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    (reblock F).traceError T = F.traceError T := rfl

@[simp] theorem reblock_frobError
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    (reblock F).frobError T = F.frobError T := rfl

@[simp] theorem reblock_A
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    (reblock F).A T = F.A T := rfl

@[simp] theorem reblock_P
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    (reblock F).P T = F.P T := rfl

@[simp] theorem reblock_Q
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    (reblock F).Q T = F.Q T := rfl

/-- A Hermitian `d × d` matrix cannot have trace squared larger than `d`
times its squared Frobenius norm. -/
theorem rtrace_sq_le_dim_mul_frobSq {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    RHLinalg.rtrace A ^ 2 ≤ (d : ℝ) * RHLinalg.frobSq A := by
  rw [RHLinalg.rtrace_eq_sum_eigenvalues hA,
    RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hA]
  simpa using (sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := hA.eigenvalues))

/-- The trace and Frobenius limits force the ambient matrix to contain every
block whose requested density stays below the explicit Cauchy--Schwarz
capacity. -/
theorem eventually_floorBlockDim_le_dim
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hRvM : RiemannVonMangoldt Z) (hμ : 0 < μ)
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (Dbar : ℝ) (hcost : profileSaturatedCost σ v ≤ Dbar)
    (hmargin : μ * (Dbar + 1 / 10) < (9 / 10 : ℝ) ^ 2) :
    ∀ᶠ T in atTop, floorBlockDim Z μ T ≤ F.dim T := by
  have hNpos := (Assembly.tendsto_N_atTop Z hRvM).eventually_gt_atTop 0
  have htraceErr := hfull.trace_small.def (by norm_num : (0 : ℝ) < 1 / 10)
  have hfrobErr := hfull.frob_small.def (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [hNpos, hfull.trace_bound, hfull.frob_bound,
    htraceErr, hfrobErr] with T hN htrace hfrob htraceErrT hfrobErrT
  let N : ℝ := Z.N T (2 * T)
  let d : ℝ := F.dim T
  let tr : ℝ := RHLinalg.rtrace (F.A T)
  let fr : ℝ := RHLinalg.frobSq (F.A T)
  have htraceErrAbs : |F.traceError T| ≤ (1 / 10 : ℝ) * N := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hN.le] using htraceErrT
  have hfrobErrAbs : |F.frobError T| ≤ (1 / 10 : ℝ) * N := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hN.le] using hfrobErrT
  have htrace' : |tr - N| ≤ F.traceError T := by
    simpa only [tr, N] using htrace
  have hfrob' : fr ≤ profileSaturatedCost σ v * N + F.frobError T := by
    simpa only [fr, N] using hfrob
  have htrLower : (9 / 10 : ℝ) * N ≤ tr := by
    have hneg := (abs_le.mp htrace').1
    have herr : F.traceError T ≤ (1 / 10 : ℝ) * N :=
      (le_abs_self _).trans htraceErrAbs
    linarith
  have hfrUpper : fr ≤ (Dbar + 1 / 10) * N := by
    have hcostN := mul_le_mul_of_nonneg_right hcost hN.le
    have herr : F.frobError T ≤ (1 / 10 : ℝ) * N :=
      (le_abs_self _).trans hfrobErrAbs
    nlinarith
  have hA : (F.A T).IsHermitian := by
    rw [hzero.truncated_decomposition T]
    exact (hzero.p_psd T).isHermitian.add (hzero.q_hermitian T)
  have hCS : tr ^ 2 ≤ d * fr := by
    simpa only [tr, d, fr] using
      rtrace_sq_le_dim_mul_frobSq (F.A T) hA
  have hfr0 : 0 ≤ fr := by
    exact Assembly.frobSq_nonneg _
  have hd0 : 0 ≤ d := by positivity
  have htrSq : ((9 / 10 : ℝ) * N) ^ 2 ≤ tr ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hN.le) htrLower 2
  have hmuNd : μ * N ≤ d := by
    by_contra hnot
    have hdlt : d < μ * N := lt_of_not_ge hnot
    have hdfr₁ : d * fr ≤ (μ * N) * fr :=
      mul_le_mul_of_nonneg_right hdlt.le hfr0
    have hdfr₂ : (μ * N) * fr ≤ (μ * N) * ((Dbar + 1 / 10) * N) :=
      mul_le_mul_of_nonneg_left hfrUpper (mul_nonneg hμ.le hN.le)
    have hdfr : d * fr ≤ (μ * N) * ((Dbar + 1 / 10) * N) :=
      hdfr₁.trans hdfr₂
    have hmarginN := mul_lt_mul_of_pos_right hmargin (sq_pos_of_pos hN)
    have hupper : d * fr < ((9 / 10 : ℝ) * N) ^ 2 := by
      calc
        d * fr ≤ (μ * N) * ((Dbar + 1 / 10) * N) := hdfr
        _ = (μ * (Dbar + 1 / 10)) * N ^ 2 := by ring
        _ < ((9 / 10 : ℝ) ^ 2) * N ^ 2 := hmarginN
        _ = ((9 / 10 : ℝ) * N) ^ 2 := by ring
    linarith
  have hfloor : (floorBlockDim Z μ T : ℝ) ≤ μ * N := by
    simpa only [floorBlockDim, N] using
      (Nat.floor_le (mul_nonneg hμ.le hN.le))
  have hfinal : (floorBlockDim Z μ T : ℝ) ≤ (F.dim T : ℝ) := by
    simpa only [d] using hfloor.trans hmuNd
  exact_mod_cast hfinal

/-- Riemann--von Mangoldt turns the exact floor construction into the density
limit consumed by every frozen quartic rung. -/
theorem reblock_densityLimit
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (hRvM : RiemannVonMangoldt Z) (hμ : 0 < μ)
    (F : QuarticGramFamily Z σ μ p v)
    (hfit : ∀ᶠ T in atTop, floorBlockDim Z μ T ≤ F.dim T) :
    BlockDensityLimit (reblock F) where
  bandwidth_pos := hμ
  block_dimension := by
    have hfloor : Tendsto
        (fun x : ℝ => (⌊μ * x⌋₊ : ℝ) / x) atTop (nhds μ) :=
      tendsto_nat_floor_mul_div_atTop hμ.le
    have hlimit := hfloor.comp (Assembly.tendsto_N_atTop Z hRvM)
    apply hlimit.congr'
    filter_upwards [hfit] with T hT
    have hT' : ⌊μ * (Z.N T (2 * T) : ℝ)⌋₊ ≤ F.dim T := by
      simpa only [floorBlockDim] using hT
    simp only [Function.comp_apply, reblock_blockDim, cappedBlockDim,
      floorBlockDim, Nat.min_eq_left hT']

/-- The canonical reblocking therefore discharges its density interface from
the ambient trace and zero-side packages alone. -/
theorem reblock_densityLimit_of_trace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (hRvM : RiemannVonMangoldt Z) (hμ : 0 < μ)
    (F : QuarticGramFamily Z σ μ p v)
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (Dbar : ℝ) (hcost : profileSaturatedCost σ v ≤ Dbar)
    (hmargin : μ * (Dbar + 1 / 10) < (9 / 10 : ℝ) ^ 2) :
    BlockDensityLimit (reblock F) :=
  reblock_densityLimit hRvM hμ F
    (eventually_floorBlockDim_le_dim hRvM hμ hfull hzero Dbar hcost hmargin)

/-- Exact support-`1.9999` specialization used by R-9506 and R-9383. -/
theorem reblock_densityLimit_9506
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family19999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F) :
    BlockDensityLimit (reblock F) := by
  apply reblock_densityLimit_of_trace hRvM (by norm_num) F hfull hzero
    (106772567 / 100000000)
  · rw [profileSaturatedCost_v9506]
    exact QuarticWindowWitnesses.D9506_lt.le
  · norm_num

/-- Exact support-`1.4999` specialization used by R-8686 and R-8657. -/
theorem reblock_densityLimit_8686
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family14999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F) :
    BlockDensityLimit (reblock F) := by
  apply reblock_densityLimit_of_trace hRvM (by norm_num) F hfull hzero
    (113434643 / 100000000)
  · rw [profileSaturatedCost_v8686]
    exact QuarticWindowWitnesses.D8686_lt.le
  · norm_num

end RH.Zeta85.BlockDensity

end
