/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Inputs95

/-!
# Isometric block architecture

The frozen coordinate-block interface is allocation-inconsistent.  The finite
stability theorem, however, already works for every isometric compression.
This file exposes that strictly more flexible block object and proves that it
inherits the identical robust tail bound.
-/

open Filter Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace RH
namespace Zeta85
namespace IsometricBlock

open Zeta23 RHLinalg RobustStability

/-- A height-dependent isometry from a smaller block space into the complete
physical channel-column space.  Its columns may mix channels. -/
structure Data
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) where
  compression :
    ∀ T : ℝ, Matrix (Fin (F.dim T)) (Fin (F.blockDim T)) ℂ
  isometry :
    ∀ T : ℝ, (compression T)ᴴ * compression T = 1

/-- Compression of the literal enlarged-window matrix by the chosen
isometry. -/
def block
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F) (T : ℝ) :
    Matrix (Fin (F.blockDim T)) (Fin (F.blockDim T)) ℂ :=
  (C.compression T)ᴴ * F.A T * C.compression T

/-- The isometrically compressed block is Hermitian under the same literal
zero-side decomposition used by the coordinate block. -/
theorem block_isHermitian
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F) (hzero : StableZeroSide F) (T : ℝ) :
    (block C T).IsHermitian := by
  rw [block, hzero.truncated_decomposition T]
  exact isHermitian_conjTranspose_mul_mul
    (C.compression T)
    ((hzero.p_psd T).isHermitian.add (hzero.q_hermitian T))

/-- Centered spectral moment of the mixed-channel block. -/
def centeredMoment
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F) (k : ℕ) (T : ℝ) : ℝ :=
  rtrace ((block C T - 1) ^ k) / (F.blockDim T : ℝ)

/-- The exact robust stability inequality survives the mixed-channel block,
with precisely the same finite error budget as the coordinate block. -/
theorem robustTailBound_eventually
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F)
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F) :
    ∀ᶠ T in Filter.atTop,
      tailExcessSq (block_isHermitian C hzero T)
          (Z.s2 T + Z.p T) ≤
        (Z.s1 T : ℝ) -
          (2 - profileSaturatedCost σ v) *
            (Z.N T (2 * T) : ℝ) +
          2 * F.pTraceError T + 4 * F.traceError T +
            F.frobError T + 2 * (Assembly.NII Z T : ℝ) := by
  filter_upwards [hzero.simple_rank_bound, hzero.simple_trace_cap,
    hzero.bad_index_bound, hfull.trace_bound, hfull.frob_bound,
    eventually_ge_atTop (0 : ℝ)] with
      T hrank htraceP hposQ htraceA hfrobA hT
  have htraceA' :
      |rtrace (F.P T + F.Q T) -
          (Z.N T (2 * T) : ℝ)| ≤ F.traceError T := by
    simpa only [← hzero.truncated_decomposition T] using htraceA
  have hfrobA' :
      frobSq (F.P T + F.Q T) ≤
        profileSaturatedCost σ v *
          (Z.N T (2 * T) : ℝ) + F.frobError T := by
    simpa only [← hzero.truncated_decomposition T] using hfrobA
  have hrob :=
    RobustStability.robust_stability_inequality_isometricCompression_withCountError
      (hzero.p_psd T) (hzero.q_hermitian T)
      (C.compression T) (C.isometry T)
      hrank htraceP hposQ
      (core_count_le_dyadic_add_edge Z hT)
      htraceA' hfrobA'
  have hblock :
      block C T =
        (C.compression T)ᴴ * (F.P T + F.Q T) *
          C.compression T := by
    rw [block, hzero.truncated_decomposition T]
  rw [tailExcessSq_congr hblock
    (block_isHermitian C hzero T)
    (isHermitian_conjTranspose_mul_mul
      (C.compression T)
      ((hzero.p_psd T).isHermitian.add
        (hzero.q_hermitian T)))]
  exact hrob

end IsometricBlock
end Zeta85
end RH

end
