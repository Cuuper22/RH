/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSPairIntegrals
import RH.Zeta85.Discharge.QuarticTransfer
import Zeta23.Poisson.ComplexDecay
import Zeta23.Poisson.Complex

/-!
# Actual-block centering bridge for the Rudnick--Sarnak route

The published Rudnick--Sarnak main term and the contraction calculations are
naturally uncentered, whereas `BlockMomentLimits` is stated for the centered
principal-block traces.  This file proves the finite binomial centering and
passes it through limits through degree four.

It does not prove any analytic passage from the actual block to the cyclic
main term.  That passage is retained verbatim in `UncenteredRSBlockLimits`,
together with eventual positivity of the block dimension.  The complex
Poisson clauses remain separate hypotheses of the final constructor.
-/

open Filter Matrix MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace RH.Zeta85.RSBlockMomentBridge

open Zeta23 RHLinalg RSReduction

/-- Normalized uncentered trace moment of the literal distinguished block. -/
def uncenteredBlockMoment {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (k : ℕ) (T : ℝ) : ℝ :=
  rtrace ((F.block T) ^ k) / (F.blockDim T : ℝ)

/-- The exact analytic remainder after the cyclic contractions have been
evaluated: the actual uncentered block moments converge to formula (27).

This predicate deliberately does not include complex Poisson summability or
cancellation, which are independent fields of `BlockMomentLimits`. -/
structure UncenteredRSBlockLimits {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  moments : ∀ k : ℕ, k ≤ 4 →
    Tendsto (uncenteredBlockMoment F k) atTop
      (nhds (uncenteredContractionMoment (topHatR3Terms p) μ k))

private theorem rtrace_one_fin {d : ℕ} :
    rtrace (1 : Matrix (Fin d) (Fin d) ℂ) = d := by
  simp [rtrace, Matrix.trace]

/-- At every positive block dimension, finite matrix centering is exactly the
scalar binomial transform used in formula (28). -/
theorem centeredBlockMoment_eq_centeredTransform
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (k : ℕ) (hk : k ≤ 4) :
    F.centeredBlockMoment k T =
      centeredTransform (fun a => uncenteredBlockMoment F a T) k := by
  simp only [QuarticGramFamily.centeredBlockMoment, centeredTransform,
    uncenteredBlockMoment]
  interval_cases k
  · simp
  · rw [show (F.block T - 1) ^ 1 = F.block T ^ 1 - 1 by noncomm_ring,
      rtrace_sub]
    norm_num [Finset.sum_range_succ, Nat.choose, rtrace_one_fin]
    ring
  · rw [show (F.block T - 1) ^ 2 =
        F.block T ^ 2 - (F.block T + F.block T) + 1 by noncomm_ring,
      rtrace_add, rtrace_sub, rtrace_add]
    norm_num [Finset.sum_range_succ, Nat.choose, rtrace_one_fin]
    ring
  · rw [show (F.block T - 1) ^ 3 =
        F.block T ^ 3 -
          (F.block T ^ 2 + F.block T ^ 2 + F.block T ^ 2) +
          (F.block T + F.block T + F.block T) - 1 by noncomm_ring,
      rtrace_sub, rtrace_add, rtrace_sub, rtrace_add, rtrace_add,
      rtrace_add, rtrace_add]
    norm_num [Finset.sum_range_succ, Nat.choose, rtrace_one_fin]
    ring
  · rw [show (F.block T - 1) ^ 4 =
        F.block T ^ 4 -
          (F.block T ^ 3 + F.block T ^ 3 + F.block T ^ 3 + F.block T ^ 3) +
          (F.block T ^ 2 + F.block T ^ 2 + F.block T ^ 2 +
            F.block T ^ 2 + F.block T ^ 2 + F.block T ^ 2) -
          (F.block T + F.block T + F.block T + F.block T) + 1 by noncomm_ring,
      rtrace_add, rtrace_sub, rtrace_add, rtrace_sub, rtrace_add,
      rtrace_add, rtrace_add, rtrace_add, rtrace_add, rtrace_add,
      rtrace_add, rtrace_add, rtrace_add, rtrace_add]
    norm_num [Finset.sum_range_succ, Nat.choose, rtrace_one_fin, rtrace_add]
    ring

/-- The uncentered formula-(27) limits imply all centered formula-(21)
limits.  This is the formal finite-sum/Tendsto step; no RS, Poisson, height,
or finite-grid estimate is hidden in the proof. -/
theorem centered_moment_limits_of_fillBounds
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hp : 0 < p) (hp1 : p ≤ 1) (hraw : UncenteredRSBlockLimits F) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      Tendsto (F.centeredBlockMoment k) atTop
        (nhds (formula21Moment k μ p)) := by
  intro k hk1 hk4
  have hcenter : ∀ T,
      F.centeredBlockMoment k T =
        centeredTransform (fun a => uncenteredBlockMoment F a T) k := by
    intro T
    exact centeredBlockMoment_eq_centeredTransform F T k hk4
  rw [funext hcenter]
  have hlim : Tendsto
      (fun T => centeredTransform (fun a => uncenteredBlockMoment F a T) k)
      atTop
      (nhds (centeredTransform
        (uncenteredContractionMoment (topHatR3Terms p) μ) k)) := by
    unfold centeredTransform
    apply tendsto_finsetSum
    intro a ha
    exact (hraw.moments a
      (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp ha)) hk4)).const_mul _
  rw [topHat_centeredContraction_eq_formula21
    hp hp1 k hk1 hk4] at hlim
  exact hlim

/-- Compatibility wrapper for the older physical-window interface. -/
theorem centered_moment_limits
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hr1a : PrincipalCyclicBlock F) (hraw : UncenteredRSBlockLimits F) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      Tendsto (F.centeredBlockMoment k) atTop
        (nhds (formula21Moment k μ p)) :=
  centered_moment_limits_of_fillBounds
    hr1a.fill_pos hr1a.fill_le_one hraw

/-- The minimal RS route to the sum-first terminal premise.  It uses only
the literal block-density limit, the scalar fill bounds, and the uncentered
actual-block moment limits; no alias or physical-window fields enter. -/
theorem quarticTraceLowerBound_of_uncenteredRS
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hdim : BlockDimensionLimit F) (hraw : UncenteredRSBlockLimits F)
    (q : Quartic) :
    QuarticTransfer.FactoredZeroKernelQuarticLowerBound q F := by
  have hmom : BlockMomentConvergence F :=
    ⟨centered_moment_limits_of_fillBounds hp hp1 hraw⟩
  have hscore : QuarticTransfer.QuarticScoreConvergence q F :=
    QuarticTransfer.quarticScoreConvergence_of_moments hmom q
  exact
    (QuarticTransfer.weightedQuarticLimit_of_separate hdim hscore).toLowerBound.toTraceLowerBound.toUncentered.toCyclic.toZeroCyclic.toTuple.toKernel.toFactored

/-- Constructor for the existing R1b interface from the exact uncentered
actual-block limit plus the two independent complex-Poisson clauses. -/
theorem blockMomentLimits_of_uncenteredRS
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hr1a : PrincipalCyclicBlock F)
    (haliasSummable : ∀ᶠ T in atTop,
      ∀ ρ ∈ Z.ZIprime T, ∀ ρ' ∈ Z.ZIprime T,
        Summable (F.complexAliasFamily T (gammaOf ρ) (gammaOf ρ')))
    (haliasZero : ∀ᶠ T in atTop,
      ∀ ρ ∈ Z.ZIprime T, ∀ ρ' ∈ Z.ZIprime T,
        ∑' a, F.complexAliasFamily T (gammaOf ρ) (gammaOf ρ') a = 0)
    (hraw : UncenteredRSBlockLimits F) :
    BlockMomentLimits F where
  complex_aliases_summable_at_zeros := haliasSummable
  offRH_complex_poisson_at_zeros := haliasZero
  moments := centered_moment_limits hr1a hraw

end RH.Zeta85.RSBlockMomentBridge

end
