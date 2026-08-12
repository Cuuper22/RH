/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Inputs95
import RH.Zeta85.Discharge.TrimmedMoment
import Zeta23.Final
import Zeta23.Tail

/-!
# Finite-to-asymptotic transfer for the quartic rungs

This file consumes only the explicit per-support analytic structures in
`Inputs95`.  It does not use the signed-pair or Rudnick--Sarnak fields: those
are upstream routes for proving the trace and moment structures, not logical
substitutes for them.

The finite bridge is evaluated at the actual first four spectral moments.
Its asymptotic boundary is only the single scalar quartic score selected by
the terminal certificate; no finite matrix is asserted to have its limiting
top-hat moments exactly.
-/

open Filter Matrix Finset Unitary
open scoped BigOperators ComplexOrder Topology

noncomputable section

namespace RH
namespace Zeta85
namespace QuarticTransfer

open Zeta23 RHLinalg
open RobustStability TrimmedMoment

/-! ## 1. Centered spectral moments -/

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem specMap_const_one {d : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian) :
    specMap hG (fun _ => (1 : ℝ)) = 1 := by
  unfold specMap
  rw [conjStarAlgAut_apply]
  simp

private theorem specMap_pow_nat {d : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian)
    (f : ℝ → ℝ) (k : ℕ) :
    (specMap hG f) ^ k = specMap hG (fun x => f x ^ k) := by
  induction k with
  | zero =>
      simpa only [pow_zero] using (specMap_const_one hG).symm
  | succ k ih =>
      rw [pow_succ, ih, ← specMap_mul]
      congr 1

/-- The normalized centered eigenvalue moment is exactly the normalized
real trace of the corresponding centered matrix power. -/
theorem spectralMoment_eq_centered_rtrace {d : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian) (k : ℕ) :
    spectralMoment hG k = rtrace ((G - 1) ^ k) / (d : ℝ) := by
  have hcenter : G - 1 = specMap hG (fun x => x - 1) := by
    calc
      G - 1 = specMap hG id - specMap hG (fun _ => (1 : ℝ)) := by
        rw [specMap_id, specMap_const_one]
      _ = specMap hG (id - fun _ => (1 : ℝ)) := (specMap_sub hG _ _).symm
      _ = specMap hG (fun x => x - 1) := by rfl
  have htrace :
      rtrace ((G - 1) ^ k) =
        ∑ i : SpectralIndex d, (hG.eigenvalues₀ i - 1) ^ k := by
    rw [hcenter, specMap_pow_nat, rtrace_specMap]
    exact sum_eigenvalues_reindex hG (fun x => (x - 1) ^ k)
  rw [htrace]
  simp only [spectralMoment, normalizedMoment, uniformWeight, centeredSpectrum,
    SpectralIndex, Fintype.card_fin, div_eq_mul_inv]
  simp only [one_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## 2. The finite affine bridge -/

/-- The quartic evaluated at the actual first four centered moments of the
distinguished finite block. -/
def quarticScore {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  q.p0 + q.p1 * F.centeredBlockMoment 1 T +
    q.p2 * F.centeredBlockMoment 2 T +
    q.p3 * F.centeredBlockMoment 3 T +
    q.p4 * F.centeredBlockMoment 4 T

/-- The sum-first version of the certificate statistic.  It combines the
block-size contribution with the four raw centered matrix traces before the
single normalization by the dyadic zero count. -/
def quarticTraceNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  q.p0 * (F.blockDim T : ℝ) +
    q.p1 * rtrace ((F.block T - 1) ^ 1) +
    q.p2 * rtrace ((F.block T - 1) ^ 2) +
    q.p3 * rtrace ((F.block T - 1) ^ 3) +
    q.p4 * rtrace ((F.block T - 1) ^ 4)

/-- Coefficients of the same polynomial after changing variables from the
centered eigenvalue y = x - 1 back to the raw eigenvalue x. -/
def uncenteredQuartic (q : Quartic) : Quartic where
  p0 := q.p0 - q.p1 + q.p2 - q.p3 + q.p4
  p1 := q.p1 - 2 * q.p2 + 3 * q.p3 - 4 * q.p4
  p2 := q.p2 - 3 * q.p3 + 6 * q.p4
  p3 := q.p3 - 4 * q.p4
  p4 := q.p4

/-- The target numerator written directly in uncentered cyclic traces. -/
def uncenteredQuarticTraceNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  let u := uncenteredQuartic q
  u.p0 * (F.blockDim T : ℝ) +
    u.p1 * rtrace ((F.block T) ^ 1) +
    u.p2 * rtrace ((F.block T) ^ 2) +
    u.p3 * rtrace ((F.block T) ^ 3) +
    u.p4 * rtrace ((F.block T) ^ 4)

/-- Finite binomial expansion: centering the matrix and shifting the
certificate coefficients are exactly the same operation. -/
theorem quarticTraceNumerator_eq_uncentered
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    quarticTraceNumerator q F T =
      uncenteredQuarticTraceNumerator q F T := by
  have hone :
      rtrace (1 : Matrix (Fin (F.blockDim T)) (Fin (F.blockDim T)) ℂ) =
        (F.blockDim T : ℝ) := by
    simp [rtrace, Matrix.trace]
  rw [quarticTraceNumerator, uncenteredQuarticTraceNumerator,
    uncenteredQuartic]
  rw [show (F.block T - 1) ^ 1 = F.block T ^ 1 - 1 by noncomm_ring]
  rw [show (F.block T - 1) ^ 2 =
      F.block T ^ 2 - (F.block T + F.block T) + 1 by noncomm_ring]
  rw [show (F.block T - 1) ^ 3 =
      F.block T ^ 3 -
        (F.block T ^ 2 + F.block T ^ 2 + F.block T ^ 2) +
        (F.block T + F.block T + F.block T) - 1 by noncomm_ring]
  rw [show (F.block T - 1) ^ 4 =
      F.block T ^ 4 -
        (F.block T ^ 3 + F.block T ^ 3 + F.block T ^ 3 + F.block T ^ 3) +
        (F.block T ^ 2 + F.block T ^ 2 + F.block T ^ 2 +
          F.block T ^ 2 + F.block T ^ 2 + F.block T ^ 2) -
        (F.block T + F.block T + F.block T + F.block T) + 1 by
          noncomm_ring]
  simp only [rtrace_add, rtrace_sub, hone]
  ring_nf

/-- Explicit cyclic index sums for the first four raw matrix traces. -/
def cyclicTrace1 {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Complex.re (∑ i : Fin d, B i i)

def cyclicTrace2 {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Complex.re (∑ i : Fin d, ∑ j : Fin d, B i j * B j i)

def cyclicTrace3 {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Complex.re (∑ i : Fin d, ∑ j : Fin d,
    (∑ k : Fin d, B i k * B k j) * B j i)

def cyclicTrace4 {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Complex.re (∑ i : Fin d, ∑ j : Fin d,
    (∑ k : Fin d, B i k * B k j) *
      (∑ l : Fin d, B j l * B l i))

theorem rtrace_pow_one_eq_cyclic {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (B ^ 1) = cyclicTrace1 B := by
  simp [cyclicTrace1, rtrace, Matrix.trace]

theorem rtrace_pow_two_eq_cyclic {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (B ^ 2) = cyclicTrace2 B := by
  rw [show B ^ 2 = B * B by noncomm_ring]
  simp [cyclicTrace2, rtrace, Matrix.trace, Matrix.mul_apply]

theorem rtrace_pow_three_eq_cyclic {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (B ^ 3) = cyclicTrace3 B := by
  rw [show B ^ 3 = (B * B) * B by noncomm_ring]
  simp [cyclicTrace3, rtrace, Matrix.trace, Matrix.mul_apply]

theorem rtrace_pow_four_eq_cyclic {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (B ^ 4) = cyclicTrace4 B := by
  rw [show B ^ 4 = (B * B) * (B * B) by noncomm_ring]
  simp [cyclicTrace4, rtrace, Matrix.trace, Matrix.mul_apply]

/-- The uncentered target numerator with every trace power replaced by its
explicit cyclic index sum. -/
def cyclicQuarticTraceNumerator {d : ℕ}
    (q : Quartic) (B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  let u := uncenteredQuartic q
  u.p0 * (d : ℝ) + u.p1 * cyclicTrace1 B +
    u.p2 * cyclicTrace2 B + u.p3 * cyclicTrace3 B +
    u.p4 * cyclicTrace4 B

theorem uncenteredQuarticTraceNumerator_eq_cyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    uncenteredQuarticTraceNumerator q F T =
      cyclicQuarticTraceNumerator q (F.block T) := by
  simp only [uncenteredQuarticTraceNumerator, cyclicQuarticTraceNumerator,
    rtrace_pow_one_eq_cyclic, rtrace_pow_two_eq_cyclic,
    rtrace_pow_three_eq_cyclic, rtrace_pow_four_eq_cyclic]

/-- One literal principal-block entry opened into the actual finite
enlarged-window zero sum. -/
def blockZeroEntry
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (i j : Fin (F.blockDim T)) : ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) *
    ∑ᶠ ρ ∈ Z.ZIprime T,
      (Z.mult ρ : ℂ) *
        F.atom T (F.blockEmbedding T i) ρ *
        F.atom T (F.blockEmbedding T j) ρ

theorem block_apply_eq_zeroEntry
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ}
    (i j : Fin (F.blockDim T)) :
    F.block T i j = blockZeroEntry F T i j := by
  rfl

/-- One summand after replacing the finite-support notation by the canonical
finite set of enlarged-window zeros. -/
def blockZeroSummand
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (i j : Fin (F.blockDim T)) (ρ : ℂ) : ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) *
    ((Z.mult ρ : ℂ) *
      F.atom T (F.blockEmbedding T i) ρ *
      F.atom T (F.blockEmbedding T j) ρ)

theorem blockZeroEntry_eq_finsetSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ}
    (i j : Fin (F.blockDim T)) :
    blockZeroEntry F T i j =
      ∑ ρ ∈ ZeroSide.ZI Z T, blockZeroSummand F T i j ρ := by
  unfold blockZeroEntry blockZeroSummand
  rw [finsum_mem_eq_finite_toFinset_sum _
    (ZeroSide.ZIprime_finite Z T)]
  rw [Finset.mul_sum]
  rfl

/-- Cyclic sums after every block entry has been replaced by its literal
finite zero sum. -/
def zeroCyclicTrace1
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ i : Fin (F.blockDim T), blockZeroEntry F T i i)

def zeroCyclicTrace2
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
    blockZeroEntry F T i j * blockZeroEntry F T j i)

def zeroCyclicTrace3
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
    (∑ k : Fin (F.blockDim T),
      blockZeroEntry F T i k * blockZeroEntry F T k j) *
        blockZeroEntry F T j i)

def zeroCyclicTrace4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
    (∑ k : Fin (F.blockDim T),
      blockZeroEntry F T i k * blockZeroEntry F T k j) *
    (∑ l : Fin (F.blockDim T),
      blockZeroEntry F T j l * blockZeroEntry F T l i))

/-- Fully expanded cyclic zero-tuple sums. -/
def zeroTupleCyclicTrace1
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ i : Fin (F.blockDim T),
    ∑ ρ ∈ ZeroSide.ZI Z T, blockZeroSummand F T i i ρ)

def zeroTupleCyclicTrace2
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
    ∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
      blockZeroSummand F T i j ρ₁ *
        blockZeroSummand F T j i ρ₂)

def zeroTupleCyclicTrace3
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
    ∑ k : Fin (F.blockDim T),
      ∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
        ∑ ρ₃ ∈ ZeroSide.ZI Z T,
          (blockZeroSummand F T i k ρ₁ *
            blockZeroSummand F T k j ρ₂) *
              blockZeroSummand F T j i ρ₃)

def zeroTupleCyclicTrace4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
    ∑ k : Fin (F.blockDim T), ∑ l : Fin (F.blockDim T),
      ∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
        ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
          (blockZeroSummand F T i k ρ₁ *
            blockZeroSummand F T k j ρ₂) *
          (blockZeroSummand F T j l ρ₃ *
            blockZeroSummand F T l i ρ₄))

/-- Commute a finite block-index sum past one explicitly supplied zero set. -/
private theorem sum_fintype_finset_comm
    {ι α : Type*} [Fintype ι]
    (s : Finset α) (f : ι → α → ℂ) :
    (∑ i : ι, ∑ a ∈ s, f i a) =
      ∑ a ∈ s, ∑ i : ι, f i a := by
  rw [Finset.sum_comm]

/-- Zero-tuple-first cyclic kernels.  Every block-index contraction now sits
inside the contribution of one explicit ordered tuple of zeros. -/
def zeroKernelCyclicTrace1
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ ∈ ZeroSide.ZI Z T,
    ∑ i : Fin (F.blockDim T), blockZeroSummand F T i i ρ)

def zeroKernelCyclicTrace2
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    ∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
      blockZeroSummand F T i j ρ₁ *
        blockZeroSummand F T j i ρ₂)

def zeroKernelCyclicTrace3
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    ∑ ρ₃ ∈ ZeroSide.ZI Z T,
      ∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
        ∑ k : Fin (F.blockDim T),
          (blockZeroSummand F T i k ρ₁ *
            blockZeroSummand F T k j ρ₂) *
              blockZeroSummand F T j i ρ₃)

def zeroKernelCyclicTrace4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
      ∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
        ∑ k : Fin (F.blockDim T), ∑ l : Fin (F.blockDim T),
          (blockZeroSummand F T i k ρ₁ *
            blockZeroSummand F T k j ρ₂) *
          (blockZeroSummand F T j l ρ₃ *
            blockZeroSummand F T l i ρ₄))

/-- One scalar contraction of two zero atoms over the distinguished column
grid.  This is the pair object to which complex Poisson summation applies. -/
def zeroPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑ i : Fin (F.blockDim T),
    F.atom T (F.blockEmbedding T i) ρ *
      F.atom T (F.blockEmbedding T i) ρ'

/-- The normalization and multiplicity carried by one zero edge. -/
def zeroEdgeWeight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ : ℂ) : ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) * (Z.mult ρ : ℂ)

/-- Factored contributions of one ordered zero tuple.  The pair kernels are
ordered by the block indices i, j, k, l, so expanding the products recovers
the literal cyclic contractions without another sum permutation. -/
def factoredZeroCycle1
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ : ℂ) : ℂ :=
  zeroPairKernel F T ρ ρ * zeroEdgeWeight F T ρ

def factoredZeroCycle2
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ₁ ρ₂ : ℂ) : ℂ :=
  zeroPairKernel F T ρ₁ ρ₂ *
    (zeroPairKernel F T ρ₁ ρ₂ *
      (zeroEdgeWeight F T ρ₁ * zeroEdgeWeight F T ρ₂))

def factoredZeroCycle3
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (ρ₁ ρ₂ ρ₃ : ℂ) : ℂ :=
  zeroPairKernel F T ρ₁ ρ₃ *
    (zeroPairKernel F T ρ₂ ρ₃ *
      (zeroPairKernel F T ρ₁ ρ₂ *
        (zeroEdgeWeight F T ρ₁ *
          (zeroEdgeWeight F T ρ₂ * zeroEdgeWeight F T ρ₃))))

def factoredZeroCycle4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (ρ₁ ρ₂ ρ₃ ρ₄ : ℂ) : ℂ :=
  zeroPairKernel F T ρ₁ ρ₄ *
    (zeroPairKernel F T ρ₂ ρ₃ *
      (zeroPairKernel F T ρ₁ ρ₂ *
        (zeroPairKernel F T ρ₃ ρ₄ *
          (zeroEdgeWeight F T ρ₁ *
            (zeroEdgeWeight F T ρ₂ *
              (zeroEdgeWeight F T ρ₃ * zeroEdgeWeight F T ρ₄))))))

theorem zeroIndexKernel1_eq_factored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} {ρ : ℂ} :
    (∑ i : Fin (F.blockDim T), blockZeroSummand F T i i ρ) =
      factoredZeroCycle1 F T ρ := by
  simp only [factoredZeroCycle1, zeroPairKernel, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [blockZeroSummand, zeroEdgeWeight]
  ring_nf

theorem zeroIndexKernel2_eq_factored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} {ρ₁ ρ₂ : ℂ} :
    (∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
      blockZeroSummand F T i j ρ₁ *
        blockZeroSummand F T j i ρ₂) =
      factoredZeroCycle2 F T ρ₁ ρ₂ := by
  simp only [factoredZeroCycle2, zeroPairKernel,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [blockZeroSummand, zeroEdgeWeight]
  ring_nf

theorem zeroIndexKernel3_eq_factored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} {ρ₁ ρ₂ ρ₃ : ℂ} :
    (∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
      ∑ k : Fin (F.blockDim T),
        (blockZeroSummand F T i k ρ₁ *
          blockZeroSummand F T k j ρ₂) *
            blockZeroSummand F T j i ρ₃) =
      factoredZeroCycle3 F T ρ₁ ρ₂ ρ₃ := by
  simp only [factoredZeroCycle3, zeroPairKernel,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [blockZeroSummand, zeroEdgeWeight]
  ring_nf

theorem zeroIndexKernel4_eq_factored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ}
    {ρ₁ ρ₂ ρ₃ ρ₄ : ℂ} :
    (∑ i : Fin (F.blockDim T), ∑ j : Fin (F.blockDim T),
      ∑ k : Fin (F.blockDim T), ∑ l : Fin (F.blockDim T),
        (blockZeroSummand F T i k ρ₁ *
          blockZeroSummand F T k j ρ₂) *
        (blockZeroSummand F T j l ρ₃ *
          blockZeroSummand F T l i ρ₄)) =
      factoredZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄ := by
  simp only [factoredZeroCycle4, zeroPairKernel,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [blockZeroSummand, zeroEdgeWeight]
  ring_nf

def factoredZeroKernelCyclicTrace1
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ ∈ ZeroSide.ZI Z T, factoredZeroCycle1 F T ρ)

def factoredZeroKernelCyclicTrace2
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    factoredZeroCycle2 F T ρ₁ ρ₂)

def factoredZeroKernelCyclicTrace3
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    ∑ ρ₃ ∈ ZeroSide.ZI Z T, factoredZeroCycle3 F T ρ₁ ρ₂ ρ₃)

def factoredZeroKernelCyclicTrace4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
      factoredZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄)

theorem zeroKernelCyclicTrace1_eq_factored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroKernelCyclicTrace1 F T = factoredZeroKernelCyclicTrace1 F T := by
  unfold zeroKernelCyclicTrace1 factoredZeroKernelCyclicTrace1
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro ρ _
  exact zeroIndexKernel1_eq_factored

theorem zeroKernelCyclicTrace2_eq_factored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroKernelCyclicTrace2 F T = factoredZeroKernelCyclicTrace2 F T := by
  unfold zeroKernelCyclicTrace2 factoredZeroKernelCyclicTrace2
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro ρ₁ _
  apply Finset.sum_congr rfl
  intro ρ₂ _
  exact zeroIndexKernel2_eq_factored

theorem zeroKernelCyclicTrace3_eq_factored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroKernelCyclicTrace3 F T = factoredZeroKernelCyclicTrace3 F T := by
  unfold zeroKernelCyclicTrace3 factoredZeroKernelCyclicTrace3
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro ρ₁ _
  apply Finset.sum_congr rfl
  intro ρ₂ _
  apply Finset.sum_congr rfl
  intro ρ₃ _
  exact zeroIndexKernel3_eq_factored

theorem zeroKernelCyclicTrace4_eq_factored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroKernelCyclicTrace4 F T = factoredZeroKernelCyclicTrace4 F T := by
  unfold zeroKernelCyclicTrace4 factoredZeroKernelCyclicTrace4
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro ρ₁ _
  apply Finset.sum_congr rfl
  intro ρ₂ _
  apply Finset.sum_congr rfl
  intro ρ₃ _
  apply Finset.sum_congr rfl
  intro ρ₄ _
  exact zeroIndexKernel4_eq_factored

theorem zeroTupleCyclicTrace1_eq_kernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroTupleCyclicTrace1 F T = zeroKernelCyclicTrace1 F T := by
  unfold zeroTupleCyclicTrace1 zeroKernelCyclicTrace1
  rw [sum_fintype_finset_comm (ZeroSide.ZI Z T)]

theorem zeroTupleCyclicTrace2_eq_kernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroTupleCyclicTrace2 F T = zeroKernelCyclicTrace2 F T := by
  unfold zeroTupleCyclicTrace2 zeroKernelCyclicTrace2
  rw [sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T)]

theorem zeroTupleCyclicTrace3_eq_kernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroTupleCyclicTrace3 F T = zeroKernelCyclicTrace3 F T := by
  unfold zeroTupleCyclicTrace3 zeroKernelCyclicTrace3
  rw [sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T)]

theorem zeroTupleCyclicTrace4_eq_kernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroTupleCyclicTrace4 F T = zeroKernelCyclicTrace4 F T := by
  unfold zeroTupleCyclicTrace4 zeroKernelCyclicTrace4
  rw [sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T),
    sum_fintype_finset_comm (ZeroSide.ZI Z T)]

theorem zeroCyclicTrace1_eq_tuple
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroCyclicTrace1 F T = zeroTupleCyclicTrace1 F T := by
  simp [zeroCyclicTrace1, zeroTupleCyclicTrace1,
    blockZeroEntry_eq_finsetSum]

theorem zeroCyclicTrace2_eq_tuple
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroCyclicTrace2 F T = zeroTupleCyclicTrace2 F T := by
  simp [zeroCyclicTrace2, zeroTupleCyclicTrace2,
    blockZeroEntry_eq_finsetSum, Finset.sum_mul, Finset.mul_sum]

theorem zeroCyclicTrace3_eq_tuple
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroCyclicTrace3 F T = zeroTupleCyclicTrace3 F T := by
  simp [zeroCyclicTrace3, zeroTupleCyclicTrace3,
    blockZeroEntry_eq_finsetSum, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]

theorem zeroCyclicTrace4_eq_tuple
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroCyclicTrace4 F T = zeroTupleCyclicTrace4 F T := by
  simp [zeroCyclicTrace4, zeroTupleCyclicTrace4,
    blockZeroEntry_eq_finsetSum, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]

def zeroCyclicQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  let u := uncenteredQuartic q
  u.p0 * (F.blockDim T : ℝ) + u.p1 * zeroCyclicTrace1 F T +
    u.p2 * zeroCyclicTrace2 F T + u.p3 * zeroCyclicTrace3 F T +
    u.p4 * zeroCyclicTrace4 F T

theorem cyclicQuarticTraceNumerator_eq_zeroCyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    cyclicQuarticTraceNumerator q (F.block T) =
      zeroCyclicQuarticNumerator q F T := by
  simp only [cyclicQuarticTraceNumerator, zeroCyclicQuarticNumerator,
    cyclicTrace1, cyclicTrace2, cyclicTrace3, cyclicTrace4,
    zeroCyclicTrace1, zeroCyclicTrace2, zeroCyclicTrace3, zeroCyclicTrace4,
    block_apply_eq_zeroEntry]

def zeroTupleQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  let u := uncenteredQuartic q
  u.p0 * (F.blockDim T : ℝ) + u.p1 * zeroTupleCyclicTrace1 F T +
    u.p2 * zeroTupleCyclicTrace2 F T + u.p3 * zeroTupleCyclicTrace3 F T +
    u.p4 * zeroTupleCyclicTrace4 F T

def zeroKernelQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  let u := uncenteredQuartic q
  u.p0 * (F.blockDim T : ℝ) + u.p1 * zeroKernelCyclicTrace1 F T +
    u.p2 * zeroKernelCyclicTrace2 F T + u.p3 * zeroKernelCyclicTrace3 F T +
    u.p4 * zeroKernelCyclicTrace4 F T

def factoredZeroKernelQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  let u := uncenteredQuartic q
  u.p0 * (F.blockDim T : ℝ) +
    u.p1 * factoredZeroKernelCyclicTrace1 F T +
    u.p2 * factoredZeroKernelCyclicTrace2 F T +
    u.p3 * factoredZeroKernelCyclicTrace3 F T +
    u.p4 * factoredZeroKernelCyclicTrace4 F T

theorem zeroKernelQuarticNumerator_eq_factored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroKernelQuarticNumerator q F T =
      factoredZeroKernelQuarticNumerator q F T := by
  simp only [zeroKernelQuarticNumerator,
    factoredZeroKernelQuarticNumerator,
    zeroKernelCyclicTrace1_eq_factored,
    zeroKernelCyclicTrace2_eq_factored,
    zeroKernelCyclicTrace3_eq_factored,
    zeroKernelCyclicTrace4_eq_factored]

theorem zeroTupleQuarticNumerator_eq_kernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroTupleQuarticNumerator q F T =
      zeroKernelQuarticNumerator q F T := by
  simp only [zeroTupleQuarticNumerator, zeroKernelQuarticNumerator,
    zeroTupleCyclicTrace1_eq_kernel, zeroTupleCyclicTrace2_eq_kernel,
    zeroTupleCyclicTrace3_eq_kernel, zeroTupleCyclicTrace4_eq_kernel]

theorem zeroCyclicQuarticNumerator_eq_tuple
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v} {T : ℝ} :
    zeroCyclicQuarticNumerator q F T =
      zeroTupleQuarticNumerator q F T := by
  simp only [zeroCyclicQuarticNumerator, zeroTupleQuarticNumerator,
    zeroCyclicTrace1_eq_tuple, zeroCyclicTrace2_eq_tuple,
    zeroCyclicTrace3_eq_tuple, zeroCyclicTrace4_eq_tuple]

/-- On a nonempty block, multiplying the normalized quartic score by the
block size is exactly the raw trace numerator. -/
theorem blockDim_mul_quarticScore
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    {T : ℝ} (hm : 0 < F.blockDim T) :
    (F.blockDim T : ℝ) * quarticScore q F T =
      quarticTraceNumerator q F T := by
  have hm0 : (F.blockDim T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  simp only [quarticScore, quarticTraceNumerator,
    QuarticGramFamily.centeredBlockMoment]
  field_simp [hm0]
  <;> ring

/-- The weighted normalized-moment expression is therefore exactly the
once-normalized raw trace numerator. -/
theorem weightedQuarticScore_eq_traceNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    {T : ℝ} (hm : 0 < F.blockDim T) :
    (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
        quarticScore q F T =
      quarticTraceNumerator q F T / (Z.N T (2 * T) : ℝ) := by
  calc
    (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
          quarticScore q F T =
        ((F.blockDim T : ℝ) * quarticScore q F T) /
          (Z.N T (2 * T) : ℝ) := by ring
    _ = quarticTraceNumerator q F T /
          (Z.N T (2 * T) : ℝ) := by
      rw [blockDim_mul_quarticScore hm]

/-- The same quartic evaluated at the formula-(21) limiting moments. -/
def limitQuarticScore (q : Quartic) (μ p : ℝ) : ℝ :=
  q.p0 + q.p1 * formula21Moment 1 μ p +
    q.p2 * formula21Moment 2 μ p +
    q.p3 * formula21Moment 3 μ p +
    q.p4 * formula21Moment 4 μ p

/-- The target-specific analytic datum actually consumed by a quartic
certificate: convergence of its one scalar score.  Separate convergence of
all four moments is a sufficient construction route, not a logical
requirement of the transfer. -/
def QuarticScoreConvergence
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop :=
  Tendsto (quarticScore q F) atTop
    (nhds (limitQuarticScore q μ p))

/-- The combined asymptotic datum actually consumed after the finite
inequality is normalized.  Taking this product before the limit permits
cancellation between the block density and normalized block moments. -/
structure WeightedQuarticLimit
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  weighted_score : Tendsto
    (fun T => (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
      quarticScore q F T)
    atTop (nhds (μ * limitQuarticScore q μ p))

/-- The one-sided weighted statement used by the density argument.  It asks
only that the certificate statistic eventually exceed every strict lower
threshold; no upper bound or exact limit is consumed downstream. -/
structure WeightedQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ, x < μ * limitQuarticScore q μ p →
    ∀ᶠ T in atTop,
      x < (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
        quarticScore q F T

/-- The analytic boundary in sum-first form: a one-sided lower bound for one
linear combination of raw centered traces, normalized only after summation. -/
structure QuarticTraceLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ, x < μ * limitQuarticScore q μ p →
    ∀ᶠ T in atTop,
      x < quarticTraceNumerator q F T / (Z.N T (2 * T) : ℝ)

/-- The same one-sided boundary in the uncentered cyclic-trace coordinates
produced directly by Gram-power expansion. -/
structure UncenteredQuarticTraceLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ, x < μ * limitQuarticScore q μ p →
    ∀ᶠ T in atTop,
      x < uncenteredQuarticTraceNumerator q F T /
        (Z.N T (2 * T) : ℝ)

/-- The final matrix-algebra-free coordinate: one lower bound on a fixed
combination of explicit cyclic entry sums. -/
structure CyclicQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ, x < μ * limitQuarticScore q μ p →
    ∀ᶠ T in atTop,
      x < cyclicQuarticTraceNumerator q (F.block T) /
        (Z.N T (2 * T) : ℝ)

/-- The zero-correlation coordinate consumed by the terminal route: one
lower bound on the explicit cyclic products of literal finite zero sums. -/
structure ZeroCyclicQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ, x < μ * limitQuarticScore q μ p →
    ∀ᶠ T in atTop,
      x < zeroCyclicQuarticNumerator q F T /
        (Z.N T (2 * T) : ℝ)

/-- The fully expanded zero-tuple correlation statement. -/
structure ZeroTupleQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ, x < μ * limitQuarticScore q μ p →
    ∀ᶠ T in atTop,
      x < zeroTupleQuarticNumerator q F T /
        (Z.N T (2 * T) : ℝ)

/-- The zero-tuple-first statement consumed by the terminal transfer. -/
structure ZeroKernelQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ, x < μ * limitQuarticScore q μ p →
    ∀ᶠ T in atTop,
      x < zeroKernelQuarticNumerator q F T /
        (Z.N T (2 * T) : ℝ)

/-- The one-sided bound after the block-index contractions have been
factorized into scalar zero-pair kernels. -/
structure FactoredZeroKernelQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ, x < μ * limitQuarticScore q μ p →
    ∀ᶠ T in atTop,
      x < factoredZeroKernelQuarticNumerator q F T /
        (Z.N T (2 * T) : ℝ)

/-- All finite errors in the affine bridge.  The coefficient `3` on the
enlarged-window edge count is exact: `2` comes from robust stability and
`1` from the two count comparisons. -/
def transferError {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  2 * F.pTraceError T + 4 * F.traceError T + F.frobError T +
    3 * (Assembly.NII Z T : ℝ)

/-- Sorted-head weak duality for the actual principal block, with all
normalizations cleared. -/
private theorem scaled_block_quartic_le_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hzero : StableZeroSide F) (q : Quartic) (cap : ℝ)
    (hdual : DualFeasible q cap) (T : ℝ) (hm : 0 < F.blockDim T) :
    (F.blockDim T : ℝ) * quarticScore q F T -
        (Z.s2 T + Z.p T : ℕ) * cap ≤
      tailExcessSq (hzero.block_isHermitian T) (Z.s2 T + Z.p T) := by
  let hB := hzero.block_isHermitian T
  have hmR : (0 : ℝ) < F.blockDim T := by exact_mod_cast hm
  have hinputs := spectral_headTrimmedMomentInputs
    (b := Z.s2 T + Z.p T) hB hm
  have hdualFinite := finite_trimmed_quartic_dual q cap
    (centeredSpectrum hB) (uniformWeight (SpectralIndex (F.blockDim T)))
    (uniformRemoved
      (spectralHeadSet (Fintype.card (Fin (F.blockDim T))) (Z.s2 T + Z.p T)))
    (spectralMoment hB 1) (spectralMoment hB 2)
    (spectralMoment hB 3) (spectralMoment hB 4)
    (((Z.s2 T + Z.p T : ℕ) : ℝ) / F.blockDim T) hdual hinputs
  have hscaled := mul_le_mul_of_nonneg_left hdualFinite hmR.le
  rw [spectral_residualTail_eq_tailExcessSq_div] at hscaled
  have hscore :
      q.p0 + q.p1 * spectralMoment hB 1 + q.p2 * spectralMoment hB 2 +
          q.p3 * spectralMoment hB 3 + q.p4 * spectralMoment hB 4 =
        quarticScore q F T := by
    simp only [quarticScore, QuarticGramFamily.centeredBlockMoment,
      spectralMoment_eq_centered_rtrace]
  rw [hscore] at hscaled
  calc
    (F.blockDim T : ℝ) * quarticScore q F T -
          (Z.s2 T + Z.p T : ℕ) * cap =
        (F.blockDim T : ℝ) *
          (quarticScore q F T -
            ((Z.s2 T + Z.p T : ℕ) : ℝ) / F.blockDim T * cap) := by
              field_simp [hmR.ne']
    _ ≤ (F.blockDim T : ℝ) *
        (tailExcessSq hB (Z.s2 T + Z.p T) / F.blockDim T) := hscaled
    _ = tailExcessSq (hzero.block_isHermitian T) (Z.s2 T + Z.p T) := by
      field_simp [hmR.ne']

/-- The exact finite affine bridge.  It uses the actual finite moments,
never their limits. -/
theorem finite_affine_bridge_at
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hzero : StableZeroSide F) (q : Quartic) (cap Dbar : ℝ)
    (hdual : DualFeasible q cap) (hcap : cap / 2 ≤ 1)
    (hcost : profileSaturatedCost σ v ≤ Dbar)
    (T : ℝ) (hT : 0 ≤ T) (hm : 0 < F.blockDim T)
    (htail :
      tailExcessSq (hzero.block_isHermitian T) (Z.s2 T + Z.p T) ≤
        (Z.s1 T : ℝ) -
          (2 - profileSaturatedCost σ v) * (Z.N T (2 * T) : ℝ) +
          2 * F.pTraceError T + 4 * F.traceError T + F.frobError T +
          2 * (Assembly.NII Z T : ℝ)) :
    (F.blockDim T : ℝ) * quarticScore q F T +
        (2 - Dbar - cap / 2) * (Z.N T (2 * T) : ℝ) ≤
      (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) + transferError F T := by
  have hweak := scaled_block_quartic_le_tail hzero q cap hdual T hm
  have hcore := core_count_le_dyadic_add_edge Z hT
  have hs1Nat := Assembly.s1_le Z hT
  have hs1 : (Z.s1 T : ℝ) ≤
      (Z.N0s T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast hs1Nat
  have hcap0 : 0 ≤ cap / 2 := div_nonneg hdual.cap_nonneg (by norm_num)
  have hremain : 0 ≤ 1 - cap / 2 := sub_nonneg.mpr hcap
  have hcoreScaled := mul_le_mul_of_nonneg_left hcore hcap0
  have hs1Scaled := mul_le_mul_of_nonneg_left hs1 hremain
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := by positivity
  have hcostScaled := mul_le_mul_of_nonneg_right hcost hN
  unfold transferError
  nlinarith

private theorem blockDim_pos_eventually
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hr1a : BlockDimensionLimit F) :
    ∀ᶠ T in atTop, 0 < F.blockDim T := by
  have hratio : ∀ᶠ T in atTop,
      0 < (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) :=
    hr1a.block_dimension.eventually (Ioi_mem_nhds hr1a.bandwidth_pos)
  filter_upwards [hratio] with T hratioT
  apply Nat.pos_of_ne_zero
  intro hm0
  simp [hm0] at hratioT

/-- Separate block-density and scalar-score limits imply the combined
weighted limit.  This compatibility theorem keeps the earlier construction
interfaces usable while exposing the weaker object the transfer needs. -/
theorem weightedQuarticLimit_of_separate
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hr1a : BlockDimensionLimit F)
    (hscore : QuarticScoreConvergence q F) :
    WeightedQuarticLimit q F :=
  ⟨blockDim_pos_eventually hr1a, hr1a.block_dimension.mul hscore⟩

/-- Exact weighted convergence supplies the weaker one-sided datum. -/
theorem WeightedQuarticLimit.toLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : WeightedQuarticLimit q F) :
    WeightedQuarticLowerBound q F :=
  ⟨h.block_dimension_pos, fun x hx =>
    h.weighted_score.eventually (Ioi_mem_nhds hx)⟩

/-- The normalized-moment and raw-trace lower-bound interfaces are
equivalent once eventual block nonemptiness is recorded. -/
theorem WeightedQuarticLowerBound.toTraceLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : WeightedQuarticLowerBound q F) :
    QuarticTraceLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx, h.block_dimension_pos]
      with T hT hm
  rw [weightedQuarticScore_eq_traceNumerator hm] at hT
  exact hT

theorem QuarticTraceLowerBound.toWeightedLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : QuarticTraceLowerBound q F) :
    WeightedQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx, h.block_dimension_pos]
      with T hT hm
  rw [weightedQuarticScore_eq_traceNumerator hm]
  exact hT

/-- Centered and uncentered raw-trace formulations are equivalent through
the finite binomial theorem above. -/
theorem QuarticTraceLowerBound.toUncentered
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : QuarticTraceLowerBound q F) :
    UncenteredQuarticTraceLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [quarticTraceNumerator_eq_uncentered] at hT
  exact hT

theorem UncenteredQuarticTraceLowerBound.toCentered
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : UncenteredQuarticTraceLowerBound q F) :
    QuarticTraceLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [quarticTraceNumerator_eq_uncentered]
  exact hT

theorem UncenteredQuarticTraceLowerBound.toCyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : UncenteredQuarticTraceLowerBound q F) :
    CyclicQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [uncenteredQuarticTraceNumerator_eq_cyclic] at hT
  exact hT

theorem CyclicQuarticLowerBound.toUncentered
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : CyclicQuarticLowerBound q F) :
    UncenteredQuarticTraceLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [uncenteredQuarticTraceNumerator_eq_cyclic]
  exact hT

theorem CyclicQuarticLowerBound.toZeroCyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : CyclicQuarticLowerBound q F) :
    ZeroCyclicQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [cyclicQuarticTraceNumerator_eq_zeroCyclic] at hT
  exact hT

theorem ZeroCyclicQuarticLowerBound.toCyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : ZeroCyclicQuarticLowerBound q F) :
    CyclicQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [cyclicQuarticTraceNumerator_eq_zeroCyclic]
  exact hT

theorem ZeroCyclicQuarticLowerBound.toTuple
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : ZeroCyclicQuarticLowerBound q F) :
    ZeroTupleQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [zeroCyclicQuarticNumerator_eq_tuple] at hT
  exact hT

theorem ZeroTupleQuarticLowerBound.toZeroCyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : ZeroTupleQuarticLowerBound q F) :
    ZeroCyclicQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [zeroCyclicQuarticNumerator_eq_tuple]
  exact hT

theorem ZeroTupleQuarticLowerBound.toKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : ZeroTupleQuarticLowerBound q F) :
    ZeroKernelQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [zeroTupleQuarticNumerator_eq_kernel] at hT
  exact hT

theorem ZeroKernelQuarticLowerBound.toTuple
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : ZeroKernelQuarticLowerBound q F) :
    ZeroTupleQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [zeroTupleQuarticNumerator_eq_kernel]
  exact hT

theorem ZeroKernelQuarticLowerBound.toZeroCyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : ZeroKernelQuarticLowerBound q F) :
    ZeroCyclicQuarticLowerBound q F :=
  h.toTuple.toZeroCyclic

theorem ZeroKernelQuarticLowerBound.toFactored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : ZeroKernelQuarticLowerBound q F) :
    FactoredZeroKernelQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [zeroKernelQuarticNumerator_eq_factored] at hT
  exact hT

theorem FactoredZeroKernelQuarticLowerBound.toKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : FactoredZeroKernelQuarticLowerBound q F) :
    ZeroKernelQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [h.eventually_gt x hx] with T hT
  rw [zeroKernelQuarticNumerator_eq_factored]
  exact hT

theorem FactoredZeroKernelQuarticLowerBound.toZeroCyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : FactoredZeroKernelQuarticLowerBound q F) :
    ZeroCyclicQuarticLowerBound q F :=
  h.toKernel.toZeroCyclic

/-- Eventual form of the finite affine bridge, obtained directly from the
proved robust stability inequality. -/
theorem finite_affine_bridge
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hblock : ∀ᶠ T in atTop, 0 < F.blockDim T)
    (q : Quartic) (cap Dbar : ℝ) (hdual : DualFeasible q cap)
    (hcap : cap / 2 ≤ 1) (hcost : profileSaturatedCost σ v ≤ Dbar) :
    ∀ᶠ T in atTop,
      (F.blockDim T : ℝ) * quarticScore q F T +
          (2 - Dbar - cap / 2) * (Z.N T (2 * T) : ℝ) ≤
        (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) + transferError F T := by
  filter_upwards [robustBlockTailBound_eventually hfull hzero,
    hblock, eventually_ge_atTop (0 : ℝ)]
      with T htail hm hT
  exact finite_affine_bridge_at hzero q cap Dbar hdual hcap hcost T hT hm htail

/-! ## 3. Passage to the limit -/

theorem quarticScore_tendsto
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hmom : BlockMomentConvergence F) (q : Quartic) :
    Tendsto (quarticScore q F) atTop (nhds (limitQuarticScore q μ p)) := by
  change Tendsto
    (fun T => q.p0 + q.p1 * F.centeredBlockMoment 1 T +
      q.p2 * F.centeredBlockMoment 2 T +
      q.p3 * F.centeredBlockMoment 3 T +
      q.p4 * F.centeredBlockMoment 4 T) atTop
    (nhds (q.p0 + q.p1 * formula21Moment 1 μ p +
      q.p2 * formula21Moment 2 μ p + q.p3 * formula21Moment 3 μ p +
      q.p4 * formula21Moment 4 μ p))
  have h1 := hmom.moments 1 (by omega) (by omega)
  have h2 := hmom.moments 2 (by omega) (by omega)
  have h3 := hmom.moments 3 (by omega) (by omega)
  have h4 := hmom.moments 4 (by omega) (by omega)
  exact
    ((((tendsto_const_nhds.add (tendsto_const_nhds.mul h1)).add
      (tendsto_const_nhds.mul h2)).add
      (tendsto_const_nhds.mul h3)).add
      (tendsto_const_nhds.mul h4))

/-- Four separate moment limits imply the one target-specific scalar limit.
This keeps the stronger formula-(21) route available without forcing every
future construction to prove unused coordinates. -/
theorem quarticScoreConvergence_of_moments
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hmom : BlockMomentConvergence F) (q : Quartic) :
    QuarticScoreConvergence q F :=
  quarticScore_tendsto hmom q

private theorem edgeCount_small
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) :
    (fun T => (Assembly.NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hRvM.local_count
  obtain ⟨C, hC⟩ := Tail.eventually_NII_le Z hA₀ hloc
  have hO : (fun T => (Assembly.NII Z T : ℝ)) =O[atTop]
      (fun T => Real.sqrt T * Zeta23.l T) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hC, Assembly.eventually_l_pos] with T hCT hlT
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    simpa [mul_assoc] using hCT
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM
      Assembly.isLittleO_sqrt_mul_l_Tl)

theorem transferError_small
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hRvM : RiemannVonMangoldt Z) (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F) :
    transferError F =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  change (fun T => 2 * F.pTraceError T + 4 * F.traceError T + F.frobError T +
    3 * (Assembly.NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ))
  have hp := hzero.p_trace_small.const_mul_left 2
  have ht := hfull.trace_small.const_mul_left 4
  have he := (edgeCount_small hRvM).const_mul_left 3
  exact (((hp.add ht).add hfull.frob_small).add he)

/-- The finite affine lower-bound expression after division by the dyadic
zero count and by the positive affine denominator. -/
def normalizedTransfer {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (cap Dbar : ℝ) (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) : ℝ :=
  (((F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ)) * quarticScore q F T +
      (2 - Dbar - cap / 2) -
      transferError F T / (Z.N T (2 * T) : ℝ)) /
    (1 - cap / 2)

theorem normalizedTransfer_tendsto
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hRvM : RiemannVonMangoldt Z) (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (q : Quartic) (hweighted : WeightedQuarticLimit q F)
    (cap Dbar : ℝ) :
    Tendsto (normalizedTransfer q cap Dbar F) atTop
      (nhds ((μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2) /
        (1 - cap / 2))) := by
  have hproduct := hweighted.weighted_score
  have herror := (transferError_small hRvM hfull hzero).tendsto_div_nhds_zero
  have hconstant : Tendsto (fun _ : ℝ => 2 - Dbar - cap / 2) atTop
      (nhds (2 - Dbar - cap / 2)) := tendsto_const_nhds
  have hnumerator :=
    (hproduct.add hconstant).sub herror
  have hquotient := hnumerator.div_const (1 - cap / 2)
  change Tendsto
    (fun T =>
      (((F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ)) * quarticScore q F T +
          (2 - Dbar - cap / 2) -
          transferError F T / (Z.N T (2 * T) : ℝ)) /
        (1 - cap / 2)) atTop
    (nhds ((μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2) /
      (1 - cap / 2)))
  have hlimit :
      (μ * limitQuarticScore q μ p + (2 - Dbar - cap / 2) - 0) /
          (1 - cap / 2) =
        (μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2) /
          (1 - cap / 2) := by ring
  rw [← hlimit]
  exact hquotient

/-- Generic finite-to-asymptotic transfer.  The strict numerical comparison
is separated as a premise so each terminal specialization must prove it by
exact arithmetic; it does not assume any zero-density conclusion. -/
theorem asymptotic_eps_transfer
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hRvM : RiemannVonMangoldt Z) (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (q : Quartic) (hfactored : FactoredZeroKernelQuarticLowerBound q F)
    (cap Dbar target : ℝ) (hdual : DualFeasible q cap)
    (hcap : cap / 2 < 1) (hcost : profileSaturatedCost σ v ≤ Dbar)
    (hstrict : target <
      (μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2) /
        (1 - cap / 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (target - ε) * (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  have hzeroCyclic := hfactored.toZeroCyclic
  have hcyclic := hzeroCyclic.toCyclic
  have huncentered := hcyclic.toUncentered
  have htrace := huncentered.toCentered
  have hweighted := htrace.toWeightedLowerBound
  have hden : 0 < 1 - cap / 2 := sub_pos.mpr hcap
  have hstrict' :
      target * (1 - cap / 2) <
        μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2 :=
    (lt_div_iff₀ hden).mp hstrict
  let δ : ℝ :=
    (μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2 -
      target * (1 - cap / 2)) / 3
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  have hscore : ∀ᶠ T in atTop,
      μ * limitQuarticScore q μ p - δ <
        (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
          quarticScore q F T :=
    hweighted.eventually_gt _ (by linarith)
  have herror0 :=
    (transferError_small hRvM hfull hzero).tendsto_div_nhds_zero
  have herror : ∀ᶠ T in atTop,
      transferError F T / (Z.N T (2 * T) : ℝ) < δ :=
    herror0.eventually (Iio_mem_nhds hδ)
  have hlower : ∀ᶠ T in atTop, target < normalizedTransfer q cap Dbar F T := by
    filter_upwards [hscore, herror] with T hscoreT herrorT
    rw [normalizedTransfer]
    apply (lt_div_iff₀ hden).2
    dsimp only [δ] at hscoreT herrorT
    linarith
  have hfinite := finite_affine_bridge hfull hzero
    hweighted.block_dimension_pos q cap Dbar hdual
    hcap.le hcost
  have hNpos := (Assembly.tendsto_N_atTop Z hRvM).eventually_gt_atTop 0
  have htarget : ∀ᶠ T in atTop,
      target * (Z.N T (2 * T) : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hlower, hfinite, hNpos] with T hlowerT hfiniteT hNT
    rw [normalizedTransfer] at hlowerT
    have hlowerDen := (lt_div_iff₀ hden).mp hlowerT
    have hrewrite :
        (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) * quarticScore q F T +
              (2 - Dbar - cap / 2) -
              transferError F T / (Z.N T (2 * T) : ℝ) =
          ((F.blockDim T : ℝ) * quarticScore q F T +
              (2 - Dbar - cap / 2) * (Z.N T (2 * T) : ℝ) -
              transferError F T) /
            (Z.N T (2 * T) : ℝ) := by
      field_simp [hNT.ne']
    rw [hrewrite] at hlowerDen
    have hlowerN := (lt_div_iff₀ hNT).mp hlowerDen
    have hmul :
        target * (1 - cap / 2) * (Z.N T (2 * T) : ℝ) <
          (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) := by
      linarith
    have hmul' :
        (1 - cap / 2) * (target * (Z.N T (2 * T) : ℝ)) <
          (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) := by
      calc
        (1 - cap / 2) * (target * (Z.N T (2 * T) : ℝ)) =
            target * (1 - cap / 2) * (Z.N T (2 * T) : ℝ) := by ring
        _ < (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) := hmul
    exact (lt_of_mul_lt_mul_left hmul' hden.le).le
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp htarget
  refine ⟨T₀, ?_⟩
  intro T hT
  have hmain := hT₀ T hT
  have hNnonneg : 0 ≤ (Z.N T (2 * T) : ℝ) := by positivity
  nlinarith

/-! ## 4. Exact terminal specializations -/

private theorem formula21_moments_8686 :
    formula21Moment 2 Terminal8686.mu Terminal8686.width = Terminal8686.m2 ∧
    formula21Moment 3 Terminal8686.mu Terminal8686.width = Terminal8686.m3 ∧
    formula21Moment 4 Terminal8686.mu Terminal8686.width = Terminal8686.m4 := by
  constructor
  · simp only [formula21Moment, Terminal8686.m2, topHatM2]
    rw [TopHatMoments.formula21M2Integral_eq
      (by norm_num [Terminal8686.width]) (by norm_num [Terminal8686.width])]
  · constructor
    · simp only [formula21Moment, Terminal8686.m3, topHatM3]
      rw [TopHatMoments.formula21M3Integral_eq
        (by norm_num [Terminal8686.width]) (by norm_num [Terminal8686.width])]
    · simp only [formula21Moment, Terminal8686.m4, topHatM4]
      rw [TopHatMoments.formula21M4Integral_eq
        (by norm_num [Terminal8686.width]) (by norm_num [Terminal8686.width])]

private theorem formula21_moments_9506 :
    formula21Moment 2 Terminal9506.mu Terminal9506.width = Terminal9506.m2 ∧
    formula21Moment 3 Terminal9506.mu Terminal9506.width = Terminal9506.m3 ∧
    formula21Moment 4 Terminal9506.mu Terminal9506.width = Terminal9506.m4 := by
  constructor
  · simp only [formula21Moment, Terminal9506.m2, topHatM2]
    rw [TopHatMoments.formula21M2Integral_eq
      (by norm_num [Terminal9506.width]) (by norm_num [Terminal9506.width])]
  · constructor
    · simp only [formula21Moment, Terminal9506.m3, topHatM3]
      rw [TopHatMoments.formula21M3Integral_eq
        (by norm_num [Terminal9506.width]) (by norm_num [Terminal9506.width])]
    · simp only [formula21Moment, Terminal9506.m4, topHatM4]
      rw [TopHatMoments.formula21M4Integral_eq
        (by norm_num [Terminal9506.width]) (by norm_num [Terminal9506.width])]

theorem limitQuarticScore_8686 :
    limitQuarticScore Terminal8686.dual Terminal8686.mu Terminal8686.width =
      Terminal8686.AP := by
  obtain ⟨hm2, hm3, hm4⟩ := formula21_moments_8686
  rw [limitQuarticScore, show formula21Moment 1 Terminal8686.mu
    Terminal8686.width = 0 by rfl, hm2, hm3, hm4]
  simp only [mul_zero, add_zero, Terminal8686.AP]

theorem limitQuarticScore_9506 :
    limitQuarticScore Terminal9506.dual Terminal9506.mu Terminal9506.width =
      Terminal9506.AP := by
  obtain ⟨hm2, hm3, hm4⟩ := formula21_moments_9506
  rw [limitQuarticScore, show formula21Moment 1 Terminal9506.mu
    Terminal9506.width = 0 by rfl, hm2, hm3, hm4]
  simp only [mul_zero, add_zero, Terminal9506.AP]

theorem strict_transfer_8686 :
    (86855250 / 100000000 : ℝ) <
      ((4999 / 10000 : ℝ) *
          limitQuarticScore Terminal8686.dual (4999 / 10000) (89 / 100) +
          2 - Terminal8686.costUpper - Terminal8686.cap / 2) /
        (1 - Terminal8686.cap / 2) := by
  rw [show limitQuarticScore Terminal8686.dual (4999 / 10000) (89 / 100) =
    Terminal8686.AP by simpa only [Terminal8686.mu, Terminal8686.width] using
      limitQuarticScore_8686]
  have hden : 0 < 1 - Terminal8686.cap / 2 :=
    sub_pos.mpr Terminal8686.cap_slope
  have hden2 : 2 - Terminal8686.cap ≠ 0 := by linarith
  have hid :
      ((4999 / 10000 : ℝ) * Terminal8686.AP + 2 -
          Terminal8686.costUpper - Terminal8686.cap / 2) /
          (1 - Terminal8686.cap / 2) =
        2 - Terminal8686.costUpper + Terminal8686.fixedPoint := by
    rw [Terminal8686.fixedPoint, Terminal8686.mu]
    field_simp [hden.ne', hden2]
    ring
  rw [hid]
  exact Terminal8686.density_gt_frozen

theorem strict_transfer_9506 :
    (95063832187565 / 100000000000000 : ℝ) <
      ((4999 / 10000 : ℝ) *
          limitQuarticScore Terminal9506.dual (4999 / 10000) (83 / 100) +
          2 - Terminal9506.costUpper - Terminal9506.cap / 2) /
        (1 - Terminal9506.cap / 2) := by
  rw [show limitQuarticScore Terminal9506.dual (4999 / 10000) (83 / 100) =
    Terminal9506.AP by simpa only [Terminal9506.mu, Terminal9506.width] using
      limitQuarticScore_9506]
  have hden : 0 < 1 - Terminal9506.cap / 2 :=
    sub_pos.mpr Terminal9506.cap_slope
  have hden2 : 2 - Terminal9506.cap ≠ 0 := by linarith
  have hid :
      ((4999 / 10000 : ℝ) * Terminal9506.AP + 2 -
          Terminal9506.costUpper - Terminal9506.cap / 2) /
          (1 - Terminal9506.cap / 2) =
        2 - Terminal9506.costUpper + Terminal9506.fixedPoint := by
    rw [Terminal9506.fixedPoint, Terminal9506.mu]
    field_simp [hden.ne', hden2]
    ring
  rw [hid]
  exact Terminal9506.density_gt_frozen

/-- Support `14999/10000`: the three explicit analytic structures imply the
frozen R-8686 epsilon form. -/
theorem eps_transfer_8686
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family14999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hfactored : FactoredZeroKernelQuarticLowerBound Terminal8686.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((86855250 / 100000000 : ℝ) - ε) * (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  have hcost :
      profileSaturatedCost (14999 / 10000) QuarticWindowWitnesses.v8686 ≤
        Terminal8686.costUpper := by
    rw [profileSaturatedCost_v8686]
    exact QuarticWindowWitnesses.D8686_lt.le
  exact asymptotic_eps_transfer hRvM hfull hzero
    Terminal8686.dual hfactored Terminal8686.cap Terminal8686.costUpper
    (86855250 / 100000000) Terminal8686.dual_feasible
    Terminal8686.cap_slope hcost strict_transfer_8686

/-- Support `19999/10000`: the three explicit analytic structures imply the
frozen R-9506 epsilon form. -/
theorem eps_transfer_9506
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family19999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hfactored : FactoredZeroKernelQuarticLowerBound Terminal9506.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((95063832187565 / 100000000000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  have hcost :
      profileSaturatedCost (19999 / 10000) QuarticWindowWitnesses.v9506 ≤
        Terminal9506.costUpper := by
    rw [profileSaturatedCost_v9506]
    exact QuarticWindowWitnesses.D9506_lt.le
  exact asymptotic_eps_transfer hRvM hfull hzero
    Terminal9506.dual hfactored Terminal9506.cap Terminal9506.costUpper
    (95063832187565 / 100000000000000) Terminal9506.dual_feasible
    Terminal9506.cap_slope hcost strict_transfer_9506

theorem frozen_8657_lt_8686 :
    (865674254456636 / 1000000000000000 : ℝ) <
      86855250 / 100000000 := by
  norm_num

theorem frozen_9383_lt_9506 :
    (938313327050949 / 1000000000000000 : ℝ) <
      95063832187565 / 100000000000000 := by
  norm_num

/-- R-8657 follows monotonically from the stronger support-`14999/10000`
frozen transfer, with no additional analytic input. -/
theorem eps_transfer_8657
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family14999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hfactored : FactoredZeroKernelQuarticLowerBound Terminal8686.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((865674254456636 / 1000000000000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eps_transfer_8686 hRvM hfull hzero hfactored ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  have hstrong := hT₀ T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := by positivity
  nlinarith [frozen_8657_lt_8686]

/-- R-9383 follows monotonically from the stronger support-`19999/10000`
frozen transfer, with no additional analytic input. -/
theorem eps_transfer_9383
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family19999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hfactored : FactoredZeroKernelQuarticLowerBound Terminal9506.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((938313327050949 / 1000000000000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eps_transfer_9506 hRvM hfull hzero hfactored ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  have hstrong := hT₀ T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := by positivity
  nlinarith [frozen_9383_lt_9506]

/-! ## 5. Concrete zeta wrappers -/

private theorem zeta_N (T₁ T₂ : ℝ) :
    zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ :=
  zetaZeros_N zetaSeam T₁ T₂

private theorem zeta_N0s (T₁ T₂ : ℝ) :
    zetaZeroConfig.N0s T₁ T₂ = N0simple T₁ T₂ :=
  zetaZeros_N0s zetaSeam T₁ T₂

/-- Concrete-zeta R-8686 epsilon form.  Riemann--von Mangoldt and its local
count are discharged by the base repository; exactly the four per-support
structures remain explicit. -/
theorem zeta_eps_transfer_8686
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hfactored : FactoredZeroKernelQuarticLowerBound Terminal8686.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((86855250 / 100000000 : ℝ) - ε) * (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_8686 paperInputs_zeta.RvM hfull hzero hfactored)

/-- Concrete-zeta R-9506 epsilon form, conditional only on the three explicit
per-support structures. -/
theorem zeta_eps_transfer_9506
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hfactored : FactoredZeroKernelQuarticLowerBound Terminal9506.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((95063832187565 / 100000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_9506 paperInputs_zeta.RvM hfull hzero hfactored)

/-- Concrete-zeta R-8657, obtained monotonically from R-8686. -/
theorem zeta_eps_transfer_8657
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hfactored : FactoredZeroKernelQuarticLowerBound Terminal8686.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((865674254456636 / 1000000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_8657 paperInputs_zeta.RvM hfull hzero hfactored)

/-- Concrete-zeta R-9383, obtained monotonically from R-9506. -/
theorem zeta_eps_transfer_9383
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hfactored : FactoredZeroKernelQuarticLowerBound Terminal9506.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((938313327050949 / 1000000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_9383 paperInputs_zeta.RvM hfull hzero hfactored)

end QuarticTransfer
end Zeta85
end RH

end
