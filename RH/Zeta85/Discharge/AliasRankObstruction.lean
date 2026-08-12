/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Zeta23.ZeroSide

/-!
# Finite common-lattice alias rank obstruction

This is the finite linear-algebra core of the A2.1 finish-or-kill argument.
After removing an alias-free distinguished channel, a strictly positive
residual profile gives an invertible diagonal fiber.  A critical-count family
of remaining channels cannot produce that fiber if the sum of their individual
rank budgets is smaller than the number of lattice cells.

The theorem permits arbitrary signs and complex phases: only ranks enter.
-/

open Matrix Finset
open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace AliasRankObstruction

variable {K : Type*} [RCLike K]

/-- A diagonal fiber with no zero entry has full rank. -/
theorem rank_diagonal_full {N : ℕ} (w : Fin N → K)
    (hw : ∀ q, w q ≠ 0) : (diagonal w).rank = N := by
  rw [Matrix.rank_diagonal]
  simp [hw]

/-- No finite family whose total rank budget is below `N` can sum to a
full-rank diagonal `N × N` fiber. -/
theorem no_lowRank_sum_eq_full_diagonal
    {N : ℕ} {I : Type*} [DecidableEq I]
    (s : Finset I) (A : I → Matrix (Fin N) (Fin N) K)
    (budget : I → ℕ) (w : Fin N → K)
    (hrank : ∀ i ∈ s, (A i).rank ≤ budget i)
    (hbudget : ∑ i ∈ s, budget i < N)
    (hw : ∀ q, w q ≠ 0) :
    ∑ i ∈ s, A i ≠ diagonal w := by
  intro hsum
  have hle := Zeta23.ZeroSide.rank_sum_le s A budget hrank
  rw [hsum, rank_diagonal_full w hw] at hle
  omega

/-- A channel with `n` residue fibers is a sum of `n` rank-one outer
products and therefore has rank at most `n`. -/
theorem rank_channelFiber_le {N n : ℕ}
    (g : Fin n → Fin N → K) :
    (∑ r : Fin n, vecMulVec (g r) (fun q ↦ star (g r q))).rank ≤ n := by
  refine (Zeta23.ZeroSide.rank_sum_le Finset.univ
    (fun r ↦ vecMulVec (g r) (fun q ↦ star (g r q))) (fun _ ↦ 1) ?_).trans ?_
  · intro r _
    exact rank_vecMulVec_le _ _
  · simp

/-- Explicit rank-one fiber version: even arbitrary complex phases in the
vectors `g` cannot overcome a deficient total residue count. -/
theorem no_rankOne_fibers_eq_full_diagonal
    {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Finset I) (n : I → ℕ)
    (g : (i : I) → Fin (n i) → Fin N → K)
    (w : Fin N → K)
    (hbudget : ∑ i ∈ s, n i < N)
    (hw : ∀ q, w q ≠ 0) :
    ∑ i ∈ s, ∑ r : Fin (n i),
        vecMulVec (g i r) (fun q ↦ star (g i r q)) ≠ diagonal w := by
  apply no_lowRank_sum_eq_full_diagonal s
    (fun i ↦ ∑ r : Fin (n i), vecMulVec (g i r) (fun q ↦ star (g i r q))) n w
  · intro i _
    exact rank_channelFiber_le (g i)
  · exact hbudget
  · exact hw

/-- Matrix form of equations (13)--(16): if the full and distinguished
fibers are diagonal and their residual is nonzero in every cell, then a
below-full-rank complement decomposition is impossible. -/
theorem no_full_distinguished_complement
    {N : ℕ} {I : Type*} [DecidableEq I]
    (s : Finset I) (A : I → Matrix (Fin N) (Fin N) K)
    (budget : I → ℕ)
    (full distinguished : Matrix (Fin N) (Fin N) K)
    (v r : Fin N → K)
    (hrank : ∀ i ∈ s, (A i).rank ≤ budget i)
    (hbudget : ∑ i ∈ s, budget i < N)
    (hfull : full = diagonal v)
    (hdistinguished : distinguished = diagonal r)
    (hcomplement : full - distinguished = ∑ i ∈ s, A i)
    (hresidual : ∀ q, v q - r q ≠ 0) : False := by
  apply no_lowRank_sum_eq_full_diagonal s A budget (fun q ↦ v q - r q)
    hrank hbudget hresidual
  calc
    ∑ i ∈ s, A i = full - distinguished := hcomplement.symm
    _ = diagonal v - diagonal r := by rw [hfull, hdistinguished]
    _ = diagonal (fun q ↦ v q - r q) := by
      ext q q'
      by_cases hqq : q = q'
      · subst q'
        simp
      · simp [hqq]

/-- Fiber-rank form of the critical-count TDAC obstruction.  The distinguished
channel uses `n₀ > 0` cells out of `N`; the remaining channel budgets sum to
`N - n₀`, so they cannot synthesize a full-rank residual fiber. -/
theorem no_critical_complement
    {N n₀ : ℕ} (hn₀ : 0 < n₀) (hn₀N : n₀ ≤ N)
    {I : Type*} [DecidableEq I]
    (s : Finset I) (A : I → Matrix (Fin N) (Fin N) K)
    (budget : I → ℕ) (w : Fin N → K)
    (hrank : ∀ i ∈ s, (A i).rank ≤ budget i)
    (hcritical : ∑ i ∈ s, budget i = N - n₀)
    (hw : ∀ q, w q ≠ 0) :
    ∑ i ∈ s, A i ≠ diagonal w := by
  apply no_lowRank_sum_eq_full_diagonal s A budget w hrank
  · rw [hcritical]
    omega
  · exact hw

/-! ## Terminal arithmetic instantiations

These corollaries record only the independently replayed lattice counts.  The
analytic assertion that each residual fiber entry is nonzero remains an
explicit premise; it is certified in `verify/a2_1_tdac_rank.py` for the three
source profiles and is not reintroduced here as a transcendental Lean claim.
-/

/-- R-9506: `N = 19999`, `n₀ = 4999`, complement budget `15000`. -/
theorem no_r9506_complement
    {I : Type*} [DecidableEq I]
    (s : Finset I) (A : I → Matrix (Fin 19999) (Fin 19999) K)
    (budget : I → ℕ) (w : Fin 19999 → K)
    (hrank : ∀ i ∈ s, (A i).rank ≤ budget i)
    (hbudget : ∑ i ∈ s, budget i = 15000)
    (hw : ∀ q, w q ≠ 0) :
    ∑ i ∈ s, A i ≠ diagonal w := by
  exact no_critical_complement (N := 19999) (n₀ := 4999)
    (by norm_num) (by norm_num) s A budget w hrank (by norm_num [hbudget]) hw

/-- R-8686: `N = 14999`, `n₀ = 4999`, complement budget `10000`. -/
theorem no_r8686_complement
    {I : Type*} [DecidableEq I]
    (s : Finset I) (A : I → Matrix (Fin 14999) (Fin 14999) K)
    (budget : I → ℕ) (w : Fin 14999 → K)
    (hrank : ∀ i ∈ s, (A i).rank ≤ budget i)
    (hbudget : ∑ i ∈ s, budget i = 10000)
    (hw : ∀ q, w q ≠ 0) :
    ∑ i ∈ s, A i ≠ diagonal w := by
  exact no_critical_complement (N := 14999) (n₀ := 4999)
    (by norm_num) (by norm_num) s A budget w hrank (by norm_num [hbudget]) hw

/-- File 15: `N = 1499999`, `n₀ = 499000`, complement budget `1000999`. -/
theorem no_file15_complement
    {I : Type*} [DecidableEq I]
    (s : Finset I) (A : I → Matrix (Fin 1499999) (Fin 1499999) K)
    (budget : I → ℕ) (w : Fin 1499999 → K)
    (hrank : ∀ i ∈ s, (A i).rank ≤ budget i)
    (hbudget : ∑ i ∈ s, budget i = 1000999)
    (hw : ∀ q, w q ≠ 0) :
    ∑ i ∈ s, A i ≠ diagonal w := by
  exact no_critical_complement (N := 1499999) (n₀ := 499000)
    (by norm_num) (by norm_num) s A budget w hrank (by norm_num [hbudget]) hw

end AliasRankObstruction
end Zeta85
end RH

end
