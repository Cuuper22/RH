/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/AliasFallback.lean — exact rational audit of the A2.2
alias-free interval fallback.

An interval restriction has the honest normalization `C = H / σ`, where
`H` has mean one.  Thus, for `Y = H - I`,

  C - I = (Y - (σ - 1) I) / σ.

The stability tail is consequently supported on `Y > σ - 1`, not on
`Y > 0`.  This file takes the paper-derived rational closed moment formulas
for the quadratic-profile restriction as definitions and constructs a
five-atom rational law with the same first four values.  It does not prove
the analytic equality of those definitions with Mathlib integrals or the
RS specialization.  At each support relevant to A2.2 every atom lies below
`σ - 1`; at the five parameter pairs checked below every weight is in fact
strictly larger than `1/25`.  Hence the corrected tail is exactly zero even
before the exceptional-rank trim, conditional on those closed formulas.

Everything in this file is proved by finite rational arithmetic, with no
analytic hypotheses.
-/
import Mathlib

namespace RH
namespace Zeta85
namespace AliasFallback

/-! ## 1. A generic five-atom reconstruction through degree four -/

/-- The five rational centered atoms.  Their intrinsic eigenvalues `1 + y`
are respectively `3/10, 4/5, 9/10, 13/10, 7/5`, so all are nonnegative. -/
def atom0 : ℚ := -7 / 10
def atom1 : ℚ := -1 / 5
def atom2 : ℚ := -1 / 10
def atom3 : ℚ := 3 / 10
def atom4 : ℚ := 2 / 5

/- The rows below are the inverse of the Vandermonde matrix
`(atom_j ^ k)_{0 ≤ k,j ≤ 4}`.  Its determinant is `99/500000`.  Since the
first two moments are fixed as `m₀ = 1`, `m₁ = 0`, the `m₁` columns have
already been suppressed in the definitions of the weights. -/

def weight0 (m2 m3 m4 : ℚ) : ℚ :=
  2 / 275 - 7 / 33 * m2 - 40 / 33 * m3 + 100 / 33 * m4

def weight1 (m2 m3 m4 : ℚ) : ℚ :=
  -14 / 25 + 74 / 3 * m2 - 20 / 3 * m3 - 200 / 3 * m4

def weight2 (m2 m3 m4 : ℚ) : ℚ :=
  7 / 5 - 185 / 6 * m2 + 50 / 3 * m3 + 250 / 3 * m4

def weight3 (m2 m3 m4 : ℚ) : ℚ :=
  7 / 25 + 17 / 2 * m2 - 30 * m3 - 50 * m4

def weight4 (m2 m3 m4 : ℚ) : ℚ :=
  -7 / 55 - 70 / 33 * m2 + 700 / 33 * m3 + 1000 / 33 * m4

/-- The `k`th moment of the rational five-atom law. -/
def reconstructedMoment (m2 m3 m4 : ℚ) (k : ℕ) : ℚ :=
  weight0 m2 m3 m4 * atom0 ^ k +
  weight1 m2 m3 m4 * atom1 ^ k +
  weight2 m2 m3 m4 * atom2 ^ k +
  weight3 m2 m3 m4 * atom3 ^ k +
  weight4 m2 m3 m4 * atom4 ^ k

/-- The inverse-Vandermonde calculation: for arbitrary rational values of
the second through fourth moments, the five weights reconstruct
`(m₀,m₁,m₂,m₃,m₄) = (1,0,m2,m3,m4)` exactly. -/
theorem moment_reconstruction (m2 m3 m4 : ℚ) :
    reconstructedMoment m2 m3 m4 0 = 1 ∧
    reconstructedMoment m2 m3 m4 1 = 0 ∧
    reconstructedMoment m2 m3 m4 2 = m2 ∧
    reconstructedMoment m2 m3 m4 3 = m3 ∧
    reconstructedMoment m2 m3 m4 4 = m4 := by
  constructor
  · norm_num [reconstructedMoment, weight0, weight1, weight2, weight3, weight4,
      atom0, atom1, atom2, atom3, atom4]
    ring
  constructor
  · norm_num [reconstructedMoment, weight0, weight1, weight2, weight3, weight4,
      atom0, atom1, atom2, atom3, atom4]
    ring
  constructor
  · norm_num [reconstructedMoment, weight0, weight1, weight2, weight3, weight4,
      atom0, atom1, atom2, atom3, atom4]
    ring
  constructor
  · norm_num [reconstructedMoment, weight0, weight1, weight2, weight3, weight4,
      atom0, atom1, atom2, atom3, atom4]
    ring
  · norm_num [reconstructedMoment, weight0, weight1, weight2, weight3, weight4,
      atom0, atom1, atom2, atom3, atom4]
    ring

/-- The determinant of the five-node Vandermonde matrix. -/
theorem vandermonde_det :
    (atom1 - atom0) * (atom2 - atom0) * (atom3 - atom0) * (atom4 - atom0) *
      (atom2 - atom1) * (atom3 - atom1) * (atom4 - atom1) *
      (atom3 - atom2) * (atom4 - atom2) * (atom4 - atom3) = 99 / 500000 := by
  norm_num [atom0, atom1, atom2, atom3, atom4]

/-! ## 2. Exact A2.2 moments for the quadratic restriction -/

/-- The relative block width `δ = μ/σ`. -/
def delta (σ μ : ℚ) : ℚ := μ / σ

/-- The quadratic coefficient in
`r(t) = 1 + b t + c (t² - 1/12)`. -/
def cCoeff (σ μ : ℚ) : ℚ :=
  -(2028 / 1031) * delta σ μ ^ 2

/-- The exact square of the linear coefficient `b`.  All moments through
degree four involve `b` only through `b²`. -/
def bSq (σ μ : ℚ) : ℚ :=
  (4056 / 1031) ^ 2 * delta σ μ ^ 2 * (1 - delta σ μ ^ 2) / 12

def q2 (σ μ : ℚ) : ℚ :=
  bSq σ μ / 12 + cCoeff σ μ ^ 2 / 180

def q3 (σ μ : ℚ) : ℚ :=
  bSq σ μ * cCoeff σ μ / 60 + cCoeff σ μ ^ 3 / 3780

def q4 (σ μ : ℚ) : ℚ :=
  bSq σ μ ^ 2 / 80 + 11 * bSq σ μ * cCoeff σ μ ^ 2 / 2520 +
    cCoeff σ μ ^ 4 / 15120

def h0 (σ μ : ℚ) : ℚ :=
  1 / 3 + cCoeff σ μ / 90 - bSq σ μ / 60 - cCoeff σ μ ^ 2 / 3780

def h1 (σ μ : ℚ) : ℚ :=
  cCoeff σ μ / 180 + bSq σ μ / 60 + cCoeff σ μ ^ 2 / 540 -
    bSq σ μ * cCoeff σ μ / 560 + cCoeff σ μ ^ 3 / 45360

def h2 (σ μ : ℚ) : ℚ :=
  bSq σ μ / 30 + 2 * cCoeff σ μ ^ 2 / 945 +
    bSq σ μ * cCoeff σ μ / 168 + cCoeff σ μ ^ 3 / 5670 -
    bSq σ μ ^ 2 / 420 - bSq σ μ * cCoeff σ μ ^ 2 / 2520 -
    cCoeff σ μ ^ 4 / 748440

def dCross (σ μ : ℚ) : ℚ :=
  -bSq σ μ / 60 - cCoeff σ μ ^ 2 / 3780 -
    bSq σ μ * cCoeff σ μ / 280 + cCoeff σ μ ^ 3 / 22680 +
    bSq σ μ ^ 2 / 336 + bSq σ μ * cCoeff σ μ ^ 2 / 7560 +
    19 * cCoeff σ μ ^ 4 / 1496880

def rContraction (σ μ : ℚ) : ℚ :=
  7 / 60 + cCoeff σ μ / 90 - 23 * bSq σ μ / 2520 +
    29 * cCoeff σ μ ^ 2 / 45360 - bSq σ μ * cCoeff σ μ / 648 +
    cCoeff σ μ ^ 3 / 149688 + 83 * bSq σ μ ^ 2 / 181440 +
    31 * bSq σ μ * cCoeff σ μ ^ 2 / 1197504 +
    23 * cCoeff σ μ ^ 4 / 116756640

def xContraction (σ μ : ℚ) : ℚ :=
  1 / 30 - bSq σ μ / 420 - cCoeff σ μ ^ 2 / 7560 +
    cCoeff σ μ ^ 3 / 311850 + bSq σ μ ^ 2 / 10080 -
    bSq σ μ * cCoeff σ μ ^ 2 / 332640 +
    cCoeff σ μ ^ 4 / 2432430

/-- The exact centered second moment of the intrinsic mean-one block `H`. -/
def intrinsicM2 (σ μ : ℚ) : ℚ :=
  q2 σ μ + μ ^ 2 * h0 σ μ

/-- The exact centered third moment of the intrinsic mean-one block `H`. -/
def intrinsicM3 (σ μ : ℚ) : ℚ :=
  q3 σ μ + 3 * μ ^ 2 * h1 σ μ

/-- The exact centered fourth moment of the intrinsic mean-one block `H`. -/
def intrinsicM4 (σ μ : ℚ) : ℚ :=
  q4 σ μ + 4 * μ ^ 2 * h2 σ μ + 2 * μ ^ 2 * dCross σ μ +
    2 * μ ^ 4 * rContraction σ μ + μ ^ 4 * xContraction σ μ

/-- The five weights specialized to the paper-derived A2.2 closed moments. -/
def A2WeightsAbove (σ μ lower : ℚ) : Prop :=
  lower < weight0 (intrinsicM2 σ μ) (intrinsicM3 σ μ) (intrinsicM4 σ μ) ∧
  lower < weight1 (intrinsicM2 σ μ) (intrinsicM3 σ μ) (intrinsicM4 σ μ) ∧
  lower < weight2 (intrinsicM2 σ μ) (intrinsicM3 σ μ) (intrinsicM4 σ μ) ∧
  lower < weight3 (intrinsicM2 σ μ) (intrinsicM3 σ μ) (intrinsicM4 σ μ) ∧
  lower < weight4 (intrinsicM2 σ μ) (intrinsicM3 σ μ) (intrinsicM4 σ μ)

/-! ## 3. Exact positivity at every A2.2 parameter pair -/

theorem weights_gt_one_25_143 :
    A2WeightsAbove (143 / 100) (499 / 1000) (1 / 25) := by
  norm_num [A2WeightsAbove, intrinsicM2, intrinsicM3, intrinsicM4,
    weight0, weight1, weight2, weight3, weight4, q2, q3, q4, h0, h1, h2,
    dCross, rContraction, xContraction, bSq, cCoeff, delta]

theorem weights_gt_one_25_1499999 :
    A2WeightsAbove (1499999 / 1000000) (499 / 1000) (1 / 25) := by
  norm_num [A2WeightsAbove, intrinsicM2, intrinsicM3, intrinsicM4,
    weight0, weight1, weight2, weight3, weight4, q2, q3, q4, h0, h1, h2,
    dCross, rContraction, xContraction, bSq, cCoeff, delta]

theorem weights_gt_one_25_14999 :
    A2WeightsAbove (14999 / 10000) (4999 / 10000) (1 / 25) := by
  norm_num [A2WeightsAbove, intrinsicM2, intrinsicM3, intrinsicM4,
    weight0, weight1, weight2, weight3, weight4, q2, q3, q4, h0, h1, h2,
    dCross, rContraction, xContraction, bSq, cCoeff, delta]

theorem weights_gt_one_25_19999 :
    A2WeightsAbove (19999 / 10000) (4999 / 10000) (1 / 25) := by
  norm_num [A2WeightsAbove, intrinsicM2, intrinsicM3, intrinsicM4,
    weight0, weight1, weight2, weight3, weight4, q2, q3, q4, h0, h1, h2,
    dCross, rContraction, xContraction, bSq, cCoeff, delta]

theorem weights_gt_one_25_endpoint_two :
    A2WeightsAbove 2 (1 / 2) (1 / 25) := by
  norm_num [A2WeightsAbove, intrinsicM2, intrinsicM3, intrinsicM4,
    weight0, weight1, weight2, weight3, weight4, q2, q3, q4, h0, h1, h2,
    dCross, rContraction, xContraction, bSq, cCoeff, delta]

/-! ## 4. Support and the cycle-3 normalization -/

/-- Every intrinsic atom is a permissible nonnegative Gram eigenvalue. -/
theorem intrinsic_atoms_nonnegative :
    0 ≤ 1 + atom0 ∧ 0 ≤ 1 + atom1 ∧ 0 ≤ 1 + atom2 ∧
      0 ≤ 1 + atom3 ∧ 0 ≤ 1 + atom4 := by
  norm_num [atom0, atom1, atom2, atom3, atom4]

/-- `2/5` is the largest of the five centered atoms. -/
theorem atoms_le_two_fifths :
    atom0 ≤ 2 / 5 ∧ atom1 ≤ 2 / 5 ∧ atom2 ≤ 2 / 5 ∧
      atom3 ≤ 2 / 5 ∧ atom4 = 2 / 5 := by
  norm_num [atom0, atom1, atom2, atom3, atom4]

/-- All five centered atoms lie strictly below the corrected threshold
`σ - 1`. -/
def AtomsBelowThreshold (σ : ℚ) : Prop :=
  atom0 < σ - 1 ∧ atom1 < σ - 1 ∧ atom2 < σ - 1 ∧
    atom3 < σ - 1 ∧ atom4 < σ - 1

theorem atoms_below_143 : AtomsBelowThreshold (143 / 100) := by
  norm_num [AtomsBelowThreshold, atom0, atom1, atom2, atom3, atom4]

theorem atoms_below_1499999 : AtomsBelowThreshold (1499999 / 1000000) := by
  norm_num [AtomsBelowThreshold, atom0, atom1, atom2, atom3, atom4]

theorem atoms_below_14999 : AtomsBelowThreshold (14999 / 10000) := by
  norm_num [AtomsBelowThreshold, atom0, atom1, atom2, atom3, atom4]

theorem atoms_below_19999 : AtomsBelowThreshold (19999 / 10000) := by
  norm_num [AtomsBelowThreshold, atom0, atom1, atom2, atom3, atom4]

theorem atoms_below_endpoint_two : AtomsBelowThreshold 2 := by
  norm_num [AtomsBelowThreshold, atom0, atom1, atom2, atom3, atom4]

/-- The centered eigenvalue after the honest cycle-3 normalization
`C = H / σ`. -/
def actualCentered (σ y : ℚ) : ℚ := (1 + y) / σ - 1

/-- The exact cycle-3 scaling identity. -/
theorem cycle3_scaling_identity (σ y : ℚ) (hσ : σ ≠ 0) :
    actualCentered σ y = (y - (σ - 1)) / σ := by
  unfold actualCentered
  field_simp [hσ]
  ring

/-- An intrinsic atom below `σ - 1` becomes an actual eigenvalue strictly
below one. -/
theorem actualCentered_neg_of_below {σ y : ℚ} (hσ : 0 < σ)
    (hy : y < σ - 1) : actualCentered σ y < 0 := by
  rw [cycle3_scaling_identity σ y hσ.ne']
  exact div_neg_of_neg_of_pos (sub_neg.mpr hy) hσ

/-- Expected corrected positive-square tail of the rational law. -/
def correctedTail (σ m2 m3 m4 : ℚ) : ℚ :=
  weight0 m2 m3 m4 * (max (actualCentered σ atom0) 0) ^ 2 +
  weight1 m2 m3 m4 * (max (actualCentered σ atom1) 0) ^ 2 +
  weight2 m2 m3 m4 * (max (actualCentered σ atom2) 0) ^ 2 +
  weight3 m2 m3 m4 * (max (actualCentered σ atom3) 0) ^ 2 +
  weight4 m2 m3 m4 * (max (actualCentered σ atom4) 0) ^ 2

/-- At strict support `1.4999`, the moment-matching law has exactly zero
honest tail, before any trim. -/
theorem corrected_tail_zero_14999 :
    correctedTail (14999 / 10000)
      (intrinsicM2 (14999 / 10000) (4999 / 10000))
      (intrinsicM3 (14999 / 10000) (4999 / 10000))
      (intrinsicM4 (14999 / 10000) (4999 / 10000)) = 0 := by
  norm_num [correctedTail, actualCentered, atom0, atom1, atom2, atom3, atom4]

/-- At strict support `1.9999`, the moment-matching law has exactly zero
honest tail, before any trim. -/
theorem corrected_tail_zero_19999 :
    correctedTail (19999 / 10000)
      (intrinsicM2 (19999 / 10000) (4999 / 10000))
      (intrinsicM3 (19999 / 10000) (4999 / 10000))
      (intrinsicM4 (19999 / 10000) (4999 / 10000)) = 0 := by
  norm_num [correctedTail, actualCentered, atom0, atom1, atom2, atom3, atom4]

end AliasFallback
end Zeta85
end RH
