/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.IsometricKernel

/-!
# Aligned virtual-channel mixing

An orthogonal synthesis turns virtual window channels into physical channels.
The complete pointwise square energy is unchanged, while a coherent weighted
sum of the physical channels recovers any chosen virtual channel exactly.
This is the finite frame dilation needed to separate the stability profile
from the top-hat profile before the zero contraction is formed.
-/

open Matrix Finset
open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace VirtualChannelMixer

/-- A finite real orthogonal synthesis matrix.  Columns are the virtual
channels and rows are the physical channels. -/
structure Data (ι : Type*) [Fintype ι] [DecidableEq ι] where
  matrix : Matrix ι ι ℝ
  orthogonal : matrix.transpose * matrix = 1

/-- Synthesize physical channels from virtual channels. -/
def synthesize
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (virtual : ι → α → ℝ) : ι → α → ℝ :=
  fun j x => ∑ r : ι, C.matrix j r * virtual r x

/-- Analyze physical channels against one column of the synthesis matrix. -/
def analyze
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (physical : ι → α → ℝ) : ι → α → ℝ :=
  fun r x => ∑ j : ι, C.matrix j r * physical j x

/-- Orthogonal analysis exactly recovers every virtual channel after
synthesis. -/
theorem analyze_synthesize
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (virtual : ι → α → ℝ) (r : ι) (x : α) :
    analyze C (synthesize C virtual) r x = virtual r x := by
  unfold analyze synthesize
  calc
    (∑ j : ι, C.matrix j r *
        ∑ s : ι, C.matrix j s * virtual s x) =
      ∑ j : ι, ∑ s : ι,
        (C.matrix j r * C.matrix j s) * virtual s x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = ∑ s : ι, ∑ j : ι,
        (C.matrix j r * C.matrix j s) * virtual s x := by
      rw [Finset.sum_comm]
    _ = ∑ s : ι,
        (∑ j : ι, C.matrix j r * C.matrix j s) *
          virtual s x := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_mul]
    _ = ∑ s : ι, (1 : Matrix ι ι ℝ) r s * virtual s x := by
      apply Finset.sum_congr rfl
      intro s _
      have hentry := congrFun (congrFun C.orthogonal r) s
      have hsum :
          (∑ j : ι, C.matrix j r * C.matrix j s) =
            (1 : Matrix ι ι ℝ) r s := by
        simpa [Matrix.mul_apply] using hentry
      rw [hsum]
    _ = virtual r x := by
      simp

/-- Pointwise Parseval identity: synthesis preserves the entire square
energy after the channel sum has been taken. -/
theorem pointwise_parseval
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (virtual : ι → α → ℝ) (x : α) :
    (∑ j : ι, (synthesize C virtual j x) ^ 2) =
      ∑ r : ι, (virtual r x) ^ 2 := by
  calc
    (∑ j : ι, (synthesize C virtual j x) ^ 2) =
      ∑ j : ι, (∑ r : ι, C.matrix j r * virtual r x) *
        synthesize C virtual j x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_two]
      rfl
    _ = ∑ j : ι, ∑ r : ι,
        (C.matrix j r * virtual r x) *
          synthesize C virtual j x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ r : ι, ∑ j : ι,
        (C.matrix j r * virtual r x) *
          synthesize C virtual j x := by
      rw [Finset.sum_comm]
    _ = ∑ r : ι, virtual r x *
        (∑ j : ι, C.matrix j r * synthesize C virtual j x) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ r : ι, virtual r x * virtual r x := by
      apply Finset.sum_congr rfl
      intro r _
      change virtual r x * analyze C (synthesize C virtual) r x = _
      rw [analyze_synthesize]
    _ = ∑ r : ι, (virtual r x) ^ 2 := by
      simp only [pow_two]

/-- A family supported in a common set remains supported there after
orthogonal synthesis. -/
theorem synthesize_eq_zero
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (virtual : ι → α → ℝ)
    (j : ι) (x : α) (hx : ∀ r : ι, virtual r x = 0) :
    synthesize C virtual j x = 0 := by
  simp [synthesize, hx]

/-- Put a single window into one virtual channel. -/
def singleChannel
    {ι α : Type*} [DecidableEq ι]
    (r : ι) (f : α → ℝ) : ι → α → ℝ :=
  fun s x => if s = r then f x else 0

/-- Synthesis of a single virtual window exposes its exact coefficient in
every physical channel. -/
theorem synthesize_singleChannel
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (r j : ι) (f : α → ℝ) (x : α) :
    synthesize C (singleChannel r f) j x =
      C.matrix j r * f x := by
  simp [synthesize, singleChannel]

/-- The coherent physical-channel sum recovers the distinguished window
with no loss. -/
theorem coherent_singleChannel
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (r : ι) (f : α → ℝ) (x : α) :
    analyze C (synthesize C (singleChannel r f)) r x = f x := by
  rw [analyze_synthesize]
  simp [singleChannel]

/-- A single virtual window contributes exactly its original square energy
to all synthesized physical channels together. -/
theorem singleChannel_parseval
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (r : ι) (f : α → ℝ) (x : α) :
    (∑ j : ι, (synthesize C (singleChannel r f) j x) ^ 2) =
      (f x) ^ 2 := by
  rw [pointwise_parseval]
  simp [singleChannel]

/-- The unweighted coherent sum of physical channels carries the column-sum
amplitude of a single virtual channel. -/
theorem sum_synthesize_singleChannel
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (r : ι) (f : α → ℝ) (x : α) :
    (∑ j : ι, synthesize C (singleChannel r f) j x) =
      (∑ j : ι, C.matrix j r) * f x := by
  simp only [synthesize_singleChannel, Finset.sum_mul]

/-- A rational three-channel orthogonal mixer.  Its first virtual column is
within two parts in 326041 of the maximally coherent flat column, avoiding
all square-root bookkeeping in the later certified inequalities. -/
def rationalMixer3 : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![329 / 571, -330 / 571, 330 / 571],
    ![330 / 571, -121 / 571, -450 / 571],
    ![330 / 571, 450 / 571, 121 / 571]]

theorem rationalMixer3_orthogonal :
    rationalMixer3.transpose * rationalMixer3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rationalMixer3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Certified three-channel synthesis data. -/
def rationalData3 : Data (Fin 3) where
  matrix := rationalMixer3
  orthogonal := rationalMixer3_orthogonal

theorem rationalMixer3_firstColumn_sum :
    (∑ j : Fin 3, rationalMixer3 j 0) = (989 : ℝ) / 571 := by
  norm_num [rationalMixer3, Fin.sum_univ_succ]

/-- The rational three-channel coherent gain is already above 2.9999 in
squared amplitude. -/
theorem rationalMixer3_coherent_gain :
    (29999 : ℝ) / 10000 <
      (∑ j : Fin 3, rationalMixer3 j 0) ^ 2 := by
  rw [rationalMixer3_firstColumn_sum]
  norm_num

/-- The four-channel Walsh-Hadamard mixer, normalized by one half. -/
def hadamardMixer4 : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1 / 2, 1 / 2, 1 / 2, 1 / 2],
    ![1 / 2, -1 / 2, 1 / 2, -1 / 2],
    ![1 / 2, 1 / 2, -1 / 2, -1 / 2],
    ![1 / 2, -1 / 2, -1 / 2, 1 / 2]]

theorem hadamardMixer4_orthogonal :
    hadamardMixer4.transpose * hadamardMixer4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamardMixer4, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Certified four-channel synthesis data. -/
def hadamardData4 : Data (Fin 4) where
  matrix := hadamardMixer4
  orthogonal := hadamardMixer4_orthogonal

theorem hadamardMixer4_firstColumn_sum :
    (∑ j : Fin 4, hadamardMixer4 j 0) = (2 : ℝ) := by
  norm_num [hadamardMixer4, Fin.sum_univ_succ]

/-- Four aligned physical channels carry the exact optimal coherent squared
amplitude gain four. -/
theorem hadamardMixer4_coherent_gain :
    (∑ j : Fin 4, hadamardMixer4 j 0) ^ 2 = (4 : ℝ) := by
  rw [hadamardMixer4_firstColumn_sum]
  norm_num

end VirtualChannelMixer
end Zeta85
end RH

end
