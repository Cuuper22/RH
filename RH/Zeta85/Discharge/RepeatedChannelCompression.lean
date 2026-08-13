/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.VirtualChannelMixer

/-!
# Repeated aligned-channel compression

Repeat one virtual mixer column independently across every common modulation
label.  The resulting matrix is an exact isometry from the label space into
the physical channel-label space, and its coherent contraction recovers the
chosen virtual atom at each label.
-/

open Matrix Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace RepeatedChannelCompression

open VirtualChannelMixer

/-- Repeat one virtual column of an orthogonal mixer across all aligned
modulation labels. -/
def matrix
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (C : Data ι) (r : ι) : Matrix (ι × κ) κ ℂ :=
  fun jk k =>
    if jk.2 = k then (C.matrix jk.1 r : ℂ) else 0

/-- Repeating an orthogonal mixer column across labels is still an exact
isometric compression. -/
theorem isometry
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (C : Data ι) (r : ι) :
    (matrix C r)ᴴ * matrix C r = 1 := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    have hentry :
        (C.matrix.transpose * C.matrix) r r =
          (1 : Matrix ι ι ℝ) r r := by
      exact congrFun (congrFun C.orthogonal r) r
    have hsumReal :
        (∑ j : ι, C.matrix j r * C.matrix j r) = (1 : ℝ) := by
      simpa [Matrix.mul_apply] using hentry
    have hsumComplex :=
      congrArg (fun y : ℝ => (y : ℂ)) hsumReal
    push_cast at hsumComplex
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, matrix,
      Fintype.sum_prod_type] using hsumComplex
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    rw [show (1 : Matrix κ κ ℂ) a b = 0 by simp [hab]]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    by_cases hka : k = a
    · subst k
      simp [matrix, hab]
    · simp [matrix, hka]

/-- Every coefficient of the repeated compression is real. -/
theorem real_entries
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (C : Data ι) (r : ι) (jk : ι × κ) (k : κ) :
    star (matrix C r jk k) = matrix C r jk k := by
  unfold matrix
  split_ifs <;> simp

/-- Synthesize one complex virtual atom vector independently at every
modulation label. -/
def physicalAtom
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (C : Data ι) (virtual : ι → κ → ℂ) :
    ι × κ → ℂ :=
  fun jk => synthesizeComplex C (fun r => virtual r jk.2) jk.1

/-- The repeated compression recovers the selected virtual atom exactly at
each aligned modulation label. -/
theorem recover_virtual_atom
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (C : Data ι) (r : ι) (virtual : ι → κ → ℂ) (k : κ) :
    (∑ jk : ι × κ, matrix C r jk k * physicalAtom C virtual jk) =
      virtual r k := by
  rw [Fintype.sum_prod_type]
  simp only [matrix, physicalAtom]
  have hcollapse : ∀ j : ι,
      (∑ k' : κ,
        (if k' = k then (C.matrix j r : ℂ) else 0) *
          synthesizeComplex C (fun s => virtual s k') j) =
        (C.matrix j r : ℂ) *
          synthesizeComplex C (fun s => virtual s k) j := by
    intro j
    simp
  simp_rw [hcollapse]
  change analyzeComplex C
    (synthesizeComplex C (fun s => virtual s k)) r = virtual r k
  exact analyzeComplex_synthesizeComplex C _ r

/-- Select a possibly different virtual mixer column at every aligned
modulation label. -/
def routedMatrix
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (C : Data ι) (selected : κ → ι) : Matrix (ι × κ) κ ℂ :=
  fun jk k =>
    if jk.2 = k then (C.matrix jk.1 (selected k) : ℂ) else 0

/-- Label-dependent column selection remains an exact isometry because
different labels have disjoint physical coordinates. -/
theorem routed_isometry
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (C : Data ι) (selected : κ → ι) :
    (routedMatrix C selected)ᴴ * routedMatrix C selected = 1 := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    have hentry :=
      congrFun (congrFun C.orthogonal (selected a)) (selected a)
    have hsumReal :
        (∑ j : ι,
          C.matrix j (selected a) * C.matrix j (selected a)) =
            (1 : ℝ) := by
      simpa [Matrix.mul_apply] using hentry
    have hsumComplex :=
      congrArg (fun y : ℝ => (y : ℂ)) hsumReal
    push_cast at hsumComplex
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, routedMatrix,
      Fintype.sum_prod_type] using hsumComplex
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    rw [show (1 : Matrix κ κ ℂ) a b = 0 by simp [hab]]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    by_cases hka : k = a
    · subst k
      simp [routedMatrix, hab]
    · simp [routedMatrix, hka]

/-- Every routed compression coefficient is real. -/
theorem routed_real_entries
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (C : Data ι) (selected : κ → ι) (jk : ι × κ) (k : κ) :
    star (routedMatrix C selected jk k) =
      routedMatrix C selected jk k := by
  unfold routedMatrix
  split_ifs <;> simp

/-- Routed compression recovers the selected virtual atom independently at
each modulation label. -/
theorem recover_routed_virtual_atom
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (C : Data ι) (selected : κ → ι)
    (virtual : ι → κ → ℂ) (k : κ) :
    (∑ jk : ι × κ,
      routedMatrix C selected jk k * physicalAtom C virtual jk) =
        virtual (selected k) k := by
  rw [Fintype.sum_prod_type]
  simp only [routedMatrix, physicalAtom]
  have hcollapse : ∀ j : ι,
      (∑ k' : κ,
        (if k' = k then (C.matrix j (selected k) : ℂ) else 0) *
          synthesizeComplex C (fun s => virtual s k') j) =
        (C.matrix j (selected k) : ℂ) *
          synthesizeComplex C (fun s => virtual s k) j := by
    intro j
    simp
  simp_rw [hcollapse]
  change analyzeComplex C
    (synthesizeComplex C (fun s => virtual s k)) (selected k) =
      virtual (selected k) k
  exact analyzeComplex_synthesizeComplex C _ (selected k)

end RepeatedChannelCompression
end Zeta85
end RH

end
