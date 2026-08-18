/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125Moments

open scoped BigOperators
open Set intervalIntegral MeasureTheory

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

def eBase : ℝ := baseL2 + sigma125 * jBase
def eCross : ℝ := 1 + sigma125 * jCross / 2
def eConst : ℝ := 1 + sigma125 * jConst
def qA : ℝ := eBase - 2 * eCross + eConst
def qB : ℝ := -2 * eBase + 2 * eCross
def qC : ℝ := eBase - target125 * sigma125
def qDisc : ℝ := qB ^ 2 - 4 * qA * qC

lemma qA_pos : 0 < qA := by
  norm_num [qA, eBase, eCross, eConst, baseL2, sigma125, jBase, jCross, jConst]

lemma qB_pos : 0 < qB := by
  norm_num [qB, eBase, eCross, baseL2, sigma125, jBase, jCross]

lemma qC_neg : qC < 0 := by
  norm_num [qC, eBase, baseL2, sigma125, jBase, target125]

lemma qAtOne_pos : 0 < qA + qB + qC := by
  norm_num [qA, qB, qC, eBase, eCross, eConst, baseL2, sigma125,
    jBase, jCross, jConst, target125]

lemma qDisc_pos : 0 < qDisc := by
  rw [qDisc]
  nlinarith [mul_pos qA_pos (neg_pos.mpr qC_neg)]

def t125 : ℝ := (-qB + Real.sqrt qDisc) / (2 * qA)

lemma t125_root : qA * t125 ^ 2 + qB * t125 + qC = 0 := by
  have hs : (Real.sqrt qDisc) ^ 2 = qDisc :=
    Real.sq_sqrt (le_of_lt qDisc_pos)
  rw [t125]
  field_simp [ne_of_gt qA_pos]
  rw [qDisc] at hs ⊢
  ring_nf at hs ⊢
  nlinarith

lemma t125_pos : 0 < t125 := by
  have hs0 : 0 ≤ Real.sqrt qDisc := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt qDisc) ^ 2 = qDisc :=
    Real.sq_sqrt (le_of_lt qDisc_pos)
  have hsq : qB ^ 2 < qDisc := by
    rw [qDisc]
    nlinarith [mul_pos qA_pos (neg_pos.mpr qC_neg)]
  have hnum : 0 < -qB + Real.sqrt qDisc := by
    nlinarith
  rw [t125]
  exact div_pos hnum (mul_pos (by norm_num) qA_pos)

lemma t125_lt_one : t125 < 1 := by
  have hs0 : 0 ≤ Real.sqrt qDisc := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt qDisc) ^ 2 = qDisc :=
    Real.sq_sqrt (le_of_lt qDisc_pos)
  have hrhs : 0 < 2 * qA + qB := by
    nlinarith [qAtOne_pos, qA_pos, qC_neg]
  have hsq : qDisc < (2 * qA + qB) ^ 2 := by
    rw [qDisc]
    nlinarith [mul_pos qA_pos qAtOne_pos]
  have hslt : Real.sqrt qDisc < 2 * qA + qB := by
    nlinarith
  rw [t125]
  apply (div_lt_iff₀ (mul_pos (by norm_num) qA_pos)).2
  linarith

lemma profile_energy_sub_target (t : ℝ) :
    ((1 - t) ^ 2 * eBase + 2 * t * (1 - t) * eCross + t ^ 2 * eConst) -
        target125 * sigma125 =
      qA * t ^ 2 + qB * t + qC := by
  simp only [qA, qB, qC]
  ring

theorem windowCost_125 :
    ∃ σ : ℝ, 1 < σ ∧ σ < 5 / 4 ∧
      SaturatedWindowCost σ target125 := by
  refine ⟨sigma125, by norm_num [sigma125], by norm_num [sigma125], ?_⟩
  refine ⟨profile125 t125, ?_, ?_, ?_⟩
  · intro s hs
    have hb := base125_pos hs
    have ht0 := t125_pos
    have ht1 := t125_lt_one
    simp only [profile125]
    nlinarith
  · rw [integral_profile125]
    norm_num
  · rw [integral_profile125, integral_profile125_sq, satJ_profile125]
    have hroot := t125_root
    have henergy := profile_energy_sub_target t125
    rw [hroot] at henergy
    simp only [eBase, eCross, eConst] at henergy
    nlinarith

end RationalWindow125
end Zeta85
end RH
