/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.AggregateComplexAlias

/-!
# Radial-shell alias cancellation

An even compact window cannot cross a half-period alias point.  The full
support is therefore split into symmetric radial shells lying strictly
between consecutive half-period radii.  Every shell is exactly disjoint from
all of its nonzero integer-period translates.
-/

open Filter Matrix Finset Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace RadialShellAlias

/-- A symmetric shell strictly between consecutive half-period radii has no
overlap with any nonzero integer-period translate. -/
theorem radialShell_shift_overlap_eq_zero
    (f : ℝ → ℝ) (L a b : ℝ) (k : ℕ)
    (hL : 0 < L)
    (ha : (k : ℝ) * L / 2 < a)
    (hb : b < ((k + 1 : ℕ) : ℝ) * L / 2)
    (hsupp : ∀ x : ℝ, f x ≠ 0 → a < |x| ∧ |x| < b)
    (m : ℤ) (hm : m ≠ 0) (u : ℝ) :
    f u * f (u - (m : ℝ) * L) = 0 := by
  by_cases hu : f u = 0
  · simp [hu]
  by_cases hv : f (u - (m : ℝ) * L) = 0
  · simp [hv]
  exfalso
  obtain ⟨hua, hub⟩ := hsupp u hu
  obtain ⟨hva, hvb⟩ :=
    hsupp (u - (m : ℝ) * L) hv
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have ha0 : 0 < a := by
    nlinarith [ha, hL]
  have hu_ne : u ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hua
    linarith
  have hv_ne : u - (m : ℝ) * L ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hva
    linarith
  have hb' : b < ((k : ℝ) + 1) * L / 2 := by
    norm_num at hb ⊢
    exact hb
  have hwidth : b - a < L := by
    nlinarith [ha, hb', hL]
  have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  have hshift_lower : L ≤ |(m : ℝ) * L| := by
    calc
      L = 1 * L := by ring
      _ ≤ |(m : ℝ)| * L :=
        mul_le_mul_of_nonneg_right hmabs hL.le
      _ = |(m : ℝ) * L| := by
        rw [abs_mul, abs_of_pos hL]
  have hdiff :
      u - (u - (m : ℝ) * L) = (m : ℝ) * L := by
    ring
  by_cases hu_pos : 0 < u
  · rw [abs_of_pos hu_pos] at hua hub
    by_cases hv_pos : 0 < u - (m : ℝ) * L
    · rw [abs_of_pos hv_pos] at hva hvb
      have habslt :
          |u - (u - (m : ℝ) * L)| < b - a := by
        rw [abs_lt]
        constructor <;> linarith
      rw [hdiff] at habslt
      linarith
    · have hv_neg : u - (m : ℝ) * L < 0 :=
        lt_of_le_of_ne (le_of_not_gt hv_pos) hv_ne
      rw [abs_of_neg hv_neg] at hva hvb
      have hdiff_pos : 0 < u - (u - (m : ℝ) * L) := by
        linarith
      have hlower :
          (k : ℝ) * L <
            |u - (u - (m : ℝ) * L)| := by
        rw [abs_of_pos hdiff_pos]
        nlinarith [ha, hua, hva]
      have hupper :
          |u - (u - (m : ℝ) * L)| <
            ((k : ℝ) + 1) * L := by
        rw [abs_of_pos hdiff_pos]
        nlinarith [hb', hub, hvb]
      rw [hdiff, abs_mul, abs_of_pos hL] at hlower hupper
      have hkabs : (k : ℝ) < |(m : ℝ)| := by
        exact (mul_lt_mul_right hL).mp hlower
      have habssucc : |(m : ℝ)| < (k : ℝ) + 1 := by
        exact (mul_lt_mul_right hL).mp hupper
      have hkabsInt : (k : ℤ) < |m| := by
        exact_mod_cast hkabs
      have habssuccInt : |m| < (k : ℤ) + 1 := by
        exact_mod_cast habssucc
      omega
  · have hu_neg : u < 0 :=
      lt_of_le_of_ne (le_of_not_gt hu_pos) hu_ne
    rw [abs_of_neg hu_neg] at hua hub
    by_cases hv_pos : 0 < u - (m : ℝ) * L
    · rw [abs_of_pos hv_pos] at hva hvb
      have hdiff_neg : u - (u - (m : ℝ) * L) < 0 := by
        linarith
      have hlower :
          (k : ℝ) * L <
            |u - (u - (m : ℝ) * L)| := by
        rw [abs_of_neg hdiff_neg]
        nlinarith [ha, hua, hva]
      have hupper :
          |u - (u - (m : ℝ) * L)| <
            ((k : ℝ) + 1) * L := by
        rw [abs_of_neg hdiff_neg]
        nlinarith [hb', hub, hvb]
      rw [hdiff, abs_mul, abs_of_pos hL] at hlower hupper
      have hkabs : (k : ℝ) < |(m : ℝ)| := by
        exact (mul_lt_mul_right hL).mp hlower
      have habssucc : |(m : ℝ)| < (k : ℝ) + 1 := by
        exact (mul_lt_mul_right hL).mp hupper
      have hkabsInt : (k : ℤ) < |m| := by
        exact_mod_cast hkabs
      have habssuccInt : |m| < (k : ℤ) + 1 := by
        exact_mod_cast habssucc
      omega
    · have hv_neg : u - (m : ℝ) * L < 0 :=
        lt_of_le_of_ne (le_of_not_gt hv_pos) hv_ne
      rw [abs_of_neg hv_neg] at hva hvb
      have habslt :
          |u - (u - (m : ℝ) * L)| < b - a := by
        rw [abs_lt]
        constructor <;> linarith
      rw [hdiff] at habslt
      linarith

/-- A finite family of smooth even radial-shell windows has exact collective
alias cancellation.  Different shells may cover the whole growing support;
only the half-period boundaries must remain outside their supports. -/
theorem aggregateAliasCancellation_of_radialShells
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T L : ℝ) (Λ : ι → ℝ) (f : ι → ℝ → ℝ)
    (shell : ι → ℕ) (a b : ι → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ r, 0 ≤ Λ r)
    (hsmooth : ∀ r,
      ContDiff ℝ 2 (fun u => (f r u : ℂ)))
    (hsuppBound : ∀ r u, Λ r < |u| → f r u = 0)
    (heven : ∀ r u, f r (-u) = f r u)
    (hshell : ∀ r x, f r x ≠ 0 →
      a r < |x| ∧ |x| < b r)
    (ha : ∀ r, (shell r : ℝ) * L / 2 < a r)
    (hb : ∀ r,
      b r < (((shell r) + 1 : ℕ) : ℝ) * L / 2) :
    AggregateComplexAlias.AggregateAliasCancellation T L f := by
  apply AggregateComplexAlias.aggregateAliasCancellation_of_pointwiseOverlap
    T L Λ f hL hΛ hsmooth hsuppBound heven
  · intro r z z' m hm
    exact AggregateComplexAlias.integrable_complexShiftOverlap
      (f r) (Λ r) ((m : ℝ) * L) (hΛ r)
      (hsmooth r) (hsuppBound r)
      (Complex.I * (z - z'))
  · intro m hm u
    apply Finset.sum_eq_zero
    intro r hr
    exact radialShell_shift_overlap_eq_zero
      (f r) L (a r) (b r) (shell r)
      hL (ha r) (hb r) (hshell r) m hm u

end RadialShellAlias
end Zeta85
end RH

end
