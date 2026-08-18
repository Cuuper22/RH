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

open MeasureTheory Filter Matrix Finset Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace RadialShellAlias

/-- The distance between two points in the same half-period radial shell is
strictly smaller than one period. -/
theorem radialShell_sameSign_distance_lt_period
    (L a b x y : ℝ) (k : ℕ)
    (hL : 0 < L)
    (ha : (k : ℝ) * L / 2 < a)
    (hb : b < ((k + 1 : ℕ) : ℝ) * L / 2)
    (hxa : a < |x|) (hxb : |x| < b)
    (hya : a < |y|) (hyb : |y| < b)
    (hsign : (0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) :
    |x - y| < L := by
  have hb' : b < ((k : ℝ) + 1) * L / 2 := by
    norm_num at hb ⊢
    exact hb
  rcases hsign with hpos | hneg
  · rw [abs_of_pos hpos.1] at hxa hxb
    rw [abs_of_pos hpos.2] at hya hyb
    rw [abs_lt]
    constructor <;> nlinarith [ha, hb', hL]
  · rw [abs_of_neg hneg.1] at hxa hxb
    rw [abs_of_neg hneg.2] at hya hyb
    rw [abs_lt]
    constructor <;> nlinarith [ha, hb', hL]

/-- The distance between two points in opposite halves of the same shell
lies strictly between consecutive integer multiples of the period. -/
theorem radialShell_oppositeSign_distance_between
    (L a b x y : ℝ) (k : ℕ)
    (hL : 0 < L)
    (ha : (k : ℝ) * L / 2 < a)
    (hb : b < ((k + 1 : ℕ) : ℝ) * L / 2)
    (hxa : a < |x|) (hxb : |x| < b)
    (hya : a < |y|) (hyb : |y| < b)
    (hsign : (0 < x ∧ y < 0) ∨ (x < 0 ∧ 0 < y)) :
    (k : ℝ) * L < |x - y| ∧
      |x - y| < ((k : ℝ) + 1) * L := by
  have hb' : b < ((k : ℝ) + 1) * L / 2 := by
    norm_num at hb ⊢
    exact hb
  rcases hsign with hpn | hnp
  · rw [abs_of_pos hpn.1] at hxa hxb
    rw [abs_of_neg hpn.2] at hya hyb
    have hxy : 0 < x - y := by linarith
    rw [abs_of_pos hxy]
    constructor <;> nlinarith [ha, hb', hL]
  · rw [abs_of_neg hnp.1] at hxa hxb
    rw [abs_of_pos hnp.2] at hya hyb
    have hxy : x - y < 0 := by linarith
    rw [abs_of_neg hxy]
    constructor <;> nlinarith [ha, hb', hL]

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
  have ha0 : 0 < a := by
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    nlinarith [ha, hL]
  have hu_ne : u ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hua
    linarith
  have hv_ne : u - (m : ℝ) * L ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hva
    linarith
  have hdistance :
      |u - (u - (m : ℝ) * L)| =
        |(m : ℝ)| * L := by
    rw [show u - (u - (m : ℝ) * L) = (m : ℝ) * L by ring,
      abs_mul, abs_of_pos hL]
  have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  by_cases hsame :
      (0 < u ∧ 0 < u - (m : ℝ) * L) ∨
        (u < 0 ∧ u - (m : ℝ) * L < 0)
  · have hlt :=
      radialShell_sameSign_distance_lt_period
        L a b u (u - (m : ℝ) * L) k
        hL ha hb hua hub hva hvb hsame
    rw [hdistance] at hlt
    nlinarith [mul_le_mul_of_nonneg_right hmabs hL.le]
  · have hu_sign : 0 < u ∨ u < 0 := by
      rcases lt_or_gt_of_ne hu_ne with hneg | hpos
      · exact Or.inr hneg
      · exact Or.inl hpos
    have hv_sign :
        0 < u - (m : ℝ) * L ∨
          u - (m : ℝ) * L < 0 := by
      rcases lt_or_gt_of_ne hv_ne with hneg | hpos
      · exact Or.inr hneg
      · exact Or.inl hpos
    have hopp :
        (0 < u ∧ u - (m : ℝ) * L < 0) ∨
          (u < 0 ∧ 0 < u - (m : ℝ) * L) := by
      rcases hu_sign with hu_pos | hu_neg <;>
        rcases hv_sign with hv_pos | hv_neg
      · exact False.elim (hsame (Or.inl ⟨hu_pos, hv_pos⟩))
      · exact Or.inl ⟨hu_pos, hv_neg⟩
      · exact Or.inr ⟨hu_neg, hv_pos⟩
      · exact False.elim (hsame (Or.inr ⟨hu_neg, hv_neg⟩))
    obtain ⟨hlower, hupper⟩ :=
      radialShell_oppositeSign_distance_between
        L a b u (u - (m : ℝ) * L) k
        hL ha hb hua hub hva hvb hopp
    rw [hdistance] at hlower hupper
    have hkabs : (k : ℝ) < |(m : ℝ)| :=
      lt_of_mul_lt_mul_right hlower hL.le
    have habssucc : |(m : ℝ)| < (k : ℝ) + 1 :=
      lt_of_mul_lt_mul_right hupper hL.le
    have hkabsInt : (k : ℤ) < |m| := by
      exact_mod_cast hkabs
    have habssuccInt : |m| < (k : ℤ) + 1 := by
      exact_mod_cast habssucc
    omega

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


/-- A central closed-half-period core can be combined with any finite family
of outer radial shells.  The core covers the origin; every outer channel
uses strict radial-shell separation.  Each channel therefore has zero
nonzero-shift integral, so their aggregate aliases cancel exactly. -/
theorem aggregateAliasCancellation_of_coreAndRadialShells
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T L : ℝ) (Λ : ι → ℝ) (f : ι → ℝ → ℝ)
    (core : Finset ι)
    (shell : ι → ℕ) (a b : ι → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ r, 0 ≤ Λ r)
    (hsmooth : ∀ r,
      ContDiff ℝ 2 (fun u => (f r u : ℂ)))
    (hsuppBound : ∀ r u, Λ r < |u| → f r u = 0)
    (heven : ∀ r u, f r (-u) = f r u)
    (hcore : ∀ r, r ∈ core →
      tsupport (f r) ⊆ Icc (-L / 2) (L / 2))
    (hshell : ∀ r, r ∉ core → ∀ x, f r x ≠ 0 →
      a r < |x| ∧ |x| < b r)
    (ha : ∀ r, r ∉ core →
      (shell r : ℝ) * L / 2 < a r)
    (hb : ∀ r, r ∉ core →
      b r < (((shell r) + 1 : ℕ) : ℝ) * L / 2) :
    AggregateComplexAlias.AggregateAliasCancellation T L f := by
  apply AggregateComplexAlias.aggregateAliasCancellation_of_shiftIntegrals
    T L Λ f hL hΛ hsmooth hsuppBound heven
  intro z z' m hm
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hrcore : r ∈ core
  · exact ComplexAliasBridge.halfPeriod_complexShiftIntegral_eq_zero
      (f r) L hL (hcore r hrcore) m hm
      (Complex.I * (z - z'))
  · rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [] with u
    have hoverlap :
        f r u * f r (u - (m : ℝ) * L) = 0 :=
      radialShell_shift_overlap_eq_zero
        (f r) L (a r) (b r) (shell r)
        hL (ha r hrcore) (hb r hrcore)
        (hshell r hrcore) m hm u
    rcases mul_eq_zero.mp hoverlap with hu | hshift
    · simp [hu]
    · simp [hshift]

end RadialShellAlias
end Zeta85
end RH

end
