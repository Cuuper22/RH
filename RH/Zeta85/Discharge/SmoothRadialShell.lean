/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import RH.Zeta85.Discharge.RadialShellFamily

/-!
# Explicit smooth radial shells

Two centered smooth bumps form an annular cutoff.  The inner factor removes
a closed radial core; the outer factor gives compact support.  Between the
two transition layers the shell equals the requested smooth even target
exactly.
-/

open Filter Matrix Finset Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace SmoothRadialShell

/-- The canonical centered smooth bump with prescribed inner and outer
radii. -/
def centeredBump
    (rIn rOut : ℝ) (hIn : 0 < rIn) (hRadii : rIn < rOut) :
    ContDiffBump (0 : ℝ) where
  rIn := rIn
  rOut := rOut
  rIn_pos := hIn
  rIn_lt_rOut := hRadii


/-- A smooth central core cutoff.  It preserves the target on the inner
closed ball and vanishes outside the outer ball. -/
def coreWindow
    (target : ℝ → ℝ) (c d : ℝ)
    (hc : 0 < c) (hcd : c < d)
    (x : ℝ) : ℝ :=
  centeredBump c d hc hcd x * target x

/-- The central core is as smooth as its target. -/
theorem coreWindow_contDiff
    (target : ℝ → ℝ) (c d : ℝ)
    (hc : 0 < c) (hcd : c < d)
    (htarget : ContDiff ℝ 2 target) :
    ContDiff ℝ 2 (coreWindow target c d hc hcd) := by
  unfold coreWindow
  exact (centeredBump c d hc hcd).contDiff.mul htarget

/-- Complex coercion preserves twice-smoothness of the core. -/
theorem coreWindow_contDiff_complex
    (target : ℝ → ℝ) (c d : ℝ)
    (hc : 0 < c) (hcd : c < d)
    (htarget : ContDiff ℝ 2 target) :
    ContDiff ℝ 2
      (fun x => (coreWindow target c d hc hcd x : ℂ)) := by
  exact Complex.ofRealCLM.contDiff.comp
    (coreWindow_contDiff target c d hc hcd htarget)

/-- An even target gives an even central core. -/
theorem coreWindow_even
    (target : ℝ → ℝ) (c d : ℝ)
    (hc : 0 < c) (hcd : c < d)
    (htarget : ∀ x, target (-x) = target x)
    (x : ℝ) :
    coreWindow target c d hc hcd (-x) =
      coreWindow target c d hc hcd x := by
  unfold coreWindow
  rw [ContDiffBump.neg, htarget]

/-- The central core vanishes at and beyond its outer radius. -/
theorem coreWindow_eq_zero_of_outer_le_abs
    (target : ℝ → ℝ) (c d : ℝ)
    (hc : 0 < c) (hcd : c < d)
    {x : ℝ} (hx : d ≤ |x|) :
    coreWindow target c d hc hcd x = 0 := by
  have hout : centeredBump c d hc hcd x = 0 := by
    apply ContDiffBump.zero_of_le_dist
    simpa [Real.dist_eq] using hx
  unfold coreWindow
  rw [hout]
  ring

/-- The topological support of the central core lies in its closed outer
ball. -/
theorem coreWindow_tsupport_subset
    (target : ℝ → ℝ) (c d : ℝ)
    (hc : 0 < c) (hcd : c < d) :
    tsupport (coreWindow target c d hc hcd) ⊆ Icc (-d) d := by
  change
    closure (Function.support (coreWindow target c d hc hcd)) ⊆
      Icc (-d) d
  apply closure_minimal
  · intro x hx
    change coreWindow target c d hc hcd x ≠ 0 at hx
    have habs : |x| < d := by
      by_contra hnot
      exact hx
        (coreWindow_eq_zero_of_outer_le_abs
          target c d hc hcd (le_of_not_gt hnot))
    exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  · exact isClosed_Icc

/-- If the outer core radius is at most half a period, the core satisfies
the closed-half-period alias condition exactly. -/
theorem coreWindow_halfPeriodSupport
    (target : ℝ → ℝ) (c d L : ℝ)
    (hc : 0 < c) (hcd : c < d)
    (hd : d ≤ L / 2) :
    tsupport (coreWindow target c d hc hcd) ⊆
      Icc (-L / 2) (L / 2) := by
  intro x hx
  have hxd :=
    coreWindow_tsupport_subset target c d hc hcd hx
  exact ⟨by linarith [hxd.1, hd], by linarith [hxd.2, hd]⟩

/-- A strict absolute support-radius clause for the central core. -/
theorem coreWindow_supportRadius
    (target : ℝ → ℝ) (c d : ℝ)
    (hc : 0 < c) (hcd : c < d)
    {x : ℝ} (hx : d < |x|) :
    coreWindow target c d hc hcd x = 0 :=
  coreWindow_eq_zero_of_outer_le_abs
    target c d hc hcd hx.le

/-- A smooth radial shell.  It vanishes on the closed ball of radius a and
outside the open ball of radius b.  It equals target on c ≤ |x| ≤ d. -/
def shellWindow
    (target : ℝ → ℝ) (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (x : ℝ) : ℝ :=
  centeredBump d b (lt_trans ha (lt_trans hac hcd)) hdb x *
    (1 - centeredBump a c ha hac x) * target x

/-- The explicit shell is as smooth as its target. -/
theorem shellWindow_contDiff
    (target : ℝ → ℝ) (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (htarget : ContDiff ℝ 2 target) :
    ContDiff ℝ 2
      (shellWindow target a c d b ha hac hcd hdb) := by
  unfold shellWindow
  exact
    ((centeredBump d b (lt_trans ha (lt_trans hac hcd)) hdb).contDiff.mul
      (contDiff_const.sub
        (centeredBump a c ha hac).contDiff)).mul htarget

/-- Complex coercion of a twice-smooth shell is twice smooth, as required by
complex Poisson summation. -/
theorem shellWindow_contDiff_complex
    (target : ℝ → ℝ) (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (htarget : ContDiff ℝ 2 target) :
    ContDiff ℝ 2
      (fun x =>
        (shellWindow target a c d b ha hac hcd hdb x : ℂ)) := by
  exact
    (shellWindow_contDiff
      target a c d b ha hac hcd hdb htarget).continuousLinearMap_comp
        Complex.ofRealCLM

/-- Even targets give even radial shells. -/
theorem shellWindow_even
    (target : ℝ → ℝ) (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (htarget : ∀ x, target (-x) = target x)
    (x : ℝ) :
    shellWindow target a c d b ha hac hcd hdb (-x) =
      shellWindow target a c d b ha hac hcd hdb x := by
  unfold shellWindow
  rw [ContDiffBump.neg, ContDiffBump.neg, htarget]

/-- The outer bump gives the exact compact support bound. -/
theorem shellWindow_eq_zero_of_outer_le_abs
    (target : ℝ → ℝ) (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    {x : ℝ} (hx : b ≤ |x|) :
    shellWindow target a c d b ha hac hcd hdb x = 0 := by
  have hout :
      centeredBump d b (lt_trans ha (lt_trans hac hcd)) hdb x = 0 := by
    apply ContDiffBump.zero_of_le_dist
    simpa [Real.dist_eq] using hx
  unfold shellWindow
  rw [hout]
  ring

/-- Nonzero shell points lie strictly between its radial support boundaries. -/
theorem shellWindow_support
    (target : ℝ → ℝ) (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    {x : ℝ}
    (hx :
      shellWindow target a c d b ha hac hcd hdb x ≠ 0) :
    a < |x| ∧ |x| < b := by
  constructor
  · by_contra hnot
    have hle : |x| ≤ a := le_of_not_gt hnot
    have hin :
        centeredBump a c ha hac x = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      simpa [Real.dist_eq] using hle
    apply hx
    unfold shellWindow
    rw [hin]
    ring
  · by_contra hnot
    exact hx
      (shellWindow_eq_zero_of_outer_le_abs
        target a c d b ha hac hcd hdb
        (le_of_not_gt hnot))

/-- Away from both transition layers the shell is literally the target. -/
theorem shellWindow_eq_target
    (target : ℝ → ℝ) (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    {x : ℝ} (hinner : c ≤ |x|) (houter : |x| ≤ d) :
    shellWindow target a c d b ha hac hcd hdb x = target x := by
  have hin :
      centeredBump a c ha hac x = 0 := by
    apply ContDiffBump.zero_of_le_dist
    simpa [Real.dist_eq] using hinner
  have hout :
      centeredBump d b (lt_trans ha (lt_trans hac hcd)) hdb x = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    simpa [Real.dist_eq] using houter
  unfold shellWindow
  rw [hin, hout]
  ring

/-- A nonnegative target stays nonnegative after shell cutoff. -/
theorem shellWindow_nonneg
    (target : ℝ → ℝ) (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (htarget : ∀ x, 0 ≤ target x)
    (x : ℝ) :
    0 ≤ shellWindow target a c d b ha hac hcd hdb x := by
  unfold shellWindow
  exact mul_nonneg
    (mul_nonneg
      (centeredBump d b
        (lt_trans ha (lt_trans hac hcd)) hdb).nonneg
      (sub_nonneg.mpr (centeredBump a c ha hac).le_one))
    (htarget x)

/-- Every shell cutoff has an immediate absolute support-radius clause. -/
theorem shellWindow_supportRadius
    (target : ℝ → ℝ) (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    {x : ℝ} (hx : b < |x|) :
    shellWindow target a c d b ha hac hcd hdb x = 0 :=
  shellWindow_eq_zero_of_outer_le_abs
    target a c d b ha hac hcd hdb hx.le


/-- Explicit central cutoffs and annular cutoffs package directly into the
complete core-plus-radial-shell family.  All smoothness, support, and parity
clauses are derived from the cutoff formulas. -/
theorem coreAndShellWindows_toCoreData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (commonPeriod : ℝ → ℝ)
    (core : ∀ T : ℝ, Finset (Fin (F.channelCount T)))
    (target : ∀ T : ℝ, Fin (F.channelCount T) → ℝ → ℝ)
    (shell : ∀ T : ℝ, Fin (F.channelCount T) → ℕ)
    (coreInner coreOuter a c d b :
      ∀ T : ℝ, Fin (F.channelCount T) → ℝ)
    (hperiod :
      ∀ T j, F.period T j = commonPeriod T)
    (hperiodPos :
      ∀ T, 0 < commonPeriod T)
    (hcoreInnerPos :
      ∀ T j, 0 < coreInner T j)
    (hcoreRadii :
      ∀ T j, coreInner T j < coreOuter T j)
    (hcoreHalf :
      ∀ T j, coreOuter T j ≤ commonPeriod T / 2)
    (ha :
      ∀ T j, 0 < a T j)
    (hac :
      ∀ T j, a T j < c T j)
    (hcd :
      ∀ T j, c T j < d T j)
    (hdb :
      ∀ T j, d T j < b T j)
    (htargetSmooth :
      ∀ T j, ContDiff ℝ 2 (target T j))
    (htargetEven :
      ∀ T j u, target T j (-u) = target T j u)
    (hwindowCore :
      ∀ T j, j ∈ core T → ∀ u,
        F.window T j u =
          coreWindow (target T j)
            (coreInner T j) (coreOuter T j)
            (hcoreInnerPos T j) (hcoreRadii T j) u)
    (hwindowShell :
      ∀ T j, j ∉ core T → ∀ u,
        F.window T j u =
          shellWindow (target T j)
            (a T j) (c T j) (d T j) (b T j)
            (ha T j) (hac T j) (hcd T j) (hdb T j) u)
    (hshellInner :
      ∀ T j, j ∉ core T →
        (shell T j : ℝ) * commonPeriod T / 2 < a T j)
    (hshellOuter :
      ∀ T j, j ∉ core T →
        b T j <
          (((shell T j) + 1 : ℕ) : ℝ) *
            commonPeriod T / 2) :
    RadialShellFamily.CoreData F := by
  refine
    { commonPeriod := commonPeriod
      supportRadius := fun T j =>
        if j ∈ core T then coreOuter T j else b T j
      core := core
      shell := shell
      innerRadius := a
      outerRadius := b
      period_eq := hperiod
      period_pos := hperiodPos
      supportRadius_nonneg := ?_
      smooth := ?_
      support := ?_
      even := ?_
      core_support := ?_
      shell_support := ?_
      shell_inner := hshellInner
      shell_outer := hshellOuter }
  · intro T j
    by_cases hj : j ∈ core T
    · simp only [hj, if_true]
      exact (lt_trans (hcoreInnerPos T j) (hcoreRadii T j)).le
    · simp only [hj, if_false]
      exact le_of_lt
        (lt_trans (ha T j)
          (lt_trans (hac T j)
            (lt_trans (hcd T j) (hdb T j))))
  · intro T j
    by_cases hj : j ∈ core T
    · have hw :
          F.window T j =
            coreWindow (target T j)
              (coreInner T j) (coreOuter T j)
              (hcoreInnerPos T j) (hcoreRadii T j) :=
        funext (hwindowCore T j hj)
      rw [hw]
      exact coreWindow_contDiff_complex
        (target T j)
        (coreInner T j) (coreOuter T j)
        (hcoreInnerPos T j) (hcoreRadii T j)
        (htargetSmooth T j)
    · have hw :
          F.window T j =
            shellWindow (target T j)
              (a T j) (c T j) (d T j) (b T j)
              (ha T j) (hac T j) (hcd T j) (hdb T j) :=
        funext (hwindowShell T j hj)
      rw [hw]
      exact shellWindow_contDiff_complex
        (target T j)
        (a T j) (c T j) (d T j) (b T j)
        (ha T j) (hac T j) (hcd T j) (hdb T j)
        (htargetSmooth T j)
  · intro T j u hu
    by_cases hj : j ∈ core T
    · simp only [hj, if_true] at hu
      rw [hwindowCore T j hj u]
      exact coreWindow_supportRadius
        (target T j)
        (coreInner T j) (coreOuter T j)
        (hcoreInnerPos T j) (hcoreRadii T j) hu
    · simp only [hj, if_false] at hu
      rw [hwindowShell T j hj u]
      exact shellWindow_supportRadius
        (target T j)
        (a T j) (c T j) (d T j) (b T j)
        (ha T j) (hac T j) (hcd T j) (hdb T j) hu
  · intro T j u
    by_cases hj : j ∈ core T
    · rw [hwindowCore T j hj (-u), hwindowCore T j hj u]
      exact coreWindow_even
        (target T j)
        (coreInner T j) (coreOuter T j)
        (hcoreInnerPos T j) (hcoreRadii T j)
        (htargetEven T j) u
    · rw [hwindowShell T j hj (-u), hwindowShell T j hj u]
      exact shellWindow_even
        (target T j)
        (a T j) (c T j) (d T j) (b T j)
        (ha T j) (hac T j) (hcd T j) (hdb T j)
        (htargetEven T j) u
  · intro T j hj
    have hw :
        F.window T j =
          coreWindow (target T j)
            (coreInner T j) (coreOuter T j)
            (hcoreInnerPos T j) (hcoreRadii T j) :=
      funext (hwindowCore T j hj)
    rw [hw]
    exact coreWindow_halfPeriodSupport
      (target T j)
      (coreInner T j) (coreOuter T j) (commonPeriod T)
      (hcoreInnerPos T j) (hcoreRadii T j)
      (hcoreHalf T j)
  · intro T j hj u hu
    have hshell :
        shellWindow (target T j)
          (a T j) (c T j) (d T j) (b T j)
          (ha T j) (hac T j) (hcd T j) (hdb T j) u ≠ 0 := by
      simpa only [hwindowShell T j hj u] using hu
    exact shellWindow_support
      (target T j)
      (a T j) (c T j) (d T j) (b T j)
      (ha T j) (hac T j) (hcd T j) (hdb T j) hshell

end SmoothRadialShell
end Zeta85
end RH

end
