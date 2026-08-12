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


/-- Pointwise identification with explicit smooth shell cutoffs packages an
entire physical channel family into the radial-shell data consumed by the
collective quartic bridge. -/
theorem shellWindows_toRadialShellData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (commonPeriod : ℝ → ℝ)
    (target :
      ∀ T : ℝ, Fin (F.channelCount T) → ℝ → ℝ)
    (shell :
      ∀ T : ℝ, Fin (F.channelCount T) → ℕ)
    (a c d b :
      ∀ T : ℝ, Fin (F.channelCount T) → ℝ)
    (hperiod :
      ∀ T j, F.period T j = commonPeriod T)
    (hperiodPos :
      ∀ T, 0 < commonPeriod T)
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
    (hwindow :
      ∀ T j u,
        F.window T j u =
          shellWindow (target T j)
            (a T j) (c T j) (d T j) (b T j)
            (ha T j) (hac T j) (hcd T j) (hdb T j) u)
    (hshellInner :
      ∀ T j,
        (shell T j : ℝ) * commonPeriod T / 2 < a T j)
    (hshellOuter :
      ∀ T j,
        b T j <
          (((shell T j) + 1 : ℕ) : ℝ) *
            commonPeriod T / 2) :
    RadialShellFamily.Data F := by
  refine
    { commonPeriod := commonPeriod
      supportRadius := b
      shell := shell
      innerRadius := a
      outerRadius := b
      period_eq := hperiod
      period_pos := hperiodPos
      supportRadius_nonneg := ?_
      smooth := ?_
      support := ?_
      even := ?_
      shell_support := ?_
      shell_inner := hshellInner
      shell_outer := hshellOuter }
  · intro T j
    exact le_of_lt
      (lt_trans (ha T j)
        (lt_trans (hac T j)
          (lt_trans (hcd T j) (hdb T j))))
  · intro T j
    simpa only [hwindow T j] using
      shellWindow_contDiff_complex
        (target T j)
        (a T j) (c T j) (d T j) (b T j)
        (ha T j) (hac T j) (hcd T j) (hdb T j)
        (htargetSmooth T j)
  · intro T j u hu
    rw [hwindow T j u]
    exact shellWindow_supportRadius
      (target T j)
      (a T j) (c T j) (d T j) (b T j)
      (ha T j) (hac T j) (hcd T j) (hdb T j) hu
  · intro T j u
    rw [hwindow T j (-u), hwindow T j u]
    exact shellWindow_even
      (target T j)
      (a T j) (c T j) (d T j) (b T j)
      (ha T j) (hac T j) (hcd T j) (hdb T j)
      (htargetEven T j) u
  · intro T j u hu
    have hshell :
        shellWindow (target T j)
          (a T j) (c T j) (d T j) (b T j)
          (ha T j) (hac T j) (hcd T j) (hdb T j) u ≠ 0 := by
      simpa only [hwindow T j u] using hu
    exact shellWindow_support
      (target T j)
      (a T j) (c T j) (d T j) (b T j)
      (ha T j) (hac T j) (hcd T j) (hdb T j) hshell

end SmoothRadialShell
end Zeta85
end RH

end
