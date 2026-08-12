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

end SmoothRadialShell
end Zeta85
end RH

end
