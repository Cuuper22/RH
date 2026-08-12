/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import RH.Zeta85.Discharge.RadialShellFamily
import RH.Zeta85.Discharge.QuarticWindowWitnesses

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


/-! ## Profiled half-period windows -/

/-- A smooth cutoff multiplied by the square root of a prescribed energy
profile.  The square root is only required to be smooth where the cutoff can
be nonzero. -/
def profiledBumpWindow
    (v : ℝ → ℝ) (L : ℝ) (b : ContDiffBump (0 : ℝ)) (u : ℝ) : ℝ :=
  Real.sqrt (v (u / L)) * b u

/-- Local positivity on the closed outer ball is enough for global
smoothness: outside that ball the bump is identically zero on a
neighborhood. -/
theorem profiledBumpWindow_contDiff
    (v : ℝ → ℝ) (L : ℝ) (b : ContDiffBump (0 : ℝ))
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ u, |u| ≤ b.rOut → 0 < v (u / L)) :
    ContDiff ℝ ∞ (profiledBumpWindow v L b) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Metric.closedBall (0 : ℝ) b.rOut
  · have hxabs : |x| ≤ b.rOut := by
      simpa [Real.dist_eq] using hx
    have hscaled :
        ContDiff ℝ ∞ (fun y : ℝ => v (y / L)) :=
      hv.comp (contDiff_id.div_const L)
    exact
      (hscaled.contDiffAt.sqrt (ne_of_gt (hpos x hxabs))).mul
        b.contDiffAt
  · have hopen :
        IsOpen ((Metric.closedBall (0 : ℝ) b.rOut)ᶜ) :=
      isClosed_closedBall.isOpen_compl
    have heq :
        profiledBumpWindow v L b =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      have hyout : b.rOut < dist y (0 : ℝ) := by
        simpa only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] using hy
      have hby : b y = 0 :=
        b.zero_of_le_dist hyout.le
      simp [profiledBumpWindow, hby]
    exact contDiff_zero.contDiffAt.congr_of_eventuallyEq heq

/-- An even profile gives an even profiled bump. -/
theorem profiledBumpWindow_even
    (v : ℝ → ℝ) (L : ℝ) (b : ContDiffBump (0 : ℝ))
    (heven : ∀ x, v (-x) = v x) (u : ℝ) :
    profiledBumpWindow v L b (-u) =
      profiledBumpWindow v L b u := by
  unfold profiledBumpWindow
  rw [show (-u) / L = -(u / L) by ring, heven, b.neg]

/-- The energy of a profiled bump is the profile times the squared cutoff. -/
theorem profiledBumpWindow_sq
    (v : ℝ → ℝ) (L : ℝ) (b : ContDiffBump (0 : ℝ))
    (u : ℝ) (hnonneg : 0 ≤ v (u / L)) :
    profiledBumpWindow v L b u ^ 2 =
      v (u / L) * b u ^ 2 := by
  unfold profiledBumpWindow
  rw [mul_pow, Real.sq_sqrt hnonneg]

/-- The profiled window has no support beyond the bump's closed outer ball. -/
theorem profiledBumpWindow_tsupport
    (v : ℝ → ℝ) (L : ℝ) (b : ContDiffBump (0 : ℝ)) :
    tsupport (profiledBumpWindow v L b) ⊆
      Metric.closedBall (0 : ℝ) b.rOut := by
  rw [tsupport]
  refine closure_minimal ?_ isClosed_closedBall
  intro u hu
  have hbu : b u ≠ 0 := by
    intro hzero
    apply hu
    simp [profiledBumpWindow, hzero]
  have hball : u ∈ Metric.ball (0 : ℝ) b.rOut := by
    rw [← b.support_eq]
    exact hbu
  exact Metric.ball_subset_closedBall hball

/-- Punching a smooth centered hole in a profiled bump produces a literal
radial shell. -/
def profiledShellWindow
    (v : ℝ → ℝ) (L : ℝ)
    (outer inner : ContDiffBump (0 : ℝ)) (u : ℝ) : ℝ :=
  profiledBumpWindow v L outer u * (1 - inner u)

/-- The profiled shell is smooth whenever the outer profiled bump is smooth. -/
theorem profiledShellWindow_contDiff
    (v : ℝ → ℝ) (L : ℝ)
    (outer inner : ContDiffBump (0 : ℝ))
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ u, |u| ≤ outer.rOut → 0 < v (u / L)) :
    ContDiff ℝ ∞ (profiledShellWindow v L outer inner) := by
  unfold profiledShellWindow
  exact
    (profiledBumpWindow_contDiff v L outer hv hpos).mul
      (contDiff_const.sub inner.contDiff)

/-- Even profiles give even profiled shells. -/
theorem profiledShellWindow_even
    (v : ℝ → ℝ) (L : ℝ)
    (outer inner : ContDiffBump (0 : ℝ))
    (heven : ∀ x, v (-x) = v x) (u : ℝ) :
    profiledShellWindow v L outer inner (-u) =
      profiledShellWindow v L outer inner u := by
  unfold profiledShellWindow
  rw [profiledBumpWindow_even v L outer heven u, inner.neg]

/-- Every nonzero profiled-shell point lies strictly outside the inner core
and strictly inside the outer cutoff. -/
theorem profiledShellWindow_support
    (v : ℝ → ℝ) (L : ℝ)
    (outer inner : ContDiffBump (0 : ℝ))
    {u : ℝ}
    (hu : profiledShellWindow v L outer inner u ≠ 0) :
    inner.rIn < |u| ∧ |u| < outer.rOut := by
  constructor
  · by_contra hnot
    have hle : |u| ≤ inner.rIn := le_of_not_gt hnot
    have hinner : inner u = 1 := by
      apply inner.one_of_mem_closedBall
      simpa [Real.dist_eq] using hle
    apply hu
    simp [profiledShellWindow, hinner]
  · by_contra hnot
    have hle : outer.rOut ≤ |u| := le_of_not_gt hnot
    have houter : outer u = 0 := by
      apply outer.zero_of_le_dist
      simpa [Real.dist_eq] using hle
    apply hu
    simp [profiledShellWindow, profiledBumpWindow, houter]

/-- The outer bump radius is an absolute support radius for a profiled shell. -/
theorem profiledShellWindow_supportRadius
    (v : ℝ → ℝ) (L : ℝ)
    (outer inner : ContDiffBump (0 : ℝ))
    {u : ℝ} (hu : outer.rOut < |u|) :
    profiledShellWindow v L outer inner u = 0 := by
  have houter : outer u = 0 := by
    apply outer.zero_of_le_dist
    simpa [Real.dist_eq] using hu.le
  simp [profiledShellWindow, profiledBumpWindow, houter]

/-- On the bump's inner ball, its energy is exactly the requested profile. -/
theorem profiledBumpWindow_sq_eq_profile
    (v : ℝ → ℝ) (L : ℝ) (b : ContDiffBump (0 : ℝ))
    (u : ℝ) (hnonneg : 0 ≤ v (u / L))
    (hu : u ∈ Metric.closedBall (0 : ℝ) b.rIn) :
    profiledBumpWindow v L b u ^ 2 = v (u / L) := by
  rw [profiledBumpWindow_sq v L b u hnonneg,
    b.one_of_mem_closedBall hu]
  ring

/-- A cutoff whose transition layer shrinks to the two half-period
endpoints. -/
def shrinkingHalfPeriodBump
    (L : ℝ) (n : ℕ) (hL : 0 < L) : ContDiffBump (0 : ℝ) where
  rIn := L / 2 - L / ((n : ℝ) + 3)
  rOut := L / 2 - L / (2 * ((n : ℝ) + 3))
  rIn_pos := by
    apply sub_pos.mpr
    rw [div_lt_div_iff₀
      (by positivity : 0 < (n : ℝ) + 3)
      (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  rIn_lt_rOut := by
    have hn : 0 < (n : ℝ) + 3 := by positivity
    have hdiv :
        L / (2 * ((n : ℝ) + 3)) <
          L / ((n : ℝ) + 3) := by
      rw [div_lt_div_iff₀ (mul_pos (by norm_num) hn) hn]
      nlinarith
    linarith

theorem shrinkingHalfPeriodBump_rOut_lt
    (L : ℝ) (n : ℕ) (hL : 0 < L) :
    (shrinkingHalfPeriodBump L n hL).rOut < L / 2 := by
  dsimp [shrinkingHalfPeriodBump]
  positivity

/-- A centered core cutoff whose entire support shrinks to the origin. -/
def shrinkingCoreBump
    (L : ℝ) (n : ℕ) (hL : 0 < L) : ContDiffBump (0 : ℝ) where
  rIn := L / (2 * ((n : ℝ) + 3))
  rOut := L / ((n : ℝ) + 3)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : 0 < (n : ℝ) + 3 := by positivity
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) hn) hn]
    nlinarith

theorem shrinkingCoreBump_rOut_lt_halfPeriod
    (L : ℝ) (n : ℕ) (hL : 0 < L) :
    (shrinkingCoreBump L n hL).rOut < L / 2 := by
  dsimp [shrinkingCoreBump]
  have hn : 0 ≤ (n : ℝ) := by positivity
  rw [div_lt_div_iff₀
    (by positivity : 0 < (n : ℝ) + 3)
    (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- Away from the origin, the shrinking core cutoff is eventually
identically zero. -/
theorem shrinkingCoreBump_eventually_zero
    (L : ℝ) (hL : 0 < L) (u : ℝ) (hu : u ≠ 0) :
    ∀ᶠ n : ℕ in Filter.atTop, shrinkingCoreBump L n hL u = 0 := by
  have huabs : 0 < |u| := abs_pos.mpr hu
  obtain ⟨N, hN⟩ := exists_nat_gt (L / |u|)
  have hNmul : L < (N : ℝ) * |u| :=
    (div_lt_iff₀ huabs).1 hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hfrac : L / ((n : ℝ) + 3) < |u| := by
    apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 3)).2
    have hmul :
        (N : ℝ) * |u| ≤ ((n : ℝ) + 3) * |u| := by
      nlinarith [mul_le_mul_of_nonneg_right hnR huabs.le]
    exact lt_of_lt_of_le hNmul hmul
  apply (shrinkingCoreBump L n hL).zero_of_le_dist
  simpa [shrinkingCoreBump, Real.dist_eq] using hfrac.le

/-- The explicit shrinking-window energy approximation to a normalized
profile. -/
def shrinkingProfileWindow
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L) (u : ℝ) : ℝ :=
  profiledBumpWindow v L (shrinkingHalfPeriodBump L n hL) u

/-- The one-channel annular approximation: a profiled half-period bump with
a shrinking smooth core removed. -/
def shrinkingProfileShellWindow
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L) (u : ℝ) : ℝ :=
  profiledShellWindow v L
    (shrinkingHalfPeriodBump L n hL)
    (shrinkingCoreBump L n hL) u

/-- A smooth positive profile on the normalized half interval gives a smooth
strict-half-period window at every finite stage. -/
theorem shrinkingProfileWindow_contDiff
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    ContDiff ℝ ∞ (shrinkingProfileWindow v L n hL) := by
  apply profiledBumpWindow_contDiff v L
    (shrinkingHalfPeriodBump L n hL) hv
  intro u hu
  apply hpos
  rw [abs_div, abs_of_pos hL]
  apply (div_le_iff₀ hL).2
  have hout :=
    (shrinkingHalfPeriodBump_rOut_lt L n hL).le
  nlinarith

/-- Every finite annular approximation is smooth. -/
theorem shrinkingProfileShellWindow_contDiff
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    ContDiff ℝ ∞ (shrinkingProfileShellWindow v L n hL) := by
  apply profiledShellWindow_contDiff
  · exact hv
  · intro u hu
    apply hpos
    rw [abs_div, abs_of_pos hL]
    apply (div_le_iff₀ hL).2
    have hout :=
      (shrinkingHalfPeriodBump_rOut_lt L n hL).le
    nlinarith

/-- Even profiles give even annular approximations. -/
theorem shrinkingProfileShellWindow_even
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    (heven : ∀ x, v (-x) = v x) (u : ℝ) :
    shrinkingProfileShellWindow v L n hL (-u) =
      shrinkingProfileShellWindow v L n hL u :=
  profiledShellWindow_even v L
    (shrinkingHalfPeriodBump L n hL)
    (shrinkingCoreBump L n hL) heven u

/-- Every nonzero annular approximation lies in the exact radial shell needed
by the aggregate alias-cancellation theorem. -/
theorem shrinkingProfileShellWindow_support
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    {u : ℝ}
    (hu : shrinkingProfileShellWindow v L n hL u ≠ 0) :
    (shrinkingCoreBump L n hL).rIn < |u| ∧
      |u| < (shrinkingHalfPeriodBump L n hL).rOut :=
  profiledShellWindow_support v L
    (shrinkingHalfPeriodBump L n hL)
    (shrinkingCoreBump L n hL) hu

/-- The annular approximation vanishes beyond the physical half-period. -/
theorem shrinkingProfileShellWindow_supportRadius
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    {u : ℝ} (hu : L / 2 < |u|) :
    shrinkingProfileShellWindow v L n hL u = 0 := by
  apply profiledShellWindow_supportRadius
  exact lt_trans
    (shrinkingHalfPeriodBump_rOut_lt L n hL) hu

/-- The inner shell radius is strictly beyond shell index zero. -/
theorem shrinkingProfileShellWindow_innerRadius_pos
    (L : ℝ) (n : ℕ) (hL : 0 < L) :
    0 < (shrinkingCoreBump L n hL).rIn :=
  (shrinkingCoreBump L n hL).rIn_pos

/-- The outer shell radius is strictly below the next half-period. -/
theorem shrinkingProfileShellWindow_outerRadius_lt
    (L : ℝ) (n : ℕ) (hL : 0 < L) :
    (shrinkingHalfPeriodBump L n hL).rOut < L / 2 :=
  shrinkingHalfPeriodBump_rOut_lt L n hL

/-- Away from the origin, annular and centered energies are eventually
literally equal. -/
theorem shrinkingProfileShellWindow_sq_eventually_eq
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (u : ℝ) (hu : u ≠ 0) :
    (fun n : ℕ => shrinkingProfileShellWindow v L n hL u ^ 2) =ᶠ[Filter.atTop]
      (fun n : ℕ => shrinkingProfileWindow v L n hL u ^ 2) := by
  filter_upwards [shrinkingCoreBump_eventually_zero L hL u hu] with n hzero
  simp [shrinkingProfileShellWindow, shrinkingProfileWindow,
    profiledShellWindow, hzero]

/-- Every shrinking profiled window lies in the closed half-period, so every
nonzero period translate has zero overlap. -/
theorem shrinkingProfileWindow_tsupport
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L) :
    tsupport (shrinkingProfileWindow v L n hL) ⊆
      Icc (-L / 2) (L / 2) := by
  intro u hu
  have hclosed :=
    profiledBumpWindow_tsupport v L
      (shrinkingHalfPeriodBump L n hL) hu
  have habs :
      |u| ≤ (shrinkingHalfPeriodBump L n hL).rOut := by
    simpa [Real.dist_eq] using hclosed
  exact abs_le.mp
    (le_trans habs (shrinkingHalfPeriodBump_rOut_lt L n hL).le)

/-- The shrinking window is literally the target energy away from its two
transition layers. -/
theorem shrinkingProfileWindow_sq_eq_profile
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (u : ℝ)
    (hu :
      |u| ≤ (shrinkingHalfPeriodBump L n hL).rIn) :
    shrinkingProfileWindow v L n hL u ^ 2 = v (u / L) := by
  apply profiledBumpWindow_sq_eq_profile
  · apply (hpos (u / L) ?_).le
    rw [abs_div, abs_of_pos hL]
    apply (div_le_iff₀ hL).2
    have hradii :
        (shrinkingHalfPeriodBump L n hL).rIn <
          (shrinkingHalfPeriodBump L n hL).rOut :=
      (shrinkingHalfPeriodBump L n hL).rIn_lt_rOut
    have hout :=
      (shrinkingHalfPeriodBump_rOut_lt L n hL).le
    nlinarith
  · simpa [Real.dist_eq] using hu


/-- A point at or beyond the bump's outer radius is exactly zero. -/
theorem profiledBumpWindow_eq_zero_of_rOut_le_abs
    (v : ℝ → ℝ) (L : ℝ) (b : ContDiffBump (0 : ℝ))
    (u : ℝ) (hu : b.rOut ≤ |u|) :
    profiledBumpWindow v L b u = 0 := by
  have hbu : b u = 0 := by
    apply b.zero_of_le_dist
    simpa [Real.dist_eq] using hu
  simp [profiledBumpWindow, hbu]

/-- Away from the two half-period endpoints, the shrinking window energy
converges pointwise to the frozen supported profile.  In fact, at every
strict interior point the sequence is eventually exactly equal to the
profile. -/
theorem tendsto_shrinkingProfileWindow_sq
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (u : ℝ) (hboundary : |u| ≠ L / 2) :
    Tendsto
      (fun n : ℕ => shrinkingProfileWindow v L n hL u ^ 2)
      Filter.atTop
      (nhds
        (@QuarticGramFamily.supportedFullProfile v (u / L))) := by
  by_cases hin : |u| < L / 2
  · have habsScaled : |u / L| ≤ (1 : ℝ) / 2 := by
      rw [abs_div, abs_of_pos hL]
      apply (div_le_iff₀ hL).2
      nlinarith
    have hmem :
        u / L ∈ Icc (-(1 : ℝ) / 2) (1 / 2) :=
      abs_le.mp habsScaled
    have htarget :
        @QuarticGramFamily.supportedFullProfile v (u / L) =
          v (u / L) := by
      rw [QuarticGramFamily.supportedFullProfile,
        Set.indicator_of_mem hmem]
    let gap : ℝ := L / 2 - |u|
    have hgap : 0 < gap := by
      dsimp [gap]
      linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (L / gap)
    have hNmul : L < (N : ℝ) * gap :=
      (div_lt_iff₀ hgap).1 hN
    have hevent :
        ∀ᶠ n : ℕ in Filter.atTop,
          shrinkingProfileWindow v L n hL u ^ 2 =
            v (u / L) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnR : (N : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn
      have hmul :
          (N : ℝ) * gap ≤ ((n : ℝ) + 3) * gap := by
        nlinarith
      have hfrac :
          L / ((n : ℝ) + 3) < gap := by
        apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 3)).2
        exact lt_of_lt_of_le hNmul hmul
      have huinner :
          |u| ≤ (shrinkingHalfPeriodBump L n hL).rIn := by
        dsimp [shrinkingHalfPeriodBump, gap] at hfrac ⊢
        linarith
      exact shrinkingProfileWindow_sq_eq_profile
        v L n hL hposProfile u huinner
    rw [htarget]
    exact tendsto_const_nhds.congr' hevent.symm
  · have houtside : L / 2 < |u| := by
      exact lt_of_le_of_ne (le_of_not_gt hin) hboundary.symm
    have hnotmem :
        u / L ∉ Icc (-(1 : ℝ) / 2) (1 / 2) := by
      intro hmem
      have hscaled : |u / L| ≤ (1 : ℝ) / 2 :=
        abs_le.mpr hmem
      rw [abs_div, abs_of_pos hL] at hscaled
      have hu : |u| ≤ L / 2 := by
        have hmul := (div_le_iff₀ hL).1 hscaled
        nlinarith
      exact (not_le_of_gt houtside) hu
    have htarget :
        @QuarticGramFamily.supportedFullProfile v (u / L) = 0 := by
      rw [QuarticGramFamily.supportedFullProfile,
        Set.indicator_of_not_mem hnotmem]
    have hzero :
        ∀ n : ℕ, shrinkingProfileWindow v L n hL u = 0 := by
      intro n
      unfold shrinkingProfileWindow
      apply profiledBumpWindow_eq_zero_of_rOut_le_abs
      exact le_trans
        (shrinkingHalfPeriodBump_rOut_lt L n hL).le
        houtside.le
    rw [htarget]
    simpa [hzero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ))
          Filter.atTop (nhds 0))

/-- The two exceptional endpoints are null, so the shrinking smooth energies
converge to the frozen profile almost everywhere. -/
theorem ae_tendsto_shrinkingProfileWindow_sq
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    ∀ᵐ u : ℝ ∂volume,
      Tendsto
        (fun n : ℕ => shrinkingProfileWindow v L n hL u ^ 2)
        Filter.atTop
        (nhds
          (@QuarticGramFamily.supportedFullProfile v (u / L))) := by
  filter_upwards [
    volume.ae_ne (-L / 2),
    volume.ae_ne (L / 2)
  ] with u hleft hright
  apply tendsto_shrinkingProfileWindow_sq v L hL hposProfile u
  intro hb
  by_cases hu : 0 ≤ u
  · apply hright
    simpa [abs_of_nonneg hu] using hb
  · apply hleft
    rw [abs_of_nonpos (le_of_not_ge hu)] at hb
    linarith


/-- Except at the null origin and the two null endpoints, the annular
energies converge to the same frozen supported profile. -/
theorem tendsto_shrinkingProfileShellWindow_sq
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (u : ℝ) (hu : u ≠ 0) (hboundary : |u| ≠ L / 2) :
    Tendsto
      (fun n : ℕ => shrinkingProfileShellWindow v L n hL u ^ 2)
      Filter.atTop
      (nhds
        (@QuarticGramFamily.supportedFullProfile v (u / L))) := by
  apply
    (tendsto_shrinkingProfileWindow_sq
      v L hL hposProfile u hboundary).congr'
  exact
    (shrinkingProfileShellWindow_sq_eventually_eq
      v L hL u hu).symm

/-- The annular energies converge almost everywhere to the frozen supported
profile. -/
theorem ae_tendsto_shrinkingProfileShellWindow_sq
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    ∀ᵐ u : ℝ ∂volume,
      Tendsto
        (fun n : ℕ => shrinkingProfileShellWindow v L n hL u ^ 2)
        Filter.atTop
        (nhds
          (@QuarticGramFamily.supportedFullProfile v (u / L))) := by
  filter_upwards [
    volume.ae_ne (0 : ℝ),
    volume.ae_ne (-L / 2),
    volume.ae_ne (L / 2)
  ] with u hzero hleft hright
  apply tendsto_shrinkingProfileShellWindow_sq
    v L hL hposProfile u hzero
  intro hb
  by_cases hu : 0 ≤ u
  · apply hright
    simpa [abs_of_nonneg hu] using hb
  · apply hleft
    rw [abs_of_nonpos (le_of_not_ge hu)] at hb
    linarith

/-! ## Frozen profile specializations -/

/-- The explicit shrinking smooth window for the R-8686 polynomial profile. -/
def frozen8686Window
    (L : ℝ) (n : ℕ) (hL : 0 < L) : ℝ → ℝ :=
  shrinkingProfileWindow QuarticWindowWitnesses.v8686 L n hL

/-- The explicit shrinking smooth window for the R-9506 polynomial profile. -/
def frozen9506Window
    (L : ℝ) (n : ℕ) (hL : 0 < L) : ℝ → ℝ :=
  shrinkingProfileWindow QuarticWindowWitnesses.v9506 L n hL

theorem frozen8686Window_contDiff
    (L : ℝ) (n : ℕ) (hL : 0 < L) :
    ContDiff ℝ ∞ (frozen8686Window L n hL) := by
  apply shrinkingProfileWindow_contDiff
  · unfold QuarticWindowWitnesses.v8686
    fun_prop
  · intro x hx
    exact QuarticWindowWitnesses.v8686_pos hx

theorem frozen9506Window_contDiff
    (L : ℝ) (n : ℕ) (hL : 0 < L) :
    ContDiff ℝ ∞ (frozen9506Window L n hL) := by
  apply shrinkingProfileWindow_contDiff
  · unfold QuarticWindowWitnesses.v9506
    fun_prop
  · intro x hx
    exact QuarticWindowWitnesses.v9506_pos hx

theorem frozen8686Window_even
    (L : ℝ) (n : ℕ) (hL : 0 < L) (u : ℝ) :
    frozen8686Window L n hL (-u) =
      frozen8686Window L n hL u := by
  apply profiledBumpWindow_even
  intro x
  simp only [QuarticWindowWitnesses.v8686]
  ring

theorem frozen9506Window_even
    (L : ℝ) (n : ℕ) (hL : 0 < L) (u : ℝ) :
    frozen9506Window L n hL (-u) =
      frozen9506Window L n hL u := by
  apply profiledBumpWindow_even
  intro x
  simp only [QuarticWindowWitnesses.v9506]
  ring

theorem frozen8686Window_tsupport
    (L : ℝ) (n : ℕ) (hL : 0 < L) :
    tsupport (frozen8686Window L n hL) ⊆
      Icc (-L / 2) (L / 2) :=
  shrinkingProfileWindow_tsupport
    QuarticWindowWitnesses.v8686 L n hL

theorem frozen9506Window_tsupport
    (L : ℝ) (n : ℕ) (hL : 0 < L) :
    tsupport (frozen9506Window L n hL) ⊆
      Icc (-L / 2) (L / 2) :=
  shrinkingProfileWindow_tsupport
    QuarticWindowWitnesses.v9506 L n hL

/-- The R-8686 smooth window energies converge almost everywhere to the exact
frozen supported profile. -/
theorem ae_tendsto_frozen8686Window_sq
    (L : ℝ) (hL : 0 < L) :
    ∀ᵐ u : ℝ ∂volume,
      Tendsto
        (fun n : ℕ => frozen8686Window L n hL u ^ 2)
        Filter.atTop
        (nhds
          (@QuarticGramFamily.supportedFullProfile
            QuarticWindowWitnesses.v8686 (u / L))) :=
  ae_tendsto_shrinkingProfileWindow_sq
    QuarticWindowWitnesses.v8686 L hL
    (fun x hx => QuarticWindowWitnesses.v8686_pos hx)

/-- The R-9506 smooth window energies converge almost everywhere to the exact
frozen supported profile. -/
theorem ae_tendsto_frozen9506Window_sq
    (L : ℝ) (hL : 0 < L) :
    ∀ᵐ u : ℝ ∂volume,
      Tendsto
        (fun n : ℕ => frozen9506Window L n hL u ^ 2)
        Filter.atTop
        (nhds
          (@QuarticGramFamily.supportedFullProfile
            QuarticWindowWitnesses.v9506 (u / L))) :=
  ae_tendsto_shrinkingProfileWindow_sq
    QuarticWindowWitnesses.v9506 L hL
    (fun x hx => QuarticWindowWitnesses.v9506_pos hx)


/-! ## Integral convergence of the shrinking energies -/

theorem mem_scaled_halfInterval_iff
    (L : ℝ) (hL : 0 < L) (u : ℝ) :
    u / L ∈ Icc (-(1 : ℝ) / 2) (1 / 2) ↔
      u ∈ Icc (-L / 2) (L / 2) := by
  rw [Set.mem_Icc, Set.mem_Icc]
  constructor
  · intro hu
    constructor
    · have h := (le_div_iff₀ hL).1 hu.1
      nlinarith
    · have h := (div_le_iff₀ hL).1 hu.2
      nlinarith
  · intro hu
    constructor
    · apply (le_div_iff₀ hL).2
      nlinarith [hu.1]
    · apply (div_le_iff₀ hL).2
      nlinarith [hu.2]

/-- Scaling the frozen normalized profile is the ordinary physical-interval
indicator of the scaled polynomial. -/
theorem supportedFullProfile_div_eq_indicator
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L) :
    (fun u : ℝ =>
      @QuarticGramFamily.supportedFullProfile v (u / L)) =
      (Icc (-L / 2) (L / 2)).indicator
        (fun u : ℝ => v (u / L)) := by
  funext u
  by_cases hu : u ∈ Icc (-L / 2) (L / 2)
  · have hscaled :=
      (mem_scaled_halfInterval_iff L hL u).2 hu
    rw [QuarticGramFamily.supportedFullProfile,
      Set.indicator_of_mem hscaled,
      Set.indicator_of_mem hu]
  · have hscaled :
        u / L ∉ Icc (-(1 : ℝ) / 2) (1 / 2) := by
      intro hs
      exact hu ((mem_scaled_halfInterval_iff L hL u).1 hs)
    rw [QuarticGramFamily.supportedFullProfile,
      Set.indicator_of_not_mem hscaled,
      Set.indicator_of_not_mem hu]

/-- The integral of the type-level supported profile is exactly its
interval integral; changing the closed endpoint convention costs nothing. -/
theorem integral_supportedFullProfile
    (v : ℝ → ℝ) :
    (∫ x : ℝ, @QuarticGramFamily.supportedFullProfile v x) =
      ∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x := by
  rw [QuarticGramFamily.supportedFullProfile,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num :
      (-(1 : ℝ) / 2) ≤ 1 / 2)]

/-- Scaling a supported normalized profile by a positive physical length
multiplies its total energy by that length. -/
theorem integral_supportedFullProfile_div
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L) :
    (∫ u : ℝ,
      @QuarticGramFamily.supportedFullProfile v (u / L)) =
      L * (∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x) := by
  calc
    (∫ u : ℝ,
      @QuarticGramFamily.supportedFullProfile v (u / L)) =
        |L| •
          (∫ x : ℝ,
            @QuarticGramFamily.supportedFullProfile v x) :=
      MeasureTheory.Measure.integral_comp_div
        (fun x : ℝ =>
          @QuarticGramFamily.supportedFullProfile v x) L
    _ = L * (∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x) := by
      rw [abs_of_pos hL, integral_supportedFullProfile]
      rfl

/-- The R-8686 limiting supported energy has a closed exact value. -/
theorem integral_supportedFullProfile_v8686_div
    (L : ℝ) (hL : 0 < L) :
    (∫ u : ℝ,
      @QuarticGramFamily.supportedFullProfile
        QuarticWindowWitnesses.v8686 (u / L)) =
      L * (3815170470337249 / 3814073303040000 : ℝ) := by
  rw [integral_supportedFullProfile_div
      QuarticWindowWitnesses.v8686 L hL,
    QuarticWindowWitnesses.integral_v8686]

/-- The R-9506 limiting supported energy has a closed exact value. -/
theorem integral_supportedFullProfile_v9506_div
    (L : ℝ) (hL : 0 < L) :
    (∫ u : ℝ,
      @QuarticGramFamily.supportedFullProfile
        QuarticWindowWitnesses.v9506 (u / L)) =
      L * (5913507107 / 5913600000 : ℝ) := by
  rw [integral_supportedFullProfile_div
      QuarticWindowWitnesses.v9506 L hL,
    QuarticWindowWitnesses.integral_v9506]

/-- A smooth normalized profile has an integrable scaled supported profile. -/
theorem integrable_supportedFullProfile_div
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hv : ContDiff ℝ ∞ v) :
    Integrable
      (fun u : ℝ =>
        @QuarticGramFamily.supportedFullProfile v (u / L)) := by
  rw [supportedFullProfile_div_eq_indicator v L hL,
    integrable_indicator_iff measurableSet_Icc]
  have hscaled :
      Continuous (fun u : ℝ => v (u / L)) :=
    (hv.comp (contDiff_id.div_const L)).continuous
  exact hscaled.continuousOn.integrableOn_compact isCompact_Icc

/-- Every finite shrinking energy is bounded pointwise by the frozen
supported profile. -/
theorem shrinkingProfileWindow_sq_le_supportedFullProfile
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (u : ℝ) :
    0 ≤ shrinkingProfileWindow v L n hL u ^ 2 ∧
      shrinkingProfileWindow v L n hL u ^ 2 ≤
        @QuarticGramFamily.supportedFullProfile v (u / L) := by
  constructor
  · positivity
  · by_cases hmem :
        u / L ∈ Icc (-(1 : ℝ) / 2) (1 / 2)
    · have habs : |u / L| ≤ (1 : ℝ) / 2 :=
        abs_le.mpr hmem
      have hvnonneg : 0 ≤ v (u / L) :=
        (hposProfile (u / L) habs).le
      rw [QuarticGramFamily.supportedFullProfile,
        Set.indicator_of_mem hmem]
      unfold shrinkingProfileWindow
      rw [profiledBumpWindow_sq _ _ _ _ hvnonneg]
      have hb0 :
          0 ≤ (shrinkingHalfPeriodBump L n hL) u :=
        (shrinkingHalfPeriodBump L n hL).nonneg
      have hb1 :
          (shrinkingHalfPeriodBump L n hL) u ≤ 1 :=
        (shrinkingHalfPeriodBump L n hL).le_one
      nlinarith
    · have hscaled : (1 : ℝ) / 2 < |u / L| := by
        apply lt_of_not_ge
        intro habs
        exact hmem (abs_le.mp habs)
      rw [abs_div, abs_of_pos hL] at hscaled
      have hout : L / 2 < |u| := by
        have hmul := (lt_div_iff₀ hL).1 hscaled
        nlinarith
      have hzero :
          shrinkingProfileWindow v L n hL u = 0 := by
        unfold shrinkingProfileWindow
        apply profiledBumpWindow_eq_zero_of_rOut_le_abs
        exact le_trans
          (shrinkingHalfPeriodBump_rOut_lt L n hL).le
          hout.le
      rw [QuarticGramFamily.supportedFullProfile,
        Set.indicator_of_not_mem hmem, hzero]
      norm_num

/-- Every finite annular energy is bounded by the same frozen supported
profile as its centered parent. -/
theorem shrinkingProfileShellWindow_sq_le_supportedFullProfile
    (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (u : ℝ) :
    0 ≤ shrinkingProfileShellWindow v L n hL u ^ 2 ∧
      shrinkingProfileShellWindow v L n hL u ^ 2 ≤
        @QuarticGramFamily.supportedFullProfile v (u / L) := by
  have hbase :=
    shrinkingProfileWindow_sq_le_supportedFullProfile
      v L n hL hposProfile u
  have hinner0 :
      0 ≤ (shrinkingCoreBump L n hL) u :=
    (shrinkingCoreBump L n hL).nonneg
  have hinner1 :
      (shrinkingCoreBump L n hL) u ≤ 1 :=
    (shrinkingCoreBump L n hL).le_one
  have hfactor :
      (1 - (shrinkingCoreBump L n hL) u) ^ 2 ≤ 1 := by
    have htwo :
        0 ≤ 2 - (shrinkingCoreBump L n hL) u := by
      linarith
    have hprod :
        0 ≤ (shrinkingCoreBump L n hL) u *
          (2 - (shrinkingCoreBump L n hL) u) :=
      mul_nonneg hinner0 htwo
    nlinarith
  have hmul :
      shrinkingProfileWindow v L n hL u ^ 2 *
          (1 - (shrinkingCoreBump L n hL) u) ^ 2 ≤
        shrinkingProfileWindow v L n hL u ^ 2 := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hfactor hbase.1
  have hsquare :
      shrinkingProfileShellWindow v L n hL u ^ 2 =
        shrinkingProfileWindow v L n hL u ^ 2 *
          (1 - (shrinkingCoreBump L n hL) u) ^ 2 := by
    simp only [shrinkingProfileShellWindow, shrinkingProfileWindow,
      profiledShellWindow, mul_pow]
  rw [hsquare]
  constructor
  · exact mul_nonneg hbase.1 (sq_nonneg _)
  · exact le_trans hmul hbase.2

/-- Dominated convergence upgrades the pointwise construction to convergence
of total physical energy. -/
theorem tendsto_integral_shrinkingProfileWindow_sq
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hv : ContDiff ℝ ∞ v)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n : ℕ =>
        ∫ u : ℝ, shrinkingProfileWindow v L n hL u ^ 2)
      Filter.atTop
      (nhds
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / L))) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun u : ℝ =>
      @QuarticGramFamily.supportedFullProfile v (u / L))
  · intro n
    exact
      ((shrinkingProfileWindow_contDiff
        v L n hL hv hposProfile).continuous.pow 2).aestronglyMeasurable
  · exact integrable_supportedFullProfile_div v L hL hv
  · intro n
    filter_upwards [] with u
    have hbound :=
      shrinkingProfileWindow_sq_le_supportedFullProfile
        v L n hL hposProfile u
    simpa [Real.norm_eq_abs, abs_of_nonneg hbound.1] using hbound.2
  · exact
      ae_tendsto_shrinkingProfileWindow_sq
        v L hL hposProfile

/-- Dominated convergence gives total-energy convergence for the literal
annular shells. -/
theorem tendsto_integral_shrinkingProfileShellWindow_sq
    (v : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hv : ContDiff ℝ ∞ v)
    (hposProfile : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    Tendsto
      (fun n : ℕ =>
        ∫ u : ℝ, shrinkingProfileShellWindow v L n hL u ^ 2)
      Filter.atTop
      (nhds
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / L))) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun u : ℝ =>
      @QuarticGramFamily.supportedFullProfile v (u / L))
  · intro n
    exact
      ((shrinkingProfileShellWindow_contDiff
        v L n hL hv hposProfile).continuous.pow 2).aestronglyMeasurable
  · exact integrable_supportedFullProfile_div v L hL hv
  · intro n
    filter_upwards [] with u
    have hbound :=
      shrinkingProfileShellWindow_sq_le_supportedFullProfile
        v L n hL hposProfile u
    simpa [Real.norm_eq_abs, abs_of_nonneg hbound.1] using hbound.2
  · exact
      ae_tendsto_shrinkingProfileShellWindow_sq
        v L hL hposProfile

/-! ## Direct family realization -/

/-- A quartic family is realized by the one-channel annular construction when
all of its physical windows are the shrinking profiled shells in one common
period. -/
structure AnnularFamilyRealization
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  commonPeriod : ℝ → ℝ
  stage : ∀ T : ℝ, Fin (F.channelCount T) → ℕ
  period_eq : ∀ T j, F.period T j = commonPeriod T
  period_pos : ∀ T, 0 < commonPeriod T
  window_eq : ∀ T j u,
    F.window T j u =
      shrinkingProfileShellWindow v (commonPeriod T) (stage T j)
        (period_pos T) u
  profile_smooth : ContDiff ℝ ∞ v
  profile_pos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x
  profile_even : ∀ x, v (-x) = v x

/-- The annular realization discharges every field of the radial-shell
interface consumed by aggregate alias cancellation. -/
theorem AnnularFamilyRealization.toRadialShellData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : AnnularFamilyRealization F) :
    RadialShellFamily.Data F := by
  refine
    { commonPeriod := h.commonPeriod
      supportRadius := fun T _ => h.commonPeriod T / 2
      shell := fun _ _ => 0
      innerRadius := fun T j =>
        (shrinkingCoreBump
          (h.commonPeriod T) (h.stage T j) (h.period_pos T)).rIn
      outerRadius := fun T j =>
        (shrinkingHalfPeriodBump
          (h.commonPeriod T) (h.stage T j) (h.period_pos T)).rOut
      period_eq := h.period_eq
      period_pos := h.period_pos
      supportRadius_nonneg := ?_
      smooth := ?_
      support := ?_
      even := ?_
      shell_support := ?_
      shell_inner := ?_
      shell_outer := ?_ }
  · intro T j
    exact div_nonneg (h.period_pos T).le (by norm_num)
  · intro T j
    have hwindow :
        (fun u => (F.window T j u : ℂ)) =
          (fun u =>
            (shrinkingProfileShellWindow v
              (h.commonPeriod T) (h.stage T j) (h.period_pos T) u : ℂ)) := by
      funext u
      rw [h.window_eq T j u]
    rw [hwindow]
    exact
      ((shrinkingProfileShellWindow_contDiff
        v (h.commonPeriod T) (h.stage T j) (h.period_pos T)
        h.profile_smooth h.profile_pos).of_le
          (by exact le_top)).continuousLinearMap_comp
            Complex.ofRealCLM
  · intro T j u hu
    rw [h.window_eq T j u]
    exact
      shrinkingProfileShellWindow_supportRadius
        v (h.commonPeriod T) (h.stage T j) (h.period_pos T) hu
  · intro T j u
    rw [h.window_eq T j (-u), h.window_eq T j u]
    exact
      shrinkingProfileShellWindow_even
        v (h.commonPeriod T) (h.stage T j) (h.period_pos T)
        h.profile_even u
  · intro T j u hu
    rw [h.window_eq T j u] at hu
    exact
      shrinkingProfileShellWindow_support
        v (h.commonPeriod T) (h.stage T j) (h.period_pos T) hu
  · intro T j
    simpa using
      shrinkingProfileShellWindow_innerRadius_pos
        (h.commonPeriod T) (h.stage T j) (h.period_pos T)
  · intro T j
    simpa using
      shrinkingProfileShellWindow_outerRadius_lt
        (h.commonPeriod T) (h.stage T j) (h.period_pos T)

/-- Hence the annular realization gives collective complex-alias cancellation
without a separate cancellation premise. -/
theorem AnnularFamilyRealization.toCollectiveWindowRegularity
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : AnnularFamilyRealization F) :
    AggregateSynthesisBridge.CollectiveWindowRegularity F :=
  h.toRadialShellData.toCollectiveWindowRegularity

theorem tendsto_integral_frozen8686Window_sq
    (L : ℝ) (hL : 0 < L) :
    Tendsto
      (fun n : ℕ => ∫ u : ℝ, frozen8686Window L n hL u ^ 2)
      Filter.atTop
      (nhds
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile
            QuarticWindowWitnesses.v8686 (u / L))) := by
  apply tendsto_integral_shrinkingProfileWindow_sq
  · unfold QuarticWindowWitnesses.v8686
    fun_prop
  · intro x hx
    exact QuarticWindowWitnesses.v8686_pos hx

theorem tendsto_integral_frozen9506Window_sq
    (L : ℝ) (hL : 0 < L) :
    Tendsto
      (fun n : ℕ => ∫ u : ℝ, frozen9506Window L n hL u ^ 2)
      Filter.atTop
      (nhds
        (∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile
            QuarticWindowWitnesses.v9506 (u / L))) := by
  apply tendsto_integral_shrinkingProfileWindow_sq
  · unfold QuarticWindowWitnesses.v9506
    fun_prop
  · intro x hx
    exact QuarticWindowWitnesses.v9506_pos hx

/-- The R-8686 shrinking annular energies converge to their exact
physical normalization. -/
theorem tendsto_integral_frozen8686Window_sq_exact
    (L : ℝ) (hL : 0 < L) :
    Tendsto
      (fun n : ℕ => ∫ u : ℝ, frozen8686Window L n hL u ^ 2)
      Filter.atTop
      (nhds
        (L * (3815170470337249 / 3814073303040000 : ℝ))) := by
  simpa only [integral_supportedFullProfile_v8686_div L hL] using
    tendsto_integral_frozen8686Window_sq L hL

/-- The R-9506 shrinking annular energies converge to their exact physical
normalization. -/
theorem tendsto_integral_frozen9506Window_sq_exact
    (L : ℝ) (hL : 0 < L) :
    Tendsto
      (fun n : ℕ => ∫ u : ℝ, frozen9506Window L n hL u ^ 2)
      Filter.atTop
      (nhds
        (L * (5913507107 / 5913600000 : ℝ))) := by
  simpa only [integral_supportedFullProfile_v9506_div L hL] using
    tendsto_integral_frozen9506Window_sq L hL

end SmoothRadialShell
end Zeta85
end RH

end
