/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSBlockMomentBridge
import RH.Zeta85.Discharge.SmoothRadialShell

/-!
# Annular profiles for the Rudnick--Sarnak diagonal

This file shifts the smooth annular energy profiles from the centered
half-interval to the unit interval required by the strict-support
four-point theorem.  Every finite stage is smooth and compactly supported;
the slow-diagonal theorem then makes the fixed-test estimate compatible
with the improving annular stage.
-/

open Filter MeasureTheory Set
open scoped ContDiff Topology

noncomputable section

namespace RH.Zeta85.RSAnnularDiagonal

open Zeta23 SmoothRadialShell

/-- The squared annular window energy shifted from
`[-1/2,1/2]` to `[0,1]`. -/
def annularRSProfile
    (v : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  shrinkingProfileShellWindow v 1 n (by norm_num) (x - 1 / 2) ^ 2

/-- Every finite annular profile is infinitely differentiable. -/
theorem annularRSProfile_contDiff
    (v : ℝ → ℝ) (n : ℕ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x) :
    ContDiff ℝ ∞ (annularRSProfile v n) := by
  unfold annularRSProfile
  exact
    ((shrinkingProfileShellWindow_contDiff
      v 1 n (by norm_num) hv hpos).comp
        (contDiff_id.sub contDiff_const)).pow 2

/-- A nonzero annular profile point lies in the closed unit interval. -/
theorem annularRSProfile_support
    (v : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hx : annularRSProfile v n x ≠ 0) :
    (0 : ℝ) ≤ x ∧ x ≤ 1 := by
  have hshell :
      shrinkingProfileShellWindow
        v 1 n (by norm_num) (x - 1 / 2) ≠ 0 := by
    intro hzero
    apply hx
    simp [annularRSProfile, hzero]
  have hsupp :=
    shrinkingProfileShellWindow_support
      v 1 n (by norm_num) hshell
  have hout :=
    shrinkingProfileShellWindow_outerRadius_lt
      1 n (by norm_num)
  have habs : |x - 1 / 2| < (1 : ℝ) / 2 :=
    lt_trans hsupp.2 hout
  rw [abs_lt] at habs
  constructor <;> linarith

/-- Every finite annular profile has compact support. -/
theorem annularRSProfile_hasCompactSupport
    (v : ℝ → ℝ) (n : ℕ) :
    HasCompactSupport (annularRSProfile v n) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  by_contra hnonzero
  exact hx (annularRSProfile_support v n x hnonzero)

/-- The fixed-test four-point theorem follows a slowly improving sequence of
the explicit annular profiles.  Only convergence of their evaluated scalar
main terms remains to identify the terminal frozen scalar. -/
theorem RS1996ZetaInputs.exists_tendsto_annularProfile_diagonal
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (v : ℝ → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, |x| ≤ (1 : ℝ) / 2 → 0 < v x)
    (g : Fin 4 → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j))
    (A : ℂ)
    (hmain : Tendsto
      (fun n =>
        RSBlockMomentBridge.frozenQuarticRSMain
          (annularRSProfile v n) g)
      atTop (nhds A)) :
    ∃ stage : ℝ → ℕ,
      Tendsto stage atTop atTop ∧
      Tendsto
        (fun T =>
          RSBlockMomentBridge.normalizedFrozenQuarticRSStatistic
            (annularRSProfile v (stage T)) g T)
        atTop (nhds A) := by
  apply
    RSBlockMomentBridge.RS1996ZetaInputs.exists_tendsto_profile_diagonal
      hrs (fun n => annularRSProfile v n)
  · intro n
    exact annularRSProfile_hasCompactSupport v n
  · intro n
    exact (annularRSProfile_contDiff v n hv hpos).of_le (by
      change (1 : ℕ∞) ≤ ⊤
      exact le_top)
  · intro n x hx
    exact annularRSProfile_support v n x hx
  · exact hg
  · exact hmain

end RH.Zeta85.RSAnnularDiagonal

end
