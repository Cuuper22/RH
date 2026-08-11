/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Statement.lean — **Phase B1**: the statement layer of the 85 % result and of the two
intermediate rungs.

Only the counting functions of the trusted definition layer occur here: `Zeta23.Ncount` and
`Zeta23.N0simple` (`Zeta23/Statement.lean` §1), which are character-for-character the `Ncount` and
`N0simple` of `comparator/ChallengeDeps.lean` §1.  Nothing from `RH/Zeta85/Hypotheses.lean` is
imported by this file: it says WHAT is claimed, not on what it rests.

Every statement is in the repository's ε-form for a liminf,
`liminf_{T→∞} X(T)/N(T) ≥ c  ↦  ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)`,
in both the dyadic (`(T, 2T]`) and the cumulative (`(0, T]`) variants, exactly as
`Zeta23/ThmD/Final.lean` states Theorem D.

## The three rungs

| rung | support σ | constant c | source |
|---|---|---|---|
| 1 | 101/100 | 0.67924886307 | `docs/run/07_root_gain_support_1p01.md` |
| 2 | 5/4 | 0.79721415286134 | `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` (1), (16) |
| 3 | 143/100 | 1893603832049143/2227707598259143 (= 0.8500235101…) | `docs/run/01_certificate_cycle1.md` (11) |

Rungs 1 and 2 carry the *truncated decimal* of their source (their optimal window is the solution of
an Euler equation with transcendental data, so its cost is not a rational); truncating the target
downward weakens the statement, never strengthens it.  This follows the repository's own precedent:
`comparator/Challenge/XiPrime.lean` states `0.85838`, `0.92919`, `0.86864`, `0.93432`.
`FINDINGS.md` §4 records the numerical check that each truncation is on the safe side.
Rung 3's constant is exact: `2 − 1/c_pc` with `c_pc` the rational of `RH/Zeta85/Certificate.lean`.
-/
import Zeta23.Statement

noncomputable section

namespace RH
namespace Zeta85

open Zeta23

/-! ## 1. The three constants -/

/-- Rung 1's certified proportion, `2 − D_{1.01} = 0.67924886307`
[07_root_gain_support_1p01.md, terminal result]. -/
def cRung101 : ℝ := 67924886307 / 100000000000

/-- Rung 2's certified proportion, `2 − D*_{5/4} = 0.79721415286134`
[08_arithmetic_cycle4_unconditional_79p7214.md (1), (16)]. -/
def cRung125 : ℝ := 79721415286134 / 100000000000000

/-- Rung 3's certified proportion, `2 − 1/c_pc = 1893603832049143/2227707598259143`
(= 0.8500235101…)  [01_certificate_cycle1.md (11)]. -/
def cRung143 : ℝ := 1893603832049143 / 2227707598259143

theorem cRung101_lt_cRung125 : cRung101 < cRung125 := by
  simp only [cRung101, cRung125]; norm_num

theorem cRung125_lt_cRung143 : cRung125 < cRung143 := by
  simp only [cRung125, cRung143]; norm_num

/-- The 85 % gate: rung 3 clears `17/20`. -/
theorem cRung143_gt_17_20 : (17 : ℝ) / 20 < cRung143 := by
  simp only [cRung143]; norm_num

/-- and clears the base repository's Theorem-D constant `2 − 1/c₁* = 0.6725007…`, whose value is
below rung 1. -/
theorem two_thirds_lt_cRung101 : (2 : ℝ) / 3 < cRung101 := by
  simp only [cRung101]; norm_num

/-! ## 2. The statements -/

/-- **Rung 1, dyadic**: `liminf_{T→∞} N₀ˢ(T,2T)/N(T,2T) ≥ 0.67924886307` — at least that proportion
of the nontrivial zeros of ζ with `T < Im ρ ≤ 2T`, counted with multiplicity, are simple zeros on the
critical line.  Support `101/100`. -/
def Rung101_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (cRung101 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)

/-- **Rung 1, cumulative**: the same for the windows `(0, T]`. -/
def Rung101_cumulative_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cRung101 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T

/-- **Rung 2, dyadic**: `liminf N₀ˢ(T,2T)/N(T,2T) ≥ 0.79721415286134`.  Support `5/4`. -/
def Rung125_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (cRung125 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)

/-- **Rung 2, cumulative**. -/
def Rung125_cumulative_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cRung125 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T

/-- **Rung 3 — the 85 % theorem, dyadic**:
`liminf_{T→∞} N₀ˢ(T,2T)/N(T,2T) ≥ 1893603832049143/2227707598259143` (= 0.8500235101…).
Support `143/100`, window `v(s) = 1 − (169/100)s²`. -/
def Rung143_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (cRung143 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)

/-- **Rung 3, cumulative**. -/
def Rung143_cumulative_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cRung143 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T

/-- **The 85 % corollary, dyadic**: `liminf N₀ˢ(T,2T)/N(T,2T) ≥ 17/20`. -/
def EightyFivePercent_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (17 / 20 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)

/-- **The 85 % corollary, cumulative**. -/
def EightyFivePercent_cumulative_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (17 / 20 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T

/-! ## 3. The corollary is a formal consequence of the rung -/

/-- Weakening the constant of an ε-form statement.  (The elementary step behind
"rung 3 ⟹ 85 %": `c' ≤ c` and `N ≥ 0`.) -/
theorem epsForm_mono {c c' : ℝ} (hc : c' ≤ c) {f g : ℝ → ℕ}
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (f T : ℝ) ≤ g T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c' - ε) * (f T : ℝ) ≤ g T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h ε hε
  refine ⟨T₀, fun T hT => le_trans ?_ (hT₀ T hT)⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- rung 3 (dyadic) implies the 85 % corollary (dyadic). -/
theorem eightyFive_of_rung143 (h : Rung143_statement) : EightyFivePercent_statement :=
  epsForm_mono (f := fun T => Ncount T (2 * T)) (g := fun T => N0simple T (2 * T))
    cRung143_gt_17_20.le h

/-- rung 3 (cumulative) implies the 85 % corollary (cumulative). -/
theorem eightyFive_cumulative_of_rung143 (h : Rung143_cumulative_statement) :
    EightyFivePercent_cumulative_statement :=
  epsForm_mono (f := fun T => Ncount 0 T) (g := fun T => N0simple 0 T) cRung143_gt_17_20.le h

end Zeta85
end RH

end
