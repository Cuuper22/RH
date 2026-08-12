/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
comparator/Solution/Zeta85.lean — SOLUTION for the topic `Zeta85`: the same eight statements as
`comparator/Challenge/Zeta85.lean`, byte-for-byte, delegated to `RH.Zeta85`.

Conditional: these proofs use the five axioms of `RH/Zeta85/Hypotheses.lean` in addition to
`propext`, `Classical.choice`, `Quot.sound`.  `comparator/config-zeta85.json` lists them; the exact
per-theorem dependency is in `AXIOMS.md`.
-/
import RH.Zeta85.Main
import ChallengeDeps

noncomputable section

/-- the solution-side constant of rung 1 is the challenge's literal. -/
private theorem cRung101_eq : RH.Zeta85.cRung101 = 67924886307 / 100000000000 := rfl

/-- the solution-side constant of rung 2 is the challenge's literal. -/
private theorem cRung125_eq : RH.Zeta85.cRung125 = 79721415286134 / 100000000000000 := rfl

/-- the solution-side constant of rung 3 is the challenge's literal. -/
private theorem cRung143_eq : RH.Zeta85.cRung143 = 1893603832049143 / 2227707598259143 := rfl

theorem zeta85_rung_support_101_over_100 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (67924886307 / 100000000000 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  RH.Zeta85.rung101

theorem zeta85_rung_support_101_over_100_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (67924886307 / 100000000000 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  RH.Zeta85.rung101_cumulative

theorem zeta85_rung_support_5_over_4 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (79721415286134 / 100000000000000 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  RH.Zeta85.rung125

theorem zeta85_rung_support_5_over_4_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (79721415286134 / 100000000000000 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  RH.Zeta85.rung125_cumulative

theorem zeta85_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1893603832049143 / 2227707598259143 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  RH.Zeta85.rung143

theorem zeta85_simple_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1893603832049143 / 2227707598259143 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  RH.Zeta85.rung143_cumulative

theorem zeta85_eighty_five_percent :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (17 / 20 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  RH.Zeta85.eightyFive

theorem zeta85_eighty_five_percent_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (17 / 20 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  RH.Zeta85.eightyFive_cumulative

end
