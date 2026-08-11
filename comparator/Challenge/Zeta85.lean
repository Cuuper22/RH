/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
comparator/Challenge/Zeta85.lean — CHALLENGE: the conditional 85 % theorem and its two lower rungs.

Trusted vocabulary: `ChallengeDeps` (the counting functions of the nontrivial zeros of Mathlib's
`riemannZeta`) over Mathlib.  Only `Ncount` and `N0simple` are used.

Eight statements, in the repository's ε-form for a liminf
(`liminf_{T→∞} X(T)/N(T) ≥ c  ↦  ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)`), each in the dyadic
window `(T, 2T]` and in the cumulative window `(0, T]`:

  * support 101/100:  N₀ˢ/N ≥ 0.67924886307
  * support 5/4:      N₀ˢ/N ≥ 0.79721415286134
  * support 143/100:  N₀ˢ/N ≥ 1893603832049143/2227707598259143 (= 0.8500235101…)
  * the corollary:    N₀ˢ/N ≥ 17/20

**These statements are CONDITIONAL.**  Unlike every other topic in this repository, they are not
proved from Mathlib alone: `Solution.Zeta85` derives them from the eight named axioms of
`RH/Zeta85/Hypotheses.lean`, and `comparator/config-zeta85.json` lists those axioms in
`permitted_axioms` alongside `propext`, `Classical.choice`, `Quot.sound`.  A reader must therefore
read `RH/Zeta85/Hypotheses.lean` (and `AXIOMS.md`) in addition to this file to know what is being
claimed.  This is the one documented deviation from the "Rules for the trusted side" of
`comparator/README.md` (rule 5).

The `sorry`s below are deliberate (this is the challenge side); expect "declaration uses 'sorry'"
warnings when building this module.
-/
import ChallengeDeps

noncomputable section

/-- **Support 101/100 — at least 0.67924886307 of the zeros are simple and on the critical line**
(dyadic windows): for every ε > 0 and all sufficiently large T,
`(0.67924886307 − ε)·N(T,2T) ≤ N₀ˢ(T,2T)`.  The zeros with `T < Im ρ ≤ 2T` are counted WITH
multiplicity on the left and as DISTINCT simple on-line points on the right. -/
theorem zeta85_rung_support_101_over_100 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (67924886307 / 100000000000 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-- **Support 101/100**, cumulative form: windows `(0, T]`. -/
theorem zeta85_rung_support_101_over_100_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (67924886307 / 100000000000 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  sorry

/-- **Support 5/4 — at least 0.79721415286134 simple and on the critical line** (dyadic windows). -/
theorem zeta85_rung_support_5_over_4 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (79721415286134 / 100000000000000 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-- **Support 5/4**, cumulative form. -/
theorem zeta85_rung_support_5_over_4_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (79721415286134 / 100000000000000 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  sorry

/-- **Support 143/100 — at least 1893603832049143/2227707598259143 (= 0.8500235101…) of the zeros
are simple and on the critical line** (dyadic windows).  This is the headline statement: the exact
rational is `2 − 1/c_pc` for the certificate constant
`c_pc = 2227707598259143/2561811364469143` of the quadratic window `v(s) = 1 − (169/100)s²` at
Fourier support `λ = 143/100`. -/
theorem zeta85_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1893603832049143 / 2227707598259143 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  sorry

/-- **Support 143/100**, cumulative form. -/
theorem zeta85_simple_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1893603832049143 / 2227707598259143 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  sorry

/-- **At least 85 % of the zeros are simple and on the critical line** (dyadic windows) — the
corollary of the previous statement, since
`1893603832049143/2227707598259143 − 17/20 = 1047470577429/44554151965182860 > 0`. -/
theorem zeta85_eighty_five_percent :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (17 / 20 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-- **At least 85 %**, cumulative form. -/
theorem zeta85_eighty_five_percent_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (17 / 20 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  sorry

end
