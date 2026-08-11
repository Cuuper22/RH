/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Main.lean — **Phase D**: the three rungs, assembled.

Given `RH/Zeta85/Hypotheses.lean`, everything here is proved.  The chain, for each rung, is

  window cost `D` at support `σ`   (Phase A for `σ = 143/100`; Axioms 6/7 for the other two)
    ── Axiom 8 (trace transfer) ──►  `TwoTraceCert zetaZeroConfig D`
    ── `RH.Zeta85.epsForm_of_twoTraceCert` ──►  `(2 − D − ε)·N(T,2T) ≤ N₀ˢ(T,2T)` eventually
    ── `Zeta23.cumulative_of_dyadic` ──►  the same for the windows `(0,T]`.

The middle arrow is the Phase-A3 count lemma applied with `s = N₀ˢ`, `d = (N − s)/2`, `p = 0`
(`RH/Zeta85/Transfer.lean`); the last arrow is the base repository's own dyadic→cumulative passage,
used with exactly the arguments `Zeta23/ThmD/Final.lean:141` uses for Theorem D.

At `σ = 143/100`, `D = D_pc = 2561811364469143/2227707598259143 = 1.1499764899… < 23/20`
(`RH.Zeta85.DPC_lt`), so the count lemma's charge is `4 − D_pc > 4 − 23/20` and the conclusion is
`N₀ˢ ≥ (2 − D_pc)N = (1893603832049143/2227707598259143)N`, exceeding `17/20` by
`1047470577429/44554151965182860` (`RH.Zeta85.margin_eq`).
-/
import RH.Zeta85.Hypotheses
import RH.Zeta85.Discharge.AliasFallback
import RH.Zeta85.Stability
import Zeta23.Final

open Filter Topology

noncomputable section

namespace RH
namespace Zeta85

open Zeta23 Hypotheses

/-! ## 0. Bridging the abstract counting functions to ζ's -/

/-- On `zetaZeroConfig`, the abstract `N` is `Zeta23.Ncount`. -/
private lemma zc_N (T₁ T₂ : ℝ) : zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ :=
  zetaZeros_N zetaSeam T₁ T₂

/-- On `zetaZeroConfig`, the abstract `N0s` is `Zeta23.N0simple`. -/
private lemma zc_N0s (T₁ T₂ : ℝ) : zetaZeroConfig.N0s T₁ T₂ = N0simple T₁ T₂ :=
  zetaZeros_N0s zetaSeam T₁ T₂

/-- the ε-form for `zetaZeroConfig` transported to the statement layer's counting functions. -/
private theorem epsForm_zeta {D : ℝ} (h : TwoTraceCert zetaZeroConfig D) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - D - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have h' := epsForm_of_twoTraceCert h
  simpa only [zc_N, zc_N0s] using h'

/-- the base repository's dyadic → cumulative passage, specialized to `N₀ˢ`.  Same call as
`Zeta23/ThmD/Final.lean:141`. -/
private theorem cumulative {c : ℝ}
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => N0simple_add' zetaSeam) h

/-! ## 1. Rung 1 — support 101/100, at least 0.67924886307 -/

/-- The two-trace certificate at support `101/100`.
Axioms: `bblr_error_bound`, `signedPair_traceGrade_lt_5_4`, `windowCost_101`,
`traceTransfer_saturated`. -/
theorem cert101 : TwoTraceCert zetaZeroConfig (2 - cRung101) :=
  traceTransfer_saturated (101 / 100) (2 - cRung101) (by norm_num) (by norm_num)
    windowCost_101
    (signedPair_traceGrade_lt_5_4 bblr_error_bound (101 / 100) (by norm_num) (by norm_num))

/-- **Rung 1, dyadic**: `liminf_{T→∞} N₀ˢ(T,2T)/N(T,2T) ≥ 0.67924886307`
[docs/run/07_root_gain_support_1p01.md]. -/
theorem rung101 : Rung101_statement := by
  simpa only [Rung101_statement, sub_sub_cancel] using epsForm_zeta cert101

/-- **Rung 1, cumulative**: the same for the windows `(0,T]`. -/
theorem rung101_cumulative : Rung101_cumulative_statement := cumulative rung101

/-! ## 2. Rung 2 — support 5/4, at least 0.79721415286134 -/

/-- The two-trace certificate at a support just below `5/4`.
Axioms: `bblr_error_bound`, `signedPair_traceGrade_lt_5_4`, `windowCost_125`,
`traceTransfer_saturated` — the same four as rung 1, with `windowCost_101` replaced by
`windowCost_125`. -/
theorem cert125 : TwoTraceCert zetaZeroConfig (2 - cRung125) := by
  obtain ⟨σ, hσ1, hσ2, hσw⟩ := windowCost_125
  exact traceTransfer_saturated σ (2 - cRung125) hσ1 (by linarith) hσw
    (signedPair_traceGrade_lt_5_4 bblr_error_bound σ hσ1 hσ2)

/-- **Rung 2, dyadic**: `liminf_{T→∞} N₀ˢ(T,2T)/N(T,2T) ≥ 0.79721415286134`
[docs/run/08_arithmetic_cycle4_unconditional_79p7214.md (1), (16)]. -/
theorem rung125 : Rung125_statement := by
  simpa only [Rung125_statement, sub_sub_cancel] using epsForm_zeta cert125

/-- **Rung 2, cumulative**. -/
theorem rung125_cumulative : Rung125_cumulative_statement := cumulative rung125

/-! ## 3. Rung 3 — support 143/100, at least 1893603832049143/2227707598259143 -/

/-- The two-trace certificate at support `143/100`, cost `D_pc`.
Axioms: `bblr_poisson_blocks`, `shiu_majorant`, `signedPair_traceGrade_lt_3_2`,
`traceTransfer_saturated`.  Note that the window cost is **not** an axiom here: it is
`RH.Zeta85.windowCost_143`, proved in `RH/Zeta85/Certificate.lean` from the three exact window
moments of `RH/Zeta85/Window.lean`. -/
theorem cert143 : TwoTraceCert zetaZeroConfig DPC :=
  traceTransfer_saturated lam DPC (by norm_num [lam]) (by norm_num [lam])
    windowCost_143
    (signedPair_traceGrade_lt_3_2 bblr_poisson_blocks shiu_majorant lam
      (by norm_num [lam]) (by norm_num [lam]))

/-- **Rung 3 — the 85 % theorem, dyadic**:
`liminf_{T→∞} N₀ˢ(T,2T)/N(T,2T) ≥ 1893603832049143/2227707598259143` (= 0.8500235101…)
[docs/run/01_certificate_cycle1.md (11), docs/run/00_FINAL_RESULT_85_PERCENT_CROSSED.md]. -/
theorem rung143 : Rung143_statement := by
  simpa only [Rung143_statement, cRung143, two_sub_DPC] using epsForm_zeta cert143

/-- **Rung 3, cumulative**. -/
theorem rung143_cumulative : Rung143_cumulative_statement := cumulative rung143

/-! ## 4. The 85 % corollary -/

/-- **At least 85 % of the zeros are simple and on the critical line, dyadic form.** -/
theorem eightyFive : EightyFivePercent_statement := eightyFive_of_rung143 rung143

/-- **At least 85 %, cumulative form.** -/
theorem eightyFive_cumulative : EightyFivePercent_cumulative_statement :=
  eightyFive_cumulative_of_rung143 rung143_cumulative

/-! ## 5. The strict margin, in the source's own form

`docs/run/01_hybrid_cycle1.md` (2)–(3): the trace budget `tr(B_T²) ≤ (23/20 − η)N` gives
`N₀ˢ ≥ (17/20 + η)N`.  At the certificate's own cost, `η = 23/20 − D_pc`, and the resulting margin
over `17/20` is the `1047470577429/44554151965182860` of `01_certificate_cycle1.md` (12). -/

/-- the certificate's slack in the trace budget, `23/20 − D_pc`, is exactly the margin. -/
theorem budget_slack_eq_margin : (23 : ℝ) / 20 - DPC = (2 - 1 / cPC) - 17 / 20 := by
  rw [margin_eq, DPC]; norm_num

/-- and it is strictly positive: `D_pc = 1.1499764899… < 23/20`. -/
theorem budget_slack_pos : (0 : ℝ) < 23 / 20 - DPC := by rw [DPC]; norm_num

/-- **The 85 % statement with the margin displayed**: for every `ε > 0` and all large `T`,
`N₀ˢ(T,2T) ≥ (17/20 + η − ε)·N(T,2T)` with
`η = 1047470577429/44554151965182860 > 0`. -/
theorem rung143_with_margin :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (17 / 20 + 1047470577429 / 44554151965182860 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  have heq : (17 : ℝ) / 20 + 1047470577429 / 44554151965182860 = cRung143 := by
    simp only [cRung143]; norm_num
  simpa only [Rung143_statement, heq] using rung143

end Zeta85
end RH

end
