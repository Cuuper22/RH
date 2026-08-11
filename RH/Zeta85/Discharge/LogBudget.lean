/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/LogBudget.lean — **C7, the logarithmic-power audit**, treated adversarially and
PROVED (no axioms, no `sorry`).

## The question

`docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` (2) delivers

    R_HB ≪ (T^{1+η} + T^{1/2+2η})·(log T)^C ,        0 < η < 1/2,                          (12.2)

with `C` "fixed by the finite identity and the fixed smooth weights", and §5 asserts that "the two
explicit logarithmic weights from the two von Mangoldt factors are below the accepted `Tℓ³` trace
normalization after recombination".  The trace budget is `o(T·L³)` against a main term of size
`≍ T·L³` (`docs/run/02_certificate_cycle2.md` (16)).  Does the fixed `(log T)^C` survive?

## The accounting, written out with every logarithm named

Fix the connected support `σ = 1 + η`, so `X = T^σ` is the prime length and `H = X/T = T^η` the shift
scale.  Three facts from the sources, each with its equation number.

1. **The coefficient.**  On a dyadic prime block `n ≍ Y` and at a shift `h ≍ H_Y = Y/T`, the complete
   coefficient multiplying `Λ(n)Λ(n+h)` in the second moment obeys
   `|W_{Y,h}(n)| ≪ (L/Y)·min(T, Y/h) + log L/Y = L·T/Y + O(log L/Y)`
   (`02_certificate_cycle2.md` (10); the `min` equals `T` at `h ≍ H_Y`).  **One** power of `L`.
2. **Entry scale.**  Hence an aggregate (already `h`-summed, sign retained) correlation remainder of
   size `E` at length `Y` enters the second moment at scale `(T·L/Y)·E`
   (`01_arithmetic_cycle1.md` §4: "an aggregate correlation error `E(M,H)` … enters at scale roughly
   `(T/M)E(M,H)`, **up to powers of L**" — that parenthesis is the imprecision resolved here; the
   power is exactly one, from 1).
3. **Multiplicity of blocks.**  The displayed sum in `02_certificate_cycle2.md` (14) runs over
   `O(log X)` dyadic prime scales `Y`, but its inner sum is directly over `h`; the formula does not
   itself display a second dyadic shift-scale sum.  Thus a literal blockwise triangle inequality
   costs **one** further logarithm.  A second logarithm is lost only if the `h`-sum is separately
   dyadicized and the resulting estimates are again summed by triangle inequality.  The latter is
   a useful fully adversarial model, but it is not forced by (14).

Where the budget's three logarithms sit (this answers `12` §5 explicitly): the trace main term
`T·L³/(2πλ²)·[∫v² + λ∬min(λ|s−t|,1)vv]` of `02_certificate_cycle2.md` (16) carries `L²` from the two
von Mangoldt weights `Λ(n)/√n`, `Λ(n+h)/√(n+h)` summed over the `h`-range, and one further `L` from
the height kernel — the same `L` that reappears in 1.  So the two von Mangoldt logarithms are
**spent**: they are part of the main term, not free room for the error.  The free room is one power
of `L`, and the entry scale in 2 already consumes it.

Putting `E ≪ X·(log T)^C` (that is (12.2) at `Y = X`) into 2:

    contribution  ≍  (T·L/X)·X·(log T)^C  =  T·(log T)^{C+1}                         (generous)
    contribution  ≍  (log T)   · T·(log T)^{C+1} = T·(log T)^{C+2}        (literal Y-dyadic)
    contribution  ≍  (log T)^2 · T·(log T)^{C+1} = T·(log T)^{C+3}        (fully triangle-summed)

against `budget = T·(log T)^3`.  Hence

    generous single-block reading:   closes  ⟺  C + 1 < 3  ⟺  **C < 2**
    literal Y-dyadic reading:        closes  ⟺  C + 2 < 3  ⟺  **C < 1**
    fully triangle-summed reading:   closes  ⟺  C + 3 < 3  ⟺  **C < 0**

The three pairs of `*_closes` / `*_fails` theorems below prove these dichotomies in Lean.

## The verdict (R2: state it, do not absorb)

None of the three thresholds is available.  The terminal family of `08` §2 is produced by a Heath–Brown identity
of a fixed depth `K` chosen so large that every truncated irregular factor has length at most
`X^{1/K} < H·T^{−10ε}`; that forces `K > (1+η)/η` — `K ≥ 4` already at `η = 43/100`, and the strict
inequality gives `K ≥ 6` at `η = 1/4`.  A depth-`K` identity replaces each von Mangoldt factor by `O(K)` divisor-type
convolutions whose mean value over a dyadic block is of size `(log X)^{K−1}`, and the BBLR weight
hypotheses `W_i^{(j)} ≪ (ABMN)^ε` do not remove them.  Hence `C ≥ K − 1 ≥ 3 > 2 > 0`:

    C + 1 ≥ 4 > 3,    C + 2 ≥ 5 > 3,    C + 3 ≥ 6 > 3.

**The log powers do not close.**  The `(log T)^C` of (12.2) exceeds the trace budget by at least
`(log T)^{C−2} ≥ log T` in the most generous reading, by `(log T)^{C−1} ≥ (log T)^2` in the literal
`Y`-dyadic reading, and by `(log T)^C ≥ (log T)^3` in the fully triangle-summed model.

There is also a stronger statement-level gap: the convenient aggregate criterion `(AS)` of
`01_arithmetic_cycle1.md` §4 demands `≪_A X·(log X)^{−A}` for **every** `A`, whereas (12.2) supplies a
logarithmic loss `(log T)^{+C}`.  `(AS)` is stronger than the exact weighted budget (18), so this is
not an independent necessity argument; it explains why (12.2) cannot discharge the Lean predicate
`SignedPairTraceGrade` as that predicate is presently stated.

This gap is **not** repaired anywhere in the run and is not repaired here.  It is the reason
`RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2` is an axiom stated at the strength the transfer
needs, rather than a theorem derived from (12.2).  See `AXIOMS.md` and `FINDINGS.md` §7.  The 85 %
target is **not** weakened to accommodate it (R2): the target stays
`1893603832049143/2227707598259143`, and the exact blocking statement is named.

The two lower rungs are unaffected: at `η < 1/4` the BBLR errors of `08` (5)–(6) are *power*-saving
relative to trace scale (`RH.Zeta85.Exponents.bblr_savings`: `T^{−3κ}` and `T^{−2κ}` against
`T^{−κ}`), and `power_beats_log` below shows that a fixed power beats every fixed logarithmic loss.
That is the precise sense in which rungs 1 and 2 rest on strictly weaker inputs than rung 3.
-/
import Mathlib

open Filter Topology Asymptotics

noncomputable section

namespace RH
namespace Zeta85
namespace LogBudget

/-! ## 1. The two sides of the budget -/

/-- The trace main term and hence the budget scale, `T·(log T)³`
[`02_certificate_cycle2.md` (16)]; the `λ`-dependent constants do not affect the log count. -/
def budget (T : ℝ) : ℝ := T * (Real.log T) ^ (3 : ℝ)

/-- The normalized contribution of an aggregate remainder of size `X·(log T)^C`, in the **generous**
single-block reading: the entry scale `(T·L/X)` of `01_arithmetic_cycle1.md` §4 contributes exactly
one power of `L`, so the contribution is `T·(log T)^{C+1}`. -/
def contribution (C T : ℝ) : ℝ := T * (Real.log T) ^ (C + 1)

/-- The fully triangle-summed model, charging one logarithm for dyadic prime scales and another for
an additional dyadic decomposition of the `h`-sum: `T·(log T)^{C+3}`. -/
def contributionDyadic (C T : ℝ) : ℝ := T * (Real.log T) ^ (C + 3)

/-- The literal blockwise reading of `02_certificate_cycle2.md` (14): one `O(log X)` sum over
dyadic prime scales `Y`, while the inner `h`-sum is kept intact.  This gives
`T·(log T)^{C+2}`. -/
def contributionPrimeDyadic (C T : ℝ) : ℝ := T * (Real.log T) ^ (C + 2)

/-! ## 2. The three dichotomies -/

private lemma log_rpow_tendsto_zero {p : ℝ} (hp : p < 0) :
    Tendsto (fun T : ℝ => (Real.log T) ^ p) atTop (𝓝 0) := by
  have h : Tendsto (fun T : ℝ => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have h2 : Tendsto (fun x : ℝ => x ^ p) atTop (𝓝 0) := by
    have hx := tendsto_rpow_neg_atTop (y := -p) (by linarith)
    simpa [neg_neg] using hx
  exact h2.comp h

private lemma ratio_eq {a : ℝ} {T : ℝ} (hTpos : 0 < T) (hlog : 0 < Real.log T) :
    (T * (Real.log T) ^ a) / (T * (Real.log T) ^ (3 : ℝ)) = (Real.log T) ^ (a - 3) := by
  rw [mul_div_mul_left _ _ (ne_of_gt hTpos), ← Real.rpow_sub hlog]

/-- **Generous reading: the budget closes iff `C < 2`** — positive half. -/
theorem budget_closes {C : ℝ} (hC : C < 2) :
    Tendsto (fun T : ℝ => contribution C T / budget T) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ (log_rpow_tendsto_zero (p := C + 1 - 3) (by linarith))
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  simp only [contribution, budget]
  exact (ratio_eq (lt_trans zero_lt_one hT) (Real.log_pos hT)).symm

/-- **Generous reading: the budget closes iff `C < 2`** — negative half.  For `C ≥ 2` the ratio is
eventually `≥ 1`: the fixed `(log T)^C` does **not** survive the normalization. -/
theorem budget_fails {C : ℝ} (hC : 2 ≤ C) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ contribution C T / budget T := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hlog1 : (1 : ℝ) ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).mpr hT
  have hlog : (0 : ℝ) < Real.log T := lt_of_lt_of_le zero_lt_one hlog1
  rw [contribution, budget, ratio_eq hTpos hlog]
  exact Real.one_le_rpow hlog1 (by linarith)

/-- **Literal `Y`-dyadic reading: the budget closes iff `C < 1`** — positive half. -/
theorem budget_primeDyadic_closes {C : ℝ} (hC : C < 1) :
    Tendsto (fun T : ℝ => contributionPrimeDyadic C T / budget T) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ (log_rpow_tendsto_zero (p := C + 2 - 3) (by linarith))
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  simp only [contributionPrimeDyadic, budget]
  exact (ratio_eq (lt_trans zero_lt_one hT) (Real.log_pos hT)).symm

/-- **Literal `Y`-dyadic reading: the budget closes iff `C < 1`** — negative half. -/
theorem budget_primeDyadic_fails {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ contributionPrimeDyadic C T / budget T := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hlog1 : (1 : ℝ) ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).mpr hT
  have hlog : (0 : ℝ) < Real.log T := lt_of_lt_of_le zero_lt_one hlog1
  rw [contributionPrimeDyadic, budget, ratio_eq hTpos hlog]
  exact Real.one_le_rpow hlog1 (by linarith)

/-- **Fully triangle-summed reading (both scale decompositions charged): the budget closes iff
`C < 0`** — positive half. -/
theorem budget_dyadic_closes {C : ℝ} (hC : C < 0) :
    Tendsto (fun T : ℝ => contributionDyadic C T / budget T) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ (log_rpow_tendsto_zero (p := C + 3 - 3) (by linarith))
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  simp only [contributionDyadic, budget]
  exact (ratio_eq (lt_trans zero_lt_one hT) (Real.log_pos hT)).symm

/-- **Fully triangle-summed reading: the budget closes iff `C < 0`** — negative half. -/
theorem budget_dyadic_fails {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ contributionDyadic C T / budget T := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hlog1 : (1 : ℝ) ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).mpr hT
  have hlog : (0 : ℝ) < Real.log T := lt_of_lt_of_le zero_lt_one hlog1
  rw [contributionDyadic, budget, ratio_eq hTpos hlog]
  exact Real.one_le_rpow hlog1 (by linarith)

/-- **The verdict at the Heath–Brown depth actually forced.**  At `η = 43/100` the depth satisfies
`K > (1+η)/η = 143/43 > 3`, so `K ≥ 4` and `C ≥ K − 1 ≥ 3`; all three thresholds fail. -/
theorem depth_at_85 : (3 : ℝ) < (1 + 43 / 100) / (43 / 100) := by norm_num

/-- At the 85-percent exponent, a depth-three truncated factor has exponent `143/300`, exceeding
the shift exponent `43/100` by exactly `7/150`. -/
theorem depth_three_excess :
    (1 + (43 : ℝ) / 100) / 3 - 43 / 100 = 7 / 150 := by norm_num

/-- Depth four is the first integer depth whose raw atom is shorter than the shift scale; its
exponent margin is exactly `29/400`. -/
theorem depth_four_margin :
    43 / 100 - (1 + (43 : ℝ) / 100) / 4 = 29 / 400 := by norm_num

/-- Completing one inverse variable with a fixed-modulus square-root estimate and then summing the
remaining `a`, `h`, and `q` variables absolutely has exponent `2η + 3/4`.  At `η = 43/100` this
is worse than the natural trace exponent `1 + η` by exactly `9/50`. -/
theorem fixed_modulus_weil_excess :
    (2 * ((43 : ℝ) / 100) + 3 / 4) - (1 + 43 / 100) = 9 / 50 := by norm_num

/-- Consequently, with `C ≥ 3`, both the generous threshold `C < 2` and the fully triangle-summed
threshold `C < 0` are violated, and `budget_fails` / `budget_dyadic_fails` apply. -/
theorem verdict {C : ℝ} (hC : 3 ≤ C) :
    (∀ᶠ T : ℝ in atTop, 1 ≤ contribution C T / budget T) ∧
    (∀ᶠ T : ℝ in atTop, 1 ≤ contributionDyadic C T / budget T) :=
  ⟨budget_fails (by linarith), budget_dyadic_fails (by linarith)⟩

/-- At the forced `C ≥ 3`, all three accounting models fail. -/
theorem verdict_all {C : ℝ} (hC : 3 ≤ C) :
    (∀ᶠ T : ℝ in atTop, 1 ≤ contribution C T / budget T) ∧
    (∀ᶠ T : ℝ in atTop, 1 ≤ contributionPrimeDyadic C T / budget T) ∧
    (∀ᶠ T : ℝ in atTop, 1 ≤ contributionDyadic C T / budget T) :=
  ⟨budget_fails (by linarith), budget_primeDyadic_fails (by linarith),
    budget_dyadic_fails (by linarith)⟩

/-! ## 3. Why the two lower rungs are unaffected -/

/-- **A fixed power beats every fixed logarithmic loss**: for `δ > 0` and every real `C`,
`T^{−δ}·(log T)^C → 0`.  This is the sense in which the power-saving BBLR errors of `08` (5)–(6) at
`η < 1/4` are trace-grade *whatever* the Heath–Brown depth's logarithmic cost, while the
merely-polylogarithmic cycle-5 bound (12.2) is not. -/
theorem power_beats_log {δ C : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℝ => T ^ (-δ) * (Real.log T) ^ C) atTop (𝓝 0) := by
  have h0 : Tendsto (fun u : ℝ => u ^ C * Real.exp (-δ * u)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C δ hδ
  have h1 := h0.comp Real.tendsto_log_atTop
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hE : Real.exp (-δ * Real.log T) = T ^ (-δ) := by
    rw [Real.rpow_def_of_pos hT, mul_comm]
  simp only [Function.comp_apply]
  rw [hE]
  ring

end LogBudget
end Zeta85
end RH

end
