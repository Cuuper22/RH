/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/Exponents.lean — the **exponent bookkeeping** of the arithmetic cycles, PROVED.

This is the part of C4/C5 that is pure real arithmetic and therefore can be, and is, discharged:
every exponent comparison of `docs/run/03_arithmetic_cycle3.md` §2,
`docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §§1–3 and
`docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §3.  No axioms, no `sorry`.

Notation throughout: `A = B = H = T^η`, `M = N = T`, `X = T^{1+η}`, so `σ = 1 + η` is the connected
support and `T^{1+η}` is the trace scale.

What is **not** here (and is therefore still in `RH/Zeta85/Hypotheses.lean`): that the terminal
Heath–Brown family actually obeys these bounds, and that the blocks exhaust.  Only the arithmetic of
the exponents is discharged.
-/
import Mathlib

noncomputable section

namespace RH
namespace Zeta85
namespace Exponents

/-! ## 1. The BBLR outside factor and the two error exponents

`(ABMNH²)^{1/4}` with `A = B = H = T^η`, `M = N = T` has exponent
`(η + η + 1 + 1 + 2η)/4 = 1/2 + η`  [08 (4)]. -/

/-- `08 (4)`: the outside factor's exponent is `1/2 + η`. -/
theorem outside_factor_exponent (η : ℝ) : (η + η + 1 + 1 + 2 * η) / 4 = 1 / 2 + η := by ring

/-- `08 (5)`: the first (non-cuspidal / large-divisor) error exponent, with the **corrected** first
factor `AB = T^{2η}`, is `E_A = T^{1/2+3η}`. -/
theorem EA_exponent (η : ℝ) : (1 / 2 + η) + 2 * η = 1 / 2 + 3 * η := by ring

/-- `08 (6)`: the Watt error exponent is
`E_W = T^{1/2+η}·T^{η/4}·T^{η/2}·T^{(2η+2)/8} = T^{3/4+2η}`. -/
theorem EW_exponent (η : ℝ) :
    (1 / 2 + η) + η / 4 + η / 2 + (2 * η + 2) / 8 = 3 / 4 + 2 * η := by ring

/-- `03 (16)`: the exponent that the **misquoted** first factor `(AB)^{1/2} = T^η` would give,
`E₁ = T^{1/2+2η}`.  Recorded so that the discrepancy with `EA_exponent` is explicit; see
`FINDINGS.md` §3. -/
theorem E1_misquoted_exponent (η : ℝ) : (1 / 2 + η) + η = 1 / 2 + 2 * η := by ring

/-- the misquote is not harmless: the two exponents differ by exactly `η`. -/
theorem misquote_gap (η : ℝ) : (1 / 2 + 3 * η) - (1 / 2 + 2 * η) = η := by ring

/-! ## 2. The trace-grade conditions  [08 (7)] -/

/-- `E_A` is trace-grade (`≤ T^{1+η}`) exactly for `η ≤ 1/4`. -/
theorem EA_traceGrade_iff (η : ℝ) : 1 / 2 + 3 * η ≤ 1 + η ↔ η ≤ 1 / 4 := by
  constructor <;> intro h <;> linarith

/-- `E_W` is trace-grade exactly for `η ≤ 1/4`. -/
theorem EW_traceGrade_iff (η : ℝ) : 3 / 4 + 2 * η ≤ 1 + η ↔ η ≤ 1 / 4 := by
  constructor <;> intro h <;> linarith

/-- The misquoted `E₁` would be trace-grade for `η ≤ 1/2` — this is why
`docs/run/03_arithmetic_cycle3.md` (19) reports "the first term permits `η < 1/2`" while
`docs/run/08` (7) correctly reports `η ≤ 1/4` for both terms. -/
theorem E1_misquoted_traceGrade_iff (η : ℝ) : 1 / 2 + 2 * η ≤ 1 + η ↔ η ≤ 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- **The BBLR black-box ceiling**: both errors are trace-grade iff `η ≤ 1/4`, i.e. iff the
connected support `σ = 1 + η` is at most `5/4`  [08 §4, Barrier theorem]. -/
theorem bblr_blackbox_ceiling (η : ℝ) :
    (1 / 2 + 3 * η ≤ 1 + η ∧ 3 / 4 + 2 * η ≤ 1 + η) ↔ η ≤ 1 / 4 := by
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; exact ⟨by linarith, by linarith⟩

/-- and at `κ > 0`, `η = 1/4 − κ` gives the strict savings of `08 (T3)–(T5)`:
`E_A = T^{5/4−3κ}`, `E_W = T^{5/4−2κ}`, trace scale `T^{5/4−κ}`. -/
theorem bblr_savings (κ : ℝ) (hκ : 0 < κ) :
    (1 / 2 + 3 * (1 / 4 - κ) = 5 / 4 - 3 * κ) ∧
    (3 / 4 + 2 * (1 / 4 - κ) = 5 / 4 - 2 * κ) ∧
    (1 + (1 / 4 - κ) = 5 / 4 - κ) ∧
    (5 / 4 - 3 * κ < 5 / 4 - κ) ∧ (5 / 4 - 2 * κ < 5 / 4 - κ) :=
  ⟨by ring, by ring, by ring, by linarith, by linarith⟩

/-! ## 3. The 85 % target exponents  [08 (8)–(9)] -/

/-- At the 85 % exponent `η = 43/100` (the rational benchmark `σ = 143/100`):
`E_A = T^{1.79}`, `E_W = T^{1.61}`, trace scale `T^{1.43}`; the misquoted `E₁` would be `T^{1.36}`.
`docs/run/08` (8) writes `E_A = T^{1.78881155261138…}` for the irrational
`η = 0.42960385087046…`; at the rational benchmark it is exactly `1.79`. -/
theorem exponents_at_43_100 :
    (1 / 2 + 3 * (43 / 100 : ℝ) = 179 / 100) ∧
    (3 / 4 + 2 * (43 / 100 : ℝ) = 161 / 100) ∧
    (1 + (43 / 100 : ℝ) = 143 / 100) ∧
    (1 / 2 + 2 * (43 / 100 : ℝ) = 136 / 100) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- the two deficits at the 85 % target: `E_A` misses by `T^{0.36}`, `E_W` by `T^{0.18}`. -/
theorem deficits_at_43_100 :
    (179 / 100 - 143 / 100 : ℝ) = 36 / 100 ∧ (161 / 100 - 143 / 100 : ℝ) = 18 / 100 := by
  refine ⟨by norm_num, by norm_num⟩

/-! ## 4. Cycle 5's exponents  [12 (18)–(19)] -/

/-- `12 (18)`: with `P_d ≍ T^{η+1/2}/d`, `Q_d ≍ T^{1/2}/d`, `H_d ≍ T^η/d`,
`P_dQ_d ≍ T^{1+η}/d²` and `P_dH_d ≍ T^{1/2+2η}/d²`. -/
theorem cycle5_scales (η : ℝ) :
    ((η + 1 / 2) + 1 / 2 = 1 + η) ∧ ((η + 1 / 2) + η = 1 / 2 + 2 * η) :=
  ⟨by ring, by ring⟩

/-- `12 (19)`: the three pieces of the cycle-5 remainder and their trace-grade conditions.
`P_dQ_d` is always at the natural signed scale `T^{1+η}`; `P_dH_d` is trace-grade iff `η ≤ 1/2`;
`H²` iff `η ≤ 1`.  Hence the local ceiling is `η = 1/2`, i.e. `σ < 3/2`. -/
theorem cycle5_traceGrade (η : ℝ) :
    (1 + η ≤ 1 + η) ∧ (1 / 2 + 2 * η ≤ 1 + η ↔ η ≤ 1 / 2) ∧ (2 * η ≤ 1 + η ↔ η ≤ 1) := by
  refine ⟨le_rfl, ⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- `12 (21)`: the gain of the signed-shift-first route over the Watt route is `T^{2η−1/2}`, which
is a genuine gain exactly for `η > 1/4`. -/
theorem cycle5_gain (η : ℝ) :
    (1 / 2 + 3 * η) - (1 + η) = 2 * η - 1 / 2 ∧ (0 < 2 * η - 1 / 2 ↔ 1 / 4 < η) := by
  refine ⟨by ring, ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- at `η = 43/100 < 1/2` the cycle-5 exponents ARE trace-grade: `1/2 + 2η = 1.36 < 1.43`. -/
theorem cycle5_ok_at_43_100 : (1 / 2 + 2 * (43 / 100 : ℝ)) < 1 + (43 / 100 : ℝ) := by norm_num

/-! ## 5. The CSQD exponents  [08 (26)–(28)] -/

/-- `08 (27)`: the two lines of (CSQD) have exponents `1/2 + 2η` and `3/4 + (3/2)η`, both below
`1 + η` for every fixed `η < 1/2`. -/
theorem csqd_traceGrade (η : ℝ) (_h0 : 0 < η) (h : η < 1 / 2) :
    1 / 2 + 2 * η < 1 + η ∧ 3 / 4 + (3 / 2) * η < 1 + η := by
  refine ⟨by linarith, by linarith⟩

/-! ## 6. Support ↔ shift exponent -/

/-- `θ = η/(1+η)`, the shift exponent relative to `X`  [03 (1)]; at the rational benchmark
`η = 43/100` this is `43/143`. -/
theorem theta_at_benchmark : (43 / 100 : ℝ) / (1 + 43 / 100) = 43 / 143 := by norm_num

/-- `02 (26)`: `43/143 > 8/33`, the Matomäki–Radziwiłł–Tao shift threshold, with the stated gap
`275/4719`. -/
theorem mrt_gap : (43 / 143 : ℝ) - 8 / 33 = 275 / 4719 := by norm_num

/-- `01 (10)`: the MRT threshold `H ≥ M^{8/33}` corresponds to `α ≥ 33/25`. -/
theorem mrt_alpha : (1 : ℝ) / (1 - 8 / 33) = 33 / 25 := by norm_num

end Exponents
end Zeta85
end RH

end
