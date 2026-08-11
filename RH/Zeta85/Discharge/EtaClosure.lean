/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/EtaClosure.lean -- exact exponent audit of the proposed
`1 / 2 < eta < 1` terminal factorization in `docs/run/18_arithmetic95_cycle1_support_2_93p2283.md`.

This file proves only unconditional algebra and limiting statements.  In
particular, it does not assert that a Heath--Brown block can be repartitioned
at an arbitrary real exponent.  The balanced `K = 3`, `j = 2` block below is
a legal counterexample to the literal relabel-only construction used in that
source: after the unique whole-variable grouping of exponent `eta`, its two
remaining atoms have exponent `1 / 2`, so no subproduct has exponent
`1 - eta` when `1 / 2 < eta < 1`.

See `docs/audit/eta_gt_half_factorization.md` for the exact method class and
the stronger coefficient construction that would be needed to leave it.
-/
import RH.Zeta85.Discharge.LogBudget

open Filter Topology

noncomputable section

namespace RH
namespace Zeta85
namespace EtaClosure

/-! ## 1. The available power margin in the preliminary replacement -/

/-- Half of the gap between the terminal exponent `eta` and one.  Splitting
each balanced smooth atom of exponent `1 / 2` into exponents `delta eta` and
`eta / 2` would give the requested aggregate split, since
`delta eta + eta / 2 = 1 / 2`.  Such a coefficient identity is not supplied
by mere relabelling. -/
def delta (eta : ℝ) : ℝ := (1 - eta) / 2

/-- For `1 / 2 < eta < 1`, the proposed refinement exponent is strictly
between zero and one half. -/
theorem delta_mem {eta : ℝ} (heta0 : 1 / 2 < eta) (heta1 : eta < 1) :
    0 < delta eta ∧ delta eta < 1 / 2 := by
  simp only [delta]
  constructor <;> linarith

/-- The exact refinement identity suggested by `delta`: a new split with
exponents `delta eta` and `eta/2` would reproduce a balanced half-length
atom. -/
theorem delta_add_half_eta (eta : ℝ) : delta eta + eta / 2 = 1 / 2 := by
  simp only [delta]
  ring

/-- The exponent of the preliminary error `H^2 (AM)^eps` under
`H = A = T^eta` and `M = T`. -/
def preliminaryExponent (eta eps : ℝ) : ℝ := 2 * eta + (1 + eta) * eps

/-- The natural trace exponent, `TH = T^(1+eta)`. -/
def traceExponent (eta : ℝ) : ℝ := 1 + eta

/-- Exact exponent form of the condition
`H^2 (AM)^eps = o(T H)`: it has a strict power saving whenever
`eps < (1-eta)/(1+eta)`. -/
theorem preliminary_exponent_lt {eta eps : ℝ} (heta0 : 1 / 2 < eta)
    (heps : eps < (1 - eta) / (1 + eta)) :
    preliminaryExponent eta eps < traceExponent eta := by
  have hden : 0 < 1 + eta := by linarith
  have hmul : eps * (1 + eta) < 1 - eta :=
    (lt_div_iff₀ hden).mp heps
  simp only [preliminaryExponent, traceExponent]
  nlinarith

/-- The positive power margin left by the preliminary replacement. -/
theorem preliminary_saving_pos {eta eps : ℝ} (heta0 : 1 / 2 < eta)
    (heps : eps < (1 - eta) / (1 + eta)) :
    0 < traceExponent eta - preliminaryExponent eta eps := by
  linarith [preliminary_exponent_lt heta0 heps]

/-- The preliminary error and trace powers written as actual real functions. -/
def preliminaryPower (eta eps T : ℝ) : ℝ := T ^ preliminaryExponent eta eps

def tracePower (eta T : ℝ) : ℝ := T ^ traceExponent eta

/-- The literal quotient of the preliminary power by the trace power tends to
zero under the same sharp exponent condition. -/
theorem preliminary_ratio_tendsto_zero {eta eps : ℝ} (heta0 : 1 / 2 < eta)
    (heps : eps < (1 - eta) / (1 + eta)) :
    Tendsto (fun T : ℝ => preliminaryPower eta eps T / tracePower eta T)
      atTop (nhds 0) := by
  have hsaving := preliminary_saving_pos heta0 heps
  have hlim :
      Tendsto
        (fun T : ℝ => T ^ (-(traceExponent eta - preliminaryExponent eta eps)))
        atTop (nhds 0) := by
    simpa using (LogBudget.power_beats_log (C := 0) hsaving)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [preliminaryPower, tracePower]
  rw [← Real.rpow_sub hT]
  congr 1
  ring

/-- The normalized preliminary error, even with any fixed explicit logarithmic
power `C`, tends to zero.  This is the precise `o`-statement; the logarithm is
not hidden in an `epsilon`. -/
theorem preliminary_with_log_is_o {eta eps C : ℝ} (heta0 : 1 / 2 < eta)
    (heps : eps < (1 - eta) / (1 + eta)) :
    Tendsto
      (fun T : ℝ =>
        T ^ (-(traceExponent eta - preliminaryExponent eta eps)) *
          (Real.log T) ^ C)
      atTop (nhds 0) :=
  LogBudget.power_beats_log (preliminary_saving_pos heta0 heps)

/-! ## 2. Conditional single-block algebra of the proposed split -/

/-- If variables of the requested lengths actually exist, the asymmetric
choice `A=H=T^eta`, `M1=T^(1-eta)` gives `P=A M1=T`. -/
theorem asymmetric_P_exponent (eta : ℝ) : eta + (1 - eta) = 1 := by ring

/-- With the dummy choice `N1=1`, both terms `P Q` and `P H` are exactly at
the trace power.  This proves the local algebra only; it does not construct
the factorization. -/
theorem asymmetric_block_exponents (eta : ℝ) :
    (eta + (1 - eta)) + (eta + 0) = traceExponent eta ∧
      (eta + (1 - eta)) + eta = traceExponent eta := by
  simp only [traceExponent]
  constructor <;> ring

/-! ## 3. A legal balanced `K=3`, `j=2` relabelling obstruction -/

/-- In a `K=3`, `j=2` Heath--Brown summand, take the two truncated atoms at
exponent `eta/2` and the two unrestricted atoms at exponent `1/2`.  Their
product has exponent `1+eta`, and the truncated atoms lie below the `K=3`
cutoff `(1+eta)/3` throughout the audited range. -/
theorem balanced_j2_K3_legal {eta : ℝ} (heta0 : 1 / 2 < eta) (heta1 : eta < 1) :
    0 < eta / 2 ∧
      eta / 2 < (1 + eta) / 3 ∧
      2 * (eta / 2) + 2 * (1 / 2 : ℝ) = 1 + eta := by
  refine ⟨by linarith, by linarith, by ring⟩

/-- Among whole-variable groupings of the two `eta/2` atoms and the two
`1/2` atoms, the only group of exponent exactly `A=eta` uses both truncated
atoms and no smooth atom. -/
theorem balanced_j2_A_group_unique {eta : ℝ} (heta0 : 1 / 2 < eta)
    (heta1 : eta < 1) {r s : ℕ} (hr : r ≤ 2) (hs : s ≤ 2)
    (hgroup : (r : ℝ) * (eta / 2) + (s : ℝ) * (1 / 2) = eta) :
    r = 2 ∧ s = 0 := by
  interval_cases r <;> interval_cases s <;> norm_num at hgroup ⊢ <;> linarith

/-- After the unique `A`-group has been removed, every whole-variable
subproduct of the two balanced smooth atoms has exponent `k/2`,
`k in {0,1,2}`.  None equals the requested `1-eta`. -/
theorem balanced_j2_no_asymmetric_M1 {eta : ℝ} (heta0 : 1 / 2 < eta)
    (heta1 : eta < 1) {k : ℕ} (hk : k ≤ 2) :
    (k : ℝ) * (1 / 2) ≠ 1 - eta := by
  intro heq
  interval_cases k <;> norm_num at heq <;> linarith

/-- A completely rational instance of the obstruction, used by the
independent verifier: `eta=3/4`, truncated atoms `3/8`, smooth atoms `1/2`,
and target `M1` exponent `1/4`. -/
theorem balanced_j2_three_quarters :
    (3 / 8 : ℝ) < (1 + 3 / 4) / 3 ∧
      2 * (3 / 8 : ℝ) + 2 * (1 / 2) = 1 + 3 / 4 ∧
      (∀ k : ℕ, k ≤ 2 → (k : ℝ) * (1 / 2) ≠ 1 / 4) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k hk heq
  interval_cases k <;> norm_num at heq

/-! ## 4. What the signed-shift-first estimate gives on that block -/

/-- On the balanced block `M1=N1=T^(1/2)`, both reciprocal variables have
exponent `eta+1/2`.  The `P Q` term exceeds the trace target by exactly
`eta`. -/
theorem balanced_PQ_excess (eta : ℝ) :
    ((eta + 1 / 2) + (eta + 1 / 2)) - traceExponent eta = eta := by
  simp only [traceExponent]
  ring

/-- The other signed-shift-first term `P H` exceeds the trace target by
exactly `eta-1/2`. -/
theorem balanced_PH_excess (eta : ℝ) :
    ((eta + 1 / 2) + eta) - traceExponent eta = eta - 1 / 2 := by
  simp only [traceExponent]
  ring

/-- Thus both terms are strictly above trace grade in the audited range. -/
theorem balanced_signedShift_misses {eta : ℝ} (heta : 1 / 2 < eta) :
    traceExponent eta < (eta + 1 / 2) + (eta + 1 / 2) ∧
      traceExponent eta < (eta + 1 / 2) + eta := by
  constructor
  · linarith [balanced_PQ_excess eta]
  · linarith [balanced_PH_excess eta]

/-! ## 5. The independent logarithmic obstruction -/

/-- Even if the asymmetric power algebra were supplied by a new coefficient
construction, the literal prime-dyadic trace accounting closes only for
`C<1`.  Every explicit `C>=1` fails. -/
theorem literal_log_budget_fails {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ LogBudget.contributionPrimeDyadic C T / LogBudget.budget T :=
  LogBudget.budget_primeDyadic_fails hC

/-- The first integer exponent on the failing side of the literal threshold. -/
theorem literal_log_budget_C1_fails :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ LogBudget.contributionPrimeDyadic 1 T / LogBudget.budget T :=
  literal_log_budget_fails (by norm_num)

end EtaClosure
end Zeta85
end RH

end
