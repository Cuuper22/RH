/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.TrimmedMoment

/-!
# Aggregate quartic blocks

The terminal quartic contribution is additive before the finite tail bound is taken.  This file
packages that change of order: apply weak duality to several normalized blocks and sum the resulting
inequalities, instead of forcing the entire limiting block density into one physical channel.
-/

open Filter Finset
open scoped BigOperators Topology

noncomputable section

namespace RH.Zeta85.TrimmedMoment

/-- Finite trimmed-moment duality is additive across an arbitrary finite family of blocks. -/
theorem finite_trimmed_quartic_dual_sum
    {ι A : Type*} [Fintype ι] [Fintype A]
    (q : Quartic) (cap : ℝ)
    (value weight removed : A → ι → ℝ)
    (m1 m2 m3 m4 alpha : A → ℝ)
    (hdual : DualFeasible q cap)
    (h : ∀ a, TrimmedMomentInputs (value a) (weight a) (removed a)
      (m1 a) (m2 a) (m3 a) (m4 a) (alpha a)) :
    ∑ a, (q.p0 + q.p1 * m1 a + q.p2 * m2 a + q.p3 * m3 a + q.p4 * m4 a -
      alpha a * cap) ≤
      ∑ a, residualTail (value a) (weight a) (removed a) := by
  exact Finset.sum_le_sum fun a _ =>
    finite_trimmed_quartic_dual q cap (value a) (weight a) (removed a)
      (m1 a) (m2 a) (m3 a) (m4 a) (alpha a) hdual (h a)

/-- Repeating the same limiting block `r` times multiplies its quartic score by `r`. -/
theorem constant_quartic_score_sum (r : ℕ) (q : Quartic) (m1 m2 m3 m4 : ℝ) :
    ∑ _a : Fin r,
        (q.p0 + q.p1 * m1 + q.p2 * m2 + q.p3 * m3 + q.p4 * m4) =
      r * (q.p0 + q.p1 * m1 + q.p2 * m2 + q.p3 * m3 + q.p4 * m4) := by
  simp
  ring

/-- The terminal R-9506 arithmetic has enough room for five half-density subblocks even if the
full-matrix cost is only the already proved support-`1.43` cost.  This is the numerical reason to
sum blocks before applying the tail bound. -/
theorem aggregate_five_clears_9506 :
    (95063832187565 / 100000000000000 : ℝ) <
      (5 * Terminal9506.mu * Terminal9506.AP +
          2 - (2 - 1893603832049143 / 2227707598259143) - Terminal9506.cap / 2) /
        (1 - Terminal9506.cap / 2) := by
  norm_num [Terminal9506.mu, Terminal9506.AP, Terminal9506.dual,
    Terminal9506.cap, Terminal9506.m2, Terminal9506.m3, Terminal9506.m4,
    topHatM2, topHatM3, topHatM4, Terminal9506.width]

/-! ## Finite-to-asymptotic aggregate transfer -/

/-- The normalized lower bound obtained after summing all blocks before division by the total
zero count. -/
def normalizedAggregate {r : ℕ}
    (N err : ℝ → ℝ) (blockDim blockScore : Fin r → ℝ → ℝ)
    (base denom : ℝ) (T : ℝ) : ℝ :=
  ((∑ j, blockDim j T / N T * blockScore j T) + base - err T / N T) / denom

/-- Generic aggregate-block transfer.  It is the multi-block analogue of the repository's
single-block `asymptotic_eps_transfer`, but assumes only the summed finite inequality. -/
theorem aggregate_asymptotic_eps_transfer {r : ℕ}
    (N lower err : ℝ → ℝ) (blockDim blockScore : Fin r → ℝ → ℝ)
    (μ AP base denom target : ℝ)
    (hdenom : 0 < denom)
    (hdim : ∀ j, Tendsto (fun T => blockDim j T / N T) atTop (nhds μ))
    (hscore : ∀ j, Tendsto (blockScore j) atTop (nhds AP))
    (herr : err =o[atTop] N)
    (hNpos : ∀ᶠ T in atTop, 0 < N T)
    (hfinite : ∀ᶠ T in atTop,
      (∑ j, blockDim j T * blockScore j T) + base * N T ≤
        denom * lower T + err T)
    (hstrict : target < (r * μ * AP + base) / denom) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (target - ε) * N T ≤ lower T := by
  have hterms : ∀ j, Tendsto
      (fun T => blockDim j T / N T * blockScore j T) atTop (nhds (μ * AP)) :=
    fun j => (hdim j).mul (hscore j)
  have hsum : Tendsto
      (fun T => ∑ j, blockDim j T / N T * blockScore j T) atTop
      (nhds (r * μ * AP)) := by
    have hs := tendsto_finset_sum Finset.univ (fun j _ => hterms j)
    simpa [mul_assoc] using hs
  have herror := herr.tendsto_div_nhds_zero
  have hnorm : Tendsto
      (normalizedAggregate N err blockDim blockScore base denom) atTop
      (nhds ((r * μ * AP + base) / denom)) := by
    have hbase : Tendsto (fun _ : ℝ => base) atTop (nhds base) := tendsto_const_nhds
    have hnumerator : Tendsto
        (fun T => (∑ j, blockDim j T / N T * blockScore j T) + base - err T / N T)
        atTop (nhds (r * μ * AP + base - 0)) :=
      (hsum.add hbase).sub herror
    have hlim := hnumerator.div_const denom
    change Tendsto
      (fun T => ((∑ j, blockDim j T / N T * blockScore j T) + base - err T / N T) /
        denom) atTop (nhds ((r * μ * AP + base) / denom))
    simpa only [sub_zero] using hlim
  have hlower : ∀ᶠ T in atTop,
      target < normalizedAggregate N err blockDim blockScore base denom T :=
    hnorm.eventually (Ioi_mem_nhds hstrict)
  have htarget : ∀ᶠ T in atTop, target * N T ≤ lower T := by
    filter_upwards [hlower, hfinite, hNpos] with T hlowerT hfiniteT hNT
    rw [normalizedAggregate] at hlowerT
    have hlowerDen := (lt_div_iff₀ hdenom).mp hlowerT
    have hrewrite :
        (∑ j, blockDim j T / N T * blockScore j T) + base - err T / N T =
          ((∑ j, blockDim j T * blockScore j T) + base * N T - err T) / N T := by
      have hterm : ∀ j,
          blockDim j T / N T * blockScore j T =
            (blockDim j T * blockScore j T) / N T := by
        intro j
        ring
      simp_rw [hterm, ← Finset.sum_div]
      field_simp [hNT.ne']
    rw [hrewrite] at hlowerDen
    have hlowerN := (lt_div_iff₀ hNT).mp hlowerDen
    have hscaled : denom * (target * N T) < denom * lower T := by
      nlinarith
    have : target * N T < lower T := by nlinarith
    exact this.le
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (htarget.and hNpos)
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨htargetT, hNT⟩ := hT₀ T hT
  exact (mul_le_mul_of_nonneg_right (by linarith) hNT.le).trans htargetT

end RH.Zeta85.TrimmedMoment
