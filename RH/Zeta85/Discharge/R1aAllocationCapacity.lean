/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Inputs95

/-!
# A finite allocation-capacity obstruction for R1a

This file isolates the elementary inequality needed to test the current
`PrincipalCyclicBlock` boundary.  It does not assert the measure-theoretic
passage from that structure to the finite hypotheses below.

If a distinguished channel has period `L = mu * ell`, carries more than a
fraction `q` of the total energy `sigma * ell * A`, and at least `1-eps` of
its normalized local mass lies in an interval of relative width `p`, then a
pointwise full-profile cap `v0` forces

`(1-eps) * q * sigma * A < mu * p * v0`.

The reverse strict inequality holds by exact rational arithmetic for both
frozen R1a families already with `q = 2/5` and `eps = 1/100`.  Thus the only
remaining work for a full impossibility theorem is to derive the displayed
finite energy and local-mass inequalities from the existing fields of
`PrincipalCyclicBlock`; no new analytic estimate is involved.
-/

namespace RH
namespace Zeta85
namespace R1aAllocationCapacity

open Set QuarticWindowWitnesses

/-- The frozen `14999/10000` full profile is bounded by its central value on
the complete active cell `|s| <= mu*p/(2*sigma)`. -/
theorem v8686_active_le_center {s : ℝ} (hs : |s| ≤ edge8686) :
    v8686 s ≤ 1189 / 1000 := by
  have hmono := v8686_antitoneOn_edge
    (show (0 : ℝ) ∈ Icc 0 edge8686 by norm_num [edge8686])
    (show |s| ∈ Icc 0 edge8686 from ⟨abs_nonneg s, hs⟩)
    (abs_nonneg s)
  have heven : v8686 |s| = v8686 s := by
    by_cases hsign : 0 ≤ s
    · rw [abs_of_nonneg hsign]
    · rw [abs_of_nonpos (le_of_not_ge hsign)]
      simp only [v8686]
      ring
  rw [heven] at hmono
  norm_num [v8686] at hmono ⊢
  exact hmono

/-- The frozen `19999/10000` full profile is bounded by its central value on
the complete active cell `|s| <= mu*p/(2*sigma)`. -/
theorem v9506_active_le_center {s : ℝ} (hs : |s| ≤ edge9506) :
    v9506 s ≤ 2509 / 2000 := by
  have hmono := v9506_antitoneOn_edge
    (show (0 : ℝ) ∈ Icc 0 edge9506 by norm_num [edge9506])
    (show |s| ∈ Icc 0 edge9506 from ⟨abs_nonneg s, hs⟩)
    (abs_nonneg s)
  have heven : v9506 |s| = v9506 s := by
    by_cases hsign : 0 ≤ s
    · rw [abs_of_nonneg hsign]
    · rw [abs_of_nonpos (le_of_not_ge hsign)]
      simp only [v9506]
      ring
  rw [heven] at hmono
  norm_num [v9506] at hmono ⊢
  exact hmono

/-- Pure finite capacity contradiction.  `mass * energy <= L * p * v0` is
the integrated form of the pointwise allocation bound on the active cell. -/
theorem no_finite_capacity_configuration
    (sigma mu p A v0 ell q eps total energy L mass : ℝ)
    (hell : 0 < ell) (hq : 0 < q) (hsigma : 0 < sigma)
    (hA : 0 < A) (heps : 0 < 1 - eps)
    (htotal : total = sigma * ell * A)
    (hperiod : L = mu * ell)
    (henergy : q * total < energy)
    (hmass : 1 - eps ≤ mass)
    (hcapacity : mass * energy ≤ L * p * v0)
    (hnumeric : mu * p * v0 < (1 - eps) * q * sigma * A) : False := by
  have htotal_pos : 0 < total := by
    rw [htotal]
    positivity
  have henergy_pos : 0 < energy :=
    lt_trans (mul_pos hq htotal_pos) henergy
  have hmass_energy : (1 - eps) * energy ≤ mass * energy :=
    mul_le_mul_of_nonneg_right hmass henergy_pos.le
  have henergy_lower :
      (1 - eps) * (q * total) < (1 - eps) * energy :=
    mul_lt_mul_of_pos_left henergy heps
  have hnumeric_ell :
      ell * (mu * p * v0) < ell * ((1 - eps) * q * sigma * A) :=
    mul_lt_mul_of_pos_left hnumeric hell
  have hchain :
      (1 - eps) * (q * total) < L * p * v0 :=
    lt_of_lt_of_le henergy_lower (hmass_energy.trans hcapacity)
  rw [htotal, hperiod] at hchain
  nlinarith

/-- Exact numerical capacity gap for the support-`14999/10000` family. -/
theorem family14999_capacity_gap :
    (4999 / 10000 : ℝ) * (89 / 100) * (1189 / 1000) <
      (99 / 100) * (2 / 5) * (14999 / 10000) *
        (3815170470337249 / 3814073303040000) := by
  norm_num

/-- Exact numerical capacity gap for the support-`19999/10000` family. -/
theorem family19999_capacity_gap :
    (4999 / 10000 : ℝ) * (83 / 100) * (2509 / 2000) <
      (99 / 100) * (2 / 5) * (19999 / 10000) *
        (5913507107 / 5913600000) := by
  norm_num

/-- Terminal finite contradiction for the support-`14999/10000` constants. -/
theorem no_family14999_finite_configuration
    (ell total energy L mass : ℝ) (hell : 0 < ell)
    (htotal : total = (14999 / 10000) * ell *
      (3815170470337249 / 3814073303040000))
    (hperiod : L = (4999 / 10000) * ell)
    (henergy : (2 / 5) * total < energy)
    (hmass : 99 / 100 ≤ mass)
    (hcapacity : mass * energy ≤ L * (89 / 100) * (1189 / 1000)) : False := by
  exact no_finite_capacity_configuration
    (14999 / 10000) (4999 / 10000) (89 / 100)
    (3815170470337249 / 3814073303040000) (1189 / 1000)
    ell (2 / 5) (1 / 100) total energy L mass hell
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    htotal hperiod henergy (by norm_num at hmass ⊢; exact hmass)
    hcapacity (by norm_num)

/-- Terminal finite contradiction for the support-`19999/10000` constants. -/
theorem no_family19999_finite_configuration
    (ell total energy L mass : ℝ) (hell : 0 < ell)
    (htotal : total = (19999 / 10000) * ell *
      (5913507107 / 5913600000))
    (hperiod : L = (4999 / 10000) * ell)
    (henergy : (2 / 5) * total < energy)
    (hmass : 99 / 100 ≤ mass)
    (hcapacity : mass * energy ≤ L * (83 / 100) * (2509 / 2000)) : False := by
  exact no_finite_capacity_configuration
    (19999 / 10000) (4999 / 10000) (83 / 100)
    (5913507107 / 5913600000) (2509 / 2000)
    ell (2 / 5) (1 / 100) total energy L mass hell
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    htotal hperiod henergy (by norm_num at hmass ⊢; exact hmass)
    hcapacity (by norm_num)

end R1aAllocationCapacity
end Zeta85
end RH
