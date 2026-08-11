/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the project LICENSE.
SPDX-License-Identifier: Apache-2.0

Exact audit of the rational quartic dual in
95maybe/16_root95_cycle3_quartic_fixed_point_86p7233.md.
The spectral-moment and principal-compression hypotheses are not asserted here.
-/
import Mathlib

namespace Zeta23
namespace RH95Audit

abbrev qa : ℚ := -(81 : ℚ) / 100
abbrev qb : ℚ := (8 : ℚ) / 55
abbrev qc : ℚ := (1027 : ℚ) / 1000

abbrev qp0 : ℚ := -(2371761774702144 : ℚ) / 175337011095659525
abbrev qp1 : ℚ := (6467268805064496 : ℚ) / 35067402219131905
abbrev qp2 : ℚ := (7947849444403220 : ℚ) / 21040441331479143
abbrev qp3 : ℚ := -(260716671644000 : ℚ) / 21040441331479143
abbrev qp4 : ℚ := -(4472897011000000 : ℚ) / 21040441331479143
abbrev qLevel : ℚ := (703830875873538941 : ℚ) / 2169788731719000000

/-- Rational quartic dual polynomial. -/
def quarticP (z : ℚ) : ℚ := qp0 + qp1 * z + qp2 * z ^ 2 + qp3 * z ^ 3 + qp4 * z ^ 4

/-- The six interpolation/tangency constraints in equation (4). -/
theorem quarticP_constraints :
    quarticP qa = 0 ∧
    (qp1 + 2 * qp2 * qa + 3 * qp3 * qa ^ 2 + 4 * qp4 * qa ^ 3) = 0 ∧
    quarticP qb = qb ^ 2 ∧
    (qp1 + 2 * qp2 * qb + 3 * qp3 * qb ^ 2 + 4 * qp4 * qb ^ 3) = 2 * qb ∧
    quarticP qc = qLevel ∧
    (qp1 + 2 * qp2 * qc + 3 * qp3 * qc ^ 2 + 4 * qp4 * qc ^ 3) = 0 := by
  norm_num [quarticP, qa, qb, qc, qp0, qp1, qp2, qp3, qp4, qLevel]

/-- Exact factorization used on the negative half-line. -/
theorem quarticP_factor (z : ℚ) :
    quarticP z =
      -44 * (100 * z + 81) ^ 2 *
          (254141875625 * z ^ 2 - 396896391260 * z + 24647314448) /
          526011033286978575 := by
  norm_num [quarticP, qp0, qp1, qp2, qp3, qp4]
  ring

/-- Exact factorization of `z² - P(z)`. -/
theorem quartic_sq_sub_factor (z : ℚ) :
    z ^ 2 - quarticP z =
      (55 * z - 8) ^ 2 *
          (36966091000000 * z ^ 2 + 12908455164000 * z + 111176333189163) /
          526011033286978575 := by
  norm_num [quarticP, qp0, qp1, qp2, qp3, qp4]
  ring

/-- Exact factorization of `L - P(z)`. -/
theorem quartic_level_sub_factor (z : ℚ) :
    qLevel - quarticP z =
      11 * (1000 * z - 1027) ^ 2 *
          (406627001000000 * z ^ 2 + 858913375658000 * z + 612795015790783) /
          21040441331479143000000 := by
  norm_num [quarticP, qLevel, qp0, qp1, qp2, qp3, qp4]
  ring

/-- First dual feasibility inequality: `P(z) ≤ 0` for `z ≤ 0`. -/
theorem quarticP_nonpos {z : ℚ} (hz : z ≤ 0) : quarticP z ≤ 0 := by
  rw [quarticP_factor]
  have hq : 0 < 254141875625 * z ^ 2 - 396896391260 * z + 24647314448 := by
    nlinarith [sq_nonneg z]
  have hprod : 0 ≤ (100 * z + 81) ^ 2 *
      (254141875625 * z ^ 2 - 396896391260 * z + 24647314448) :=
    mul_nonneg (sq_nonneg _) hq.le
  have hnum : -44 * ((100 * z + 81) ^ 2 *
      (254141875625 * z ^ 2 - 396896391260 * z + 24647314448)) ≤ 0 := by
    nlinarith
  exact div_nonpos_of_nonpos_of_nonneg hnum (by norm_num)

/-- Second dual feasibility inequality: `P(z) ≤ z²` for `z ≥ 0`. -/
theorem quarticP_le_sq {z : ℚ} (hz : 0 ≤ z) : quarticP z ≤ z ^ 2 := by
  have hq : 0 ≤ 36966091000000 * z ^ 2 + 12908455164000 * z + 111176333189163 := by
    nlinarith [sq_nonneg z]
  have hfactor : 0 ≤ z ^ 2 - quarticP z := by
    rw [quartic_sq_sub_factor]
    positivity
  linarith

/-- Third dual feasibility inequality: `P(z) ≤ L` for `z ≥ 0`. -/
theorem quarticP_le_level {z : ℚ} (hz : 0 ≤ z) : quarticP z ≤ qLevel := by
  have hq : 0 ≤ 406627001000000 * z ^ 2 + 858913375658000 * z + 612795015790783 := by
    nlinarith [sq_nonneg z]
  have hfactor : 0 ≤ qLevel - quarticP z := by
    rw [quartic_level_sub_factor]
    positivity
  linarith

abbrev quarticA : ℚ := qp0 + qp2 / 3 + 4 * qp4 / 15
abbrev quarticMu : ℚ := (499 : ℚ) / 1000
abbrev quarticD0 : ℚ := (1134325953 : ℚ) / 1000000000
abbrev quarticC0 : ℚ := quarticMu ^ 2 * qLevel / 2
abbrev quarticFixed : ℚ :=
  ((2 - quarticD0) + quarticMu ^ 3 * quarticA - quarticC0) / (1 - quarticC0)

/-- Exact moment functional value in equation (7). -/
theorem quarticA_exact :
    quarticA = (29297479972587068 : ℚ) / 526011033286978575 := by
  norm_num [quarticA, qp0, qp2, qp4]

/-- Exact fixed-point fraction printed in cycle 3. -/
theorem quarticFixed_exact :
    quarticFixed =
      (35020104682575465786049152683 : ℚ) /
      40381438885077201583684516123 := by
  norm_num [quarticFixed, quarticD0, quarticMu, quarticA, quarticC0,
    qLevel, qp0, qp2, qp4]

/-- The source's exact rational checkpoint exceeds 86.7 percent. -/
theorem quarticFixed_gt_867 : (867 : ℚ) / 1000 < quarticFixed := by
  norm_num [quarticFixed, quarticD0, quarticMu, quarticA, quarticC0,
    qLevel, qp0, qp2, qp4]

/--
Pure scalar fixed-point assembly.  The premise is exactly the inequality that the archive
claims to obtain from spectral stability and the four-moment dual.
-/
theorem quartic_fixed_point_of_scalar_inequality {z : ℚ}
    (h : (1 - quarticC0) * z ≥
      (2 - quarticD0) + quarticMu ^ 3 * quarticA - quarticC0) :
    quarticFixed ≤ z := by
  have hc : 0 < 1 - quarticC0 := by
    norm_num [quarticC0, quarticMu, qLevel]
  rw [quarticFixed]
  exact (div_le_iff₀ hc).2 h

end RH95Audit
end Zeta23
