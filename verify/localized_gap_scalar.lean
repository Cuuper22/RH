-- Scalar implication only for the localized cubic certificate
-- (docs/research/multiwindow_20261003.md). No analytic moment input is
-- assumed proved here. The constants are outward roundings of the exact
-- certificate in verify/multiwindow_certificate.py:
--   kappa_phi >= 25729/1000000, q = 6 sup|phi| <= 60011/10000,
--   C_phi <= 64909/10000.
import Mathlib

theorem localized_gap_scalar (delta kappa q C : ℝ) (hd : 0 ≤ delta)
    (hk : (25729 : ℝ) / 1000000 ≤ kappa)
    (hq0 : 0 ≤ q) (hq : q ≤ (60011 : ℝ) / 10000)
    (hC : C ≤ (64909 : ℝ) / 10000)
    (h : kappa ≤ q * delta + Real.sqrt delta * C) :
    (1 : ℝ) / 64200 < delta := by
  by_contra! hle
  set s := Real.sqrt delta with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = delta := Real.sq_sqrt hd
  -- q * delta is at most the rounded q times 1/64200
  have h1 : q * delta ≤ (60011 : ℝ) / 10000 * (1 / 64200) :=
    mul_le_mul hq hle hd (by norm_num)
  -- s * C is at most s times the rounded C
  have h2 : s * C ≤ s * ((64909 : ℝ) / 10000) := mul_le_mul_of_nonneg_left hC hs0
  set m : ℝ := (25729 : ℝ) / 1000000 - (60011 : ℝ) / 10000 * (1 / 64200) with hm
  have hm0 : 0 < m := by rw [hm]; norm_num
  -- (C_hi s)^2 <= C_hi^2 / 64200 < m^2, hence C_hi s < m
  have hsq : ((64909 : ℝ) / 10000 * s) ^ 2 < m ^ 2 := by
    have : ((64909 : ℝ) / 10000 * s) ^ 2 = ((64909 : ℝ) / 10000) ^ 2 * delta := by
      rw [mul_pow, hss]
    rw [this, hm]
    nlinarith
  have hlt : (64909 : ℝ) / 10000 * s < m := by
    have hnn : 0 ≤ (64909 : ℝ) / 10000 * s := by positivity
    nlinarith [sq_nonneg ((64909 : ℝ) / 10000 * s - m)]
  rw [hm] at hlt
  linarith

#print axioms localized_gap_scalar
