-- Scalar implication only; no analytic moment input is assumed proved here.
import Mathlib

theorem refined_ordered_gap_scalar (delta : ℝ) (hd : 0 ≤ delta)
    (h : (471 : ℝ) / 40000 ≤ 6 * delta +
      (433377 : ℝ) / 100000 * Real.sqrt (2 * delta)) :
    (1 : ℝ) / 272000 < delta := by
  by_contra! hle
  have hs := Real.sq_sqrt (show 0 ≤ 2 * delta by positivity)
  have hr := Real.sqrt_nonneg (2 * delta)
  have hp : 0 ≤ (433377 : ℝ) / 100000 * Real.sqrt (2 * delta) -
      ((471 : ℝ) / 40000 - 6 * delta) := by linarith
  have hq : 0 ≤ (433377 : ℝ) / 100000 * Real.sqrt (2 * delta) +
      ((471 : ℝ) / 40000 - 6 * delta) := by nlinarith
  have hm := mul_nonneg hp hq
  have hmul := mul_nonneg hd (show 0 ≤ (1 : ℝ) / 272000 - delta by linarith)
  nlinarith

#print axioms refined_ordered_gap_scalar
