-- Scalar corollary only: does not assert the analytic moment inputs.
-- Checked through AXLE on lean-4.31.0, 2026-09-05; not a repository build.
import Mathlib

theorem ordered_gap_scalar (epsilon : ℝ) (he : 0 ≤ epsilon)
    (h : (1 : ℝ) / 100 ≤ 42 * Real.sqrt (2 * epsilon)) :
    (1 : ℝ) / 35280000 ≤ epsilon := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * epsilon by positivity)
  have hr := Real.sqrt_nonneg (2 * epsilon)
  nlinarith [sq_nonneg (Real.sqrt (2 * epsilon) - (1 : ℝ) / 4200)]

#print axioms ordered_gap_scalar
