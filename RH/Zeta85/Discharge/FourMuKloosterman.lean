/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/FourMuKloosterman.lean

Exact exponent audit for the four-Moebius-slot route left open by
PreMajorantDI.  The candidate d=1 block retains

  u1,u2,v1,v2 : 43/200,   m,n : 2/5,   r=|ell|h : 33/50.

Thus each product side u1*u2*m or v1*v2*n has exponent 83/100.

This file proves arithmetic facts only.  In particular,
`oneSidedSquareRootTriangleExponent` is the output of the prescribed
architecture which freezes the modulus side and numerator, grants a
square-root-size bound on the other whole product side, and then sums the
frozen variables by triangle inequality.  It is not a lower bound for the
source sum and is not a universal limitation on other methods.

The simultaneous exponent 149/100 is likewise a target calculation, not an
analytic estimate: it is what square-root-size cancellation in both product
sides, followed by the trivial numerator count, would give.
-/
import Mathlib

noncomputable section

namespace RH.Zeta85.FourMuKloosterman

/-! ## The seven literal scales -/

/-- Exponent of each of `u1,u2,v1,v2`. -/
def muSlotExponent : ℝ := 43 / 200

/-- Exponent of each short smooth slot `m,n`. -/
def smoothSlotExponent : ℝ := 2 / 5

/-- Exponent of the collapsed numerator `r=|ell|h`. -/
def numeratorExponent : ℝ := 33 / 50

/-- Exponent of `|ell|`. -/
def frequencyExponent : ℝ := 23 / 100

/-- Exponent of the shift `h`. -/
def shiftExponent : ℝ := 43 / 100

/-- Exponent of either full product side, for example `u1*u2*m`. -/
def productSideExponent : ℝ := 2 * muSlotExponent + smoothSlotExponent

/-- Total number-of-tuples exponent before any cancellation. -/
def sevenVariableVolumeExponent : ℝ :=
  4 * muSlotExponent + 2 * smoothSlotExponent + numeratorExponent

/-- Physical length exponent of the source `x` integral. -/
def physicalXExponent : ℝ := -(23 / 100)

/-- Required fixed-`x` exponent. -/
def fixedXTargetExponent : ℝ := 83 / 50

/-- Required exponent after the physical `x` integration. -/
def integratedTargetExponent : ℝ := 143 / 100

/-- All seven scales and both target scales, by exact rational arithmetic. -/
theorem seven_scales_exact :
    2 * muSlotExponent = 43 / 100 ∧
      frequencyExponent + shiftExponent = numeratorExponent ∧
      productSideExponent = 83 / 100 ∧
      sevenVariableVolumeExponent = 58 / 25 ∧
      fixedXTargetExponent + physicalXExponent = integratedTargetExponent := by
  norm_num [muSlotExponent, smoothSlotExponent, numeratorExponent,
    frequencyExponent, shiftExponent, productSideExponent,
    sevenVariableVolumeExponent, fixedXTargetExponent, physicalXExponent,
    integratedTargetExponent]

/-- Relative to the actual modulus scale `q=T^(83/100)`, one individual
Moebius interval has exponent `43/166`, strictly below the square-root
threshold. -/
theorem one_mu_relative_to_modulus :
    muSlotExponent / productSideExponent = 43 / 166 ∧
      muSlotExponent / productSideExponent < 1 / 2 := by
  norm_num [muSlotExponent, productSideExponent, smoothSlotExponent]

/-- In the asymptotic dyadic block the source modulus `v1*v2*n` has a
nontrivial displayed factorization, so a theorem whose hypothesis is that
this literal modulus is prime cannot be applied directly. -/
theorem source_modulus_not_prime
    {v1 v2 n : ℕ} (hv1 : 2 ≤ v1) (hv2n : 2 ≤ v2 * n) :
    ¬ Nat.Prime (v1 * v2 * n) := by
  rw [mul_assoc]
  exact Nat.not_prime_mul (by omega) (by omega)

/-! ## Prescribed one-sided fixed-modulus architecture -/

/-- Output exponent after granting square-root size on one whole product
side and triangle-summing the other product side and the numerator. -/
def oneSidedSquareRootTriangleExponent : ℝ :=
  productSideExponent / 2 + productSideExponent + numeratorExponent

/-- Its output after the source physical `x` integration. -/
def oneSidedIntegratedExponent : ℝ :=
  oneSidedSquareRootTriangleExponent + physicalXExponent

/-- The prescribed one-sided chain gives `381/200` at fixed `x` and
`67/40` after integration.  These are outputs of that upper-bound chain,
not lower bounds for the signed block. -/
theorem oneSided_squareRoot_output_exact :
    oneSidedSquareRootTriangleExponent = 381 / 200 ∧
      oneSidedIntegratedExponent = 67 / 40 := by
  norm_num [oneSidedSquareRootTriangleExponent, oneSidedIntegratedExponent,
    productSideExponent, muSlotExponent, smoothSlotExponent,
    numeratorExponent, physicalXExponent]

/-- The prescribed one-sided output misses the fixed-`x` target by
exactly `49/200`. -/
theorem oneSided_fixedX_excess_exact :
    oneSidedSquareRootTriangleExponent - fixedXTargetExponent = 49 / 200 := by
  norm_num [oneSidedSquareRootTriangleExponent, productSideExponent,
    muSlotExponent, smoothSlotExponent, numeratorExponent,
    fixedXTargetExponent]

/-- Physical integration subtracts the same exponent from the chain and the
target, so the miss remains exactly `49/200`. -/
theorem oneSided_integrated_excess_exact :
    oneSidedIntegratedExponent - integratedTargetExponent = 49 / 200 := by
  norm_num [oneSidedIntegratedExponent, oneSidedSquareRootTriangleExponent,
    productSideExponent, muSlotExponent, smoothSlotExponent,
    numeratorExponent, physicalXExponent, integratedTargetExponent]

/-- Adding a nonnegative theorem loss cannot make the prescribed one-sided
upper-bound chain trace-grade.  This is still only a statement about that
chain's exponent. -/
theorem oneSided_not_fixedX_grade_with_slack
    {slack : ℝ} (hslack : 0 ≤ slack) :
    fixedXTargetExponent < oneSidedSquareRootTriangleExponent + slack := by
  have h := oneSided_fixedX_excess_exact
  linarith

/-! ## Exact simultaneous candidate -/

/-- Target exponent obtained by granting square-root size simultaneously in
both product sides and then counting the numerator trivially.  No analytic
theorem with this conclusion is asserted here. -/
def simultaneousBothSidesCandidateExponent : ℝ :=
  productSideExponent / 2 + productSideExponent / 2 + numeratorExponent

/-- The simultaneous candidate has exponent `149/100`, below the fixed-`x`
target by exactly `17/100`. -/
theorem simultaneous_candidate_exact :
    simultaneousBothSidesCandidateExponent = 149 / 100 ∧
      fixedXTargetExponent - simultaneousBothSidesCandidateExponent = 17 / 100 := by
  norm_num [simultaneousBothSidesCandidateExponent, productSideExponent,
    muSlotExponent, smoothSlotExponent, numeratorExponent,
    fixedXTargetExponent]

/-- Before allocating any analytic or logarithmic power loss, physical
integration changes the simultaneous candidate exponent to `63/50`, still
with its intrinsic `17/100` margin. -/
theorem simultaneous_candidate_integrated_exact :
    simultaneousBothSidesCandidateExponent + physicalXExponent = 63 / 50 ∧
      integratedTargetExponent - (63 / 50 : ℝ) = 17 / 100 := by
  norm_num [simultaneousBothSidesCandidateExponent, productSideExponent,
    muSlotExponent, smoothSlotExponent, numeratorExponent,
    physicalXExponent, integratedTargetExponent]

/-- The simultaneous candidate gains an additional `83/200` over the
one-sided chain.  Only `49/200` is needed, leaving the `17/100` margin. -/
theorem simultaneous_gain_decomposition_exact :
    oneSidedSquareRootTriangleExponent -
        simultaneousBothSidesCandidateExponent = 83 / 200 ∧
      (83 / 200 : ℝ) = 49 / 200 + 17 / 100 := by
  norm_num [oneSidedSquareRootTriangleExponent,
    simultaneousBothSidesCandidateExponent, productSideExponent,
    muSlotExponent, smoothSlotExponent, numeratorExponent]

/-- Any positive power loss strictly smaller than `17/100` remains below the
fixed-`x` target.  This theorem only records the exponent implication that a
future analytic estimate would use. -/
theorem simultaneous_candidate_with_power_slack
    {slack : ℝ} (hslack : slack < 17 / 100) :
    simultaneousBothSidesCandidateExponent + slack < fixedXTargetExponent := by
  have h := simultaneous_candidate_exact
  linarith

/-- A concrete strict allocation for the candidate calculation: reserve
`17/400` for the analytic `T^epsilon` and another `17/400` to dominate the
two explicit long logarithms.  The resulting raw exponent is `63/40`, with
`17/200` left before both the fixed-`x` and integrated targets.  This is
exponent bookkeeping only; it does not assert the candidate estimate or the
eventual logarithm inequality. -/
theorem simultaneous_concrete_loss_allocation_exact :
    simultaneousBothSidesCandidateExponent + 17 / 400 + 17 / 400 = 63 / 40 ∧
      fixedXTargetExponent - (63 / 40 : ℝ) = 17 / 200 ∧
      (63 / 40 : ℝ) + physicalXExponent = 269 / 200 ∧
      integratedTargetExponent - (269 / 200 : ℝ) = 17 / 200 := by
  norm_num [simultaneousBothSidesCandidateExponent, productSideExponent,
    muSlotExponent, smoothSlotExponent, numeratorExponent,
    fixedXTargetExponent, physicalXExponent, integratedTargetExponent]

/-- The two unnormalized long logarithmic slots contribute the explicit
logarithmic exponent two; dividing each by `log T` contributes zero. -/
def normalizedLongLogExponent : ℝ := 0

def rawLongLogExponent : ℝ := 2

theorem long_log_exponents_exact :
    normalizedLongLogExponent = 0 ∧ rawLongLogExponent = 2 := by
  norm_num [normalizedLongLogExponent, rawLongLogExponent]

end RH.Zeta85.FourMuKloosterman

end
