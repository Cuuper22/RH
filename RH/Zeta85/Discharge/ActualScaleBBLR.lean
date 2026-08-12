/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/ActualScaleBBLR.lean

Exact exponent audit for the symmetric actual-scale BBLR block left after the
fixed asymmetric literal grouping is removed.  On each side the exponents are

  outer = 43/100,  inner short = 2/5,  inner long = 3/5,

and the shift exponent is 43/100.  This module records two separate failures.

* The two terms in the published BBLR Proposition 3.1 error have exponents
  179/100 and 161/100, exceeding the trace exponent 143/100 by 9/25 and 9/50.
* In equation (14), after the canonical gcd allocation and at d=1, the
  progression-majorant lengths are P=Q=T^(83/100).  Consequently the
  P(Q+H) estimate has exponent 83/50, exceeding trace by 23/100.  Its PH term
  is harmless; the obstruction is exactly PQ.  The Fourier integral has
  physical exponent -23/100, but the source frequency cutoff has exponent
  23/100, so summing the nonzero frequencies cancels that apparent saving.

These are method-class statements about the displayed bounds.  They do not
assert a lower bound for the original signed remainder and therefore do not
rule out cancellation before the progression majorant is applied.
-/
import Mathlib

noncomputable section

namespace RH.Zeta85.ActualScaleBBLR

/-! ## Exact block geometry -/

/-- The endpoint shift and outer-coefficient exponent. -/
def eta : ℝ := 43 / 100

/-- The natural trace exponent `1 + eta`. -/
def traceExponent : ℝ := 1 + eta

/-- Exponent of each arbitrary outer BBLR coefficient variable. -/
def outerExponent : ℝ := 43 / 100

/-- Exponent of each shorter literal smooth variable. -/
def innerShortExponent : ℝ := 2 / 5

/-- Exponent of each longer literal smooth variable. -/
def innerLongExponent : ℝ := 3 / 5

/-- Exponent of the shift length `H`. -/
def shiftExponent : ℝ := 43 / 100

/-- Exponent of `ABMN`, with `M=M1*M2` and `N=N1*N2`. -/
def productExponent : ℝ :=
  2 * outerExponent + 2 * (innerShortExponent + innerLongExponent)

/-- The literal block is balanced, each side has exponent `143/100`, and the
Watt-range condition `H <= (AB)^(1/2+epsilon)` is at equality before the
nonnegative epsilon slack is added. -/
theorem block_geometry_exact :
    innerShortExponent ≤ innerLongExponent ∧
      outerExponent + innerShortExponent + innerLongExponent = traceExponent ∧
      productExponent = 143 / 50 ∧
      shiftExponent = (outerExponent + outerExponent) / 2 := by
  norm_num [innerShortExponent, innerLongExponent, outerExponent,
    traceExponent, eta, productExponent, shiftExponent]

/-! ## Published BBLR Proposition 3.1 error -/

/-- Exponent of `(ABMNH^2)^(1/4)` before the proposition's epsilon slack. -/
def outsideExponent : ℝ := (productExponent + 2 * shiftExponent) / 4

/-- Exponent of the `AB` contribution to the BBLR error. -/
def blackBoxABExponent : ℝ := outsideExponent + 2 * outerExponent

/-- Exponent of
`H^(1/4) * (A+B)^(1/2) * (ABMN)^(1/8)`.
Because `A=B=T^outerExponent`, the fixed factor two in `A+B` does not alter
the power of `T`, so `(A+B)^(1/2)` contributes `outerExponent/2`. -/
def wattParenthesisExponent : ℝ :=
  shiftExponent / 4 + outerExponent / 2 + productExponent / 8

/-- Exponent of the Watt/Kuznetsov contribution to the BBLR error. -/
def blackBoxWattExponent : ℝ := outsideExponent + wattParenthesisExponent

/-- Exact values of all pieces of the black-box error substitution. -/
theorem blackBox_exponents_exact :
    outsideExponent = 93 / 100 ∧
      wattParenthesisExponent = 17 / 25 ∧
      blackBoxABExponent = 179 / 100 ∧
      blackBoxWattExponent = 161 / 100 := by
  norm_num [outsideExponent, wattParenthesisExponent, blackBoxABExponent,
    blackBoxWattExponent, productExponent, shiftExponent, outerExponent,
    innerShortExponent, innerLongExponent]

/-- The corrected `AB` error exceeds the trace scale by exactly `9/25`. -/
theorem blackBoxAB_excess :
    blackBoxABExponent - traceExponent = 9 / 25 := by
  norm_num [blackBoxABExponent, outsideExponent, productExponent,
    shiftExponent, outerExponent, innerShortExponent, innerLongExponent,
    traceExponent, eta]

/-- The Watt error exceeds the trace scale by exactly `9/50`. -/
theorem blackBoxWatt_excess :
    blackBoxWattExponent - traceExponent = 9 / 50 := by
  norm_num [blackBoxWattExponent, wattParenthesisExponent, outsideExponent,
    productExponent, shiftExponent, outerExponent, innerShortExponent,
    innerLongExponent, traceExponent, eta]

/-- Even before the proposition's nonnegative epsilon loss, neither displayed
black-box error is trace-grade. -/
theorem blackBox_not_traceGrade :
    traceExponent < blackBoxABExponent ∧
      traceExponent < blackBoxWattExponent := by
  norm_num [blackBoxABExponent, blackBoxWattExponent, wattParenthesisExponent,
    outsideExponent, productExponent, shiftExponent, outerExponent,
    innerShortExponent, innerLongExponent, traceExponent, eta]

/-- Adding any nonnegative power slack cannot repair either black-box error. -/
theorem blackBox_not_traceGrade_with_slack {slack : ℝ} (hslack : 0 ≤ slack) :
    traceExponent < blackBoxABExponent + slack ∧
      traceExponent < blackBoxWattExponent + slack := by
  obtain ⟨hAB, hW⟩ := blackBox_not_traceGrade
  constructor <;> linarith

/-! ## Source Poisson/progression-majorant lengths at d=1 -/

/-- Equation (14)'s Fourier integral is supported on
`x` of scale `M2/(B*N1) = N2/(A*M1)` at `d=1`. -/
def fourierPhysicalExponent : ℝ :=
  innerLongExponent - outerExponent - innerShortExponent

/-- The source cutoff
`L = A*(M1*M2)/(M2*N2)` at `d=1`, with epsilon slack suppressed. -/
def frequencyCutoffExponent : ℝ :=
  outerExponent + innerShortExponent + innerLongExponent -
    innerLongExponent - innerLongExponent

/-- The low-frequency count and the physical size of each Fourier integral
cancel in power: `T^(23/100) * T^(-23/100) = T^0`. -/
theorem source_fourier_exponents_exact :
    fourierPhysicalExponent = -(23 / 100) ∧
      frequencyCutoffExponent = 23 / 100 ∧
      fourierPhysicalExponent + frequencyCutoffExponent = 0 := by
  norm_num [fourierPhysicalExponent, frequencyCutoffExponent,
    innerLongExponent, outerExponent, innerShortExponent]

/-- Equation (14), after gcd allocation at `d=1`, has `P` of length `A*M1`. -/
def poissonPExponent : ℝ := outerExponent + innerShortExponent

/-- The right-side progression modulus length `Q=B*N1` at `d=1`. -/
def poissonQExponent : ℝ := outerExponent + innerShortExponent

/-- Power exponent of the `P*Q` summand in `P(Q+H)`. -/
def progressionPQExponent : ℝ := poissonPExponent + poissonQExponent

/-- Power exponent of the `P*H` summand in `P(Q+H)`. -/
def progressionPHExponent : ℝ := poissonPExponent + shiftExponent

/-- The power exponent of a sum of two nonnegative power bounds is their
maximum. -/
def progressionMajorantExponent : ℝ :=
  max progressionPQExponent progressionPHExponent

/-- Exact `d=1` source lengths and the two summands of `P(Q+H)`. -/
theorem source_lengths_exact :
    poissonPExponent = 83 / 100 ∧
      poissonQExponent = 83 / 100 ∧
      progressionPQExponent = 83 / 50 ∧
      progressionPHExponent = 63 / 50 := by
  norm_num [poissonPExponent, poissonQExponent, progressionPQExponent,
    progressionPHExponent, outerExponent, innerShortExponent, shiftExponent]

/-- Since `Q` is longer than `H`, the source majorant is dominated by `PQ`. -/
theorem progression_majorant_is_PQ :
    progressionMajorantExponent = progressionPQExponent := by
  norm_num [progressionMajorantExponent, progressionPQExponent,
    progressionPHExponent, poissonPExponent, poissonQExponent,
    outerExponent, innerShortExponent, shiftExponent, max_eq_left]

/-- The `PQ` term exceeds trace by exactly `23/100`. -/
theorem progressionPQ_excess :
    progressionPQExponent - traceExponent = 23 / 100 := by
  norm_num [progressionPQExponent, poissonPExponent, poissonQExponent,
    outerExponent, innerShortExponent, traceExponent, eta]

/-- The `PH` term is below trace by exactly `17/100`. -/
theorem progressionPH_saving :
    traceExponent - progressionPHExponent = 17 / 100 := by
  norm_num [progressionPHExponent, poissonPExponent, outerExponent,
    innerShortExponent, shiftExponent, traceExponent, eta]

/-- Hence the literal `d=1` progression majorant misses trace by `23/100`,
already with logarithmic exponent zero. -/
theorem progression_majorant_not_traceGrade :
    progressionMajorantExponent = 83 / 50 ∧
      progressionMajorantExponent - traceExponent = 23 / 100 ∧
      traceExponent < progressionMajorantExponent := by
  rw [progression_majorant_is_PQ]
  norm_num [progressionPQExponent, poissonPExponent, poissonQExponent,
    outerExponent, innerShortExponent, traceExponent, eta]

/-- The preliminary zero-shift Taylor error `H^2` is not the obstruction. -/
theorem taylor_H_sq_saving :
    traceExponent - 2 * shiftExponent = 57 / 100 := by
  norm_num [traceExponent, eta, shiftExponent]

end RH.Zeta85.ActualScaleBBLR

end
