/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/SQ4SimultaneousRoutes.lean

Exact power accounting for six concrete method classes around the surviving
four-Moebius-slot estimate.  This file asserts no analytic estimate.  Each
quantity below is the output of the explicitly prescribed upper-bound chain
in docs/audit/sq4_simultaneous_routes.md.
-/
import Mathlib

noncomputable section

namespace RH.Zeta85.SQ4SimultaneousRoutes

/-- Exponent of either full product side. -/
def productExponent : ℝ := 83 / 100

/-- Exponent of the collapsed numerator `r = |ell| h`. -/
def numeratorExponent : ℝ := 33 / 50

/-- Exponent of one smooth slot. -/
def smoothExponent : ℝ := 2 / 5

/-- Exponent of either pair of retained Moebius slots. -/
def muPairExponent : ℝ := 43 / 100

def physicalXExponent : ℝ := -(23 / 100)
def fixedXTargetExponent : ℝ := 83 / 50
def integratedTargetExponent : ℝ := 143 / 100

theorem source_scales_exact :
    muPairExponent + smoothExponent = productExponent ∧
      fixedXTargetExponent + physicalXExponent = integratedTargetExponent := by
  norm_num [muPairExponent, smoothExponent, productExponent,
    fixedXTargetExponent, physicalXExponent, integratedTargetExponent]

/-! ## Multiplicative Fourier plus one all-modulus large sieve -/

/-- Power of the square root of the classical conductor count `Q^2 + P`.
Here `P=Q`, so `Q^2` dominates. -/
def characterConductorFactorExponent : ℝ := productExponent

/-- Output after the two ideal coefficient `L²` norms, the conductor factor,
and triangle summation over the numerator. -/
def characterLargeSieveFixedExponent : ℝ :=
  productExponent / 2 + productExponent / 2 +
    characterConductorFactorExponent + numeratorExponent

theorem character_large_sieve_output_exact :
    (max (2 * productExponent) productExponent) / 2 =
        characterConductorFactorExponent ∧
      characterLargeSieveFixedExponent = 58 / 25 ∧
      characterLargeSieveFixedExponent - fixedXTargetExponent = 33 / 50 := by
  norm_num [productExponent, characterConductorFactorExponent,
    characterLargeSieveFixedExponent, numeratorExponent,
    fixedXTargetExponent, max_eq_left]

theorem character_large_sieve_integrated_excess_exact :
    characterLargeSieveFixedExponent + physicalXExponent = 209 / 100 ∧
      characterLargeSieveFixedExponent + physicalXExponent -
        integratedTargetExponent = 33 / 50 := by
  norm_num [characterLargeSieveFixedExponent,
    characterConductorFactorExponent, productExponent, numeratorExponent,
    physicalXExponent, integratedTargetExponent]

/-! ## Coefficient-uniform two-sided norm-only class -/

/-- A single column of the unnormalised phase matrix has this norm exponent.
It is therefore a lower bound for any coefficient-uniform `L²` operator norm. -/
def singleColumnOperatorExponent : ℝ := productExponent / 2

def normOnlyFixedExponent : ℝ :=
  productExponent / 2 + productExponent / 2 +
    singleColumnOperatorExponent + numeratorExponent

theorem norm_only_output_exact :
    singleColumnOperatorExponent = 83 / 200 ∧
      normOnlyFixedExponent = 381 / 200 ∧
      normOnlyFixedExponent - fixedXTargetExponent = 49 / 200 := by
  norm_num [singleColumnOperatorExponent, normOnlyFixedExponent,
    productExponent, numeratorExponent, fixedXTargetExponent]

theorem norm_only_integrated_excess_exact :
    normOnlyFixedExponent + physicalXExponent = 67 / 40 ∧
      normOnlyFixedExponent + physicalXExponent -
        integratedTargetExponent = 49 / 200 := by
  norm_num [normOnlyFixedExponent, singleColumnOperatorExponent,
    productExponent, numeratorExponent, physicalXExponent,
    integratedTargetExponent]

/-! ## One additive large sieve in the numerator -/

/-- Power of `sqrt(R + Q^2)` for reciprocal Farey points of denominator
scale `Q`.  At the source scales `Q^2` dominates `R`. -/
def additiveFareyFactorExponent : ℝ := productExponent

def additiveLargeSieveFixedExponent : ℝ :=
  productExponent / 2 + productExponent / 2 +
    numeratorExponent / 2 + additiveFareyFactorExponent

theorem additive_large_sieve_output_exact :
    (max numeratorExponent (2 * productExponent)) / 2 =
        additiveFareyFactorExponent ∧
      additiveLargeSieveFixedExponent = 199 / 100 ∧
      additiveLargeSieveFixedExponent - fixedXTargetExponent = 33 / 100 := by
  norm_num [numeratorExponent, productExponent, additiveFareyFactorExponent,
    additiveLargeSieveFixedExponent, fixedXTargetExponent, max_eq_right]

theorem additive_large_sieve_integrated_excess_exact :
    additiveLargeSieveFixedExponent + physicalXExponent = 44 / 25 ∧
      additiveLargeSieveFixedExponent + physicalXExponent -
        integratedTargetExponent = 33 / 100 := by
  norm_num [additiveLargeSieveFixedExponent, additiveFareyFactorExponent,
    productExponent, numeratorExponent, physicalXExponent,
    integratedTargetExponent]

/-! ## Reciprocity and one smooth Poisson completion -/

def dualFrequencyExponent : ℝ := productExponent - smoothExponent
def completionPrefactorExponent : ℝ := smoothExponent - productExponent

/-- The normalized long-slot argument, the reciprocity-profile parameter,
and the dual-to-modulus ratio used in the rapid-decay truncation. -/
theorem reciprocal_profile_scales_exact :
    muPairExponent + smoothExponent + physicalXExponent - 3 / 5 = 0 ∧
      numeratorExponent - productExponent - muPairExponent - smoothExponent = -1 ∧
      dualFrequencyExponent - productExponent = -(2 / 5) := by
  norm_num [muPairExponent, smoothExponent, physicalXExponent,
    numeratorExponent, productExponent, dualFrequencyExponent]

/-- Power inventory of the Poisson zero mode after the Ramanujan sum is
averaged at divisor-bound cost.  The analytic divisor estimate is not asserted
in this file. -/
def poissonZeroModeFixedExponent : ℝ :=
  completionPrefactorExponent + productExponent +
    muPairExponent + numeratorExponent

/-- Power output of the direct nonzero-frequency fallback which uses Weil on
each complete sum and triangle inequality in every remaining variable. -/
def poissonWeilTriangleFixedExponent : ℝ :=
  completionPrefactorExponent + productExponent + muPairExponent +
    numeratorExponent + dualFrequencyExponent + productExponent / 2

theorem reciprocal_poisson_scales_exact :
    dualFrequencyExponent = 43 / 100 ∧
      completionPrefactorExponent = -(43 / 100) ∧
      poissonZeroModeFixedExponent = 149 / 100 ∧
      fixedXTargetExponent - poissonZeroModeFixedExponent = 17 / 100 := by
  norm_num [dualFrequencyExponent, completionPrefactorExponent,
    poissonZeroModeFixedExponent, productExponent, smoothExponent,
    muPairExponent, numeratorExponent, fixedXTargetExponent]

theorem poisson_zero_mode_integrated_exact :
    poissonZeroModeFixedExponent + physicalXExponent = 63 / 50 ∧
      integratedTargetExponent -
        (poissonZeroModeFixedExponent + physicalXExponent) = 17 / 100 := by
  norm_num [poissonZeroModeFixedExponent, completionPrefactorExponent,
    productExponent, smoothExponent, muPairExponent, numeratorExponent,
    physicalXExponent, integratedTargetExponent]

theorem poisson_weil_triangle_output_exact :
    poissonWeilTriangleFixedExponent = 467 / 200 ∧
      poissonWeilTriangleFixedExponent - fixedXTargetExponent = 27 / 40 := by
  norm_num [poissonWeilTriangleFixedExponent, completionPrefactorExponent,
    dualFrequencyExponent, productExponent, smoothExponent, muPairExponent,
    numeratorExponent, fixedXTargetExponent]

theorem poisson_weil_triangle_integrated_excess_exact :
    poissonWeilTriangleFixedExponent + physicalXExponent = 421 / 200 ∧
      poissonWeilTriangleFixedExponent + physicalXExponent -
        integratedTargetExponent = 27 / 40 := by
  norm_num [poissonWeilTriangleFixedExponent, completionPrefactorExponent,
    dualFrequencyExponent, productExponent, smoothExponent, muPairExponent,
    numeratorExponent, physicalXExponent, integratedTargetExponent]

/-! ## Explicit logarithmic inventory -/

/-- Every auxiliary logarithmic loss in the optimistic method-class
calculations is explicitly granted exponent zero. -/
def normalizedAuxiliaryLogExponent : ℝ := 0

/-- Restoring the two unnormalised long Heath--Brown log slots contributes
exactly exponent two. -/
def rawLongSlotLogExponent : ℝ := 2

theorem route_log_exponents_exact :
    normalizedAuxiliaryLogExponent = 0 ∧ rawLongSlotLogExponent = 2 := by
  norm_num [normalizedAuxiliaryLogExponent, rawLongSlotLogExponent]

end RH.Zeta85.SQ4SimultaneousRoutes

end
