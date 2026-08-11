/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/SQ4CorrelatedMoment.lean

Exact power accounting for two correlated transforms of the nonzero SQ4
family.  This file asserts neither transform nor an analytic estimate.  The
identities and the precise method classes are documented in
docs/audit/sq4_correlated_moment.md.
-/
import Mathlib

noncomputable section

namespace RH.Zeta85.SQ4CorrelatedMoment

def shortMuExponent : ℝ := 43 / 200
def smoothExponent : ℝ := 2 / 5
def productExponent : ℝ := 83 / 100
def muPairExponent : ℝ := 43 / 100
def numeratorExponent : ℝ := 33 / 50
def dualExponent : ℝ := 43 / 100
def physicalXExponent : ℝ := -(23 / 100)
def completionPrefactorExponent : ℝ := -(43 / 100)
def sq4HBTargetExponent : ℝ := 149 / 100
def fixedBudgetExponent : ℝ := 83 / 50
def integratedBudgetExponent : ℝ := 143 / 100

theorem source_scales_exact :
    2 * shortMuExponent + smoothExponent = productExponent ∧
      2 * shortMuExponent = muPairExponent ∧
      productExponent - smoothExponent = dualExponent ∧
      smoothExponent - productExponent = completionPrefactorExponent := by
  norm_num [shortMuExponent, smoothExponent, productExponent,
    muPairExponent, dualExponent, completionPrefactorExponent]

/-! ## Exact generalized-Gauss-product character-moment bookkeeping -/

/-- Number of modulus-character pairs in an all-modulus family. -/
def characterFamilyExponent : ℝ := 2 * productExponent

/-- Optimistic `L²` exponent for the two short Möbius character polynomials. -/
def characterVPairNormExponent : ℝ :=
  (characterFamilyExponent + muPairExponent) / 2

def characterKRLengthExponent : ℝ := dualExponent + numeratorExponent

/-- Optimistic `L²` exponent for the product of the dual and numerator
character polynomials under one coefficient-blind large sieve. -/
def characterKRNormExponent : ℝ :=
  (max characterFamilyExponent characterKRLengthExponent +
    characterKRLengthExponent) / 2

def characterCauchyFixedExponent : ℝ :=
  completionPrefactorExponent + characterVPairNormExponent +
    characterKRNormExponent

theorem character_norms_exact :
    characterFamilyExponent = 83 / 50 ∧
      characterKRLengthExponent = 109 / 100 ∧
      characterVPairNormExponent = 209 / 200 ∧
      characterKRNormExponent = 11 / 8 := by
  norm_num [characterFamilyExponent, characterKRLengthExponent,
    characterVPairNormExponent, characterKRNormExponent,
    productExponent, muPairExponent, dualExponent, numeratorExponent,
    max_eq_left]

theorem character_cauchy_output_exact :
    characterCauchyFixedExponent = 199 / 100 ∧
      characterCauchyFixedExponent - fixedBudgetExponent = 33 / 100 ∧
      characterCauchyFixedExponent - sq4HBTargetExponent = 1 / 2 := by
  norm_num [characterCauchyFixedExponent, completionPrefactorExponent,
    characterVPairNormExponent, characterKRNormExponent,
    characterFamilyExponent, characterKRLengthExponent, productExponent,
    muPairExponent, dualExponent, numeratorExponent, fixedBudgetExponent,
    sq4HBTargetExponent, max_eq_left]

theorem character_cauchy_integrated_exact :
    characterCauchyFixedExponent + physicalXExponent = 44 / 25 ∧
      characterCauchyFixedExponent + physicalXExponent -
        integratedBudgetExponent = 33 / 100 := by
  norm_num [characterCauchyFixedExponent, completionPrefactorExponent,
    characterVPairNormExponent, characterKRNormExponent,
    characterFamilyExponent, characterKRLengthExponent, productExponent,
    muPairExponent, dualExponent, numeratorExponent, physicalXExponent,
    integratedBudgetExponent, max_eq_left]

/-! ## Fixed-(p,v) square-root-only bookkeeping -/

/-- Completion, triangle in p and v, ideal square root in the k,r pair, and
Weil square root for the complete sum.  This is a prescribed method-class
output, not an analytic lower bound. -/
def fixedPVSquareRootExponent : ℝ :=
  completionPrefactorExponent + productExponent + muPairExponent +
    (dualExponent + numeratorExponent) / 2 + productExponent / 2

theorem fixed_pv_square_root_output_exact :
    fixedPVSquareRootExponent = 179 / 100 ∧
      fixedPVSquareRootExponent - fixedBudgetExponent = 13 / 100 ∧
      fixedPVSquareRootExponent - sq4HBTargetExponent = 3 / 10 ∧
      fixedPVSquareRootExponent + physicalXExponent = 39 / 25 := by
  norm_num [fixedPVSquareRootExponent, completionPrefactorExponent,
    productExponent, muPairExponent, dualExponent, numeratorExponent,
    fixedBudgetExponent, sq4HBTargetExponent, physicalXExponent]

/-! ## Blomer--Pascadi Theorem 5.5 on a fixed-(p,v) block -/

/-- First summand in the exponent of the theorem's `H(K,R,P)` factor. -/
def blomerPascadiH1Exponent : ℝ :=
  dualExponent / 8 +
    (max productExponent (dualExponent + numeratorExponent) +
      max productExponent (2 * numeratorExponent)) / 16 -
    productExponent / 4 +
    min (productExponent - dualExponent) (productExponent / 2) / 16

/-- Second summand in the exponent of the theorem's `H(K,R,P)` factor. -/
def blomerPascadiH2Exponent : ℝ :=
  max (2 * numeratorExponent - 2 * productExponent)
      (numeratorExponent / 2 + dualExponent +
        max productExponent (2 * numeratorExponent) -
        5 * productExponent / 2) / 16

def blomerPascadiH3Exponent : ℝ :=
  max dualExponent numeratorExponent / 3 - productExponent / 5

def blomerPascadiH4Exponent : ℝ :=
  max (dualExponent / 2 + numeratorExponent / 6)
      (dualExponent / 6 + numeratorExponent / 2) -
    7 * productExponent / 18

def blomerPascadiH5Exponent : ℝ :=
  max dualExponent numeratorExponent / 15 - productExponent / 15

def blomerPascadiHExponent : ℝ :=
  max blomerPascadiH1Exponent
    (max blomerPascadiH2Exponent
      (max blomerPascadiH3Exponent
        (max blomerPascadiH4Exponent blomerPascadiH5Exponent)))

/-- The fixed-modulus bilinear output: the two coefficient norms, the factor
`p`, and the largest summand of `H(K,R,p)`. -/
def blomerPascadiFixedPVInnerExponent : ℝ :=
  (dualExponent + numeratorExponent) / 2 + productExponent +
    blomerPascadiHExponent

/-- The prescribed outer-triangle chain, including completion and the
families of `p` and `v`. -/
def blomerPascadiFixedPVOuterExponent : ℝ :=
  completionPrefactorExponent + productExponent + muPairExponent +
    blomerPascadiFixedPVInnerExponent

theorem blomer_pascadi_fixed_pv_terms_exact :
    blomerPascadiH1Exponent = 7 / 320 ∧
      blomerPascadiH2Exponent = 1 / 3200 ∧
      blomerPascadiH3Exponent = 27 / 500 ∧
      blomerPascadiH4Exponent = 71 / 900 ∧
      blomerPascadiH5Exponent = -(17 / 1500) ∧
      blomerPascadiHExponent = 71 / 900 := by
  norm_num [blomerPascadiH1Exponent, blomerPascadiH2Exponent,
    blomerPascadiH3Exponent, blomerPascadiH4Exponent,
    blomerPascadiH5Exponent, blomerPascadiHExponent, productExponent,
    dualExponent, numeratorExponent, max_eq_left, max_eq_right, min_eq_left]

theorem blomer_pascadi_fixed_pv_output_exact :
    blomerPascadiFixedPVInnerExponent = 2617 / 1800 ∧
      blomerPascadiFixedPVOuterExponent = 4111 / 1800 ∧
      blomerPascadiFixedPVOuterExponent - fixedBudgetExponent = 1123 / 1800 ∧
      blomerPascadiFixedPVOuterExponent - sq4HBTargetExponent = 1429 / 1800 ∧
      blomerPascadiFixedPVOuterExponent + physicalXExponent = 3697 / 1800 := by
  norm_num [blomerPascadiFixedPVInnerExponent,
    blomerPascadiFixedPVOuterExponent, blomerPascadiHExponent,
    blomerPascadiH1Exponent, blomerPascadiH2Exponent,
    blomerPascadiH3Exponent, blomerPascadiH4Exponent,
    blomerPascadiH5Exponent, completionPrefactorExponent, productExponent,
    muPairExponent, dualExponent, numeratorExponent, fixedBudgetExponent,
    sq4HBTargetExponent, physicalXExponent, max_eq_left, max_eq_right,
    min_eq_left]

/-! ## Kerr--Shparlinski--Wu--Xi favourable Type-I bookkeeping -/

def sourceFrequencyExponent : ℝ := numeratorExponent - muPairExponent

def kswxDeltaATerm1 : ℝ :=
  -productExponent / 4 - muPairExponent + productExponent / 2
def kswxDeltaATerm2 : ℝ :=
  productExponent / 2 - muPairExponent - productExponent / 2
def kswxDeltaATerm3 : ℝ := -muPairExponent / 2
def kswxDeltaAExponent : ℝ :=
  max kswxDeltaATerm1 (max kswxDeltaATerm2 kswxDeltaATerm3)

def kswxDeltaBTerm1 : ℝ :=
  -productExponent / 2 +
    max (-3 * muPairExponent / 4 + productExponent / 2) 0
def kswxDeltaBTerm2 : ℝ := -muPairExponent / 2
def kswxDeltaBExponent : ℝ := max kswxDeltaBTerm1 kswxDeltaBTerm2

def kswxDeltaCTerm1 : ℝ :=
  -productExponent / 2 +
    max (-muPairExponent + productExponent / 2) (productExponent / 4)
def kswxDeltaCTerm2 : ℝ := -muPairExponent / 2
def kswxDeltaCExponent : ℝ := max kswxDeltaCTerm1 kswxDeltaCTerm2

def kswxBestDeltaExponent : ℝ :=
  min kswxDeltaAExponent (min kswxDeltaBExponent kswxDeltaCExponent)

/-- The favourable fixed-`(p,ell)` Type-I output: the granted collapsed
coefficient norm, full residue interval, `h` interval, modulus, and the best
of the three displayed `Delta_1` choices. -/
def kswxPerPFrequencyExponent : ℝ :=
  muPairExponent + productExponent / 2 + muPairExponent +
    productExponent / 2 + kswxBestDeltaExponent

def kswxTypeIFixedExponent : ℝ :=
  completionPrefactorExponent + productExponent + sourceFrequencyExponent +
    kswxPerPFrequencyExponent

/-- The already-audited Weil/triangle output after gaining the exact
`T⁻¹` from replacing the reciprocity phase by `1`. -/
def kswxReciprocityErrorExponent : ℝ := 467 / 200 - 1

/-- A concrete admissible split of the positive Poisson-truncation and
aggregate analytic losses in the reciprocity-error estimate. -/
def kswxReciprocityEtaAllocation : ℝ := 1 / 20
def kswxReciprocityEpsilonAllocation : ℝ := 1 / 20
def kswxReciprocityErrorAllocatedExponent : ℝ :=
  kswxReciprocityErrorExponent + kswxReciprocityEtaAllocation +
    kswxReciprocityEpsilonAllocation

theorem kswx_type_i_delta_terms_exact :
    sourceFrequencyExponent = 23 / 100 ∧
      kswxDeltaATerm1 = -(89 / 400) ∧
      kswxDeltaATerm2 = -(43 / 100) ∧
      kswxDeltaATerm3 = -(43 / 200) ∧
      kswxDeltaAExponent = -(43 / 200) ∧
      kswxDeltaBTerm1 = -(129 / 400) ∧
      kswxDeltaBTerm2 = -(43 / 200) ∧
      kswxDeltaBExponent = -(43 / 200) ∧
      kswxDeltaCTerm1 = -(83 / 400) ∧
      kswxDeltaCTerm2 = -(43 / 200) ∧
      kswxDeltaCExponent = -(83 / 400) ∧
      kswxBestDeltaExponent = -(43 / 200) := by
  norm_num [sourceFrequencyExponent, kswxDeltaATerm1, kswxDeltaATerm2,
    kswxDeltaATerm3, kswxDeltaAExponent, kswxDeltaBTerm1,
    kswxDeltaBTerm2, kswxDeltaBExponent, kswxDeltaCTerm1,
    kswxDeltaCTerm2, kswxDeltaCExponent, kswxBestDeltaExponent,
    productExponent, muPairExponent, numeratorExponent, max_eq_left,
    max_eq_right, min_eq_left, min_eq_right]

theorem kswx_type_i_output_exact :
    kswxPerPFrequencyExponent = 59 / 40 ∧
      kswxTypeIFixedExponent = 421 / 200 ∧
      kswxTypeIFixedExponent - fixedBudgetExponent = 89 / 200 ∧
      kswxTypeIFixedExponent - sq4HBTargetExponent = 123 / 200 ∧
      kswxTypeIFixedExponent + physicalXExponent = 15 / 8 ∧
      kswxReciprocityErrorExponent = 267 / 200 ∧
      kswxReciprocityEtaAllocation = 1 / 20 ∧
      kswxReciprocityEpsilonAllocation = 1 / 20 ∧
      kswxReciprocityErrorAllocatedExponent = 287 / 200 ∧
      sq4HBTargetExponent - kswxReciprocityErrorAllocatedExponent =
        11 / 200 := by
  norm_num [kswxPerPFrequencyExponent, kswxTypeIFixedExponent,
    kswxReciprocityErrorExponent, kswxReciprocityEtaAllocation,
    kswxReciprocityEpsilonAllocation,
    kswxReciprocityErrorAllocatedExponent, kswxBestDeltaExponent,
    kswxDeltaAExponent, kswxDeltaBExponent, kswxDeltaCExponent,
    kswxDeltaATerm1, kswxDeltaATerm2, kswxDeltaATerm3,
    kswxDeltaBTerm1, kswxDeltaBTerm2, kswxDeltaCTerm1,
    kswxDeltaCTerm2, sourceFrequencyExponent, completionPrefactorExponent,
    productExponent, muPairExponent, numeratorExponent, fixedBudgetExponent,
    sq4HBTargetExponent, physicalXExponent, max_eq_left, max_eq_right,
    min_eq_left, min_eq_right]

/-! ## Squarefree-v Ramanujan lift plus Pascadi Corollary 5.11 -/

def liftedLevelExponent : ℝ := 2 * muPairExponent
def liftedSecondIndexExponent : ℝ := muPairExponent + numeratorExponent
def pascadiRootPrefactorExponent : ℝ :=
  (liftedLevelExponent + dualExponent) / 2
def pascadiCoefficientNormExponent : ℝ :=
  (liftedLevelExponent + numeratorExponent) / 2

def pascadiAExponent : ℝ := liftedLevelExponent + smoothExponent
def pascadiBExponent : ℝ :=
  (dualExponent + liftedSecondIndexExponent) / 2
def pascadiCExponent : ℝ :=
  (liftedLevelExponent + dualExponent) / 2 + smoothExponent
def pascadiDExponent : ℝ :=
  (liftedLevelExponent + liftedSecondIndexExponent) / 2 + smoothExponent

/-- The rational factor on the last line of Pascadi's equation (5.32), at
the lifted source scales. -/
def pascadiGeometryExponent : ℝ :=
  max pascadiAExponent (max pascadiBExponent pascadiCExponent) +
    max pascadiAExponent (max pascadiBExponent pascadiDExponent) -
    max pascadiAExponent pascadiBExponent

def pascadiBeforeCompletionExponent : ℝ :=
  pascadiRootPrefactorExponent + pascadiCoefficientNormExponent +
    pascadiGeometryExponent

def pascadiLiftedFixedExponent : ℝ :=
  completionPrefactorExponent + pascadiBeforeCompletionExponent

/-- Extra power from applying the stated fixed-phase Corollary 5.11 separately
to every additive component and recombining by triangle. -/
def literalCor511RecombinationExponent : ℝ := muPairExponent / 2

def literalCor511BeforeCompletionExponent : ℝ :=
  pascadiBeforeCompletionExponent + literalCor511RecombinationExponent

def literalCor511FixedExponent : ℝ :=
  completionPrefactorExponent + literalCor511BeforeCompletionExponent

theorem pascadi_parameters_exact :
    liftedLevelExponent = 43 / 50 ∧
      liftedSecondIndexExponent = 109 / 100 ∧
      pascadiRootPrefactorExponent = 129 / 200 ∧
      pascadiCoefficientNormExponent = 19 / 25 ∧
      pascadiAExponent = 63 / 50 ∧
      pascadiBExponent = 19 / 25 ∧
      pascadiCExponent = 209 / 200 ∧
      pascadiDExponent = 11 / 8 := by
  norm_num [liftedLevelExponent, liftedSecondIndexExponent,
    pascadiRootPrefactorExponent, pascadiCoefficientNormExponent,
    pascadiAExponent, pascadiBExponent, pascadiCExponent,
    pascadiDExponent, muPairExponent, numeratorExponent, dualExponent,
    smoothExponent]

theorem pascadi_geometry_exact :
    pascadiGeometryExponent = 11 / 8 := by
  norm_num [pascadiGeometryExponent, pascadiAExponent, pascadiBExponent,
    pascadiCExponent, pascadiDExponent, liftedLevelExponent,
    liftedSecondIndexExponent, muPairExponent, numeratorExponent,
    dualExponent, smoothExponent, max_eq_left, max_eq_right]

theorem pascadi_lifted_output_exact :
    pascadiBeforeCompletionExponent = 139 / 50 ∧
      pascadiLiftedFixedExponent = 47 / 20 ∧
      pascadiLiftedFixedExponent - fixedBudgetExponent = 69 / 100 ∧
      pascadiLiftedFixedExponent - sq4HBTargetExponent = 43 / 50 := by
  norm_num [pascadiBeforeCompletionExponent, pascadiLiftedFixedExponent,
    completionPrefactorExponent, pascadiRootPrefactorExponent,
    pascadiCoefficientNormExponent, pascadiGeometryExponent,
    pascadiAExponent, pascadiBExponent, pascadiCExponent,
    pascadiDExponent, liftedLevelExponent, liftedSecondIndexExponent,
    muPairExponent, numeratorExponent, dualExponent, smoothExponent,
    fixedBudgetExponent, sq4HBTargetExponent, max_eq_left, max_eq_right]

theorem pascadi_lifted_integrated_exact :
    pascadiLiftedFixedExponent + physicalXExponent = 53 / 25 ∧
      pascadiLiftedFixedExponent + physicalXExponent -
        integratedBudgetExponent = 69 / 100 := by
  norm_num [pascadiLiftedFixedExponent, pascadiBeforeCompletionExponent,
    completionPrefactorExponent, pascadiRootPrefactorExponent,
    pascadiCoefficientNormExponent, pascadiGeometryExponent,
    pascadiAExponent, pascadiBExponent, pascadiCExponent,
    pascadiDExponent, liftedLevelExponent, liftedSecondIndexExponent,
    muPairExponent, numeratorExponent, dualExponent, smoothExponent,
    physicalXExponent, integratedBudgetExponent, max_eq_left, max_eq_right]

/-! ## Literal fixed-phase Corollary 5.11 recombination -/

theorem literal_cor511_output_exact :
    literalCor511RecombinationExponent = 43 / 200 ∧
      literalCor511BeforeCompletionExponent = 599 / 200 ∧
      literalCor511FixedExponent = 513 / 200 ∧
      literalCor511FixedExponent - fixedBudgetExponent = 181 / 200 ∧
      literalCor511FixedExponent - sq4HBTargetExponent = 43 / 40 ∧
      literalCor511FixedExponent + physicalXExponent = 467 / 200 := by
  norm_num [literalCor511RecombinationExponent,
    literalCor511BeforeCompletionExponent, literalCor511FixedExponent,
    pascadiBeforeCompletionExponent, completionPrefactorExponent,
    pascadiRootPrefactorExponent, pascadiCoefficientNormExponent,
    pascadiGeometryExponent, pascadiAExponent, pascadiBExponent,
    pascadiCExponent, pascadiDExponent, liftedLevelExponent,
    liftedSecondIndexExponent, muPairExponent, numeratorExponent,
    dualExponent, smoothExponent, fixedBudgetExponent, sq4HBTargetExponent,
    physicalXExponent, max_eq_left, max_eq_right]

/-! ## Explicit fixed logarithmic inventory -/

def optimisticNormalizedAuxiliaryLogExponent : ℝ := 0
def rawLongSlotLogExponent : ℝ := 2
def literalCor511DualDyadicLogExponent : ℝ := 1
def literalCor511RawLogExponent : ℝ :=
  rawLongSlotLogExponent + literalCor511DualDyadicLogExponent
def grantedGeneralBDivisorLogExponent : ℝ := 1
def grantedGeneralBNormalizedLogExponent : ℝ :=
  literalCor511DualDyadicLogExponent + grantedGeneralBDivisorLogExponent
def grantedGeneralBRawLogExponent : ℝ :=
  rawLongSlotLogExponent + grantedGeneralBNormalizedLogExponent

theorem correlated_route_log_exponents_exact :
    optimisticNormalizedAuxiliaryLogExponent = 0 ∧
      rawLongSlotLogExponent = 2 ∧
      literalCor511DualDyadicLogExponent = 1 ∧
      literalCor511RawLogExponent = 3 ∧
      grantedGeneralBDivisorLogExponent = 1 ∧
      grantedGeneralBNormalizedLogExponent = 2 ∧
      grantedGeneralBRawLogExponent = 4 := by
  norm_num [optimisticNormalizedAuxiliaryLogExponent,
    rawLongSlotLogExponent, literalCor511DualDyadicLogExponent,
    literalCor511RawLogExponent, grantedGeneralBDivisorLogExponent,
    grantedGeneralBNormalizedLogExponent, grantedGeneralBRawLogExponent]

end RH.Zeta85.SQ4CorrelatedMoment

end
