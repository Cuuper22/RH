/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/SQ4PublishedLiterature.lean

Exact rational power and fixed-log bookkeeping for the published-literature
audit of the surviving SQ4 family.  The file reuses the arithmetic constants
already proved by SQ4SimultaneousRoutes and SQ4CorrelatedMoment.  It asserts
neither a cited analytic theorem nor an applicability statement.
-/
import RH.Zeta85.Discharge.SQ4CorrelatedMoment
import RH.Zeta85.Discharge.SQ4SimultaneousRoutes

noncomputable section

namespace RH.Zeta85.SQ4PublishedLiterature

/-- The exact target for `M4 = (P / M) * Z_nz`, before restoring the
Poisson-completion prefactor. -/
def preCompletionTargetExponent : ℝ :=
  SQ4CorrelatedMoment.sq4HBTargetExponent -
    SQ4CorrelatedMoment.completionPrefactorExponent

/-- Convert a completed exponent back to the `M4` pre-completion
normalization used by the literature audit. -/
def preCompletionOf (completedExponent : ℝ) : ℝ :=
  completedExponent - SQ4CorrelatedMoment.completionPrefactorExponent

theorem precompletion_target_exact :
    preCompletionTargetExponent = 48 / 25 ∧
      preCompletionTargetExponent +
        SQ4CorrelatedMoment.completionPrefactorExponent = 149 / 100 := by
  norm_num [preCompletionTargetExponent,
    SQ4CorrelatedMoment.sq4HBTargetExponent,
    SQ4CorrelatedMoment.completionPrefactorExponent]

/-! ## Existing method classes in the common pre-completion normalization -/

def characterPreCompletionExponent : ℝ :=
  preCompletionOf SQ4CorrelatedMoment.characterCauchyFixedExponent

def fixedPVSquareRootPreCompletionExponent : ℝ :=
  preCompletionOf SQ4CorrelatedMoment.fixedPVSquareRootExponent

def directWeilTrianglePreCompletionExponent : ℝ :=
  preCompletionOf SQ4SimultaneousRoutes.poissonWeilTriangleFixedExponent

theorem existing_benchmark_precompletion_exact :
    characterPreCompletionExponent = 121 / 50 ∧
      characterPreCompletionExponent - preCompletionTargetExponent = 1 / 2 ∧
      fixedPVSquareRootPreCompletionExponent = 111 / 50 ∧
      fixedPVSquareRootPreCompletionExponent - preCompletionTargetExponent =
        3 / 10 ∧
      directWeilTrianglePreCompletionExponent = 553 / 200 ∧
      directWeilTrianglePreCompletionExponent - preCompletionTargetExponent =
        169 / 200 := by
  norm_num [characterPreCompletionExponent,
    fixedPVSquareRootPreCompletionExponent,
    directWeilTrianglePreCompletionExponent, preCompletionOf,
    preCompletionTargetExponent,
    SQ4CorrelatedMoment.characterCauchyFixedExponent,
    SQ4CorrelatedMoment.characterVPairNormExponent,
    SQ4CorrelatedMoment.characterKRNormExponent,
    SQ4CorrelatedMoment.characterFamilyExponent,
    SQ4CorrelatedMoment.characterKRLengthExponent,
    SQ4CorrelatedMoment.fixedPVSquareRootExponent,
    SQ4CorrelatedMoment.completionPrefactorExponent,
    SQ4CorrelatedMoment.productExponent,
    SQ4CorrelatedMoment.muPairExponent,
    SQ4CorrelatedMoment.dualExponent,
    SQ4CorrelatedMoment.numeratorExponent,
    SQ4CorrelatedMoment.sq4HBTargetExponent,
    SQ4SimultaneousRoutes.poissonWeilTriangleFixedExponent,
    SQ4SimultaneousRoutes.completionPrefactorExponent,
    SQ4SimultaneousRoutes.productExponent,
    SQ4SimultaneousRoutes.muPairExponent,
    SQ4SimultaneousRoutes.numeratorExponent,
    SQ4SimultaneousRoutes.dualFrequencyExponent,
    SQ4SimultaneousRoutes.smoothExponent, max_eq_left]

/-! ## Shparlinski 2019, Theorem 2.1: favourable restricted-class power -/

/-- Granted `L1` exponent for the collapsed `(k,v)` coefficient. -/
def shparlinski19AlphaL1Exponent : ℝ :=
  2 * SQ4CorrelatedMoment.muPairExponent

/-- Granted `L2` exponent for the same collapsed coefficient. -/
def shparlinski19AlphaL2Exponent : ℝ :=
  SQ4CorrelatedMoment.muPairExponent

/-- Exponent of `(||alpha||_1 ||alpha||_2)^(1/2)`. -/
def shparlinski19NormFactorExponent : ℝ :=
  (shparlinski19AlphaL1Exponent + shparlinski19AlphaL2Exponent) / 2

/-- Exponent of `N^(1/8) q` at `N = T^(43/100)` and
`q = T^(83/100)`. -/
def shparlinski19Kernel1Exponent : ℝ :=
  SQ4CorrelatedMoment.muPairExponent / 8 +
    SQ4CorrelatedMoment.productExponent

/-- Exponent of `N^(1/2) q^(3/4)` at the same scales. -/
def shparlinski19Kernel2Exponent : ℝ :=
  SQ4CorrelatedMoment.muPairExponent / 2 +
    3 * SQ4CorrelatedMoment.productExponent / 4

def shparlinski19KernelExponent : ℝ :=
  max shparlinski19Kernel1Exponent shparlinski19Kernel2Exponent

def shparlinski19LocalExponent : ℝ :=
  shparlinski19NormFactorExponent + shparlinski19KernelExponent

/-- The favourable Theorem 2.1 class after triangle summation in the
outer `p` and `ell` families. -/
def shparlinski19PreCompletionExponent : ℝ :=
  SQ4CorrelatedMoment.productExponent +
    SQ4CorrelatedMoment.sourceFrequencyExponent +
    shparlinski19LocalExponent

theorem shparlinski19_t21_terms_exact :
    shparlinski19AlphaL1Exponent = 43 / 50 ∧
      shparlinski19AlphaL2Exponent = 43 / 100 ∧
      shparlinski19NormFactorExponent = 129 / 200 ∧
      shparlinski19Kernel1Exponent = 707 / 800 ∧
      shparlinski19Kernel2Exponent = 67 / 80 ∧
      shparlinski19KernelExponent = 707 / 800 ∧
      shparlinski19LocalExponent = 1223 / 800 ∧
      shparlinski19PreCompletionExponent = 2071 / 800 ∧
      shparlinski19PreCompletionExponent - preCompletionTargetExponent =
        107 / 160 := by
  norm_num [shparlinski19AlphaL1Exponent,
    shparlinski19AlphaL2Exponent, shparlinski19NormFactorExponent,
    shparlinski19Kernel1Exponent, shparlinski19Kernel2Exponent,
    shparlinski19KernelExponent, shparlinski19LocalExponent,
    shparlinski19PreCompletionExponent, preCompletionTargetExponent,
    SQ4CorrelatedMoment.muPairExponent,
    SQ4CorrelatedMoment.productExponent,
    SQ4CorrelatedMoment.sourceFrequencyExponent,
    SQ4CorrelatedMoment.numeratorExponent,
    SQ4CorrelatedMoment.sq4HBTargetExponent,
    SQ4CorrelatedMoment.completionPrefactorExponent, max_eq_left]

/-! ## Shparlinski 2019, Theorem 2.2: good-modulus part only -/

def shparlinski19AlmostAllMoment : ℝ := 2

def shparlinski19AlmostAllNormExponent : ℝ :=
  shparlinski19AlphaL1Exponent *
      (1 - 1 / shparlinski19AlmostAllMoment) +
    shparlinski19AlphaL2Exponent / shparlinski19AlmostAllMoment

def shparlinski19AlmostAllKernel1Exponent : ℝ :=
  SQ4CorrelatedMoment.productExponent

def shparlinski19AlmostAllKernel2Exponent : ℝ :=
  SQ4CorrelatedMoment.muPairExponent / 2 +
    SQ4CorrelatedMoment.productExponent *
      (1 / 2 + 1 / (2 * shparlinski19AlmostAllMoment))

def shparlinski19AlmostAllKernelExponent : ℝ :=
  max shparlinski19AlmostAllKernel1Exponent
    shparlinski19AlmostAllKernel2Exponent

/-- Base power for the good-modulus portion.  The exceptional-modulus
source mass is outside this numerical definition. -/
def shparlinski19AlmostAllPreCompletionExponent : ℝ :=
  SQ4CorrelatedMoment.productExponent +
    SQ4CorrelatedMoment.sourceFrequencyExponent +
    shparlinski19AlmostAllNormExponent +
    shparlinski19AlmostAllKernelExponent

theorem shparlinski19_t22_good_part_exact :
    shparlinski19AlmostAllMoment = 2 ∧
      shparlinski19AlmostAllNormExponent = 129 / 200 ∧
      shparlinski19AlmostAllKernel1Exponent = 83 / 100 ∧
      shparlinski19AlmostAllKernel2Exponent = 67 / 80 ∧
      shparlinski19AlmostAllKernelExponent = 67 / 80 ∧
      shparlinski19AlmostAllPreCompletionExponent = 1017 / 400 ∧
      shparlinski19AlmostAllPreCompletionExponent -
        preCompletionTargetExponent = 249 / 400 := by
  norm_num [shparlinski19AlmostAllMoment,
    shparlinski19AlmostAllNormExponent,
    shparlinski19AlmostAllKernel1Exponent,
    shparlinski19AlmostAllKernel2Exponent,
    shparlinski19AlmostAllKernelExponent,
    shparlinski19AlmostAllPreCompletionExponent,
    shparlinski19AlphaL1Exponent, shparlinski19AlphaL2Exponent,
    preCompletionTargetExponent, SQ4CorrelatedMoment.muPairExponent,
    SQ4CorrelatedMoment.productExponent,
    SQ4CorrelatedMoment.sourceFrequencyExponent,
    SQ4CorrelatedMoment.numeratorExponent,
    SQ4CorrelatedMoment.sq4HBTargetExponent,
    SQ4CorrelatedMoment.completionPrefactorExponent, max_eq_right]

/-! ## Other audited classes in the common normalization -/

def blomerPascadiPreCompletionExponent : ℝ :=
  preCompletionOf SQ4CorrelatedMoment.blomerPascadiFixedPVOuterExponent

def kswxPreCompletionExponent : ℝ :=
  preCompletionOf SQ4CorrelatedMoment.kswxTypeIFixedExponent

theorem other_precompletion_outputs_exact :
    blomerPascadiPreCompletionExponent = 977 / 360 ∧
      blomerPascadiPreCompletionExponent - preCompletionTargetExponent =
        1429 / 1800 ∧
      kswxPreCompletionExponent = 507 / 200 ∧
      kswxPreCompletionExponent - preCompletionTargetExponent = 123 / 200 ∧
      SQ4CorrelatedMoment.pascadiBeforeCompletionExponent = 139 / 50 ∧
      SQ4CorrelatedMoment.pascadiBeforeCompletionExponent -
        preCompletionTargetExponent = 43 / 50 ∧
      SQ4CorrelatedMoment.literalCor511BeforeCompletionExponent = 599 / 200 ∧
      SQ4CorrelatedMoment.literalCor511BeforeCompletionExponent -
        preCompletionTargetExponent = 43 / 40 := by
  norm_num [blomerPascadiPreCompletionExponent,
    kswxPreCompletionExponent, preCompletionOf,
    preCompletionTargetExponent,
    SQ4CorrelatedMoment.blomerPascadiFixedPVOuterExponent,
    SQ4CorrelatedMoment.blomerPascadiFixedPVInnerExponent,
    SQ4CorrelatedMoment.blomerPascadiHExponent,
    SQ4CorrelatedMoment.blomerPascadiH1Exponent,
    SQ4CorrelatedMoment.blomerPascadiH2Exponent,
    SQ4CorrelatedMoment.blomerPascadiH3Exponent,
    SQ4CorrelatedMoment.blomerPascadiH4Exponent,
    SQ4CorrelatedMoment.blomerPascadiH5Exponent,
    SQ4CorrelatedMoment.kswxTypeIFixedExponent,
    SQ4CorrelatedMoment.kswxPerPFrequencyExponent,
    SQ4CorrelatedMoment.kswxBestDeltaExponent,
    SQ4CorrelatedMoment.kswxDeltaAExponent,
    SQ4CorrelatedMoment.kswxDeltaBExponent,
    SQ4CorrelatedMoment.kswxDeltaCExponent,
    SQ4CorrelatedMoment.kswxDeltaATerm1,
    SQ4CorrelatedMoment.kswxDeltaATerm2,
    SQ4CorrelatedMoment.kswxDeltaATerm3,
    SQ4CorrelatedMoment.kswxDeltaBTerm1,
    SQ4CorrelatedMoment.kswxDeltaBTerm2,
    SQ4CorrelatedMoment.kswxDeltaCTerm1,
    SQ4CorrelatedMoment.kswxDeltaCTerm2,
    SQ4CorrelatedMoment.pascadiBeforeCompletionExponent,
    SQ4CorrelatedMoment.literalCor511BeforeCompletionExponent,
    SQ4CorrelatedMoment.literalCor511RecombinationExponent,
    SQ4CorrelatedMoment.pascadiRootPrefactorExponent,
    SQ4CorrelatedMoment.pascadiCoefficientNormExponent,
    SQ4CorrelatedMoment.pascadiGeometryExponent,
    SQ4CorrelatedMoment.pascadiAExponent,
    SQ4CorrelatedMoment.pascadiBExponent,
    SQ4CorrelatedMoment.pascadiCExponent,
    SQ4CorrelatedMoment.pascadiDExponent,
    SQ4CorrelatedMoment.liftedLevelExponent,
    SQ4CorrelatedMoment.liftedSecondIndexExponent,
    SQ4CorrelatedMoment.completionPrefactorExponent,
    SQ4CorrelatedMoment.productExponent,
    SQ4CorrelatedMoment.muPairExponent,
    SQ4CorrelatedMoment.dualExponent,
    SQ4CorrelatedMoment.numeratorExponent,
    SQ4CorrelatedMoment.smoothExponent,
    SQ4CorrelatedMoment.sourceFrequencyExponent,
    SQ4CorrelatedMoment.sq4HBTargetExponent, max_eq_left, max_eq_right,
    min_eq_left, min_eq_right]

theorem audited_log_exponents_exact :
    SQ4CorrelatedMoment.optimisticNormalizedAuxiliaryLogExponent = 0 ∧
      SQ4CorrelatedMoment.rawLongSlotLogExponent = 2 ∧
      SQ4CorrelatedMoment.literalCor511DualDyadicLogExponent = 1 ∧
      SQ4CorrelatedMoment.literalCor511RawLogExponent = 3 ∧
      SQ4CorrelatedMoment.grantedGeneralBNormalizedLogExponent = 2 ∧
      SQ4CorrelatedMoment.grantedGeneralBRawLogExponent = 4 := by
  norm_num [SQ4CorrelatedMoment.optimisticNormalizedAuxiliaryLogExponent,
    SQ4CorrelatedMoment.rawLongSlotLogExponent,
    SQ4CorrelatedMoment.literalCor511DualDyadicLogExponent,
    SQ4CorrelatedMoment.literalCor511RawLogExponent,
    SQ4CorrelatedMoment.grantedGeneralBDivisorLogExponent,
    SQ4CorrelatedMoment.grantedGeneralBNormalizedLogExponent,
    SQ4CorrelatedMoment.grantedGeneralBRawLogExponent]

end RH.Zeta85.SQ4PublishedLiterature

end
