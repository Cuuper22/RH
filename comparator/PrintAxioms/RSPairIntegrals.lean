/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSPairIntegrals

/-! Dependency audit for the analytic RS contractions through degree four. -/

#print axioms RH.Zeta85.RSPairIntegrals.integral_abs_mul_shift_div
#print axioms RH.Zeta85.RSPairIntegrals.distanceIntegral_comm
#print axioms RH.Zeta85.RSPairIntegrals.onePairCoordinateIntegral_eq
#print axioms RH.Zeta85.RSPairIntegrals.onePairIntegrand_integrable_of_continuous_compact
#print axioms RH.Zeta85.RSPairIntegrals.distanceKernel_integrable_of_continuous_compact
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_one_eq_coordinate
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_one_eq_distance
#print axioms RH.Zeta85.RSPairIntegrals.integral_fin_two
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_two_eq_coordinate
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k2_distance
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k3_01_distance
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k3_02_distance
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k3_12_distance
#print axioms RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_01
#print axioms RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_02
#print axioms RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_03
#print axioms RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_12
#print axioms RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_13
#print axioms RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_23
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_01_distance
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_02_distance
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_03_distance
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_12_distance
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_13_distance
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_23_distance
#print axioms RH.Zeta85.RSPairIntegrals.normalized_k4_onePairSum
#print axioms RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_separated
#print axioms RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_nested
#print axioms RH.Zeta85.RSPairIntegrals.weightedCyclicSymbol_k4_crossing
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_separated_coordinate
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_nested_coordinate
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_crossing_coordinate
#print axioms RH.Zeta85.RSPairIntegrals.separatedTwoPairSection_eq
#print axioms RH.Zeta85.RSPairIntegrals.separatedTwoPairCoordinateIntegral_eq
#print axioms RH.Zeta85.RSPairIntegrals.nestedTwoPairSection_eq
#print axioms RH.Zeta85.RSPairIntegrals.nestedTwoPairCoordinateIntegral_eq
#print axioms RH.Zeta85.RSPairIntegrals.crossingTwoPairCoordinateIntegral_eq
#print axioms RH.Zeta85.RSPairIntegrals.separatedTwoPairFubiniKernel_integrable_of_continuous_compact
#print axioms RH.Zeta85.RSPairIntegrals.nestedTwoPairFubiniKernel_integrable_of_continuous_compact
#print axioms RH.Zeta85.RSPairIntegrals.crossingRawKernel_integrable_of_continuous_compact
#print axioms RH.Zeta85.RSPairIntegrals.nestedDistanceKernel_integrable_of_continuous_compact
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_separated_eq
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_nested_eq
#print axioms RH.Zeta85.RSPairIntegrals.rsPairIntegral_k4_crossing_eq
#print axioms RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k1
#print axioms RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k2
#print axioms RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k3
#print axioms RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k4
#print axioms RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k2_of_continuous_compactSupport
#print axioms RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k3_of_continuous_compactSupport
#print axioms RH.Zeta85.RSPairIntegrals.normalizedRSMainTerm_k4_of_continuous_compactSupport
