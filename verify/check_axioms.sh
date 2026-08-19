#!/usr/bin/env bash
set -euo pipefail

expected_zeta85() {
  cat verify/zeta85_axioms.expected
}

actual_zeta85() {
  lake env lean comparator/PrintAxioms/Zeta85.lean 2>&1
}

diff -u <(expected_zeta85) <(actual_zeta85)

expected_stability() {
  cat <<'EOF'
'RH.Zeta85.stability_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.tailExcessSq_isometricCompression_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.tailExcessSq_principalCompression_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.stability_inequality_isometricCompression' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.stability_inequality_principalCompression' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF
}

actual_stability() {
  lake env lean comparator/PrintAxioms/Stability.lean 2>&1
}

diff -u <(expected_stability) <(actual_stability)

expected_alias_fallback() {
  cat <<'EOF'
'RH.Zeta85.AliasFallback.moment_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.vandermonde_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.weights_gt_one_25_143' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.weights_gt_one_25_1499999' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.weights_gt_one_25_14999' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.weights_gt_one_25_19999' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.weights_gt_one_25_endpoint_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.intrinsic_atoms_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.atoms_below_14999' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.atoms_below_19999' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.cycle3_scaling_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.corrected_tail_zero_14999' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.AliasFallback.corrected_tail_zero_19999' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF
}

actual_alias_fallback() {
  lake env lean comparator/PrintAxioms/AliasFallback.lean 2>&1
}

diff -u <(expected_alias_fallback) <(actual_alias_fallback)

expected_standard_three_from_printer() {
  awk '
    /^#print axioms / {
      sub(/^#print axioms /, "")
      print "\047" $0 "\047 depends on axioms: [propext, Classical.choice, Quot.sound]"
    }
  ' "$1"
}

normalize_axiom_output() {
  awk '
    {
      line = $0
      sub(/^[[:space:]]+/, "", line)
      if (buffer == "") buffer = line
      else buffer = buffer " " line
      if (line ~ /\]$/) {
        print buffer
        buffer = ""
      }
    }
    END {
      if (buffer != "") print buffer
    }
  '
}

for audit in \
  comparator/PrintAxioms/ActualScaleBBLR.lean \
  comparator/PrintAxioms/PreMajorantDI.lean \
  comparator/PrintAxioms/SQ4SimultaneousRoutes.lean \
  comparator/PrintAxioms/SQ4GaussSquareTransform.lean \
  comparator/PrintAxioms/SQ4CRTConductor.lean \
  comparator/PrintAxioms/SQ4CorrelatedMoment.lean \
  comparator/PrintAxioms/SQ4PublishedLiterature.lean \
  comparator/PrintAxioms/AliasRankObstruction.lean \
  comparator/PrintAxioms/BBLRGCDAllocation.lean \
  comparator/PrintAxioms/EtaClosure.lean \
  comparator/PrintAxioms/EtaSuperpositionObstruction.lean \
  comparator/PrintAxioms/HBDepthFour.lean \
  comparator/PrintAxioms/HBToBBLRSmoothGrouping.lean \
  comparator/PrintAxioms/Inputs95.lean \
  comparator/PrintAxioms/QuarticMain.lean \
  comparator/PrintAxioms/QuarticTransfer.lean \
  comparator/PrintAxioms/QuarticWindowWitnesses.lean \
  comparator/PrintAxioms/R9383ExactEndpoint.lean \
  comparator/PrintAxioms/R1aAllocationNoGo.lean \
  comparator/PrintAxioms/RobustStability.lean \
  comparator/PrintAxioms/RSPairIntegrals.lean \
  comparator/PrintAxioms/RSReduction.lean \
  comparator/PrintAxioms/RSBlockMomentBridge.lean \
  comparator/PrintAxioms/ShiuMajorantQuarter.lean \
  comparator/PrintAxioms/ShiuNoGo.lean \
  comparator/PrintAxioms/TopHatMoments.lean \
  comparator/PrintAxioms/TrimmedMoment.lean
do
  diff -u \
    <(expected_standard_three_from_printer "$audit") \
    <(lake env lean "$audit" 2>&1 | normalize_axiom_output)
done

expected_four_mu_kloosterman() {
  cat <<'EOF'
'RH.Zeta85.FourMuKloosterman.seven_scales_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.one_mu_relative_to_modulus' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.source_modulus_not_prime' depends on axioms: [propext, Quot.sound]
'RH.Zeta85.FourMuKloosterman.oneSided_squareRoot_output_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.oneSided_fixedX_excess_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.oneSided_integrated_excess_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.oneSided_not_fixedX_grade_with_slack' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.simultaneous_candidate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.simultaneous_candidate_integrated_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.simultaneous_gain_decomposition_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.simultaneous_candidate_with_power_slack' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.simultaneous_concrete_loss_allocation_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.FourMuKloosterman.long_log_exponents_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF
}

diff -u \
  <(expected_four_mu_kloosterman) \
  <(lake env lean comparator/PrintAxioms/FourMuKloosterman.lean 2>&1 | normalize_axiom_output)

for audit in \
  comparator/PrintAxioms.lean \
  comparator/PrintAxioms/Multiplicity.lean \
  comparator/PrintAxioms/XiPrime.lean \
  comparator/PrintAxioms/PairCeiling.lean
do
  lake env lean "$audit"
done
