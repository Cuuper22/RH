#!/usr/bin/env bash
set -euo pipefail

expected() {
  cat <<'EOF'
'zeta85_rung_support_101_over_100' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_rung_support_101_over_100_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_rung_support_5_over_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_rung_support_5_over_4_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_simple_on_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.shiu_majorant₂,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_simple_on_critical_line_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.shiu_majorant₂,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_eighty_five_percent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.shiu_majorant₂,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_eighty_five_percent_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.shiu_majorant₂,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
EOF
}

actual() {
  lake env lean comparator/PrintAxioms/Zeta85.lean 2>&1
}

diff -u <(expected) <(actual)
