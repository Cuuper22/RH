#!/usr/bin/env bash
set -euo pipefail

expected_zeta85() {
  awk '
    /^## 1\. `#print axioms`/ { section = 1; next }
    section && /^### 1\.4 / { exit }
    section && /^```$/ { code = !code; next }
    section && code { print }
  ' AXIOMS.md
}

actual_zeta85() {
  lake env lean comparator/PrintAxioms/Zeta85.lean 2>&1
}

diff -u <(expected_zeta85) <(actual_zeta85)

for audit in \
  comparator/PrintAxioms.lean \
  comparator/PrintAxioms/Multiplicity.lean \
  comparator/PrintAxioms/XiPrime.lean \
  comparator/PrintAxioms/PairCeiling.lean
do
  lake env lean "$audit"
done
