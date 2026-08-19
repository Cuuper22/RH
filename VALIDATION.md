# VALIDATION.md -- build and audit record for the 85 % layer

Environment: Linux x86-64, Lean `v4.33.0-rc2` (via `elan`), Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129` (pinned in `lake-manifest.json`).
Base commit: `3635e74`.

---

## Table of contents

1. [Build](#1-build)
2. [`sorry` audit](#2-sorry-audit)
3. [`axiom` audit](#3-axiom-audit)
4. [The base repository is unchanged](#4-the-base-repository-is-unchanged)
5. [The conditional topic's axiom audit](#5-the-conditional-topics-axiom-audit)
6. [Statement equality, challenge / solution](#6-statement-equality-challenge--solution)
7. [Deviation from base comparator conventions, declared](#7-deviation-from-base-comparator-conventions-declared)
8. [Numerical cross-checks performed outside Lean](#8-numerical-cross-checks-performed-outside-lean)
9. [Phase 0b inventory and status validation](#9-phase-0b-inventory-and-status-validation)
10. [Phase 0d CI configuration](#10-phase-0d-ci-configuration) | 11. [A1.1 exact exponent audit](#11-a11-exact-exponent-audit)
12. [A1.2 cross-scale audit](#12-a12-cross-scale-audit) | 13. [B-2 Rudnick--Sarnak source audit](#13-b-2-rudnicksarnak-source-audit)
14. [B-1 stability proof](#14-b-1-stability-proof) | 15. [A1.3 exact exponent audit](#15-a13-exact-exponent-audit)
16. [A2.1 common-lattice rank and profile audit](#16-a21-common-lattice-rank-and-profile-audit) | 17. [A2.2 normalization and corrected-tail audit](#17-a22-normalization-and-corrected-tail-audit)
18. [B-3 terminal certificate layer](#18-b-3-terminal-certificate-layer) | 19. [B-4 eta > 1/2 factorization audit](#19-b-4-eta--12-factorization-audit)
20. [Phase-C robust stability and spectral normalization](#20-phase-c-robust-stability-and-spectral-normalization) | 21. [Phase-C Inputs95 boundary](#21-phase-c-inputs95-boundary)
22. [Phase-C quartic transfer and conditional headlines](#22-phase-c-quartic-transfer-and-conditional-headlines) | 23. [A1 exact depth-four Heath--Brown coefficient layer](#23-a1-exact-depth-four-heathbrown-coefficient-layer)
24. [A1 BBLR gcd allocation and finite coefficient collapse](#24-a1-bblr-gcd-allocation-and-finite-coefficient-collapse) | 25. [A1 fixed asymmetric smooth-grouping method class](#25-a1-fixed-asymmetric-smooth-grouping-method-class)
26. [A1 actual-scale BBLR positive-majorant method classes](#26-a1-actual-scale-bblr-positive-majorant-method-classes) | 27. [B-2 RS pair-integral and compact-support gate](#27-b-2-rs-pair-integral-and-compact-support-gate)
28. [A1 pre-majorant DI one-shot gates](#28-a1-pre-majorant-di-one-shot-gates) | 29. [A1 four-Mobius-slot exponent and method-class gates](#29-a1-four-mobius-slot-exponent-and-method-class-gates)
30. [A1 simultaneous SQ4 route gates](#30-a1-simultaneous-sq4-route-gates) | 31. [A1 SQ4 finite Gauss-transform and inversion gates](#31-a1-sq4-finite-gauss-transform-and-inversion-gates)
32. [A1 SQ4 CRT/conductor and shared-gcd gates](#32-a1-sq4-crtconductor-and-shared-gcd-gates) | 33. [A1 SQ4 correlated-moment and published-family gates](#33-a1-sq4-correlated-moment-and-published-family-gates)
34. [A1 SQ4 published-literature gate](#34-a1-sq4-published-literature-gate) | 35. [B-2 actual-block centering bridge gate](#35-b-2-actual-block-centering-bridge-gate)
36. [A2 R1a allocation-capacity no-go gate](#36-a2-r1a-allocation-capacity-no-go-gate) | 37. [B-4 eta-superposition support-model gate](#37-b-4-eta-superposition-support-model-gate)

---

## Summary gate table

"Standard three" below means `[propext, Classical.choice, Quot.sound]`.

| # | Section | What was checked | Result |
|---|---------|-----------------|--------|
| 1 | Build | `lake build` full repo | Zero errors |
| 2 | `sorry` audit | `grep -rn sorry` | Clean (prose only) |
| 3 | `axiom` audit | `grep -rn ^axiom` | 4 in `Hypotheses.lean` |
| 4 | Base repo | Base `PrintAxioms` (43 lines) | Standard three only |
| 5 | Conditional audit | `PrintAxioms/Zeta85` (8 lines) | Expected axiom sets |
| 6 | Statement equality | Type diff (challenge vs. solution) | Identical |
| 7 | Deviation | Rule (5) review | Deviation declared |
| 8 | Cross-checks | External rational arithmetic | Corroborated |
| 9 | Phase 0b | Manifest + 100% claim | Present; claim contradicted |
| 10 | Phase 0d CI | CI workflow build + axioms | Exit zero |
| 11 | A1.1 exponent | `a1_1_method_kill.py` | Byte-for-byte replay |
| 12 | A1.2 cross-scale | `a1_2_cross_scale.py` | Byte-for-byte replay |
| 13 | B-2 RS source | Lean (9 thms) + PDF audit | Standard three |
| 14 | B-1 stability | Lean (5 thms) | Standard three |
| 15 | A1.3 exponent | `a1_3_wg_hb.py` | Byte-for-byte replay |
| 16 | A2.1 rank/profile | Lean (9 thms) + Python | Standard three |
| 17 | A2.2 normalization | Lean + Python | Standard three |
| 18 | B-3 certificate | Lean + 2 Python verifiers | Standard three |
| 19 | B-4 eta closure | Lean (14 thms) + Python | Standard three |
| 20 | Robust stability | Lean + Python | Standard three |
| 21 | Inputs95 | Lean (6 thms) | Standard three |
| 22 | Quartic transfer | Lean (21+8 thms) + Python | Standard three |
| 23 | HB depth-four | Lean (29 thms) | Standard three |
| 24 | BBLR gcd | Lean (5 thms) + Python | Standard three |
| 25 | Smooth grouping | Lean (15 thms) + Python | Standard three |
| 26 | Actual-scale BBLR | Lean (13 thms) + Python | Standard three |
| 27 | RS pair-integral | Lean (51 thms) + Python | Standard three |
| 28 | Pre-majorant DI | Lean (15 thms) + Python | Standard three |
| 29 | Four-Mobius-slot | Lean (13 thms) + Python | 12 standard three + 1 reduced |
| 30 | SQ4 routes | Lean (13 thms) + Python | Standard three |
| 31 | SQ4 Gauss-transform | Lean (6 thms) + Python | Standard three |
| 32 | SQ4 CRT/conductor | Lean (31 thms) + Python | Standard three |
| 33 | SQ4 correlated | Lean (15 thms) + Python | Standard three |
| 34 | SQ4 literature | Lean (6 thms) + Python | Standard three |
| 35 | RS block bridge | Lean (3 thms) + Python | Standard three |
| 36 | R1a allocation no-go | Lean (7 thms) + Python | Standard three |
| 37 | Eta-superposition | Lean (12 thms) + Python | Standard three |

---

## 1. Build

```
$ lake exe cache get        # Decompressed 8681 file(s), exit 0
$ lake build                # Build completed successfully (9023 jobs)
$ lake build Solution Solution.Multiplicity Solution.XiPrime Solution.Zeta85
                            # Build completed successfully (9010 jobs)
```

`lake build` covers `defaultTargets = ["Zeta23", "RH"]`; the `RH` library is the conditional
85 % layer (`lakefile.toml`).

**Zero errors.**  Warnings are pre-existing Mathlib deprecation notices (`Set.mem_setOf_eq`,
`MeasureTheory.integral_finset_sum`) plus unused-variable hints; none originate in `RH/`.

## 2. `sorry` audit

```
$ grep -rn "sorry" --include=*.lean Zeta23/ RH/ comparator/ | grep -v "^comparator/Challenge"
Zeta23/FromPNTPlus/Mertens.lean:31,32     (prose in a module docstring)
Zeta23/FromPNTPlus/StrongPNTPrefix.lean:4 (prose in a module docstring)
comparator/PrintAxioms.lean:10            (prose in a module docstring)
RH/Zeta85/Discharge/SignedShift.lean:10   (prose in a module docstring: "no axioms, no `sorry`")
```

No `sorry` in any proof under `Zeta23/` or `RH/`.  The only proof-level `sorry`s are the deliberate
ones in the trusted challenge files -- `comparator/Challenge.lean`,
`comparator/Challenge/Multiplicity.lean`, `comparator/Challenge/XiPrime.lean` and
`comparator/Challenge/Zeta85.lean` (8 of them, one per statement), exactly as the base repository does.

## 3. `axiom` audit

```
$ grep -rn "^axiom " --include=*.lean Zeta23/ RH/ comparator/
RH/Zeta85/Hypotheses.lean:186  axiom shiu_majorant2 : ...
RH/Zeta85/Hypotheses.lean:220  axiom signedPair_traceGrade_lt_5_4 : ...
RH/Zeta85/Hypotheses.lean:269  axiom signedPair_traceGrade_lt_3_2 : ...
RH/Zeta85/Hypotheses.lean:340  axiom traceTransfer_saturated : ...
```

Four legacy declarations, all in `RH/Zeta85/Hypotheses.lean`.  The former `windowCost_101`,
`windowCost_125`, `bblr_poisson_blocks`, and `bblr_error_bound` are now proved theorems in
`RH/Zeta85/Discharge/`.  `shiu_majorant2` asserts the corrected interface `ShiuMajorant2`
(`RH/Zeta85/ShiuInterface.lean`); the frozen interface `ShiuMajorant` it replaces is refuted
in-repo by `RH.Zeta85.not_shiuMajorant_quarter` (`RH/Zeta85/Discharge/ShiuNoGo.lean`) -- see
`AXIOMS.md` S3, Axiom 1.  These four declarations remain the conditional boundary, not the target
standard.  (The two `axiom` lines in `Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean` sit inside
a fenced code block in a docstring and are not declarations -- this is the point `AUDIT.md` already
records for the base repository.)

## 4. The base repository is unchanged

`lake env lean` on `comparator/PrintAxioms.lean`, `PrintAxioms/Multiplicity.lean`,
`PrintAxioms/XiPrime.lean`, and `PrintAxioms/PairCeiling.lean` produces 43 lines total.  Every line
of the first three reads `'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`;
`PairCeiling` reports `LawN256_check` depends on `[propext]` and `LawN256_edge` depends on no
axioms.  No base theorem acquired a new axiom: nothing under `Zeta23/` imports anything under `RH/`.

## 5. The conditional topic's axiom audit

`lake env lean comparator/PrintAxioms/Zeta85.lean` produces eight lines (reproduced verbatim in
`AXIOMS.md` S1).  The support-`101/100` statements depend on `propext`, `Classical.choice`,
`Quot.sound` and `{signedPair_traceGrade_lt_5_4, traceTransfer_saturated}`.  The support-`5/4`
statements use the same two; the 85 % statements use
`{shiu_majorant2, signedPair_traceGrade_lt_3_2, traceTransfer_saturated}`.  Nothing else appears.

An intermediate revision had collapsed the axiom list to the single refuted `shiu_majorant` and
added eight closed `RH.Zeta85.rung*_from_shiu_contradiction` headlines (R-8657 ... R-9506) whose
proofs were `False`-eliminations off `shiu_interface_contradiction`.  Those eight declarations and
the contradiction are removed; the audit is back to the eight genuine statements, and the per-rung
dependency sets are once again distinct (rungs 1-2 versus rung 3 -- `AXIOMS.md` S2).

## 6. Statement equality, challenge / solution

The `comparator` binary, `landrun` and `lean4export` are **not available in this environment** (no
outbound GitHub access beyond the repository itself).  The full comparator run is recorded as
*not executed*; the command is:

```bash
lake exe cache get
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator/.lake/build/bin/comparator comparator/config-zeta85.json'
```

with `comparator/config-zeta85.json` listing the four `RH.Zeta85.Hypotheses` axioms in
`permitted_axioms` alongside the standard three (see S7).

What **was** executed: `lake build Solution.Zeta85` plus the axiom audit above, and a mechanical
statement-equality check:

```
$ diff <(lake env lean /tmp/tychal.lean | grep -v "declaration uses") \
       <(lake env lean /tmp/tysol.lean)    # no output -- STATEMENT TYPES IDENTICAL
```

with `set_option pp.numericTypes true`.  The elaborated types on both sides coincide, e.g.:

```
zeta85_rung_support_101_over_100 : forall e > (0 : R),
  exists T0, forall T >= T0, ((67924886307 / 100000000000 : R) - e) * (Ncount T ((2 : R) * T))
    <= (N0simple T ((2 : R) * T))
```

This checks the statement-equality half of a comparator run.  It does **not** substitute for the
export + kernel-replay half, which requires the missing tooling.

## 7. Deviation from base comparator conventions, declared

`comparator/README.md`, rule (5): *a statement enters a challenge file only when the Zeta23 theorem
it delegates to is sorry-free with `#print axioms` = the standard three.*

Topic `Zeta85` **deviates** from rule (5): its theorems are conditional on the four named axioms,
and `comparator/config-zeta85.json` lists those axioms in `permitted_axioms`.  This is the only such
topic; the base files and topics `Multiplicity`/`XiPrime` are untouched and unconditional.  A reader
auditing the 85 % claim must read `RH/Zeta85/Hypotheses.lean` in addition to
`comparator/Challenge/Zeta85.lean`.  The exception is a current deficiency to discharge, not an
accepted endpoint.

## 8. Numerical cross-checks performed outside Lean

Recorded in `FINDINGS.md` S4 (exact-rational verification of the whole Phase-A certificate chain,
and double-precision verification of the two source transcendental window costs).  The Phase-A chain
is *also* proved inside Lean, so its external check is only corroboration.  Both frozen lower-rung
targets now have different exact rational witnesses proved in Lean.

## 9. Phase 0b inventory and status validation

The four logical source batches are inventoried in `docs/run/MANIFEST.md`, recording each committed
source file's byte size, SHA-256 digest, and role.  The exact terminal filenames required by the
intake gate are present.

The 100% terminal claim was checked independently with mpmath at 50 and 80 decimal digits plus
exact rational arithmetic in `verify/withdrawn_100_claim.py` (output:
`verify/withdrawn_100_claim.out`).  The calculation proves the endpoint contradiction and shows that
the handoff's M2 <= 0.3144 bound does not follow from the pointwise cone in the supplied sources, so
that number remains an explicit missing-condition finding.

This milestone changes documentation, archived sources, and verification artifacts only.  It does
not constitute the Phase 0c build, comparator, or `#print axioms` rerun; those remain to be
recorded separately.

---

## Convention for sections 10-37

Each gate below follows this pattern unless otherwise noted:

- **Build:** `lake build <Module> RH.Zeta85.Main` (targets vary per section)
- **Printer:** `lake env lean comparator/PrintAxioms/<Module>.lean`
- **Axiom check:** `bash verify/check_axioms.sh` -- every printed theorem diffed against `[propext, Classical.choice, Quot.sound]` ("standard three")
- **Python verifier** (where listed): committed output replays byte-for-byte via `diff -u` or `cmp -s`
- **Source scans:** no `axiom`, `sorry`, `admit`, or `unsafe` in module or printer
- **Import:** `RH.Zeta85.Main` imports every gate module

All gates exit zero.  Deviations are stated explicitly.

---

## 10. Phase 0d CI configuration

The workflow at `.github/workflows/ci.yml` runs `lake exe cache get`, then
`lake build Zeta23 RH.Zeta85.Main Solution Solution.Multiplicity Solution.XiPrime Solution.Zeta85`,
then `bash verify/check_axioms.sh`.

`verify/check_axioms.sh` extracts the expected 44 lines for the eight Zeta85 headlines from
`AXIOMS.md` SS1.1-1.3, diffs against fresh Lean output, runs the four base `PrintAxioms` audits,
and scans for proof-level `sorry`/`admit` outside challenge files.

The GitHub-hosted run is the authoritative CI record (the shell path initially had no Lean
executable; Phase 0c's DigitalOcean reproduction was waived).  The audit harness was repaired at
commit `810353e`: stability module documentation now follows its `import`, and every `Solution*`
module is built before the audit.  With the pinned local toolchain, both build and
`verify/check_axioms.sh` exit zero.

## 11. A1.1 exact exponent audit

**Verifier:** `verify/a1_1_method_kill.py` (exact `Fraction` arithmetic; output:
`verify/a1_1_method_kill.out`).

The script recomputes Phase A1.1 scales and asserts:
- P=HQ, Q=P^{50/93}, PQ=T^{143/100}
- Nguyen + residue Parseval/Cauchy exponent 3917/2400, excess 97/480
- Parry + Parseval and absolute modulus summation exponent 261/160, excess 161/800
- Parry's 4/7 range margin 22/651; Wei--Xue--Zhang range deficit 1951/54312
- Natural-order variance + Cauchy: exactly zero power margin
- Literal C=0 log exponent 2, strictly below trace-normalization exponent 3

Premises checked against `docs/audit/log_budget_routes.md`, Route 5.  No Lean declaration changed;
no axiom or `Inputs95` field introduced.

## 12. A1.2 cross-scale audit

**Verifier:** `verify/a1_2_cross_scale.py` (exact `Fraction` arithmetic; output:
`verify/a1_2_cross_scale.out`).

The script asserts:
- P=T^{93/100}, Q=T^{1/2}, PQ=T^{143/100}=Y; PH=T^{34/25}, giving exact power saving T^{-7/100}
- At forced C=3: literal dyadic summation log exponent 5, cross-Y recombination exponent 4, budget exponent 3; equation (6) misses by exactly one log power
- A five-block aligned family attains the sum of the five individual bounds

The last statement is generalized in Lean by `RH.Zeta85.LogBudget.blockwise_triangle_sharp`; the
forced-exponent failure is `crossScale_recombination_fails`.  No analytic input or new field
introduced.

The requested historical signed-prime experiment could not be reproduced: no generating script or
coefficient construction is present in the supplied archives or connected Drive intake.  This
negative inventory result is recorded.

## 13. B-2 Rudnick--Sarnak source audit

**Source:** `docs/audit/rs_reduction.md`, checked against Rudnick--Sarnak (1996) primary PDF
(SHA-256: `83010c4f68efc5f5628a71a589ff3a374220b25902384e9c1a34b3d6cd0834d6`).  The audit records
Theorem 3.1 (unconditional at m=1), Theorem 3.2 (RH hypothesis), Lemmas 4.2-4.3 (distributional
content), cyclic symbol, flat contractions, weighted specialization to terminal formula (18), and
corrected source map.

**Gate:** `lake build RSReduction Main` | `PrintAxioms/RSReduction.lean` | `check_axioms.sh`.
**Axioms:** 9 theorems, standard three.

`RSReduction.lean` proves the zero-frequency cyclic-symbol identity, zero-sum contraction vectors,
exact 0,1,3,6+3 pairing enumeration, formula-(27)-to-(18) centering, and top-hat
formula-(18)-to-(21) specialization.

This deterministic milestone alone was not the analytic R1b discharge.  `RSPairIntegrals.lean` (S27)
later identifies `normalizedRSMainTerm` with the uncentered contraction formula for a continuous
compactly supported profile.  No theorem transfers that formula to the actual principal block.
Cyclic-symbol admissibility, the actual published-field instance, common height smoothing,
log-T-normalization, off-RH complex Poisson, and k=3,4 finite-grid/end estimates remain listed in
`FINDINGS.md` S16 and `docs/audit/rs_reduction.md` S9.

## 14. B-1 stability proof

**Gate:** CI build targets include `RH.Zeta85.Main` (which imports `Stability.lean`) |
`PrintAxioms/Stability.lean` | `check_axioms.sh`.  **Axioms:** 5 theorems (stability + compression
headlines), standard three.

No new field or primitive declaration introduced.  The GitHub workflow run is the authoritative build
in the current environment.

## 15. A1.3 exact exponent audit

**Verifier:** `verify/a1_3_wg_hb.py` (exact `Fraction` arithmetic; output:
`verify/a1_3_wg_hb.out`).

The script constructs (not hard-codes) the two Bettin--Chandee exponents from the theorem's
L^2-norm and bracket factors.  It also checks:
- Candidate simultaneous-dispersion saving 7/200 and net saving 7/400
- Fixed-Weil excess 9/50
- BBLR endpoint excesses
- Blomer--Pascadi range gap 83/300
- Milicevic--Qin--Wu condition gaps 141/250 and 47/100

Matching arithmetic identities formalized in `RH/Zeta85/Discharge/LogBudget.lean`.  This validates
the method-class audit only; it does not add the missing analytic estimate.

## 16. A2.1 common-lattice rank and profile audit

**Verifier:** `verify/a2_1_tdac_rank.py` (exact `Fraction` intervals + 90-decimal
integer-square-root enclosures + rational Taylor remainders; output: `verify/a2_1_tdac_rank.out`).
The script reconstructs matching constants A, B, normalization M, endpoint value, and edge margin
from terminal file 24's equations (28)-(29); no constant is hard-coded.  Separate 60- and
100-decimal `mpmath` evaluations agree beyond 55 places.  Committed output certifies positive
residual margins >1/1000, >1/1000, >1/10 for R-9506, R-8686, and file-15 Euler repair respectively,
checks three exact rank deficits, and derives edge residual `42756493/1031000000 > 0` and central
average `1157918831/1031000000 > 1` by exact rational arithmetic.  The latter prevents the
unnormalized profile from being used to claim a false zero-row obstruction.

**Lean gate:** `PrintAxioms/AliasRankObstruction.lean`.  **Axioms:** 9 theorems, standard three.
The module proves explicit outer-product channel rank bound, full diagonal rank, critical-count
contradiction, full-minus-distinguished formulation, and three terminal integer count corollaries.
Two Euler-profile nonvanishing premises remain in the interval verifier.  This formalizes the
algebraic method-class impossibility without adding an analytic input or changing a frozen rung.

## 17. A2.2 normalization and corrected-tail audit

**Verifier:** `verify/a2_2_alias_free_scaling.py` (exact `Fraction`; output:
`verify/a2_2_alias_free_scaling.out`).  The script:
- Derives A=1031/1200 and sup V_sigma = 1200/1031 < 143/100
- Recomputes saturated quadratic costs at 143/100, 1.499999, 1.4999, 1.9999, and diagnostic endpoint 2
- Reconstructs rational closed moments M_2, M_3, M_4 from restriction parameters
- Inverts the rational 5-node Vandermonde matrix (determinant 99/500000); checks every weight > 1/25
- Checks exact moment equality through degree four and strict support gap 2/5 < sigma - 1
- Independently evaluates terminal formula (18) by 55-digit tensor Gauss--Legendre quadrature; largest calibration discrepancy below 2e-56

**Lean gate:** `PrintAxioms/AliasFallback.lean`.  **Axioms:** standard three.
`AliasFallback.lean` contains no proof placeholder or primitive assumption.  This validates the
finite rational countermodel conditional on the paper-derived closed moment formulas; it does not
formalize their equality with Mathlib integrals or the RS bridge to formula (18), add a
principal-block input, or alter a frozen rung.

## 18. B-3 terminal certificate layer

**Verifiers:** `verify/b3_certificate_audit.py` and `verify/b3_r9383_exact_endpoint.py` (both
byte-for-byte replay).

| File | SHA-256 |
|------|---------|
| `verify/b3_certificate_audit.py` | `2f264e6637de2ec09ef5eae93f9f1368eb9a3c6ad0ea2e0c4b05c084f125ceab` |
| `verify/b3_certificate_audit.out` | `f34b7ca98bebe570140778d1d7341f04ad3191c199153bbecffe17528d2eb130` |
| `verify/b3_r9383_exact_endpoint.py` | `3b01ca20b4c0b4ce54ac067050998796852be8417df57a204aa5ab20bc5b77ab` |
| `verify/b3_r9383_exact_endpoint.out` | `aa8b584aaf771b15ea0b1aeea18df69b29dd4563b6246fa25cd0eda7b861aaad` |

`b3_certificate_audit.py` uses exact rational arithmetic for terminal moments, dual-polynomial
factor signs, fixed-point comparisons, Bernstein positivity, and polynomial window-cost integrations
(`mpmath` three-atom calculations are calibration only).  `b3_r9383_exact_endpoint.py` uses only
integer and `Fraction` operations: rational Taylor remainders, integer-square-root bounds, and
interval AD isolate the flat endpoint in [0.9383133270509488847, 0.9383133270509488848], strictly
below frozen R-9383.

**Lean gate:** `lake build QuarticWindowWitnesses R9383ExactEndpoint TopHatMoments TrimmedMoment
Main` | 4 isolated printers | `check_axioms.sh`.  **Axioms:** standard three for every theorem.
`TopHatMoments.crossingReduction` proves the full determinant-one change of variables,
support-intersection calculation, four-quadrant reduction, and `formula21M4Integral_eq` proves the
original three-dimensional formula-(21) fourth moment without a field or named premise.

The finite R-8686 and R-9506 implications do not instantiate the missing A1, R1a, or R1b analytic
bridges.  No quartic headline existed at this B-3 gate alone; the later Phase-C transfer (S22)
assembles conditional headlines under four explicit structures without discharging them.

## 19. B-4 `eta > 1/2` factorization audit

**Verifier:** `verify/b4_eta_closure.py` (exact `Fraction`; output: `verify/b4_eta_closure.out`).

| File | SHA-256 |
|------|---------|
| `verify/b4_eta_closure.py` | `b934eab4fc22da185cda8a1bc2e11a10cdda3449b1479c435902d681997f008f` |
| `verify/b4_eta_closure.out` | `441e426de1218676e6cf322f2971c8d403d9fd439d0f5973ac000ace9e3568b3` |

At exact witness eta=3/4, the script verifies the legal depth-three j=2 block, exhausts all
whole-variable groupings, checks the unavailable M1 exponent, recomputes both balanced-block power
excesses, the positive preliminary margin, and the literal C<1 logarithmic threshold.

**Axioms:** 14 theorems, standard three.  These checks establish the unconditional exponent and
method-class audit only; they do not assert (EF_eta) or change a frozen rung's status.

## 20. Phase-C robust stability and spectral normalization

**Verifier:** `verify/robust_stability.py` (integer + `Fraction`; output:
`verify/robust_stability.out`).

| File | SHA-256 |
|------|---------|
| `verify/robust_stability.py` | `8510ca4748e26e9310c3f89a5df1ef95d5f015761bec86f41b8e545fd04454bc` |
| `verify/robust_stability.out` | `8d2cf177b0104dc0872591fde5da73f950415b56b185ed68917451d90931117b` |

The verifier independently expands the finite prebound, checks error vector (2,4,1,2) and exact
count slack, evaluates three rational substitutions, and checks sorted-head cardinality, removed
mass, and residual identities on explicit finite spectra.

**Axioms:** standard three (finite prebound, base/isometric/principal robust inequalities, uniform
trim construction, exact residual identity, four-moment adapter).  No analytic moment equality or
limiting statement is asserted.  The robust-stability result alone discharges no analytic premise;
conditional assembly is in S22.

## 21. Phase-C `Inputs95` boundary

**Lean gate:** `lake build RH.Zeta85.Inputs95 RH.Zeta85.Main` | `PrintAxioms/Inputs95.lean`.
**Axioms:** 6 theorems (`profileSaturatedCost_v8686`, `profileSaturatedCost_v9506`,
`G_eq_A_add_E`, `block_isHermitian`, `core_count_le_dyadic_add_edge`,
`robustBlockTailBound_eventually`), all standard three.

Family types contain exact B-3 profiles.  Matrix definitions use the actual full zero sum and finite
`ZIprime` truncation; the robust adapter concludes on that truncation's literal principal block.
No `Inputs95` instance or constructor theorem exists.  This gate validates the hypothesis boundary
and its finite adapters; the separate conditional headline gate is S22.

## 22. Phase-C quartic transfer and conditional headlines

**Verifier:** `verify/quartic_transfer.py` (exact `Fraction`; output:
`verify/quartic_transfer.out`).

| File | SHA-256 |
|------|---------|
| `verify/quartic_transfer.py` | `dc99b510fdf1966f11535bf57a3dc53f4056c679e0275c8a649c01facf5f3bdf` |
| `verify/quartic_transfer.out` | `05615d7eb1727532cb81a5c04598630ebd9c29408b729770d34e4b282b533cce` |

The script checks edge identity 2 + (1-cap/2) + cap/2 = 3, both fixed-point quotient identities,
both strict frozen-target margins, and monotone comparisons R-8657 < R-8686 and R-9383 < R-9506.

**Lean gate:** `PrintAxioms/QuarticTransfer.lean` + `PrintAxioms/QuarticMain.lean`.  **Axioms:** 21
transfer + 8 headline theorems, all standard three.  `QuarticTransfer` proves spectral-moment
identity, exact finite dual scaling, edge coefficient three, NII=o(N), normalized limit, generic
epsilon transfer, and four concrete zeta specializations.  Direct R-8686 and R-9506 branches have
strict exact margins; R-8657 is monotone from R-8686, R-9383 from R-9506.

`QuarticMain.lean` exposes eight final statements (`rung8657`, `rung8657_cumulative`, `rung8686`,
`rung8686_cumulative`, `rung9383`, `rung9383_cumulative`, `rung9506`, `rung9506_cumulative`), each
taking exactly `FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, and
`BlockMomentLimits`.  Pair-trace and RS structures are upstream derivation routes, not headline
premises.

No instance of the four analytic structures is constructed.  The comparator dependency audit
confirms only their standard-three kernel footprint.  It neither supplies trusted-statement
comparator equality nor makes the four rungs unconditional.

## 23. A1 exact depth-four Heath--Brown coefficient layer

**Lean gate:** `PrintAxioms/HBDepthFour.lean`.  **Axioms:** 29 theorems, standard three.

`HBDepthFour.lean` proves the exact four-term sharp-cutoff identity through n <= Z^4, arbitrary
eight-slot grouping factorization, exact d_1 d_2 = d_3 d_4 = d coefficient sums, literal triangle
majorants, dyadic support machinery, common (j,d,l,p,q) indexing, generic residue-cell centering,
reduced-residue mean construction with signed four-component sum (each reduced centered sum is zero),
and exact countermodels showing the old all-class mean cannot replace the reduced mean and reduced
centering alone cannot imply a singular-series main term.  Planned closed floor blocks are not
claimed to be the source partition; neither residue mean is claimed to be BBLR's frequency l=0
gcd/integral term.  Boundary: `docs/audit/hb_depth_four_coefficients.md`.

No numeric verifier required (no calibrated numerical claim).  The printer is a dependency audit,
not a trusted Challenge/Solution comparator.  No theorem identifies these sharp coefficients with
run 12's smooth c, e, or F, evaluates the signed frequency l=0 integrals against the Ramanujan
singular series with an explicit error, proves an A1 estimate, or changes a frozen rung status.

## 24. A1 BBLR gcd allocation and finite coefficient collapse

**Lean gate:** `PrintAxioms/BBLRGCDAllocation.lean`.  **Axioms:** 5 theorems, standard three.
**Verifier:** `verify/bblr_gcd_allocation.py` (exact replay).

`BBLRGCDAllocation.lean` proves positive-d canonical allocation equivalence, both inverse
identities, reduced-product coprimality and its converse gcd formula, filtered one-side coefficient
collapse with multiplicity one, and two-sided finite-kernel reindexing.  The d=p=2 regression proves
the canonical unit coefficient has three terms while the unfiltered raw split has four; the Python
enumeration matches.

This validates only the finite source collapse for supplied BBLR outer sequences, inner smooth
weights, and kernel.  It does not construct the smooth signed Heath--Brown grouping, prove (EDB) or
(WG-HB), evaluate the frequency l=0 integrals, or change any frozen rung status.  Boundary:
`docs/audit/bblr_gcd_allocation.md`.

## 25. A1 fixed asymmetric smooth-grouping method class

**Lean gate:** `PrintAxioms/HBToBBLRSmoothGrouping.lean`.  **Axioms:** 15 theorems, standard three.
**Verifier:** `verify/a1_smooth_grouping.py` (exact `Fraction` replay).

| File | SHA-256 |
|------|---------|
| `verify/a1_smooth_grouping.py` | `67550b74daf9ae0ed31ad37729fbf35ba52a64ddd245a2860ada0da65df42793` |
| `verify/a1_smooth_grouping.out` | `fd1fa689b25c6dfdc9545b6bf248cd9079126b8c07ad681ece66262cb1f8c5bb` |

The Lean module checks zero-based j=1 component inventory and scalar, proves truncated Mobius atoms
are not coefficient-one slots, verifies the exact terminal exponent block, and proves fixed
left/right/two-sided literal-slot assignments impossible below their exact gaps.  It also proves
collapsing two coefficient-one slots creates zeta*zeta rather than a literal BBLR smooth variable.
The Python verifier checks the signed component coefficient, Mobius/coefficient-one distinction
at (2), every exponent identity and gap, and divisor multiplicities at (2) and (4).

This validates only the killed fixed-scale literal-slot method class.  It does not supply an
actual-scale all-block estimate, smooth superposition identity, higher-dimensional divisor theorem,
(EDB), (WG-HB), or A1 trace input, and changes no frozen rung status.

## 26. A1 actual-scale BBLR positive-majorant method classes

**Lean gate:** `PrintAxioms/ActualScaleBBLR.lean`.  **Axioms:** 13 theorems, standard three.
**Verifier:** `verify/a1_actual_scale_bblr.py` (exact `Fraction` replay).

| File | SHA-256 |
|------|---------|
| `verify/a1_actual_scale_bblr.py` | `e7c25c211113adc8a0ab51a7e348073f6c4ffacb96ae05785f9d16199d3adb2a` |
| `verify/a1_actual_scale_bblr.out` | `5c0514d743c30ae1b1d89420bb4ff295c01534031d41e2f004b176dcb7f00c42` |

`ActualScaleBBLR.lean` proves exact actual-block geometry, both BBLR Proposition 3.1 error exponents
and positive excesses, equation (14) Fourier physical scale and frequency-cutoff cancellation, exact
d=1 progression lengths, the PQ obstruction, and harmless PH and H^2 terms.

This validates only the failure of direct Proposition 3.1 and of the run-12 progression majorant on
the exact symmetric block.  It does not prove a lower bound for the signed remainder, exclude
simultaneous coefficient cancellation before the majorant, supply an A1 trace input, or change a
frozen rung status.

## 27. B-2 RS pair-integral and compact-support gate

**Lean gate:** `PrintAxioms/RSPairIntegrals.lean`.  **Axioms:** 51 theorems, standard three.
**Verifier:** `verify/rs_pair_integrals_exact.py` (exact replay).

| File | SHA-256 |
|------|---------|
| `verify/rs_pair_integrals_exact.py` | `04b2a386bd83f19c39307ddf4b7ea36ffc62802f924efcf1d53292d5aa929833` |
| `verify/rs_pair_integrals_exact.out` | `e090227f8f2768c2a75771ce9ac2fc157e45b1650e09f901530f0a76ab48f4f2` |

`RSPairIntegrals.lean` proves all one-pair and two-pair contractions through degree four, their
exact normalization, and final wrappers deriving all kernel integrability from `0 < mu`,
`Continuous r`, and `HasCompactSupport r`.  The Python verifier enumerates pairing counts and every
partial-sum profile and checks raw/normalized scaling powers.

This gate discharges only the internal analytic RS main-term evaluation.  It does not construct
`BlockMomentLimits`, instantiate the actual published theorem-3.1 field, or discharge
cyclic-symbol admissibility, common height smoothing, log T vs. ell(T) = log(T/2*pi), complex
Poisson, degree-three/-four finite-grid/end estimates, or actual principal-block identification.
No frozen rung status changes.

## 28. A1 pre-majorant DI one-shot gates

**Lean gate:** `PrintAxioms/PreMajorantDI.lean`.  **Axioms:** 15 theorems, standard three.
**Verifier:** `verify/a1_premajorant_di.py` (exact `Fraction` replay).

| File | SHA-256 |
|------|---------|
| `verify/a1_premajorant_di.py` | `1901eda16d2824e1692c1639eccf120d24cd40c1ddefbf631a55fccbb776db2b` |
| `verify/a1_premajorant_di.out` | `0d95711e582c826ff0227daef45bd2bbf73885723d189f43283a06eb9a27756a` |

`PreMajorantDI.lean` proves exact source scales, collapsed coefficient norm exponent, all three
Drappeau K^2 exponents, direct integrated exponent 179/100, its exact 9/25 excess over trace, the
finite Z/5Z inverse mismatch, and candidate Pascadi factor arithmetic (explicitly conditional: no
cited analytic theorem or source-faithful reindex asserted).

Two distinct conclusions: the direct collapsed Drappeau class is power-killed at 179/100, and the
literal completed r=a Pascadi map is structurally inapplicable.  A (q,a)-dependent reindex with
separate k=0 treatment remains open.  No A1 field discharged; no frozen rung status changes.

## 29. A1 four-Mobius-slot exponent and method-class gates

**Lean gate:** `PrintAxioms/FourMuKloosterman.lean`.  **Axioms:** 12 theorems at standard three;
1 (`source_modulus_not_prime`) at `[propext, Quot.sound]` only -- `check_axioms.sh` records that
line separately.  **Verifier:** `verify/a1_four_mu_kloosterman.py` (exact `Fraction`).

`FourMuKloosterman.lean` proves exact seven retained scales, composite-modulus obstruction, killed
one-sided fixed-modulus/square-root/triangle output, and arithmetic of the surviving simultaneous
candidate.  The Python verifier checks fixed-x and integrated targets, the 49/200 one-sided misses,
149/100 and 63/50 simultaneous candidate exponents, 17/400+17/400 strict loss allocation, and
normalized/raw long-log exponents 0 and 2.

| File | SHA-256 |
|------|---------|
| `Discharge/FourMuKloosterman.lean` | `bc67127847ef877cf3d615a747df83e60da2fa7a046c0ed8ed372d18ca23601c` |
| `PrintAxioms/FourMuKloosterman.lean` | `33a45b0dfa795ee0a88457710b50df1f9129a30e0e85b8905e4ef692e7476968` |
| `docs/audit/four_mu_kloosterman.md` | `f3c697d60b70f32abb22748f7dd28219c2e656fc0efeaa5fd61d7af560436901` |
| `verify/a1_four_mu_kloosterman.py` | `a8eb4b39fb9215c0af8b45449a036c8cee4c434a0906c3a9f6a55742e1146594` |
| `verify/a1_four_mu_kloosterman.out` | `3c1abc99cb74c993323371b23ed806dad68ad76fc0472a665cb989a1f11e6977` |

This validates exponent bookkeeping and the exact narrow method-class verdict only.  The
simultaneous analytic estimate (SQ4-HB) and smooth source-identification/recombination identity
remain unproved.  No A1 field discharged; no frozen rung status changes.

## 30. A1 simultaneous SQ4 route gates

**Lean gate:** `PrintAxioms/SQ4SimultaneousRoutes.lean`.  **Axioms:** 13 theorems, standard three.
**Verifier:** `verify/a1_sq4_simultaneous_routes.py` (exact `Fraction`).

`SQ4SimultaneousRoutes.lean` proves exact rational source scales; fixed-x and integrated outputs and
excesses of the character-large-sieve, coefficient-uniform norm-only, additive-large-sieve, Poisson
zero-mode, and Poisson-Weil/triangle calculations; reciprocal profile, completion prefactor, and
dual length; and normalized/raw logarithmic exponents 0 and 2.  No analytic estimate or placeholder
stated.

The Python verifier checks all fixed and integrated outputs/excesses, profile and truncation scales,
explicit nonzero loss T^{eta+epsilon} with 0 < eta < 2/5, normalized/raw long-log exponents, and
six route labels.  Two structural-applicability verdicts are source-audited in
`docs/audit/sq4_simultaneous_routes.md`.

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4SimultaneousRoutes.lean` | `3ff0acf59b6a0f828f5d0e00fe8af3a4ef9225a8d3456f3877f2193b1c52c661` |
| `PrintAxioms/SQ4SimultaneousRoutes.lean` | `eaa5e835a79bdcfe051811a8c9d8e690ca5d6fbe1895fbf973909c9470da910b` |
| `docs/audit/sq4_simultaneous_routes.md` | `c87497add008c3113efb23528c07df9f39f45c8867278209f7f3fe49008c08c5` |
| `verify/a1_sq4_simultaneous_routes.py` | `fe11015425ec5312fd1894144ff17b6bcb8cfd303735c5774068e8554c04cd6a` |
| `verify/a1_sq4_simultaneous_routes.out` | `ece3e6a0dd1de6ba8100c90e2d59ba1caf4af77de6ea72283b0acf79945932b8` |

The audit makes the Poisson zero mode power-safe but does not prove (SQ4-HB).  The nonzero
transformed family (33), smooth source-identification/recombination, and required correlated estimate
remain open.  No A1 field discharged; no frozen rung status changes.

## 31. A1 SQ4 finite Gauss-transform and inversion gates

**Lean gate:** `PrintAxioms/SQ4GaussSquareTransform.lean`.  **Axioms:** 6 theorems, standard three.
**Verifier:** `verify/a1_sq4_gauss_square_transform.py` (exact `Fraction`).

The Lean module proves six exact finite-algebra results: abstract correlation transform, product of
two generalized shifted Gauss sums for arbitrary residues, unit-shift scaling identity, Gauss-square
specialization, full Dirichlet-character Fourier inversion for every positive modulus (including
composite), and exact Kloosterman-kernel character inversion.  No complete-sum bound, primitivity
assumption, CRT recombination, analytic moment, (SQ4-HB), or placeholder stated.

The Python verifier reconstructs source scales, completion exponent -43/100, exact pre-completion
(SQ4-HB) target 48/25 with fixed log exponent 0, weaker literal target 209/100, coefficient-blind
pre-completion output 121/50 (misses targets by 1/2 and 33/100), and raw two-long-slot logarithmic
exponent 2.  All builds, printer, diff, axiom gate, source scans, and `git diff --check` exit zero.

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4GaussSquareTransform.lean` | `1c58791ca5d3f2f2879c6e5e6ae60ebb3b9efd9b1f9c0ae90ae1c73aa72dc3e5` |
| `PrintAxioms/SQ4GaussSquareTransform.lean` | `99359bb5bc9cd5de16edac3cf369deed8def95e8b4129dd18dae8ef58d8e2db2` |
| `docs/audit/sq4_gauss_square_transform.md` | `03a629e8e1c522c8f84766b4f06e49d9ef5fb8154fa5564d617eb545533a1dac` |
| `verify/a1_sq4_gauss_square_transform.py` | `387225f5f613fcf79be7412f308f2859b255eefade6237ed2ddfd3432e337981` |
| `verify/a1_sq4_gauss_square_transform.out` | `89168a2503baea412b3bc96b465ff7f7335ac700f41e23ddbe6190cb63d718d0` |

The exact unresolved analytic object is equation (14) of
`docs/audit/sq4_gauss_square_transform.md`, retaining all four Mobius factors, generalized shifted
Gauss products on every nonunit conductor/gcd stratum, and the varying factorized composite modulus.
The required bound and smooth source-identification/recombination remain unproved.  No A1 field
discharged; no frozen rung status changes.

## 32. A1 SQ4 CRT/conductor and shared-gcd gates

**Lean gate:** `PrintAxioms/SQ4CRTConductor.lean` (38 declarations).  **Axioms:** 31 printed
theorems, standard three.  **Verifier:** `verify/a1_sq4_crt_conductor.py` (integer polynomial in
Q[x]/Phi_q(x)).

The Lean module proves coprime CRT factorization with complementary-modulus twists, arbitrary
nonunit-shift conductor support, general complex primitive-`changeLevel` imprimitive Gauss formula
in divisor-d and divisor-s coordinates, inverse-to-conjugate phase, unit-supported formula,
squarefree shared-gcd decomposition, Mobius-sign cancellation, and minimal Z/4Z false-CRT
counterexample.

The Python checker calibrates 3,336 imprimitive identities for selected primitive real characters
(including zero shifts and shared-prime quotient levels), checks 1,208 nonzero conductor-support
instances, and enumerates 3,721 squarefree shared-gcd strata.  The general nonreal complex
conjugation phase is proved by Lean only.  `Fraction` also verifies 48/25 - 43/100 = 149/100 and
121/50 - 48/25 = 1/2.

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4CRTConductor.lean` | `7e42a5cdad131001fdc411d66229f5aa845a63da42b92334579f0e309853b2b3` |
| `PrintAxioms/SQ4CRTConductor.lean` | `217ff71194a7769b45be368239db747f37627ab061054a26f57795423342f8cd` |
| `docs/audit/sq4_crt_conductor_strata.md` | `47a4f858b284e2106051d6dc5a3ef1d50a1aed27ce89730bda27dd9d6d0181ea` |
| `verify/a1_sq4_crt_conductor.py` | `43291f853513881dfba2aa432a59993364257be3756f406bf00c2ac5d62bf02f` |
| `verify/a1_sq4_crt_conductor.out` | `78ed2cedad32d5ebd348aaa034f98bda5676804ab9691b7cb963752eceeb24e1` |

The exact analytic target remains |M_4(T,x)| << T^{48/25+epsilon} (log T)^0, with all four Mobius
factors, shared conductor/divisor coupling, and joint source weight retained before Cauchy.  The
smooth source bridge is a separate blocker.  No A1 field discharged; no frozen rung status changes.

## 33. A1 SQ4 correlated-moment and published-family gates

**Lean gate:** `PrintAxioms/SQ4CorrelatedMoment.lean`.  **Axioms:** 15 theorems, standard three.
**Verifier:** `verify/a1_sq4_correlated_moment.py` (exact `Fraction`).

`SQ4CorrelatedMoment.lean` proves exact rational scales, fixed and integrated outputs, strict
excesses, explicit KSWX reciprocity-error allocation, corrected Pascadi equation-(5.32) geometry,
and every fixed logarithmic exponent.  It asserts none of the cited analytic theorems, no favourable
grant, no estimate for family (33), no (SQ4-HB), and no source-identification bridge.

The Python verifier checks these distinct method-class outputs:
- Coefficient-blind character Cauchy: 199/100; budget and (SQ4-HB) excesses 33/100 and 1/2
- Ideal fixed-(p,v) square-root cancellation in (k,r): 179/100; excesses 13/100 and 3/10
- Blomer--Pascadi July 2026 preprint at fixed (p,v): H=71/900, inner 2617/1800, outer-triangled 4111/1800
- Published KSWX favourable Type-I: best Delta_1 = -43/200, completed 421/200, reciprocity-error 287/200 after allocations eta=epsilon=1/20, margin 11/200
- Published Pascadi Corollary 5.11: literal squarefree-v output 513/200, vs. conditional 47/20 under unstated general-first-sequence/recombination grant
- Normalized/raw fixed log exponents 0/2, literal Corollary 5.11 exponents 1/3, favourable general-first-sequence 2/4

Primary-source map recorded in audit, not Lean.  Blomer--Pascadi Theorem 5.5 is a preprint; KSWX
Theorem 2.1 and Pascadi Corollary 5.11 are published but the former has explicit favourable
coprimality/energy grants and the latter literal lift covers squarefree-v strata only.  Pascadi
Corollary 5.9/Assumption 5.4 cited with journal numbering (arXiv: 16 and 14); Assumption-5.4
instance derived from published Theorem 1.2 after norm-preserving additive twist.

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4CorrelatedMoment.lean` | `8d3ea41ae50b37f089408aa78c56dcc0d84be18661fdc0fae2587c03556f7f66` |
| `PrintAxioms/SQ4CorrelatedMoment.lean` | `e9c09a9d0cd8e7963b1216cac2f3e0018dd8122e2866ab95b0a1577653c5d733` |
| `docs/audit/sq4_correlated_moment.md` | `65b9cb6d5f88b0b014e4425319c1518b4ba26d2430c7cb2e48745ab44e1ac659` |
| `verify/a1_sq4_correlated_moment.py` | `72b24b4ba09b195651192b03adef58aed7e3706541bf3abc76bfb0595105db31` |
| `verify/a1_sq4_correlated_moment.out` | `cc815831e1961a5853d628148ad9c84ed94753ac36597c9c7dc274e80f4064b5` |

This gate does not prove the required T^{48/25+epsilon} (log T)^0 signed generalized-Gauss-product
level moment, cover the nonsquarefree g-does-not-divide-k strata by the Ramanujan lift, or supply
the smooth source-identification/recombination identity.  No A1 field discharged; no frozen rung
status changes.

## 34. A1 SQ4 published-literature gate

**Lean gate:** `PrintAxioms/SQ4PublishedLiterature.lean`.  **Axioms:** 6 theorems, standard three.
**Verifier:** `verify/a1_sq4_published_literature.py` (exact `Fraction`).

The Lean module proves common pre-completion normalization, exact outputs and positive target gaps
for the reviewed numerical method classes, and normalized/raw fixed-log inventories.  The Python
verifier checks pre-completion target 48/25, completion prefactor -43/100, and audited outputs
121/50, 111/50, 553/200, 2071/800, 1017/400, 977/360, 507/200, 139/50, 599/200 with all displayed
gaps.  It reconstructs fixed-log exponents: standard 0/2, literal Pascadi 1/3, conditional Pascadi
2/4.

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4PublishedLiterature.lean` | `246f5fbfa341df4fd90c1cea2ea7ee2092cb30cdf75bf812cdbdb9d8640aa5d4` |
| `PrintAxioms/SQ4PublishedLiterature.lean` | `3cca37c88b5f70eb138f6df8c9fcbf2819daa6accf32788f5daf86be2abaf52e` |
| `docs/audit/sq4_published_literature.md` | `4d80e51bb81bab4687058cc6d9d9b508157ec047a37b2a1b5499c621a8a2a8a3` |
| `verify/a1_sq4_published_literature.py` | `5917882577253cf755f96685a16680d92ee2b240512c6d7cc6220e60a1ff63a6` |
| `verify/a1_sq4_published_literature.out` | `2585a510a4eb651c62521d58ba6ddab8753d22f0f54a2f73b24d9e95c8c598be` |

The source audit finds no published theorem in the audited classes with the literal full-M_4
left-hand side (not a universal nonexistence claim).  The required T^{48/25+epsilon} (log T)^0 bound
and smooth source identification/recombination remain unproved.  No A1 field discharged; no frozen
rung status changes.

## 35. B-2 actual-block centering bridge gate

**Lean gate:** `PrintAxioms/RSBlockMomentBridge.lean`.  **Axioms:** 3 theorems, standard three.
**Verifier:** `verify/rs_block_moment_bridge_exact.py` (integer polynomial multiplication).

`RSBlockMomentBridge.lean` proves the literal finite-matrix binomial identity through degree four,
passes assumed uncentered actual-block limits through that transform, identifies the result with
formula (21), and supplies a constructor for `BlockMomentLimits`.  The raw degree-zero limit retains
eventual positivity of block dimension.  The constructor boundary remains analytic: it assumes
`UncenteredRSBlockLimits F` and separately assumes complex-alias summability and cancellation at
actual enlarged-window zeros.  It does not derive these from `RS1996ZetaInputs`, construct a
principal family, or prove cyclic-symbol, height-removal, normalization, complex-Poisson, or higher
finite-grid estimates.  The Python verifier independently expands (X-1)^k with integer polynomial
multiplication and compares coefficients with the binomial transform for 0 <= k <= 4.

| File | SHA-256 |
|------|---------|
| `Discharge/RSBlockMomentBridge.lean` | `1ee61b9737e3ce8bb4d70da268e88ff1a3446e2b1be33916f1d0b05028702836` |
| `PrintAxioms/RSBlockMomentBridge.lean` | `d0b7a2a3ed973c7be5934dcd1c803148f890bf7be044bdafffc6a37a8138269a` |
| `docs/audit/rs_block_moment_bridge.md` | `205e99200cf09361563f850886409042fd6b6c4599fcb592cbf6f7a885ac9918` |
| `verify/rs_block_moment_bridge_exact.py` | `87303ae07633c1402a83ea31845eaaacd9daab3172cc1841b78e57b54a72adc8` |
| `verify/rs_block_moment_bridge_exact.out` | `4735ec2bb4334b0eecf172e0bc662df7dc0d29859ff7bc6392120806ac7f5b4a` |

This gate discharges only finite centering and the raw-to-centered limit adapter.
`UncenteredRSBlockLimits`, both complex-alias clauses, and the underlying analytic
RS-to-actual-block derivation remain unproved.  No `BlockMomentLimits` instance constructed; no
frozen rung status changes.

## 36. A2 R1a allocation-capacity no-go gate

**Lean gate:** `PrintAxioms/R1aAllocationNoGo.lean`.  **Axioms:** 7 theorems, standard three.
**Verifier:** `verify/r1a_allocation_nogo.py` (integer + `Fraction`).

The capacity module proves two exact active-cell profile caps, abstract finite contradiction, and
both frozen rational gaps.  The NoGo module derives every finite hypothesis from
`PrincipalCyclicBlock` fields using almost-everywhere reconstruction, exact full-profile scaling,
distinguished energy-ratio limit, and degree-one zero-shift translated-product limit.  It proves
`no_principal14999` and `no_principal19999` for arbitrary `ZeroConfig` and every value of the
corresponding exact family type.  The Python verifier reconstructs both profile integrals, active
edges, Bernstein-basis monotonicity certificates, capacity sides, and strict gaps from raw
polynomial and frozen family constants.

| File | SHA-256 |
|------|---------|
| `Discharge/R1aAllocationCapacity.lean` | `c5d5d0f8fd939a97477189ceedeef0d3af112894b246bbe44fe377cad393c6d2` |
| `Discharge/R1aAllocationNoGo.lean` | `7a53acb3a61e1af357a10dab696e70a472b321400a325ca553d423b33c5737db` |
| `PrintAxioms/R1aAllocationNoGo.lean` | `368a1907abcbcb0ba6c874ddb218fa3df4e9663dfc0352dee4fef9bb3ae1953e` |
| `docs/audit/r1a_allocation_nogo.md` | `03454e0c3ba7dee4037e658836299459c4a91c03ea1f7921d51a6421a209f4fc` |
| `verify/r1a_allocation_nogo.py` | `866b8275b81b6bc49ea63b2d6fb60a7df4335a0a45fcd13f206e6f95cda47143` |
| `verify/r1a_allocation_nogo.out` | `ea2d1f902975651b6b23c58195568401f9e2f9e14bb72bc17be52ce525c1fc96` |

This gate does not change any frozen theorem statement or constant.  Quartic theorem declarations
remain conditional implications, but their current `PrincipalCyclicBlock` premise is formally
uninhabited for both exact family types.  No valid current-interface construction exists.

## 37. B-4 eta-superposition support-model gate

**Lean gate:** `PrintAxioms/EtaSuperpositionObstruction.lean`.  **Axioms:** 12 theorems, standard
three.  **Verifier:** `verify/b4_eta_superposition_obstruction.py` (integer + `Fraction`).

The Lean module proves generic no-supported-divisor convolution lemma, scale-free prime-square
specialization, and concrete eta=3/4, T=625, n=899 regression.  The balanced [25,50] box model has
coefficient two at 899, whereas every finite signed superposition with all first supports in [5,10]
vanishes there.  It also proves the retained balanced positive progression majorant misses trace by
exactly eta in PQ and eta - 1/2 in PH.  The Python verifier enumerates all ordered divisors of 899,
reconstructs three exact boxes and both supported-pair lists, and recomputes PQ and PH excesses.  It
does not verify a logarithmic budget; the cited C<1 threshold is from existing
`LogBudget`/`EtaClosure` theorems.

| File | SHA-256 |
|------|---------|
| `Discharge/EtaSuperpositionObstruction.lean` | `5d21ff3339fa654268dd84821ddc1dacd67320b6d75e6bb217fb9dd8e4cfd73c` |
| `PrintAxioms/EtaSuperpositionObstruction.lean` | `06f6d413afbf765dae6e40c6a919192f779fa7187e6613ac50919d6146b29570` |
| `docs/audit/eta_superposition_obstruction.md` | `d4ed1194ea882921581ee3e08f2430df1aa4e451fd1cff1c2f9f3206a8fac9cd` |
| `verify/b4_eta_superposition_obstruction.py` | `343f2a70ae558f83be9529b3f5864478b5245ad6326fdaaee9717ecf9055a965` |
| `verify/b4_eta_superposition_obstruction.out` | `373ba96868de9bc757c0d181d1e2f23d8f88a1361b80b0a0cf835f1616ee678d` |

This gate does not identify the model coefficient with an actual terminal Heath--Brown coefficient,
kill (EF_eta), or assert (HD_eta).  The exact survivor remains |R_HD(Y,T,eta)| << Y(log T)^C with
C<1, after signed h-sum and actual zero-mode subtraction before outer dyadic Y-sum.  A1 and every
frozen-rung status remain unchanged.
