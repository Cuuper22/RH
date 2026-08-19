# VALIDATION.md -- build and audit record for the 85 % layer

Environment: Linux x86-64, Lean `v4.33.0-rc2` (via `elan`), Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` (pinned in `lake-manifest.json`). Base commit: `3635e74`.

---

## Table of contents

1. [Build](#1-build)
2. [`sorry` audit](#2-sorry-audit)
3. [`axiom` audit](#3-axiom-audit)
4. [Base repository unchanged](#4-the-base-repository-is-unchanged)
5. [Conditional axiom audit](#5-the-conditional-topics-axiom-audit)
6. [Statement equality](#6-statement-equality-challenge--solution)
7. [Deviation declaration](#7-deviation-from-base-comparator-conventions-declared)
8. [Numerical cross-checks](#8-numerical-cross-checks-performed-outside-lean)
9. [Phase 0b inventory](#9-phase-0b-inventory-and-status-validation)
10. [Phase 0d CI](#10-phase-0d-ci-configuration) | 11. [A1.1 exponent](#11-a11-exact-exponent-audit) | 12. [A1.2 cross-scale](#12-a12-cross-scale-audit)
13. [B-2 RS source](#13-b-2-rudnicksarnak-source-audit) | 14. [B-1 stability](#14-b-1-stability-proof) | 15. [A1.3 exponent](#15-a13-exact-exponent-audit)
16. [A2.1 rank/profile](#16-a21-common-lattice-rank-and-profile-audit) | 17. [A2.2 normalization](#17-a22-normalization-and-corrected-tail-audit) | 18. [B-3 certificate](#18-b-3-terminal-certificate-layer)
19. [B-4 eta closure](#19-b-4-eta--12-factorization-audit) | 20. [Robust stability](#20-phase-c-robust-stability-and-spectral-normalization) | 21. [Inputs95](#21-phase-c-inputs95-boundary)
22. [Quartic transfer](#22-phase-c-quartic-transfer-and-conditional-headlines) | 23. [HB depth-four](#23-a1-exact-depth-four-heathbrown-coefficient-layer) | 24. [BBLR gcd](#24-a1-bblr-gcd-allocation-and-finite-coefficient-collapse)
25. [Smooth grouping](#25-a1-fixed-asymmetric-smooth-grouping-method-class) | 26. [Actual-scale BBLR](#26-a1-actual-scale-bblr-positive-majorant-method-classes) | 27. [RS pair-integral](#27-b-2-rs-pair-integral-and-compact-support-gate)
28. [Pre-majorant DI](#28-a1-pre-majorant-di-one-shot-gates) | 29. [Four-Mobius-slot](#29-a1-four-mobius-slot-exponent-and-method-class-gates) | 30. [SQ4 routes](#30-a1-simultaneous-sq4-route-gates)
31. [SQ4 Gauss-transform](#31-a1-sq4-finite-gauss-transform-and-inversion-gates) | 32. [SQ4 CRT/conductor](#32-a1-sq4-crtconductor-and-shared-gcd-gates) | 33. [SQ4 correlated](#33-a1-sq4-correlated-moment-and-published-family-gates)
34. [SQ4 literature](#34-a1-sq4-published-literature-gate) | 35. [RS block bridge](#35-b-2-actual-block-centering-bridge-gate) | 36. [R1a no-go](#36-a2-r1a-allocation-capacity-no-go-gate)
37. [Eta-superposition](#37-b-4-eta-superposition-support-model-gate)

---

## Summary gate table

"Standard three" = `[propext, Classical.choice, Quot.sound]`.

| # | Section | What was checked | Result |
|---|---------|-----------------|--------|
| 1 | Build | `lake build` full repo | Zero errors |
| 2 | `sorry` audit | `grep -rn sorry` | Clean (prose only) |
| 3 | `axiom` audit | `grep -rn ^axiom` | 4 in `Hypotheses.lean` |
| 4 | Base repo | Base `PrintAxioms` (43 lines) | Standard three only |
| 5 | Conditional audit | `PrintAxioms/Zeta85` (8 lines) | Expected axiom sets |
| 6 | Statement equality | Type diff (challenge vs solution) | Identical |
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
| 29 | Four-Mobius-slot | Lean (13 thms) + Python | 12 std three + 1 reduced |
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

`lake build` covers `defaultTargets = ["Zeta23", "RH"]`; the `RH` library is the conditional 85 % layer (`lakefile.toml`). **Zero errors.** Warnings are pre-existing Mathlib deprecation notices (`Set.mem_setOf_eq`, `MeasureTheory.integral_finset_sum`) plus unused-variable hints; none originate in `RH/`.

## 2. `sorry` audit

```
$ grep -rn "sorry" --include=*.lean Zeta23/ RH/ comparator/ | grep -v "^comparator/Challenge"
Zeta23/FromPNTPlus/Mertens.lean:31,32     (prose in a module docstring)
Zeta23/FromPNTPlus/StrongPNTPrefix.lean:4 (prose in a module docstring)
comparator/PrintAxioms.lean:10            (prose in a module docstring)
RH/Zeta85/Discharge/SignedShift.lean:10   (prose in a module docstring: "no axioms, no `sorry`")
```

No `sorry` in any proof under `Zeta23/` or `RH/`. The only proof-level `sorry`s are the deliberate ones in the trusted challenge files -- `comparator/Challenge.lean`, `comparator/Challenge/Multiplicity.lean`, `comparator/Challenge/XiPrime.lean` and `comparator/Challenge/Zeta85.lean` (8 of them, one per statement), exactly as the base repository does.

## 3. `axiom` audit

```
$ grep -rn "^axiom " --include=*.lean Zeta23/ RH/ comparator/
RH/Zeta85/Hypotheses.lean:186  axiom shiu_majorant2 : ...
RH/Zeta85/Hypotheses.lean:220  axiom signedPair_traceGrade_lt_5_4 : ...
RH/Zeta85/Hypotheses.lean:269  axiom signedPair_traceGrade_lt_3_2 : ...
RH/Zeta85/Hypotheses.lean:340  axiom traceTransfer_saturated : ...
```

Four legacy declarations, all in `RH/Zeta85/Hypotheses.lean`. The former `windowCost_101`, `windowCost_125`, `bblr_poisson_blocks`, and `bblr_error_bound` are now proved theorems in `RH/Zeta85/Discharge/`. `shiu_majorant2` asserts the corrected interface `ShiuMajorant2` (`RH/Zeta85/ShiuInterface.lean`); the frozen `ShiuMajorant` it replaces is refuted in-repo by `RH.Zeta85.not_shiuMajorant_quarter` (`RH/Zeta85/Discharge/ShiuNoGo.lean`) -- see `AXIOMS.md` S3, Axiom 1. These four remain the conditional boundary, not the target standard. (The two `axiom` lines in `Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean` sit inside a docstring code block and are not declarations -- recorded in `AUDIT.md`.)

## 4. The base repository is unchanged

`lake env lean` on `comparator/PrintAxioms.lean`, `PrintAxioms/Multiplicity.lean`, `PrintAxioms/XiPrime.lean`, and `PrintAxioms/PairCeiling.lean` produces 43 lines. Every line of the first three reads `'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`; `PairCeiling` reports `LawN256_check` depends on `[propext]` and `LawN256_edge` depends on no axioms. No base theorem acquired a new axiom: nothing under `Zeta23/` imports anything under `RH/`.

## 5. The conditional topic's axiom audit

`lake env lean comparator/PrintAxioms/Zeta85.lean` produces eight lines (reproduced in `AXIOMS.md` S1). Support-`101/100` and support-`5/4` statements depend on `{signedPair_traceGrade_lt_5_4, traceTransfer_saturated}` plus the standard three; the 85 % statements use `{shiu_majorant2, signedPair_traceGrade_lt_3_2, traceTransfer_saturated}` plus the standard three. Nothing else appears.

An intermediate revision had collapsed the axiom list to the single refuted `shiu_majorant` and added eight `False`-elimination headlines. Those are removed; the audit is back to the eight genuine statements with distinct per-rung dependency sets (rungs 1-2 versus rung 3 -- `AXIOMS.md` S2).

## 6. Statement equality, challenge / solution

The `comparator` binary, `landrun` and `lean4export` are **not available** (no outbound GitHub access). The full comparator run is *not executed*; the command is:

```bash
lake exe cache get
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator/.lake/build/bin/comparator comparator/config-zeta85.json'
```

with `comparator/config-zeta85.json` listing the four `RH.Zeta85.Hypotheses` axioms in `permitted_axioms` alongside the standard three (see S7). What **was** executed: `lake build Solution.Zeta85` plus the axiom audit above, and a mechanical statement-equality check:

```
$ diff <(lake env lean /tmp/tychal.lean | grep -v "declaration uses") \
       <(lake env lean /tmp/tysol.lean)    # no output -- STATEMENT TYPES IDENTICAL
```

with `set_option pp.numericTypes true`. Elaborated types coincide on both sides. This checks statement-equality only; it does **not** substitute for the export + kernel-replay half, which requires the missing tooling.

## 7. Deviation from base comparator conventions, declared

`comparator/README.md`, rule (5): *a statement enters a challenge file only when the Zeta23 theorem it delegates to is sorry-free with `#print axioms` = the standard three.*

Topic `Zeta85` **deviates** from rule (5): its theorems are conditional on the four named axioms, and `comparator/config-zeta85.json` lists those axioms in `permitted_axioms`. This is the only such topic; the base files and topics `Multiplicity`/`XiPrime` are untouched. A reader auditing the 85 % claim must read `RH/Zeta85/Hypotheses.lean` in addition to `comparator/Challenge/Zeta85.lean`. The exception is a current deficiency to discharge, not an accepted endpoint.

## 8. Numerical cross-checks performed outside Lean

Recorded in `FINDINGS.md` S4 (exact-rational verification of the Phase-A certificate chain, and double-precision verification of two source transcendental window costs). The Phase-A chain is *also* proved inside Lean; its external check is corroboration only. Both frozen lower-rung targets now have different exact rational witnesses proved in Lean.

## 9. Phase 0b inventory and status validation

Four logical source batches inventoried in `docs/run/MANIFEST.md` (byte size, SHA-256 digest, role per file). Exact terminal filenames required by the intake gate are present. The 100% terminal claim was checked independently with mpmath at 50 and 80 decimal digits plus exact rational arithmetic in `verify/withdrawn_100_claim.py` (output: `verify/withdrawn_100_claim.out`). The calculation proves the endpoint contradiction and shows the handoff's M2 <= 0.3144 bound does not follow from the pointwise cone, so it remains an explicit missing-condition finding. This milestone changes documentation, archives, and verification artifacts only; it does not constitute the Phase 0c build, comparator, or `#print axioms` rerun.

---

## Convention for sections 10-37

Each gate runs (unless noted): `lake build <Module> RH.Zeta85.Main`, `lake env lean comparator/PrintAxioms/<Module>.lean`, `bash verify/check_axioms.sh`. Python verifiers replay byte-for-byte. Unless stated otherwise: all printed theorems depend exactly on `[propext, Classical.choice, Quot.sound]` ("standard three"); source scans find no `axiom`/`sorry`/`admit`/`unsafe`; `RH.Zeta85.Main` imports the module; no frozen rung status changes; no A1 field is discharged. All gates exit zero. Deviations are stated explicitly.

---

## 10. Phase 0d CI configuration

CI workflow (`.github/workflows/ci.yml`) runs `lake exe cache get`, `lake build Zeta23 RH.Zeta85.Main Solution Solution.Multiplicity Solution.XiPrime Solution.Zeta85`, `bash verify/check_axioms.sh`. The script extracts 44 expected lines for eight Zeta85 headlines from `AXIOMS.md` SS1.1-1.3, diffs against fresh output, runs four base `PrintAxioms` audits, and scans for `sorry`/`admit` outside challenge files. GitHub-hosted run is authoritative (shell initially lacked Lean; Phase 0c DigitalOcean reproduction waived). Harness repaired at `810353e` (stability docs after import; all `Solution*` built before audit); both exit zero.

## 11. A1.1 exact exponent audit

**Verifier:** `verify/a1_1_method_kill.py` (exact `Fraction`; output `.out`). Recomputes Phase A1.1 scales: P=HQ, Q=P^{50/93}, PQ=T^{143/100}; Nguyen+Parseval/Cauchy exponent 3917/2400 (excess 97/480); Parry+Parseval exponent 261/160 (excess 161/800); Parry 4/7 range margin 22/651, Wei--Xue--Zhang deficit 1951/54312; natural-order variance+Cauchy zero power margin; literal C=0 log exponent 2 < trace-normalization 3. Premises checked against `docs/audit/log_budget_routes.md` Route 5. No Lean change; no axiom or `Inputs95` field added.

## 12. A1.2 cross-scale audit

**Verifier:** `verify/a1_2_cross_scale.py` (exact `Fraction`; output `.out`). Asserts P=T^{93/100}, Q=T^{1/2}, PQ=T^{143/100}=Y, PH=T^{34/25} with exact power saving T^{-7/100}; at forced C=3, dyadic summation log exponent 5, cross-Y recombination 4, budget 3, equation (6) misses by one log power; five-block aligned family attains sum of five individual bounds. Last statement generalized in Lean (`blockwise_triangle_sharp`); forced-exponent failure is `crossScale_recombination_fails`. No analytic input or new field. The requested historical signed-prime experiment could not be reproduced (no generating script in archives or Drive intake).

## 13. B-2 Rudnick--Sarnak source audit

**Source:** `docs/audit/rs_reduction.md` checked against Rudnick--Sarnak (1996) primary PDF (SHA-256 `83010c4f68efc5f5628a71a589ff3a374220b25902384e9c1a34b3d6cd0834d6`). Records Theorem 3.1 (unconditional at m=1), Theorem 3.2 (RH hypothesis), Lemmas 4.2-4.3, cyclic symbol, flat contractions, weighted specialization to formula (18), corrected source map.

**Gate:** 9 theorems, standard three. `RSReduction.lean` proves zero-frequency cyclic-symbol identity, zero-sum contraction vectors, exact 0,1,3,6+3 pairing enumeration, formula-(27)-to-(18) centering, top-hat formula-(18)-to-(21) specialization. This alone was not the R1b discharge. `RSPairIntegrals.lean` (S27) later identifies `normalizedRSMainTerm` with uncentered contraction for continuous compactly supported profiles, but no theorem transfers it to the actual principal block. Remaining: cyclic-symbol admissibility, published-field instance, height smoothing, log-T normalization, off-RH complex Poisson, k=3,4 finite-grid/end estimates (`FINDINGS.md` S16, `rs_reduction.md` S9).

## 14. B-1 stability proof

**Gate:** 5 theorems (stability + compression headlines), standard three. No new field or primitive declaration. GitHub workflow is the authoritative build.

## 15. A1.3 exact exponent audit

**Verifier:** `verify/a1_3_wg_hb.py` (exact `Fraction`; output `.out`). Constructs (not hard-codes) two Bettin--Chandee exponents from L^2-norm and bracket factors; checks candidate simultaneous-dispersion saving 7/200 and net saving 7/400; fixed-Weil excess 9/50; BBLR endpoint excesses; Blomer--Pascadi range gap 83/300; Milicevic--Qin--Wu gaps 141/250 and 47/100. Matching identities in `RH/Zeta85/Discharge/LogBudget.lean`. Validates method-class audit only; does not add missing analytic estimate.

## 16. A2.1 common-lattice rank and profile audit

**Verifier:** `verify/a2_1_tdac_rank.py` (exact `Fraction` intervals + 90-decimal integer-sqrt enclosures + rational Taylor remainders; output `.out`). Reconstructs A, B, M, endpoint, edge margin from terminal file 24 eqs (28)-(29); no constant hard-coded. 60- and 100-decimal `mpmath` agree beyond 55 places. Certifies residual margins >1/1000, >1/1000, >1/10 for R-9506, R-8686, file-15 Euler repair; checks three rank deficits; derives edge residual `42756493/1031000000 > 0` and central average `1157918831/1031000000 > 1` (prevents false zero-row obstruction).

**Lean:** 9 theorems, standard three. Proves outer-product channel rank bound, full diagonal rank, critical-count contradiction, full-minus-distinguished formulation, three terminal integer count corollaries. Two Euler-profile nonvanishing premises remain in interval verifier. Formalizes algebraic method-class impossibility without analytic input.

## 17. A2.2 normalization and corrected-tail audit

**Verifier:** `verify/a2_2_alias_free_scaling.py` (exact `Fraction`; output `.out`). Derives A=1031/1200, sup V_sigma=1200/1031<143/100; recomputes saturated quadratic costs at 143/100, 1.499999, 1.4999, 1.9999, endpoint 2; reconstructs closed moments M_2, M_3, M_4; inverts 5-node Vandermonde (det 99/500000), checks weights >1/25; exact moment equality through degree 4 and support gap 2/5<sigma-1; 55-digit tensor Gauss--Legendre quadrature of formula (18), max discrepancy <2e-56.

**Lean:** Standard three. `AliasFallback.lean` has no placeholder or primitive assumption. Validates finite rational countermodel conditional on paper-derived moments; does not formalize Mathlib integral equality, RS bridge to formula (18), principal-block input, or alter a frozen rung.

## 18. B-3 terminal certificate layer

**Verifiers:** `b3_certificate_audit.py` (exact rational arithmetic for moments, dual-polynomial signs, Bernstein positivity, window-cost integrations; `mpmath` is calibration only) and `b3_r9383_exact_endpoint.py` (integer + `Fraction`: rational Taylor, integer-sqrt bounds, interval AD isolate flat endpoint in [0.9383133270509488847, 0.9383133270509488848], below frozen R-9383).

| File | SHA-256 |
|------|---------|
| `verify/b3_certificate_audit.py` | `2f264e6637de2ec09ef5eae93f9f1368eb9a3c6ad0ea2e0c4b05c084f125ceab` |
| `verify/b3_certificate_audit.out` | `f34b7ca98bebe570140778d1d7341f04ad3191c199153bbecffe17528d2eb130` |
| `verify/b3_r9383_exact_endpoint.py` | `3b01ca20b4c0b4ce54ac067050998796852be8417df57a204aa5ab20bc5b77ab` |
| `verify/b3_r9383_exact_endpoint.out` | `aa8b584aaf771b15ea0b1aeea18df69b29dd4563b6246fa25cd0eda7b861aaad` |

**Lean:** Builds `QuarticWindowWitnesses`, `R9383ExactEndpoint`, `TopHatMoments`, `TrimmedMoment`; 4 isolated printers, all standard three. `crossingReduction` proves determinant-one change of variables, support-intersection, four-quadrant reduction; `formula21M4Integral_eq` proves formula-(21) fourth moment without field or premise. R-8686/R-9506 implications do not instantiate A1/R1a/R1b bridges; no quartic headline at this gate alone (Phase-C transfer in S22 assembles conditionals).

## 19. B-4 `eta > 1/2` factorization audit

**Gate:** 14 theorems, standard three. **Verifier:** `b4_eta_closure.py` (exact `Fraction`).
At eta=3/4: verifies legal depth-three j=2 block, exhausts whole-variable groupings, checks unavailable M1 exponent, recomputes both balanced-block power excesses, positive preliminary margin, literal C<1 threshold. Establishes unconditional exponent and method-class audit only; does not assert (EF_eta).

| File | SHA-256 |
|------|---------|
| `verify/b4_eta_closure.py` | `b934eab4fc22da185cda8a1bc2e11a10cdda3449b1479c435902d681997f008f` |
| `verify/b4_eta_closure.out` | `441e426de1218676e6cf322f2971c8d403d9fd439d0f5973ac000ace9e3568b3` |

## 20. Phase-C robust stability and spectral normalization

**Gate:** Standard three. **Verifier:** `robust_stability.py` (integer + `Fraction`).
Independently expands finite prebound, checks error vector (2,4,1,2) and exact count slack, evaluates three rational substitutions, checks sorted-head cardinality, removed mass, residual identities on finite spectra. Lean proves finite prebound, base/isometric/principal robust inequalities, uniform trim, exact residual identity, four-moment adapter. No analytic moment equality or limiting statement asserted; robust-stability alone discharges no analytic premise (conditional assembly in S22).

| File | SHA-256 |
|------|---------|
| `verify/robust_stability.py` | `8510ca4748e26e9310c3f89a5df1ef95d5f015761bec86f41b8e545fd04454bc` |
| `verify/robust_stability.out` | `8d2cf177b0104dc0872591fde5da73f950415b56b185ed68917451d90931117b` |

## 21. Phase-C `Inputs95` boundary

**Gate:** 6 theorems (`profileSaturatedCost_v8686/v9506`, `G_eq_A_add_E`, `block_isHermitian`, `core_count_le_dyadic_add_edge`, `robustBlockTailBound_eventually`), all standard three. Family types contain exact B-3 profiles; matrix definitions use actual full zero sum and finite `ZIprime` truncation; robust adapter concludes on literal principal block. No `Inputs95` instance or constructor exists. Validates hypothesis boundary and adapters; conditional headline gate is S22.

## 22. Phase-C quartic transfer and conditional headlines

**Gate:** 21 transfer + 8 headline theorems, all standard three. **Verifier:** `quartic_transfer.py` (exact `Fraction`). Checks edge identity 2+(1-cap/2)+cap/2=3, fixed-point quotient identities, strict frozen-target margins, monotone comparisons R-8657<R-8686 and R-9383<R-9506.

`QuarticTransfer` proves spectral-moment identity, exact finite dual scaling, edge coefficient three, NII=o(N), normalized limit, generic epsilon transfer, four zeta specializations; R-8686/R-9506 direct with strict margins, R-8657 monotone from R-8686, R-9383 from R-9506. `QuarticMain` exposes `rung{8657,8686,9383,9506}` and `rung{...}_cumulative` (eight statements), each taking `FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, `BlockMomentLimits`. No instance of the four analytic structures is constructed; audit confirms standard-three footprint only.

| File | SHA-256 |
|------|---------|
| `verify/quartic_transfer.py` | `dc99b510fdf1966f11535bf57a3dc53f4056c679e0275c8a649c01facf5f3bdf` |
| `verify/quartic_transfer.out` | `05615d7eb1727532cb81a5c04598630ebd9c29408b729770d34e4b282b533cce` |

## 23. A1 exact depth-four Heath--Brown coefficient layer

**Gate:** 29 theorems, standard three. No numeric verifier (no calibrated numerical claim).

Proves exact four-term sharp-cutoff identity through n<=Z^4, eight-slot grouping factorization, exact d_1 d_2=d_3 d_4=d coefficient sums, triangle majorants, dyadic support, (j,d,l,p,q) indexing, residue-cell centering, reduced-residue mean with signed four-component sum (each zero), countermodels showing all-class mean cannot replace reduced mean and centering alone cannot imply singular-series main term. Planned floor blocks not claimed as source partition; neither mean claimed as BBLR l=0 term. Printer is dependency audit, not comparator. No theorem identifies these with run 12's smooth c/e/F, evaluates l=0 integrals vs Ramanujan series, or proves an A1 estimate. Boundary: `docs/audit/hb_depth_four_coefficients.md`.

## 24. A1 BBLR gcd allocation and finite coefficient collapse

**Gate:** 5 theorems, standard three. **Verifier:** `bblr_gcd_allocation.py` (exact replay).
Proves positive-d canonical allocation equivalence, both inverse identities, reduced-product coprimality and converse gcd formula, filtered one-side coefficient collapse (multiplicity one), two-sided finite-kernel reindexing. At d=p=2: canonical unit coefficient has 3 terms, unfiltered raw split has 4. Validates finite source collapse only; does not construct smooth signed HB grouping, prove (EDB)/(WG-HB), or evaluate l=0 integrals. Boundary: `docs/audit/bblr_gcd_allocation.md`.

## 25. A1 fixed asymmetric smooth-grouping method class

**Gate:** 15 theorems, standard three. **Verifier:** `a1_smooth_grouping.py` (exact `Fraction`).
Lean checks j=1 component inventory/scalar, proves truncated Mobius atoms not coefficient-one slots, verifies terminal exponent block, proves fixed left/right/two-sided slot assignments impossible below exact gaps, proves collapsing two coefficient-one slots creates zeta*zeta not a BBLR smooth variable. Python checks signed coefficient, Mobius/coefficient-one distinction at (2), exponent identities/gaps, divisor multiplicities at (2)/(4). Validates killed fixed-scale literal-slot class only.

| File | SHA-256 |
|------|---------|
| `verify/a1_smooth_grouping.py` | `67550b74daf9ae0ed31ad37729fbf35ba52a64ddd245a2860ada0da65df42793` |
| `verify/a1_smooth_grouping.out` | `fd1fa689b25c6dfdc9545b6bf248cd9079126b8c07ad681ece66262cb1f8c5bb` |

## 26. A1 actual-scale BBLR positive-majorant method classes

**Gate:** 13 theorems, standard three. **Verifier:** `a1_actual_scale_bblr.py` (exact `Fraction`).
Proves exact actual-block geometry, both BBLR Prop 3.1 error exponents and positive excesses, eq (14) Fourier scale and frequency-cutoff cancellation, exact d=1 progression lengths, PQ obstruction, harmless PH/H^2 terms. Validates failure of direct Prop 3.1 and run-12 progression majorant on exact symmetric block only; does not bound signed remainder or exclude pre-majorant coefficient cancellation.

| File | SHA-256 |
|------|---------|
| `verify/a1_actual_scale_bblr.py` | `e7c25c211113adc8a0ab51a7e348073f6c4ffacb96ae05785f9d16199d3adb2a` |
| `verify/a1_actual_scale_bblr.out` | `5c0514d743c30ae1b1d89420bb4ff295c01534031d41e2f004b176dcb7f00c42` |

## 27. B-2 RS pair-integral and compact-support gate

**Gate:** 51 theorems, standard three. **Verifier:** `rs_pair_integrals_exact.py` (exact replay).
Proves all one-pair and two-pair contractions through degree four, exact normalization, wrappers deriving kernel integrability from `0<mu`, `Continuous r`, `HasCompactSupport r`. Python enumerates pairing counts, partial-sum profiles, raw/normalized scaling powers. Discharges internal RS main-term evaluation only; does not construct `BlockMomentLimits`, instantiate theorem-3.1 field, or discharge cyclic-symbol admissibility, height smoothing, log-T vs ell(T), complex Poisson, degree-3/4 finite-grid/end, or principal-block identification.

| File | SHA-256 |
|------|---------|
| `verify/rs_pair_integrals_exact.py` | `04b2a386bd83f19c39307ddf4b7ea36ffc62802f924efcf1d53292d5aa929833` |
| `verify/rs_pair_integrals_exact.out` | `e090227f8f2768c2a75771ce9ac2fc157e45b1650e09f901530f0a76ab48f4f2` |

## 28. A1 pre-majorant DI one-shot gates

**Gate:** 15 theorems, standard three. **Verifier:** `a1_premajorant_di.py` (exact `Fraction`).
Proves exact source scales, collapsed coefficient norm exponent, three Drappeau K^2 exponents, direct integrated exponent 179/100 with 9/25 excess over trace, finite Z/5Z inverse mismatch, candidate Pascadi factor arithmetic (explicitly conditional). Two conclusions: direct collapsed Drappeau class power-killed at 179/100; literal completed r=a Pascadi map structurally inapplicable. (q,a)-dependent reindex with separate k=0 treatment remains open.

| File | SHA-256 |
|------|---------|
| `verify/a1_premajorant_di.py` | `1901eda16d2824e1692c1639eccf120d24cd40c1ddefbf631a55fccbb776db2b` |
| `verify/a1_premajorant_di.out` | `0d95711e582c826ff0227daef45bd2bbf73885723d189f43283a06eb9a27756a` |

## 29. A1 four-Mobius-slot exponent and method-class gates

**Gate:** 13 theorems; 12 standard three, 1 (`source_modulus_not_prime`) at `[propext, Quot.sound]` only (`check_axioms.sh` records it separately). **Verifier:** `a1_four_mu_kloosterman.py` (exact `Fraction`).
Proves seven retained scales, composite-modulus obstruction, killed one-sided fixed-modulus/sqrt/triangle output, surviving simultaneous candidate arithmetic. Python checks fixed-x/integrated targets, 49/200 one-sided misses, 149/100 and 63/50 simultaneous exponents, 17/400+17/400 strict loss, normalized/raw long-log exponents 0/2. Simultaneous estimate (SQ4-HB) and smooth source identity remain unproved.

| File | SHA-256 |
|------|---------|
| `Discharge/FourMuKloosterman.lean` | `bc67127847ef877cf3d615a747df83e60da2fa7a046c0ed8ed372d18ca23601c` |
| `PrintAxioms/FourMuKloosterman.lean` | `33a45b0dfa795ee0a88457710b50df1f9129a30e0e85b8905e4ef692e7476968` |
| `docs/audit/four_mu_kloosterman.md` | `f3c697d60b70f32abb22748f7dd28219c2e656fc0efeaa5fd61d7af560436901` |
| `verify/a1_four_mu_kloosterman.py` | `a8eb4b39fb9215c0af8b45449a036c8cee4c434a0906c3a9f6a55742e1146594` |
| `verify/a1_four_mu_kloosterman.out` | `3c1abc99cb74c993323371b23ed806dad68ad76fc0472a665cb989a1f11e6977` |

## 30. A1 simultaneous SQ4 route gates

**Gate:** 13 theorems, standard three. **Verifier:** `a1_sq4_simultaneous_routes.py` (exact `Fraction`).
Proves exact source scales; fixed-x and integrated outputs/excesses of character-large-sieve, coefficient-uniform norm-only, additive-large-sieve, Poisson zero-mode, Poisson-Weil/triangle; reciprocal profile, completion prefactor, dual length; normalized/raw log exponents 0/2. No analytic estimate stated. Python checks all outputs/excesses, profile/truncation scales, nonzero loss T^{eta+epsilon} (0<eta<2/5), six route labels. Structural-applicability verdicts source-audited in `docs/audit/sq4_simultaneous_routes.md`. Makes Poisson zero mode power-safe; (SQ4-HB), nonzero family (33), smooth source identity, correlated estimate remain open.

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4SimultaneousRoutes.lean` | `3ff0acf59b6a0f828f5d0e00fe8af3a4ef9225a8d3456f3877f2193b1c52c661` |
| `PrintAxioms/SQ4SimultaneousRoutes.lean` | `eaa5e835a79bdcfe051811a8c9d8e690ca5d6fbe1895fbf973909c9470da910b` |
| `docs/audit/sq4_simultaneous_routes.md` | `c87497add008c3113efb23528c07df9f39f45c8867278209f7f3fe49008c08c5` |
| `verify/a1_sq4_simultaneous_routes.py` | `fe11015425ec5312fd1894144ff17b6bcb8cfd303735c5774068e8554c04cd6a` |
| `verify/a1_sq4_simultaneous_routes.out` | `ece3e6a0dd1de6ba8100c90e2d59ba1caf4af77de6ea72283b0acf79945932b8` |

## 31. A1 SQ4 finite Gauss-transform and inversion gates

**Gate:** 6 theorems, standard three. **Verifier:** `a1_sq4_gauss_square_transform.py` (exact `Fraction`).
Proves abstract correlation transform, shifted Gauss-sum products for arbitrary residues, unit-shift scaling, Gauss-square specialization, Dirichlet-character Fourier inversion (all positive moduli including composite), Kloosterman-kernel character inversion. Python reconstructs source scales, completion exponent -43/100, (SQ4-HB) target 48/25 (log exp 0), weaker target 209/100, coefficient-blind output 121/50 (misses by 1/2 and 33/100), raw log exponent 2. Unresolved: equation (14) of `docs/audit/sq4_gauss_square_transform.md` (all four Mobius factors, shifted Gauss products on nonunit conductor/gcd strata, varying composite modulus).

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4GaussSquareTransform.lean` | `1c58791ca5d3f2f2879c6e5e6ae60ebb3b9efd9b1f9c0ae90ae1c73aa72dc3e5` |
| `PrintAxioms/SQ4GaussSquareTransform.lean` | `99359bb5bc9cd5de16edac3cf369deed8def95e8b4129dd18dae8ef58d8e2db2` |
| `docs/audit/sq4_gauss_square_transform.md` | `03a629e8e1c522c8f84766b4f06e49d9ef5fb8154fa5564d617eb545533a1dac` |
| `verify/a1_sq4_gauss_square_transform.py` | `387225f5f613fcf79be7412f308f2859b255eefade6237ed2ddfd3432e337981` |
| `verify/a1_sq4_gauss_square_transform.out` | `89168a2503baea412b3bc96b465ff7f7335ac700f41e23ddbe6190cb63d718d0` |

## 32. A1 SQ4 CRT/conductor and shared-gcd gates

**Gate:** 31 theorems (from 38 declarations), standard three. **Verifier:** `a1_sq4_crt_conductor.py` (integer polynomial in Q[x]/Phi_q(x)).
Proves coprime CRT factorization with complementary-modulus twists, nonunit-shift conductor support, complex primitive-`changeLevel` imprimitive Gauss formula (divisor-d and -s coordinates), inverse-to-conjugate phase, unit-supported formula, squarefree shared-gcd decomposition, Mobius-sign cancellation, minimal Z/4Z false-CRT counterexample. Python calibrates 3,336 imprimitive identities, checks 1,208 conductor-support instances, enumerates 3,721 squarefree shared-gcd strata; general nonreal conjugation phase proved by Lean only. Also verifies 48/25-43/100=149/100 and 121/50-48/25=1/2. Target remains |M_4(T,x)| << T^{48/25+epsilon} (log T)^0 with all Mobius factors and shared conductor/divisor coupling before Cauchy; smooth source bridge is separate blocker.

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4CRTConductor.lean` | `7e42a5cdad131001fdc411d66229f5aa845a63da42b92334579f0e309853b2b3` |
| `PrintAxioms/SQ4CRTConductor.lean` | `217ff71194a7769b45be368239db747f37627ab061054a26f57795423342f8cd` |
| `docs/audit/sq4_crt_conductor_strata.md` | `47a4f858b284e2106051d6dc5a3ef1d50a1aed27ce89730bda27dd9d6d0181ea` |
| `verify/a1_sq4_crt_conductor.py` | `43291f853513881dfba2aa432a59993364257be3756f406bf00c2ac5d62bf02f` |
| `verify/a1_sq4_crt_conductor.out` | `78ed2cedad32d5ebd348aaa034f98bda5676804ab9691b7cb963752eceeb24e1` |

## 33. A1 SQ4 correlated-moment and published-family gates

**Gate:** 15 theorems, standard three. **Verifier:** `a1_sq4_correlated_moment.py` (exact `Fraction`).
Proves exact scales, fixed/integrated outputs, strict excesses, KSWX reciprocity-error allocation, corrected Pascadi eq-(5.32) geometry, fixed log exponents. Asserts no cited analytic theorem, no favourable grant, no estimate for family (33), no (SQ4-HB), no source bridge.

Python checks distinct method-class outputs: coefficient-blind Cauchy 199/100 (excesses 33/100, 1/2); ideal fixed-(p,v) sqrt cancellation 179/100 (excesses 13/100, 3/10); Blomer--Pascadi preprint at fixed (p,v): H=71/900, inner 2617/1800, outer 4111/1800; published KSWX favourable Type-I: Delta_1=-43/200, output 421/200, reciprocity-error 287/200 after eta=epsilon=1/20 (margin 11/200); Pascadi Cor 5.11: squarefree-v output 513/200, conditional 47/20; fixed-log exponents: standard 0/2, literal Cor 5.11 1/3, favourable 2/4. Source map in audit. B--P Thm 5.5 is preprint. KSWX Thm 2.1/Pascadi Cor 5.11 published but former has favourable grants, latter covers squarefree-v only. Pascadi Cor 5.9/Assum 5.4 cited with journal numbering (arXiv: 16, 14); Assum-5.4 from published Thm 1.2 via norm-preserving additive twist. Does not prove T^{48/25+epsilon}(log T)^0 level moment, cover nonsquarefree strata, or supply smooth source identity.

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4CorrelatedMoment.lean` | `8d3ea41ae50b37f089408aa78c56dcc0d84be18661fdc0fae2587c03556f7f66` |
| `PrintAxioms/SQ4CorrelatedMoment.lean` | `e9c09a9d0cd8e7963b1216cac2f3e0018dd8122e2866ab95b0a1577653c5d733` |
| `docs/audit/sq4_correlated_moment.md` | `65b9cb6d5f88b0b014e4425319c1518b4ba26d2430c7cb2e48745ab44e1ac659` |
| `verify/a1_sq4_correlated_moment.py` | `72b24b4ba09b195651192b03adef58aed7e3706541bf3abc76bfb0595105db31` |
| `verify/a1_sq4_correlated_moment.out` | `cc815831e1961a5853d628148ad9c84ed94753ac36597c9c7dc274e80f4064b5` |

## 34. A1 SQ4 published-literature gate

**Gate:** 6 theorems, standard three. **Verifier:** `a1_sq4_published_literature.py` (exact `Fraction`).
Proves common pre-completion normalization, exact outputs and positive target gaps, fixed-log inventories. Python checks target 48/25, prefactor -43/100, outputs 121/50, 111/50, 553/200, 2071/800, 1017/400, 977/360, 507/200, 139/50, 599/200 with gaps; fixed-log exponents: standard 0/2, literal Pascadi 1/3, conditional 2/4. Source audit finds no published theorem with literal full-M_4 LHS (not universal nonexistence). Required T^{48/25+epsilon}(log T)^0 bound and smooth source identity remain unproved.

| File | SHA-256 |
|------|---------|
| `Discharge/SQ4PublishedLiterature.lean` | `246f5fbfa341df4fd90c1cea2ea7ee2092cb30cdf75bf812cdbdb9d8640aa5d4` |
| `PrintAxioms/SQ4PublishedLiterature.lean` | `3cca37c88b5f70eb138f6df8c9fcbf2819daa6accf32788f5daf86be2abaf52e` |
| `docs/audit/sq4_published_literature.md` | `4d80e51bb81bab4687058cc6d9d9b508157ec047a37b2a1b5499c621a8a2a8a3` |
| `verify/a1_sq4_published_literature.py` | `5917882577253cf755f96685a16680d92ee2b240512c6d7cc6220e60a1ff63a6` |
| `verify/a1_sq4_published_literature.out` | `2585a510a4eb651c62521d58ba6ddab8753d22f0f54a2f73b24d9e95c8c598be` |

## 35. B-2 actual-block centering bridge gate

**Gate:** 3 theorems, standard three. **Verifier:** `rs_block_moment_bridge_exact.py` (integer polynomial).
Proves finite-matrix binomial identity through degree four, passes assumed uncentered actual-block limits through transform, identifies with formula (21), supplies `BlockMomentLimits` constructor. Raw degree-zero limit retains eventual positivity. Constructor assumes `UncenteredRSBlockLimits F` plus complex-alias summability/cancellation; does not derive from `RS1996ZetaInputs`, construct a principal family, or prove cyclic-symbol/height-removal/normalization/complex-Poisson/finite-grid estimates. Python expands (X-1)^k and compares with binomial transform for 0<=k<=4. No `BlockMomentLimits` instance constructed.

| File | SHA-256 |
|------|---------|
| `Discharge/RSBlockMomentBridge.lean` | `1ee61b9737e3ce8bb4d70da268e88ff1a3446e2b1be33916f1d0b05028702836` |
| `PrintAxioms/RSBlockMomentBridge.lean` | `d0b7a2a3ed973c7be5934dcd1c803148f890bf7be044bdafffc6a37a8138269a` |
| `docs/audit/rs_block_moment_bridge.md` | `205e99200cf09361563f850886409042fd6b6c4599fcb592cbf6f7a885ac9918` |
| `verify/rs_block_moment_bridge_exact.py` | `87303ae07633c1402a83ea31845eaaacd9daab3172cc1841b78e57b54a72adc8` |
| `verify/rs_block_moment_bridge_exact.out` | `4735ec2bb4334b0eecf172e0bc662df7dc0d29859ff7bc6392120806ac7f5b4a` |

## 36. A2 R1a allocation-capacity no-go gate

**Gate:** 7 theorems, standard three. **Verifier:** `r1a_allocation_nogo.py` (integer + `Fraction`).
Capacity module: two exact active-cell profile caps, abstract finite contradiction, both frozen rational gaps. NoGo module: derives every finite hypothesis from `PrincipalCyclicBlock` via almost-everywhere reconstruction, full-profile scaling, distinguished energy-ratio limit, degree-one zero-shift translated-product limit; proves `no_principal14999` and `no_principal19999` for arbitrary `ZeroConfig`. Python reconstructs profile integrals, active edges, Bernstein-basis certificates, capacity sides, strict gaps. Does not change frozen statements or constants. Quartic declarations remain conditional, but `PrincipalCyclicBlock` is formally uninhabited for both family types.

| File | SHA-256 |
|------|---------|
| `Discharge/R1aAllocationCapacity.lean` | `c5d5d0f8fd939a97477189ceedeef0d3af112894b246bbe44fe377cad393c6d2` |
| `Discharge/R1aAllocationNoGo.lean` | `7a53acb3a61e1af357a10dab696e70a472b321400a325ca553d423b33c5737db` |
| `PrintAxioms/R1aAllocationNoGo.lean` | `368a1907abcbcb0ba6c874ddb218fa3df4e9663dfc0352dee4fef9bb3ae1953e` |
| `docs/audit/r1a_allocation_nogo.md` | `03454e0c3ba7dee4037e658836299459c4a91c03ea1f7921d51a6421a209f4fc` |
| `verify/r1a_allocation_nogo.py` | `866b8275b81b6bc49ea63b2d6fb60a7df4335a0a45fcd13f206e6f95cda47143` |
| `verify/r1a_allocation_nogo.out` | `ea2d1f902975651b6b23c58195568401f9e2f9e14bb72bc17be52ce525c1fc96` |

## 37. B-4 eta-superposition support-model gate

**Gate:** 12 theorems, standard three. **Verifier:** `b4_eta_superposition_obstruction.py` (integer + `Fraction`).
Proves generic no-supported-divisor convolution lemma, prime-square specialization, concrete eta=3/4, T=625, n=899 regression: balanced [25,50] box has coefficient 2 at 899 while every signed superposition with first supports in [5,10] vanishes. Balanced positive progression majorant misses trace by eta in PQ and eta-1/2 in PH. Python enumerates divisors of 899, reconstructs boxes and supported-pair lists, recomputes excesses (does not verify logarithmic budget; C<1 from `LogBudget`/`EtaClosure`). Does not identify model coefficient with actual HB coefficient, kill (EF_eta), or assert (HD_eta). Exact survivor: |R_HD(Y,T,eta)| << Y(log T)^C with C<1 after signed h-sum and zero-mode subtraction before dyadic Y-sum. A1 unchanged.

| File | SHA-256 |
|------|---------|
| `Discharge/EtaSuperpositionObstruction.lean` | `5d21ff3339fa654268dd84821ddc1dacd67320b6d75e6bb217fb9dd8e4cfd73c` |
| `PrintAxioms/EtaSuperpositionObstruction.lean` | `06f6d413afbf765dae6e40c6a919192f779fa7187e6613ac50919d6146b29570` |
| `docs/audit/eta_superposition_obstruction.md` | `d4ed1194ea882921581ee3e08f2430df1aa4e451fd1cff1c2f9f3206a8fac9cd` |
| `verify/b4_eta_superposition_obstruction.py` | `343f2a70ae558f83be9529b3f5864478b5245ad6326fdaaee9717ecf9055a965` |
| `verify/b4_eta_superposition_obstruction.out` | `373ba96868de9bc757c0d181d1e2f23d8f88a1361b80b0a0cf835f1616ee678d` |
