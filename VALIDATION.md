# VALIDATION.md — build and audit record for the 85 % layer

Environment: Linux x86-64, Lean `v4.33.0-rc2` (installed via `elan`), Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129` (pinned in `lake-manifest.json`, fetched with
`lake exe cache get`).  Base commit before this change: `3635e74`.

---

## 1. Build

```
$ lake exe cache get
… Decompressed 8681 file(s)                                    (exit 0)

$ lake build
Build completed successfully (9023 jobs).

$ lake build Solution Solution.Multiplicity Solution.XiPrime Solution.Zeta85
Build completed successfully (9010 jobs).
```

`lake build` now covers `defaultTargets = ["Zeta23", "RH"]`; the `RH` library is the conditional
85 % layer (`lakefile.toml`).

**Zero errors.**  Warnings are the pre-existing Mathlib deprecation notices of the base repository
(`Set.mem_setOf_eq`, `MeasureTheory.integral_finset_sum`) plus unused-variable hints; none originate
in `RH/`.

## 2. `sorry` audit

```
$ grep -rn "sorry" --include=*.lean Zeta23/ RH/ comparator/ | grep -v "^comparator/Challenge"
Zeta23/FromPNTPlus/Mertens.lean:31,32     (prose in a module docstring)
Zeta23/FromPNTPlus/StrongPNTPrefix.lean:4 (prose in a module docstring)
comparator/PrintAxioms.lean:10            (prose in a module docstring)
RH/Zeta85/Discharge/SignedShift.lean:10   (prose in a module docstring: "no axioms, no `sorry`")
```

No `sorry` in any proof under `Zeta23/` or `RH/`.  The only proof-level `sorry`s in the repository
are the deliberate ones in the trusted challenge files — `comparator/Challenge.lean`,
`comparator/Challenge/Multiplicity.lean`, `comparator/Challenge/XiPrime.lean` and the new
`comparator/Challenge/Zeta85.lean` (8 of them, one per statement), exactly as the base repository
does.

## 3. `axiom` audit

```
$ grep -rn "^axiom " --include=*.lean Zeta23/ RH/ comparator/
RH/Zeta85/Hypotheses.lean:186  axiom shiu_majorant₂ : …
RH/Zeta85/Hypotheses.lean:220  axiom signedPair_traceGrade_lt_5_4 : …
RH/Zeta85/Hypotheses.lean:269  axiom signedPair_traceGrade_lt_3_2 : …
RH/Zeta85/Hypotheses.lean:340  axiom traceTransfer_saturated : …
```

Four legacy declarations, all in the single file `RH/Zeta85/Hypotheses.lean`.  The former
`windowCost_101`, `windowCost_125`, `bblr_poisson_blocks`, and `bblr_error_bound` declarations are
now theorems proved in their respective `RH/Zeta85/Discharge/` modules.  `shiu_majorant₂` asserts
the corrected interface `ShiuMajorant₂` (`RH/Zeta85/ShiuInterface.lean`); the frozen interface
`ShiuMajorant` it replaces is refuted in-repo by `RH.Zeta85.not_shiuMajorant_quarter`
(`RH/Zeta85/Discharge/ShiuNoGo.lean`) — see `AXIOMS.md` §3, Axiom 1.  These four declarations remain the
conditional boundary, not the target standard.  (The two `axiom`
lines in `Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean` sit inside a fenced code block in a
docstring and are not declarations — this is the point `AUDIT.md` already records for the base
repository.)

## 4. The base repository is unchanged

```
$ lake env lean comparator/PrintAxioms.lean
$ lake env lean comparator/PrintAxioms/Multiplicity.lean
$ lake env lean comparator/PrintAxioms/XiPrime.lean
$ lake env lean comparator/PrintAxioms/PairCeiling.lean
```

43 lines in total.  Every line of the first three files reads
`'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`; the `PairCeiling` file
reports, as before, `'Zeta23.PairCeiling.LawN256_check' depends on axioms: [propext]` and
`'Zeta23.PairCeiling.LawN256_edge' does not depend on any axioms`.  No base theorem acquired a new
axiom: nothing under `Zeta23/` imports anything under `RH/`.

## 5. The conditional topic's axiom audit

```
$ lake env lean comparator/PrintAxioms/Zeta85.lean
```

Output reproduced verbatim in `AXIOMS.md` §1.  Summary: the support-`101/100` statements depend on
`propext`, `Classical.choice`, `Quot.sound` and two of the four research axioms,
`{signedPair_traceGrade_lt_5_4, traceTransfer_saturated}`.  The support-`5/4`
statements use the same two; the 85 % statements use
`{shiu_majorant₂, signedPair_traceGrade_lt_3_2, traceTransfer_saturated}`.
Nothing else appears.

Eight lines, one per comparator statement.  An intermediate revision printed sixteen: it had
collapsed the axiom list to the single refuted `shiu_majorant` and added eight closed
`RH.Zeta85.rung*_from_shiu_contradiction` headlines (R-8657 … R-9506) whose proofs were
`False`-eliminations off `shiu_interface_contradiction`, so that *every* extension headline listed
the refuted axiom as its sole custom dependency.  Those eight declarations and the contradiction
are removed; the audit is back to the eight genuine statements above, and the per-rung dependency
sets are once again distinct (rungs 1–2 versus rung 3 — `AXIOMS.md` §2).

## 6. Statement equality, challenge ↔ solution

The `comparator` binary, `landrun` and `lean4export` are **not available in this environment** (no
outbound GitHub access beyond the repository itself, so the release tarballs cannot be fetched).
The full comparator run is therefore recorded here as *not executed*; the commands to run it are

```bash
lake exe cache get
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator/.lake/build/bin/comparator comparator/config-zeta85.json'
```

with `comparator/config-zeta85.json` as shipped (it lists the four `RH.Zeta85.Hypotheses` axioms in
`permitted_axioms` alongside the standard three — see §7).

What **was** executed is the repository's own documented substitute ("Quick check (no extra
tooling)", `comparator/README.md`) — `lake build Solution.Zeta85` plus the axiom audit above — and,
in addition, a mechanical statement-equality check of the kind comparator performs:

```
$ cat /tmp/tychal.lean          # import Challenge.Zeta85; #check @… for all eight names
$ cat /tmp/tysol.lean           # the same with  import Solution.Zeta85
$ diff <(lake env lean /tmp/tychal.lean | grep -v "declaration uses") \
       <(lake env lean /tmp/tysol.lean)
                                # no output
STATEMENT TYPES IDENTICAL
```

with `set_option pp.numericTypes true`, so that every numeral's type is displayed.  The elaborated
types printed on both sides are, for instance,

```
zeta85_rung_support_101_over_100 : ∀ ε > (0 : ℝ),
  ∃ T₀, ∀ T ≥ T₀, ((67924886307 / 100000000000 : ℝ) - ε) * ↑(Ncount T ((2 : ℝ) * T))
    ≤ ↑(N0simple T ((2 : ℝ) * T))
```

This checks the statement-equality half of a comparator run (the solution proves *exactly* the
challenge statements, with every constant coinciding).  It does **not** substitute for the export +
kernel-replay half, which requires the missing tooling.

## 7. Deviation from the base comparator conventions, declared

`comparator/README.md`, "Rules for the trusted side", rule (5): *a statement enters a challenge file
only when the Zeta23 theorem it delegates to is sorry-free with `#print axioms` = the standard
three.*

The topic `Zeta85` **deviates** from rule (5), visibly: its theorems are conditional
on the four named axioms, and `comparator/config-zeta85.json` lists those axioms in
`permitted_axioms`.  This is the only such topic in the repository; the base four files
(`Challenge.lean`, `Solution.lean`, `config.json`, `PrintAxioms.lean`) and the topics `Multiplicity`
and `XiPrime` are untouched and remain unconditional.  A reader auditing the 85 % claim must read
`RH/Zeta85/Hypotheses.lean` in addition to `comparator/Challenge/Zeta85.lean`.  The exception is a
current deficiency to discharge, not an accepted endpoint for the new mission.

## 8. Numerical cross-checks performed outside Lean

Recorded in `FINDINGS.md` §4 (exact-rational verification of the whole Phase-A certificate chain, and
double-precision verification of the two source transcendental window costs).  The Phase-A chain is
*also* proved inside Lean, so its external check is only corroboration.  Both frozen lower-rung
targets now have different exact rational witnesses proved in Lean.

## 9. Phase 0b inventory and status validation

The four logical source batches are inventoried in `docs/run/MANIFEST.md`,
which records each committed source file's byte size, SHA-256 digest, and
role.  The exact terminal filenames required by the intake gate are present.

The 100% terminal claim was checked independently with mpmath at 50 and 80
decimal digits plus exact rational arithmetic in
`verify/withdrawn_100_claim.py`; the committed output is
`verify/withdrawn_100_claim.out`.  The calculation proves the endpoint
contradiction.  It also shows that the handoff's $M₂ ≤ 0.3144$ bound does
not follow from the pointwise cone written in the supplied sources, so that
number remains an explicit missing-condition finding rather than being
silently promoted.

This milestone changes documentation, archived sources, and verification
artifacts only.  It does not constitute the Phase 0c build, comparator, or
`#print axioms` rerun; those remain to be recorded separately.

## 10. Phase 0d CI configuration

The push, pull-request, and manual workflow at `.github/workflows/ci.yml` runs:

```bash
lake exe cache get
lake build Zeta23 RH.Zeta85.Main \
  Solution Solution.Multiplicity Solution.XiPrime Solution.Zeta85
bash verify/check_axioms.sh
```

`verify/check_axioms.sh` extracts the expected 44 lines for the eight compiled
Zeta85 headlines from `AXIOMS.md` §§1.1–1.3 and performs an exact diff against
fresh Lean output.  It then runs the four base `PrintAxioms` audits.  A final
source scan rejects proof-level `sorry` and `admit` outside the comparator
challenge files.

The shell path initially exposed no Lean executable, so the GitHub-hosted run
remains the authoritative CI record.  Phase 0c's DigitalOcean reproduction was
waived explicitly by the user and was not performed.

The audit harness was repaired at commit `810353e`: the stability module
documentation now follows its `import`, as Lean requires, and every
`Solution*` module imported by the base `PrintAxioms` files is built
explicitly before the audit.  With the pinned local toolchain invoked by its
full path, the expanded build and `verify/check_axioms.sh` both exit zero.

## 11. A1.1 exact exponent audit

`verify/a1_1_method_kill.py` uses `fractions.Fraction` throughout to
recompute the Phase A1.1 scales and every claimed exponent difference.  Its
committed output is `verify/a1_1_method_kill.out`.  A byte-for-byte rerun is
checked with:

```bash
cmp -s verify/a1_1_method_kill.out <(python3 verify/a1_1_method_kill.py)
```

The script asserts:

- \(P=HQ\), \(Q=P^{50/93}\), and \(PQ=T^{143/100}\);
- Nguyen plus residue Parseval/Cauchy has exponent \(3917/2400\), an
  excess of \(97/480\);
- Parry plus Parseval and absolute modulus summation has exponent
  \(261/160\), an excess of \(161/800\);
- Parry's \(4/7\) range margin is \(22/651\), while the
  Wei--Xue--Zhang range deficit is \(1951/54312\);
- natural-order variance plus Cauchy has exactly zero power margin; and
- a literal \(C=0\) contribution has log exponent 2, strictly below the
  trace-normalization exponent 3.

The analytic premises used in those exponent substitutions were checked
against the primary theorem statements linked in
`docs/audit/log_budget_routes.md`, Route 5.  The audit changes no Lean
declaration and introduces no axiom or `Inputs95` field.

## 12. A1.2 cross-scale audit

`verify/a1_2_cross_scale.py` uses exact rational arithmetic to
recompute the local cycle-5 scales and the logarithmic comparison.  Its
committed output is `verify/a1_2_cross_scale.out`; a byte-for-byte
rerun is checked with:

```bash
cmp -s verify/a1_2_cross_scale.out <(python3 verify/a1_2_cross_scale.py)
```

The script asserts

- \(P=T^{93/100}\), \(Q=T^{1/2}\), \(PQ=T^{143/100}=Y\);
- \(PH=T^{34/25}\), giving the secondary term the exact power saving
  \(T^{-7/100}\);
- at the forced \(C=3\), literal dyadic summation has log exponent 5,
  cross-\(Y\) recombination has exponent 4, and the budget has exponent 3;
  hence equation (6) still misses by exactly one log power; and
- a five-block aligned family attains the sum of the five individual bounds.

The last statement is generalized in Lean by
`RH.Zeta85.LogBudget.blockwise_triangle_sharp`; the forced-exponent
budget failure after recombination is
`RH.Zeta85.LogBudget.crossScale_recombination_fails`.  No analytic
input or new field is introduced.  The exact actual-coefficient blocker is
equation (14) of `docs/audit/log_budget_routes.md`.

The requested historical signed-prime experiment could not be reproduced:
no generating script or coefficient construction is present in the supplied
archives or connected Drive intake.  This negative inventory result is
recorded rather than substituting a different experiment.

## 13. B-2 Rudnick--Sarnak source audit

`docs/audit/rs_reduction.md` was checked against the author-hosted
primary PDF of Rudnick--Sarnak (1996), whose SHA-256 is

```text
83010c4f68efc5f5628a71a589ff3a374220b25902384e9c1a34b3d6cd0834d6
```

The audit records the exact unconditional scope of Theorem 3.1 at \(m=1\),
the RH hypothesis in Theorem 3.2, and the narrower distributional content of
Lemmas 4.2--4.3.  The cyclic symbol, flat contractions, weighted
specialization to terminal formula (18), and corrected repository source map
are explicit in that document.

The deterministic contraction layer is now checked by:

```bash
lake build RH.Zeta85.Discharge.RSReduction RH.Zeta85.Main
lake env lean comparator/PrintAxioms/RSReduction.lean
bash verify/check_axioms.sh
```

`RSReduction.lean` proves the zero-frequency cyclic-symbol identity,
zero-sum contraction vectors, the exact \(0,1,3,6+3\) pairing enumeration,
formula-(27)-to-(18) centering, and the top-hat formula-(18)-to-(21)
specialization.  All nine printed theorems depend exactly on
`[propext, Classical.choice, Quot.sound]`; source scans find no `axiom`,
`sorry`, or `admit` in the module.

This deterministic milestone alone was not the analytic R1b discharge.  The
later `RSPairIntegrals.lean` milestone now identifies
`normalizedRSMainTerm` with the uncentered contraction formula for a
continuous compactly supported profile.  No theorem transfers that formula
to the actual principal block.  Cyclic-symbol admissibility, the actual
published-field instance, common height smoothing, \(\log T\)-normalization,
off-RH complex Poisson, and the \(k=3,4\) finite-grid/end estimates remain
listed in `FINDINGS.md` §16 and `docs/audit/rs_reduction.md` §9.

## 14. B-1 stability proof

`RH/Zeta85/Stability.lean` is imported by
`RH/Zeta85/Main.lean`.  The CI build target
`lake build Zeta23 RH.Zeta85.Main Solution Solution.Multiplicity
Solution.XiPrime Solution.Zeta85` therefore checks
the full stability module.

`comparator/PrintAxioms/Stability.lean` prints the five public
stability and compression headlines.  `verify/check_axioms.sh`
performs an exact diff against:

```text
[propext, Classical.choice, Quot.sound]
```

for each theorem.  The source scan also covers the new module and rejects
`sorry` or `admit`.  No new field or primitive declaration is
introduced.  The GitHub workflow run attached to this milestone is the
authoritative build in the current environment, where `lake` is not
available on the shell path.

## 15. A1.3 exact exponent audit

`verify/a1_3_wg_hb.py` uses `fractions.Fraction` throughout
and recomputes every exponent recorded for the final log-budget route.  Its
committed output is `verify/a1_3_wg_hb.out`; reproduce it with:

```bash
cmp -s verify/a1_3_wg_hb.out <(python3 verify/a1_3_wg_hb.py)
```

The script constructs, rather than hard-codes, the two Bettin--Chandee
exponents from the theorem's \(L^2\)-norm and bracket factors.  It also
checks:

- the candidate simultaneous-dispersion saving \(7/200\) and net saving
  \(7/400\);
- the fixed-Weil excess \(9/50\);
- the BBLR endpoint excesses;
- the Blomer--Pascadi range gap \(83/300\); and
- the two Milićević--Qin--Wu condition gaps \(141/250\) and \(47/100\).

The matching arithmetic identities are formalized in
`RH/Zeta85/Discharge/LogBudget.lean` as
`wg_hb_candidate_saving`, `wg_hb_net_saving`,
`bettin_chandee_excess`, `bblr_endpoint_first_excess`,
`blomer_pascadi_range_excess`, and
`mqw_range_excesses`.  This validates the method-class audit only;
it does not add the missing analytic estimate.

## 16. A2.1 common-lattice rank and profile audit

`docs/audit/r1a_power_complementary_partition.md` gives the exact fiber-rank
proof for the finite common-lattice PB/TDAC class.  The algebraic rank
contradiction uses no numerical premise.  Its application to the claimed
symbols is reproduced by:

```bash
python3 -m pip install -r verify/requirements.txt
cmp -s verify/a2_1_tdac_rank.out \
  <(python3 verify/a2_1_tdac_rank.py)
```

The script uses `fractions.Fraction` intervals, 90-decimal integer-square-root
enclosures, and rational Taylor remainder bounds.  It reconstructs the
matching constants \(A,B\), normalization \(M\), endpoint value, and edge
margin from terminal file 24's equations (28)--(29); no reported profile
constant is hard-coded.  Separate 60- and 100-decimal `mpmath` evaluations
agree beyond 55 decimal places.  The committed output certifies positive
residual margins greater than \(1/1000\), \(1/1000\), and \(1/10\) for
R-9506, R-8686, and the file-15 Euler repair respectively, and checks the
three exact rank deficits.  For the normalized quadratic profile it derives
the edge residual `42756493/1031000000 > 0` and the central average
`1157918831/1031000000 > 1` using exact rational arithmetic.  The latter
check prevents the unnormalized profile from being used to claim a false
zero-row obstruction.

The finite rank core now has a separate Lean gate:

```bash
lake build RH.Zeta85.Discharge.AliasRankObstruction RH.Zeta85.Main
lake env lean comparator/PrintAxioms/AliasRankObstruction.lean
bash verify/check_axioms.sh
```

It proves the explicit outer-product channel rank bound, full diagonal rank,
critical-count contradiction, full-minus-distinguished formulation, and the
three terminal integer count corollaries.  All nine printed theorems depend
exactly on `[propext, Classical.choice, Quot.sound]`, with no declaration of
`axiom`, `sorry`, or `admit`.  The two Euler-profile nonvanishing premises
remain in the exact interval verifier above; the original quadratic edge
margin is exact rational arithmetic there.  This formalizes the algebraic
method-class impossibility without adding an analytic input, changing a
headline dependency, or changing a frozen rung status.

## 17. A2.2 normalization and corrected-tail audit

The exact independent verifier is reproduced by:

```bash
python3 -m pip install -r verify/requirements.txt
cmp -s verify/a2_2_alias_free_scaling.out \
  <(python3 verify/a2_2_alias_free_scaling.py)
```

All proof decisions use `fractions.Fraction`.  The script:

- derives \(A=1031/1200\) and
  \(\sup V_\sigma=1200/1031<143/100\);
- recomputes the saturated quadratic costs at
  \(143/100\), \(1.499999\), \(1.4999\), \(1.9999\), and the diagnostic
  endpoint \(2\);
- reconstructs the paper-derived rational closed moments
  \(M_2,M_3,M_4\) from the restriction parameters;
- inverts the rational five-node Vandermonde matrix, whose determinant is
  \(99/500000\), and checks every weight is \(>1/25\);
- checks exact moment equality through degree four and the strict support
  gap \(2/5<\sigma-1\); and
- independently evaluates terminal formula (18), including its crossing
  contraction, by 55-digit tensor Gauss--Legendre quadrature.  The largest
  committed calibration discrepancy is below \(2\cdot10^{-56}\).

The corresponding kernel audit is:

```bash
lake build RH.Zeta85.Discharge.AliasFallback RH.Zeta85.Main
lake env lean comparator/PrintAxioms/AliasFallback.lean
bash verify/check_axioms.sh
```

`RH/Zeta85/Discharge/AliasFallback.lean` contains no proof placeholder or
primitive assumption.  Its public audit headlines report exactly
`[propext, Classical.choice, Quot.sound]`.  This validates the finite
rational countermodel conditional on the paper-derived closed moment
formulas; it does not formalize their equality with Mathlib integrals or the
RS bridge to formula (18), add a principal-block input, or alter a frozen
rung.

## 18. B-3 terminal certificate layer

The two independent verifiers replay byte for byte with:

```bash
python3 -m pip install -r verify/requirements.txt
cmp -s verify/b3_certificate_audit.out \
  <(python3 verify/b3_certificate_audit.py)
cmp -s verify/b3_r9383_exact_endpoint.out \
  <(python3 verify/b3_r9383_exact_endpoint.py)
```

Their committed SHA-256 values are:

```text
2f264e6637de2ec09ef5eae93f9f1368eb9a3c6ad0ea2e0c4b05c084f125ceab  verify/b3_certificate_audit.py
f34b7ca98bebe570140778d1d7341f04ad3191c199153bbecffe17528d2eb130  verify/b3_certificate_audit.out
3b01ca20b4c0b4ce54ac067050998796852be8417df57a204aa5ab20bc5b77ab  verify/b3_r9383_exact_endpoint.py
aa8b584aaf771b15ea0b1aeea18df69b29dd4563b6246fa25cd0eda7b861aaad  verify/b3_r9383_exact_endpoint.out
```

`b3_certificate_audit.py` uses exact rational arithmetic for the terminal
moments, dual-polynomial factor signs, fixed-point comparisons, Bernstein
positivity, and polynomial window-cost integrations.  Its `mpmath`
three-atom calculations are explicitly calibration only.  The second script
uses only integer and `fractions.Fraction` operations: rational Taylor
remainders, integer-square-root bounds, and interval automatic
differentiation isolate the flat endpoint in
`[0.9383133270509488847, 0.9383133270509488848]`, strictly below frozen
R-9383.

The formal build gate is:

```bash
lake build \
  RH.Zeta85.Discharge.QuarticWindowWitnesses \
  RH.Zeta85.Discharge.R9383ExactEndpoint \
  RH.Zeta85.Discharge.TopHatMoments \
  RH.Zeta85.Discharge.TrimmedMoment \
  RH.Zeta85.Main
bash verify/check_axioms.sh
```

The four isolated B-3 printers are diffed theorem by theorem against exactly
`[propext, Classical.choice, Quot.sound]`.  The check normalizes only Lean's
line wrapping; theorem names and dependency contents are compared verbatim.
In particular, `TopHatMoments.crossingReduction` proves the full
determinant-one change of variables, support-intersection calculation, and
four-quadrant reduction, and `formula21M4Integral_eq` proves the original
three-dimensional formula-(21) fourth moment without a field or named
premise.  No B-3 source contains `axiom`, `sorry`, or `admit`.

The finite R-8686 and R-9506 implications do not instantiate the missing A1,
R1a, or R1b analytic bridges.  At this B-3 gate alone there was therefore no
quartic headline.  The later Phase-C transfer in §22 assembles conditional
headlines under four explicit structures; it does not discharge them.

## 19. B-4 `eta > 1/2` factorization audit

The exact rational replay is:

```bash
cmp -s verify/b4_eta_closure.out <(python3 verify/b4_eta_closure.py)
```

with committed hashes:

```text
b934eab4fc22da185cda8a1bc2e11a10cdda3449b1479c435902d681997f008f  verify/b4_eta_closure.py
441e426de1218676e6cf322f2971c8d403d9fd439d0f5973ac000ace9e3568b3  verify/b4_eta_closure.out
```

The script uses only `fractions.Fraction`.  At the exact witness
`eta=3/4`, it verifies the legal depth-three, `j=2` block, exhausts all
whole-variable groupings, checks the unavailable `M1` exponent, and
recomputes both balanced-block power excesses.  It separately checks the
positive preliminary margin and the literal `C<1` logarithmic threshold.

The formal gate is:

```bash
lake build RH.Zeta85.Discharge.EtaClosure RH.Zeta85.Main
lake env lean comparator/PrintAxioms/EtaClosure.lean
bash verify/check_axioms.sh
```

The isolated printer's fourteen headlines each report exactly
`[propext, Classical.choice, Quot.sound]`; CI diffs that output through the
same line-wrap normalizer used for B-3.  The new Lean file has no declaration
using `axiom`, `sorry`, or `admit`.  These checks establish the unconditional
exponent and method-class audit only.  They do not assert the missing
pointwise convolution identity `(EF_eta)` or change a frozen rung's status.

## 20. Phase-C robust stability and spectral normalization

The independent exact replay is:

```bash
cmp -s verify/robust_stability.out <(python3 verify/robust_stability.py)
```

with committed hashes:

```text
8510ca4748e26e9310c3f89a5df1ef95d5f015761bec86f41b8e545fd04454bc  verify/robust_stability.py
8d2cf177b0104dc0872591fde5da73f950415b56b185ed68917451d90931117b  verify/robust_stability.out
```

The verifier uses only integers and `fractions.Fraction`.  It independently
expands the finite prebound, checks the error vector `(2,4,1,2)` and exact
count slack `2*(s+2*b-zeroScale-countErr)`, evaluates three rational
substitutions, and checks sorted-head
cardinality, removed mass, and residual identities on explicit finite
spectra.

The formal gate is:

```bash
lake build RH.Zeta85.Discharge.RobustStability RH.Zeta85.Main
lake env lean comparator/PrintAxioms/RobustStability.lean
bash verify/check_axioms.sh
```

The `PrintAxioms` dependency printer covers the public finite prebound, base/isometric/principal
robust inequalities, uniform trim construction, exact residual identity, and
the four-moment adapter.  Every line is diffed against exactly
`[propext, Classical.choice, Quot.sound]`.  Source scans find no declaration
using `axiom`, `sorry`, or `admit`.  No analytic moment equality or limiting
statement is asserted by this milestone.  By itself, the robust-stability
result discharges no analytic premise; the later conditional assembly is
validated in §22.

## 21. Phase-C `Inputs95` boundary

The formal gate is:

```bash
lake build RH.Zeta85.Inputs95 RH.Zeta85.Main
lake env lean comparator/PrintAxioms/Inputs95.lean
bash verify/check_axioms.sh
```

The isolated printer reports:

```text
'RH.Zeta85.profileSaturatedCost_v8686' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.profileSaturatedCost_v9506' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.QuarticGramFamily.G_eq_A_add_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.StableZeroSide.block_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.core_count_le_dyadic_add_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.robustBlockTailBound_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The family types contain the exact B-3 profiles.  The matrix definitions use
the actual full zero sum and finite `ZIprime` truncation, and the robust
adapter concludes on that truncation's literal principal block.  Source scans
find no declaration using `axiom`, `sorry`, or `admit`.  No `Inputs95`
instance or constructor theorem exists.  This gate validates the hypothesis
boundary and its finite adapters; the separate conditional headline gate is
§22.

## 22. Phase-C quartic transfer and conditional headlines

The exact independent replay is:

```bash
cmp -s verify/quartic_transfer.out \
  <(python3 verify/quartic_transfer.py)
```

with committed hashes:

```text
dc99b510fdf1966f11535bf57a3dc53f4056c679e0275c8a649c01facf5f3bdf  verify/quartic_transfer.py
05615d7eb1727532cb81a5c04598630ebd9c29408b729770d34e4b282b533cce  verify/quartic_transfer.out
```

The script uses only exact `fractions.Fraction` arithmetic.  It checks the
edge identity `2 + (1-cap/2) + cap/2 = 3`, both fixed-point quotient
identities, both strict frozen-target margins, and the monotone comparisons
R-8657 < R-8686 and R-9383 < R-9506.  Its output replays byte for byte.

The formal gate is:

```bash
lake build \
  RH.Zeta85.Discharge.QuarticTransfer \
  RH.Zeta85.QuarticMain \
  RH.Zeta85.Main
lake env lean comparator/PrintAxioms/QuarticTransfer.lean
lake env lean comparator/PrintAxioms/QuarticMain.lean
bash verify/check_axioms.sh
```

`QuarticTransfer.lean` proves the spectral-moment identity, exact finite
dual scaling, edge coefficient three, `NII=o(N)`, normalized limit, generic
epsilon transfer, and the four concrete zeta specializations.  The direct
R-8686 and R-9506 branches have strict exact margins.  R-8657 is obtained
monotonically from R-8686; R-9383 is obtained monotonically from R-9506, not
from the killed upward-rounded flat branch.

`QuarticMain.lean` exposes eight final statements:

```text
RH.Zeta85.rung8657
RH.Zeta85.rung8657_cumulative
RH.Zeta85.rung8686
RH.Zeta85.rung8686_cumulative
RH.Zeta85.rung9383
RH.Zeta85.rung9383_cumulative
RH.Zeta85.rung9506
RH.Zeta85.rung9506_cumulative
```

Each takes exactly `FullTraceLimits`, `StableZeroSide`,
`PrincipalCyclicBlock`, and `BlockMomentLimits` for its support family.
Pair-trace and RS structures are upstream derivation routes and are not
headline premises.  The transfer `PrintAxioms` dependency printer covers 21
public theorems, and the headline dependency printer covers all eight
statements; every line is exactly
`[propext, Classical.choice, Quot.sound]`.  Source scans find no `axiom`,
`sorry`, or `admit` in these files.  No separate trusted-statement
comparator topic has yet been added for the quartic headlines.

No instance of the four analytic structures is constructed.  The comparator
dependency audit therefore confirms only their standard-three kernel
footprint.  It neither supplies trusted-statement comparator equality nor
makes R-8657, R-8686, R-9383, or R-9506 unconditional.

## 23. A1 exact depth-four Heath--Brown coefficient layer

The formal gate is:

```bash
lake build RH.Zeta85.Discharge.HBDepthFour RH.Zeta85.Main
lake env lean comparator/PrintAxioms/HBDepthFour.lean
bash verify/check_axioms.sh
```

`HBDepthFour.lean` proves the exact four-term sharp-cutoff identity through
\(n\le Z^4\), arbitrary eight-slot grouping factorization, exact
\(d_1d_2=d_3d_4=d\) coefficient sums, literal triangle majorants, dyadic
support machinery, common \((j,d,\ell,p,q)\) indexing, and generic
residue-cell centering.  It now also constructs the literal reduced-residue
mean for one planned component and its signed four-component sum, proving
each reduced centered sum is zero.  Exact countermodels prove that the old
all-class mean cannot replace the reduced mean and that reduced centering
alone cannot imply a singular-series main term.  The planned closed floor
blocks are not claimed to be the source partition, and neither residue mean
is claimed to be BBLR's frequency \(\ell=0\) gcd/integral term.  The
dependency printer covers 29 selected public theorems, all depending exactly on
`[propext, Classical.choice, Quot.sound]`.  Source scans find no `axiom`, `sorry`,
`admit`, or `unsafe` in the module or printer.

No numeric verifier is required for this milestone: it introduces no
calibrated numerical claim.  Its exact source-identification boundary is
recorded in `docs/audit/hb_depth_four_coefficients.md`.  In particular, the
printer is a dependency audit rather than a trusted Challenge/Solution
statement comparator, and no theorem identifies these sharp coefficients
with run 12's smooth `c`, `e`, or `F`, evaluates the signed frequency
\(\ell=0\) integrals against the Ramanujan singular series with an explicit
error, proves an A1 estimate, or changes a frozen rung status.

## 24. A1 BBLR gcd allocation and finite coefficient collapse

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.BBLRGCDAllocation RH.Zeta85.Main
lake env lean comparator/PrintAxioms/BBLRGCDAllocation.lean
python3 verify/bblr_gcd_allocation.py
diff -u verify/bblr_gcd_allocation.out \
  <(python3 verify/bblr_gcd_allocation.py)
bash verify/check_axioms.sh
```

`BBLRGCDAllocation.lean` proves the positive-\(d\) canonical allocation
equivalence, both inverse identities, reduced-product coprimality and its
converse gcd formula, the filtered one-side coefficient collapse with
multiplicity one, and the two-sided finite-kernel reindexing.  The regression
at \(d=p=2\) proves that the canonical unit coefficient has three terms while
the unfiltered raw split has four; the independent Python enumeration matches
the committed output exactly.

The dedicated printer selects five core public theorems.  Every line is
exactly `[propext, Classical.choice, Quot.sound]`, and the printer is included
in `verify/check_axioms.sh`.  Source scans find no `axiom`, `sorry`, `admit`,
or `unsafe` in the module or printer.  `RH.Zeta85.Main` imports the module.

This validates only the finite source collapse for supplied BBLR outer
sequences, inner smooth weights, and kernel.  It does not construct the
smooth signed Heath--Brown grouping, prove `(EDB)` or `(WG-HB)`, evaluate the
frequency \(\ell=0\) integrals against the Ramanujan singular series, or
change any frozen rung status.  The exact boundary is recorded in
`docs/audit/bblr_gcd_allocation.md`.

## 25. A1 fixed asymmetric smooth-grouping method class

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.HBToBBLRSmoothGrouping RH.Zeta85.Main
lake env lean comparator/PrintAxioms/HBToBBLRSmoothGrouping.lean
python3 verify/a1_smooth_grouping.py
diff -u verify/a1_smooth_grouping.out \
  <(python3 verify/a1_smooth_grouping.py)
bash verify/check_axioms.sh
```

`HBToBBLRSmoothGrouping.lean` checks the zero-based `j = 1` component
inventory and scalar, proves that its truncated Möbius atoms are not
coefficient-one slots, verifies the exact terminal exponent block, and
proves the fixed left, right, and two-sided literal-slot assignments
impossible below their exact gaps.  It also proves that collapsing two
coefficient-one slots creates the nonconstant convolution
`zeta * zeta`, rather than a literal BBLR smooth variable.

The independent `Fraction` replay checks the signed component coefficient,
the Möbius/coefficient-one distinction at (2), every exponent identity and
gap, and the divisor multiplicities at (2) and (4).  Its committed hashes
are:

```text
67550b74daf9ae0ed31ad37729fbf35ba52a64ddd245a2860ada0da65df42793  verify/a1_smooth_grouping.py
fd1fa689b25c6dfdc9545b6bf248cd9079126b8c07ad681ece66262cb1f8c5bb  verify/a1_smooth_grouping.out
```

The dependency printer selects 15 public theorems.  Every line is exactly
`[propext, Classical.choice, Quot.sound]`; the printer is included in
`verify/check_axioms.sh`, and `RH.Zeta85.Main` imports the module.  Source
scans find no `axiom`, `sorry`, `admit`, or `unsafe` in the module or
printer.

This validates only the killed fixed-scale literal-slot method class.  It
does not supply an actual-scale all-block estimate, a smooth superposition
identity, a higher-dimensional divisor theorem, `(EDB)`, `(WG-HB)`, or an
A1 trace input, and it changes no frozen rung status.

## 26. A1 actual-scale BBLR positive-majorant method classes

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.ActualScaleBBLR RH.Zeta85.Main
lake env lean comparator/PrintAxioms/ActualScaleBBLR.lean
python3 verify/a1_actual_scale_bblr.py
diff -u verify/a1_actual_scale_bblr.out \
  <(python3 verify/a1_actual_scale_bblr.py)
bash verify/check_axioms.sh
```

`ActualScaleBBLR.lean` proves the exact actual-block geometry, both BBLR
Proposition 3.1 error exponents and their positive excesses, the equation
(14) Fourier physical scale and frequency-cutoff cancellation, the exact
\(d=1\) progression lengths, the \(PQ\) obstruction, and the harmless
\(PH\) and \(H^2\) terms.  It declares no premise and contains no proof
placeholder.  `RH.Zeta85.Main` imports the module.

The printer selects 13 public theorems.  Every line is exactly
`[propext, Classical.choice, Quot.sound]`; the printer is included in
`verify/check_axioms.sh`.  The independent verifier uses exact
`fractions.Fraction` arithmetic.  Its committed hashes are:

```text
e7c25c211113adc8a0ab51a7e348073f6c4ffacb96ae05785f9d16199d3adb2a  verify/a1_actual_scale_bblr.py
5c0514d743c30ae1b1d89420bb4ff295c01534031d41e2f004b176dcb7f00c42  verify/a1_actual_scale_bblr.out
```

This validates only the failure of direct Proposition 3.1 and of the run-12
progression majorant applied after equation (14) on the exact symmetric
block.  It does not prove a lower bound for the original signed remainder,
exclude simultaneous coefficient cancellation before the majorant, supply
an A1 trace input, or change a frozen rung status.

## 27. B-2 RS pair-integral and compact-support gate

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.RSPairIntegrals RH.Zeta85.Main
lake env lean comparator/PrintAxioms/RSPairIntegrals.lean
python3 verify/rs_pair_integrals_exact.py
diff -u verify/rs_pair_integrals_exact.out \
  <(python3 verify/rs_pair_integrals_exact.py)
bash verify/check_axioms.sh
```

`RSPairIntegrals.lean` proves all one-pair and two-pair contractions through
degree four, their exact normalization, and final wrappers which derive all
kernel integrability from `0 < mu`, `Continuous r`, and
`HasCompactSupport r`.  `RH.Zeta85.Main` imports the module.  The dedicated
printer contains 51 selected public theorems and is included in the generic
standard-three loop in `verify/check_axioms.sh`; every normalized line is
exactly `[propext, Classical.choice, Quot.sound]`.  Source scans find no
`axiom`, `sorry`, `admit`, or `unsafe` in the module or printer.

The independent exact verifier enumerates the pairing counts and every
partial-sum profile and checks the raw/normalized scaling powers.  Its
committed hashes are:

```text
04b2a386bd83f19c39307ddf4b7ea36ffc62802f924efcf1d53292d5aa929833  verify/rs_pair_integrals_exact.py
e090227f8f2768c2a75771ce9ac2fc157e45b1650e09f901530f0a76ab48f4f2  verify/rs_pair_integrals_exact.out
```

This gate discharges only the internal analytic RS main-term evaluation.  It
does not construct `BlockMomentLimits`, instantiate the actual published
theorem-3.1 field, or discharge cyclic-symbol admissibility, common height
smoothing, `log T` versus `ell(T) = log(T/2*pi)`, complex Poisson, the
degree-three and degree-four finite-grid/end estimates, or the actual
principal-block identification.  No frozen rung status changes.

## 28. A1 pre-majorant DI one-shot gates

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.PreMajorantDI RH.Zeta85.Main
lake env lean comparator/PrintAxioms/PreMajorantDI.lean
python3 verify/a1_premajorant_di.py
diff -u verify/a1_premajorant_di.out \
  <(python3 verify/a1_premajorant_di.py)
bash verify/check_axioms.sh
```

`PreMajorantDI.lean` proves the exact source scales, collapsed coefficient
norm exponent, all three Drappeau \(K^2\) exponents, the direct integrated
exponent \(179/100\), and its exact \(9/25\) excess over trace.  It also
formalizes the finite \(\mathbb Z/5\mathbb Z\) inverse mismatch and the
candidate Pascadi factor arithmetic.  The latter is explicitly conditional
arithmetic: the module asserts neither cited analytic theorem nor the
missing source-faithful reindex.  `RH.Zeta85.Main` imports the module.

The dedicated printer selects 15 public theorems and is included in the
generic standard-three loop in `verify/check_axioms.sh`.  Every normalized
line is exactly `[propext, Classical.choice, Quot.sound]`.  Source scans find
no `axiom`, `sorry`, `admit`, or `unsafe` in the module or printer.

The independent verifier uses exact `fractions.Fraction` arithmetic and
checks every exponent, comparison, the finite inverse regression, and the
separate literal-map applicability flag.  Its hashes are:

```text
1901eda16d2824e1692c1639eccf120d24cd40c1ddefbf631a55fccbb776db2b  verify/a1_premajorant_di.py
0d95711e582c826ff0227daef45bd2bbf73885723d189f43283a06eb9a27756a  verify/a1_premajorant_di.out
```

This validates two distinct conclusions: the direct collapsed Drappeau
class is power-killed at \(179/100\), while the literal completed \(r=a\)
Pascadi map is structurally inapplicable.  The conditional Pascadi exponent
substitution is not a bound.  A \((q,a)\)-dependent reindex with a separate
\(k=0\) treatment remains open.  No A1 field is discharged and no frozen
rung status changes.

## 29. A1 four-Möbius-slot exponent and method-class gates

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.FourMuKloosterman RH.Zeta85.Main
lake env lean comparator/PrintAxioms/FourMuKloosterman.lean
python3 verify/a1_four_mu_kloosterman.py
diff -u verify/a1_four_mu_kloosterman.out \
  <(python3 verify/a1_four_mu_kloosterman.py)
bash verify/check_axioms.sh
```

`FourMuKloosterman.lean` proves the exact seven retained scales, the
composite-modulus obstruction, the killed one-sided
fixed-modulus/square-root/triangle output, and the arithmetic of the
surviving simultaneous candidate.  It proves no analytic form of
`(SQ4-HB)` and introduces no premise or placeholder.  The exact verifier
checks fixed-\(x\) and integrated targets, the \(49/200\) one-sided misses,
the \(149/100\) and \(63/50\) simultaneous candidate exponents, the
\(17/400+17/400\) strict loss allocation, and the explicit normalized/raw
long-log exponents \(0\) and \(2\).

The dedicated printer selects 13 public theorems.  Twelve normalize exactly
to `[propext, Classical.choice, Quot.sound]`.  The elementary theorem
`source_modulus_not_prime` has the strictly smaller dependency set
`[propext, Quot.sound]`; `verify/check_axioms.sh` records that line
separately rather than inflating its expected dependencies.  `RH.Zeta85.Main`
imports the module.  Source scans find no `axiom`, `sorry`, `admit`, or
`unsafe` in the module or printer.

The exact artifact hashes are:

```text
bc67127847ef877cf3d615a747df83e60da2fa7a046c0ed8ed372d18ca23601c  RH/Zeta85/Discharge/FourMuKloosterman.lean
33a45b0dfa795ee0a88457710b50df1f9129a30e0e85b8905e4ef692e7476968  comparator/PrintAxioms/FourMuKloosterman.lean
f3c697d60b70f32abb22748f7dd28219c2e656fc0efeaa5fd61d7af560436901  docs/audit/four_mu_kloosterman.md
a8eb4b39fb9215c0af8b45449a036c8cee4c434a0906c3a9f6a55742e1146594  verify/a1_four_mu_kloosterman.py
3c1abc99cb74c993323371b23ed806dad68ad76fc0472a665cb989a1f11e6977  verify/a1_four_mu_kloosterman.out
```

This validates exponent bookkeeping and the exact narrow method-class
verdict only.  The simultaneous analytic estimate `(SQ4-HB)` and the smooth
source-identification/recombination identity remain unproved.  No A1 field
is discharged and no frozen rung status changes.

## 30. A1 simultaneous SQ4 route gates

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.SQ4SimultaneousRoutes RH.Zeta85.Main
lake env lean comparator/PrintAxioms/SQ4SimultaneousRoutes.lean
python3 verify/a1_sq4_simultaneous_routes.py
diff -u verify/a1_sq4_simultaneous_routes.out \
  <(python3 verify/a1_sq4_simultaneous_routes.py)
bash verify/check_axioms.sh
```

`SQ4SimultaneousRoutes.lean` proves the exact rational source scales; the
fixed-\(x\) and integrated outputs and excesses of the character-large-sieve,
coefficient-uniform norm-only, additive-large-sieve, Poisson zero-mode, and
Poisson-Weil/triangle calculations; the reciprocal profile, completion
prefactor, and dual length; and normalized/raw logarithmic exponents \(0\)
and \(2\).  It states no analytic estimate or placeholder.  In particular,
it does not assert Poisson summation, the character or additive large sieve,
the Ramanujan or Weil estimates, a Kuznetsov application, `(SQ4-HB)`, or a
bound for the nonzero transformed family (33).

The dedicated printer selects 13 public theorems and is included in the
generic standard-three loop in `verify/check_axioms.sh`.  Every normalized
line is exactly `[propext, Classical.choice, Quot.sound]`.
`RH.Zeta85.Main` imports the module.  Source scans find no `axiom`, `sorry`,
`admit`, or `unsafe` in the module or printer.

The independent `fractions.Fraction` verifier checks all fixed and
integrated outputs and excesses, the profile and truncation scales, the
explicit nonzero loss \(T^{\eta+\varepsilon}\) with \(0<\eta<2/5\), and
the normalized/raw long-log exponents \(0\) and \(2\); it also records the
six route labels.  The two structural-applicability verdicts are instead
source-audited in `docs/audit/sq4_simultaneous_routes.md`.  The exact artifact
hashes are:

```text
3ff0acf59b6a0f828f5d0e00fe8af3a4ef9225a8d3456f3877f2193b1c52c661  RH/Zeta85/Discharge/SQ4SimultaneousRoutes.lean
eaa5e835a79bdcfe051811a8c9d8e690ca5d6fbe1895fbf973909c9470da910b  comparator/PrintAxioms/SQ4SimultaneousRoutes.lean
c87497add008c3113efb23528c07df9f39f45c8867278209f7f3fe49008c08c5  docs/audit/sq4_simultaneous_routes.md
fe11015425ec5312fd1894144ff17b6bcb8cfd303735c5774068e8554c04cd6a  verify/a1_sq4_simultaneous_routes.py
ece3e6a0dd1de6ba8100c90e2d59ba1caf4af77de6ea72283b0acf79945932b8  verify/a1_sq4_simultaneous_routes.out
```

The audit makes the Poisson zero mode power-safe but does not prove
`(SQ4-HB)`.  The nonzero transformed family (33), the smooth
source-identification/recombination identity, and the required correlated
estimate remain open.  No A1 field is discharged and no frozen rung status
changes.

## 31. A1 SQ4 finite Gauss-transform and inversion gates

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.SQ4GaussSquareTransform RH.Zeta85.Main
lake env lean comparator/PrintAxioms/SQ4GaussSquareTransform.lean
python3 verify/a1_sq4_gauss_square_transform.py
diff -u verify/a1_sq4_gauss_square_transform.out \
  <(python3 verify/a1_sq4_gauss_square_transform.py)
bash verify/check_axioms.sh
```

`SQ4GaussSquareTransform.lean` proves six exact finite-algebra results:
the abstract correlation transform; the product of two generalized shifted
Gauss sums for arbitrary residues; the unit-shift scaling identity; its
Gauss-square specialization; full Dirichlet-character Fourier inversion
for every positive modulus, including composite moduli; and the exact
Kloosterman-kernel character inversion.  It states no complete-sum bound,
primitivity assumption, CRT recombination, analytic moment, `(SQ4-HB)`, or
placeholder.

The dedicated printer selects those six theorems and is included in the
generic standard-three loop in `verify/check_axioms.sh`.  Every normalized
line is exactly `[propext, Classical.choice, Quot.sound]`.
`RH.Zeta85.Main` imports the module.  The targeted build, Main build,
printer, independent-output diff, full axiom gate, source scans, and
`git diff --check` all exit zero.

The independent `fractions.Fraction` verifier reconstructs the source
scales, the completion exponent \(-43/100\), the exact pre-completion
`(SQ4-HB)` target \(48/25\) with fixed log exponent \(0\), the weaker
literal target \(209/100\), and
the coefficient-blind pre-completion output \(121/50\).  The latter
misses the two targets by exactly \(1/2\) and \(33/100\).  It also
records the raw two-long-slot logarithmic exponent \(2\).  These are
power comparisons only, not analytic estimates.

The exact artifact hashes are:

```text
1c58791ca5d3f2f2879c6e5e6ae60ebb3b9efd9b1f9c0ae90ae1c73aa72dc3e5  RH/Zeta85/Discharge/SQ4GaussSquareTransform.lean
99359bb5bc9cd5de16edac3cf369deed8def95e8b4129dd18dae8ef58d8e2db2  comparator/PrintAxioms/SQ4GaussSquareTransform.lean
03a629e8e1c522c8f84766b4f06e49d9ef5fb8154fa5564d617eb545533a1dac  docs/audit/sq4_gauss_square_transform.md
387225f5f613fcf79be7412f308f2859b255eefade6237ed2ddfd3432e337981  verify/a1_sq4_gauss_square_transform.py
89168a2503baea412b3bc96b465ff7f7335ac700f41e23ddbe6190cb63d718d0  verify/a1_sq4_gauss_square_transform.out
```

The exact unresolved analytic object is equation (14) of
`docs/audit/sq4_gauss_square_transform.md`.  It retains all four Möbius
factors, the generalized shifted Gauss products on every nonunit
conductor/gcd stratum, and the varying factorized composite modulus before
coefficient-blind Cauchy.  The required bound and the separate smooth
source-identification/recombination identity remain unproved.  No A1 field
is discharged and no frozen rung status changes.

## 32. A1 SQ4 CRT/conductor and shared-gcd gates

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.SQ4CRTConductor RH.Zeta85.Main
lake env lean comparator/PrintAxioms/SQ4CRTConductor.lean
python3 verify/a1_sq4_crt_conductor.py
diff -u verify/a1_sq4_crt_conductor.out \
  <(python3 verify/a1_sq4_crt_conductor.py)
bash verify/check_axioms.sh
```

`SQ4CRTConductor.lean` contains 38 theorem or lemma declarations.  It proves
coprime CRT factorization with the complementary-modulus twists, arbitrary
nonunit-shift conductor support, the general complex primitive-`changeLevel`
imprimitive Gauss formula in equivalent divisor-\(d\) and divisor-\(s\)
coordinates, the inverse-to-conjugate phase, the unit-supported formula, the
squarefree shared-gcd decomposition, Möbius-sign cancellation, and the
minimal \(\mathbb Z/4\mathbb Z\) false-CRT counterexample.  It asserts no
analytic estimate, source-weight factorization, `(SQ4-HB)`, or smooth source
bridge.

The dedicated printer selects 31 public results and is included in the
generic standard-three loop in `verify/check_axioms.sh`.  Every normalized
line is exactly `[propext, Classical.choice, Quot.sound]`.
`RH.Zeta85.Main` imports the module.  The targeted build, Main build,
printer, independent-output diff, full axiom gate, source scans, and
`git diff --check` all exit zero.

The independent exact checker uses integer polynomial arithmetic in
\(\mathbb Q[x]/\Phi_q(x)\), not floating-point roots of unity.  It calibrates
3,336 imprimitive identities for selected primitive real characters,
including zero shifts and shared-prime quotient levels, checks 1,208 nonzero
conductor-support instances, and enumerates 3,721 squarefree shared-gcd
strata.  The general nonreal complex conjugation phase is proved by Lean and
is explicitly outside the finite checker's scope.  `fractions.Fraction`
also verifies

\[
 {48\over25}-{43\over100}={149\over100},\qquad
 {121\over50}-{48\over25}={1\over2}.
\]

The exact artifact hashes are:

```text
7e42a5cdad131001fdc411d66229f5aa845a63da42b92334579f0e309853b2b3  RH/Zeta85/Discharge/SQ4CRTConductor.lean
217ff71194a7769b45be368239db747f37627ab061054a26f57795423342f8cd  comparator/PrintAxioms/SQ4CRTConductor.lean
47a4f858b284e2106051d6dc5a3ef1d50a1aed27ce89730bda27dd9d6d0181ea  docs/audit/sq4_crt_conductor_strata.md
43291f853513881dfba2aa432a59993364257be3756f406bf00c2ac5d62bf02f  verify/a1_sq4_crt_conductor.py
78ed2cedad32d5ebd348aaa034f98bda5676804ab9691b7cb963752eceeb24e1  verify/a1_sq4_crt_conductor.out
```

The exact analytic target remains
\(\lvert\mathfrak M_4(T,x)\rvert
\ll_{\varepsilon,\mathbf W}T^{48/25+\varepsilon}(\log T)^0\), with all
four Möbius factors, the shared conductor/divisor coupling, and the joint
source weight retained before Cauchy.  The smooth source bridge remains a
separate blocker.  No A1 field is discharged and no frozen rung status
changes.

## 33. A1 SQ4 correlated-moment and published-family gates

The formal and independent gates are:

    lake build RH.Zeta85.Discharge.SQ4CorrelatedMoment \
      RH.Zeta85.Discharge.SQ4GaussSquareTransform RH.Zeta85.Main
    lake env lean comparator/PrintAxioms/SQ4CorrelatedMoment.lean
    python3 verify/a1_sq4_correlated_moment.py
    diff -u verify/a1_sq4_correlated_moment.out \
      <(python3 verify/a1_sq4_correlated_moment.py)
    bash verify/check_axioms.sh

SQ4CorrelatedMoment.lean proves the exact rational scales, fixed and
integrated outputs, strict excesses, explicit KSWX reciprocity-error
allocation, corrected Pascadi equation-(5.32) geometry, and every fixed
logarithmic exponent for the correlated-moment audit.  It asserts none of
the cited analytic theorems, no favourable grant, no estimate for family
(33), no (SQ4-HB), and no source-identification bridge.

The dedicated printer selects all 15 public theorems and is included in the
generic standard-three loop in verify/check_axioms.sh.  Every normalized
line is exactly [propext, Classical.choice, Quot.sound].
RH.Zeta85.Main imports the module.  The targeted build, Main build, printer,
independent-output diff, full axiom gate, source scans, and
git diff --check all exit zero.

The independent fractions.Fraction verifier checks the following distinct
method-class outputs:

- coefficient-blind character Cauchy: \(199/100\), with budget and
  (SQ4-HB) excesses \(33/100\) and \(1/2\);
- ideal fixed-\((p,v)\) square-root cancellation only in \((k,r)\):
  \(179/100\), with excesses \(13/100\) and \(3/10\);
- the locally applicable Blomer--Pascadi July 2026 preprint at fixed
  \((p,v)\): \(H=71/900\), inner output \(2617/1800\), and
  outer-triangled output \(4111/1800\);
- the published KSWX favourable Type-I class: best
  \(\Delta_1=-43/200\), completed output \(421/200\), and reciprocity-error
  exponent \(287/200\) after the explicit allocations
  \(\eta=\varepsilon=1/20\), leaving margin \(11/200\);
- published Pascadi Corollary 5.11 (Corollary 17 in the arXiv version):
  literal squarefree-\(v\), separate-\((d,a)\) output \(513/200\), versus
  conditional \(47/20\) arithmetic under the unstated
  general-first-sequence/recombination grant; and
- normalized/raw fixed logarithmic exponents \(0/2\), literal Corollary
  5.11 exponents \(1/3\), and favourable general-first-sequence exponents
  \(2/4\).

The primary-source map is recorded in the audit rather than asserted in
Lean.  Blomer--Pascadi Theorem 5.5 is a preprint and genuinely applies only
to the fixed block used here.  KSWX Theorem 2.1 and Pascadi Corollary 5.11
are published, but the former source reduction has explicit favourable
coprimality/energy grants, while the latter literal lift covers only the
squarefree-\(v\) strata and pays the separate recombination cost.  Pascadi
Corollary 5.9 and Assumption 5.4 are cited with their final journal
numbering; the audit also records their arXiv numbers 16 and 14.  The
arbitrary-coefficient Assumption-5.4 instance is derived directly from
published Theorem 1.2 after the norm-preserving additive twist.

The exact artifact hashes are:

    8d3ea41ae50b37f089408aa78c56dcc0d84be18661fdc0fae2587c03556f7f66  RH/Zeta85/Discharge/SQ4CorrelatedMoment.lean
    e9c09a9d0cd8e7963b1216cac2f3e0018dd8122e2866ab95b0a1577653c5d733  comparator/PrintAxioms/SQ4CorrelatedMoment.lean
    65b9cb6d5f88b0b014e4425319c1518b4ba26d2430c7cb2e48745ab44e1ac659  docs/audit/sq4_correlated_moment.md
    72b24b4ba09b195651192b03adef58aed7e3706541bf3abc76bfb0595105db31  verify/a1_sq4_correlated_moment.py
    cc815831e1961a5853d628148ad9c84ed94753ac36597c9c7dc274e80f4064b5  verify/a1_sq4_correlated_moment.out

This gate does not prove the required
\(T^{48/25+\varepsilon}(\log T)^0\) signed generalized-Gauss-product level
moment, cover the nonsquarefree \(g\nmid k\) strata by the Ramanujan lift, or
supply the separate smooth source-identification/recombination identity.
No A1 field is discharged and no frozen rung status changes.

## 34. A1 SQ4 published-literature gate

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.SQ4PublishedLiterature RH.Zeta85.Main
lake env lean comparator/PrintAxioms/SQ4PublishedLiterature.lean
python3 verify/a1_sq4_published_literature.py
diff -u verify/a1_sq4_published_literature.out \
  <(python3 verify/a1_sq4_published_literature.py)
bash verify/check_axioms.sh
```

`SQ4PublishedLiterature.lean` proves the common pre-completion normalization,
the exact outputs and positive target gaps for the reviewed numerical method
classes, and their normalized/raw fixed-log inventories.  It asserts no
cited analytic theorem, literature-applicability statement, favourable
coefficient grant, full-source moment estimate, `(SQ4-HB)`, or smooth source
bridge.

The dedicated printer selects all six public theorems and is included in the
generic standard-three loop in `verify/check_axioms.sh`.  Every normalized
line is exactly `[propext, Classical.choice, Quot.sound]`.
`RH.Zeta85.Main` imports the module.  The targeted build, Main build, printer,
independent-output diff, full axiom gate, source scans, and
`git diff --check` all exit zero.

The exact verifier checks the pre-completion target \(48/25\), completion
prefactor \(-43/100\), and the audited outputs \(121/50\), \(111/50\),
\(553/200\), \(2071/800\), \(1017/400\), \(977/360\), \(507/200\),
\(139/50\), and \(599/200\), together with every displayed gap.  It
reconstructs fixed-log exponents from primitive sources: standard
normalized/raw \(0/2\), literal Pascadi \(1/3\), and conditional Pascadi
\(2/4\).

The exact artifact hashes are:

```text
246f5fbfa341df4fd90c1cea2ea7ee2092cb30cdf75bf812cdbdb9d8640aa5d4  RH/Zeta85/Discharge/SQ4PublishedLiterature.lean
3cca37c88b5f70eb138f6df8c9fcbf2819daa6accf32788f5daf86be2abaf52e  comparator/PrintAxioms/SQ4PublishedLiterature.lean
4d80e51bb81bab4687058cc6d9d9b508157ec047a37b2a1b5499c621a8a2a8a3  docs/audit/sq4_published_literature.md
5917882577253cf755f96685a16680d92ee2b240512c6d7cc6220e60a1ff63a6  verify/a1_sq4_published_literature.py
2585a510a4eb651c62521d58ba6ddab8753d22f0f54a2f73b24d9e95c8c598be  verify/a1_sq4_published_literature.out
```

The source audit finds no published theorem in the audited classes with the
literal full-\(\mathfrak M_4\) left-hand side.  This is not a universal
nonexistence claim.  The required
\(T^{48/25+\varepsilon}(\log T)^0\) bound and the separate smooth source
identification/recombination identity remain unproved.  No A1 field is
discharged and no frozen rung status changes.

## 35. B-2 actual-block centering bridge gate

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.RSBlockMomentBridge RH.Zeta85.Main
lake env lean comparator/PrintAxioms/RSBlockMomentBridge.lean
python3 verify/rs_block_moment_bridge_exact.py
diff -u verify/rs_block_moment_bridge_exact.out \
  <(python3 verify/rs_block_moment_bridge_exact.py)
bash verify/check_axioms.sh
```

`RSBlockMomentBridge.lean` proves the literal finite-matrix binomial identity
through degree four, passes assumed uncentered actual-block limits through
that finite transform, identifies the result with formula (21), and supplies
a constructor for the existing `BlockMomentLimits` interface.  The raw
degree-zero limit retains eventual positivity of the block dimension.

The constructor boundary remains analytic: it assumes
`UncenteredRSBlockLimits F` and separately assumes complex-alias summability
and cancellation at the actual enlarged-window zeros.  It does not derive
these clauses from `RS1996ZetaInputs`, construct a principal family, or prove
the cyclic-symbol, height-removal, normalization, complex-Poisson, or higher
finite-grid estimates.

The dedicated printer selects all three public theorems and is included in
the generic standard-three loop in `verify/check_axioms.sh`.  Every
normalized line is exactly `[propext, Classical.choice, Quot.sound]`.
`RH.Zeta85.Main` imports the module.  The targeted/Main build, printer,
exact-output diff, full axiom gate, source scans, and `git diff --check` all
exit zero.

The Python verifier independently expands \((X-1)^k\) with integer
polynomial multiplication and compares its coefficients with the binomial
transform for \(0\le k\le4\).  Its printed analytic-interface inventory is
descriptive; the Lean theorem statements and dependency printer validate
that split.

The exact artifact hashes are:

```text
1ee61b9737e3ce8bb4d70da268e88ff1a3446e2b1be33916f1d0b05028702836  RH/Zeta85/Discharge/RSBlockMomentBridge.lean
d0b7a2a3ed973c7be5934dcd1c803148f890bf7be044bdafffc6a37a8138269a  comparator/PrintAxioms/RSBlockMomentBridge.lean
205e99200cf09361563f850886409042fd6b6c4599fcb592cbf6f7a885ac9918  docs/audit/rs_block_moment_bridge.md
87303ae07633c1402a83ea31845eaaacd9daab3172cc1841b78e57b54a72adc8  verify/rs_block_moment_bridge_exact.py
4735ec2bb4334b0eecf172e0bc662df7dc0d29859ff7bc6392120806ac7f5b4a  verify/rs_block_moment_bridge_exact.out
```

This gate discharges only finite centering and the raw-to-centered limit
adapter.  `UncenteredRSBlockLimits`, both complex-alias clauses, and the
underlying analytic RS-to-actual-block derivation remain unproved.  No
`BlockMomentLimits` instance is constructed and no frozen rung status
changes.

## 36. A2 R1a allocation-capacity no-go gate

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.R1aAllocationCapacity \
  RH.Zeta85.Discharge.R1aAllocationNoGo RH.Zeta85.Main
lake env lean comparator/PrintAxioms/R1aAllocationNoGo.lean
python3 verify/r1a_allocation_nogo.py
diff -u verify/r1a_allocation_nogo.out \
  <(python3 verify/r1a_allocation_nogo.py)
bash verify/check_axioms.sh
```

The capacity module proves the two exact active-cell profile caps, an
abstract finite contradiction, and both frozen rational gaps.  The NoGo
module derives every finite hypothesis from the current
`PrincipalCyclicBlock` fields using the almost-everywhere reconstruction
identity, exact full-profile scaling, the distinguished energy-ratio limit,
and the degree-one zero-shift translated-product limit.  It proves
`no_principal14999` and `no_principal19999` for arbitrary `ZeroConfig` and
every value of the corresponding exact family type.

The dedicated printer selects seven public theorems and is included in the
generic standard-three loop in `verify/check_axioms.sh`.  Every normalized
line is exactly `[propext, Classical.choice, Quot.sound]`.
`RH.Zeta85.Main` imports the module.  The targeted/Main build, printer,
exact-output diff, full axiom gate, source scans, and `git diff --check` all
exit zero.

The independent verifier copies the raw polynomial and frozen family
constants, then reconstructs both profile integrals, active edges,
Bernstein-basis monotonicity certificates, capacity sides, and strict gaps
with integer arithmetic and `fractions.Fraction`.  The gaps are derived, not
hardcoded.

The exact artifact hashes are:

```text
c5d5d0f8fd939a97477189ceedeef0d3af112894b246bbe44fe377cad393c6d2  RH/Zeta85/Discharge/R1aAllocationCapacity.lean
7a53acb3a61e1af357a10dab696e70a472b321400a325ca553d423b33c5737db  RH/Zeta85/Discharge/R1aAllocationNoGo.lean
368a1907abcbcb0ba6c874ddb218fa3df4e9663dfc0352dee4fef9bb3ae1953e  comparator/PrintAxioms/R1aAllocationNoGo.lean
03454e0c3ba7dee4037e658836299459c4a91c03ea1f7921d51a6421a209f4fc  docs/audit/r1a_allocation_nogo.md
866b8275b81b6bc49ea63b2d6fb60a7df4335a0a45fcd13f206e6f95cda47143  verify/r1a_allocation_nogo.py
ea2d1f902975651b6b23c58195568401f9e2f9e14bb72bc17be52ce525c1fc96  verify/r1a_allocation_nogo.out
```

This gate does not change any frozen theorem statement or constant.  The
quartic theorem declarations remain conditional implications, but their
current `PrincipalCyclicBlock` premise is formally uninhabited for both
exact family types.  No valid current-interface construction exists.

## 37. B-4 eta-superposition support-model gate

The formal and independent gates are:

```bash
lake build RH.Zeta85.Discharge.EtaSuperpositionObstruction RH.Zeta85.Main
lake env lean comparator/PrintAxioms/EtaSuperpositionObstruction.lean
python3 verify/b4_eta_superposition_obstruction.py
diff -u verify/b4_eta_superposition_obstruction.out \
  <(python3 verify/b4_eta_superposition_obstruction.py)
bash verify/check_axioms.sh
```

The Lean module proves the generic no-supported-divisor convolution lemma,
its scale-free prime-square specialization, and the concrete
`eta=3/4`, `T=625`, `n=899` regression.  The balanced `[25,50]` box model
has coefficient two at 899, whereas every finite signed superposition with
all first supports in `[5,10]` vanishes there.  It also proves that the
retained balanced positive progression majorant misses trace by exactly
`eta` in `PQ` and `eta - 1/2` in `PH`.

The dedicated printer selects twelve public theorems and is included in the
generic standard-three loop in `verify/check_axioms.sh`.  Every normalized
line is exactly `[propext, Classical.choice, Quot.sound]`.
`RH.Zeta85.Main` imports the module.  The targeted/Main build, printer,
exact-output diff, full axiom gate, source scans, and `git diff --check` all
exit zero.

The independent verifier uses only integer arithmetic and
`fractions.Fraction`.  It enumerates all ordered divisors of 899, reconstructs
the three exact boxes and both supported-pair lists, and recomputes the `PQ`
and `PH` excesses.  It does not verify a logarithmic budget; the cited
`C<1` threshold is supplied by the existing `LogBudget`/`EtaClosure`
theorems.

The exact artifact hashes are:

```text
5d21ff3339fa654268dd84821ddc1dacd67320b6d75e6bb217fb9dd8e4cfd73c  RH/Zeta85/Discharge/EtaSuperpositionObstruction.lean
06f6d413afbf765dae6e40c6a919192f779fa7187e6613ac50919d6146b29570  comparator/PrintAxioms/EtaSuperpositionObstruction.lean
d4ed1194ea882921581ee3e08f2430df1aa4e451fd1cff1c2f9f3206a8fac9cd  docs/audit/eta_superposition_obstruction.md
343f2a70ae558f83be9529b3f5864478b5245ad6326fdaaee9717ecf9055a965  verify/b4_eta_superposition_obstruction.py
373ba96868de9bc757c0d181d1e2f23d8f88a1361b80b0a0cf835f1616ee678d  verify/b4_eta_superposition_obstruction.out
```

This gate does not identify the model coefficient with an actual terminal
Heath--Brown coefficient, kill `(EF_eta)`, or assert `(HD_eta)`.  The exact
survivor remains the actual-coefficient per-`Y` estimate
`|R_HD(Y,T,eta)| << Y(log T)^C` with `C<1`, after the signed `h`-sum and
actual zero-mode subtraction but before the outer dyadic `Y`-sum.  A1 and
every frozen-rung status remain unchanged.
