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
RH/Zeta85/Hypotheses.lean:87   axiom bblr_error_bound : BBLRErrorBound
RH/Zeta85/Hypotheses.lean:119  axiom bblr_poisson_blocks : BBLRPoissonBlocks
RH/Zeta85/Hypotheses.lean:151  axiom shiu_majorant : …
RH/Zeta85/Hypotheses.lean:185  axiom signedPair_traceGrade_lt_5_4 : …
RH/Zeta85/Hypotheses.lean:232  axiom signedPair_traceGrade_lt_3_2 : …
RH/Zeta85/Hypotheses.lean:266  axiom windowCost_101 : …
RH/Zeta85/Hypotheses.lean:291  axiom windowCost_125 : …
RH/Zeta85/Hypotheses.lean:335  axiom traceTransfer_saturated : …
```

Eight legacy declarations, all in the single file `RH/Zeta85/Hypotheses.lean`.  This is the
reproduced pre-mission state, not the target standard.  (The two `axiom`
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

Output reproduced verbatim in `AXIOMS.md` §1.  Summary: each of the eight statements depends on
`propext`, `Classical.choice`, `Quot.sound` and on four of the eight axioms of
`RH/Zeta85/Hypotheses.lean` — the two lower rungs on
`{bblr_error_bound, signedPair_traceGrade_lt_5_4, windowCost_101|windowCost_125,
traceTransfer_saturated}`, the 85 % statements on
`{bblr_poisson_blocks, shiu_majorant, signedPair_traceGrade_lt_3_2, traceTransfer_saturated}`.
Nothing else appears.

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

with `comparator/config-zeta85.json` as shipped (it lists the eight `RH.Zeta85.Hypotheses` axioms in
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
on the eight named axioms, and `comparator/config-zeta85.json` lists those axioms in
`permitted_axioms`.  This is the only such topic in the repository; the base four files
(`Challenge.lean`, `Solution.lean`, `config.json`, `PrintAxioms.lean`) and the topics `Multiplicity`
and `XiPrime` are untouched and remain unconditional.  A reader auditing the 85 % claim must read
`RH/Zeta85/Hypotheses.lean` in addition to `comparator/Challenge/Zeta85.lean`.  The exception is a
current deficiency to discharge, not an accepted endpoint for the new mission.

## 8. Numerical cross-checks performed outside Lean

Recorded in `FINDINGS.md` §4 (exact-rational verification of the whole Phase-A certificate chain, and
double-precision verification of the two transcendental window costs).  The Phase-A chain is *also*
proved inside Lean, so its external check is only corroboration; the two transcendental costs are
axioms precisely because their external check could not be internalized.

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
lake build Zeta23 RH.Zeta85.Main Solution.Zeta85
bash verify/check_axioms.sh
```

`verify/check_axioms.sh` extracts the expected 56 lines for the eight compiled
Zeta85 headlines from `AXIOMS.md` §§1.1–1.3 and performs an exact diff against
fresh Lean output.  It then runs the four base `PrintAxioms` audits.  A final
source scan rejects proof-level `sorry` and `admit` outside the comparator
challenge files.

The workflow and extraction logic were inspected locally; this environment has
no Lean executable, so the authoritative build result is the GitHub-hosted run
triggered by the Phase 0d commit.  Phase 0c's DigitalOcean reproduction was
waived explicitly by the user and was not performed.

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

This is a source-and-derivation audit, not a Lean discharge.  It adds no
declaration, axiom, or `Inputs95` field.  The nine remaining formal
bridges are listed verbatim in `FINDINGS.md` §16 and
`docs/audit/rs_reduction.md` §9.

## 14. B-1 stability proof

`RH/Zeta85/Stability.lean` is imported by
`RH/Zeta85/Main.lean`.  The CI build target
`lake build Zeta23 RH.Zeta85.Main Solution.Zeta85` therefore checks
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
