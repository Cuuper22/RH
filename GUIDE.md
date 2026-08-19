# Guide to the Zeta23 repository

This guide explains what this repository contains, how it is organized, and where to find things. For the formal theorem statements and build instructions, see [README.md](README.md).

## What this repository proves

This repository contains a machine-checked proof, written in the Lean 4 theorem prover, that **at least two thirds of the nontrivial zeros of the Riemann zeta function lie on the critical line** (the line Re(s) = 1/2 in the complex plane). The proof builds on Mathlib (Lean's mathematical library) and verifies every analytic input from scratch — nothing is assumed beyond Lean's three standard logical axioms. A conditional extension layer attempts to push the proportion to 85%, but that layer rests on four explicit unproved assumptions and does not yet meet the unconditional standard.

## The three layers

The codebase is organized into three independent layers, each with its own trust boundary:

### 1. `Zeta23/` — the unconditional base (319 Lean files)

This is the core of the project. It contains complete, sorry-free proofs of the paper's Theorems A through E:

- **Theorem A**: At least 2/3 of zeros are on the critical line
- **Theorem B**: At least 2/3 are simple and on the line
- **Theorem C**: At least 5/6 of zeros are distinct
- **Theorem D**: Optimal Montgomery-Taylor window variants of A-C
- **Theorem E**: Analogues of A-D for Dirichlet L-functions

Every theorem here depends only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No external analytic result is assumed — Weil's explicit formula, the Riemann-von Mangoldt zero-counting formula, Stirling estimates, Chebyshev-Mertens prime sums, and the Montgomery-Vaughan inequality are all proved from Mathlib definitions.

### 2. `RH/` — the conditional 85% extension (154 Lean files)

This layer attempts to prove that 85% or more of zeros are on the critical line. It introduces exactly **four axioms** (unproved assumptions), all declared in the single file `RH/Zeta85/Hypotheses.lean`:

| Axiom | What it asserts | Status |
|---|---|---|
| `shiu_majorant_2` | A corrected Shiu-type progression-majorant bound | Proved for eta >= 1/4; open for eta < 1/4 |
| `signedPair_traceGrade_lt_5_4` | A signed-pair trace-grade bound at support < 5/4 | Open |
| `signedPair_traceGrade_lt_3_2` | A signed-pair trace-grade bound at support < 3/2 | Open |
| `traceTransfer_saturated` | A saturated trace-transfer statement | Open |

An earlier version of this layer collapsed to a single axiom (`shiu_majorant`) that the repository itself then proved **false** — see `RH/Zeta85/Discharge/ShiuNoGo.lean`. The current four-axiom state is the honest replacement. No extension rung currently meets the unconditional target standard.

### 3. `comparator/` — the trust boundary (45 Lean files)

This layer implements the Lean FRO's `comparator` verification protocol. It cleanly separates:

- **Trusted side** (`Challenge.lean`, `Challenge/`): States theorems with `sorry` placeholder proofs, using only Mathlib definitions
- **Untrusted side** (`Solution.lean`, `Solution/`): Proves the same statements by delegating to `Zeta23` or `RH`
- **Axiom audit** (`PrintAxioms.lean`, `PrintAxioms/`): Runs `#print axioms` to verify no hidden dependencies

The comparator ensures that the statements proved by the untrusted code exactly match what the trusted side claims.

## Project history

The project unfolded in several campaigns, all documented in `docs/run/`:

1. **The 85% campaign** (files 01-12): Started from the accepted two-thirds paper and extended the prime-side trace construction to support > 1. Discovered and corrected an error in the BBLR bound (cycle 3 vs. cycle 4). Reached 85% at support 143/100 and a limiting checkpoint of 86.57% as support approaches 3/2. See [docs/run/NARRATIVE_85.md](docs/run/NARRATIVE_85.md).

2. **The 95% campaign** (files 13-24): Extended to quartic trace certificates at support approaching 2. Crossed 95% via a nonflat nested-block construction. See [docs/run/NARRATIVE_95.md](docs/run/NARRATIVE_95.md).

3. **The withdrawn 100% campaign** (files in `docs/run/100/`): Attempted to push to density one but the terminal result was found to contain a self-contradiction. The claim is formally withdrawn. Every file in `100/` belongs to this withdrawn program. See [docs/run/NARRATIVE_100.md](docs/run/NARRATIVE_100.md).

4. **The formalization campaign** (106 agent branches, 60 PRs, 747 commits): Translated the research results into Lean. Documented in [docs/CONSOLIDATION.md](docs/CONSOLIDATION.md).

5. **The Shiu campaign** (PRs #63-77): Built out the `RH/Zeta85/Shiu/` module to prove the corrected Shiu majorant for eta >= 1/4. Ongoing at HEAD.

## Directory map

| Path | What it contains |
|---|---|
| `Zeta23/` | Unconditional proof code (Lean 4) |
| `Zeta23.lean` | Root import file for the base library |
| `RH/` | Conditional 85% extension code (Lean 4) |
| `RH.lean` | Root import file for the extension layer |
| `comparator/` | Trust-boundary verification code and configs |
| `docs/` | All documentation beyond the top-level files |
| `docs/audit/` | Per-topic audit memos (24 files) |
| `docs/run/` | Research run logs, grouped by campaign |
| `docs/run/100/` | The withdrawn 100% research fork |
| `docs/research/` | Standalone research memos |
| `verify/` | Python verification scripts and their recorded output |
| `.github/workflows/` | CI configuration |

### Top-level files

| File | Purpose |
|---|---|
| [README.md](README.md) | Formal theorem statements, status table, build instructions |
| [GUIDE.md](GUIDE.md) | This file — how to navigate the repository |
| [FINDINGS.md](FINDINGS.md) | Where the source documents were wrong, imprecise, or unprovable |
| [AXIOMS.md](AXIOMS.md) | What the 85% layer assumes and why |
| [VALIDATION.md](VALIDATION.md) | Build and audit record for the 85% layer |
| [AUDIT.md](AUDIT.md) | Verification commands and how to reproduce them |
| `lakefile.toml` | Build configuration (three library targets) |
| `lean-toolchain` | Pins the Lean toolchain version |
| `lake-manifest.json` | Dependency lockfile (Mathlib + transitive deps) |

## Reading order

**If you want to understand what's proved**, start with:
1. [README.md](README.md) — the theorem statements and status table
2. [AUDIT.md](AUDIT.md) — how to verify the claims yourself

**If you want to understand the research journey**, read:
1. This file (you're here)
2. [docs/run/NARRATIVE_85.md](docs/run/NARRATIVE_85.md) — the 85% campaign story
3. [docs/run/NARRATIVE_95.md](docs/run/NARRATIVE_95.md) — the 95% campaign story
4. [docs/run/NARRATIVE_100.md](docs/run/NARRATIVE_100.md) — the withdrawn 100% attempt

**If you want to understand the conditional layer's assumptions**, read:
1. [AXIOMS.md](AXIOMS.md) — the four axioms and their status

**If you want to audit specific topics**, use the index below to find the right file in `docs/audit/`.

**Reference-only files** (you don't need to read these cover-to-cover):
- [FINDINGS.md](FINDINGS.md) — consult the TOC for specific sections
- [VALIDATION.md](VALIDATION.md) — consult the summary table for specific gates
- [docs/run/INDEX.md](docs/run/INDEX.md) — consult for specific run-log files
- [docs/REUSE_MAP.md](docs/REUSE_MAP.md) — which Zeta23 declarations the extension reuses

## Topic index

For topics covered in multiple places, the **canonical reference** is listed first, followed by supporting material.

| Topic | Canonical reference | Supporting material |
|---|---|---|
| **BBLR error correction** | [FINDINGS.md](FINDINGS.md) section 3 | [docs/audit/actual_scale_bblr.md](docs/audit/actual_scale_bblr.md), [docs/audit/bblr_gcd_allocation.md](docs/audit/bblr_gcd_allocation.md), run logs 03 and 08 |
| **Shiu majorant refutation** | [AXIOMS.md](AXIOMS.md) (Axiom 1 section) | [docs/audit/vacuity_20260818.md](docs/audit/vacuity_20260818.md), [docs/research/shiu_routes_20260818.md](docs/research/shiu_routes_20260818.md) |
| **Window cost proofs** | [FINDINGS.md](FINDINGS.md) sections 2, 4 | [VALIDATION.md](VALIDATION.md) section 14 |
| **Withdrawn 100% claim** | [docs/run/100/FINAL_100_RESULT.md](docs/run/100/FINAL_100_RESULT.md) | [verify/withdrawn_100_claim.py](verify/withdrawn_100_claim.py), [docs/run/NARRATIVE_100.md](docs/run/NARRATIVE_100.md) |
| **Trace transfer / signed pairs** | [AXIOMS.md](AXIOMS.md) (Axioms 2-4) | [docs/audit/sq4_correlated_moment.md](docs/audit/sq4_correlated_moment.md), [docs/audit/sq4_simultaneous_routes.md](docs/audit/sq4_simultaneous_routes.md) |
| **Branch consolidation** | [docs/CONSOLIDATION.md](docs/CONSOLIDATION.md) | [docs/run/NARRATIVE_85.md](docs/run/NARRATIVE_85.md) |
| **Log-budget routes** | [docs/audit/log_budget_routes.md](docs/audit/log_budget_routes.md) | [FINDINGS.md](FINDINGS.md) section 5 |
| **Kloosterman / four-mu** | [docs/audit/four_mu_kloosterman.md](docs/audit/four_mu_kloosterman.md) | [FINDINGS.md](FINDINGS.md) section 6 |
| **R1a allocation obstruction** | [docs/audit/r1a_allocation_nogo.md](docs/audit/r1a_allocation_nogo.md) | [docs/audit/r1a_alias_free_fallback.md](docs/audit/r1a_alias_free_fallback.md), [docs/audit/r1a_power_complementary_partition.md](docs/audit/r1a_power_complementary_partition.md) |

## Verification scripts

The `verify/` directory contains 22 standalone Python scripts that independently verify the exact arithmetic used in the Lean proofs, using `fractions.Fraction` (exact rationals) and `mpmath` (for transcendental quantities). Each `.py` script has a matching `.out` file with recorded output. The scripts are grouped by prefix:

| Prefix | Topic |
|---|---|
| `a1_*` | Phase A1 exponent and scale audits |
| `a2_*` | Alias-free scaling, TDAC rank |
| `b3_*`, `b4_*` | Certificate arithmetic, eta-closure |
| `r1a_*` | R1a allocation obstructions |
| `rs_*` | Rudnick-Sarnak pairing bookkeeping |
| `quartic_*`, `robust_*` | Quartic transfer and stability |
| `withdrawn_*` | Disproof of the withdrawn 100% claim |

Run `pip install mpmath==1.3.0` and then `python3 verify/<script>.py` to reproduce any check. The shell script `verify/check_axioms.sh` runs the Lean axiom audit and is called by CI on every push.
