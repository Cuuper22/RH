# Branch and PR consolidation — 2026-08-18

This document records the salvage of the August 11–13 proof-development campaign
(106 `agent/*` branches, 60 open pull requests, 747 unmerged commits) into a
single validated line, and the disposition of every branch.

## Method

Every decision below is empirical: a branch was kept only if its content merges
into the carrier and the result **builds** (`lake build Zeta23 RH.Zeta85.Main
Solution Solution.Multiplicity Solution.XiPrime Solution.Zeta85`) and passes the
repository's own gates (`verify/check_axioms.sh`, placeholder scan). Builds ran
on a DigitalOcean worker pool seeded from the campaign's own build droplet
(`zeta-lean`), on a clean-room from-scratch worker, locally, and in GitHub CI.

## The carrier

The consolidated line is the union of the two surviving programs:

1. `agent/diagonal-lower-bound-transfer` (242 commits) — the annular/diagonal
   normalization line. Supersedes its near-twin
   `agent/aligned-virtual-channel-frame` (all but one deleted doc line
   contained, +1,313 further lines) and transitively contains the
   `prove-window-cost-*`, `prove-bblr-*` and `isometric-*` chains.
2. `agent/guarded-poisson-tails` (145 commits) — the Rudnick–Sarnak
   height-decay line, the only branch with a green GitHub CI run at its tip
   (2026-08-13 03:49Z). Roughly 91 of its commits (the RS height machinery)
   appear nowhere in the diagonal line.

The union merge resolved 22 conflict hunks in 6 files; see the merge commit
message for the per-file resolution policy. Three late experiment branches with
novel declarations were folded on top (each is the maximal element of a
declaration-nested family):

- `agent/smooth-core-window` (⊇ `core-radial-shell-alias`, `-family`, `-targets`)
- `agent/collective-frozen-profile` (⊇ `collective-energy-profile`)
- `agent/annular-weighted-fourier` (⊇ `routed-energy-normalization`)

## What the consolidated line achieves over `main`

(As recorded at consolidation time; the axiom-collapse items were subsequently
reversed — see the addendum at the end of this document.)

- Four of the six named analytic hypotheses of the 85% layer are **proved** and
  removed as axioms: `bblr_error_bound`, `bblr_poisson_blocks`,
  `windowCost_101`, `windowCost_125`. At consolidation time
  `RH/Zeta85/Hypotheses.lean` declared a single axiom, `shiu_majorant` —
  a state the addendum below records as unsound and reversed.
- At consolidation time every extension rung R-679 … R-9506 compiled
  conditional on that single axiom; the `Family14999`/`Family19999`
  `PrincipalCyclicBlock` premises were removed from the headline path.
  (Reversed by the addendum: the closed R-8657 … R-9506 headlines were
  vacuous and are deleted; the quartic implications keep their four explicit
  structure premises.)
- Comparator statements `zeta85_rung_8657/8686/9383/9506` (dyadic and
  cumulative) were registered in `comparator/config-zeta85.json` and are
  de-registered again by the addendum.
- README and AXIOMS.md were maintained by the line itself.  VALIDATION.md was
  **not**: it kept its pre-consolidation four-axiom text (stale line numbers,
  per-rung dependency sets contradicting the collapsed AXIOMS.md §1.1), and
  `comparator/config-zeta85.json` kept three ex-axioms in `permitted_axioms`.
  Both are reconciled by the addendum's rewiring.

## Branch disposition

Categories (full per-branch list in the consolidation PR):

- **Merged via this consolidation (carrier + folded, 26 branches)** — the two
  carrier lines, the three folded experiment tips, and the 18 branches whose
  tips are ancestors of the result, plus the three subsumed members of each
  folded family. Closed as merged; tips preserved via the keep-alive ref.
- **Superseded snapshots (20 branches)** — mid-chain PR heads whose diff
  against the carrier adds zero novel declarations (typically an 8-line tweak
  the line later rebased or rewrote). Closed unmerged.
- **Dead ends (~60 branches)** — lines the campaign itself abandoned or that
  conflict with the surviving program. Includes the whole `rs-*` sharp-top-hat
  family: the campaign's own bisect harness (`rhverify/` on the build droplet)
  recorded every one of its last 25 commits failing with 3–6 errors, and its
  final CI run (2026-08-13 04:06Z) is red. Closed unmerged.
- **`audit/rh95-extension-20260810` (PR #1)** — an audit of a pre-campaign
  proposal, based 37 commits behind current main. Closed as historical.

Every deleted branch tip is preserved through the keep-alive ref
`archive/campaign-20260813`: a parent-only commit whose 108 parents are the
exact final commits of every removed branch, with the branch-to-commit table
in its commit message (`git log -1 archive/campaign-20260813`).

## Finishing the frontier

The carrier's last-day files (the aggregate/virtual-channel program) had never
compiled anywhere — the campaign died mid-construction. Consolidation finished
them: roughly thirty repairs across twelve files, each verified by rebuild.
Recurring defect classes, recorded for future campaign configuration:

- **Data-carrying `Prop` structures** (5 structures in 4 files): regularity
  records holding `commonPeriod`/`supportRadius` functions were declared
  `: Prop`, which cannot generate projections. De-Propped; their constructors
  became `def`s.
- **Swallowed subtractions** (5 theorem/def statements): `∫ u, f u - tail` and
  `∑ r, a * ∫ ... - tail` parse with the subtraction inside the binder body.
  Parenthesized to the intended reading.
- **Uninferable implicit/explicit arguments**: field notation on
  `fullLength`/`supportedFullProfile` (whose `include F` is inert on defs),
  simp rewrites whose key variable occurs only on the right-hand side,
  `(κ :=)`/`(q :=)`/`(F :=)` pins, and one application-precedence bug
  (`f x.of_le (by ...)` passes the projection and the tactic block as separate
  arguments).
- **Mathlib drift**: `Set.indicator_of_not_mem` → `Set.indicator_of_notMem`,
  `integral_congr` → `integral_congr_ae`, order-coercion proofs through
  `WithTop ℕ∞` (`(WithTop.coe_le_coe).2`), `integral_complex_ofReal`.
- **Tactic-level regressions at the twins' tip**: three proofs where
  `agent/aligned-virtual-channel-frame` held the working form and
  `agent/diagonal-lower-bound-transfer` had regressed it.

`RH/Zeta85/Discharge/SmoothRadialShell.lean` (an experiment leaf imported by
nothing in the CI cone) still contains unfinished work in its second half
(~34 outstanding errors, including references to nonexistent measure-theory
API) and is left unwired; its front half was repaired here. It is removed
from the targeted `bridge` workflow's build list until completed.

## Verification evidence for the consolidated tip

- Warm incremental build + gates on the campaign's build image (worker
  `zeta-clone`).
- From-scratch clean-room build + gates (worker `cleanroom-01`).
- Independent local build of the diagonal carrier.
- GitHub CI on the consolidation branch.

The campaign's own final verification (2026-08-13 07:12–09:46Z, preserved in
`rhverify/` on `zeta-lean`) had identified `agent/poisson-tail-expansion` as
its last fully certified state; that commit is an ancestor of the carrier.

## Addendum — honest-core rewiring (2026-08-18)

The consolidation's final axiom collapse — down to a single axiom, as its
commit title records — was unsound and has been reversed.  The single surviving axiom asserted the frozen interface
`ShiuMajorant`, which this repository itself refutes:
`RH.Zeta85.not_shiuMajorant_quarter` (`RH/Zeta85/Discharge/ShiuNoGo.lean`)
proves `¬ ShiuMajorant (1/4)`, so `shiu_interface_contradiction : False` was
derivable and every theorem routed through it — both signed-pair trace grades,
`traceTransfer_saturated`, `windowCost_125`, and the eight closed
R-8657 … R-9506 headlines — was a vacuous `False`-elimination.

The honest state is restored:

- `RH/Zeta85/Hypotheses.lean` declares **four** axioms — `shiu_majorant₂`
  (the corrected interface `ShiuMajorant₂` of `RH/Zeta85/ShiuInterface.lean`:
  majorant scale `(log P)^C`, modulus range `q ≤ P^(1−η)`, class-uniform
  constants), `signedPair_traceGrade_lt_5_4`, `signedPair_traceGrade_lt_3_2`,
  and `traceTransfer_saturated`.
- `windowCost_125` is again the real proof
  (`RH/Zeta85/Discharge/RationalWindow125Final.lean` and its rational
  certificate chain), not a `False`-elimination.
- The eight vacuous `*_from_shiu_contradiction` headlines are deleted; the
  comparator topic `Zeta85` is back to its eight genuine statements, with
  `permitted_axioms` listing exactly the four axioms above.
- `ShiuNoGo` remains in the build graph as the proved refutation of the old
  interface; it is consistent with the corrected axiom.

See `AXIOMS.md` (intro and §§2–3) for the full record.
