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

- Four of the six named analytic hypotheses of the 85% layer are **proved** and
  removed as axioms: `bblr_error_bound`, `bblr_poisson_blocks`,
  `windowCost_101`, `windowCost_125` (and the signed-pair/trace-transfer
  premises are discharged structurally). `RH/Zeta85/Hypotheses.lean` now
  declares a single axiom, `shiu_majorant`.
- Every extension rung R-679 … R-9506 compiles conditional on that single
  axiom; the formerly uninstantiable `Family14999`/`Family19999`
  `PrincipalCyclicBlock` premises are gone from the headline path.
- New comparator statements `zeta85_rung_8657/8686/9383/9506` (dyadic and
  cumulative) are registered in `comparator/config-zeta85.json`.
- README/AXIOMS/VALIDATION were maintained by the line itself and reflect the
  new state.

## Branch disposition

Categories (full per-branch list in the consolidation PR):

- **Merged via this consolidation (carrier + folded, 26 branches)** — the two
  carrier lines, the three folded experiment tips, and the 18 branches whose
  tips are ancestors of the result, plus the three subsumed members of each
  folded family. Closed as merged; tips preserved under `archive/` tags.
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

Every deleted branch tip is preserved as a tag `archive/<branch-name>` so no
commit is lost; `git tag -l 'archive/*'` lists them.

## Verification evidence for the consolidated tip

- Warm incremental build + gates on the campaign's build image (worker
  `zeta-clone`).
- From-scratch clean-room build + gates (worker `worker-golden`).
- Independent local build of the diagonal carrier.
- GitHub CI on the consolidation branch.

The campaign's own final verification (2026-08-13 07:12–09:46Z, preserved in
`rhverify/` on `zeta-lean`) had identified `agent/poisson-tail-expansion` as
its last fully certified state; that commit is an ancestor of the carrier.
