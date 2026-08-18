/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Shiu.lean — root of the Shiu-majorant campaign.

The modules below are the unconditional mathematics built toward `ShiuMajorant₂`
(`RH/Zeta85/ShiuInterface.lean`), the corrected progression-majorant interface.  None of them is
in the headline closure `RH.Zeta85.Main`, and none of them is used by any axiom or rung: they are
free-standing mathematics.  This root exists so that CI elaborates them — it is built by the
bridge job of `.github/workflows/lean-targeted.yml`, deliberately NOT by `RH.Zeta85.Main`, so that
the gate's closure stays exactly the headline cone.

Import graph:

  ProgressionCount      — residue-class counting; the `progressionSum` reduction API
  BoundedCoefficients   — the `k = 0` case of the corrected interface, proved at full range
  TauPointwise          — generalized divisor functions; the keystone `τ_a · τ_b ≤ τ_{ab}`
  TauSummatory          — the `τ_K` summatory ladder, uniform in `K` (incl. the `K!`-sharp form)
  ShortInterval         — interval/AP counting and initial-segment-to-short-interval transfer
  Landreau              — Lay's explicit Landreau inequality at the published constants `(8, 7)`
  MaxCoordinate         — Route 1: sharp-exponent `τ^2`, `τ^4` short-interval bounds (`y` near `x`)
  BrunCore              — Route 3 seed: Bonferroni truncation, `∏(1−1/p) ≤ 1/log z`, rough counts
  AllTheta              — Route 2: the short-interval `τ^4` bound for all `θ > 1/4`, conditional
  AllThetaUnconditional — Route 2 composed: `Landreau` discharges `AllTheta`'s hypothesis
  ProgressionRoute2     — Route 2 in progressions: the interface's own shape for `q ≤ N^{3/4}`
  MajorantQuarter       — `ShiuMajorant₂ η` PROVED for every `η ≥ 1/4`

The last of these is the campaign's headline: the interface that `Hypotheses.lean` assumes for
all `η ∈ (0, 1/2)` is a theorem on `η ≥ 1/4`.  The axiom survives only for `η ∈ (0, 1/4)`, where
the modulus band runs past `P^{3/4}`.

See `docs/research/shiu_routes_20260818.md` for the route analysis and
`docs/audit/vacuity_20260818.md` for what this campaign replaced.
-/
import RH.Zeta85.Shiu.ProgressionCount
import RH.Zeta85.Shiu.BoundedCoefficients
import RH.Zeta85.Shiu.TauPointwise
import RH.Zeta85.Shiu.TauSummatory
import RH.Zeta85.Shiu.ShortInterval
import RH.Zeta85.Shiu.Landreau
import RH.Zeta85.Shiu.MaxCoordinate
import RH.Zeta85.Shiu.BrunCore
import RH.Zeta85.Shiu.AllTheta
import RH.Zeta85.Shiu.AllThetaUnconditional
import RH.Zeta85.Shiu.ProgressionRoute2
import RH.Zeta85.Shiu.MajorantQuarter
