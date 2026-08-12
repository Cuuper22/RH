# Phase-C `Inputs95` boundary

Status: **interface and conditional transfer proved; the current R1a premise
is uninhabited for both frozen family types; no unconditional quartic
headline**.

This note records exactly what `RH/Zeta85/Inputs95.lean` defines and what it
does not prove.  The purpose is to keep every frozen rung attached to one
literal matrix family while the open analytic work remains visible as
Prop-valued structure fields.

## 1. Fixed data

The strict branches are fixed in their types:

| branch | support | block bandwidth | fill | full profile |
|---|---:|---:|---:|---|
| `Family14999` | `14999/10000` | `4999/10000` | `89/100` | `QuarticWindowWitnesses.v8686` |
| `Family19999` | `19999/10000` | `4999/10000` | `83/100` | `QuarticWindowWitnesses.v9506` |

Theorems, rather than fields, rewrite the corresponding saturated costs to
the exact B-3 values `D8686` and `D9506`.  Thus neither a profile nor a cost
can drift while a rung is assembled.

For each height, the displayed channel windows and column addresses define:

* the hat denominator `L * integral (sum_j window_j^2)`;
* the full all-zero Gram matrix `G`;
* the finite enlarged-window sum `A` over `ZIprime`;
* the tail `E = G - A`; and
* the distinguished block as a literal principal compression of `A`.

`G=A+E` is proved by unfolding.  No unrelated matrix witness is accepted.

## 2. Proved finite adapters

The base zero populations give, with no research field,

\[
 s_1(T)+2(s_2(T)+p(T))
 \leq N(T,2T)+N_{II}(T).
\]

If the trace and zero-side structures hold, the proved robust theorem yields

\[
 \operatorname{Tail}_{s_2+p}(\operatorname{block} A)
 \leq s_1-(2-D)N+2e_P+4e_T+e_F+2N_{II}.
\]

The coefficient two on `NII` is the exact count-error coefficient, not an
asymptotic convention.  Hermiticity of the block is derived from the same
decomposition `A=P+Q`.

## 3. Analytic fields

The top-level bundle has eleven fields:

| fields | content | present status |
|---|---|---|
| `pair14999`, `pair19999` | smooth signed pair trace with explicit arbitrary log saving | open A1 |
| `trace14999`, `trace19999` | trace and Frobenius limits for the displayed `A` | open pair-to-matrix bridge |
| `zeroSide14999`, `zeroSide19999` | actual `A=P+Q`, rank, trace-cap, and positive-index bounds | open new-window zero side |
| `rs1996` | published smoothed RS Theorem 3.1, `m=1`, gauge fixed | stated field; no instance |
| `r1a14999`, `r1a19999` | literal windows, critical grids, full-energy reconstruction, real aliases, corrected allocation, and translated products | formally uninhabited for the exact frozen family types under the current interface |
| `r1b14999`, `r1b19999` | complex alias identity on actual enlarged-window zeros and first four block-moment limits | open RS/grid passage |

The pair fields do not imply the trace fields in the current code.  The
published RS field does not imply the R1b fields.  Those are deliberate
separations: citations record provenance, while the missing derivations stay
named blockers.

The internal analytic evaluation of the published RS contraction main term
through degree four is now proved separately in
`Discharge/RSPairIntegrals.lean`.  For a continuous compactly supported
profile its final wrappers derive all Fubini/integrability premises and give
the normalized one- and two-pair formula.  This removes no field here:
`rs1996` still requires the actual theorem instance and `r1b14999`/
`r1b19999` still require admissibility, common height smoothing, the
`log T`/`ell(T) = log(T/2pi)` normalization, complex Poisson, the
degree-three/four finite-grid/end estimates, and identification with the
actual principal block.

## 4. Corrected R1a normalization and capacity obstruction

The distinguished window has period `mu * log(T/2pi)`.  Its energy fraction
in the full system must tend to `mu`, not `mu/sigma`, for the literal
principal block to have mean one in hat units.  `PrincipalCyclicBlock`
therefore requires:

* positive distinguished energy;
* a nonnegative, supported, mean-one local profile;
* almost-everywhere full-energy reconstruction by all windows; and
* integrable, locally uniform `L1` convergence of every translated product
  through degree four to the exact top hat of fill `p`.

The translated-product integrability clause prevents Mathlib's totalized
integral from making a nonintegrable error estimate vacuous.  No scalar
`L1` convergence is used to infer a fourth moment.

The companion audit `docs/audit/r1a_allocation_nogo.md` now proves that these
requirements are mutually incompatible for both exact family types.  The
degree-one translated-product limit puts at least \(99/100\) of the
distinguished normalized mass in the active top-hat cell, while the energy
ratio eventually exceeds \(2/5\).  Almost-everywhere reconstruction and the
frozen profile cap give the opposite finite capacity bound.  Exact rational
arithmetic closes the contradiction.  The resulting Lean theorems are
`R1aAllocationNoGo.no_principal14999` and `no_principal19999`.

## 5. Honest status

The module constructs no `Inputs95` value.  More strongly, the allocation
no-go proves that no R1a window system can satisfy the current
`PrincipalCyclicBlock` interface for either exact frozen family type.  It
proves no pair trace or RS-to-grid passage.  The separate proved modules
`Discharge/QuarticTransfer.lean` and `QuarticMain.lean` now assemble dyadic
and cumulative frozen-rung statements, but each theorem takes exactly four
structures for its displayed family:

* `FullTraceLimits`;
* `StableZeroSide`;
* `PrincipalCyclicBlock`; and
* `BlockMomentLimits`.

Thus `rung8657` and `rung8686` are conditional implications on those four structures for
`Family14999`, while `rung9383` and `rung9506` are conditional on them for
`Family19999`; each has a `_cumulative` companion.  R-8657 is a monotone
consequence of the strict R-8686 branch.  R-9383 is a monotone consequence of
the R-9506 branch: the separate flat three-atom route remains invalid because
its exact endpoint lies below the frozen decimal.

`PairTraceGrade95` and `RS1996ZetaInputs` are upstream proposed routes for
proving `FullTraceLimits` and `BlockMomentLimits`; neither is a premise of the
compiled headlines and neither is silently substituted for the required
structure.  Since the required `PrincipalCyclicBlock` structure is formally
uninhabited for both displayed family types, these theorem declarations have
no valid current-interface construction.  They remain conditional
implications, not unconditional headlines.  Any replacement must change at
least one consumed energy/profile/translated-product semantic and rederive
the affected trace and moment adapters.
