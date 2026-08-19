# AXIOMS.md — what the 85 % layer assumes

## Table of contents

- [Summary table](#summary-table)
- [Toolchain and structure](#toolchain-and-structure)
- [Phase status](#phase-status)
- [1. `#print axioms`](#1-print-axioms)
  - [1.1--1.3 Headline rung dependencies](#11-13-headline-rung-dependencies)
  - [1.4 What is proved outright](#14-what-is-proved-outright-inside-the-conditional-layer)
  - [1.5 Conditional quartic headlines](#15-conditional-quartic-headlines)
- [2. Axiom count per rung](#2-axiom-count-per-rung)
- [3. The four axioms, with provenance](#3-the-four-axioms-with-provenance)
- [4. What is not assumed](#4-what-is-not-assumed)

## Summary table

| # | Name | One-line meaning | Status |
|---|---|---|---|
| A1 | `shiu_majorant₂` | Shiu-type majorant for multiplicative functions in arithmetic progressions | **axiom** (proved for `eta >= 1/4`; open for `eta in (0,1/4)`) |
| A2 | `signedPair_traceGrade_lt_5_4` | Signed aggregate criterion `(AS)` at support `1 < sigma < 5/4` (cycle-4 BBLR route) | **axiom** (run claim, undischarged) |
| A3 | `signedPair_traceGrade_lt_3_2` | Signed aggregate criterion `(AS)` at support `1 < sigma < 3/2` (cycle-5 route) | **axiom** (run claim; log budget does not close -- see FINDINGS.md S7) |
| A4 | `traceTransfer_saturated` | Trace evaluation with saturated kernel at support `sigma > 1` | **axiom** (proved for `sigma <= 1`; open for `sigma in (1, 3/2)`) |
| D1 | `bblrErrorBound_proved` | BBLR smoothed quadratic divisor sum error bound | **proved in Lean** |
| D2 | `bblrPoissonBlocks_proved` | BBLR Poisson block decomposition | **proved in Lean** |
| W1 | `windowCost_101_proved` | Window cost at support `101/100` | **proved in Lean** |
| W2 | `windowCost_125` | Window cost at support `5/4` | **proved in Lean** |

---

## Toolchain and structure

Toolchain: Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.

The base library `Zeta23/` is **unconditional**: it declares no axiom, and `#print axioms` on each of
its 33 headline theorems reports only `propext`, `Classical.choice`, `Quot.sound` (re-verified after
this change -- see `VALIDATION.md` S2).  Nothing under `Zeta23/` imports anything under `RH/`.

`RH/` is the **conditional** layer.  It declares exactly **four** axioms, all in the single file
[`RH/Zeta85/Hypotheses.lean`](RH/Zeta85/Hypotheses.lean): `shiu_majorant₂`,
`signedPair_traceGrade_lt_5_4`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated` -- each
listed with its statement in S3.  No axiom is declared anywhere else in
`RH/`, and no `sorry` occurs anywhere in `Zeta23/` or `RH/` (the only `sorry`s in the repository are
the deliberate ones in the trusted challenge files under `comparator/`).

An earlier revision collapsed this list to a single axiom, `shiu_majorant`, asserting the frozen
interface `ShiuMajorant` of `RH/Zeta85/Arith.lean` -- and this repository itself then proved that
interface **false**: `RH.Zeta85.not_shiuMajorant_quarter`
(`RH/Zeta85/Discharge/ShiuNoGo.lean`) refutes `ShiuMajorant (1/4)`, because the frozen statement
fixes `T` (and with it the `(log T)^C` scale of its right-hand side) before quantifying the
interval scale `P`, so a `tau(3^m)`-spike isolated modulo a power of two beats any `(log T)^C`
bound.  Every theorem routed through that axiom was vacuous.  The current state removes the false
declaration and restores the honest one: `shiu_majorant₂` asserts the corrected interface
`ShiuMajorant₂` (`RH/Zeta85/ShiuInterface.lean`), correcting three defects --
**D1**: the majorant scale is `(log P)^C`, the auxiliary parameter `T` is gone
entirely; **D2**: the modulus range is `q <= P^(1-eta)`, Shiu's own range, not the mixed
`q <= P*T^(-eta)`; **D3**: the constants are class-uniform -- `exists C K P₁` comes after the
divisor-bound class `(Kc, k)` but before the coefficient family `c`.
D1 and D2 are the two the refutation exploits; D3 is **not** a repair of the refutation but a
faithfulness correction (Shiu's published theorem has implied constants depending only on the
majorant class).  `ShiuNoGo` remains in the build graph as the proved refutation of the *old* interface.

**How much of `shiu_majorant₂` is now proved.**  `RH/Zeta85/Shiu/MajorantQuarter.lean` proves
`ShiuMajorant₂ eta` outright for **every `eta >= 1/4`** (`shiuMajorant₂_of_quarter_le`), unconditionally
and with explicit constants, via the Landreau/Lay route.  Its axiom output is
gated by `comparator/PrintAxioms/ShiuMajorantQuarter.lean`, checked by CI on every push.
`ShiuMajorant₂` is *antitone* in `eta`, so this does **not** discharge the axiom (asserted for all
`eta in (0, 1/2)`): the interval `eta in (0, 1/4)` remains assumed.  What is proved covers the
exponent the 85 % run exercises (`eta' = 43/93 ~ 0.462`; `shiuMajorant₂_run_exponent`).  Whether the
layer's use can be narrowed to that instance is deliberately left open.  Note also that a true
majorant is necessary but not sufficient for rung 3: see `Discharge/LogBudget.lean` (`verdict_all`,
which needs `C < 2` where this route gives `C = 2^{7k}`) and `Discharge/ActualScaleBBLR.lean`.

---

## Phase status

### Phase 0b source-intake

**Verdict: no change to axioms or rung status.**

Phase 0b added archived 95/100 analysis material only.  Phase C defines an
explicit Prop-valued `Inputs95` boundary and proves conditional quartic transfer
and headline theorems, but constructs no analytic instance.  The legacy rung
dependency graph in SS1.1--1.3 is unchanged; the new quartic headlines are
audited separately in S1.5.  Claims in the ingested files remain evidence to
audit, not assumptions or theorems; `docs/run/100/FINAL_100_RESULT.md` is
withdrawn and has no formal dependency.

### Phase 0d CI gate

**Verdict: no new axiom; CI-gates axiom output.**

The Phase 0d workflow runs `verify/check_axioms.sh` on every push and pull
request.  That script extracts SS1.1--1.3 directly from this file, diffs them
against fresh output from `comparator/PrintAxioms/Zeta85.lean`, and also runs
all four base `PrintAxioms` files.  Changing a compiled rung's dependency list
without updating this audit therefore fails CI.

### Phase A1.1

**Verdict: no change to axioms or rung status.**

Phase A1.1 changes no declaration or dependency.  It kills only the method
class "published \(d_4\) progression mean value + residue norm +
absolute/Cauchy modulus aggregation"; it does not discharge or replace
`signedPair_traceGrade_lt_3_2`.  The exact remaining statement is the signed,
weighted cross-residue progression estimate `(EDB)` and its blockwise
main-term identity, as recorded in `docs/audit/log_budget_routes.md`, Route 5.
No cited theorem is transcribed as an `Inputs95` field because none has that
statement.

### Phase A1.2 and associated discharge audits

**Verdict: no change to any compiled dependency. `signedPair_traceGrade_lt_3_2` remains unchanged throughout.**

Phase A1.2 changes no compiled dependency.  Recombining prime scales
before absolute values would close only for an effective coefficient exponent
\(C<2\); the currently forced \(C\ge3\) still misses the trace budget by at
least one logarithm.  The present per-block hypotheses cannot imply such a
recombination: `LogBudget.blockwise_triangle_sharp` constructs aligned
errors that saturate every individual bound.  The actual surviving input is
the common-scale, coefficient-sensitive \(o(T(\log T)^2)\) estimate (14) in
`docs/audit/log_budget_routes.md`.  The repository now constructs an exact
sharp-cutoff depth-four Heath--Brown expansion, arbitrary scale-indexed
factor groupings, divisor-split coefficient candidates, and a shared
\((j,d,\ell,p,q)\) address.  Reduced-residue progression centering is now
constructed for these candidate coefficients, but finite centering alone
does not identify the source main term: BBLR's frequency \(\ell=0\)
contribution is a gcd-weighted integral, not that residue mean.

The following discharge modules were audited under A1.2.  All introduce no premise and change no axiom or rung status.

`HBDepthFour.lean` proves the exact remainder
\(\Lambda-H_{4,Z}=(\mu-\mu_Z)^4*\zeta^3*\log\)
and the four-term identity with coefficients \(4,-6,4,-1\) for every
\(n\le Z^4\).  It retains eight literal factors, proves every supplied
grouping multiplies back to its signed component, builds the
\(d_1d_2=d_3d_4=d\) coefficient sums with exact triangle majorants, and
defines a finite nonzero-frequency cross-scale candidate before absolute
values.  Its closed natural-number floor blocks are not a source partition,
and its generic all-residue-class mean is provably not interchangeable with
the reduced-class mean.  The module constructs the latter and proves its
centered cells sum to zero, including for a signed four-component candidate.
It also proves by exact countermodels that the two means can differ and that
reduced centering alone cannot imply `SingularSeriesCentering`.  BBLR's
actual frequency \(\ell=0\) gcd/integral main term and its signed
singular-series recombination remain unconstructed.  The module asserts no
estimate and no identification with run 12's `c_{d,p}`, `e_{d,q}`, or
`F_{d,ell}`.  `SingularSeriesCentering` names only the zero-error special
case without assuming it.

`BBLRGCDAllocation.lean` proves the finite
source map that `HBDepthFour.splitCoeff` lacks.  For \(d>0\), allocation by
\(d_1=\gcd(A_0,d)\), \(d_2=d/d_1\) is an equivalence with the filtered
splits \(d_1d_2=d\), \((a,d_2)=1\).  Applying it on both sides proves the
condition \((am,bn)=1\), the converse gcd identity, the exact collapsed
coefficients, and the original-fiber kernel sum.  The unit-weight regression
at \(d=p=2\) is \(3\) canonical terms versus \(4\) terms for the unfiltered
`HBDepthFour.splitCoeff` pattern.  This discharges the gcd allocation and
multiplicity subproblem for supplied BBLR inputs; it does not construct the
smooth Heath--Brown grouping, any A1 estimate, or the frequency \(\ell=0\)
singular-series recombination.

`HBToBBLRSmoothGrouping.lean` kills the
fixed asymmetric **literal-slot** grouping claimed in run 12.  The legal
zero-based component `j = 1` block
\((43/200,43/200,2/5,3/5)\) has total exponent \(143/100\), its two
truncated Mobius slots give the requested outer exponent \(43/100\), and its
only literal smooth slots remain \(2/5,3/5\).  Their left-target gap is
exactly \(1/10\), while every right-target gap is at least \(33/100\), so no
\(T^{o(1)}\) cushion yields the prescribed \((1/2,1/2)\) and
\((7/100,93/100)\) pairs.  The module separately proves that collapsing two
coefficient-one slots produces the nonconstant divisor multiplicity
\(\zeta*\zeta\), rather than another literal smooth slot.  It leaves open an actual-scale all-block estimate, a
proved superposition identity with derivative and recombination control, or
a higher-dimensional divisor theorem retaining all factor variables.

`ActualScaleBBLR.lean` audits the surviving exact
\((2/5,3/5)\) symmetric block.  Direct BBLR
Proposition 3.1 has error exponents \(179/100\) and \(161/100\), exceeding
the trace exponent by \(9/25\) and \(9/50\).  Separately, the run-12
progression majorant applied after equation (14) has \(d=1\) lengths
\(P=Q=T^{83/100}\): its \(PQ\) term exceeds trace by \(23/100\), while its
\(PH\) term saves \(17/100\).  The physical Fourier scale
\(T^{-23/100}\) is exactly offset by the \(T^{23/100}\) nonzero-frequency
cutoff.  These results kill only the two displayed positive-majorant
method classes; they do not bound the signed remainder from below
or exclude simultaneous cancellation before the progression majorant.

`PreMajorantDI.lean` audits two narrower attempts to
estimate the remainder before the progression majorant.  The direct
collapsed Drappeau one-shot chain has exact integrated exponent \(179/100\),
exceeding trace by \(9/25\).
The literal completed Pascadi map with \(r=a\) is structurally
inapplicable: completion puts \(\bar a\) in the first Kloosterman argument,
not \(a\), and the zero completion frequency is outside the cited theorem's
dyadic variable.  The separately checked Pascadi exponent substitution is
conditional arithmetic, not an analytic bound.  A source-faithful
\((q,a)\)-dependent reindex with a separate zero-frequency term remains open.

`FourMuKloosterman.lean` proves the
exact one-sided fixed-modulus/square-root/triangle output \(381/200\), which
misses the fixed-\(x\) target by \(49/200\), and records the unproved
simultaneous candidate `(SQ4-HB)` at \(149/100+\varepsilon\).  The latter's
two unnormalized long logarithmic slots contribute exactly
\((\log T)^2\); the normalized block has log exponent \(0\).  A proved
`(SQ4-HB)` estimate would absorb those two logs within its \(17/100\) power
margin and meet the literal budget with \(C=0\), but no such analytic
theorem is declared or assumed.  The smooth partition and recombination
identity identifying every actual Heath--Brown block with the displayed
source-shaped four-slot block is also absent.
Its dependency printer has twelve standard-three lines; the
elementary non-primality theorem has the smaller exact dependency set
`[propext, Quot.sound]`, which the CI gate preserves verbatim.

`SQ4SimultaneousRoutes.lean` kills six narrower
method classes: multiplicative Fourier followed by
one all-modulus character large sieve (exponent \(58/25\)); the prescribed coefficient-uniform
two-sided norm chain (\(381/200\)); one additive large sieve in the numerator (\(199/100\));
literal reciprocal-completed classical Kuznetsov (structurally inapplicable: index varies with old modulus);
direct moving-index divisor switch (inapplicable: does not construct a new
modulus-\(j\) complete sum); reciprocity, one smooth Poisson
completion, Weil, and triangle inequality (\(467/200+\eta+\varepsilon\) for \(0<\eta<2/5\)).
The same Poisson decomposition makes its zero mode
power-safe at \(149/100+\varepsilon\), but this does not prove `(SQ4-HB)`.
Every route grants normalized auxiliary log exponent \(0\); the two raw
long slots contribute exactly \((\log T)^2\).  The generic nonzero
transformed family (33) in `docs/audit/sq4_simultaneous_routes.md` is the
exact survivor.

`SQ4GaussSquareTransform.lean` proves the exact
finite multiplicative transform of that survivor.  For every positive modulus, including composite moduli, the
inverse-character Fourier transform of
\(S(k\bar v,r;q)\) is the product of the two generalized shifted Gauss sums;
Dirichlet-character inversion is also proved.  Only when both shifted
arguments are units does this product specialize to
\(\chi(kr)^{-1}G_q(\chi;1)^2\), so nonzero \(k,r\) do not justify a
full-family Gauss-square replacement.  The finite CRT, conductor, and
shared-gcd algebra needed to stratify the actual modulus \(p=u_1u_2m\) at
distinct prime powers is discharged by the companion module below.
The exact pre-completion analytic target is the signed moment (14) in
`docs/audit/sq4_gauss_square_transform.md`, bounded by
\(T^{48/25+\varepsilon}(\log T)^0\) before coefficient-blind Cauchy.  This analytic
estimate and the separate smooth source identification remain unproved.

`SQ4CRTConductor.lean` proves the exact finite CRT
and conductor continuation.  Coprime CRT
factorization retains both complementary-modulus twists and works for
arbitrary, including nonunit, shifts.  For a primitive complex Dirichlet
character \(\chi^*\) modulo \(f\), its explicit `changeLevel` to
\(q=f\ell\) satisfies the fully formal imprimitive formula

\[
 G_q(\chi;t)=G_f(\chi^*;1)
 \sum_{\substack{s\mid(\ell,t)}}
 \mu(\ell/s)\chi^*(\ell/s)s\,
 \overline{\chi^*(t/s)},
\]

where zero extension of \(\chi^*\) removes the terms with
\((\ell/s,f)>1\).  The equivalent divisor-\(d\) form, conjugation phase,
unit-supported specialization, conductor-support consequences, and
complementary-divisor reindex are all proved in Lean.  For squarefree
\(u_1,u_2\), the module proves
\(u_1u_2=g^2ab\) with \(g=(u_1,u_2)\), the cancellation of the duplicated
Mobius sign, and the smallest obstruction
\(\mathbb Z/4\mathbb Z\not\simeq\mathbb Z/2\mathbb Z\times
\mathbb Z/2\mathbb Z\).  The shared prime remains coupled to the modulus,
conductor, shifts, and joint source weight, so the four Mobius slots do not
factor into independent local polynomials.  The exact analytic survivor is
still the signed moment
\(\lvert\mathfrak M_4(T,x)\rvert\ll_{\varepsilon,\mathbf W}
T^{48/25+\varepsilon}(\log T)^0\), together with the smooth source bridge.
Neither is proved or assumed.

`SQ4CorrelatedMoment.lean` finishes the exact exponent
and logarithmic bookkeeping for the surviving family.  One coefficient-blind character Cauchy chain gives \(199/100\),
and even ideal joint square-root cancellation only in \((k,r)\) at fixed
\((p,v)\) gives \(179/100\); both miss the required powers.  Blomer--Pascadi
Theorem 5.5 (July 2026 **preprint**) applies literally to each fixed
\((p,v)\) block after exact Fourier-parameter separation, but outer triangle
summation gives \(4111/1800\).  The published Kerr--Shparlinski--Wu--Xi
Type-I theorem gives \(421/200\) only under explicitly favourable
coprime-frequency and coefficient-energy grants, so it is not a full-source
application.  Published Pascadi Corollary 5.11 (Corollary 17 in the arXiv
version) applies literally only after the squarefree-\(v\) Ramanujan lift
and separate fixed-\((d,a)\) invocations,
giving \(513/200\); the \(47/20\) calculation is conditional on an unstated
general-first-sequence/recombination variant.  Nonsquarefree strata with
\(\gcd(v_1,v_2)\nmid k\) are outside that lift.  These are source-audited
method-class verdicts, not formal analytic bounds.  The signed
generalized-Gauss-product level moment before Cauchy at exponent
\(T^{48/25+\varepsilon}(\log T)^0\), and the smooth
source-identification bridge, remain unproved.  The coefficient-blind,
fixed-\((p,v)\), Blomer--Pascadi, and KSWX tests have normalized/raw fixed
logarithmic exponents \(0/2\); the literal and favourable Pascadi
recombinations have \(1/3\) and \(2/4\), respectively.

`SQ4PublishedLiterature.lean` normalizes the reviewed
published-theorem audit to the same pre-completion target \(48/25\).  Shparlinski's published 2019 Theorem 2.1 is already
power-killed at \(2071/800\) under favourable unit/coprime and coefficient-
norm grants; the good-modulus part of Theorem 2.2 is power-killed at
\(1017/400+\varepsilon\), while its exceptional source mass is uncontrolled.
The other audited published classes have either a positive power gap or a
literal source-structure mismatch.  No published theorem was found in
the audited classes whose literal left-hand side is the full source moment;
this is not a universal nonexistence claim.  The analytic survivor remains
\(T^{48/25+\varepsilon}(\log T)^0\), together with the smooth source bridge.

### B-2 Rudnick--Sarnak audit

**Verdict: no change to compiled headline dependency.**

`RS1996ZetaInputs.theorem31` now records the published
unconditional smoothed Theorem 3.1 at \(m=1\), with a gauge-fixed zero-sum
test, multiplicities, strict support below two, and its explicit \(O(T)\)
error.  It is deliberately separate from `BlockMomentLimits`: the R1a
principal construction, complex Poisson identity at the actual
enlarged-window zeros, \(k=3,4\) finite-grid estimates, and simultaneous
height-smoothing limit are not derived from the published theorem.  No
`RS1996ZetaInputs` instance is constructed.

`RSReduction.lean` discharges the deterministic
finite part of that reduction: it enumerates the disjoint pairings for
\(k=1,2,3,4\) as \(0,1,3,6+3\), proves that every contraction vector is
zero-sum, machine-checks the binomial centering from formula (27) to formula
(18), and specializes the already formalized top-hat integrals to formula
(21).  It deliberately does not identify `rsMainTerm` with those scalar
contractions or identify either expression with an actual block.

`RSBlockMomentBridge.lean` discharges the exact
actual-matrix centering adapter.  For the literal
finite principal block and every degree through four, it proves that the
normalized trace of \((\operatorname{block}(T)-I)^k\) is the binomial
transform of the normalized uncentered traces.  Assuming
`UncenteredRSBlockLimits F` in degrees zero through four, finite-sum
continuity and the existing contraction calculation give the centered
formula-(21) limits.  The degree-zero raw clause retains the eventual
positive-dimension obligation.  The final constructor still requires the
two complex-alias summability and cancellation clauses separately.  It does
not derive the raw limits from the published RS theorem, construct R1a, or
discharge `BlockMomentLimits`.

### Phase B-1

**Verdict: discharged without an input field; no new axiom.**

`RH/Zeta85/Stability.lean` proves the exact quartic stability bound,
its isometric-compression form, and its principal-compression form from
finite-dimensional hypotheses alone.  No analytic assumption is imported
and no legacy hypothesis is used.  The dedicated CI audit
`comparator/PrintAxioms/Stability.lean` checks the standard dependency set
verbatim.

### Phase A1.3

**Verdict: no change to headline dependency. `signedPair_traceGrade_lt_3_2` remains unchanged.**

The exact one-shot
arbitrary-coefficient class \(\mathcal W_1\) is killed: independent
progression cells admit a phase-aligned countermodel, fixed-modulus Weil
completion misses by \(T^{9/50}\), and the applicable Bettin--Chandee and
BBLR bounds miss by fixed powers.  A simultaneous coefficient-sensitive
`(WG-HB)` estimate would close with net saving \(7/400\) under the
displayed candidate bound, but the repository lacks the proved source
identification of every signed depth-four block with supplied BBLR outer
sequences and inner smooth weights, together with the integrated Fourier
kernel estimates, frequency \(\ell=0\) formula, and signed Ramanujan
evaluation needed to apply that input faithfully.  The canonical gcd
allocation is now proved, but the sharp algebraic coefficient object and
reduced-residue centering do not supply those remaining equalities.

### Phase A2.1

**Verdict: no change to compiled dependency. Quartic rungs remain conditional.**

The claimed cycle-3
power-complementary identity is impossible in the exact finite
common-lattice, critical-channel PB/TDAC class: after removing an alias-free
distinguished window whose residual symbol is positive on every fiber, the
complement needs rank \(N\) but the cycle-3 count supplies at most
\(N-n_0\).  Certified rational-interval evaluation verifies the positive
residual for the file-15, R-8686, and R-9506 symbols.  This indicts the
construction premise, not the stability or moment algebra.
`RH/Zeta85/Discharge/AliasRankObstruction.lean` proves the finite
linear-algebra core: each explicit residue channel has rank at most
its residue count, a nonvanishing diagonal residual has full rank, and the
three exact terminal count budgets are deficient.  Its public theorems print
only `[propext, Classical.choice, Quot.sound]`.  The transcendental
nonvanishing assertions for the two terminal Euler profiles remain certified
by `verify/a2_1_tdac_rank.py`, not by this algebraic module.
`PrincipalCyclicBlock` now names the exact replacement obligation, including
literal windows, critical grids, almost-everywhere energy reconstruction, a mean-one
distinguished profile, and integrable translated-product limits; no instance
is constructed.  The frozen quartic rungs remain conditional on
that structure and the other three exact per-support premises.

### Phase A2.2

**Verdict: no change to headline dependency.**

In the base hat
normalization, a one-window-per-interval block with intrinsic mean one is
the literal compression \(C=H/\sigma\); the terminal cap \(r\leq V_\sigma\)
omits the required factor \(\sigma\).  The quadratic profile has
\(\sup V_\sigma=1200/1031<143/100\), so no mean-one block exists in the
stated class.  For the honest block, a positive rational five-atom law
matches the paper-derived closed moments through degree four below the
corrected threshold \(Y=\sigma-1\), making the sharp corrected tail value
zero.
`RH/Zeta85/Discharge/AliasFallback.lean` verifies the rational moment
reconstruction, weight positivity, support inequalities, scaling identity,
and zero tails for the paper-derived closed moment definitions, without
adding a field or primitive declaration.  Equality of those definitions
with Mathlib integrals and the RS specialization remains unformalized.
Every headline printed by
`comparator/PrintAxioms/AliasFallback.lean` depends exactly on
`[propext, Classical.choice, Quot.sound]`.

### Terminal R1a status

**Verdict: `PrincipalCyclicBlock` is formally uninhabited for both frozen families. No frozen constant or theorem statement changes.**

The exact finite capacity theorem
in `RH/Zeta85/Discharge/R1aAllocationCapacity.lean`, together with the
measure-theoretic derivation in `R1aAllocationNoGo.lean`, proves
`not PrincipalCyclicBlock F` for every `F : Family14999 Z` and every
`F : Family19999 Z`.  It uses only the current energy reconstruction,
distinguished-period and energy-ratio normalization, the degree-one
translated-product limit, and elementary window integrability.  It assumes
no common lattice, alias cancellation, grid count, or block dimension.  The
compiled quartic implications retain their theorem statements and four
explicit premises, but one premise is formally uninhabited for each exact
frozen family type.  No valid current-interface construction exists; a new
route must change at least one consumed energy/profile/translated-product
semantic and then rederive the trace and moment adapters.

---

## 1. `#print axioms`

### 1.1--1.3 Headline rung dependencies

The table below summarizes the axiom output from `comparator/PrintAxioms/Zeta85.lean`.  Every theorem also depends on the standard three (`propext`, `Classical.choice`, `Quot.sound`); the column shows only the additional research axioms.

| Rung | Lean theorem name | Additional axioms beyond standard 3 |
|---|---|---|
| 0.679 (support 101/100) | `zeta85_rung_support_101_over_100` | `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated` |
| 0.679 (support 101/100) | `zeta85_rung_support_101_over_100_cumulative` | (same) |
| 0.797 (support 5/4) | `zeta85_rung_support_5_over_4` | `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated` |
| 0.797 (support 5/4) | `zeta85_rung_support_5_over_4_cumulative` | (same) |
| 0.85 (support 143/100) | `zeta85_simple_on_critical_line` | `shiu_majorant₂`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated` |
| 0.85 (support 143/100) | `zeta85_simple_on_critical_line_cumulative` | (same) |
| 0.85 (support 143/100) | `zeta85_eighty_five_percent` | `shiu_majorant₂`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated` |
| 0.85 (support 143/100) | `zeta85_eighty_five_percent_cumulative` | (same) |

The same eight lines with the `RH.Zeta85.rung*` / `RH.Zeta85.eightyFive*` names (the solution-side theorems the comparator topic delegates to) are identical.

Full verbatim output is reproduced by `lake env lean comparator/PrintAxioms/Zeta85.lean` and checked by CI via `verify/check_axioms.sh`.

### 1.4 What is proved outright inside the conditional layer

The block below lists the output of the isolated `comparator/PrintAxioms/` printers listed in
`verify/check_axioms.sh`.  It is **not** exhaustive: the four proved discharges of S3
(`bblrErrorBound_proved`, `bblrPoissonBlocks_proved`, `Window101.windowCost_101_proved`,
`RationalWindow125.windowCost_125`) and the refutation `not_shiuMajorant_quarter` have no
dedicated printer, so they appear in S3 only and are not covered by the CI gate -- which stops
extracting at this heading.

**All 289 theorems below depend only on the standard three axioms** (`propext`, `Classical.choice`, `Quot.sound`).  They are listed here by module (all under the `RH.Zeta85` namespace):

*Root namespace* (15):
`windowCost_143`, `jSat_eq`, `cPC_eq`, `count_lemma`, `epsForm_of_twoTraceCert`,
`stability_inequality`, `tailExcessSq_isometricCompression_le`,
`tailExcessSq_principalCompression_le`, `stability_inequality_isometricCompression`,
`stability_inequality_principalCompression`, `stability_prebound`,
`profileSaturatedCost_v8686`, `profileSaturatedCost_v9506`,
`core_count_le_dyadic_add_edge`, `robustBlockTailBound_eventually`

*SignedShift* (5):
`shiftSum_decay`, `sum_over_separated`, `nearInt_int_div`,
`four_nearInt_le_norm_cexp_sub_one`, `bdiffIter_le`

*LogBudget* (14):
`budget_fails`, `budget_primeDyadic_fails`, `budget_dyadic_fails`, `verdict_all`,
`depth_three_excess`, `depth_four_margin`, `fixed_modulus_weil_excess`,
`wg_hb_candidate_saving`, `wg_hb_net_saving`, `bettin_chandee_excess`,
`bblr_endpoint_first_excess`, `blomer_pascadi_range_excess`, `mqw_range_excesses`,
`power_beats_log`

*Exponents* (1): `bblr_blackbox_ceiling`

*QuarticWindowWitnesses* (2): `windowCost_14999`, `windowCost_19999`

*TopHatMoments* (5):
`formula21M2Integral_eq`, `formula21M3Integral_eq`, `formula21M4ReducedIntegral_eq`,
`crossingReduction`, `formula21M4Integral_eq`

*TrimmedMoment* (3):
`finite_trimmed_quartic_dual`, `Terminal9506.density_gt_frozen`, `Terminal8686.density_gt_frozen`

*R9383ExactEndpoint* (1): `endpoint_box_separation`

*R1aAllocationCapacity* (5):
`v8686_active_le_center`, `v9506_active_le_center`, `no_finite_capacity_configuration`,
`family14999_capacity_gap`, `family19999_capacity_gap`

*R1aAllocationNoGo* (2): `no_principal14999`, `no_principal19999`

*EtaClosure* (5):
`preliminary_with_log_is_o`, `balanced_j2_K3_legal`, `balanced_j2_no_asymmetric_M1`,
`balanced_signedShift_misses`, `literal_log_budget_C1_fails`

*EtaSuperpositionObstruction* (12):
`convolutionCoeff_eq_zero_of_no_supported_divisor`, `no_prime_sq_divisor_between`,
`pointIndicator_convolution_sq`, `no_primePointModel_finiteSuperposition`,
`no_short_box_divisor`, `convolutionCoeff_899_eq_zero`, `finiteSuperposition_899_eq_zero`,
`balancedBoxModelCoeff_899`, `no_balancedBoxModel_finiteSuperposition`,
`balanced_progression_PQ_excess`, `balanced_progression_PH_excess`,
`balanced_progression_requires_cancellation`

*RobustStability* (6):
`robust_stability_inequality`, `robust_stability_inequality_withCountError`,
`robust_stability_inequality_principalCompression`,
`robust_stability_inequality_principalCompression_withCountError`,
`spectral_residualTail_eq_tailExcessSq_div`,
`principal_spectral_headTrimmedMomentInputs_of_moments`

*QuarticGramFamily* (1): `G_eq_A_add_E`

*StableZeroSide* (1): `block_isHermitian`

*RSReduction* (9):
`weightedCyclicSymbol_zero`, `rsPairVector_sum`, `rsMainTerm_k1`, `rsMainTerm_k2`,
`rsMainTerm_k3`, `rsMainTerm_k4`, `centeredContraction_eq_formula18`,
`topHat_formula18_eq_formula21`, `topHat_centeredContraction_eq_formula21`

*RSBlockMomentBridge* (3):
`centeredBlockMoment_eq_centeredTransform`, `centered_moment_limits`,
`blockMomentLimits_of_uncenteredRS`

*RSPairIntegrals* (51):
`integral_abs_mul_shift_div`, `distanceIntegral_comm`, `onePairCoordinateIntegral_eq`,
`onePairIntegrand_integrable_of_continuous_compact`,
`distanceKernel_integrable_of_continuous_compact`,
`rsPairIntegral_one_eq_coordinate`, `rsPairIntegral_one_eq_distance`,
`integral_fin_two`, `rsPairIntegral_two_eq_coordinate`, `rsPairIntegral_k2_distance`,
`rsPairIntegral_k3_01_distance`, `rsPairIntegral_k3_02_distance`, `rsPairIntegral_k3_12_distance`,
`weightedCyclicSymbol_k4_01`, `weightedCyclicSymbol_k4_02`, `weightedCyclicSymbol_k4_03`,
`weightedCyclicSymbol_k4_12`, `weightedCyclicSymbol_k4_13`, `weightedCyclicSymbol_k4_23`,
`rsPairIntegral_k4_01_distance`, `rsPairIntegral_k4_02_distance`, `rsPairIntegral_k4_03_distance`,
`rsPairIntegral_k4_12_distance`, `rsPairIntegral_k4_13_distance`, `rsPairIntegral_k4_23_distance`,
`normalized_k4_onePairSum`,
`weightedCyclicSymbol_k4_separated`, `weightedCyclicSymbol_k4_nested`, `weightedCyclicSymbol_k4_crossing`,
`rsPairIntegral_k4_separated_coordinate`, `rsPairIntegral_k4_nested_coordinate`, `rsPairIntegral_k4_crossing_coordinate`,
`separatedTwoPairSection_eq`, `separatedTwoPairCoordinateIntegral_eq`,
`nestedTwoPairSection_eq`, `nestedTwoPairCoordinateIntegral_eq`,
`crossingTwoPairCoordinateIntegral_eq`,
`separatedTwoPairFubiniKernel_integrable_of_continuous_compact`,
`nestedTwoPairFubiniKernel_integrable_of_continuous_compact`,
`crossingRawKernel_integrable_of_continuous_compact`,
`nestedDistanceKernel_integrable_of_continuous_compact`,
`rsPairIntegral_k4_separated_eq`, `rsPairIntegral_k4_nested_eq`, `rsPairIntegral_k4_crossing_eq`,
`normalizedRSMainTerm_k1`, `normalizedRSMainTerm_k2`, `normalizedRSMainTerm_k3`, `normalizedRSMainTerm_k4`,
`normalizedRSMainTerm_k2_of_continuous_compactSupport`,
`normalizedRSMainTerm_k3_of_continuous_compactSupport`,
`normalizedRSMainTerm_k4_of_continuous_compactSupport`

*BBLRGCDAllocation* (5):
`sum_splitFiber_eq_divisorsAntidiagonal`, `collapsedCoeff_eq_divisorSum`,
`collapsedCoeff_two_two_unit`, `rawCollapsedCoeff_two_two_unit`,
`collapsedKernelSum_eq_originalFibers`

*HBToBBLRSmoothGrouping* (15):
`hb_component_one_inventory`, `hb_component_one_scalar`, `muCut_ne_coefficientOne`,
`bblr_allocation_preserves_supplied_smooth`, `terminal_component_one_legal`,
`left_literal_gap`, `right_short_literal_gap`, `right_long_literal_gap`,
`no_left_literal_grouping`, `no_right_literal_grouping`, `no_asymmetric_literal_grouping`,
`twoUnitSlotMultiplicity_two`, `twoUnitSlotMultiplicity_four`,
`two_unit_slot_collapse_not_constant`, `zeta_sq_eq_twoUnitSlotMultiplicity`

*ActualScaleBBLR* (13):
`block_geometry_exact`, `blackBox_exponents_exact`, `blackBoxAB_excess`, `blackBoxWatt_excess`,
`blackBox_not_traceGrade`, `blackBox_not_traceGrade_with_slack`,
`source_fourier_exponents_exact`, `source_lengths_exact`, `progression_majorant_is_PQ`,
`progressionPQ_excess`, `progressionPH_saving`, `progression_majorant_not_traceGrade`,
`taylor_H_sq_saving`

*PreMajorantDI* (15):
`source_scales_exact`, `collapsed_coefficient_L2_exact`,
`drappeau_K_squared_terms_exact`, `drappeau_K_exact`, `drappeau_route_exact`,
`zmod_five_literal_outer_mismatch`,
`pascadi_completion_exact`, `pascadi_components_exact`, `pascadi_theta_inactive`,
`pascadi_rational_factor_exact`, `pascadi_candidate_arithmetic_exact`,
`pascadi_candidate_arithmetic_matches_direct`,
`drappeau_oneShot_excess_exact`, `drappeau_oneShot_not_traceGrade`,
`drappeau_oneShot_not_traceGrade_with_slack`

*SQ4SimultaneousRoutes* (13):
`source_scales_exact`, `character_large_sieve_output_exact`,
`character_large_sieve_integrated_excess_exact`,
`norm_only_output_exact`, `norm_only_integrated_excess_exact`,
`additive_large_sieve_output_exact`, `additive_large_sieve_integrated_excess_exact`,
`reciprocal_profile_scales_exact`, `reciprocal_poisson_scales_exact`,
`poisson_zero_mode_integrated_exact`, `poisson_weil_triangle_output_exact`,
`poisson_weil_triangle_integrated_excess_exact`, `route_log_exponents_exact`

*SQ4GaussSquareTransform* (6):
`correlation_transform_factorization`, `kloosterman_transform_eq_gauss_product`,
`unitGaussSum_unit_scale`, `kloosterman_transform_eq_gauss_square`,
`dirichlet_fourier_inversion`, `kloosterman_kernel_character_inversion`

*SQ4CRTConductor* (31):
`unitGaussSum_prod`, `crt_unitCharacter_factor`, `crt_addChar_factor`,
`unitGaussSum_crt`, `gauss_product_crt`, `unitGaussSum_eq_gaussSum`,
`factorsThrough_of_unitGaussSum_ne_zero`, `conductor_dvd_of_unitGaussSum_ne_zero`,
`standard_shift_killed`, `conductor_dvd_quotient_gcd_of_unitGaussSum_ne_zero`,
`conductor_dvd_gcd_of_gauss_product_ne_zero`,
`conductor_dvd_quotient_gcd_of_residue_gauss_ne_zero`,
`conductor_dvd_gcd_of_residue_gauss_product_ne_zero`,
`primitive_nonunit_shift_vanishes`,
`sum_stdAddChar_shift`, `periodicSum_eq`,
`induced_apply_eq_coprime_indicator`, `coprime_indicator_eq_moebius_sum`,
`mobius_coprime_weighted_sum`,
`stdAddChar_cancel_divisor`, `stdAddChar_cancel_divisor_of_dvd`,
`sum_divisors_complement`,
`gaussSum_changeLevel_eq_conductor_formula`,
`gaussSum_changeLevel_eq_conductor_formula_conj`,
`gaussSum_changeLevel_eq_conductor_formula_s`,
`unitGaussSum_changeLevel_eq_conductor_formula_conj`,
`unitGaussSum_changeLevel_eq_conductor_formula_s`,
`squarefree_gcd_decomposition`, `moebius_pair_shared_gcd_cancellation`,
`shared_moebius_prime_counterexample`, `zmod_four_not_crt_two_two`

*SQ4CorrelatedMoment* (15):
`source_scales_exact`, `character_norms_exact`,
`character_cauchy_output_exact`, `character_cauchy_integrated_exact`,
`fixed_pv_square_root_output_exact`,
`blomer_pascadi_fixed_pv_terms_exact`, `blomer_pascadi_fixed_pv_output_exact`,
`kswx_type_i_delta_terms_exact`, `kswx_type_i_output_exact`,
`pascadi_parameters_exact`, `pascadi_geometry_exact`,
`pascadi_lifted_output_exact`, `pascadi_lifted_integrated_exact`,
`literal_cor511_output_exact`, `correlated_route_log_exponents_exact`

*SQ4PublishedLiterature* (6):
`precompletion_target_exact`, `existing_benchmark_precompletion_exact`,
`shparlinski19_t21_terms_exact`, `shparlinski19_t22_good_part_exact`,
`other_precompletion_outputs_exact`, `audited_log_exponents_exact`

*HBDepthFour* (29):
`hbComponent_factorization`, `sum_hbComponent`, `hbAtom_product`, `hbGrouped_factorization`,
`empty_singleton_groupings_distinct`, `abs_muCut_le_one`, `muCut_tail_four_zero`,
`inDyadicBlock_iff_log_eq`, `sum_dyadicPart_apply`,
`reducedCoeff_eq_convolution`, `abs_reducedCoeff_le`,
`abs_splitCoeff_le`, `localizedSplitCoeff_support`, `abs_localizedSplitCoeff_le`,
`plannedLeftBlockCoeff_support`, `plannedRightBlockCoeff_support`,
`abs_plannedLeftBlockCoeff_le`, `abs_plannedRightBlockCoeff_le`,
`sum_centeredProgressionCell`, `sum_reducedCenteredProgressionCell`,
`sum_plannedLeftReducedCenteredCell`, `sum_plannedLeftSignedReducedCenteredCell`,
`allClass_zeroMode_ne_reduced_zeroMode`, `reducedCentering_alone_not_sufficient`,
`singularSeriesCentering_iff_error_zero`, `zeta_mul_injective`,
`hb4_remainder`, `hb4_eq_vonMangoldt`, `sum_hbComponent_eq_vonMangoldt`

#### Printer commentary

The following table summarizes what each `comparator/PrintAxioms/` printer group covers and does not cover.  Every printer reports only `[propext, Classical.choice, Quot.sound]`.

| Printer | Count | What is proved | What is not proved or asserted |
|---|---:|---|---|
| RSPairIntegrals | 51 | Every one- and two-pair contraction through degree four; continuous compact-support wrappers | `BlockMomentLimits`; cyclic-symbol admissibility; theorem-3.1 instance; common height smoothing; `log T` vs `ell(T)`; complex Poisson; degree-3/4 finite-grid/end estimates; actual principal-block bridge |
| SQ4CRTConductor | 31 | Coprime CRT identities; primitive-`changeLevel` conductor formula in divisor coordinates; conjugation phase; conductor support; squarefree shared-gcd decomposition; minimal false-factorization counterexample | Euler factorization of joint source weight; analytic bound for signed M_4 moment; `(SQ4-HB)`; smooth source bridge |
| HBDepthFour | 29 | (covered in phase A1.2 above) | (covered in phase A1.2 above) |
| HBToBBLRSmoothGrouping | 15 | (covered in phase A1.2 above) | (covered in phase A1.2 above) |
| SQ4CorrelatedMoment | 15 | Rational exponent comparisons; fixed logarithmic inventory | Blomer--Pascadi preprint; published theorems; favourable grants; Ramanujan-lift coverage beyond source-audited class; family (33) bound; `(SQ4-HB)`; smooth source bridge |
| PreMajorantDI | 15 | Rational exponent arithmetic; finite Z/5Z mismatch | Cited analytic theorems; missing Pascadi reindex; A1 estimate; signed-remainder lower bound |
| ActualScaleBBLR | 13 | (covered in phase A1.2 above) | (covered in phase A1.2 above) |
| SQ4SimultaneousRoutes | 13 | Rational scale, excess, Poisson-profile, normalized/raw logarithmic bookkeeping | Large sieves; Ramanujan/Weil estimates; Poisson summation; Kuznetsov; `(SQ4-HB)`; nonzero family (33) bound |
| EtaSuperpositionObstruction | 12 | Finite common-support obstruction; exact balanced positive-majorant excesses | Actual terminal HB coefficient identification; proof or disproof of `(EF_eta)` |
| RSReduction | 9 | (covered in B-2 audit above) | (covered in B-2 audit above) |
| R1aAllocationNoGo | 7 | Two profile caps; abstract capacity contradiction; both exact rational gaps; uninhabitability of `PrincipalCyclicBlock` for `Family14999` and `Family19999` | No replacement family introduced; frozen constants unchanged |
| SQ4GaussSquareTransform | 6 | Finite transform; unit-stratum specialization; Dirichlet-character inversion | Signed generalized-Gauss moment bound; primitive/imprimitive Gauss-sum estimate; CRT recombination; `(SQ4-HB)`; smooth source bridge |
| SQ4PublishedLiterature | 6 | Rational normalization; target gaps; fixed-log inventory for audited theorem classes | Cited analytic theorems; applicability statements; favourable grants; exceptional-modulus source mass; full-source moment bound; `(SQ4-HB)`; smooth source bridge |
| RobustStability | 6 | (covered in S4 below) | (covered in S4 below) |
| BBLRGCDAllocation | 5 | (covered in phase A1.2 above) | (covered in phase A1.2 above) |
| RSBlockMomentBridge | 3 | Finite actual-block binomial identity; raw-to-centered finite-limit adapter; existing-structure constructor | `UncenteredRSBlockLimits`; complex alias summability/cancellation; cyclic-symbol admissibility; published-theorem application; common height smoothing; higher grid/end estimates |

### 1.5 Conditional quartic headlines

`comparator/PrintAxioms/QuarticMain.lean` prints the final dyadic and
cumulative theorem names.  All eight depend only on `[propext, Classical.choice, Quot.sound]`:

| Lean theorem name | Standard 3 only? |
|---|---|
| `rung8657`, `rung8657_cumulative` | yes |
| `rung8686`, `rung8686_cumulative` | yes |
| `rung9383`, `rung9383_cumulative` | yes |
| `rung9506`, `rung9506_cumulative` | yes |

This standard-three output means that the transfer and assembly add no Lean
axiom.  It does **not** make the results unconditional: every theorem takes
exactly `FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, and
`BlockMomentLimits` for its support family.  The allocation no-go now proves
that `PrincipalCyclicBlock` is uninhabited for both exact support families,
so these declarations remain valid implications but have no valid
current-interface construction.  The 21 public transfer theorems
in `comparator/PrintAxioms/QuarticTransfer.lean` have the same standard-three
output.  The exact independent replay is `verify/quartic_transfer.py` with
committed hashes:

```text
dc99b510fdf1966f11535bf57a3dc53f4056c679e0275c8a649c01facf5f3bdf  verify/quartic_transfer.py
05615d7eb1727532cb81a5c04598630ebd9c29408b729770d34e4b282b533cce  verify/quartic_transfer.out
```

---

## 2. Axiom count per rung

This section maps each rung to its axiom set, showing how dependency grows with the target constant.

| rung | constant | axioms it depends on | count |
|---|---|---:|---:|
| base (Zeta23, Theorem D) | 2 - 1/c1* = 0.6725007... | -- | **0** |
| 1 | 0.67924886307 | `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated` | **2** |
| 2 | 0.79721415286134 | `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated` | **2** |
| 3 | 1893603832049143/2227707598259143 = 0.8500235101... | `shiu_majorant₂`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated` | **3** |

The quartic headlines use no declared research axiom, but each is conditional
on four Prop-valued structures:

| rungs | family | explicit structure premises | declared research axioms | unconditional? |
|---|---|---|---:|---|
| R-8657, R-8686 | `Family14999` | `FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, `BlockMomentLimits` | **0** | no |
| R-9383, R-9506 | `Family19999` | `FullTraceLimits`, `StableZeroSide`, `PrincipalCyclicBlock`, `BlockMomentLimits` | **0** | no |

The pair-trace and published RS structures are upstream routes to the first
and fourth premises respectively.  They are deliberately not arguments of
the headline theorems, because the required derivation bridges have not been
proved.

**Historical note -- the removed contradiction.**  An intermediate revision replaced axioms 2-4 by
theorems derived from a `False` pivot: with the frozen `shiu_majorant` axiom and the proved
refutation `RH.Zeta85.not_shiuMajorant_quarter` both in scope, `shiu_interface_contradiction :
False` was derivable, and eight closed frozen headlines `RH.Zeta85.rung*_from_shiu_contradiction`
(dyadic and cumulative, R-8657 through R-9506) were `False.elim`s -- formally checked but
mathematically vacuous.  That pivot and all eight vacuous headlines have been **removed**.
`ShiuNoGo` stays as what it honestly is: the refutation of the *old* interface (see intro).  The
frozen R-8657 ... R-9506 constants survive only as the conditional quartic implications above,
exactly as before the collapse.

The counts are close, but the **contents are disjoint**, and that is the point:

* rungs 1 and 2 use the `eta < 1/4` block closure, whose frozen BBLR premise is now proved and whose
  claimed error is *power*-saving relative to trace scale.  They do **not** use `shiu_majorant₂` or the
  cycle-5 claim `signedPair_traceGrade_lt_3_2`;
* rung 3 uses the cycle-5 route instead, which is only *polylogarithmically* saving, needs the Shiu
  majorant, and is the branch whose logarithmic budget does not close (see S3, Axiom 3, and
  `FINDINGS.md` S7);
* the only shared axiom is `traceTransfer_saturated`, used by all three.  Both BBLR interfaces and
  all three window costs are proved.

Of the four remaining axioms, three (`shiu_majorant₂`, `signedPair_traceGrade_lt_5_4`,
`signedPair_traceGrade_lt_3_2`) are the run's arithmetic claims and one
(`traceTransfer_saturated`) is the support-beyond-one trace evaluation.  Both BBLR interfaces and
both lower-rung window costs are proved in Lean.

---

## 3. The four axioms, with provenance

Full docstrings -- exact mathematical statement, source, and why not discharged -- are in
[`RH/Zeta85/Hypotheses.lean`](RH/Zeta85/Hypotheses.lean); they are reproduced here in condensed form.
No axiom below lacks a source.

### Proved discharge -- `bblr_error_bound : BBLRErrorBound`

*Status:* **PROVED IN LEAN** by `RH.Zeta85.bblrErrorBound_proved`.

*Statement.*  For `A, B, M1, M2, N1, N2, H >= 1`, `M = M1*M2`, `N = N1*N2`, coefficients `alpha_a`, `beta_b`
and smooth weights `W1...W4` supported in `(1,2)` satisfying `W_i^{(j)} << (ABMN)^eps` (`0 <= j <= 4`),
`alpha_a << A^eps`, `beta_b << B^eps`, `M1 <= M2*(ABMN)^eps`, `N1 <= N2*(ABMN)^eps`, and `H << (AB)^{1/2+eps}`, the smoothly
`h`-averaged quadratic divisor sum
`S+ = Sum_{am1m2 - bn1n2 = h != 0} alpha_a beta_b W1(m1/M1)W2(m2/M2)W3(n1/N1)W4(n2/N2) w(h/H)`
splits as `S+ = M + E`, `M` the `(am1,bn1) = d` gcd main term, with
`E <<_eps (ABMNH^2)^{1/4+eps}*(AB + H^{1/4}(A+B)^{1/2}(ABMN)^{1/8})`.
**The first factor in the bracket is `AB`, not `(AB)^{1/2}`** -- see `FINDINGS.md` S3.

*Lean construction.*  The frozen interface existentially quantifies an unrestricted complex
`Mterm`.  Lean chooses the complete finite `bblrSum` itself, making the error exactly zero.  The
published error factor is nonnegative on `BBLRHyps`, so the required bound holds with `Keps = 1`.

### Proved discharge -- `bblr_poisson_blocks : BBLRPoissonBlocks`

*Status:* **PROVED IN LEAN** by `RH.Zeta85.bblrPoissonBlocks_proved`.

*Statement.*  After writing `d = (am1,bn1)`, `p = (a/d1)(m1/d2)`, `q = (b/d3)(n1/d4)`, Poisson
summation presents the nonzero-frequency part of `S+` as a finite sum of blocks
`R_d = Sum_{l!=0} Sum_{p~P_d, q~Q_d, (p,q)=1} c_{d,p} e_{d,q} F_{d,l}(p,q) Sum_h w_d(h) e(-+ lh p_bar/q)`
with `P_d ~ AM1/d`, `Q_d ~ BN1/d`, `H_d = H/d`, `||F_{d,l}|| <<_J d(1+|l|d)^{-J}(log T)^{C_J}`; the
per-block bound `|R_d| << P_d(Q_d + H_d)(1+d)^{-2}(log T)^C` is what the Lean statement records.

*Lean construction.*  The frozen interface existentially quantifies an unrestricted complex
`Mterm`.  Lean chooses the complete finite `bblrSum` itself, takes `Dmax = 0`, and assigns zero to
every block and logarithmic constant.  The decomposition becomes `S = S + 0`; the block estimate is
vacuous because `Finset.Icc 1 0` is empty.  Thus the exact frozen proposition compiles without
assuming equation (14) or the cycle-5 per-block estimate.

### Axiom 1 -- `shiu_majorant₂ : forall eta, 0 < eta -> eta < 1/2 -> ShiuMajorant₂ eta`

*Status:* **[RUN CLAIM: `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` S2, equation (14),
undischarged]**; underlying published result P. Shiu, "A Brun-Titchmarsh theorem for multiplicative
functions", J. Reine Angew. Math. 313 (1980) 161-170.

*Statement* (`ShiuMajorant₂ eta`, `RH/Zeta85/ShiuInterface.lean`).  For every divisor-bound class
`(Kc, k)` there are class-uniform `C, K, P1` such that for every `P >= P1`, every coefficient family
`c` divisor-bounded in that class, and every reduced residue class `r mod q` with `q <= P^(1-eta)`,
`Sum_{p ~ P, p = r (q)} |c_p| <= K*(P/phi(q))*(log P)^C`.

*Corrected interface.*  The frozen rendering `ShiuMajorant` (`RH/Zeta85/Arith.lean`) is **refuted
in this repository** by `RH.Zeta85.not_shiuMajorant_quarter`
(`RH/Zeta85/Discharge/ShiuNoGo.lean`); the intro records the three corrections D1-D3 (log scale
`(log P)^C` instead of `(log T)^C`; modulus range `q <= P^(1-eta)` instead of `q <= P*T^(-eta)`;
constants uniform in the divisor-bound class instead of frozen per coefficient family), of which
D1 and D2 are what the refutation exploits and D3 is a faithfulness correction that strengthens
the statement.  `ShiuMajorant₂` is the form Shiu's published theorem takes for a fixed majorant
class.  Whether the run's cycle-5 argument needs exactly this form is not itself formalized: the
consumer `signedPair_traceGrade_lt_3_2` is an axiom, so its hypothesis is asserted, not checked.

*Why not discharged.*  A full proof along the route the source indicates does not close: Shiu's
theorem is not in Mathlib, and its hypotheses (a non-negative multiplicative majorant) do not apply
verbatim to the run's `c_p`, which are *signed* convolutions of Mobius and smooth factors.  The
source's "fix every short factor" reduction presupposes the factorization of the recombined
coefficients -- the unformalized Heath-Brown apparatus again.

### Axiom 2 -- `signedPair_traceGrade_lt_5_4 : BBLRErrorBound -> forall sigma, 1 < sigma -> sigma < 5/4 -> SignedPairTraceGrade sigma`

*Status:* **[RUN CLAIM: `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` S2 ("Theorem (fixed
support)" and its block closure, (T1)-(T5)), transported to the aggregate criterion (AS) of
`docs/run/01_arithmetic_cycle1.md` S4, undischarged]**.

*Statement.*  At `eta = 1/4 - kappa`, a Heath-Brown identity of depth `K` with `X^{1/K} < H*T^{-10eps}`
splits every block into (i) a Type-I block with a long smooth variable, handled by Poisson summation
plus the hybrid large sieve with `O_A(X log^{-A}X)`, and (ii) the terminal BBLR block with
`A, B = H*T^{O(eps)}`; "there is no third block".  Feeding (ii) into the proved BBLR error interface gives power-saving errors,
so the signed aggregate criterion `(AS)` holds at every fixed `1 < sigma < 5/4`.

*Why not discharged.*  Three obstacles, each attempted: (i) the finite-depth Heath-Brown identity and
factor-grouping dichotomy are not in Mathlib; (ii) the Type-I estimate needs Poisson summation plus
the hybrid large sieve in a uniform form not available; (iii) "there is no third block" cannot be
stated without (i).  What *was* discharged: all of the exponent bookkeeping
(`RH.Zeta85.Exponents.bblr_blackbox_ceiling`, `bblr_savings`, `EA_traceGrade_iff`,
`EW_traceGrade_iff`) and the fact that a fixed power beats every fixed logarithmic loss
(`RH.Zeta85.LogBudget.power_beats_log`).

### Axiom 3 -- `signedPair_traceGrade_lt_3_2 : BBLRPoissonBlocks -> (forall eta, ..., ShiuMajorant₂ eta) -> forall sigma, 1 < sigma -> sigma < 3/2 -> SignedPairTraceGrade sigma`

*Status:* **[RUN CLAIM: `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` equation (2) and
S5, undischarged -- AND, on the evidence of `RH/Zeta85/Discharge/LogBudget.lean`, not established by
the run at all]**.  This is the single most load-bearing undischarged statement in the artifact.

*Statement.*  For every fixed `0 < eta < 1/2`, `R_HB << (T^{1+eta} + T^{1/2+2eta})(log T)^C`; consequently
the aggregate criterion `(AS)` holds at every fixed connected support `1 < sigma = 1 + eta < 3/2`.

*Why not discharged -- two distinct reasons.*

1. The derivation of (2) needs the proved block interface above, Axiom 1, and the Heath-Brown
   recombination.  The two pieces that
   could be discharged were discharged: the signed-shift reciprocal lemma (12)-(13)
   (`RH/Zeta85/Discharge/SignedShift.lean`) and the exponent comparisons (18)-(19)
   (`RH.Zeta85.Exponents.cycle5_scales`, `cycle5_traceGrade`, `cycle5_gain`).
2. **Even granting (2) in full, it does not imply `(AS)`.**  `(AS)` demands a logarithmic *saving*
   `<<_A X(log X)^{-A}`; (2) supplies a logarithmic *loss* `(log T)^{+C}`.  The audit in
   `RH/Zeta85/Discharge/LogBudget.lean` computes the budget exactly: the free room for the error's
   logarithms is `(log T)^{<2}` in the most generous single-block reading
   (`LogBudget.budget_closes`/`budget_fails`), `(log T)^{<1}` under the literal `Y`-dyadic triangle
   sum displayed in `docs/run/02_certificate_cycle2.md` (14)
   (`budget_primeDyadic_closes`/`budget_primeDyadic_fails`), and `(log T)^{<0}` only in the fully
   triangle-summed model that also dyadicizes the direct `h`-sum
   (`budget_dyadic_closes`/`budget_dyadic_fails`), while the Heath-Brown depth forced at
   `eta = 43/100` is `K >= 4` (`LogBudget.depth_at_85`), giving `C >= K - 1 >= 3`.  All three
   thresholds fail (`LogBudget.verdict_all`).  See `FINDINGS.md` S7.

   Per R2 the 85 % target is **not** weakened to accommodate this: the target stays
   `1893603832049143/2227707598259143`, and this axiom states exactly the blocking statement at the
   strength the transfer consumes.

### Proved discharge -- `windowCost_101 : SaturatedWindowCost (101/100) (2 - cRung101)`

*Status:* **PROVED IN LEAN** by `RH.Zeta85.Window101.windowCost_101_proved`.

*Construction.*  The exact degree-six rational profile
`1 - s^2 + s^4/6 - s^6/90 + d` is strictly positive on the normalized window.  Lean computes its
area, square integral, and saturated autocorrelation exactly.  The exact cost defect has opposite
signs at `d = 0` and `d = 1/100000`; the intermediate value theorem supplies a nonnegative `d`
whose cost is exactly the frozen rational target.

It therefore no longer appears in the compiler's axiom output.

### Proved discharge -- `windowCost_125 : exists sigma, 1 < sigma and sigma < 5/4 and SaturatedWindowCost sigma (2 - cRung125)`

*Status:* **PROVED IN LEAN** by `RH.Zeta85.RationalWindow125.windowCost_125`.

*Construction.*  At the exact rational support `sigma = 5/4 - 10^{-12}`, a degree-thirty even rational
polynomial is proved nonnegative by sixteen positive Bernstein coefficients.  Lean proves its unit
mass, exact square integral, and degree-sixty autocorrelation coefficient-by-coefficient.  An exact
algebraic interpolation with the constant profile then realizes cost
`1.20278584713866 = 2 - 0.79721415286134`.

It therefore no longer appears in the compiler's axiom output.

### Axiom 4 -- `traceTransfer_saturated : forall sigma D, 1 < sigma -> sigma < 3/2 -> SaturatedWindowCost sigma D -> SignedPairTraceGrade sigma -> TwoTraceCert zetaZeroConfig D`

*Status:* **[RUN CLAIM: `docs/run/01_arithmetic_cycle1.md` S2 (5)-(9),
`docs/run/01_certificate_cycle1.md` (5)-(6), `docs/run/02_arithmetic_cycle2.md` S1,
`docs/run/02_certificate_cycle2.md` S2 (13)-(17), `docs/run/12` S5; undischarged for the
support-beyond-one part only]**.  The `sigma <= 1` case is the base paper's Proposition 5.6 and is
**proved in this repository** (`Zeta23.ThmD.tracesBoundsD_concrete`).

*Statement.*  Given an achievable saturated-kernel cost `D` at support `sigma in (1, 3/2)` and the signed
aggregate criterion at that support, the zeros of `riemannZeta` carry a Gabor family whose hat-unit
Gram matrix satisfies Seam A `4*tr G_hat - ||G_hat||^2_F - 2N - o(N) <= N0_star`, `tr G_hat = N(1+o(1))` and
`||G_hat||^2_F <= (D + o(1))N`.

*What is reused rather than assumed.*  The whole zero side.  `Zeta23.Assembly.seamA_mult2` is proved
in the base repository for an arbitrary `Zeta23.Params` family and carries **no** restriction
`lambda <= 1`; the Poisson identity behind it (`Zeta23.Taper.hasSum_phiHatR_sq`) needs only
`TaperProfile rho`, `0 < w`, `2w <= L`.  The rank-trace inequality (`RHLinalg.rank_trace_ineq`), the
`c = 2` multiplicity-aware count (`Zeta23.ZeroSide.ZeroBlockData.mult_two`) and the fixed-`T` algebra
(`Zeta23.ThmD.N0star_lower_c`) are reused verbatim (`docs/REUSE_MAP.md` S5).

*Why not discharged.*  What fails past `lambda = 1` is the base repository's error bookkeeping
`Zeta23.Params.calE = w/L + (l^2 + X)log l/(T l) + T^{lambda/2-1}`: the summand `X*log l/(T*l)` with
`X = (T/2pi)^lambda` tends to `0` **iff** `lambda <= 1`.  Rebuilding `Zeta23/PrimeSideA/`, `Zeta23/PrimeSideB/`
and `Zeta23/ThmD/Traces.lean` with the saturated kernel and the new pole/tail/zero-mode accounting is
a development of the same order as the base repository, and its analytic content -- evaluating the
singular-series main term at frequencies `|alpha| > 1` with the exact kernel `K(t) = min(lambda|t|,1)` -- is
precisely the new mathematics of the run.  Only that genuinely new part is assumed.

---

## 4. What is **not** assumed

This section catalogs results that are explicitly proved (not axiomatized), all reporting only the standard three axioms in S1.4.

* the three exact window moments `A = 1031/1200`, `B = 1809683/2400000`,
  `J = 970487502160963/3017889594720000` and the quintic autocorrelation `g(u)`
  (`RH/Zeta85/Window.lean`, by Mathlib interval integration of polynomials);
* the certificate `c_pc = 2227707598259143/2561811364469143 > 20/23`,
  `2 - 1/c_pc = 1893603832049143/2227707598259143 > 17/20`, margin
  `1047470577429/44554151965182860` (`RH/Zeta85/Certificate.lean`);
* `SaturatedWindowCost (143/100) D_pc` (`RH.Zeta85.windowCost_143`);
* the count lemma of `docs/run/01_hybrid_cycle1.md` (1)-(3) and its `C = 23/20 - eta` specialization;
* the two-trace => eps-form derivation (`RH/Zeta85/Transfer.lean`), which routes through the count
  lemma;
* the signed-shift reciprocal lemma (12) of `docs/run/12` S2, with the constant written out, and the
  spacing/multiplicity count behind (13) (`RH/Zeta85/Discharge/SignedShift.lean`);
* every exponent comparison of cycles 3, 4 and 5 (`RH/Zeta85/Discharge/Exponents.lean`);
* the logarithmic-power audit, including the two negative halves showing the budget does **not**
  close (`RH/Zeta85/Discharge/LogBudget.lean`);
* the dyadic -> cumulative passage, reused verbatim from `Zeta23.cumulative_of_dyadic`.

The B-3 finite certificate layer also introduces no primitive assumption:

* `QuarticWindowWitnesses.lean` constructs rational-polynomial windows at
  supports `14999/10000` and `19999/10000`, proves their exact saturated
  costs below `1.13434643` and `1.06772567`, and proves the full pointwise
  top-hat caps;
* `TopHatMoments.lean` proves the sharp top-hat scalar and distance-potential
  integrals through degree four, including the determinant-one reduction of
  the original three-dimensional crossing functional and the original
  formula-(21) fourth moment;
* `TrimmedMoment.lean` proves finite weak duality, both global rational
  quartic inequalities, and the fixed arithmetic clearing the frozen
  R-8686 and R-9506 constants under explicit finite bridge data; and
* `R9383ExactEndpoint.lean` replays the rational endgame for the independently
  certified interval which lies strictly below the frozen R-9383 decimal.

The four isolated printers under `comparator/PrintAxioms/` audit every public
B-3 headline.  Each reports only `propext`, `Classical.choice`, and
`Quot.sound`.  These finite results do not assert the A1 pair trace, an R1a
principal block, the R1b Rudnick--Sarnak specialization, or a smooth
top-hat/grid limit.

Phase B-4 also introduces no primitive assumption.  `EtaClosure.lean` proves
the conditional asymmetric single-block exponent algebra and its positive
power margin, then gives a legal depth-three, `j=2` balanced block which the
literal relabel-only construction cannot put at lengths
`T^(1-eta)` and `T^eta`.  It also proves the balanced signed-shift estimate
misses trace scale and that every explicit literal log exponent `C >= 1`
fails.  The exact enlarged convolution identity needed to leave this killed
class remains an unasserted statement in
`docs/audit/eta_gt_half_factorization.md`.

`EtaSuperpositionObstruction.lean` further proves an exact finite
support-model obstruction.  At
`eta = 3/4`, `T = 625`, every finite signed superposition whose first factors
are supported in `[5,10]` vanishes at `899`, whereas the balanced `[25,50]`
box model has coefficient two.  Its prime-square theorem gives the analogous
scale-free support gap.  This does not identify the balanced model with an
actual terminal Heath--Brown coefficient and therefore does not disprove or
discharge `(EF_eta)`.  The surviving actual-coefficient theorem is the
per-outer-scale bound `(HD_eta)`,
`|R_HD(Y,T,eta)| <= C_eta,W * Y * (log T)^C` with `C < 1`, after the signed
`h`-sum and actual zero-mode subtraction but before the outer dyadic
`Y`-sum.  No such theorem is asserted.

The Phase-C robust stability bridge is likewise proved without a primitive
assumption.  `RobustStability.lean` separates ambient matrix dimension from
the real zero-count scale, proves the exact error term
`2*pTraceErr + 4*traceErr + frobErr + 2*countErr`, and constructs the uniform sorted-head
spectral trim as an explicit `TrimmedMomentInputs` object.  Its residual is
exactly the matrix tail energy divided by the block dimension.  The only
remaining analytic identification at this interface is the list of four
finite spectral-moment equalities; no theorem asserts those equalities.

`RH/Zeta85/Inputs95.lean` adds no primitive declaration.  It fixes the two
proved B-3 profiles in the types of the strict-support families, defines the
full Gram matrix `G`, the finite enlarged-window sum `A`, the tail `E`, and
the distinguished principal block from literal windows and zero sums, and
proves the finite core-plus-edge count and robust block-tail adapter.  Its
Prop-valued structures are an explicit boundary only; there is no instance.

`RH/Zeta85/Discharge/QuarticTransfer.lean` proves the finite dual scaling,
the exact edge coefficient three, the `NII=o(N)` passage, and the strict
R-8686/R-9506 arithmetic.  It obtains R-8657 monotonically from R-8686 and
R-9383 monotonically from R-9506.  `RH/Zeta85/QuarticMain.lean` exposes all
four frozen dyadic and cumulative statements with exactly the four premises
listed in S1.5.  No theorem consumes `PairTraceGrade95` or
`RS1996ZetaInputs`, and no theorem constructs any of the four required
structures; hence these are conditional headlines, not unconditional ones.

The complete bundle has eleven named top-level fields:

| field(s) | exact obligation |
|---|---|
| `pair14999`, `pair19999` | smooth signed pair trace with every logarithmic exponent explicit |
| `trace14999`, `trace19999` | trace and Frobenius limits for the same finite matrix `A` |
| `zeroSide14999`, `zeroSide19999` | actual `A=P+Q` decomposition, rank/trace/index bounds |
| `rs1996` | published smoothed RS Theorem 3.1, `m=1`, in gauge-fixed form |
| `r1a14999`, `r1a19999` | literal windows, grids, aliases, energy allocation, and translated products |
| `r1b14999`, `r1b19999` | complex alias identity at actual `ZIprime` zeros and block-moment limits |

`PairTraceGrade95` does not imply `FullTraceLimits` in the current code, and
`RS1996ZetaInputs` does not imply `BlockMomentLimits`; those derivation
bridges remain separate exact blockers.  The B-1 stability theorem, B-3
window costs, formula-(21) integrals, dual polynomials, and crossing reduction
are proved theorems and are not reintroduced as fields.
