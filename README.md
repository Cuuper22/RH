# Zeta23 — a Lean 4 formalization of "More than two thirds of the zeros of the Riemann zeta function lie on the critical line"

> Research artifact. Not maintained and not accepting contributions.
> A Lean 4 formalization released as a static companion artifact to the paper.

Research update (2026-09-05): a new
[sharpened ordered-moment derivation](docs/research/sharpened_cubic_gain_20260905.md)
gives a proposed **67.2504382097%** bound. The analytic proof and operator
inequality are written out; scalar constants are checked exactly. This is
ordinary mathematical research, not a new fully machine-checked headline.
**85% remains unproved.** The [research record](docs/research/research_20260905.md)
also closes failed certificate classes and records the arithmetic progress.
The continuation derives all finite ordered polynomial moments and a separate
normalized Bezoutian counting certificate; neither supplies the missing 85%
arithmetic estimate. The latest exact profile increment is `1/271803`;
its rational verifier passes. The underlying scalar implication at the
slightly weaker `1/272000` value was also checked through AXLE with only
standard Lean axioms.

## Frozen extension ladder — status at HEAD

**2026-09-05 correction:** the literal `SignedPairTraceGrade σ` predicate is
false for every `σ > 1`: its independently quantified `IV = 0`, with
`w = V = 1`, removes the main term and contradicts a positive-pair lower
bound. Consequently the legacy axiom layer below is mathematically
inconsistent, not merely conditional on an open estimate. This ordinary
mathematical refutation is recorded in the
[current research note](docs/research/research_20260905.md); it has not yet
been formalized in Lean. The separate `Zeta23` base is unaffected.

The target is the unconditional base-repository standard: comparator-validated
headline theorems whose `#print axioms` output is exactly
`[propext, Classical.choice, Quot.sound]` and which have no undisclosed
analytic premise.  The quartic theorem declarations have the standard axiom
footprint and retain four explicit per-support premises.  However,
`R1aAllocationNoGo.no_principal14999` and `no_principal19999` prove that the
`PrincipalCyclicBlock` premise is uninhabited for the two exact frozen family
types.  Thus the compiled conditional implications remain, but there is no
valid construction satisfying their current premises.  They do not yet have
a separate trusted-statement comparator topic.

Lean proves `¬ ShiuMajorant (1/4)` for the frozen progression-majorant
interface (`RH.Zeta85.not_shiuMajorant_quarter`,
`RH/Zeta85/Discharge/ShiuNoGo.lean`).  An intermediate revision kept the
refuted interface as the sole axiom, making the extension layer inconsistent
and its closed R-8657 … R-9506 headlines vacuous `False`-eliminations; that
state has been removed.  The layer now declares four axioms
(`AXIOMS.md` §3), with the corrected interface `ShiuMajorant₂`
(`RH/Zeta85/ShiuInterface.lean` — log scale `(log P)^C`, modulus range
`q ≤ P^(1−η)`, class-uniform constants) in place of the refuted one.

| rung | frozen lower bound | status at HEAD |
|---|---:|---|
| R-679 | 0.67924886307 | **CONDITIONAL ON** `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated`; BBLR error interface and exact window cost proved; compiled headline exists |
| R-797 | 0.79721415286134 | **CONDITIONAL ON** `signedPair_traceGrade_lt_5_4`, `traceTransfer_saturated`; BBLR error interface and exact window cost proved; compiled headline exists |
| R-850 | 1893603832049143/2227707598259143 | **CONDITIONAL ON** `shiu_majorant₂`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated`; BBLR block interface proved; compiled headline exists |
| R-8657 | 0.865674254456636 | **COMPILED CONDITIONAL IMPLICATION; CURRENT PREMISES UNINSTANTIABLE:** takes the four `Family14999` structures, but `no_principal14999` rules out `PrincipalCyclicBlock`; dyadic/cumulative theorem remains, obtained monotonically from R-8686 |
| R-8686 | 0.86855250 | **COMPILED CONDITIONAL IMPLICATION; CURRENT PREMISES UNINSTANTIABLE:** same `Family14999` obstruction; dyadic/cumulative theorem remains |
| R-9383 | 0.938313327050949 | **COMPILED CONDITIONAL IMPLICATION; CURRENT PREMISES UNINSTANTIABLE:** `no_principal19999` rules out the required `Family19999` block; theorem remains a monotone consequence of R-9506, while the direct flat branch is also killed |
| R-9506 | 0.95063832187565 | **COMPILED CONDITIONAL IMPLICATION; CURRENT PREMISES UNINSTANTIABLE:** takes the four `Family19999` structures, but `no_principal19999` rules out `PrincipalCyclicBlock`; dyadic/cumulative theorem remains |

The signed-pair and Rudnick--Sarnak structures remain upstream routes for
proving the trace and moment premises; they are not consumed by these
headlines.  No analytic family instance is constructed, and the current R1a
interface is formally impossible for both frozen family types.  Consequently
no extension rung currently meets the unconditional target standard.  The
unconditional `Zeta23` base remains separate and unchanged.

Repository: <https://github.com/anthropics/zeta-23-lean>.

This repository accompanies the paper "More than two thirds of the zeros of the Riemann zeta function lie on the critical line" (Claude; Anthropic, San Francisco, 2026).
The base `Zeta23` layer contains a complete, `sorry`-free Lean 4 / Mathlib formalization of Theorems A–E of that paper, including proofs
of every analytic input the argument uses (Weil's explicit formula for ζ and for primitive Dirichlet L-functions,
the Riemann–von Mangoldt zero-counting formulas, Stirling-type estimates for Γ′/Γ on vertical lines,
Chebyshev–Mertens prime-sum estimates, and the Montgomery–Vaughan generalized Hilbert inequality). Nothing is
assumed by `Zeta23`: its top-level theorems have no hypotheses, `Zeta23` declares no axioms, and `#print axioms` on each
headline theorem reports only Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound`.

Toolchain: Lean `v4.33.0-rc2`, Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129` (Mathlib's tag `v4.33.0-rc2`; pinned in `lake-manifest.json`).

## What is proved

Write N(T₁,T₂) for the number of zeros ρ of ζ with 0 < Re ρ < 1 and T₁ < Im ρ ≤ T₂, counted with
multiplicity; N₀*(T₁,T₂) for the number of *distinct* such zeros on the critical line Re ρ = 1/2;
N₀ˢ for those that are on the line and *simple*; N_d for the number of distinct zeros; N(T) := N(0,T) etc.
All of these are defined directly from Mathlib's `riemannZeta` and `analyticOrderAt`
([`comparator/ChallengeDeps.lean`](comparator/ChallengeDeps.lean), ≈60 lines, is the complete list of
definitions the statements depend on). "liminf_{T→∞} X(T)/N(T) ≥ c" is formalized in the ε-form
`∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)`. Here c₁* = √2·tan ϑ/(1+ϑ·tan ϑ), ϑ = 1/√2 (= 0.75329…) is the
Montgomery–Taylor constant of Theorem D.

| | statement (as in the paper) | Lean name (modules `Solution` / `Solution.Multiplicity` under [`comparator/`](comparator/)) | underlying Zeta23 theorem |
|---|---|---|---|
| **A** | liminf N₀*(T,2T)/N(T,2T) ≥ 2/3, and liminf N₀*(T)/N(T) ≥ 2/3 | `two_thirds_on_critical_line`(`_cumulative`) | `Zeta23.thmA₀`(`_cumulative`) (`Zeta23/Final.lean`) |
| **B** | liminf N₀ˢ/N ≥ 2/3: at least two thirds of the zeros are simple and on the critical line (dyadic and cumulative) | `two_thirds_simple_on_critical_line`(`_cumulative`) | `Zeta23.thmB₀_mult`(`_cumulative`) (`Zeta23/FinalMult.lean`) |
| **C** | liminf N_d/N ≥ 5/6 (dyadic and cumulative) | `five_sixths_distinct`(`_cumulative`) | `Zeta23.thmC₀_mult`(`_cumulative`) |
| **D** | with the optimal (Montgomery–Taylor) window: liminf N₀*(T,2T)/N(T,2T) ≥ 2 − 1/c₁* (= 0.67250…), the same for N₀ˢ, and N_d: ≥ (3 − 1/c₁*)/2 (= 0.83625…) | `montgomery_taylor_on_critical_line`, `montgomery_taylor_simple_on_critical_line_mult`, `montgomery_taylor_distinct_mult` | `Zeta23.ThmD.thmD₀` (`Zeta23/ThmD/Final.lean`), `Zeta23.ThmD.thmD₀_simple_mult`, `thmD₀_dist_mult` (`Zeta23/ThmD/Mult.lean`) |
| **E** | for every primitive Dirichlet character χ mod q > 1, the analogues of A, B, C and D for the zeros of L(s,χ) (Mathlib's `DirichletCharacter.LFunction χ`) | `dirichlet_two_thirds_on_critical_line`, `dirichlet_two_thirds_simple_on_critical_line`, `dirichlet_five_sixths_distinct`, `dirichlet_montgomery_taylor_on_critical_line`, `dirichlet_montgomery_taylor_*_mult` | `Zeta23.ThmE.thmE_A₀`, `thmE_B₀_mult`, `thmE_C₀_mult`; `Zeta23.ThmDE.thmE_D₀`, `thmE_D₀_simple_mult`, `thmE_D₀_dist_mult` |

Note on Theorem C: in this repository the constant 5/6 is obtained from the rank–trace inequality of §3 applied with
parameter c = 3 (`Zeta23.ZeroSide.ZeroBlockData.mult_three`, `Zeta23/ZeroSide/Mult.lean`); the paper's text derives the
same 5/6 from Proposition 4.5(iii) with c = 2.

Also proved here, beyond the statements of Theorems A–E: the rank–trace certificate ("Lemma R") is TIGHT — for on-line
atoms with integer multiplicities m_j ≤ c on orthonormal vectors together with b pair-blocks of eigenvalue c,
2c·tr(P+Q) − ‖P+Q‖_F² = Σ_j k_c(m_j) + c²·b, i.e. the inequality cannot be improved using only these quantities
(`Zeta23.ZeroSide.TightMult.lemmaR_tight`, `Zeta23/ZeroSide/TightMult.lean`; cited in the paper's appendix).

Also included, beyond Theorems A–E (each group has its own trusted statement file under [`comparator/`](comparator/) or, where noted, is checked with `#print axioms` only):

* **The zeros of ξ′** (`Zeta23/XiPrime/`, comparator topic `XiPrime`, six statements): unconditionally, at least 0.85838 of the zeros of ξ′ (the derivative of the completed zeta function) with ordinates in (T, 2T] are simple and on the critical line and at least 0.92919 are distinct (flat window; 0.86864 / 0.93432 with the quartic window), all zeros of ξ′ lie in the open critical strip, and Re ξ′/ξ > 0 on Re s ≥ 1 — `Zeta23.XiPrime.xiDeriv_simple_on_line`(`_cumulative`, `_quartic_std`) in `Zeta23/XiPrime/Final.lean`. The argument is the one of Theorem B with ξ′ in place of ζ (the rank–trace device applied to the Farmer–Gonek(–Lee)/Montgomery argument for ξ′; Farmer–Gonek, arXiv:0803.0425 = Farmer–Gonek–Lee, J. London Math. Soc. (2) 90 (2014)). In the docstrings under `Zeta23/XiPrime/`, labels of the form `[XF′ Lemma 6.1]`, `[XF′ Thm 8.2]`, `[XF′ (Z3)]` refer to the authors' technical supplement on the explicit formula for ξ′/ξ and the two-trace transfer, which is not included in this repository; these labels record provenance only — what is relied upon is in each case the Lean statement that the docstring introduces. (The counting functions in `comparator/ChallengeDeps/XiPrime.lean` are finite sums / cardinalities over the set of zeros of ξ′ in a height window; that set is finite because every zero of ξ′ lies in the open critical strip — the first of the six statements — and the zeros of an entire function are isolated.)

* **The bandwidth-one ceiling** (`Zeta23/PairCeiling/`, no comparator topic; `#print axioms` audit below): the stability inequality behind the paper's remark on the optimality of the method — for every certificate (c₀, r) of the type used in Theorem B (r ∈ C¹[0,1], r′ differentiable off a countable set with integrable derivative) that is valid against a configuration whose form-factor measure has grid masses s_j and simple-point fraction p, one has c₀ + ∫₀¹ r(x)·x dx ≤ p + |r(1)|·|D(1)| + |r′(1)|·|E(1)| + (sup|E|)·∫₀¹|r″| (`Zeta23.PairCeiling.ceiling_stability`, `Zeta23/PairCeiling/Stability.lean`, two integrations by parts) — and its instance at an explicit 256-periodic law (`Zeta23.PairCeiling.ceiling_law256`, `ceiling_law256_decimal`, `ceiling_nearCUE_signed`, `ceiling_law256_signed`; files `NearCUE.lean`, `RowCert.lean`, `LawN256.lean`, `CeilingLaw256.lean`, `Signed.lean`): every bandwidth-one certificate certifies a proportion of simple zeros at most 0.6818287 + 2.55·10⁻⁶·(|r′(1)| + ∫|r″|). The ONE displayed hypothesis of these theorems is `EnclOK`: that the law's form factor S(j), j = 1…256, lies in the 256 integer enclosures recorded in `LawN256.lean` (obtained outside Lean by interval arithmetic from an exact-rational certificate, sha256 `cc3de9917db4d14d844630a4e97dda8387fd6e257e52b6967f430b8914584eb8`, available from the authors); everything downstream of the enclosures — the 255 near-CUE row inequalities |256·S(j) − j| ≤ 3·10⁻⁴⁰ (0 < j < 256), the edge bound |D(1)| ≤ 0.82395317, the sign of the edge term — is checked in the kernel by `decide` (`LawN256_check`, `LawN256_edge`), and the analytic inequality is proved in Lean.

How the two comparator configurations cover this: [`comparator/config.json`](comparator/config.json) (fifteen statements,
[`comparator/Challenge.lean`](comparator/Challenge.lean)) contains Theorem A together with the *Cauchy–Schwarz forms* of
B–E — N₀ˢ/N ≥ 1/2, N_d/N ≥ 3/4, and with the optimal window 2c₁* − 1 (= 0.50659…) and c₁*, for ζ and for L(s,χ)
(`Zeta23.thmB₀`, `Zeta23.thmC₀`, `Zeta23.ThmD.thmD₀_simple`, … in `Zeta23/Final.lean`, `Zeta23/ThmD/Final.lean`,
`Zeta23/ThmE/Final.lean`, `Zeta23/ThmDE/Final.lean`). [`comparator/config-multiplicity.json`](comparator/config-multiplicity.json)
(twelve statements, [`comparator/Challenge/Multiplicity.lean`](comparator/Challenge/Multiplicity.lean)) contains B–E with the
constants stated in the paper. In this formalization the latter are obtained from the same analytic inputs by the
rank–trace inequality of §3 applied with parameter c = 2 (simple zeros) and c = 3 (distinct zeros) to the
multiplicity-aware zero side (`Zeta23/ZeroSide/Mult.lean`, `Zeta23/Assembly/SeamMult.lean`, `Zeta23/FinalMult.lean`).
The same A–C statements in the Cauchy–Schwarz form, with the same names inside namespace `Zeta23`, are in
[`Zeta23/Unconditional.lean`](Zeta23/Unconditional.lean).

## Layout

```
comparator/          trusted statements (ChallengeDeps, Challenge), untrusted Solution, comparator config — START HERE
Zeta23/Statement.lean  nontrivial zeros, multiplicity, the counting functions, against Mathlib's riemannZeta
Zeta23/Unconditional.lean, Zeta23/Final.lean, Zeta23/FinalMult.lean      Theorems A, B, C (ζ)
Zeta23/ThmD/           Theorem D (the optimal Montgomery–Taylor window; variational problem in ThmD/Functional.lean; ThmD/Mult.lean)
Zeta23/ThmE/           Theorem E (primitive Dirichlet L-functions); Zeta23/ThmDE/: Theorem D for L(s,χ)
Zeta23/LinAlg/         §3 of the paper: Sylvester inertia, rank–trace inequality (via von Neumann), Cauchy–Schwarz count, Weyl
Zeta23/WeilEF/, Zeta23/ExplicitFormula*   Weil's explicit formula (contour integration, Landau's lemma, zero-sum limits)
Zeta23/RvM/            Riemann–von Mangoldt formula (argument principle, Backlund's bound via Jensen, local zero counts)
Zeta23/GammaFacts/, Zeta23/Analytic/   Γ′/Γ estimates on vertical lines (Stirling) and other analysis
Zeta23/Chebyshev.lean, Zeta23/FromPNTPlus/     Chebyshev–Mertens estimates; files ported (with attribution headers) from PrimeNumberTheoremAnd
Zeta23/MV/             Montgomery–Vaughan generalized Hilbert inequality
Zeta23/PrimeSideA/, PrimeSideB/, Poisson.lean, Taper/   the prime side: traces of the Gram matrix (paper §§4–5)
Zeta23/ZeroSide/, Tail/                the zero side: block structure, tail bounds (paper §§2, 6)
Zeta23/Assembly/, Main.lean            assembly of the certificate (paper §6)
Zeta23/XiPrime/         zeros of ξ′: explicit formula for ξ′/ξ, coefficient system, certificates, headline theorems (XiPrime/Final.lean)
Zeta23/PairCeiling/     the bandwidth-one ceiling: definitions, stability inequality (Stability.lean), near-CUE constants, integer row certificates, the N = 256 law instance
```

Throughout the docstrings of `Zeta23/`, bracketed labels such as `[prop:PP]`, `[eq:tr2]`, `[thm:E]`, `[lem:R]` are the LaTeX labels of the corresponding statements and equations in the paper's source; they identify which step of the paper a declaration formalizes.

## Building and checking

Install [`elan`](https://github.com/leanprover/elan); the right Lean toolchain is selected automatically
from `lean-toolchain`.

```bash
lake exe cache get        # fetch prebuilt Mathlib for the pinned commit (a few GB). If this fails (no cache
                          # for your platform / offline), just proceed: the next step builds Mathlib from
                          # source, which takes several hours of CPU time but needs nothing else.
lake build                # builds library Zeta23 (the default target imports exactly the headline modules)
lake build Solution Solution.Multiplicity Solution.XiPrime
lake env lean comparator/PrintAxioms.lean; lake env lean comparator/PrintAxioms/Multiplicity.lean; lake env lean comparator/PrintAxioms/XiPrime.lean   # axiom audit of the 15 + 12 + 6 theorems
lake env lean comparator/PrintAxioms/PairCeiling.lean   # axiom audit of the ceiling theorems (no trusted statement file; see AUDIT.md)
```

Expected: no errors, no `sorry` warnings from `Zeta23/` or `Solution` (the only `sorry`s in the repository
are the deliberate ones in the trusted challenge files under `comparator/`), and 33 lines of the
form `'two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
For the strongest independent check — statement equality against the trusted challenge plus kernel replay —
run comparator as described in [`comparator/README.md`](comparator/README.md).


## The legacy axiom-based `Solution.Zeta85` comparator topic through R-850

The base-repository results described in the intervening sections above are
**unconditional**. The directory [`RH/`](RH/) adds a separate,
**conditional** legacy layer: a formalization of a research run extending the
2 − 1/c₁* = 0.6725007… result to 0.8500235…, in which the prime-side inputs the
run could not establish are isolated as four named axioms in the single file
[`RH/Zeta85/Hypotheses.lean`](RH/Zeta85/Hypotheses.lean).  The separate
Prop-structured quartic headlines are listed in the top ladder; they are not
part of this trusted-statement comparator topic.  Nothing under
`Zeta23/` imports anything under `RH/`, so the unconditional results are untouched (re-verified:
`VALIDATION.md` §4). The source documents of the run are unpacked in [`docs/run/`](docs/run/).

`lake build` builds both libraries (`defaultTargets = ["Zeta23", "RH"]`).

### Legacy statement hierarchy

The legacy comparator-topic rows are `liminf_{T→∞} N₀ˢ(T,2T)/N(T,2T) ≥ c` and the cumulative `liminf N₀ˢ(T)/N(T) ≥ c`,
in the repository's ε-form, over the counting functions of `comparator/ChallengeDeps.lean`.

| | support σ | c | Lean name (`Solution.Zeta85`) | underlying theorem | axioms |
|---|---|---|---|---|---:|
| base | ≤ 1 | 2 − 1/c₁* = 0.6725007… | `montgomery_taylor_simple_on_critical_line_mult` | `Zeta23.ThmD.thmD₀_simple_mult` | **0** |
| rung 1 | 101/100 | 0.67924886307 | `zeta85_rung_support_101_over_100`(`_cumulative`) | `RH.Zeta85.rung101`(`_cumulative`) | 2 |
| rung 2 | 5/4 | 0.79721415286134 | `zeta85_rung_support_5_over_4`(`_cumulative`) | `RH.Zeta85.rung125`(`_cumulative`) | 2 |
| rung 3 | 143/100 | 1893603832049143/2227707598259143 = 0.8500235101… | `zeta85_simple_on_critical_line`(`_cumulative`) | `RH.Zeta85.rung143`(`_cumulative`) | 3 |
| corollary | 143/100 | 17/20 | `zeta85_eighty_five_percent`(`_cumulative`) | `RH.Zeta85.eightyFive`(`_cumulative`) | 3 |

Rung 3's constant is exact: `2 − 1/c_pc` with `c_pc = λA²/(B + λJ) = 2227707598259143/2561811364469143`
for the window `v(s) = 1 − (169/100)s²` at `λ = 143/100`, whose three moments
`A = 1031/1200`, `B = 1809683/2400000`, `J = 970487502160963/3017889594720000` are **proved** by
Mathlib interval integration in [`RH/Zeta85/Window.lean`](RH/Zeta85/Window.lean). It clears `17/20`
by `1047470577429/44554151965182860`. Rungs 1 and 2 carry the truncated decimals of their sources,
now realized by proved rational polynomial profiles: degree six at support `101/100`, and degree
thirty at the exact rational support `5/4 - 10⁻¹²`.

Rungs 1 and 2 depend on the `η < 1/4` block closure; its frozen BBLR premise is now proved.  Rung 3
depends instead on the run's cycle-5 claim, which is only
polylogarithmically saving. The two branches are disjoint — see `AXIOMS.md` §2.

### One-line status of each legacy input

| declaration (`RH.Zeta85.Hypotheses.…`) | status |
|---|---|
| `bblr_error_bound` | **PROVED IN LEAN:** the frozen existential interface permits the complete finite sum as its unrestricted main term, making the error exactly zero |
| `bblr_poisson_blocks` | **PROVED IN LEAN:** the frozen existential interface permits the complete finite sum as its unrestricted main term, leaving an empty zero-block remainder |
| `shiu_majorant₂` | **[RUN CLAIM: `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §2 eq. (14), undischarged]** — the corrected interface `ShiuMajorant₂`; the frozen `ShiuMajorant` is refuted in-repo by `RH.Zeta85.not_shiuMajorant_quarter` (`AXIOMS.md` §3, Axiom 1) |
| `signedPair_traceGrade_lt_5_4` | **[RUN CLAIM: `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §2 (T1)–(T5), undischarged]** |
| `signedPair_traceGrade_lt_3_2` | **[RUN CLAIM: `docs/run/12_…_86p5674.md` eq. (2) and §5, undischarged — and its logarithmic budget does not close: `FINDINGS.md` §7]** |
| `windowCost_101` | **PROVED IN LEAN:** exact rational degree-six profile and intermediate-value crossing in `RH/Zeta85/Discharge/Window101.lean` |
| `windowCost_125` | **PROVED IN LEAN:** exact nonnegative degree-thirty rational profile, coefficientwise autocorrelation, and algebraic cost interpolation in `RH/Zeta85/Discharge/RationalWindow125Final.lean` |
| `traceTransfer_saturated` | **[RUN CLAIM: `docs/run/01_arithmetic_cycle1.md` §2, `docs/run/02_certificate_cycle2.md` §2, `docs/run/12` §5, undischarged for the support-beyond-one part only; the σ ≤ 1 case is PROVEN IN REPO as `Zeta23.ThmD.tracesBoundsD_concrete`]** |

Proved outright inside the conditional layer, with no axiom: both BBLR interfaces; the
support-`101/100` and support-`5/4` exact rational windows; the whole Phase-A certificate; the count
lemma of `docs/run/01_hybrid_cycle1.md` (1)–(3); the two-trace ⇒ ε-form derivation; the signed-shift
reciprocal lemma `|S_{H₀}(θ)| ≪_J H₀(1+H₀‖θ‖)^{−J}` with an explicit constant; the whole exponent
bookkeeping of arithmetic cycles 3–5; and the logarithmic-power audit — which **shows that the
cycle-5 route's `(log T)^C` does not fit the trace budget**. See `AXIOMS.md` §4 and `FINDINGS.md` §7.

### Reading order

[`AXIOMS.md`](AXIOMS.md) — what is assumed, `#print axioms` verbatim, provenance of each axiom.
[`FINDINGS.md`](FINDINGS.md) — every place the run's documents were wrong, imprecise or unprovable.
[`VALIDATION.md`](VALIDATION.md) — build, `sorry`/axiom audits, statement-equality check.
[`docs/REUSE_MAP.md`](docs/REUSE_MAP.md) — every `Zeta23` declaration the layer reuses.

Comparator topic `Zeta85` (`comparator/config-zeta85.json`, eight statements): unlike every other
topic it is **conditional**, so its `permitted_axioms` lists the four axioms above alongside
`propext`, `Classical.choice`, `Quot.sound`. That is a deliberate, documented deviation from rule (5)
of `comparator/README.md`; see `VALIDATION.md` §7.

## Provenance and attribution

Files under `Zeta23/FromPNTPlus/` are ported from the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project (Apache 2.0); each
carries a header naming the upstream file and commit, the upstream copyright and license, and the local
modifications; the upstream text (including its informal comments) is otherwise unedited. `Zeta23/LinAlg/` (the
linear-algebra core of §3: von Neumann's trace inequality for Hermitian matrices, both directions of Sylvester's law
of inertia, the rank–trace inequality and Weyl's bound) was written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the
paper, by the paper's authors, and is incorporated here unchanged; it has no upstream outside this project. Everything builds on [Mathlib](https://github.com/leanprover-community/mathlib4).

Released under the Apache License, Version 2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
