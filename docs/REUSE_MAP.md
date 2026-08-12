# REUSE_MAP — Zeta23 declarations reused by `RH/Zeta85/`

Every declaration below is **already proved in this repository** (base commit `3635e74`, `lake build`
clean, `#print axioms` = the standard three) and is used unchanged by the 85 % layer.  Nothing in this
table is re-proved, re-stated or weakened; where the 85 % layer needs a variant, the variant is stated
in `RH/Zeta85/` and *derived* from the entry named here.

Toolchain: Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.

## 1. Trusted statement vocabulary (comparator side)

| declaration | file | used for |
|---|---|---|
| `IsNontrivialZero` | `comparator/ChallengeDeps.lean:38` | the challenge statements of the 85 % topic |
| `zeroMult` | `comparator/ChallengeDeps.lean:43` | idem |
| `zerosIn` | `comparator/ChallengeDeps.lean:47` | idem |
| `Ncount` | `comparator/ChallengeDeps.lean:52` | denominator `N(T₁,T₂)` of every rung |
| `N0simple` | `comparator/ChallengeDeps.lean:68` | numerator `N₀ˢ(T₁,T₂)` of every rung |
| `N0star` | `comparator/ChallengeDeps.lean:64` | (not used by the 85 % statements; listed for completeness) |

`comparator/Challenge/Zeta85.lean` uses **only** `Ncount` and `N0simple` from this file, in the
repository's ε-form `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)`.  No new `ChallengeDeps/<Topic>.lean`
is needed.

## 2. The Zeta23 statement layer

| declaration | file | used for |
|---|---|---|
| `Zeta23.Ncount` | `Zeta23/Statement.lean:49` | solution-side counting function (definitionally the challenge's) |
| `Zeta23.N0simple` | `Zeta23/Statement.lean:62` | idem |
| `Zeta23.ZetaSeam` | `Zeta23/Statement.lean:75` | hypothesis record for the dyadic→cumulative passage |
| `Zeta23.zetaSeam` | `Zeta23/Statement/SeamClosed.lean:22` | the *proved* instance of `ZetaSeam` for Mathlib's `riemannZeta` |
| `Zeta23.zetaZeroConfig` | `Zeta23/Statement/SeamClosed.lean:26` | ζ's zeros as an abstract `ZeroConfig` |
| `Zeta23.paperInputs_zeta` | `Zeta23/Final.lean:291` | the proved `PaperInputs zetaZeroConfig` (Weil EF, RvM, MV, Γ) |

## 3. Abstract zero configuration and counting

| declaration | file | used for |
|---|---|---|
| `Zeta23.ZeroConfig` | `Zeta23/Defs.lean` | carrier of `RH.Zeta85.TwoTraceCert` |
| `Zeta23.ZeroConfig.N` | `Zeta23/Defs.lean` | `N(T₁,T₂)` on the abstract side |
| `Zeta23.ZeroConfig.N0s` | `Zeta23/Defs.lean:158` | `N₀ˢ(T₁,T₂)` on the abstract side |
| `Zeta23.zetaZeros_N` | `Zeta23/Statement.lean:107` | `(zetaZeros hs).N = Ncount` |
| `Zeta23.zetaZeros_N0s` | `Zeta23/Statement.lean:115` | `(zetaZeros hs).N0s = N0simple` |

## 4. Dyadic → cumulative passage (mirrored exactly, D1)

| declaration | file | used for |
|---|---|---|
| `Zeta23.cumulative_of_dyadic` | `Zeta23/Main.lean:51` | turns each dyadic rung into its cumulative form |
| `Zeta23.N0simple_add'` | `Zeta23/Main.lean:69` | additivity of `N₀ˢ` over adjacent windows |
| `Zeta23.PaperInputs.RvM` (field) | `Zeta23/Assembly/Inputs.lean` | the `RiemannVonMangoldt` input `cumulative_of_dyadic` consumes |

This is the *same* three-argument call the base repository makes for Theorems A–D, e.g.
`Zeta23/ThmD/Final.lean:141`
(`cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => N0simple_add' zetaSeam) thmD₀_simple`).
`RH/Zeta85/Main.lean` uses that call verbatim with the 85 % dyadic theorem in the last slot.

## 5. Rank–trace / inertia core (Proposition 4.4 analogue)

| declaration | file | role in the paper |
|---|---|---|
| `RHLinalg.rank_trace_ineq` | `Zeta23/LinAlg/RankTrace.lean:163` | Lemma R, the rank–trace inequality (via von Neumann) |
| `RHLinalg.rank_trace_ineq_two` | `Zeta23/LinAlg/RankTrace.lean:260` | its two-matrix form |
| `Zeta23.ZeroSide.ZeroBlockData.mult_two` | `Zeta23/ZeroSide/Mult.lean:128` | c = 2 multiplicity-aware count (simple ∧ on line) |
| `Zeta23.ZeroSide.hatAz_mult2` | `Zeta23/ZeroSide/Mult.lean:185` | the same in hat units for `Â_z` |
| `Zeta23.Assembly.seamA_mult2` | `Zeta23/Assembly/SeamMult.lean:46` | **Seam A**: `4·tr Ĝ − ‖Ĝ‖²_F − 2N − 3·N_II − B(4+2√‖Ĝ‖²+B) ≤ N₀ˢ` |
| `Zeta23.ThmD.N0star_lower_c` | `Zeta23/ThmD/AssemblyD.lean:41` | the pure real-arithmetic step Seam A + two trace bounds ⟹ `(2 − D)N − err ≤ N₀ˢ` |

`RH/Zeta85/Transfer.lean` reuses `Zeta23.ThmD.N0star_lower_c` verbatim as the fixed-`T` algebra;
`Zeta23.Assembly.seamA_mult2` is the shape that `RH.Zeta85.TwoTraceData.zeroSide` records (see
`RH/Zeta85/Transfer.lean` docstring — the seam itself carries **no** restriction `λ ≤ 1`; only the
prime side does, which is exactly why the 85 % hypotheses are prime-side only).

## 6. Prime side (Proposition 5.6 analogue) and the window functional

| declaration | file | role |
|---|---|---|
| `Zeta23.ThmD.cRatio` | `Zeta23/ThmD/AssemblyD.lean:28` | `cRatio λ₁ a b J = λ₁·a²/(b + λ₁²·J)` — the paper's (7.3) ratio at support ≤ 1 |
| `Zeta23.ThmD.TracesBoundsD` | `Zeta23/ThmD/AssemblyD.lean:61` | the prime-side interface: `tr G̃` and `tr G̃²` with the `cRatio` main term |
| `Zeta23.ThmD.tracesBoundsD_concrete` | `Zeta23/ThmD/Concrete.lean` | the *proof* of that interface for `λ ≤ 1` |
| `Zeta23.ThmD.thmD_mult2_abstract` | `Zeta23/ThmD/Mult.lean:48` | traces ⟹ `(2 − c⁻¹ − ε)·N ≤ N₀ˢ`, the λ ≤ 1 endgame |
| `Zeta23.Params`, `Zeta23.Params.Valid` | `Zeta23/Defs.lean:186,193` | the Gabor family; `Valid` contains `lam_le_one` |
| `Zeta23.Params.calE` | `Zeta23/Defs.lean` | the error bookkeeping `ℰ_T = w/L + (l²+X)log l/(T l) + T^{λ/2−1}` |
| `Zeta23.Taper.hasSum_phiHatR_sq` | `Zeta23/Poisson.lean:367` | Lemma poisson, `Σ_k φ̂(γ−τ_k)² = aL²` — **needs only** `TaperProfile ϱ`, `0 < w`, `2w ≤ L` |

**Where λ ≤ 1 actually bites.**  `Params.Valid.lam_le_one` occurs 72 times in `Zeta23/`; every
occurrence is on the prime side or in `calE`.  `calE` contains the summand `X·log l/(T·l)` with
`X = (T/2π)^λ`, which tends to `0` iff `λ ≤ 1`.  This is the formal shadow of the mathematical fact
that the pair-correlation main term is only *evaluated* for support ≤ 1 in the accepted base.  The zero
side (`Zeta23/ZeroSide/`, `Zeta23/Poisson.lean`, `Zeta23/Assembly/SeamMult.lean`) never uses it.  This
is the reason the 85 % axiom set in `RH/Zeta85/Hypotheses.lean` consists of prime-side statements only.

## 7. Constant-form conventions reused

| declaration | file | note |
|---|---|---|
| `cMT` | `comparator/ChallengeDeps.lean:115` | the Montgomery–Taylor constant in closed Mathlib form |
| `Zeta23.ThmD.cStar`, `Zeta23.ThmD.HD` | `Zeta23/ThmD/Functional.lean:35,53` | `HD λ = 2 − 1/c*(λ)` |
| `cStar_one_eq_cMT` | `comparator/Solution.lean:37` | the challenge↔solution bridge lemma pattern |

The 85 % rungs state their constants as **exact rationals** (85 %) or as the **truncated decimals of the
source documents** (0.679 and 0.797 rungs), following the precedent of the repository's `XiPrime`
topic, whose challenge file uses the literals `0.85838`, `0.92919`, `0.86864`, `0.93432`
(`comparator/Challenge/XiPrime.lean`).  Truncating the target downward makes the statement *weaker*
than the source claim, never stronger; see `FINDINGS.md` §4 for the numerical verification that each
truncation is on the safe side.

## 8. Comparator topic conventions reused

`comparator/README.md` "Layout convention: one topic per file" — the 85 % topic adds
`comparator/Challenge/Zeta85.lean`, `comparator/Solution/Zeta85.lean`,
`comparator/config-zeta85.json`, `comparator/PrintAxioms/Zeta85.lean` and edits none of the base four
files.  The one documented deviation from the base convention is rule (5) (`permitted_axioms` = the
standard three): the 85 % topic is *conditional*, so its `config-zeta85.json` lists the
`RH.Zeta85.Hypotheses` axioms explicitly.  See `AXIOMS.md`.
