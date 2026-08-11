# AXIOMS.md — what the 85 % layer assumes

Toolchain: Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.

The base library `Zeta23/` is **unconditional**: it declares no axiom, and `#print axioms` on each of
its 33 headline theorems reports only `propext`, `Classical.choice`, `Quot.sound` (re-verified after
this change — see `VALIDATION.md` §2).  Nothing under `Zeta23/` imports anything under `RH/`.

`RH/` is the **conditional** layer.  It declares exactly **eight** axioms, all in the single file
[`RH/Zeta85/Hypotheses.lean`](RH/Zeta85/Hypotheses.lean).  No axiom is declared anywhere else in
`RH/`, and no `sorry` occurs anywhere in `Zeta23/` or `RH/` (the only `sorry`s in the repository are
the deliberate ones in the trusted challenge files under `comparator/`).

---

## 1. `#print axioms` — verbatim

### 1.1 The 0.679 theorem (support 101/100)

```
'zeta85_rung_support_101_over_100' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_error_bound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated,
 RH.Zeta85.Hypotheses.windowCost_101]
'zeta85_rung_support_101_over_100_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_error_bound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated,
 RH.Zeta85.Hypotheses.windowCost_101]
```

### 1.2 The 0.797 theorem (support 5/4)

```
'zeta85_rung_support_5_over_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_error_bound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated,
 RH.Zeta85.Hypotheses.windowCost_125]
'zeta85_rung_support_5_over_4_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_error_bound,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4,
 RH.Zeta85.Hypotheses.traceTransfer_saturated,
 RH.Zeta85.Hypotheses.windowCost_125]
```

### 1.3 The 0.85 theorem (support 143/100) and its corollary

```
'zeta85_simple_on_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_poisson_blocks,
 RH.Zeta85.Hypotheses.shiu_majorant,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_simple_on_critical_line_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_poisson_blocks,
 RH.Zeta85.Hypotheses.shiu_majorant,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_eighty_five_percent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_poisson_blocks,
 RH.Zeta85.Hypotheses.shiu_majorant,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
'zeta85_eighty_five_percent_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RH.Zeta85.Hypotheses.bblr_poisson_blocks,
 RH.Zeta85.Hypotheses.shiu_majorant,
 RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2,
 RH.Zeta85.Hypotheses.traceTransfer_saturated]
```

Reproduce with `lake env lean comparator/PrintAxioms/Zeta85.lean`.  The same eight lines with the
`RH.Zeta85.rung*` / `RH.Zeta85.eightyFive*` names (the solution-side theorems the comparator topic
delegates to) are identical.

### 1.4 What is proved outright inside the conditional layer

```
'RH.Zeta85.windowCost_143' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.jSat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.cPC_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.count_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.epsForm_of_twoTraceCert' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.shiftSum_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.sum_over_separated' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.nearInt_int_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.four_nearInt_le_norm_cexp_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.SignedShift.bdiffIter_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.budget_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.budget_dyadic_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.LogBudget.power_beats_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH.Zeta85.Exponents.bblr_blackbox_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 2. Axiom count per rung

| rung | constant | axioms it depends on | count |
|---|---|---:|---:|
| base (Zeta23, Theorem D) | 2 − 1/c₁* = 0.6725007… | — | **0** |
| 1 | 0.67924886307 | `bblr_error_bound`, `signedPair_traceGrade_lt_5_4`, `windowCost_101`, `traceTransfer_saturated` | **4** |
| 2 | 0.79721415286134 | `bblr_error_bound`, `signedPair_traceGrade_lt_5_4`, `windowCost_125`, `traceTransfer_saturated` | **4** |
| 3 | 1893603832049143/2227707598259143 = 0.8500235101… | `bblr_poisson_blocks`, `shiu_majorant`, `signedPair_traceGrade_lt_3_2`, `traceTransfer_saturated` | **4** |

The counts coincide but the **contents differ**, and that is the point:

* rungs 1 and 2 use the **published** BBLR error bound and the `η < 1/4` block closure, which is
  *power*-saving relative to trace scale.  They do **not** use `shiu_majorant` and do **not** use the
  cycle-5 claim `signedPair_traceGrade_lt_3_2`;
* rung 3 uses the cycle-5 route instead, which is only *polylogarithmically* saving, needs the Shiu
  majorant, and is the branch whose logarithmic budget does not close (see §3, Axiom 5, and
  `FINDINGS.md` §7);
* the only shared axioms are `traceTransfer_saturated` (used by all three) and — for rungs 1 and 2 —
  the published BBLR bound.  Rung 3's window cost is **not** an axiom: `RH.Zeta85.windowCost_143` is
  proved from the exact rational moments of `RH/Zeta85/Window.lean`.

Two of the eight axioms (`bblr_error_bound`, `bblr_poisson_blocks`) are published literature; three
(`shiu_majorant`, `signedPair_traceGrade_lt_5_4`, `signedPair_traceGrade_lt_3_2`) are the run's
arithmetic claims; two (`windowCost_101`, `windowCost_125`) are the run's numerical certificates for
transcendental windows; one (`traceTransfer_saturated`) is the support-beyond-one trace evaluation.

---

## 3. The eight axioms, with provenance

Full docstrings — exact mathematical statement, source, and why not discharged — are in
[`RH/Zeta85/Hypotheses.lean`](RH/Zeta85/Hypotheses.lean); they are reproduced here in condensed form.
No axiom below lacks a source.

### Axiom 1 — `bblr_error_bound : BBLRErrorBound`

*Status:* **[PUBLISHED LITERATURE: Bettin–Bui–Li–Radziwiłł, "A quadratic divisor problem and moments
of the Riemann zeta-function", J. Eur. Math. Soc. 22 (2020) 3953–3980, Proposition 3.1 (error
bound)]**, as quoted at `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` equation (3).

*Statement.*  For `A, B, M₁, M₂, N₁, N₂, H ≥ 1`, `M = M₁M₂`, `N = N₁N₂`, coefficients `α_a`, `β_b`
and smooth weights `W₁…W₄` supported in `(1,2)` satisfying `W_i^{(j)} ≪ (ABMN)^ε` (`0 ≤ j ≤ 4`),
`α_a ≪ A^ε`, `β_b ≪ B^ε`, `M₁ ≤ M₂(ABMN)^ε`, `N₁ ≤ N₂(ABMN)^ε`, and `H ≪ (AB)^{1/2+ε}`, the smoothly
`h`-averaged quadratic divisor sum
`S₊ = Σ_{am₁m₂ − bn₁n₂ = h ≠ 0} α_a β_b W₁(m₁/M₁)W₂(m₂/M₂)W₃(n₁/N₁)W₄(n₂/N₂) w(h/H)`
splits as `S₊ = M + E`, `M` the `(am₁,bn₁) = d` gcd main term, with
`E ≪_ε (ABMNH²)^{1/4+ε}·(AB + H^{1/4}(A+B)^{1/2}(ABMN)^{1/8})`.
**The first factor in the bracket is `AB`, not `(AB)^{1/2}`** — see `FINDINGS.md` §3.

*Why not discharged.*  Published; its proof is a dispersion argument plus Watt's spectral estimate
for sums of Kloosterman sums.  The task specification directs that it be taken verbatim.  The main
term is existentially quantified in the Lean rendering, which makes the axiom weaker than the
published statement.

### Axiom 2 — `bblr_poisson_blocks : BBLRPoissonBlocks`

*Status:* **[PUBLISHED LITERATURE: BBLR, ibid., the displayed equation (14) inside the proof of
Proposition 3.1]**, transcribed with the block scales at
`docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §1 (5)–(7), (9)–(11), and combined with §3
(16)–(17).

*Statement.*  After writing `d = (am₁,bn₁)`, `p = (a/d₁)(m₁/d₂)`, `q = (b/d₃)(n₁/d₄)`, Poisson
summation presents the nonzero-frequency part of `S₊` as a finite sum of blocks
`R_d = Σ_{ℓ≠0} Σ_{p≍P_d, q≍Q_d, (p,q)=1} c_{d,p} e_{d,q} F_{d,ℓ}(p,q) Σ_h w_d(h) e(∓ℓh p̄/q)`
with `P_d ≍ AM₁/d`, `Q_d ≍ BN₁/d`, `H_d = H/d`, `‖F_{d,ℓ}‖ ≪_J d(1+|ℓ|d)^{−J}(log T)^{C_J}`; the
per-block bound `|R_d| ≪ P_d(Q_d + H_d)(1+d)^{−2}(log T)^C` is what the Lean statement records.

*Why not discharged.*  The identity is published (as Axiom 1).  The per-block bound is a derived
statement of the run; the parts of that derivation that *could* be discharged here have been — the
signed-shift reciprocal lemma (12)–(13) is **proved** in `RH/Zeta85/Discharge/SignedShift.lean` and
every exponent comparison of §3 in `RH/Zeta85/Discharge/Exponents.lean`.  What survives is (14)
itself plus the claim that `c_{d,p}`, `e_{d,q}` are the actual fixed-depth convolution coefficients
with the stated majorants, which is not formalizable without the whole Heath–Brown apparatus.

### Axiom 3 — `shiu_majorant : ∀ η, 0 < η → η < 1/2 → ShiuMajorant η`

*Status:* **[RUN CLAIM: `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §2, equation (14),
undischarged]**; underlying published result P. Shiu, "A Brun–Titchmarsh theorem for multiplicative
functions", J. Reine Angew. Math. 313 (1980) 161–170.

*Statement.*  For the recombined divisor-bounded Heath–Brown coefficients `c_p`,
`Σ_{p ≍ P, p ≡ r (q), (r,q)=1} |c_p| ≪ (P/φ(q))·(log T)^C`, uniformly for `q ≤ P·T^{−η+o(1)}`.

*Why not discharged.*  A full proof along the route the source indicates does not close: Shiu's
theorem is not in Mathlib, and its hypotheses (a non-negative multiplicative majorant) do not apply
verbatim to the run's `c_p`, which are *signed* convolutions of Möbius and smooth factors.  The
source's "fix every short factor" reduction presupposes the factorization of the recombined
coefficients — the unformalized Heath–Brown apparatus again.

### Axiom 4 — `signedPair_traceGrade_lt_5_4 : BBLRErrorBound → ∀ σ, 1 < σ → σ < 5/4 → SignedPairTraceGrade σ`

*Status:* **[RUN CLAIM: `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §2 ("Theorem (fixed
support)" and its block closure, (T1)–(T5)), transported to the aggregate criterion (AS) of
`docs/run/01_arithmetic_cycle1.md` §4, undischarged]**.

*Statement.*  At `η = 1/4 − κ`, a Heath–Brown identity of depth `K` with `X^{1/K} < H·T^{−10ε}`
splits every block into (i) a Type-I block with a long smooth variable, handled by Poisson summation
plus the hybrid large sieve with `O_A(X log^{−A}X)`, and (ii) the terminal BBLR block with
`A, B = H·T^{O(ε)}`; "there is no third block".  Feeding (ii) into Axiom 1 gives power-saving errors,
so the signed aggregate criterion `(AS)` holds at every fixed `1 < σ < 5/4`.

*Why not discharged.*  Three obstacles, each attempted: (i) the finite-depth Heath–Brown identity and
factor-grouping dichotomy are not in Mathlib; (ii) the Type-I estimate needs Poisson summation plus
the hybrid large sieve in a uniform form not available; (iii) "there is no third block" cannot be
stated without (i).  What *was* discharged: all of the exponent bookkeeping
(`RH.Zeta85.Exponents.bblr_blackbox_ceiling`, `bblr_savings`, `EA_traceGrade_iff`,
`EW_traceGrade_iff`) and the fact that a fixed power beats every fixed logarithmic loss
(`RH.Zeta85.LogBudget.power_beats_log`).

### Axiom 5 — `signedPair_traceGrade_lt_3_2 : BBLRPoissonBlocks → (∀ η, …, ShiuMajorant η) → ∀ σ, 1 < σ → σ < 3/2 → SignedPairTraceGrade σ`

*Status:* **[RUN CLAIM: `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` equation (2) and
§5, undischarged — AND, on the evidence of `RH/Zeta85/Discharge/LogBudget.lean`, not established by
the run at all]**.  This is the single most load-bearing undischarged statement in the artifact.

*Statement.*  For every fixed `0 < η < 1/2`, `R_HB ≪ (T^{1+η} + T^{1/2+2η})(log T)^C`; consequently
the aggregate criterion `(AS)` holds at every fixed connected support `1 < σ = 1 + η < 3/2`.

*Why not discharged — two distinct reasons.*

1. The derivation of (2) needs Axioms 2 and 3 and the Heath–Brown recombination.  The two pieces that
   could be discharged were discharged: the signed-shift reciprocal lemma (12)–(13)
   (`RH/Zeta85/Discharge/SignedShift.lean`) and the exponent comparisons (18)–(19)
   (`RH.Zeta85.Exponents.cycle5_scales`, `cycle5_traceGrade`, `cycle5_gain`).
2. **Even granting (2) in full, it does not imply `(AS)`.**  `(AS)` demands a logarithmic *saving*
   `≪_A X(log X)^{−A}`; (2) supplies a logarithmic *loss* `(log T)^{+C}`.  The audit in
   `RH/Zeta85/Discharge/LogBudget.lean` computes the budget exactly: the free room for the error's
   logarithms is `(log T)^{<2}` in the most generous single-block reading
   (`LogBudget.budget_closes`/`budget_fails`) and `(log T)^{<0}` with the dyadic multiplicities of
   `docs/run/02_certificate_cycle2.md` (14) restored
   (`budget_dyadic_closes`/`budget_dyadic_fails`), while the Heath–Brown depth forced at
   `η = 43/100` is `K ≥ 4` (`LogBudget.depth_at_85`), giving `C ≥ K − 1 ≥ 3`.  Both thresholds fail
   (`LogBudget.verdict`).  See `FINDINGS.md` §7.

   Per R2 the 85 % target is **not** weakened to accommodate this: the target stays
   `1893603832049143/2227707598259143`, and this axiom states exactly the blocking statement at the
   strength the transfer consumes.

### Axiom 6 — `windowCost_101 : SaturatedWindowCost (101/100) (2 − cRung101)`

*Status:* **[RUN CLAIM: `docs/run/07_root_gain_support_1p01.md`, "Explicit numerical certificate",
undischarged]**.

*Statement.*  At `λ = 101/100` with `v(s) = cos(√2 s)` on `[−1/2,1/2]` and `K_λ(s,t) = min(λ|s−t|,1)`:
`I₁ = 2sin(√2/2)/√2`, `I₂ = 1/2 + sin√2/(2√2)`, `J_λ = 2λ∫₀^{1/λ}d·A(d)dd + 2∫_{1/λ}^1 A(d)dd` with
`A(d) = ((1−d)/2)cos(√2 d) + sin(√2(1−d))/(2√2)`, and
`D_{1.01}(v) = (I₂ + λJ_λ)/(λI₁²) = 1.32075113693…`, so `2 − D = 0.67924886307…`.  The axiom asserts
the cost at the **truncated** decimal, which is the weaker assertion.

*Why not discharged.*  The window is transcendental; a rational bound to twelve significant figures
requires certified interval arithmetic on `sin`/`cos` at `√2`, which Mathlib's `norm_num` extensions
do not provide.  Verified numerically outside Lean (`FINDINGS.md` §4): the computed value is
`2 − D = 0.6792488630700078…`, so the truncation is on the safe side.

### Axiom 7 — `windowCost_125 : ∃ σ, 1 < σ ∧ σ < 5/4 ∧ SaturatedWindowCost σ (2 − cRung125)`

*Status:* **[RUN CLAIM: `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §3, equations
(11)–(16); same numbers at `docs/run/03_arithmetic_cycle3.md` §5 (32)–(37); undischarged]**.

*Statement.*  For `K(t) = min(|t|,1)` at `σ = 5/4`, the Euler equation
`u(x) + ∫min(|x−y|,1)u(y)dy = C` has the even solution `u(x) = cos(√2 x)` on `|x| ≤ 3/8`,
`u(x) = A₀cos(|x|−1/2) + B₀sin(√3(|x|−1/2))` on `3/8 ≤ |x| ≤ 5/8`, with `A₀ = 0.765651150533640…`,
`B₀ = −0.479300891051646…`; `∫u = 1.09716424928793…`, `C = 1.31965363103003…`,
`D*_{5/4} = 1.20278584713866…`, `2 − D*_{5/4} = 0.79721415286134…`.  Since `σ ↑ 5/4` is a limit, the
axiom asserts the cost at *some* fixed `σ ∈ (1, 5/4)` and at the truncated decimal.

*Why not discharged.*  As Axiom 6, plus: the profile is characterised as the solution of an integral
equation, so discharging it also requires proving that the displayed function *is* that solution.
Verified numerically outside Lean (`FINDINGS.md` §4): the Euler equation holds to `1·10⁻⁹` uniformly
on the support, and `2 − D = 0.7972141529233692…`, so the truncation is on the safe side.

### Axiom 8 — `traceTransfer_saturated : ∀ σ D, 1 < σ → σ < 3/2 → SaturatedWindowCost σ D → SignedPairTraceGrade σ → TwoTraceCert zetaZeroConfig D`

*Status:* **[RUN CLAIM: `docs/run/01_arithmetic_cycle1.md` §2 (5)–(9),
`docs/run/01_certificate_cycle1.md` (5)–(6), `docs/run/02_arithmetic_cycle2.md` §1,
`docs/run/02_certificate_cycle2.md` §2 (13)–(17), `docs/run/12` §5; undischarged for the
support-beyond-one part only]**.  The `σ ≤ 1` case is the base paper's Proposition 5.6 and is
**proved in this repository** (`Zeta23.ThmD.tracesBoundsD_concrete`).

*Statement.*  Given an achievable saturated-kernel cost `D` at support `σ ∈ (1, 3/2)` and the signed
aggregate criterion at that support, the zeros of `riemannZeta` carry a Gabor family whose hat-unit
Gram matrix satisfies Seam A `4·tr Ĝ − ‖Ĝ‖²_F − 2N − o(N) ≤ N₀ˢ`, `tr Ĝ = N(1+o(1))` and
`‖Ĝ‖²_F ≤ (D + o(1))N`.

*What is reused rather than assumed.*  The whole zero side.  `Zeta23.Assembly.seamA_mult2` is proved
in the base repository for an arbitrary `Zeta23.Params` family and carries **no** restriction
`λ ≤ 1`; the Poisson identity behind it (`Zeta23.Taper.hasSum_phiHatR_sq`) needs only
`TaperProfile ϱ`, `0 < w`, `2w ≤ L`.  The rank–trace inequality (`RHLinalg.rank_trace_ineq`), the
`c = 2` multiplicity-aware count (`Zeta23.ZeroSide.ZeroBlockData.mult_two`) and the fixed-`T` algebra
(`Zeta23.ThmD.N0star_lower_c`) are reused verbatim (`docs/REUSE_MAP.md` §5).

*Why not discharged.*  What fails past `λ = 1` is the base repository's error bookkeeping
`Zeta23.Params.calE = w/L + (l² + X)log l/(T l) + T^{λ/2−1}`: the summand `X·log l/(T·l)` with
`X = (T/2π)^λ` tends to `0` **iff** `λ ≤ 1`.  Rebuilding `Zeta23/PrimeSideA/`, `Zeta23/PrimeSideB/`
and `Zeta23/ThmD/Traces.lean` with the saturated kernel and the new pole/tail/zero-mode accounting is
a development of the same order as the base repository, and its analytic content — evaluating the
singular-series main term at frequencies `|α| > 1` with the exact kernel `K(t) = min(λ|t|,1)` — is
precisely the new mathematics of the run.  Only that genuinely new part is assumed.

---

## 4. What is **not** assumed

Explicitly proved, not axiomatized (all reported as depending only on the standard three, §1.4):

* the three exact window moments `A = 1031/1200`, `B = 1809683/2400000`,
  `J = 970487502160963/3017889594720000` and the quintic autocorrelation `g(u)`
  (`RH/Zeta85/Window.lean`, by Mathlib interval integration of polynomials);
* the certificate `c_pc = 2227707598259143/2561811364469143 > 20/23`,
  `2 − 1/c_pc = 1893603832049143/2227707598259143 > 17/20`, margin
  `1047470577429/44554151965182860` (`RH/Zeta85/Certificate.lean`);
* `SaturatedWindowCost (143/100) D_pc` (`RH.Zeta85.windowCost_143`);
* the count lemma of `docs/run/01_hybrid_cycle1.md` (1)–(3) and its `C = 23/20 − η` specialization;
* the two-trace ⇒ ε-form derivation (`RH/Zeta85/Transfer.lean`), which routes through the count
  lemma;
* the signed-shift reciprocal lemma (12) of `docs/run/12` §2, with the constant written out, and the
  spacing/multiplicity count behind (13) (`RH/Zeta85/Discharge/SignedShift.lean`);
* every exponent comparison of cycles 3, 4 and 5 (`RH/Zeta85/Discharge/Exponents.lean`);
* the logarithmic-power audit, including the two negative halves showing the budget does **not**
  close (`RH/Zeta85/Discharge/LogBudget.lean`);
* the dyadic → cumulative passage, reused verbatim from `Zeta23.cumulative_of_dyadic`.
