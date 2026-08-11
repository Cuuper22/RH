/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Hypotheses.lean — **the complete axiom set of the 85 % layer.**

This is the ONLY file in `RH/` that declares an axiom.  Everything else under `RH/Zeta85/` is proved
from Mathlib and from the base `Zeta23` library; `#print axioms` on the headline theorems of
`RH/Zeta85/Main.lean` reports `propext`, `Classical.choice`, `Quot.sound` and a subset of the eight
axioms below, and nothing else (`AXIOMS.md` reproduces the three outputs verbatim).

Each axiom carries: (a) its exact mathematical statement, (b) its source — the published paper with
proposition number, or the run file with equation number — and (c) why it was not discharged.  The
statements are rendered over the vocabulary of `RH/Zeta85/Arith.lean`, which is definitions only.

## What is deliberately NOT axiomatized here (it is proved)

* the three window moments and the certificate constant `c_pc` (`RH/Zeta85/Window.lean`,
  `RH/Zeta85/Certificate.lean`, Phase A);
* the count lemma `s + 2d + 2p ≤ N ∧ 3s+4d+4p ≥ (4−C)N ⟹ s ≥ (2−C)N` (Phase A3);
* the passage from a two-trace certificate to the ε-form (`RH/Zeta85/Transfer.lean`);
* `SaturatedWindowCost (143/100) D_pc` (`RH.Zeta85.windowCost_143`);
* the signed-shift reciprocal lemma of `docs/run/12` §2, equations (12)–(13)
  (`RH/Zeta85/Discharge/SignedShift.lean`, C1 — PROVED, not assumed);
* every exponent comparison of cycles 3, 4 and 5 (`RH/Zeta85/Discharge/Exponents.lean`);
* the logarithmic-power audit (`RH/Zeta85/Discharge/LogBudget.lean`, C7).

## Reading guide to the dependency layering

```
  bblr_error_bound  ──►  signedPair_traceGrade_lt_5_4  ─┐
                                                        ├─►  traceTransfer_saturated  ──► rungs
  bblr_poisson_blocks ─┐                                │            ▲
  shiu_majorant       ─┴► signedPair_traceGrade_lt_3_2 ─┘            │
                                                             windowCost_101 / _125
                                                             (windowCost_143 is PROVED)
```
Rungs 1 (0.679) and 2 (0.797) use the left branch only: the **published** BBLR error bound.  Rung 3
(0.85) uses the right branch: the run's cycle-5 claim.  Neither branch is used by the other, so the
axiom sets of the three rungs are genuinely different — see `AXIOMS.md`.
-/
import RH.Zeta85.Arith
import RH.Zeta85.Transfer
import RH.Zeta85.Statement
import Zeta23.Statement.SeamClosed

noncomputable section

namespace RH
namespace Zeta85
namespace Hypotheses

open Zeta23

/-! ## 1. Published literature: the quadratic divisor problem -/

/--
**AXIOM 1 — BBLR Proposition 3.1, the error bound.**

*Exact statement.*  Let `A, B, M₁, M₂, N₁, N₂, H ≥ 1`, `M = M₁M₂`, `N = N₁N₂`, let `α_a`, `β_b` be
complex coefficients and `W₁, …, W₄` smooth weights supported in `(1,2)`, and suppose
  `W_i^{(j)} ≪ (ABMN)^ε` for `0 ≤ j ≤ 4`,  `α_a ≪ A^ε`,  `β_b ≪ B^ε`,
  `M₁ ≤ M₂(ABMN)^ε`,  `N₁ ≤ N₂(ABMN)^ε`,  and  `H ≪ (AB)^{1/2+ε}`.
Then, for
  `S₊ = Σ_{a m₁ m₂ − b n₁ n₂ = h ≠ 0} α_a β_b W₁(m₁/M₁)W₂(m₂/M₂)W₃(n₁/N₁)W₄(n₂/N₂)·w(h/H)`,
one has `S₊ = M + E`, where `M` is the `(am₁, bn₁) = d` gcd main term and
  `E ≪_ε (ABMNH²)^{1/4+ε}·( AB + H^{1/4}(A+B)^{1/2}(ABMN)^{1/8} )`.

**The first factor inside the bracket is `AB`, not `(AB)^{1/2}`.**  `docs/run/03_arithmetic_cycle3.md`
(12) writes `(AB)^{1/2}` and its exponent conclusion (16) `E₁ = T^{1/2+2η}` is therefore too
optimistic; `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` (3), (5) has the correct form
`E_A = T^{1/2+3η}`.  The two differ by exactly `T^η`
(`RH.Zeta85.Exponents.misquote_gap`).  See `FINDINGS.md` §3.

*Source.*  S. Bettin, H. M. Bui, X. Li, M. Radziwiłł, "A quadratic divisor problem and moments of the
Riemann zeta-function", J. Eur. Math. Soc. **22** (2020), 3953–3980, Proposition 3.1 (error bound),
as quoted in `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` equation (3).

*Why not discharged.*  Published literature.  Its proof is a dispersion argument followed by Watt's
spectral estimate for sums of Kloosterman sums (Kuznetsov's formula and bounds for the exceptional
Maaß spectrum); formalizing it is out of scope for this artifact and is not attempted here (the task
specification directs that this be taken verbatim).  The main term is existentially quantified in
the Lean rendering, which makes the axiom **weaker** than the published statement.
-/
axiom bblr_error_bound : BBLRErrorBound

/--
**AXIOM 2 — BBLR Proposition 3.1, the Poisson-stage identity (their equation (14)), with the
cycle-5 block bound.**

*Exact statement.*  In the proof of BBLR Proposition 3.1, after writing `d = (am₁, bn₁)`,
`d₁d₂ = d₃d₄ = d`, `p = (a/d₁)(m₁/d₂)`, `q = (b/d₃)(n₁/d₄)`, Poisson summation in the two long
variables presents the nonzero-frequency part of `S₊` as a fixed finite sum of

  `R_d = Σ_{ℓ≠0} Σ_{p ≍ P_d, q ≍ Q_d, (p,q)=1} c_{d,p} e_{d,q} F_{d,ℓ}(p,q) Σ_h w_d(h) e(∓ℓ h p̄/q)`,
  `P_d ≍ AM₁/d`,  `Q_d ≍ BN₁/d`,  `w_d(h) = W₀(dh/H)`,  `H_d = H/d`,

and the Fourier integral obeys the separation bound
`‖F_{d,ℓ}‖_sep ≪_J d(1+|ℓ|d)^{−J}(log T)^{C_J}` for every fixed `J`.  Combining that decay with the
signed-shift lemma (proved here, `RH.Zeta85.SignedShift`) and the progression majorants gives the
per-block bound `|R_d| ≪ P_d(Q_d + H_d)(1+d)^{−2}(log T)^C`, which is what the Lean statement
records.

*Source.*  BBLR (as in Axiom 1), the displayed equation (14) inside the proof of Proposition 3.1;
transcribed with the block scales at `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §1,
equations (5)–(7), (9)–(11), and combined at §3, equations (16)–(17).

*Why not discharged.*  The identity itself is published literature (as Axiom 1).  The per-block
bound it is stated with is `docs/run/12` (17), which is a *derived* statement of the run; the pieces
of that derivation that could be discharged here have been: the signed-shift reciprocal lemma
(12)–(13) is proved in `RH/Zeta85/Discharge/SignedShift.lean`, and every exponent comparison of §3 is
proved in `RH/Zeta85/Discharge/Exponents.lean`.  What survives is the identity (14) itself together
with the claim that the recombined coefficients `c_{d,p}`, `e_{d,q}` are the actual fixed-depth
convolution coefficients with the stated majorants — neither is formalizable here without the whole
Heath–Brown apparatus.  This axiom is used by rung 3 only.
-/
axiom bblr_poisson_blocks : BBLRPoissonBlocks

/-! ## 2. The run's arithmetic claims -/

/--
**AXIOM 3 — the Shiu-type progression majorant (C3).**

*Exact statement.*  `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` (14): for the
recombined Heath–Brown coefficients `c_p` (defined at `docs/run/08` §2 and `docs/run/12` §1), which
are divisor-bounded,

  `Σ_{p ≍ P, p ≡ r (mod q), (r,q) = 1} |c_p| ≪ (P/φ(q))·(log T)^C`,

uniformly for `q ≤ P·T^{−η+o(1)}`, with `C` fixed.  The source's own justification: "fix every short
factor, and the remaining smooth factor occupies one residue class; the interval contains
`P/q ≫ T^{η−o(1)}` representatives.  Equivalently, (14) is the standard Shiu/Brun upper bound for a
fixed-divisor majorant."

*Source.*  `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §2, equation (14).  The
underlying published result is P. Shiu, "A Brun–Titchmarsh theorem for multiplicative functions",
J. Reine Angew. Math. **313** (1980), 161–170.

*Why not discharged.*  A full proof was attempted along the route the source indicates and did not
close in Lean: Shiu's theorem is not in Mathlib, and its hypotheses (a multiplicative,
non-negative, sub-multiplicatively bounded majorant, together with the uniformity range
`q ≤ P^{1−δ}`) do not apply verbatim to the run's `c_p`, which are *signed* convolutions of Möbius
and smooth factors rather than a multiplicative majorant.  The source's "fix every short factor"
reduction is a rearrangement that presupposes the factorization of the recombined coefficients, and
that factorization is exactly the unformalized Heath–Brown apparatus.  What could be discharged —
the elementary counting once a divisor majorant is granted — is subsumed by the statement below and
is not separable from it.  This axiom is used by rung 3 only.
-/
axiom shiu_majorant : ∀ η : ℝ, 0 < η → η < 1 / 2 → ShiuMajorant η

/--
**AXIOM 4 — the block closure at support `< 5/4` (C5), transported to the aggregate criterion.**

*Exact statement.*  `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §2, "Theorem (fixed
support)" together with its "block closure": fix `κ > 0`, `η = 1/4 − κ`, `σ = 1 + η`, `X = T^σ`,
`H = X/T = T^η`.  Choose a Heath–Brown depth `K` so large that every truncated irregular factor has
length at most `X^{1/K} < H·T^{−10ε}`.  After dyadic subdivision and the factor-grouping dichotomy
applied to both von Mangoldt factors, every block is either (i) a Type-I block with a long smooth
`1`- or `log`-variable, evaluated by Poisson summation plus the hybrid large sieve with
`O_A(X log^{−A} X)`, or (ii) the terminal BBLR block with grouped irregular factors
`A, B = H·T^{O(ε)}`.  "There is no third block."  Feeding (ii) into Axiom 1 gives errors
`E_A = T^{5/4−3κ+ε}`, `E_W = T^{5/4−2κ+ε}` against the trace scale `T^{5/4−κ}`, both power-saving;
the diagonal and the four zero-frequency terms recombine to the Ramanujan main term.  Hence the
signed aggregate criterion `(AS)` of `docs/run/01_arithmetic_cycle1.md` §4 holds at every fixed
`1 < σ < 5/4`.

*Source.*  `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §2 (block closure, (T1)–(T5)),
combined with `docs/run/01_arithmetic_cycle1.md` §4 (AS) and
`docs/run/02_certificate_cycle2.md` §3 (18) for the shape of the criterion.

*Why not discharged.*  Three separate obstacles, each attempted.  (i) The Heath–Brown identity of
arbitrary fixed depth and the factor-grouping dichotomy are not in Mathlib and would have to be
built from scratch (the identity itself, its Type-I/Type-II split, and the dyadic bookkeeping).
(ii) The Type-I estimate needs Poisson summation for the long smooth variable together with the
hybrid large sieve, neither available in the required uniform form.  (iii) The claim "there is no
third block" is a combinatorial statement about the grouping procedure that cannot be stated, let
alone proved, without (i).  What *was* discharged: the entire exponent bookkeeping (i)–(iii) rests
on, in `RH/Zeta85/Discharge/Exponents.lean` (`bblr_blackbox_ceiling`, `bblr_savings`,
`EA_traceGrade_iff`, `EW_traceGrade_iff`), and the observation that the resulting power saving
dominates any fixed logarithmic loss (`RH.Zeta85.LogBudget.power_beats_log`).
This axiom is used by rungs 1 and 2 only.
-/
axiom signedPair_traceGrade_lt_5_4 :
    BBLRErrorBound → ∀ σ : ℝ, 1 < σ → σ < 5 / 4 → SignedPairTraceGrade σ

/--
**AXIOM 5 — the terminal remainder bound at support `< 3/2` (C4), transported to the aggregate
criterion.**

*Exact statement.*  `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` (2): for every fixed
`0 < η < 1/2`, with `A = B = H = T^η`, `M = N = T`, the terminal Heath–Brown remainder satisfies

  `R_HB ≪ (T^{1+η} + T^{1/2+2η})·(log T)^C`,

`C` fixed by the finite identity and the fixed smooth weights; consequently — §5 — the signed
aggregate criterion `(AS)` holds at every fixed connected support `1 < σ = 1 + η < 3/2`.

*Source.*  `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md`, equation (2), proved there from
(6)–(19); the transport to `(AS)` is its §5.

*Why not discharged, and the DEFECT this axiom papers over.*  Two distinct reasons, and the second
is a genuine gap in the source, not a formalization difficulty.

1.  The derivation of (2) needs the block decomposition (Axiom 2), the progression majorant
    (Axiom 3), and the Heath–Brown recombination (as in Axiom 4).  The two pieces that could be
    discharged were: the signed-shift reciprocal lemma (12)–(13), proved in
    `RH/Zeta85/Discharge/SignedShift.lean`, and the exponent comparisons (18)–(19), proved in
    `RH/Zeta85/Discharge/Exponents.lean` (`cycle5_scales`, `cycle5_traceGrade`, `cycle5_gain`).

2.  **Even granting (2) in full, it does not imply `(AS)`.**  `(AS)` demands a logarithmic *saving*
    `≪_A X(log X)^{−A}` for every `A`; (2) supplies a logarithmic *loss* `(log T)^{+C}`.  The
    normalization audit in `RH/Zeta85/Discharge/LogBudget.lean` computes the budget exactly: the
    trace main term is `≍ T·L³`, of which `L²` is spent on the two von Mangoldt weights and one `L`
    is consumed by the entry scale `(T·L/X)` of `docs/run/01_arithmetic_cycle1.md` §4, so the
    surviving room for the error's logarithms is `(log T)^{<2}` in the most generous single-block
    reading and `(log T)^{<0}` once the `O(log X)` dyadic prime scales and `O(log X)` dyadic shift
    scales of `docs/run/02_certificate_cycle2.md` (14) are restored
    (`LogBudget.budget_closes` / `budget_fails`, `budget_dyadic_closes` / `budget_dyadic_fails`).
    The Heath–Brown depth forced at `η = 43/100` is `K ≥ 4` (`LogBudget.depth_at_85`), giving
    `C ≥ K − 1 ≥ 3`; both thresholds fail (`LogBudget.verdict`).  `docs/run/12` §5's assertion that
    "the two explicit logarithmic weights from the two von Mangoldt factors are below the accepted
    `Tℓ³` trace normalization after recombination" is therefore not established by the run.

    In accordance with R2 the 85 % target is **not** weakened to accommodate this.  Instead the
    exact blocking statement — the aggregate criterion at the strength the transfer consumes — is
    what this axiom asserts, and the shortfall is recorded here, in
    `RH/Zeta85/Discharge/LogBudget.lean`, and in `FINDINGS.md` §7.  This axiom is used by rung 3
    only, and it is the single most load-bearing undischarged statement in the artifact.
-/
axiom signedPair_traceGrade_lt_3_2 :
    BBLRPoissonBlocks → (∀ η : ℝ, 0 < η → η < 1 / 2 → ShiuMajorant η) →
    ∀ σ : ℝ, 1 < σ → σ < 3 / 2 → SignedPairTraceGrade σ

/-! ## 3. The two transcendental window costs -/

/--
**AXIOM 6 — the support-101/100 window cost.**

*Exact statement.*  `docs/run/07_root_gain_support_1p01.md`: at `λ = 101/100` with the
Montgomery–Taylor window `v(s) = cos(√2 s)` on `[−1/2,1/2]` and the saturated pair kernel
`K_λ(s,t) = min(λ|s−t|,1)`,

  `I₁ = ∫v = 2sin(√2/2)/√2 = 0.9187253698655684…`,
  `I₂ = ∫v² = 1/2 + sin√2/(2√2) = 0.8492279993183042…`,
  `J_λ = 2λ∫₀^{1/λ} d·A(d) dd + 2∫_{1/λ}^1 A(d) dd = 0.27396852346630846…`,
  `A(d) = ((1−d)/2)cos(√2 d) + sin(√2(1−d))/(2√2)`,
  `D_{1.01}(v) = (I₂ + λJ_λ)/(λ I₁²) = 1.32075113693…`,

so `2 − D_{1.01}(v) = 0.67924886307…`.  The axiom asserts `SaturatedWindowCost (101/100)
(2 − 0.67924886307)`, i.e. the cost at the *truncated* decimal, which is the weaker assertion.

*Source.*  `docs/run/07_root_gain_support_1p01.md`, "Explicit numerical certificate".

*Why not discharged.*  The window is transcendental.  Discharging the statement means proving a
rational bound for `(I₂ + λJ_λ)/(λI₁²)` where the three moments are values of `sin`, `cos` and
polynomial-times-trigonometric integrals at `√2`; that requires certified interval arithmetic on
those transcendentals to about 12 significant figures, which Mathlib's `norm_num` extensions do not
provide for `Real.sin`/`Real.cos` at irrational arguments.  A numerical verification to double
precision was carried out outside Lean and is recorded in `FINDINGS.md` §4: the computed value is
`2 − D = 0.6792488630700078…`, so the truncation `0.67924886307` is on the safe side (the axiom is
weaker than the source's claim).  The corresponding statement for the *rational* window at
`σ = 143/100` is not an axiom: it is proved, as `RH.Zeta85.windowCost_143`.
-/
axiom windowCost_101 : SaturatedWindowCost (101 / 100) (2 - cRung101)

/--
**AXIOM 7 — the support-5/4 window cost.**

*Exact statement.*  `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §3 (11)–(16): for the
saturated kernel `K(t) = min(|t|,1)` at `σ = 5/4`, the Euler equation `u(x) + ∫min(|x−y|,1)u(y)dy = C`
has the even solution `u(x) = cos(√2 x)` on `|x| ≤ 3/8` and
`u(x) = A₀cos(|x|−1/2) + B₀ sin(√3(|x|−1/2))` on `3/8 ≤ |x| ≤ 5/8`, with
`A₀ = 0.765651150533640…`, `B₀ = −0.479300891051646…`; then `∫u = 1.09716424928793…`,
`C = 1.31965363103003…`, `D*_{5/4} = C/∫u = 1.20278584713866…`, `2 − D*_{5/4} = 0.79721415286134…`.
Since `σ ↑ 5/4` is a limit, the axiom asserts the cost at *some* `σ` strictly between `1` and `5/4`,
which is what the theorem at a fixed support needs, and at the *truncated* decimal.

*Source.*  `docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §3, equations (11)–(16); the same
numbers appear at `docs/run/03_arithmetic_cycle3.md` §5 (32)–(37).

*Why not discharged.*  As for Axiom 6, plus: the profile is only characterised as the solution of an
integral (Euler) equation, so discharging it also requires proving that the displayed piecewise
function *is* that solution.  A numerical verification outside Lean is recorded in `FINDINGS.md` §4:
`u` satisfies the Euler equation to `1·10⁻⁹` uniformly on the support (limited by the 15 digits of
`A₀, B₀` given in the source), `∫u = 1.0971642492879266…`, `C = 1.3196536309619744…`,
`D = 1.2027858470766308…`, `2 − D = 0.7972141529233692…`; the truncation `0.79721415286134` is on
the safe side.
-/
axiom windowCost_125 :
    ∃ σ : ℝ, 1 < σ ∧ σ < 5 / 4 ∧ SaturatedWindowCost σ (2 - cRung125)

/-! ## 4. The trace transfer -/

/--
**AXIOM 8 — the trace transfer beyond bandwidth one (C6).**

*Exact statement.*  Let `1 < σ < 3/2` and let `D` be an achievable saturated-kernel cost at support
`σ` (`SaturatedWindowCost σ D`, i.e. `D = (∫v² + σ∬min(σ|s−t|,1)vv)/(σ(∫v)²)` for a positive profile
`v` on `[−1/2,1/2]`).  Assume the signed prime-pair aggregate criterion `(AS)` at support `σ`.  Then
the zeros of `riemannZeta` carry a two-trace certificate at cost `D`: there is a Gabor family, at
support `σ`, whose hat-unit Gram matrix `Ĝ_T` satisfies

  `4·tr Ĝ_T − ‖Ĝ_T‖²_F − 2·N(T,2T) − o(N) ≤ N₀ˢ(T,2T)`   (Seam A),
  `tr Ĝ_T = N(T,2T)·(1+o(1))`                              (`[eq:tr1]`),
  `‖Ĝ_T‖²_F ≤ (D + o(1))·N(T,2T)`                          (the second moment at support `σ`).

*Source.*  The `σ ≤ 1` case is the base paper's Proposition 5.6 together with §§2, 4, 6, formalized
in this repository (`Zeta23/PrimeSideB/`, `Zeta23/ThmD/Traces.lean`,
`Zeta23.ThmD.tracesBoundsD_concrete`); the extension to `1 < σ < 3/2` with the **saturated** kernel
`K(t) = min(σ|t|,1)` is `docs/run/01_arithmetic_cycle1.md` §2 (equations (5)–(9)),
`docs/run/01_certificate_cycle1.md` (5)–(6), `docs/run/02_arithmetic_cycle2.md` §1 and
`docs/run/02_certificate_cycle2.md` §2 (equations (13)–(17)), and `docs/run/12` §5.

*What is reused rather than assumed.*  Everything on the zero side.  Seam A
(`Zeta23.Assembly.seamA_mult2`) is proved in the base repository for an arbitrary `Zeta23.Params`
family and carries no restriction `λ ≤ 1`: it consumes only `PhiHatConj`, `PhiHatReal`, `PoissonSq`
and `TailInputs`, and the Poisson identity behind `PoissonSq`
(`Zeta23.Taper.hasSum_phiHatR_sq`) needs only `TaperProfile ϱ`, `0 < w`, `2w ≤ L`.  The rank–trace
inequality (`RHLinalg.rank_trace_ineq`), the `c = 2` multiplicity-aware count
(`Zeta23.ZeroSide.ZeroBlockData.mult_two`) and the fixed-`T` algebra
(`Zeta23.ThmD.N0star_lower_c`) are likewise reused verbatim; see `docs/REUSE_MAP.md` §5.

*Why not discharged.*  What genuinely fails past `λ = 1` is the base repository's error bookkeeping
`ℰ_T = w/L + (l² + X)·log l/(T·l) + T^{λ/2−1}` (`Zeta23.Params.calE`): the summand `X·log l/(T·l)`
with `X = (T/2π)^λ` tends to `0` **iff** `λ ≤ 1`.  Rebuilding the whole of `Zeta23/PrimeSideA/`,
`Zeta23/PrimeSideB/` and `Zeta23/ThmD/Traces.lean` with the saturated kernel and the new
pole/tail/zero-mode accounting of `docs/run/01_arithmetic_cycle1.md` §6 is a development of the same
order as the base repository itself, and its analytic content — the evaluation of the singular-series
main term at frequencies `|α| > 1` with the exact kernel `K(t) = min(λ|t|,1)` — is precisely the new
mathematics of the run.  Only the *genuinely new* part is assumed: the support-beyond-one evaluation.
This axiom is used by all three rungs.
-/
axiom traceTransfer_saturated :
    ∀ σ D : ℝ, 1 < σ → σ < 3 / 2 → SaturatedWindowCost σ D → SignedPairTraceGrade σ →
      TwoTraceCert zetaZeroConfig D

end Hypotheses
end Zeta85
end RH

end
