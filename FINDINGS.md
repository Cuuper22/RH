# FINDINGS.md — where the run documents were wrong, imprecise, or unprovable as written

Every section below is populated; where a phase produced no failure, the affirmative verification
note is recorded instead of an empty heading.  Source files are those unpacked into `docs/run/`.

---

## 1. Setup and reading (S1–S3) — affirmative

All 21 markdown files and both PDFs in the initial archive were read.  The base repository builds clean at commit `3635e74`
(`lake build`, 9010 jobs, zero errors; the four `PrintAxioms` audits give the standard three axioms
on all 43 headline theorems).  One discrepancy between the task description and the repository, with
no consequence: the task refers to `Zeta23/ThmD/Final.lean` and `Zeta23/ThmD/Mult.lean` — both exist;
it also refers to a "Proposition 4.4 analogue" and a "Proposition 5.6 analogue", which are
`Zeta23.Assembly.seamA_mult2` / `RHLinalg.rank_trace_ineq` and
`Zeta23.ThmD.tracesBoundsD_concrete` respectively.  All reuse points are tabulated in
`docs/REUSE_MAP.md`.

**One structural fact discovered during S2, which shaped the whole design.**
`Zeta23.Params.Valid.lam_le_one` occurs 72 times in `Zeta23/`, and *every* occurrence is on the prime
side or inside the error bookkeeping `Zeta23.Params.calE`.  The zero side —
`Zeta23/ZeroSide/`, `Zeta23/Poisson.lean`, `Zeta23/Assembly/SeamMult.lean` — never uses it; in
particular `Zeta23.Taper.hasSum_phiHatR_sq` (Lemma poisson) needs only `TaperProfile ϱ`, `0 < w`,
`2w ≤ L`.  Consequently Seam A holds at *any* support and the 85 % axiom set could be confined to
prime-side statements.  What genuinely breaks past `λ = 1` is `calE`'s summand `X·log l/(T·l)` with
`X = (T/2π)^λ`, which tends to `0` iff `λ ≤ 1`.

---

## 2. Phase A — arithmetic core — affirmative, with one notational clarification

Everything asked for in A1–A3 is **proved** in Lean with no axiom
(`RH/Zeta85/Window.lean`, `RH/Zeta85/Certificate.lean`):

| claim | source | status |
|---|---|---|
| `A = ∫v = 1031/1200` | `01_certificate_cycle1.md` (9) | proved (`integral_vProf`) |
| `B = ∫v² = 1809683/2400000` | ibid. | proved (`integral_vProf_sq`) |
| `g(u)` = the displayed quintic | ibid. (8) | proved (`integral_autocorr`) |
| `J = 970487502160963/3017889594720000` | ibid. (9) | proved (`jSat_eq`) |
| `c_pc = 2227707598259143/2561811364469143` | ibid. (10) | proved (`cPC_eq`) |
| `c_pc > 20/23` | ibid. | proved (`cPC_gt`) |
| `2 − 1/c_pc = 1893603832049143/2227707598259143` | ibid. (11) | proved (`two_sub_inv_cPC`) |
| margin `= 1047470577429/44554151965182860 > 0` | ibid. (12) | proved (`margin_eq`, `margin_pos`) |
| count lemma (1)–(3) | `01_hybrid_cycle1.md` §1 | proved (`count_lemma`) |
| specialization `C = 23/20 − η` | ibid. (2)–(3) | proved (`count_lemma_85`) |

Every one of these was **independently confirmed by exact rational arithmetic outside Lean before
formalization** (Python `fractions`), and every one matched the source to the last digit.  The
external check also produced the two intermediate quantities that make the certificate transparent
and that are now separate Lean theorems: `λA² = 152003423/144000000` and
`B + λJ = 2561811364469143/2110412304000000` — note that the numerator of the second is *exactly* the
denominator of `c_pc`.  The integer cross-multiplication
`152003423 · 2110412304000000 = 144000000 · 2227707598259143` is proved by `decide`.

*Notational clarification (not an error).*  `01_certificate_cycle1.md` (9) introduces `J` both as the
two-dimensional integral `∬ min(λ|s−t|,1)v(s)v(t) ds dt` and as the one-dimensional expression
`2(λ∫₀^{1/λ}u g(u)du + ∫_{1/λ}^1 g(u)du)`.  The two agree (Fubini plus the evenness of the kernel),
but only the one-dimensional form is used anywhere downstream, and only it is needed to define the
achievable cost.  `RH/Zeta85/Certificate.lean` therefore takes the one-dimensional form as the
definition (`satJ`), and `RH.Zeta85.satJ_lam_vProf` identifies it with `jSat`.  The two-dimensional
identity is not proved and is not used; this is a deliberate scope decision, recorded so that no
reader mistakes `satJ` for an unjustified reformulation.

*Also confirmed:* the count lemma's nonnegativity hypotheses `s, d, p ≥ 0` are stated because the
source states them, but they are **not needed** — `(2) − 2·(1)` is already the conclusion.  The Lean
statement keeps them (with the `unusedVariables` linter locally disabled) so that it is the source's
statement verbatim.

---

## 3. The BBLR error bound: `docs/run/03_arithmetic_cycle3.md` (12) is wrong

**The exact statement attempted.**  `03_arithmetic_cycle3.md` §2, equation (12), states the
Watt-strengthened BBLR error as

    E ≪_ε (ABMNH_s²)^{1/4+ε} · ( (AB)^{1/2} + H_s^{1/4}(A+B)^{1/2}(ABMN)^{1/8} ) .

**The exact failure.**  The first factor inside the bracket is `AB`, not `(AB)^{1/2}`.
`docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` (3) has the correct form, and says so
explicitly ("The main correction is important: the first term in the BBLR error is `AB`, not
`(AB)^{1/2}`.  Thus this report supersedes the exponent substitution in cycle 3, equations
(12)–(20).").  The consequence is not cosmetic: at `A = B = H = T^η`, `M = N = T` the two readings
give

    misquoted:  E₁  = T^{1/2+2η}   →  trace-grade for η ≤ 1/2
    correct:    E_A = T^{1/2+3η}   →  trace-grade for η ≤ 1/4

so cycle 3's (19) ("the first term permits `η < 1/2`") is an artifact of the misquote.  Both readings
and the gap between them are **proved as real-arithmetic statements** in
`RH/Zeta85/Discharge/Exponents.lean`: `EA_exponent`, `E1_misquoted_exponent`, `misquote_gap`
(`= η`), `EA_traceGrade_iff`, `E1_misquoted_traceGrade_iff`.

**What replaced it.**  Axiom 1, `RH.Zeta85.Hypotheses.bblr_error_bound`, states the **corrected**
form (`RH.Zeta85.bblrErrorFactor` has `A*B`, not `(A*B)^{1/2}`), with the misquote flagged in its
docstring.  No statement in this artifact relies on the cycle-3 version.

*A second, smaller inconsistency in the same place.*  Cycle 3's conclusion `σ < 5/4` happens to
coincide with cycle 4's, but for a different reason: cycle 3 gets it from the Watt term alone, cycle
4 from *both* terms meeting the trace scale at `η = 1/4`.  `Exponents.bblr_blackbox_ceiling` records
the correct joint statement.

---

## 4. The two transcendental window costs: verified numerically, truncations checked

**What was attempted.**  Proving `SaturatedWindowCost (101/100) (2 − 0.67924886307)` and the `5/4`
analogue inside Lean, as was done for the rational window at `143/100`
(`RH.Zeta85.windowCost_143`, proved).

**The exact failure.**  Both windows are transcendental.  Rung 1's is `v(s) = cos(√2 s)`, whose three
moments are values of `sin`/`cos` at `√2` and of polynomial-times-trigonometric integrals; rung 2's
is only *characterised* as the solution of the Euler equation
`u(x) + ∫min(|x−y|,1)u(y)dy = C`, given numerically by `A₀ = 0.765651150533640…`,
`B₀ = −0.479300891051646…`.  Discharging either needs certified interval arithmetic on `Real.sin`,
`Real.cos` at irrational arguments to about twelve significant figures; Mathlib's `norm_num`
extensions do not provide it, and rung 2 additionally needs a proof that the displayed piecewise
function *is* the Euler solution.

**What was verified outside Lean** (120-node Gauss–Legendre, double precision):

*Rung 1, `λ = 101/100`, `v(s) = cos(√2 s)`:*

| quantity | source value | computed |
|---|---|---|
| `I₁ = ∫v` | 0.9187253698655684 | 0.9187253698655684 |
| `I₂ = ∫v²` | 0.8492279993183042 | 0.8492279993183042 |
| `J_λ` | 0.27396852346630846 | 0.2739685234663084 |
| `D_{1.01} = (I₂+λJ)/(λI₁²)` | 1.32075113693… | 1.3207511369299922 |
| `2 − D` | 0.67924886307… | **0.6792488630700078** |

`0.6792488630700078 ≥ 0.67924886307`, so the truncated literal used in the statement is on the safe
side: **the axiom is weaker than the source's claim**, and the theorem is not strengthened.

*Rung 2, `σ = 5/4`:*

| quantity | source value | computed |
|---|---|---|
| `∫u` | 1.09716424928793 | 1.0971642492879266 |
| `C` (Euler constant) | 1.31965363103003 | 1.3196536309619744 |
| `D*_{5/4} = C/∫u` | 1.20278584713866 | 1.2027858470766308 |
| `2 − D*` | 0.79721415286134 | **0.7972141529233692** |

The Euler equation was checked at nine interior points; `u(x) + ∫min(|x−y|,1)u(y)dy` is constant to
`1·10⁻⁹`, the residual being consistent with the 15 published digits of `A₀`, `B₀`.  Again
`0.7972141529233692 ≥ 0.79721415286134`, so the truncation is on the safe side.

**What replaced them.**  Axioms 6 and 7 (`windowCost_101`, `windowCost_125`), each asserting the cost
at the *truncated* decimal — the weaker assertion — with the full numerical certificate reproduced in
the docstring.  Rung 2's axiom additionally quantifies over "some `σ ∈ (1, 5/4)`" rather than
asserting the limit point, because `08` §3 obtains its constant as `σ ↑ 5/4`; asserting it *at* `5/4`
would be stronger than the source.

**Precedent for the truncation.**  The base repository's own `XiPrime` topic states truncated
decimals (`0.85838`, `0.92919`, `0.86864`, `0.93432`) in `comparator/Challenge/XiPrime.lean`.  Rung 3
needs no truncation: its constant is the exact rational `1893603832049143/2227707598259143`.

---

## 5. Shiu-type progression majorant (C3) — attempted, not discharged

**The exact statement attempted.**  `docs/run/12` §2 (14):
`Σ_{p ≍ P, p ≡ r (q), (r,q)=1} |c_p| ≪ (P/φ(q))·(log T)^C`, uniformly for `q ≤ P·T^{−η+o(1)}`, for
the recombined Heath–Brown coefficients `c_p` of `08` §2 / `12` §1.

**The exact failure.**  Two independent blockers.  (i) Shiu's theorem (J. Reine Angew. Math. 313
(1980) 161–170) is not in Mathlib, and its hypotheses require a *non-negative multiplicative*
majorant with a sub-multiplicative growth condition; the run's `c_p` are **signed** convolutions of
Möbius and smooth factors, so the theorem does not apply verbatim — one must first pass to `|c_p|`
and exhibit a multiplicative majorant, which the sources do not do.  (ii) The source's own
justification ("fix every short factor, and the remaining smooth factor occupies one residue class")
presupposes the explicit factorization of the recombined coefficients, i.e. the finite-depth
Heath–Brown identity, which is not formalized anywhere in this artifact or in Mathlib.

**What replaced it.**  Axiom 3, `RH.Zeta85.Hypotheses.shiu_majorant`, stated over the concrete
vocabulary `RH.Zeta85.ShiuMajorant` / `progressionSum` / `DivisorBounded` of `RH/Zeta85/Arith.lean`
(so the axiom is a statement about objects a reader can inspect, not an opaque constant).  It is used
by rung 3 only.

---

## 6. Signed-shift reciprocal lemma (C1) — PROVED

The task directed that this be proved rather than axiomatized, and it is:
`RH/Zeta85/Discharge/SignedShift.lean`, no axioms
(`#print axioms RH.Zeta85.SignedShift.shiftSum_decay` = the standard three).

*Equation (12)*, `|S_{H₀}(θ)| ≪_J H₀(1 + H₀‖θ‖)^{−J}`, is proved in the multiplicative form

    ‖S_{H₀}(θ)‖ · (1 + H₀‖θ‖)^J ≤ (J+5)·2^J·(K₀+K_J)·H₀

for `w ∈ C^J(ℝ)` vanishing outside `(1,2)` with `|w| ≤ K₀`, `|w^{(J)}| ≤ K_J`, every `H₀ ≥ 1` and
every real `θ` (`RH.Zeta85.SignedShift.shiftSum_decay`).  The constant is explicit; no `≪` is hidden.

*Deviation from the source's proof, deliberate.*  `docs/run/12` §2 says "Poisson summation gives
(12)".  Poisson summation for a `C^J` (not Schwartz) compactly supported weight requires either a
Schwartz-class detour or a separate justification of the interchange, and Mathlib's Poisson summation
formula is stated for functions with `rpow` decay on both sides.  The route taken here is the
equivalent elementary one — `J`-fold summation by parts against the geometric kernel — which yields
the same bound with a uniform explicit constant and no convergence bookkeeping.  Its four ingredients
are all proved: `bdiffIter_le` (iterated mean value theorem, `|Δ_c^J u| ≤ ‖u^{(J)}‖_∞ c^J`),
`abel_iter` (`(z−1)^j Σ u_k z^k = (−1)^j Σ (Δ^j u)_k z^k`), `norm_cexp_sub_one`
(`|e(x) − 1| = 2|sin πx|`) and `jordan` (`2|x| ≤ |sin πx|` for `|x| ≤ 1/2`), combining to
`four_nearInt_le_norm_cexp_sub_one` : `4‖θ‖ ≤ |e(θ) − 1|`.

*Equation (13)*, `Σ*_{r mod q} |S_{H₀}(ℓr/q)| ≪_J q + H₀(ℓ,q)`.  The source's proof has two halves
and both are proved:

* the spacing half — `nearInt_int_div` : `q ∤ a ⟹ ‖a/q‖ ≥ 1/q`, which is exactly the source's
  "the image of the reduced residues has spacing at least `(ℓ,q)/q`" once one writes `d = (ℓ,q)`,
  `ℓ = dℓ'`, `q = dq'` and observes `ℓr/q = ℓ'r/q'`;
* the counting half — `sum_over_separated` : for points labelled by arc index with fibres of size at
  most `m` and separation `δ`, obeying (12) at `J = 2`, the total is
  `≤ m·(C·H₀ + 2C/(H₀δ²))`.  At `δ = (ℓ,q)/q`, `m = (ℓ,q)` and on the range where the `h`-sum is used
  (`q ≍ H₀(ℓ,q)`, `docs/run/12` (9)) this is `q + H₀(ℓ,q)`.

**Scope note, recorded rather than hidden.**  `sum_over_separated` is stated for an arbitrary
labelling instead of for the specific map `r ↦ ℓr mod q`.  Supplying that labelling requires the
elementary fibre count `#{r < q : ℓr ≡ c (mod q)} ≤ (ℓ,q)`, which is standard but was not
formalized here; a first attempt using `Nat.ModEq.cancel_left_of_coprime` did not close and was
withdrawn rather than left half-done.  **No axiom was introduced for it**: (13) is a step inside the
justification of Axiom 2, and Axiom 2 already sits above it, so nothing in the formal development
depends on the missing instantiation.  The two proved halves are the content that (13) contributes.

---

## 7. The logarithmic-power audit (C7): **the powers do not close**

This is the most important finding.  It is treated in full in
`RH/Zeta85/Discharge/LogBudget.lean` (module docstring plus six proved theorems) and summarised here.

**The exact statement attempted.**  `docs/run/12` (2) plus §5: `R_HB ≪ (T^{1+η} + T^{1/2+2η})(log T)^C`
with `C` fixed, and hence the signed aggregate criterion `(AS)` of `01_arithmetic_cycle1.md` §4 at
every fixed `σ = 1 + η < 3/2`, because "the two explicit logarithmic weights from the two von
Mangoldt factors are below the accepted `Tℓ³` trace normalization after recombination".

**The exact failure, with the inequalities written out.**  Three facts from the sources:

1. on a dyadic prime block `n ≍ Y`, at a shift `h ≍ H_Y = Y/T`, the complete coefficient of
   `Λ(n)Λ(n+h)` is `≪ (L/Y)min(T, Y/h) + log L/Y = LT/Y + O(log L/Y)`
   (`02_certificate_cycle2.md` (10)) — **one** power of `L`;
2. hence an already-`h`-summed remainder of size `E` at length `Y` enters the second moment at scale
   `(T·L/Y)·E` (`01_arithmetic_cycle1.md` §4, which says "up to powers of L" and does not name the
   power — that is the imprecision);
3. the displayed sum in `02_certificate_cycle2.md` (14) runs over `O(log X)` dyadic prime scales,
   but its inner sum is directly over `h`; it does not display a second dyadic shift-scale sum.
   Thus the literal blockwise triangle inequality costs **one** further power.  A second is charged
   only in the more adversarial model that separately dyadicizes the `h`-sum and again uses triangle
   inequality.  The Heath--Brown identities and subdivisions add further unspecified fixed powers.

The budget's three logarithms are accounted for: the main term `T·L³/(2πλ²)·[…]` of
`02_certificate_cycle2.md` (16) carries `L²` from the two von Mangoldt weights and one further `L`
from the height kernel — the same `L` that reappears in 1.  So the two von Mangoldt logarithms are
**spent** inside the main term; they are not free room for the error.  Substituting `E ≪ X(log T)^C`:

    contribution ≍ (T·L/X)·X·(log T)^C = T·(log T)^{C+1}              (generous)
    contribution ≍ (log T)·T·(log T)^{C+1} = T·(log T)^{C+2}         (literal Y-dyadic)
    contribution ≍ (log T)²·T·(log T)^{C+1} = T·(log T)^{C+3}        (fully triangle-summed)
    budget       = T·(log T)³

Thus the three thresholds are respectively **`C < 2`**, **`C < 1`**, and **`C < 0`**.  All three
dichotomies are proved in Lean, in both directions: `LogBudget.budget_closes` / `budget_fails`,
`LogBudget.budget_primeDyadic_closes` / `budget_primeDyadic_fails`, and
`LogBudget.budget_dyadic_closes` / `budget_dyadic_fails`.

None of the three thresholds is available.  `08` §2 chooses the Heath–Brown depth `K` so that
`X^{1/K} < H·T^{−10ε}`, which forces `K > (1+η)/η`; at `η = 43/100` that is `K > 143/43 > 3`, hence
`K ≥ 4` (`LogBudget.depth_at_85`).  A depth-`K` identity replaces each von Mangoldt factor by `O(K)`
divisor-type convolutions whose dyadic mean value is of size `(log X)^{K−1}`, and the BBLR weight
hypotheses `W_i^{(j)} ≪ (ABMN)^ε` do not remove them.  So `C ≥ K − 1 ≥ 3`, and
`C + 1 ≥ 4 > 3`, `C + 2 ≥ 5 > 3`, and `C + 3 ≥ 6 > 3` (`LogBudget.verdict_all`).

At the level of the formal statement there is a stronger mismatch: `(AS)` demands a logarithmic
*saving* `≪_A X(log X)^{−A}` for every `A`, while (2) supplies a logarithmic *loss*
`(log T)^{+C}`.  No rearrangement of (2) produces `(AS)`.  This is not a second necessity argument,
because `(AS)` is stronger than the exact weighted budget (18); it explains why the current Lean
predicate cannot be discharged from (2).

**What replaced it, and what was NOT done.**  Per R2 the target is **not** weakened: the 85 %
statement remains `liminf N₀ˢ/N ≥ 1893603832049143/2227707598259143`.  Instead the exact blocking
statement is named and isolated as Axiom 5,
`RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_3_2`, whose docstring records this defect in full.
The consequence for a reader is precise: **`docs/run/12` (2) does not establish the input the 85 %
theorem needs**, and the artifact says so rather than absorbing the discrepancy into an implied
constant.

**The two lower rungs are unaffected**, and this is why their axiom sets are genuinely weaker: at
`η < 1/4` the BBLR errors are *power*-saving relative to trace scale
(`Exponents.bblr_savings`: `T^{5/4−3κ}`, `T^{5/4−2κ}` against `T^{5/4−κ}`), and a fixed power beats
every fixed logarithmic loss (`LogBudget.power_beats_log`, proved).

---

## 8. Block closure at support `< 5/4` (C5) — attempted, not discharged

**The exact statement attempted.**  `08` §2, "Theorem (fixed support)" and the block closure: the
depth-`K` Heath–Brown decomposition of both von Mangoldt factors, the factor-grouping dichotomy, the
Type-I estimate via Poisson summation plus the hybrid large sieve, the terminal BBLR family, and
"there is no third block".

**The exact failure.**  (i) The finite-depth Heath–Brown identity and its Type-I/Type-II grouping
lemma are not in Mathlib and would have to be built from scratch, together with the dyadic
bookkeeping.  (ii) The Type-I estimate needs Poisson summation in a long smooth variable *and* the
hybrid large sieve, in a uniform form that does not exist in Mathlib.  (iii) "There is no third
block" is a combinatorial statement about the grouping procedure and cannot even be stated without
(i).

**What was discharged.**  All of the exponent arithmetic the closure rests on, in
`RH/Zeta85/Discharge/Exponents.lean` — `outside_factor_exponent`, `EA_exponent`, `EW_exponent`,
`EA_traceGrade_iff`, `EW_traceGrade_iff`, `bblr_blackbox_ceiling`, `bblr_savings`,
`exponents_at_43_100`, `deficits_at_43_100`, `cycle5_scales`, `cycle5_traceGrade`, `cycle5_gain`,
`csqd_traceGrade`, `theta_at_benchmark`, `mrt_gap`, `mrt_alpha` — plus `LogBudget.power_beats_log`.

**What replaced it.**  Axiom 4, `RH.Zeta85.Hypotheses.signedPair_traceGrade_lt_5_4`, stated as an
implication from `BBLRErrorBound` so that the dependence on the published input is visible in the
Lean type and in `#print axioms`.

---

## 9. The trace transfer beyond bandwidth one (C6) — reused where possible, axiomatized where new

**What was reused rather than assumed** — the entire zero side, unchanged from the base repository:
`Zeta23.Assembly.seamA_mult2` (Seam A), `RHLinalg.rank_trace_ineq`,
`Zeta23.ZeroSide.ZeroBlockData.mult_two`, `Zeta23.ThmD.N0star_lower_c`,
`Zeta23.Taper.hasSum_phiHatR_sq`, `Zeta23.cumulative_of_dyadic`, `Zeta23.N0simple_add'`,
`Zeta23.zetaSeam`, `Zeta23.paperInputs_zeta`.  See `docs/REUSE_MAP.md` §§4–6.  As recorded in §1
above, none of these carries the restriction `λ ≤ 1`.

**What is genuinely new and therefore assumed.**  The support-beyond-one evaluation of the
second moment with the saturated kernel `K(t) = min(λ|t|,1)`, i.e. exactly the content of
`01_arithmetic_cycle1.md` §2 (5)–(9) and `02_certificate_cycle2.md` §2 (13)–(17).  Axiom 8,
`traceTransfer_saturated`, is stated as an implication taking the window cost and the aggregate
criterion as hypotheses, so it cannot smuggle in either the arithmetic or the numerics.

**The formal obstruction, identified precisely.**  `Zeta23.Params.calE` contains `X·log l/(T·l)`,
`X = (T/2π)^λ`, which tends to `0` iff `λ ≤ 1`.  Re-deriving the trace bounds at `λ > 1` means
rebuilding `Zeta23/PrimeSideA/`, `Zeta23/PrimeSideB/` and `Zeta23/ThmD/Traces.lean` with the new
pole/tail/zero-mode accounting of `01_arithmetic_cycle1.md` §6 — a development of the same order as
the base repository.

---

## 10. Statements in the run that are *not* used, and why — affirmative

Several routes in the archive are explicitly self-terminated by their own authors, and none of them
is relied on here.  Recorded so that a reader does not look for them in the formalization:

* the **hybrid / selector** route (`01_hybrid`, `02_hybrid`, `05_hybrid`, `06_hybrid`, `10_hybrid`,
  `11_hybrid`): `02_hybrid` §7 concludes "no honest unconditional constant above 0.6725007036… was
  derived on this route"; `11_hybrid` proves the sawtooth cancellation `M_s ≥ 0` and nothing more.
  Its useful residue — the count LP (1)–(3) of `01_hybrid` §1 — *is* used, and is Phase A3.
* the **Routh/resultant** route (`03_hybrid`, `04_hybrid`): `04_hybrid` §5 tabulates its own output
  as `0.4021932`, weaker than the accepted base.
* the **one-sided sieve** route (`04_certificate`): shown there to have an *infinite* limiting
  majorant cost, ratio `H_Y/L² → ∞`.
* the **quartic residual** route (`09_certificate`): would give `13/18 = 0.7222…`, weaker than rung 2,
  and its input is unproved.
* the **three-lobe sparse** construction (`01_arithmetic` §3): would give `0.8908336` but needs (AS)
  in the separated bands, i.e. strictly more than what rung 3 already assumes.

The formalized chain uses only: the count LP, the saturated-kernel functional, the BBLR inputs, the
cycle-4/cycle-5 aggregate criteria, and the base repository's zero side.

---

## 11. Summary table of replacements

| # | statement attempted | source | outcome |
|---|---|---|---|
| 1 | window moments, `c_pc`, margin, count lemma | `01_certificate`, `01_hybrid` | **proved** |
| 2 | `SaturatedWindowCost (143/100) D_pc` | ibid. | **proved** |
| 3 | signed-shift decay (12) | `12` §2 | **proved** (by summation by parts, not Poisson) |
| 4 | (13), spacing + counting halves | `12` §2 | **proved**; instantiation to `ℓr/q` left open, no axiom |
| 5 | exponent bookkeeping of cycles 3–5 | `03`, `08`, `12` | **proved** |
| 6 | log-power audit | `12` §5 | **proved — and the budget does not close** |
| 7 | BBLR Prop 3.1 error bound (corrected `AB`) | BBLR / `08` (3) | axiom 1 (published) |
| 8 | BBLR Poisson identity (14) + block bound | BBLR / `12` (6),(11),(17) | axiom 2 (published + derived) |
| 9 | Shiu progression majorant | `12` (14) | axiom 3 |
| 10 | block closure `σ < 5/4` ⟹ (AS) | `08` §2 | axiom 4 |
| 11 | cycle-5 remainder `σ < 3/2` ⟹ (AS) | `12` (2), §5 | axiom 5 — **and see §7** |
| 12 | window cost at `101/100` | `07` | axiom 6 (numerics) |
| 13 | window cost at `5/4` | `08` §3 | axiom 7 (numerics) |
| 14 | trace transfer at `1 < σ < 3/2` | `01`, `02`, `12` §5 | axiom 8 |

---

## 12. Phase 0 source intake and the withdrawn 100% terminal claim

The supplied analysis material consists of two physical ZIP archives plus two
logical loose-file batches from the supplied Google Drive folder.  All four
logical batches were ingested.  The terminal 95 batch is present, including
`24_TERMINAL_certificate95_cycle2_95p063832.md` and
`00_FINAL_95_RESULT_95p063832.md`; their presence passes the intake gate but
does not validate their claims.  The exact inventory is `docs/run/MANIFEST.md`.

`docs/run/100/FINAL_100_RESULT.md` is **WITHDRAWN**.  Two independent issues
are load-bearing.

1. The wide-block moment has no verified principal-compression / alias-
   cancelling construction.  The mission handoff additionally reports the
   pointwise-admissible maximum $M₂ ≤ 0.3144$ at $μ=2/3$, but no supplied
   file states the extra condition from which that number follows.  The
   independent reconstruction in `verify/withdrawn_100_claim.py` shows that
   the pointwise cone actually written in the source admits


   \[
   r(t)=V_{1.9999}(\mu t)\mathbf 1_{\{|t|\geq g/2\}},
   \qquad \int r=1,
   \]

   with $0 ≤ r(t) ≤ V_{1.9999}(μt)$ identically and
   $M₂=0.374347517070571…$.  The 50- and 80-decimal calculations agree
   within $10^{-51}$.  Thus $0.3144$ is **not reproduced** by the stated
   model and is not used as an established bound here.  An additional explicit
   admissibility condition—plausibly the missing R1a paraunitary/alias
   condition—is the exact blocker.
2. Even without the unverified $0.3144$ cap, the file's own premise package
   is inconsistent at $s/N=1$.  There $b/N=0$ and
   $ε=D−1<3385873/50000000$.  The stronger quadratic printed in the
   file and the charged stability inequality then force


   \[
   M_2<\frac{64517303}{172727100}
      =0.373521601416338\ldots,
   \]

   while the file assumes $M₂>18717/50000=0.37434$.  The excess of the
   assumed lower bound is exactly $70679807/86363550000>0$, and the direct
   trace-score gap is $6425437/25000000000>0$.

The simultaneous premises therefore describe an empty feasible class.  Their
contradiction indicts the block/moment premise and cannot prove density one.
The script output is committed as `verify/withdrawn_100_claim.out`; no theorem
or rung depends on the withdrawn source.

---

## 13. Phase 0d continuous-integration gate

`.github/workflows/ci.yml` installs the pinned Lean toolchain with the official
Lean action, fetches the Mathlib cache, builds `Zeta23`, `RH.Zeta85.Main`, and
`Solution.Zeta85`, diffs fresh Zeta85 headline axiom output against
`AXIOMS.md`, runs every existing base headline axiom audit, and rejects
proof-level `sorry`/`admit` outside comparator challenge files.  This is a
reproduction guard only: it discharges no mathematical input and changes no
rung status.

---

## 14. A1.1 evaluate-don't-bound — one exact method class killed

At \(P=T^{93/100}\), \(Q=T^{1/2}\), and \(H=T^{43/100}\), the literal
\(C=0\) target is the signed weighted progression estimate

\[
 \sum_{q\asymp Q} e_q\sum_{r\bmod q}^{*}
 S_H(\ell\bar r/q)E_c(P;q,r)\ll PQ,
\]

together with an identity matching every signed Heath--Brown progression
main term to the prime-pair singular-series subtraction.  If proved, this
target closes the literal log budget alone:
\(T(\log T)^2=o(T(\log T)^3)\).  The earlier Program status that also
required a cross-\(Y\) estimate in the \(C=0\) case was incorrect and is
corrected in `docs/audit/log_budget_routes.md`.

The published \(d_4\) mean-value route does not prove the target.  The exact
residue Parseval bound

\[
 \sum_{r\bmod q}^{*}|S_H(\ell\bar r/q)|^2
 \leq q(\lceil H\rceil+1)
\]

combined with Nguyen's Theorem 3 and Cauchy gives
\(T^{3917/2400}(\log T)^{15/2}\), exceeding
\(PQ=T^{143/100}\) by \(T^{97/480}(\log T)^{15/2}\).  Parry's Theorem 1,
Parseval, and absolute summation over the moduli give
\(T^{261/160+\varepsilon}\), exceeding \(PQ\) by
\(T^{161/800+\varepsilon}\).  Wei--Xue--Zhang's modulus range misses the
required exponent by \(1951/54312\); the unconditional
Rodgers--Soundararajan variance range stops below
\(\log P/\log Q=93/50\).

This is a finish-or-kill result only for the stated method class:

> published \(d_4\) progression mean value + norm bound in residues +
> absolute/Cauchy aggregation in \(q\).

It is not an impossibility result for the signed target itself.  Two further
statement gaps remain before exponents are considered: the actual
coefficients are signed, smoothly truncated Möbius/Heath--Brown convolutions,
not \(d_4\), and no cited theorem identifies the resulting blockwise main
terms with the singular-series subtraction.  Therefore no new `Inputs95`
field is attributed to the cited papers.  The next ordered route is A1.2,
the cross-\(Y\) signed estimate; `(WG-HB)` remains the final route.

---

## 15. A1.2 cross-scale signs — current method classes killed

On a local block \(Y=T^{1+\theta}\), cycle 5 has

\[
 H=T^\theta,\qquad P=H\sqrt T,\qquad Q=\sqrt T,
 \qquad PQ=Y,\qquad PH/Y=H/Q.
\]

Thus \(PH\) has a \(T^{-7/100}\) saving for
\(\theta\le43/100\), while \(PQ\) is critical.  The depth-four-compatible
band \(143/400+\varepsilon<\theta<43/100\) alone contains

\[
 \frac{29/400-\varepsilon}{\log2}\log T+O(1)
\]

dyadic critical blocks.  If \(A_j=(T/Y_j)E_{Y_j}\), the current premise is
only \(|A_j|\ll T(\log T)^C\).  An all-positive family saturates the
triangle inequality exactly, as proved by
`RH.Zeta85.LogBudget.blockwise_triangle_sharp`.

Equation (6) of the route document, even if granted verbatim, produces a
trace error \(O(T(\log T)^{C+1})\).  It closes only for \(C<2\).  At the
forced \(C\ge3\), it still exceeds the \(o(T(\log T)^3)\) budget by at least
one logarithm; `RH.Zeta85.LogBudget.crossScale_recombination_fails`
formalizes this comparison.  Even root-number-of-blocks cancellation closes
only for \(C<3/2\).

Five exact method classes are therefore finished and killed:

- recombination after cycle 5 has taken absolute values, because all
  cross-scale signs have already been erased;
- endpoint-phase cancellation, because
  \((n_j,h_j)=(2^jn_0,2^jh_0)\) makes
  \(T\log(1+h_j/n_j)\) constant in \(j\);
- Mellin orthogonality away from zero, because every dyadic partition of
  unity has Mellin zero mode \(\int\psi(u)du/u=\log2\);
- Cauchy/square-function arguments from the present per-block energy, which
  return the same full logarithm (or, with an idealized energy input, only
  its square root); and
- Abel summation without a new uniform dyadic-prefix bound, because that
  prefix bound is stronger than equation (6).

This is not an impossibility theorem for the actual signed Heath--Brown
coefficients.  Those coefficients are not constructed as a common-scale
object in the repository: \(c_{d,p}\) and \(e_{d,q}\) occur only in prose,
while `BBLRPoissonBlocks` hides scalar blocks existentially.  The exact
surviving statement is equation (14) of
`docs/audit/log_budget_routes.md`: construct compatible signed
families \(c_{j,d,p},e_{j,d,q},F_{j,d,\ell}\), cancel their zero terms
pointwise against the singular series before absolute values, and prove the
resulting common-scale leading family is \(o(T(\log T)^2)\).

The supplied archives and linked Drive folder contain no script or explicit
coefficient construction for the historical five-scale prime experiment.
The only Python source found in that Drive intake is
`sixth_block_search.py`.  Consequently the quoted z-scores
\(-0.15,-0.43,0.14,0.78,0.46\) cannot be rerun from supplied material and
are not used as evidence; no replacement experiment was fabricated.

---

## 16. B-2 Rudnick--Sarnak reduction — source scope corrected, bridge open

Rudnick--Sarnak (1996) Theorem 3.1, specialized to degree \(m=1\), is an
unconditional **smoothed** all-tuples correlation theorem at strict total
Fourier support below \(2\).  Its tuples include repetitions and zeros are
counted with multiplicity, matching a matrix trace expansion.  The paper's
Theorem 3.2 is the sharp-height variant and explicitly assumes RH; it cannot
be substituted in an unconditional rung.

The paper's Lemmas 4.2--4.3 give the distributional cyclic sinc transform and
the translated-interval intersection length.  They do not state the nonflat
profile formula or the constants \(1/3,7/60,1/30\).  In
`docs/audit/rs_reduction.md`, those constants are instead constructed
from the explicit cyclic symbol, and the disjoint-pair contractions are
expanded through the weighted formula

\[
\begin{aligned}
 M_2&=\int q^2+\mu^2\int rh,\\
 M_3&=\int q^3+3\mu^2\int qrh,\\
 M_4&=\int q^4+4\mu^2\int q^2rh\\
 &\quad+2\mu^2\iint q(x)r(x)q(y)r(y)|x-y|\,dx\,dy\\
 &\quad+2\mu^4\int r^2h^2+\mu^4\mathcal X(r),
\end{aligned}
\]

which is formula (18) of terminal file 24.  The reusable \(k=2\) repository
bridge is in `Zeta23/Poisson.lean` and
`Zeta23/PrimeSideA/EndsCore.lean`, not
`Zeta23/Taper.lean`.

`RH/Zeta85/Discharge/RSReduction.lean` now discharges the deterministic
finite layer.  It defines the gauge-fixed weighted cyclic symbol, proves its
zero-frequency value, proves every `rsPairVector` is zero-sum, and enumerates
the exact RS main terms for \(k=1,2,3,4\): no contraction, one pair, three
pairs, and six one-pair plus three two-pair contractions.  A separate
polynomial theorem proves formula (27) centers to formula (18) through
degree four.  Finally, the proved Mathlib top-hat integrals specialize this
identity to the repository's formula (21).

This does not yet discharge B-2.  The exact remaining blockers are:

1. prove smoothness and strict support for an admissible smoothed cyclic
   symbol and evaluate each displayed `rsPairIntegral`, thereby connecting
   `rsMainTerm` to the uncentered contraction formula;
2. instantiate the published `RS1996ZetaInputs.theorem31` field for zeta;
3. supply the R1a principal-block identification for the weighted cyclic
   symbol;
4. extend the real-argument Poisson theorem to actual complex zero
   ordinates, or give another unconditional bridge;
5. prove the \(k=3,4\) Fubini and finite-grid end estimates;
6. construct a simultaneous smooth-height limit whose normalization factors
   tend to one for \(1\le k\le4\);
7. carry the exact conversion
   \(\mu_T=\mu\log(T/2\pi)/\log T\to\mu\); and
8. take the top-hat smoothing limit after \(T\to\infty\), with the required
   uniform domination and strict admissibility margin.

The remaining actual-block limit is still the explicit
`BlockMomentLimits` structure.  No instance is constructed, no new research
axiom is declared, and no rung status or dependency changes.

---

## 17. B-1 quartic stability inequality — discharged

`RH/Zeta85/Stability.lean` proves the exact finite-dimensional
statement from `docs/audit/stability_inequality_proof.md`.  For
\(G=P+Q\), with \(P\succeq0\),
\(\operatorname{rank}P\le s\), \(\operatorname{tr}P\le s\),
\(n_+(Q)\le b\), \(s+2b\le N\),
\(\operatorname{tr}G=N\), and
\(\lVert G\rVert_F^2\le DN\), it proves

\[
 \sum_{i>b}(\lambda_i(G)-1)_+^2\le s-(2-D)N.
\]

The formal proof constructs rather than assumes both interlacing steps:

- a threshold-count rank-update theorem for adding a positive-semidefinite
  matrix, yielding the rank-\(b\) Weyl inequality; and
- a threshold-count hard-Sylvester theorem for isometric compressions,
  yielding Cauchy interlacing and the principal-compression bound.

It then formalizes the scalar positive-excess estimate, the bound
\(n_+(P-Q_-)\le\operatorname{rank}P\), and the exact nonnegative slack
decomposition using
\(\operatorname{tr}(PQ_+)\ge0\) and the rank--trace square inequality.
The public theorems
`stability_inequality`,
`tailExcessSq_isometricCompression_le`,
`tailExcessSq_principalCompression_le`,
`stability_inequality_isometricCompression`, and
`stability_inequality_principalCompression` introduce no field and
depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

This discharges the stability inequality only.  It does not supply the R1a
principal block to which the compression theorem would be applied, so the
quartic rung statuses remain unchanged.

---

## 18. A1.3 Weil-grade HB — one-shot class killed, simultaneous route open

At
\[
 \eta=\frac{43}{100},\qquad H=T^\eta,\qquad Q=T^{1/2},
 \qquad P=HQ,\qquad HQ^2=T^{143/100},
\]
any bound
\[
 \sum_{q\asymp Q}|\mathcal R_{q,\ell}|
 \ll HQ^2T^{-\delta}(\log T)^B
\]
with fixed \(\delta>0\) closes the log budget.  Summing the \(O(\log T)\)
prime blocks after multiplying by \(T/Y\) gives
\(T^{1-\delta}(\log T)^{B+1}=o(T(\log T)^2)\), leaving the trace contribution
\(o(T(\log T)^3)\).

The proposed simultaneous quadratic-dispersion right side
\[
 T^{1/2+2\eta+\varepsilon}+T^{3/4+3\eta/2+\varepsilon}
\]
has exponents \(34/25+\varepsilon\) and
\(279/200+\varepsilon\).  Its limiting saving is \(7/200\);
\(\varepsilon=7/400\) leaves the explicit net
\(\delta=7/400\).  This is a sufficient conditional calculation, not a
proof of the estimate.

The exact class \(\mathcal W_1\) is finished and killed.  It consists of
arguments that use independent progression-cell sizes, complete at most one
variable and sum the rest by triangle/Cauchy, or apply one
arbitrary-coefficient trilinear/fixed-modulus bilinear Kloosterman theorem
without simultaneously exploiting two retained Heath--Brown factors.

- Parseval gives
  \(\sum_r|S_H(r/q)|^2\asymp qH\) and hence
  \(\sum_{r\ne0}|S_H(r/q)|\gg q\).  Independent admissible cell phases of
  size \(P/q\asymp H\) align to give
  \(\gg HQ^2/\log Q\), ruling out every fixed power saving in that class.
- One completion plus Weil gives \(T^{161/100}\), an excess \(T^{9/50}\).
- Bettin--Chandee Theorem 1 gives
  \(T^{3627/2000}\) and \(T^{719/400}\); its larger term exceeds the target
  by \(T^{767/2000}\).
- The applicable BBLR/Kuznetsov architecture gives
  \(T^{179/100}\) and \(T^{161/100}\), again above the target.
- The 2025--2026 Blomer--Pascadi and Milićević--Qin--Wu preprints are outside
  the required length \(H=q^{43/50}\); Wright's fixed-denominator gain does
  not improve the unavoidable \(d=1\), \(R=1\) block.

This is not an impossibility theorem for simultaneous coefficient-sensitive
cancellation.  The repository does not define the needed object: it lacks
the signed depth-four expansions of both von Mangoldt factors, formulas and
norms for \(\alpha_a,\beta_m,e_q\), common divisor bookkeeping, the exact
\(F_{q,\ell}(a,m)\) with theorem-compatible regularity, and the pointwise
zero-mode/singular-series identity.  The exact surviving statement is
`(WG-HB)` in `docs/audit/log_budget_routes.md`; it remains
unproved and cannot yet be faithfully made an `Inputs95` field.

---

## 19. A2.1 R1a alias construction — critical-density TDAC class killed

The scalar power-complement identity in cycle 3 controls only the zero-alias
row of the Poisson formula.  It does not imply the nonzero alias equations
needed for the asserted Gram matrix.  A Princen--Bradley sign pair can cancel
one cross alias, so positivity alone is not the obstruction.

For the exact finite common-lattice class used by cycle 3, let the full
support be \(S=Na\), the periods be \(L_j=n_ja\), and retain the asserted
critical count \(\sum_j n_j=N\).  Fiberization modulo \(a\) expresses the
\(j\)-th window contribution as a sum of \(n_j\) rank-one outer products,
so it has rank at most \(n_j\).  The distinguished window is supported in
one period and is therefore alias-free.  If its residual energy \(v-r\) is
positive on every fiber, the complementary diagonal has rank \(N\), whereas
all remaining channels have rank at most
\(\sum_{j>0}n_j=N-n_0<N\).  This contradiction is unchanged by arbitrary
real signs or complex phases.

`RH/Zeta85/Discharge/AliasRankObstruction.lean` machine-checks this finite
rank argument.  It proves the rank bound for an explicit sum of residue
outer products, the full-rank diagonal lemma, the full-minus-distinguished
matrix form of (13)--(16), and the exact `19999/4999`, `14999/4999`, and
`1499999/499000` count corollaries.  The analytic premise in those
corollaries is exactly that every sampled residual entry is nonzero; it is
not replaced by a stronger or conclusion-shaped assumption.

`verify/a2_1_tdac_rank.py` reconstructs the terminal Euler profiles and
certifies their signs using exact rational intervals for square roots and
Taylor remainders.  It proves the conservative margins

\[
 V_{19999/10000}\bigl(\mu(83/100)/2\bigr)-100/83>1/1000,
 \qquad
 V_{14999/10000}\bigl(\mu(89/100)/2\bigr)-100/89>1/1000,
\]

at \(\mu=4999/10000\), and the later Euler repair of file 15 has margin
greater than \(1/10\).  For file 15's original quadratic profile, the
hat-unit symbol is \(V=v/(1031/1200)\).  Its exact central edge residual is

\[
 V(\mu/2)-1=\frac{42756493}{1031000000}>0
\]

at \(\mu=499/1000\), so the rank obstruction applies directly.  The
normalized central average is
\(1157918831/1031000000>1\); there is no zero-row average contradiction.

This kills A2.1 only for finite commensurable systems with the cycle-3
coefficient count and the claimed distinguished symbols.  It does not rule
out oversampling or a separately derived noncommensurable architecture.
A2.2 has now been tested separately and killed at the base normalization;
every frozen quartic rung remains conditional on its own missing R1a
construction.

---

## 20. A2.2 R1a alias-free fallback — normalization and quartic class killed

The base Lemma 2.2 mechanism does give an exact alias-free construction:
partition the full length \(L=\sigma\ell\) into intervals, use one window
supported in each interval, and set its period equal to that interval's
length.  The obstruction is the global hat normalization, not aliasing.
For a cell of period \(L_j=\mu_j\ell\), cycle 3 uses amplitude
\((L/L_j)^{1/2}\).  Poisson and division by \(aL^2\) give block mean

\[
 \frac1{a\sigma L_j}\int|\varphi_j|^2
 =\frac1\sigma\int_{-1/2}^{1/2}r_j(t)\,dt.
\]

Thus an intrinsic mean-one block is the literal compression \(C=H/\sigma\),
and a prescribed mean-one symbol requires \(\sigma r\leq V_\sigma\), not
the terminal condition \(r\leq V_\sigma\).  For the quadratic profile,
\(\sup V_\sigma=1200/1031<143/100\), so no mean-one interval block exists
at any support in scope.

The requested restriction can nevertheless be constructed intrinsically.
With

\[
 x_0^2=\frac{\sigma^2-\mu^2}{12},\qquad
 r(t)=V_\sigma(x_0+\mu t),
\]

its intrinsic mean is exactly one.  The five-interval sharp partition is
alias-free almost everywhere.  Tapering its ten endpoints over physical
width \(w\) changes the global normalization by at most
\(10w/(\sigma\ell)\); after division by \(A=1031/1200\), the relative
full-energy loss is at most \(10w/(A\sigma\ell)\) and the distinguished
intrinsic mean loss is at most \(2w/(A\mu\ell)\).  These vanish for
\(w=o(\ell)\) but do not change the fixed factor \(1/\sigma\).

For \(Y=H-I\), the honest stability threshold is

\[
 (C-I)_+^2=\sigma^{-2}(Y-(\sigma-1))_+^2.
\]

The common rational atoms

\[
 \left(-\frac7{10},-\frac15,-\frac1{10},\frac3{10},\frac25\right)
\]

have positive weights \(>1/25\) matching the paper-derived rational closed
moments through degree four at every relevant strict parameter pair.  Their
largest atom is \(2/5\), below the smallest threshold \(43/100\), and
\(1+y\geq3/10\).  Hence the corrected primal tail is zero even before
trimming.  Nonnegativity and the zero polynomial show that both the sharp
degree-four primal and dual values are exactly zero.  A2.2 therefore yields
no quartic increment; its exact recomputed outputs are only the two-trace
baselines listed in docs/audit/r1a_alias_free_fallback.md.

RH/Zeta85/Discharge/AliasFallback.lean proves the generic rational
moment reconstruction, all parameter-specific positivity and support
checks, the scaling identity, and the strict-support zero tails for the
paper-derived closed moment definitions.  It does not prove that those
definitions equal Mathlib integrals or the RS specialization to formula
(18); that analytic bridge remains open.  The independent exact-plus-
numerical verifier is verify/a2_2_alias_free_scaling.py with committed
output verify/a2_2_alias_free_scaling.out.

Exact blocker after A2.2: within the finite one-window interval class,
periods summing to \(L\), unchanged cycle-3 coefficient
count, and normalization by \(aL^2\), no mean-one literal principal block
exists; the honest degree-four replacement has tail optimum zero.  Escaping
this statement requires a new coefficient count/normalization and zero-side
trace proof, a modulation system outside A2.1 and A2.2, or spectral input
beyond four moments.  By itself, this A2.2 result discharges no frozen-rung
premise; the later conditional assembly is recorded in §25.

---

## 21. B-3 terminal certificate layer — finite arithmetic discharged; frozen R-9383 endpoint obstructed

The two terminal scalar cost claims now have explicit constructions.
`RH/Zeta85/Discharge/QuarticWindowWitnesses.lean` defines even rational
polynomials of degrees 18 and 10, proves strict positivity by exact Bernstein
coefficients, evaluates their autocorrelations and saturated costs by Mathlib
integration, and obtains

\[
 D_{14999/10000}<1.13434643,
 \qquad
 D_{19999/10000}<1.06772567.
\]

Exact derivative-quotient Bernstein bounds prove monotonicity on the whole
allocation interval.  Together with the exact edge inequalities, this gives
the pointwise top-hat caps, not a sampled check.  These theorems discharge
the two scalar window-cost subtasks; a future `Inputs95` must not reintroduce
them as fields.  They do not supply the R1a modulation/principal block, which
was killed in both requested construction classes in §§19--20.

`RH/Zeta85/Discharge/TopHatMoments.lean` starts from actual indicator and
interval-integral definitions.  It proves the centered scalar moments through
degree four, all four distance-potential contractions, and

\[
 \int r_p^2h_p^2=\frac{7p}{60},
 \qquad
 \mathcal X_{\mathrm{simplex}}(r_p)=\frac p{30}.
\]

It assembles the exact closed second, third, and fourth moments in terminal
formula (21).  The original three-dimensional crossing functional is a
separate definition.  `crossingReduction` proves its determinant-one
substitution, exact support-intersection length, and four-quadrant reduction;
`formula21M4Integral_eq` therefore proves the original fourth formula with no
bridge proposition.  The R1b theorem that the actual grid/compression moments
converge to formula (18), and the quantitative smooth-top-hat limit, remain
absent.

`RH/Zeta85/Discharge/TrimmedMoment.lean` proves finite trimmed quartic weak
duality and checks both rational terminal quartics globally.  Each of
`P`, `y²-P`, and `L-P` is factored exactly; rational sign and discriminant
checks replace every sampled inequality.  The affine fixed-point arithmetic
gives conditional finite outputs

\[
 0.868552508285414235\ldots>0.86855250,
 \qquad
 0.950638321875659418\ldots>0.95063832187565.
\]

The displayed rational duals are near-optimal rather than exact
complementary-slackness pairs.  The proof correctly uses weak duality; the
independent primal computations are labelled calibration and no equality is
claimed.

The flat R-9383 branch has a different verdict.  Exact rational Taylor and
square-root enclosures in `verify/b3_r9383_exact_endpoint.py` isolate its
unique fixed root and prove

\[
 0.9383133270509488847
 \leq r_{\mathrm{flat}}
 \leq0.9383133270509488848
 <0.938313327050949.
\]

Thus file 19 rounded the endpoint upward by at least
`0.0000000000000001152`.  A second exact rational five-atom law independently
gives a strict upper comparison.  The rational endgame is replayed in
`RH/Zeta85/Discharge/R9383ExactEndpoint.lean`.

This kills the exact flat three-atom endpoint certificate class, not the
frozen target itself.  The later Phase-C transfer does not revive that class:
its conditional R-9383 theorem is instead a monotone consequence of the
strict support-`19999/10000` R-9506 branch.  R-8686 and R-9506 likewise now
have conditional headlines, while their four per-support analytic structures
remain uninstantiated.  Full formulas, exact fractions, and reproduction
commands are in `docs/audit/b3_certificate_layer.md`.

---

## 22. B-4 `eta > 1/2` factorization — conditional algebra proved; relabel-only class killed

For a block already carrying the lengths asserted in file 18, the local
power calculation is correct.  At fixed `1/2 < eta < 1`, choosing

\[
 M_1=T^{1-\eta},\quad M_2=T^\eta,\qquad N_1\asymp1,\quad N_2=T
\]

gives `PQ = PH = T^(1+eta)`.  The preliminary replacement has exponent
`2 eta + (1+eta) epsilon` and is power-small whenever
`epsilon < (1-eta)/(1+eta)`.  `EtaClosure.preliminary_with_log_is_o` proves
this with every fixed logarithmic exponent explicit.

The missing step is the asserted all-block factorization.  A legal
depth-three, `j=2` block has two truncated atoms of exponent `eta/2` and two
smooth atoms of exponent `1/2`.  The only whole-variable group of exponent
`eta` is the pair of truncated atoms.  The remaining whole-factor exponents
are `0`, `1/2`, and `1`, none equal to `1-eta`.  Thus literal relabelling
cannot construct the requested `M1`.  Keeping the balanced block does not
repair the estimate: its `PQ` and `PH` powers exceed trace scale by exactly
`eta` and `eta-1/2`.  The Lean theorems
`balanced_j2_K3_legal`, `balanced_j2_A_group_unique`,
`balanced_j2_no_asymmetric_M1`, and `balanced_signedShift_misses` prove these
statements for the full open interval.

This kills only the exact relabel-only method class.  The surviving route is
a pointwise finite signed convolution identity `(EF_eta)` which constructs
the two asymmetric factors, preserves the logarithmic and coefficient
weights, meets every BBLR support/derivative hypothesis, and recombines all
zero modes with the singular-series subtraction before absolute values.
Under the literal prime-dyadic accounting it must additionally produce an
effective log exponent `C < 1`; `C = 0` closes without a cross-scale estimate,
while `EtaClosure.literal_log_budget_fails` proves every `C >= 1` fails.
No such identity is present or asserted.  The exact method class, witness,
and blocking statement are in `docs/audit/eta_gt_half_factorization.md`.

---

## 23. Phase-C robust stability and finite spectral trim

The exact B-1 theorem used the same integer `N` for ambient dimension, trace
normalization, and zero-count scale.  The analytic assembly only supplies the
latter two asymptotically, and the distinguished principal block has a
different dimension.  This mismatch is now removed rather than hidden in a
limit notation.

`RH.Zeta85.stability_prebound` proves the finite estimate

\[
 \operatorname{Tail}_b(G)
 \leq \lVert G\rVert_F^2-4\operatorname{tr}G+s
      +2\operatorname{traceCap}+4b.
\]

If `tr P <= s + eP`, `|tr G - N0| <= eT`,
`||G||_F^2 <= D*N0 + eF`, and `s+2b <= N0+eC`, then
`RobustStability.robust_stability_inequality_withCountError` gives

\[
 \operatorname{Tail}_b(G)
 \leq s-(2-D)N_0+2e_P+4e_T+e_F+2e_C.
\]

Here the ambient dimension `d` and real scale `N0` are independent.  The
same bound is proved for isometric and principal compressions.  The
coefficients `(2,4,1,2)` and the remaining count slack
`2(s+2b-N0-eC)` are exact, not asymptotic conventions.  The original
zero-count-error APIs remain unchanged.

The finite spectral bridge is also explicit.  The uniform centered
eigenvalue law, after deleting the first `b` decreasing eigenvalues, has
removed mass at most `b/d`; its residual positive-square moment is exactly
`tailExcessSq/d`.  `principal_spectral_headTrimmedMomentInputs_of_moments`
therefore needs only four named equalities between the actual finite spectral
moments and the analytic target moments.  It introduces no spectral-law or
limit field itself.  Those four same-block moment identifications remain the
precise R1b/grid interface for Phase C.

---

## 24. Phase-C `Inputs95` boundary — same matrices, exact profiles, no instance

`RH/Zeta85/Inputs95.lean` now records the honest analytic boundary without
declaring a Lean axiom or constructing an instance.  Each family is indexed
by its exact support, distinguished bandwidth, fill, and B-3 profile.  The
two exact rewrite theorems identify the literal saturated costs with
`QuarticWindowWitnesses.D8686` and `D9506`; there is no free numeric cost
field.

For each height, the displayed windows and modulation columns define the
full all-zero matrix `G`, the finite enlarged-window `ZIprime` sum `A`, and
the tail `E=G-A`.  The distinguished block is definitionally a principal
compression of `A`.  `StableZeroSide` requires the same `A` to decompose as
`P+Q`.  The proved base population identity supplies

\[
 s_1+2(s_2+p)\leq N(T,2T)+N_{II}(T),
\]

so the robust block-tail adapter incurs exactly `2*NII` through the proved
count-error coefficient.  The ambient matrix dimension is never identified
with the dyadic zero count.

`PrincipalCyclicBlock` is the exact R1a construction obligation: literal
smooth compact windows, positive periods, critical grids, pointwise full
energy reconstruction, real alias cancellation, corrected distinguished
energy fraction tending to `mu` (not `mu/sigma`), positive distinguished
energy, a mean-one supported local profile, and integrable locally uniform
translated-product convergence through degree four.  No common-lattice or
one-window construction is asserted; the two requested construction classes
remain killed by §§19--20.

`RS1996ZetaInputs.theorem31` separately records the published smoothed
all-tuples theorem.  `BlockMomentLimits` then states the still-unproved R1b
bridge for the actual block: complex alias summability and exact cancellation
at every pair of actual enlarged-window zeros, followed by convergence of
the first four centered block moments to the proved formula-(21) integrals.
The pair-trace field does not derive the trace limits, and the published RS
field does not derive the block-moment limits.  Those separations prevent a
provenance citation from silently becoming an analytic proof.

The top-level `Inputs95` bundle has eleven fields: two pair fields, two trace
fields, two zero-side fields, one shared RS field, two R1a fields, and two
R1b fields.  This boundary module itself constructs no bundle instance.  The
subsequent transfer in §25 deliberately takes the four exact structures it
uses rather than treating the complete bundle as an instance.

---

## 25. Phase-C quartic transfer — conditional frozen headlines assembled

`RH/Zeta85/Discharge/QuarticTransfer.lean` now connects the proved finite
stability and B-3 certificate layers to the exact asymptotic structure
boundary.  For a block of dimension \(d\), trim budget \(b=s_2+p\), dual cap
\(c\), and certified cost upper bound \(\bar D\), finite weak duality and robust
stability give

\[
 dA_P+(2-\bar D-c/2)N
 \leq (1-c/2)N_0^s
   +2e_P+4e_T+e_F+3N_{II}.
\]

The coefficient three is exact.  Robust count slack contributes
`2*NII`; replacing `s1` by `N0s+NII` contributes
`(1-cap/2)*NII`; and controlling the trim count from
`s1+2b <= N+NII` contributes `(cap/2)*NII`.  The cap-dependent pieces cancel.
The cost inequality is used in the safe direction
`profileSaturatedCost <= costUpper`.

The base Riemann--von Mangoldt and local-count theorems prove
`NII=o(N)` and eventual positivity of `N`.  The block-dimension limit and the
four actual block-moment limits then yield the normalized transfer quotient.
The exact rational certificates give strict margins above R-8686 and R-9506.
R-8657 follows monotonically from R-8686, and R-9383 follows monotonically
from R-9506; the upward-rounded flat R-9383 route remains killed.

`RH/Zeta85/QuarticMain.lean` exposes the final theorem pairs
`rung8657`(`_cumulative`), `rung8686`(`_cumulative`),
`rung9383`(`_cumulative`), and `rung9506`(`_cumulative`).  Each takes exactly
four structures for its support family:

* `FullTraceLimits`;
* `StableZeroSide`;
* `PrincipalCyclicBlock`; and
* `BlockMomentLimits`.

The `PairTraceGrade95` and `RS1996ZetaInputs` structures are upstream routes
for proving trace and moment limits, but are not consumed by the transfer or
headline theorems.  This avoids substituting a provenance citation for the
missing pair-to-matrix or RS-to-grid proof.  No instance of the four premises
is constructed, so all four rungs remain conditional and none reaches the
unconditional base-repository standard.

The independent exact replay is `verify/quartic_transfer.py`; its committed
hashes are

```text
dc99b510fdf1966f11535bf57a3dc53f4056c679e0275c8a649c01facf5f3bdf  verify/quartic_transfer.py
05615d7eb1727532cb81a5c04598630ebd9c29408b729770d34e4b282b533cce  verify/quartic_transfer.out
```

The 21 public transfer theorems and eight final headline theorems all print
exactly `[propext, Classical.choice, Quot.sound]`.  That dependency result
certifies the formal derivation under the displayed premises; it does not
discharge those premises.
