# Routes to a corrected Shiu majorant (`ShiuMajorant₂`)

**Research memo — Shiu campaign, unit U13.**
Date: 2026-08-18.  Baseline: `main` at 49c9708 ("Consolidate the agent campaign: one validated
line, 10 axioms down to 1").  Branch: `shiu/u13-research-memo`.

*Evidence discipline.*  Every claim about this repository is cited as `file:line` and was
re-checked against the tree at the baseline commit (sibling-branch claims name the branch and
commit).  External references are cited per the campaign specification, whose citation list was
pre-verified; entries are marked "(per campaign spec)" and no web-sourced text is quoted.

**Contents**

1. [The problem](#1-the-problem)
2. [Defect analysis: D1, D2, D3](#2-defect-analysis-d1-d2-d3)
3. [The corrected interface](#3-the-corrected-interface)
4. [Literature review](#4-literature-review)
5. [The three routes, ranked](#5-the-three-routes-ranked)
6. [What a proved `ShiuMajorant₂` does NOT give](#6-what-a-proved-shiumajorant₂-does-not-give)
7. [Staged roadmap](#7-staged-roadmap)

---

## 1. The problem

### 1.1 The frozen interface

`RH/` declares exactly one axiom (`AXIOMS.md`, preamble and §2; re-verified: the only `axiom` keyword in
compiled `RH/` code is `RH/Zeta85/Hypotheses.lean:158`; the two hits under
`Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean:183-184` sit inside a docstring example, not
compiled code).  The axiom is stated over three definitions of `RH/Zeta85/Arith.lean`:

`RH/Zeta85/Arith.lean:56-57`:

```lean
def DivisorBounded (c : ℕ → ℝ) (K : ℝ) (k : ℕ) : Prop :=
  ∀ n : ℕ, |c n| ≤ K * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
```

`RH/Zeta85/Arith.lean:202-203`:

```lean
def progressionSum (c : ℕ → ℝ) (P : ℝ) (q r : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q), |c p|
```

and, with its docstring (`RH/Zeta85/Arith.lean:205-211`):

```lean
/-- The Shiu-type majorant of `docs/run/12` (14):
`Σ_{p ≍ P, p ≡ r (q), (r,q)=1} |c_p| ≪ (P/φ(q))·(log T)^C`, uniformly for `q ≤ P·T^{−η+o(1)}`. -/
def ShiuMajorant (η : ℝ) : Prop :=
  ∀ (c : ℕ → ℝ) (Kc : ℝ) (k : ℕ), DivisorBounded c Kc k →
    ∃ C K T₁ : ℝ, ∀ T ≥ T₁, ∀ P : ℝ, 1 ≤ P → ∀ q r : ℕ, 0 < q → Nat.Coprime r q →
      (q : ℝ) ≤ P * T ^ (-η) →
      progressionSum c P q r ≤ K * (P / (Nat.totient q : ℝ)) * (Real.log T) ^ C
```

The axiom (`RH/Zeta85/Hypotheses.lean:158`):

```lean
axiom shiu_majorant : ∀ η : ℝ, 0 < η → η < 1 / 2 → ShiuMajorant η
```

It renders equation (14) of `docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` (the
progression majorant for the recombined Heath–Brown coefficients, displayed at
`docs/run/12:156-159` with its range `q ≤ P·T^{−η+o(1)}` at line 161); the underlying published
result is P. Shiu's Brun–Titchmarsh theorem for multiplicative functions (see §4), as recorded in
the axiom's docstring (`RH/Zeta85/Hypotheses.lean:144-146`) and in `FINDINGS.md` §5.

### 1.2 Its role: the application site

The 85 % headline is assembled in `RH/Zeta85/Main.lean`:

* `cert143` (`RH/Zeta85/Main.lean:132-136`) passes `shiu_majorant` by name into
  `signedPair_traceGrade_lt_3_2` (`RH/Zeta85/Hypotheses.lean:247-252`, whose second explicit
  premise is `∀ η, 0 < η → η < 1/2 → ShiuMajorant η`), then feeds the resulting trace-grade
  criterion at `lam = 143/100` (`RH/Zeta85/Window.lean:40`) into `traceTransfer_saturated`
  together with the proved `windowCost_143`;
* `rung143` (`Main.lean:141-142`) and `rung143_cumulative` (`Main.lean:145`) convert the
  certificate to the counting statement;
* `eightyFive` / `eightyFive_cumulative` (`Main.lean:150,153-154`) are the 85 % corollaries.

Per `AXIOMS.md` §2, every assembled rung — R-679 through R-9506 — now lists `shiu_majorant` as its
single custom axiom.

### 1.3 The refutation: the interface is false

`RH/Zeta85/Discharge/ShiuNoGo.lean` proves, with no axioms:

```lean
theorem not_shiuMajorant_quarter : ¬ ShiuMajorant (1 / 4 : ℝ)     -- ShiuNoGo.lean:28
```

The construction (line references into `RH/Zeta85/Discharge/ShiuNoGo.lean`):

1. **Coefficient.**  Take `c = τ` (the divisor function, `σ₀`), which is `DivisorBounded c 1 1`
   (:30-33).  Extract the interface's constants `C, K, T₁` for this one sequence (:34).
2. **Freeze the scale that carries the logarithms.**  Set `T := max T₁ 1 + 1` (:36) — a single
   admissible `T`, fixed once and for all.  The whole right-hand side is now bounded by the fixed
   budget `B := K·(2T)·(log T)^C` (:45) *whenever* `P/φ(q)` can be pinned to `2T` (step 5).
3. **Spike.**  Choose `m ∈ ℕ` with `m > max B 1` (:46-49) and set `n := 3^m` (:51), so
   `|c n| = τ(3^m) = m + 1` (:106-110) exceeds the budget by construction.
4. **Modulus isolating the spike.**  Let `e := Nat.clog 2 n`, `q := 2^e` (:55-63): the least power
   of two with `n ≤ q`; `3^m` and `2^e` are coprime (:64-66).  Then `φ(q) = q/2` (:112-127) — the
   progression's *normalized* length `P/φ(q)` will be independent of `m`.
5. **Scale.**  Put `P := q·T` (:68).  The frozen range condition holds:
   `q ≤ P·T^{−1/4} = q·T^{3/4}` since `T ≥ 1` (:73-84).  And
   `K·(P/φ(q))·(log T)^C = K·(2T)·(log T)^C = B` exactly (:129-136).
6. **Contradiction.**  `n = 3^m ≤ q ≤ P` lies in `[1, ⌈2P⌉]` and in its own residue class, so the
   single term already gives `progressionSum c P q n ≥ m + 1` (:88-104).  The interface forces
   `m + 1 ≤ B < m + 1` (:138-141).

The mechanism, in one sentence: the interface lets the adversary grow the summation scale `P`
*after* `T` — hence after the constants and after every logarithm on the right-hand side — is
frozen, while a modulus `2^e` tracking `3^m` keeps the class length `P/φ(q) = 2T` constant, so a
single τ-spike `τ(3^m) = m+1 → ∞` beats any fixed `(log T)^C`.

Consequences in the tree: `shiu_interface_contradiction : False`
(`RH/Zeta85/Hypotheses.lean:161-163`), after which the remaining conditional layers are discharged
by `False.elim` — `signedPair_traceGrade_lt_5_4` (:197-199), `signedPair_traceGrade_lt_3_2`
(:247-252), `windowCost_125` (:274-276), `traceTransfer_saturated` (:319-322) — and the closed
quartic headlines are produced the same way (`RH/Zeta85/Main.lean:162-186`).  **Every headline
result of the layer is therefore vacuously true**: the artifact currently proves the rungs the way
one proves anything from a false axiom.  `AXIOMS.md` §2 records this ("the signed-pair and
trace-transfer declarations are therefore Lean theorems obtained from
`shiu_interface_contradiction`"); the campaign exists to end this regime.

---

## 2. Defect analysis: D1, D2, D3

The refutation is not an artifact of a clever adversary; the frozen statement mis-transcribes the
mathematics in three separable ways.  All three are visible as literal text in
`RH/Zeta85/Arith.lean:207-211`.

### D1 — the logarithm is taken at the wrong scale: `(Real.log T) ^ C`

*Textual evidence:* `... * (Real.log T) ^ C` (`Arith.lean:211`).

Shiu-type bounds control a divisor sum over an interval of scale `P` by `(log P)^C` — the
logarithm of the summation scale, the only scale in the arithmetic statement.  `T` is foreign to
the progression sum: it enters only through the run's *application* (where `P` happens to be a
power of `T`).  Writing `(log T)^C` makes the majorant's logarithmic cost constant in `P`, while
the true class average of `τ^k` over `[1, 2P]` grows like a power of `log P`.  The spike of §1.3
exploits exactly this: at fixed `T`, the left side grows with `P` and the right side does not.

### D2 — the modulus range is coupled to the foreign parameter: `q ≤ P·T^(−η)`

*Textual evidence:* `(q : ℝ) ≤ P * T ^ (-η)` (`Arith.lean:210`).

The honest range for a Shiu-type statement is `q ≤ P^{1−η}`: a *fixed power saving in `P`*, the
scale of the sum.  The run's own instances always sit in the regime `P ≤ T`, where the corrected
range is the faithful — and never weaker — transcription:

* In the run's block geometry (`docs/run/12:92-104`, equations (8)–(9)), at gcd parameter `d = 1`
  the progression length is `P ≍ A·M₁ = T^{η+1/2}` and the modulus is `q ≍ B·N₁ = T^{1/2}`.
  Since `η < 1/2`, `P ≤ T`; hence `T^{−η} ≤ P^{−η}` and every pair the run generates under
  `q ≤ P·T^{−η}` satisfies `q ≤ P^{1−η}` *with the same η*.
* The exact transcription at the run's scales: with `T = P^{1/(η+1/2)}`, the range
  `q ≤ P·T^{−η}` is `q ≤ P^{1−η′}` for `η′ = η/(η + 1/2)`.  At the run's endpoint `η = 43/100`
  (`docs/run/12:13-29`; the same exponent frozen at
  `RH/Zeta85/Discharge/ActualScaleBBLR.lean:38`), `η′ = 43/93 ≈ 0.462 ∈ (0, 1/2)`, i.e. the run
  needs moduli up to `q ≈ P^{50/93} ≈ P^{0.538}` — beyond `√P` (see §5.0), but comfortably inside
  the corrected family `∀ η ∈ (0, 1/2), q ≤ P^{1−η}`.

So the corrected range both covers everything the run uses and decouples the statement from `T`.

### D3 — quantifier order: the constants (and `T`) are frozen before the scale `P`

*Textual evidence:* `∃ C K T₁ : ℝ, ∀ T ≥ T₁, ∀ P : ℝ, 1 ≤ P → ...` (`Arith.lean:209`).

Nothing ties `P` to `T`: after `T` is chosen, `P` may exceed any function of `T`, and with it the
left side's genuine logarithmic growth — while D1 has pinned the right side's logarithms to `T`.
This is the degree of freedom §1.3's spike drives to infinity.  Note the interface is even
per-sequence generous — the constants may depend on the individual `c`, not merely on its
divisor-bounded class (`∀ c ... → ∃ C K T₁`, `Arith.lean:208-209`) — and the refutation still goes
through with the single fixed sequence `c = τ`.  The cure is not more per-`c` freedom but the
correct dependence order: constants first (per class), then the scale, then everything measured at
that scale.

Any one of D1–D3 alone might be survivable; their conjunction is what `not_shiuMajorant_quarter`
refutes.  The corrected interface repairs all three at once.

---

## 3. The corrected interface

Unit U1 lands the following in `RH/Zeta85/ShiuInterface.lean` (not yet present on `main` at the
baseline; verified by grep — no `ShiuMajorant₂` anywhere in-tree):

```lean
def ShiuMajorant₂ (η : ℝ) : Prop :=
  ∀ (Kc : ℝ) (k : ℕ), ∃ C K P₁ : ℝ, ∀ P ≥ P₁, ∀ c : ℕ → ℝ, DivisorBounded c Kc k →
    ∀ q r : ℕ, 0 < q → Nat.Coprime r q → (q : ℝ) ≤ P ^ (1 - η) →
      progressionSum c P q r ≤ K * (P / (Nat.totient q : ℝ)) * (Real.log P) ^ C
```

Design decisions, one per defect and two more:

1. **`(Real.log P) ^ C`** — D1 repaired.  `P` is the only scale in the statement; `T` is gone.
2. **`(q : ℝ) ≤ P ^ (1 - η)`** — D2 repaired.  Fixed power saving in `P`; by §2/D2 this covers
   every instance the run generates (worst case `η = 43/93 ≈ 0.462`, still `< 1/2`).
3. **Quantifier order** — D3 repaired.  Constants `C, K, P₁` depend only on `(η, Kc, k)`; the
   scale `P` comes next; the coefficient sequence `c` comes *after* `P`.  This is deliberate:
   the run's coefficient families are `T`-dependent (they are rebuilt at every `T`;
   `docs/run/12:85-88` notes they carry fixed-divisor majorants), so the statement must be uniform
   over the whole `(Kc, k)`-class rather than per-sequence.
4. **Class uniformity is free.**  `progressionSum` is monotone in `|c|` term by term, and
   `DivisorBounded c Kc k` says exactly `|c n| ≤ Kc·τ(n)^k` pointwise.  Hence the `∀ c` statement
   is *equivalent* to its single worst instance `c = Kc·τ^k`:

   `progressionSum c P q r ≤ Kc · Σ_{p ≤ ⌈2P⌉, p ≡ r (q)} τ(p)^k`.

   (The reduction is already formalized on the U3 branch:
   `progressionSum_mono` and the keystone `progressionSum_le_of_divisorBounded`,
   `RH/Zeta85/Shiu/ProgressionCount.lean:209,243` at commit 5df7bcb.)  The class statement is
   therefore exactly Shiu's Theorem 2 for `f = τ^k` at `y = x` (full interval `[1, 2P]`,
   modulus range `q ≤ y^{1−α}` — see §4.1): no strengthening has been smuggled in.
5. **`C` stays existential.**  Different routes deliver different logarithmic exponents for the
   same statement — `C = 2^k − 1` (sharp, Route 1/Route 3) versus `C ≈ 2^{7k}` (Route 2's
   small-divisor detour, §5.2) — and fixing `C` in the interface would marry it to one route.
   The repository's discipline is that `C` is never absorbed and always audited
   (`RH/Zeta85/Arith.lean:59-61`; `RH/Zeta85/Discharge/LogBudget.lean`), so each proof exhibits
   its own `C` and the LogBudget layer consumes the exhibited value (§6.2).

---

## 4. Literature review

All external citations in this section are per the campaign specification (pre-verified there);
in-tree citation trails are given where the tree already cites the work.

### 4.1 The target theorem

**P. Shiu, "A Brun–Titchmarsh theorem for multiplicative functions", J. reine angew. Math. 313
(1980), 161–170** (per campaign spec; cited in-tree at `RH/Zeta85/Hypotheses.lean:144-146`,
`FINDINGS.md` §5, `AXIOMS.md` §3).  Theorem 2 is the progressions form (per campaign spec): for
`f` nonnegative multiplicative with `f(p^ℓ) ≤ A₁^ℓ` and `f(n) ≤ A₂(ε)·n^ε`, uniformly in
`(a, q) = 1`, `q ≤ y^{1−α}` and `x^ε ≤ y ≤ x` (any fixed `α, ε`),

`Σ_{x−y<n≤x, n≡a (q)} f(n)  ≪  (y/φ(q)) · (1/log x) · exp( Σ_{p≤x, p∤q} f(p)/p )`.

At `f = τ^k` the exponential factor is `≍ (log x)^{2^k}` (since `f(p) = 2^k`), so the bound reads
`(y/φ(q)) · (log x)^{2^k−1}` — the sharp exponent, with the characteristic extra `1/log x`
saving.  Three features matter for us: the modulus range is a *fixed power of the interval
length* (the corrected D2 shape); the logarithms are in `x` (the corrected D1 shape); the
constants depend only on the class data (the corrected D3 shape).  At `y = x` this is precisely
`ShiuMajorant₂` for the worst class member (§3.4).  `FINDINGS.md` §5 records why the original
formalization attempt did not close: the theorem is not in Mathlib, and the run's signed `c_p`
must first be replaced by the class majorant — which is exactly what the corrected interface's
`DivisorBounded` hypothesis and the §3.4 reduction now do.

### 4.2 Small-divisor (Landreau-type) inequalities — Route 2's pointwise engine

**B. Landreau, "Majorations de fonctions arithmétiques en moyenne sur des ensembles de faible
densité", Bull. Soc. Math. France 117 (1989)** (per campaign spec): the τ-power small-divisor
lemma — divisor powers are controlled on average by divisor powers at *small* divisors, schema
`τ(n)^k ≤ A(k,ℓ) · Σ_{d ∣ n, d^ℓ ≤ n} τ(d)^{B(k,ℓ)}`, at any fixed depth `ℓ`.  The point: the
interchange of the `d`-sum and the progression sum then meets only divisors `d ≤ (2P)^{1/ℓ}`, so
the rounding errors total `≈ P^{1/ℓ}` instead of `≈ √P` (§5.0, §5.2).

**J. P. S. Lay, arXiv:1711.05924** (per campaign spec): the explicit depth-four case —

`τ(n) ≤ 8 · Σ_{d ∣ n, d ≤ n^{1/4}} τ(d)^7`,

in the strong single-divisor form: for every `n ≥ 1` there *exists* `d ∣ n`, `d ≤ n^{1/4}`, with
`τ(n) ≤ 8·τ(d)^7`.  The existential form makes powering free — `τ(n)^k ≤ 8^k·τ(d)^{7k}` for the
same `d` — so one explicit lemma serves every class exponent `k`.  The proof is an elementary
finite case analysis (on the prime-factorization shape of `n`), which is precisely the kind of
argument that formalizes well; this is unit U8's target.

### 4.3 Explicit Shiu-type machinery — Route 3's backbone

**O. Bordellès, arXiv:2402.12333** (per campaign spec): fully explicit Shiu-type bounds for short
sums of nonnegative arithmetic functions under a divisor-type growth condition — every constant
displayed, no asymptotic `≪`.  Its role here is methodological: it demonstrates that the
Erdős–Wolke–Shiu machine (rough-number counts by a truncated sieve, smooth-part summation, a
Rankin-type tail) can be run with explicit constants end to end.  Unit U10 adopts this
discipline for the Brun core (§5.3); a Lean proof needs either elementary structure (Routes 1–2)
or explicit constants (Route 3), and Bordellès shows the latter is available at full strength.

### 4.4 Context: the uniform frameworks and recent activity

**K. Henriot, arXiv:1102.1643** (per campaign spec): the Nair–Tenenbaum framework made uniform in
the polynomial discriminant — the modern general-purpose form of Shiu-type bounds over polynomial
values.  **T. Wright, arXiv:2508.17217** (per campaign spec): recent explicit
Brun–Titchmarsh-flavor extensions of Shiu's theorem to larger function classes — evidence the
classical statement is still the reference point and the area is active.  Neither is on the
critical path (see §4.6).

### 4.5 The summatory ladder

**F. Luca, L. Tóth, arXiv:1703.08785** (per campaign spec): an elementary treatment of divisor-sum
moments.  Its role for the campaign is as the model for unit U6: the elementary ladder
`Σ_{n≤x} τ_K(n) ≪ x·(log x)^{K−1}` (by induction on `K` through the hyperbola-free bound
`Σ_{n≤x} τ_K(n) ≤ Σ_{d≤x} τ_{K−1}(d)·⌊x/d⌋`), together with its harmonic form
`Σ_{n≤x} τ_K(n)/n ≪ (log x)^K`.  These exponents — `2^k − 1` for `τ^k = τ_{2^k}`'s mean — are the
sharp constants that Routes 1 and 3 inherit and that §6.2's budget arithmetic consumes.

### 4.6 Assessed and rejected: Nair 1992 / Nair–Tenenbaum

The Nair (1992) and Nair–Tenenbaum generalizations (per campaign spec; the framework made
discriminant-uniform by Henriot, §4.4) prove Shiu-type bounds for `f(|Q(n)|)` over polynomial
values, in several variables, and with multiplicativity relaxed.  For this formalization they are
**rejected**, for cause:

* **Generality we cannot spend.**  Our instance is `f = τ^k` at the identity polynomial over a
  full interval — every axis of the Nair–Tenenbaum generalization (polynomial arguments,
  several variables, non-multiplicative `f`, discriminant uniformity) is vacuous at the target.
* **Strictly more machinery than Shiu for our range.**  The framework's proofs contain the whole
  Erdős–Wolke–Shiu apparatus *plus* the polynomial-value bookkeeping; in Lean, cost is counted in
  lemmas built, not in generality obtained.  Shiu's original argument — or its explicit
  Bordellès-style rendering — is the minimal machine whose output type matches `ShiuMajorant₂`.
* **No explicit-constant tradition.**  The framework's statements are `≪`-asymptotic with
  inexplicit class dependence; making them explicit would be a research project of its own,
  duplicating what §4.3 already offers for the statement we need.

---

## 5. The three routes, ranked

### 5.0 The difficulty scale, and the elementary `√P` wall

The class `{p ≤ ⌈2P⌉ : p ≡ r (q)}` has `≈ 2P/q + O(1)` elements.  The run's own justification for
(14) — "the interval contains `P/q ≫ T^{η−o(1)}` representatives" (`docs/run/12:161-165`) — is
*counting*, and counting alone cannot prove any `ShiuMajorant₂`: the pointwise divisor bound is
not polylogarithmic (`τ(n)` reaches `exp(c·log P/ log log P)` on `[1, 2P]`), so a mean-value
mechanism over the class is mandatory.  The elementary mechanism is the divisor-sum interchange:
bound `τ(n)^k` by divisor sums, swap, and count multiples in the progression,

`#{n ≤ 2P : d ∣ n, n ≡ r (q)} ≤ 2P/(dq) + 1`  (empty unless `(d, q) = 1`),

so each divisor `d` below the cutoff costs a rounding error `+1`.  With the trivial cutoff — every
divisor pair of `n` has a member `≤ √n` — the errors total `≈ √(2P)`, against a main term
`≈ (P/q)·log P`.  **Classes with `q` near `√P` retain only `≈ √P` elements, and the accumulated
divisor-count fluctuations (`≈ √P`) swamp what trivial counting can certify** — the elementary
argument saturates at `q ≈ P^{1/2−o(1)}`.  The run needs `q ≈ P^{0.538}` (§2/D2): every viable
route must push the interchange cutoff *below* `√n`, and pay for the depth somewhere.  Routes 1–3
are the three known ways to pay.

### 5.1 Route 1 — max-coordinate split (unit U7, `shiu/u07-max-coordinate`)

**Pointwise.**  `τ(n)^k = τ₂(n)^k ≤ τ_{2^k}(n)` by iterating `τ_a(n)·τ_b(n) ≤ τ_{ab}(n)`
(unit U5; the convolution-direction companion `τ(ms) ≤ τ(m)·τ(s)` is already in the tree as
`EtaDivisorRefinement.sigma_zero_mul_le`, U2 branch at 8650d5e, line 325).  Write `K := 2^k`.

**Split.**  Every `K`-factorization `d₁⋯d_K = n` has a coordinate `≥ n^{1/K}`.  A union bound
over which coordinate is maximal gives
`τ_K(n) ≤ K · Σ_{b·a = n, a ≥ n^{1/K}} τ_{K−1}(b)`, so the cofactor `b` obeys `b ≤ n^{1−1/K}`.

**Interchange and ladder.**  Summing over the class and counting multiples (unit U3, landed:
`RH/Zeta85/Shiu/ProgressionCount.lean` at 5df7bcb):

`Σ_{n≤2P, n≡r(q)} τ_K(n) ≤ K·(2P/q)·Σ_{b≤(2P)^{1−1/K}} τ_{K−1}(b)/b + K·Σ_{b≤(2P)^{1−1/K}} τ_{K−1}(b)`
`≤ C_K (P/q)(log P)^{K−1} + C_K P^{1−1/K}(log P)^{K−2}`,

by the τ-summatory ladder (unit U6, §4.5).  In interval form this is the campaign's headline

`Σ_{x<n≤x+y} τ(n)^4 ≤ C·y·(log x)^15   for  y ≥ x^{15/16}`

(`K = 16`, `K − 1 = 15`): **sharp logarithmic exponent** `2^k − 1`, matching the true mean.

**Verdict.**  The error term `P^{1−1/K}` confines the progression form to `q ≤ P^{1/K}` (times
logs) and the interval form to `y ≥ x^{1−1/K}` — at `k = 4`, `q ≤ P^{1/16}` and `y ≥ x^{15/16}`:
*only near θ = 1*, far short of the wall.  Its value is threefold: it is the cheapest complete
proof of a nontrivial `ShiuMajorant₂`-shaped statement; it forces U5+U6 into existence (every
route needs them); and it sets the sharp-`C` benchmark that §6.2's audit consumes.

### 5.2 Route 2 — Landreau/Lay small divisors (units U8 `shiu/u08-landreau` + U9 `shiu/u09-all-theta`)

**Pointwise (Lay, §4.2).**  For each `n` there exists `d ∣ n`, `d^4 ≤ n`, with `τ(n) ≤ 8·τ(d)^7`;
powering, `τ(n)^k ≤ 8^k·τ(d)^{7k} ≤ 8^k · Σ_{d∣n, d⁴≤n} τ(d)^{7k}` — the campaign schema
`τ(n)^4 ≤ A·Σ_{d∣n, d⁴≤n} τ(d)^B` with `A = 8^4`, `B = 28`.

**Interchange.**  The cutoff is now `d ≤ (2P)^{1/4}`:

`Σ_{n≤2P, n≡r(q)} τ(n)^k ≤ 8^k Σ_{d≤(2P)^{1/4}, (d,q)=1} τ(d)^{7k}·(2P/(dq) + 1)`
`≤ C (P/q)(log P)^{2^{7k}} + C·P^{1/4}(log P)^{2^{7k}−1}`

(U6 ladder at exponent `B = 7k`).  The rounding budget has shrunk from `√P` to `P^{1/4}`.

**Range.**  Error below main for every `q ≤ P^{3/4−ε}` — i.e. `ShiuMajorant₂ η` for **every
`η > 1/4`**, and in interval form every `y ≥ x^{1/4+ε}`: all `θ ∈ (1/2, 1)`, indeed all
`θ > 1/4`.  In particular the run's worst case `η′ = 43/93 ≈ 0.462` (modulus `≈ P^{0.538}`,
§2/D2) is covered with room to spare.  Deeper Landreau depths `ℓ > 4` (§4.2) extend the same
skeleton toward every `η > 1/ℓ`, at doubly growing `B(k, ℓ)`.

**Cost.**  The logarithmic exponent is `E ≈ 2^{7k}` — astronomically non-sharp, but a *fixed
constant*, which is all the corrected interface requires (§3.5) and all the LogBudget audit needs
to see exhibited (§6.2 shows even the sharp exponent fails the window budget, so nothing
downstream is lost to the non-sharpness).

**Verdict.**  The pragmatic winner for breadth: it crosses the `√P` wall by elementary means,
covers the run's entire modulus range, and every ingredient is Lean-friendly — Lay's lemma is a
finite case analysis, the interchange is Finset algebra over U3's counting, and the ladder is U6.

### 5.3 Route 3 — Bordellès-explicit Shiu with a Brun pure-sieve core (seed: unit U10, `shiu/u10-brun-core`)

**Goal.**  The genuine Shiu strength: `(P/φ(q))·(log P)^{2^k−1}` — sharp exponent *and* the
`1/log` saving structure — uniformly for `q ≤ P^{1−η}` at **every** `η ∈ (0, 1/2)`.  This is the
only route that reaches the run's `q ≈ P^{0.54}` at full strength, and the only one whose range
covers the `η ≤ 1/4` half of the corrected interface (moduli between `P^{3/4}` and `P`), where
Route 2's fixed divisor depth gives out.

**Mechanism** (three stages, mirroring the explicit discipline of §4.3):

1. *Brun pure-sieve rough counts.*  Bonferroni-truncated Möbius over the primes `≤ z` dividing
   neither `q` nor the sieved variable: an even-order truncation is an upper bound, with an
   explicit error counting only the truncated square-free sieve terms.  Output: for the `z`-rough
   integers (no prime factor `≤ z`) of a progression class of `[1, X]`,
   `count ≤ (X/q)·Π_{p≤z, p∤q}(1 − 1/p)·(1 + explicit) + explicit error`.
2. *Mertens-free product bound.*  `Π_{p≤z}(1 − 1/p) ≤ 1/log z`, elementarily: the reciprocal
   product expands into `Σ 1/n` over `z`-smooth `n`, which contains `Σ_{n≤z} 1/n ≥ log z`.  No
   Mertens theorem, no analytic input — this single inequality is the `1/log` saving, and it is
   provable in Lean from `Finset` manipulations and the harmonic lower bound.
3. *Smooth/rough decomposition.*  Each `n` factors uniquely as `n = s·m` with `s` its `z`-smooth
   part and `m` its `z`-rough part.  Then `τ(n)^k = τ(s)^k·τ(m)^k`, and on the rough part
   `τ(m) ≤ 2^{Ω(m)} ≤ 2^{log(2P)/log z}` — a fixed constant once `z = P^δ`.  Summing over the
   class: fix `s` (coprime to `q`), count rough cofactors by stages 1–2, and sum
   `Σ_s τ(s)^k/s = Π_{p≤z}(1 + 2^k/p + ⋯) ≍ (log z)^{2^k}` over the smooth parts, with a
   Rankin-type tail bound for large `s`.  Net: `(P/q)·(log z)^{2^k}·(1/log z) ≍
   (P/q)·(log P)^{2^k−1}` at `z = P^δ` — the sharp form, at any modulus `q ≤ P^{1−η}` with
   `δ ≍ η/k` chosen so the sieve errors stay below `(P/q)·P^{−ε}`.

**Why the smooth/rough mechanism is genuinely required beyond the wall (at full strength).**  In
Routes 1–2 the error term is a count of *all* integers below the divisor cutoff — `Σ_{d≤D} τ^B(d)`
— so depth is bought only by shrinking `D`, and each shrink is paid in logarithmic exponent
(`K − 1` at depth `1 − 1/K`; `2^{7k}` at depth `1/4`); the range ceiling is hard-wired to the
cutoff.  The sieve mechanism is different in kind: it replaces "all `d` below the cutoff" by
"rough `m` only", a set of density `≈ 1/log z`, which simultaneously (i) turns the rounding budget
into a *saving* on the main term and (ii) unties the modulus range from any fixed divisor depth —
the only constraint is the sieve error level, tunable by `z = P^δ`.  Both the sharp exponent and
the full `η → 0⁺` range come from this replacement, and from nothing available to Routes 1–2.

**In-tree seed.**  The ported `EtaDivisorRefinement` (U2 branch, commit 8650d5e; §7) already
carries the grammar of stage 3: the canonical largest-divisor-below-a-cutoff selection and its
regular-or-rough alternative (`canonicalDivisor`, `canonical_regular_or_rough`, lines 41, 108),
rough-cofactor `Ω`-bounds (`rough_pow_cardFactors_le`, `cardFactors_lt_of_rough_of_lt_pow`, lines
258, 269), `τ(s) ≤ 2^{Ω(s)}` (`card_divisors_le_two_pow_cardFactors`, line 353), and a proved
zero-logarithm progression majorant for its rough-core family
(`roughCoreAF_family_zero_log_majorant`, line 1278), alongside the progression-cardinality bound
`progression_filter_card_le_five` (line 1143: the class of `[1, ⌈2P⌉]` has at most `5·P/φ(q)`
elements for `q ≤ P`).

**Verdict.**  The longest route — Brun bookkeeping, Rankin tails, and progression-compatible
smooth summation — but the only endgame at full strength.  Start it last, from U10's core.

**Ranking.**  For the run's actual range need: Route 2.  For the sharp exponent and shared
infrastructure at least cost: Route 1.  For the full interface `∀ η ∈ (0, 1/2)` at full
strength: Route 3, and only Route 3.  Formalization order: U7 → U8/U9 → U10⁺, because Route 1's
infrastructure (U3, U5, U6) is consumed by both later routes.

---

## 6. What a proved `ShiuMajorant₂` does NOT give

Two obstructions are already **proved** in the tree — both axiom-free — and both survive any
proof of the corrected majorant.  They bound what this campaign can honestly claim.

### 6.1 The power-scale obstruction: `ActualScaleBBLR.progression_majorant_not_traceGrade`

`RH/Zeta85/Discharge/ActualScaleBBLR.lean:197-203`:

```lean
theorem progression_majorant_not_traceGrade :
    progressionMajorantExponent = 83 / 50 ∧
      progressionMajorantExponent - traceExponent = 23 / 100 ∧
      traceExponent < progressionMajorantExponent
```

At the run's symmetric actual-scale block (`η = 43/100`, :38; at `d = 1` the progression lengths
are `P = Q = T^{83/100}`, :151-154, :168-174), the majorant-based per-block estimate `P(Q + H)`
has exponent `max(83/50, 63/50) = 83/50 = 1.66`, exceeding the trace exponent `1 + η = 143/100`
by exactly `23/100` (:184-187) — **already with the logarithmic exponent set to zero**.  A true
Shiu majorant, inserted exactly where the run inserts equation (14), leaves rung 3's remainder a
full power `T^{23/100}` above trace on the literal block.  The module is careful about its scope
(:25-27): it does not assert a lower bound for the original *signed* remainder, so cancellation
before the majorant is applied remains possible — but that cancellation is then the load-bearing
mathematics, and it is not a majorant statement at all.

### 6.2 The logarithmic-budget obstruction: `LogBudget.verdict_all`

`RH/Zeta85/Discharge/LogBudget.lean:275-280`:

```lean
theorem verdict_all {C : ℝ} (hC : 3 ≤ C) :
    (∀ᶠ T : ℝ in atTop, 1 ≤ contribution C T / budget T) ∧
    (∀ᶠ T : ℝ in atTop, 1 ≤ contributionPrimeDyadic C T / budget T) ∧
    (∀ᶠ T : ℝ in atTop, 1 ≤ contributionDyadic C T / budget T)
```

The trace budget is `T·(log T)³` (:109); an aggregate remainder `X·(log T)^C` enters the second
moment at `T·(log T)^{C+1}` at minimum (:114), and the three accounting models close **iff
`C < 2` / `C < 1` / `C < 0`** respectively (`budget_closes`/`budget_fails` :162-178, and
:181-215).  At `η = 43/100` the Heath–Brown depth is forced to `K ≥ 4` (`depth_at_85` :219),
giving an effective coefficient exponent `C ≥ K − 1 ≥ 3`; `verdict_all` then closes all three
doors.  The same arithmetic bites on the majorant side directly: a `τ^k`-class majorant carries
the mean value of `τ^k`, whose logarithmic exponent is `2^k − 1` even when proved *sharply*
(§4.1, §4.5) — so at the depth-forced powers `u ≥ 2` of the run's coefficients, Shiu's method
inherently yields `C = 2^u − 1 ≥ 3`, while the most generous window budget demands `C < 2`.  No
route of §5 changes this: Routes 1 and 3 exhibit `C = 2^k − 1 ≥ 3`, Route 2 exhibits more.

### 6.3 The honest claim

A proved `ShiuMajorant₂` therefore delivers exactly this: it ends the ex-falso regime of §1.3
(the layer stops proving its headlines from a false axiom), it replaces the one axiom's vocabulary
with a statement that is *true* and carried by published mathematics, and it discharges the
arithmetic ingredient that `docs/run/12` (14) actually claimed.  It does **not** un-condition
rung 3: by §6.1 the majorant-based block estimate misses trace grade by `T^{23/100}` at the 85 %
endpoint, and by §6.2 its logarithmic cost exceeds the window budget by at least one power of
`log T` in the most generous accounting.  `signedPair_traceGrade_lt_3_2` remains the load-bearing
gap after this campaign succeeds, and the 85 % target is not thereby weakened (R2 discipline:
`RH/Zeta85/Discharge/LogBudget.lean:84-88`, `FINDINGS.md` §7).

---

## 7. Staged roadmap

### 7.1 The thirteen campaign units

Status is as verified in-tree on 2026-08-18 (branch tips at the named commits); units without a
note were at the baseline commit when this memo was written.

| unit | branch | target |
|---|---|---|
| U1 | `shiu/u01-honest-core` | land `RH/Zeta85/ShiuInterface.lean` (`ShiuMajorant₂`, §3) and rewire the axiom layer off the refuted interface, ending the ex-falso regime of §1.3 |
| U2 | `shiu/u02-eta-divisor-port` | port `RH/Zeta85/Discharge/EtaDivisorRefinement.lean` — **landed** (8650d5e, 1,514 lines, unimported; headline results incl. `roughCoreAF_family_zero_log_majorant`, `progression_filter_card_le_five`; §5.3's in-tree seed) |
| U3 | `shiu/u03-progression-count` | progression counting core `RH/Zeta85/Shiu/ProgressionCount.lean` — **landed** (5df7bcb; `progCount_*` at `N/q ± O(1)` and `≤ 4P/φ(q)`, `progressionSum` API, class-reduction keystone `progressionSum_le_of_divisorBounded`; review-fixed at 61d9d3b) |
| U4 | `shiu/u04-bounded-coefficients` | `k = 0` inhabitation `RH/Zeta85/Shiu/BoundedCoefficients.lean` — **landed** (6115c76; `boundedCoeff_progression_majorant`: explicit constants, zero logarithmic loss, full range `q ≤ P`) |
| U5 | `shiu/u05-tau-pointwise` | τ-power pointwise calculus, incl. `τ_a·τ_b ≤ τ_{ab}` (hence `τ^k ≤ τ_{2^k}`) |
| U6 | `shiu/u06-tau-summatory` | `τ_K` summatory ladder: `Σ_{n≤x} τ_K(n) ≪ x(log x)^{K−1}` and harmonic forms (§4.5) |
| U7 | `shiu/u07-max-coordinate` | Route 1 (§5.1): max-coordinate split, sharp-exponent interval/progression bounds near `θ = 1` |
| U8 | `shiu/u08-landreau` | Lay's explicit small-divisor inequality `τ(n) ≤ 8·Σ_{d∣n, d≤n^{1/4}} τ(d)^7` (§4.2) |
| U9 | `shiu/u09-all-theta` | Route 2 assembled (§5.2): the interchange at depth `1/4`, all `θ > 1/4` |
| U10 | `shiu/u10-brun-core` | Route 3 seed (§5.3): Bonferroni truncated Möbius, Mertens-free `Π_{p≤z}(1−1/p) ≤ 1/log z`, rough interval/progression counts |
| U11 | `shiu/u11-short-interval` | short-interval transfer toolkit (interval forms ↔ progression forms; dyadic-block plumbing) |
| U12 | `shiu/u12-vacuity-audit` | vacuity audit: pin down and document the §1.3 ex-falso surface while it still exists — **landed** (dfb4f62, `docs/audit/vacuity_20260818.md`) |
| U13 | `shiu/u13-research-memo` | this memo |

### 7.2 Assembly plan (after the units land)

1. **Partial `ShiuMajorant₂` at `k ≥ 1`, moduli `q ≤ P^{1/2−ε}`.**  Fold U3's counting, U5's
   pointwise calculus, and U6's summatory ladder through the §3.4 class reduction: below the wall
   the trivial-cutoff interchange closes, giving `ShiuMajorant₂ η` for every `η > 1/2 − ε`
   region reachable without small-divisor input, with `C` exhibited.  (U4 already inhabits the
   `k = 0` corner at full range.)
2. **Wire Route 2 for all θ.**  U8's lemma through the same skeleton (U9): `ShiuMajorant₂ η` for
   every `η > 1/4` — covering the run's `η′ = 43/93` — with explicit `A = 8^k`, `B = 7k`, and
   exhibited `C`.  This is the campaign's deliverable statement for the honest core (U1) to
   consume.
3. **Continue Route 3 toward full range.**  From U10's core: rough counts in progressions →
   smooth/rough class summation (leaning on U2's ported canonical-divisor grammar) → the sharp
   `(P/φ(q))(log P)^{2^k−1}` at every `η ∈ (0, 1/2)`.  Note U2's file is deliberately unimported
   (its commit message); assembly must bring these modules into the build graph deliberately.

### 7.3 Follow-up campaign items

* **Smooth/rough decomposition end-to-end** — Shiu's actual argument (§5.3 stage 3) as a
  standalone reusable development: unique smooth/rough factorization, progression-compatible
  smooth summation, Rankin tails.
* **Bordellès-grade explicit constants** (§4.3) throughout the Route 3 chain, so the final
  `ShiuMajorant₂` instances exhibit numeric `K` and `C` — the form the LogBudget audit and any
  future window-budget arithmetic consume best.
* **The `C < 2` question as a separate research problem** (§6.2): what coefficient-sensitive
  mechanism — cancellation *before* absolute values, per `ActualScaleBBLR`'s scope note and
  `docs/audit/log_budget_routes.md` — could beat the majorant's inherent `C = 2^u − 1 ≥ 3`?  This
  is rung 3's true frontier; no majorant route of §5 touches it, and it should not be allowed to
  masquerade as one.
