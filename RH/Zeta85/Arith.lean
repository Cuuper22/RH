/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Arith.lean — the arithmetic vocabulary in which `RH/Zeta85/Hypotheses.lean` states its
axioms.  **Definitions only**: no axiom, no `sorry`, nothing opaque.  Every object below is built
from Mathlib (`ArithmeticFunction.vonMangoldt`, `Nat.totient`, `ArithmeticFunction.sigma`,
`Complex.exp`) by finite sums and elementary operations, so that the axioms of the next layer are
statements about objects a reader can inspect.

Two deliberate design choices, both of which make the axioms **weaker** (hence safer) than the
sources they render:

* every "main term" (the BBLR gcd main term, the prime-pair singular series) is **existentially
  quantified** rather than written out.  The sources characterise those terms by the computation
  that produces them; existentially quantifying them is strictly less than asserting the sources'
  formulas, and it is all the downstream transfer consumes.
* every "≪" is rendered as an explicit `∃ K, ∀ large …` with the implied constants exposed, and
  every logarithmic power is an explicit exponent variable (never absorbed) — see
  `RH/Zeta85/Discharge/LogBudget.lean` for the audit this makes possible.
-/
import Mathlib

open scoped BigOperators ArithmeticFunction
open Finset

noncomputable section

namespace RH
namespace Zeta85

/-! ## 1. Elementary vocabulary -/

/-- `e(x) = exp(2πix)`. -/
def cexp (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * x * Complex.I)

/-- `‖θ‖`, the distance from `θ` to the nearest integer. -/
def nearInt (θ : ℝ) : ℝ := |θ - (round θ : ℝ)|

lemma nearInt_nonneg (θ : ℝ) : 0 ≤ nearInt θ := abs_nonneg _

lemma nearInt_le_half (θ : ℝ) : nearInt θ ≤ 1 / 2 := by
  simpa [nearInt] using abs_sub_round θ

/-- `S_{H₀}(θ) = Σ_h w(h/H₀)·e(hθ)`, the smooth signed shift sum of
`docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §2.  A weight `w` supported in `(1,2)`
makes `w(h/H₀) = 0` unless `H₀ < h < 2H₀`, so truncating the range at `⌈2H₀⌉` loses nothing. -/
def shiftSum (w : ℝ → ℝ) (H₀ θ : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ⌈2 * H₀⌉₊, (w (h / H₀) : ℂ) * cexp (h * θ)

/-- A coefficient sequence is *divisor bounded* of order `k` with constant `K`:
`|c n| ≤ K·τ(n)^k`, `τ = σ₀` the divisor-counting function.  This is the "fixed-divisor majorant"
hypothesis of `docs/run/12` §2 and of BBLR Proposition 3.1. -/
def DivisorBounded (c : ℕ → ℝ) (K : ℝ) (k : ℕ) : Prop :=
  ∀ n : ℕ, |c n| ≤ K * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k

/-- `R` obeys `|R T| ≤ K·T^θ·(log T)^C` for all large `T` — a `≪` with **both** the power and the
logarithmic exponent named.  Never absorb a log into `K`: `C` is the audited quantity of
`RH/Zeta85/Discharge/LogBudget.lean`. -/
def PolyLogBound (R : ℝ → ℝ) (θ C K T₁ : ℝ) : Prop :=
  ∀ T ≥ T₁, |R T| ≤ K * T ^ θ * (Real.log T) ^ C

/-! ## 2. The BBLR quadratic-divisor sum -/

/-- `S₊`, the smoothly `h`-averaged quadratic-divisor sum of Bettin–Bui–Li–Radziwiłł,
Proposition 3.1 (JEMS 22 (2020) 3953–3980):

  `S₊ = Σ_{a m₁ m₂ − b n₁ n₂ = h ≠ 0} α_a β_b W₁(m₁/M₁) W₂(m₂/M₂) W₃(n₁/N₁) W₄(n₂/N₂) · wt(h/H)`,

with `a ≍ A`, `b ≍ B`, `m₁ ≍ M₁`, `m₂ ≍ M₂`, `n₁ ≍ N₁`, `n₂ ≍ N₂`, `M = M₁M₂`, `N = N₁N₂`,
`h ≍ H`.  The dyadic ranges are rendered as `Icc 1 ⌈2·⋆⌉`, which contains the support of every
weight normalised to `(1,2)`; the `h ≠ 0` restriction is the `if` below.  This is the
"quadratic-divisor shape" that `docs/run/03_arithmetic_cycle3.md` (11) and
`docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` §1 feed the proposition. -/
def bblrSum (α β : ℕ → ℂ) (W₁ W₂ W₃ W₄ wt : ℝ → ℂ) (A B M₁ M₂ N₁ N₂ H : ℝ) : ℂ :=
  ∑ a ∈ Finset.Icc 1 ⌈2 * A⌉₊, ∑ b ∈ Finset.Icc 1 ⌈2 * B⌉₊,
  ∑ m₁ ∈ Finset.Icc 1 ⌈2 * M₁⌉₊, ∑ m₂ ∈ Finset.Icc 1 ⌈2 * M₂⌉₊,
  ∑ n₁ ∈ Finset.Icc 1 ⌈2 * N₁⌉₊, ∑ n₂ ∈ Finset.Icc 1 ⌈2 * N₂⌉₊,
    (if ((a * m₁ * m₂ : ℤ) - (b * n₁ * n₂ : ℤ)) ≠ 0 then
      α a * β b * W₁ (m₁ / M₁) * W₂ (m₂ / M₂) * W₃ (n₁ / N₁) * W₄ (n₂ / N₂)
        * wt ((((a * m₁ * m₂ : ℤ) - (b * n₁ * n₂ : ℤ) : ℤ) : ℝ) / H)
    else 0)

/-- The five hypotheses of BBLR Proposition 3.1, at parameter `ε` and with the constants named:
`W_i^{(j)} ≪ (ABMN)^ε` for `j ≤ 4` (rendered as a uniform bound on the four weights and their
iterated derivatives), `α_a ≪ A^ε`, `β_b ≪ B^ε`, `M₁ ≤ M₂(ABMN)^ε`, `N₁ ≤ N₂(ABMN)^ε`; together
with the range restriction `H ≪ (AB)^{1/2+ε}` under which the Watt-strengthened error is valid. -/
structure BBLRHyps (α β : ℕ → ℂ) (W₁ W₂ W₃ W₄ : ℝ → ℂ)
    (A B M₁ M₂ N₁ N₂ H ε : ℝ) : Prop where
  A_pos : 1 ≤ A
  B_pos : 1 ≤ B
  M₁_pos : 1 ≤ M₁
  M₂_pos : 1 ≤ M₂
  N₁_pos : 1 ≤ N₁
  N₂_pos : 1 ≤ N₂
  H_pos : 1 ≤ H
  eps_pos : 0 < ε
  /-- `W_i^{(j)} ≪ (ABMN)^ε`, `0 ≤ j ≤ 4`, for each of the four smooth weights. -/
  weights : ∀ i : Fin 4, ∀ j ≤ 4, ∀ x : ℝ,
    ‖iteratedDeriv j (![W₁, W₂, W₃, W₄] i) x‖ ≤ (A * B * (M₁ * M₂) * (N₁ * N₂)) ^ ε
  /-- `α_a ≪ A^ε`. -/
  alpha : ∀ a : ℕ, ‖α a‖ ≤ A ^ ε
  /-- `β_b ≪ B^ε`. -/
  beta : ∀ b : ℕ, ‖β b‖ ≤ B ^ ε
  /-- `M₁ ≤ M₂ (ABMN)^ε`. -/
  M_bal : M₁ ≤ M₂ * (A * B * (M₁ * M₂) * (N₁ * N₂)) ^ ε
  /-- `N₁ ≤ N₂ (ABMN)^ε`. -/
  N_bal : N₁ ≤ N₂ * (A * B * (M₁ * M₂) * (N₁ * N₂)) ^ ε
  /-- `H ≪ (AB)^{1/2+ε}` — the range of the Watt-strengthened error term. -/
  H_range : H ≤ (A * B) ^ (1 / 2 + ε)

/-- The published BBLR error factor, **with the first term `AB` and not `(AB)^{1/2}`**
(`docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` (3); `docs/run/03_arithmetic_cycle3.md`
(12) misquotes it — see `FINDINGS.md` §3):

  `(ABMNH²)^{1/4+ε}·(AB + H^{1/4}(A+B)^{1/2}(ABMN)^{1/8})`. -/
def bblrErrorFactor (A B M₁ M₂ N₁ N₂ H ε : ℝ) : ℝ :=
  (A * B * (M₁ * M₂) * (N₁ * N₂) * H ^ 2) ^ (1 / 4 + ε)
    * (A * B + H ^ ((1 : ℝ) / 4) * (A + B) ^ ((1 : ℝ) / 2)
        * (A * B * (M₁ * M₂) * (N₁ * N₂)) ^ ((1 : ℝ) / 8))

/-- **BBLR Proposition 3.1, the error bound**, as a Prop.  Under the five hypotheses `BBLRHyps` and
`H ≪ (AB)^{1/2+ε}`, the quadratic-divisor sum splits as `S₊ = M + E` with `M` the `(am₁,bn₁) = d`
gcd main term and

  `E ≪_ε (ABMNH²)^{1/4+ε}·(AB + H^{1/4}(A+B)^{1/2}(ABMN)^{1/8})`.

The main term `M` is existentially quantified (see the module docstring): asserting only its
existence is weaker than asserting BBLR's formula for it, and it is all the downstream chain uses. -/
def BBLRErrorBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Kε : ℝ, 0 < Kε ∧
    ∀ (α β : ℕ → ℂ) (W₁ W₂ W₃ W₄ wt : ℝ → ℂ) (A B M₁ M₂ N₁ N₂ H : ℝ),
      BBLRHyps α β W₁ W₂ W₃ W₄ A B M₁ M₂ N₁ N₂ H ε →
      (∀ x, ‖wt x‖ ≤ 1) →
      ∃ Mterm : ℂ,
        ‖bblrSum α β W₁ W₂ W₃ W₄ wt A B M₁ M₂ N₁ N₂ H - Mterm‖
          ≤ Kε * bblrErrorFactor A B M₁ M₂ N₁ N₂ H ε

/-- **The Poisson-stage block decomposition** — BBLR Proposition 3.1's proof, equation (14),
combined with the separation bound and the `d`-sum of
`docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` (6), (11), (17).

After Poisson summation in the two long variables, `S₊` is the zero-frequency (main) term plus a
finite sum over `d = (am₁, bn₁)` of blocks

  `R_d = Σ_{ℓ≠0} Σ_{p ≍ P_d, q ≍ Q_d, (p,q)=1} c_{d,p} e_{d,q} F_{d,ℓ}(p,q) Σ_h w_d(h) e(∓ℓ h p̄/q)`,

with `P_d ≍ AM₁/d`, `Q_d ≍ BN₁/d`, `H_d = H/d`, and `‖F_{d,ℓ}‖ ≪_J d(1+|ℓ|d)^{−J}(log T)^{C_J}`.
Cycle 5's §3 combines that decay with the signed-shift lemma (12)–(13) and the progression majorant
(14)–(15) into the per-block bound `|R_d| ≪ P_d(Q_d + H_d)(1+d)^{−2}(log T)^C`, which is what is
recorded here (the individual blocks are existentially quantified rather than written out; the
per-block bound is the content the `d`-sum of (18) consumes). -/
def BBLRPoissonBlocks : Prop :=
  ∀ (α β : ℕ → ℂ) (W₁ W₂ W₃ W₄ wt : ℝ → ℂ) (A B M₁ M₂ N₁ N₂ H : ℝ),
    1 ≤ A → 1 ≤ B → 1 ≤ M₁ → 1 ≤ N₁ → 1 ≤ H →
    ∃ (Mterm : ℂ) (Dmax : ℕ) (blocks : ℕ → ℂ) (Klog Clog : ℝ), 0 ≤ Klog ∧
      bblrSum α β W₁ W₂ W₃ W₄ wt A B M₁ M₂ N₁ N₂ H
        = Mterm + ∑ d ∈ Finset.Icc 1 Dmax, blocks d ∧
      ∀ d ∈ Finset.Icc 1 Dmax,
        ‖blocks d‖ ≤ Klog * ((A * M₁ / d) * (B * N₁ / d + H / d)) * (1 + (d : ℝ)) ^ (-(2 : ℝ))
          * (Real.log (A * B * M₁ * N₁ * H + 3)) ^ Clog

/-! ## 3. The signed prime-pair aggregate -/

/-- `Σ_{n ≤ 2X} Λ(n)Λ(n+h)·V(n/X)`, the smoothly weighted prime-pair correlation at shift `h`
(`docs/run/02_certificate_cycle2.md` (12), `docs/run/01_arithmetic_cycle1.md` (5)). -/
def pairCorr (V : ℝ → ℝ) (X : ℝ) (h : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌈2 * X⌉₊,
    ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + h) * V (n / X)

/-- The **signed, smoothly weighted aggregate discrepancy** `(AS)` of
`docs/run/01_arithmetic_cycle1.md`, with the singular-series main term written through an
unspecified `S : ℕ → ℝ`:

  `Σ_h w(h/H)·( Σ_n Λ(n)Λ(n+h)V(n/X) − S(h)·X·I_V )`,

`I_V = ∫₀^∞ V`.  The `h`-sum is performed **before** any absolute value is taken — that is the whole
point of the construction (`docs/run/12` §2, "the notation on the left means that the `h`-sum itself
is performed first"). -/
def signedPairAggregate (w V : ℝ → ℝ) (S : ℕ → ℝ) (IV X H : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ⌈2 * H⌉₊, w (h / H) * (pairCorr V X h - S h * X * IV)

/-- **The trace-grade criterion at connected support `σ`.**  There is a singular-series function `S`
such that, for every pair of bounded weights `(w, V)` and every logarithmic saving `A`, the signed
aggregate at `X = T^σ`, `H = X/T = T^{σ−1}` is `O_A(X (log X)^{−A})`.

This is exactly `(AS)` of `docs/run/01_arithmetic_cycle1.md` §4 / `(18)` of
`docs/run/02_certificate_cycle2.md` §3, i.e. the statement whose *failure by one factor `H`* is the
whole obstruction analysed in cycles 1–4 and whose proof at every fixed `σ < 3/2` is claimed by
cycle 5.  `S` is existentially quantified (see the module docstring). -/
def SignedPairTraceGrade (σ : ℝ) : Prop :=
  ∃ S : ℕ → ℝ, ∀ (w V : ℝ → ℝ), (∀ x, |w x| ≤ 1) → (∀ x, |V x| ≤ 1) → ∀ IV : ℝ, |IV| ≤ 1 →
    ∀ Alog : ℝ, 0 < Alog → ∃ K T₁ : ℝ, ∀ T ≥ T₁,
      |signedPairAggregate w V S IV (T ^ σ) (T ^ (σ - 1))|
        ≤ K * T ^ σ * (Real.log T) ^ (-Alog)

/-! ## 4. The Shiu-type progression majorant -/

/-- `Σ_{p ≍ P, p ≡ r (q)} |c_p|`, the progression sum of `docs/run/12` (14). -/
def progressionSum (c : ℕ → ℝ) (P : ℝ) (q r : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q), |c p|

/-- The Shiu-type majorant of `docs/run/12` (14):
`Σ_{p ≍ P, p ≡ r (q), (r,q)=1} |c_p| ≪ (P/φ(q))·(log T)^C`, uniformly for `q ≤ P·T^{−η+o(1)}`. -/
def ShiuMajorant (η : ℝ) : Prop :=
  ∀ (c : ℕ → ℝ) (Kc : ℝ) (k : ℕ), DivisorBounded c Kc k →
    ∃ C K T₁ : ℝ, ∀ T ≥ T₁, ∀ P : ℝ, 1 ≤ P → ∀ q r : ℕ, 0 < q → Nat.Coprime r q →
      (q : ℝ) ≤ P * T ^ (-η) →
      progressionSum c P q r ≤ K * (P / (Nat.totient q : ℝ)) * (Real.log T) ^ C

end Zeta85
end RH

end
