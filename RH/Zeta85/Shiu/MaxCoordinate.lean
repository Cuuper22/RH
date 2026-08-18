/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Shiu/MaxCoordinate.lean — Route 1 (max-coordinate split): SHARP-log-exponent bounds for
`∑ τ(n)^j` over short intervals `(x, x+y]`.

Max-coordinate / divisor-splitting argument, classical (cf. proofs of Shiu-type theorems for `τ^k`
in short intervals); sharp log exponent `2^j − 1`.  Every ordered `K`-fold factorization
`d₁ ⋯ d_K = n` of an `n ∈ (x, x+y]` has some coordinate `d ≥ n^{1/K}`; extracting it — cost: a
factor `K`, realized below as an induction on the number of convolution factors rather than by
manipulating tuple sets — and re-grouping the resulting double count so that the cofactor
`m = n/d ≤ (x+y)/x^{1/K}` is the outer variable turns the short-interval sum of `(ζ^K) n` into
`K · ∑_{m ≤ M} (ζ^{K−1}) m · #{multiples of m in (x, x+y]}`, which the divisor-power summatory
ladder bounds by `O(y (1 + log x)^{K−1})` as soon as `y ⪆ x^{1−1/K}`.

Main results:
* `maxCoord_tau_sq_short_interval` : for `x ≥ 1` and `x^{3/4} ≤ y ≤ x`,
  `∑_{x < n ≤ x+y} τ(n)² ≤ 400 · y · (1 + log x)³`;
* `maxCoord_tau_fourth_short_interval` : for `x ≥ 1` and `x^{15/16} ≤ y ≤ x`,
  `∑_{x < n ≤ x+y} τ(n)⁴ ≤ 2097152 · y · (1 + log x)^15`.

Both log exponents are sharp (`2^j − 1` for `τ^j`).

Everything is self-contained over Mathlib: the campaign's units never import each other, so the
τ-power pointwise calculus and the `(ζ^k)` summatory ladder are restated and proved locally as
`private` lemmas.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace RH
namespace Zeta85
namespace Shiu

/-! ## ζ-convolution evaluation helpers

`ζ^K` (Dirichlet-convolution power of `ArithmeticFunction.zeta`) is the ordered-`K`-fold-
factorization counting function; peeling one convolution factor off either end rewrites its value
as a sum over `Nat.divisorsAntidiagonal`. -/

private lemma zeta_mul_apply_AD (f : ArithmeticFunction ℕ) {n : ℕ} (hn : n ≠ 0) :
    (ζ * f) n = ∑ p ∈ n.divisorsAntidiagonal, f p.2 := by
  rw [mul_apply]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have h1 : p.1 ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hp1
    exact hn hp1.symm
  rw [zeta_apply_ne h1, one_mul]

private lemma mul_zeta_apply_AD (f : ArithmeticFunction ℕ) {n : ℕ} (hn : n ≠ 0) :
    (f * ζ) n = ∑ p ∈ n.divisorsAntidiagonal, f p.1 := by
  rw [mul_apply]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have h2 : p.2 ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hp1
    exact hn hp1.symm
  rw [zeta_apply_ne h2, mul_one]

private lemma zetaPow_succ_apply_left (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (ζ ^ (k + 1)) n = ∑ p ∈ n.divisorsAntidiagonal, (ζ ^ k) p.2 := by
  rw [pow_succ']
  exact zeta_mul_apply_AD _ hn

private lemma zetaPow_succ_apply_right (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (ζ ^ (k + 1)) n = ∑ p ∈ n.divisorsAntidiagonal, (ζ ^ k) p.1 := by
  rw [pow_succ]
  exact mul_zeta_apply_AD _ hn

/-- Hockey-stick, in the running form: `∑_{i ≤ m} C(i+K, K) = C(m+K+1, K+1)`. -/
private lemma sum_range_choose_add (K : ℕ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (i + K).choose K = (m + K + 1).choose (K + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have e1 : m + 1 + K = m + K + 1 := by omega
    rw [e1]
    have h : (m + K + 1 + 1).choose (K + 1)
        = (m + K + 1).choose K + (m + K + 1).choose (K + 1) :=
      Nat.choose_succ_succ' (m + K + 1) K
    omega

/-- `(ζ^K)(p^m) = C(m+K−1, K−1)`: the prime-power value of the `K`-fold divisor function. -/
private lemma zetaPow_apply_prime_pow (k : ℕ) {p : ℕ} (hp : p.Prime) :
    ∀ m : ℕ, (ζ ^ (k + 1)) (p ^ m) = (m + k).choose k := by
  induction k with
  | zero =>
    intro m
    rw [pow_one, zeta_apply_ne (pow_ne_zero m hp.pos.ne')]
    simp
  | succ K ih =>
    intro m
    rw [pow_succ', zeta_mul_apply, Nat.divisors_prime_pow hp, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    rw [Finset.sum_congr rfl fun i _ => ih i]
    exact sum_range_choose_add K m

/-! ## Prime-power `choose` inequalities -/

/-- `(m+1)² ≤ C(m+3, 3)`: the τ² prime-power comparison, by the ratio induction
`C(m+4,3)·(m+1) = C(m+3,3)·(m+4)` (from `Nat.choose_mul_succ_eq`). -/
private lemma succ_sq_le_choose (m : ℕ) : (m + 1) ^ 2 ≤ (m + 3).choose 3 := by
  induction m with
  | zero => norm_num [Nat.choose_self]
  | succ m ih =>
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos m)
    have hid : (m + 4).choose 3 * (m + 1) = (m + 3).choose 3 * (m + 4) :=
      (Nat.choose_mul_succ_eq (m + 3) 3).symm
    rw [hid]
    calc (m + 2) ^ 2 * (m + 1)
        ≤ (m + 1) ^ 2 * (m + 4) := by
          have hkey : (m + 2) ^ 2 * (m + 1) + m * (m + 1) = (m + 1) ^ 2 * (m + 4) := by ring
          omega
      _ ≤ (m + 3).choose 3 * (m + 4) := Nat.mul_le_mul ih le_rfl

/-! ## Pointwise majorization `τ(n)² ≤ (ζ⁴) n` -/

/-- Pointwise: `τ(n)² ≤ (ζ^4) n` for `n ≠ 0`.  Both sides are multiplicative; on prime powers this
is `(m+1)² ≤ C(m+3, 3)`.  (Restated locally: campaign units do not import each other.) -/
private lemma tau_sq_le_zetaPow_four {n : ℕ} (hn : n ≠ 0) : σ 0 n ^ 2 ≤ (ζ ^ 4) n := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn,
    (isMultiplicative_zeta.pow (k := 4)).multiplicative_factorization _ hn]
  rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
  refine Finset.prod_le_prod' fun q hq => ?_
  have hq' : q.Prime := Nat.prime_of_mem_primeFactors (by
    rwa [Nat.support_factorization] at hq)
  rw [sigma_zero_apply_prime_pow hq']
  have h4 : (ζ ^ 4) (q ^ n.factorization q) = (n.factorization q + 3).choose 3 :=
    zetaPow_apply_prime_pow 3 hq' _
  rw [h4]
  exact succ_sq_le_choose _

/-! ## The max-coordinate split

The indicator of the "large" coordinates is an arithmetic function, so extracting a large
coordinate is a Dirichlet convolution and the bookkeeping of the split is ring arithmetic in
`ArithmeticFunction ℕ` rather than a bijection of tuple sets. -/

/-- Indicator of `[max t 1, ∞)` as an arithmetic function. -/
private def bigIndicator (t : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if max t 1 ≤ n then 1 else 0, by simp⟩

private lemma bigIndicator_apply (t n : ℕ) :
    bigIndicator t n = if max t 1 ≤ n then 1 else 0 := rfl

private lemma bigIndicator_mul_apply (t k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (bigIndicator t * ζ ^ k) n
      = ∑ p ∈ n.divisorsAntidiagonal, (if t ≤ p.1 then (ζ ^ k) p.2 else 0) := by
  rw [mul_apply]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have h1 : p.1 ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hp1
    exact hn hp1.symm
  rw [bigIndicator_apply]
  by_cases hc : t ≤ p.1
  · rw [if_pos (by omega), if_pos hc, one_mul]
  · rw [if_neg (by omega), if_neg hc, zero_mul]

/-- **Max-coordinate split.**  If `t^{k+1} ≤ n` then every ordered `(k+1)`-fold factorization of
`n` has a coordinate `≥ t`; splitting off one such coordinate (at a cost of `k+1`, for the choice
of which coordinate) bounds `(ζ^{k+1}) n` by `(k+1)` times the convolution of the large-coordinate
indicator with `ζ^k`. -/
private lemma zetaPow_le_maxCoord (t : ℕ) :
    ∀ (k n : ℕ), n ≠ 0 → t ^ (k + 1) ≤ n →
      (ζ ^ (k + 1)) n ≤ (k + 1) * (bigIndicator t * ζ ^ k) n := by
  intro k
  induction k with
  | zero =>
    intro n hn ht
    rw [pow_one] at ht
    rw [pow_one, zeta_apply_ne hn, pow_zero, mul_one, bigIndicator_apply, if_pos (by omega)]
  | succ k ih =>
    intro n hn ht
    have hsplit : ∀ p ∈ n.divisorsAntidiagonal,
        (ζ ^ (k + 1)) p.2 ≤ (if t ≤ p.1 then (ζ ^ (k + 1)) p.2 else 0)
          + (k + 1) * (bigIndicator t * ζ ^ k) p.2 := by
      intro p hp
      obtain ⟨hp1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      by_cases hc : t ≤ p.1
      · rw [if_pos hc]
        exact Nat.le_add_right _ _
      · rw [if_neg hc, zero_add]
        have hd0 : p.1 ≠ 0 := by
          rintro h
          rw [h, zero_mul] at hp1
          exact hn hp1.symm
        have he0 : p.2 ≠ 0 := by
          rintro h
          rw [h, mul_zero] at hp1
          exact hn hp1.symm
        refine ih p.2 he0 ?_
        rcases Nat.lt_or_ge p.2 (t ^ (k + 1)) with hlt | hge
        · exfalso
          have h1 : p.1 * p.2 < t * t ^ (k + 1) := Nat.mul_lt_mul'' (by omega) hlt
          rw [hp1, ← pow_succ'] at h1
          omega
        · exact hge
    calc (ζ ^ (k + 1 + 1)) n
        = ∑ p ∈ n.divisorsAntidiagonal, (ζ ^ (k + 1)) p.2 := zetaPow_succ_apply_left (k + 1) hn
      _ ≤ ∑ p ∈ n.divisorsAntidiagonal, ((if t ≤ p.1 then (ζ ^ (k + 1)) p.2 else 0)
            + (k + 1) * (bigIndicator t * ζ ^ k) p.2) := Finset.sum_le_sum hsplit
      _ = (bigIndicator t * ζ ^ (k + 1)) n
            + (k + 1) * ∑ p ∈ n.divisorsAntidiagonal, (bigIndicator t * ζ ^ k) p.2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, bigIndicator_mul_apply t (k + 1) hn]
      _ = (bigIndicator t * ζ ^ (k + 1)) n
            + (k + 1) * (ζ * (bigIndicator t * ζ ^ k)) n := by
          rw [zeta_mul_apply_AD _ hn]
      _ = (k + 1 + 1) * (bigIndicator t * ζ ^ (k + 1)) n := by
          rw [show (ζ : ArithmeticFunction ℕ) * (bigIndicator t * ζ ^ k)
                = bigIndicator t * ζ ^ (k + 1) from by ring]
          ring

/-! ## Re-grouping the double count over a short interval -/

/-- Re-grouping the max-coordinate double count over `(x, x+y]`: the cofactor `m` becomes the outer
variable, ranging over `m ≤ (x+y)/t`, and the inner count is the number of multiples of `m` in the
interval. -/
private lemma sum_interval_maxCoord (t x y : ℕ) (ht : 0 < t) (g : ℕ → ℕ) :
    ∑ n ∈ Finset.Ioc x (x + y), ∑ p ∈ n.divisorsAntidiagonal, (if t ≤ p.1 then g p.2 else 0)
      ≤ ∑ m ∈ Finset.Ioc 0 ((x + y) / t), g m * ((x + y) / m - x / m) := by
  have key : ∑ n ∈ Finset.Ioc x (x + y),
        ∑ p ∈ n.divisorsAntidiagonal, (if t ≤ p.1 then g p.2 else 0)
      = ∑ m ∈ Finset.Ioc 0 ((x + y) / t),
          ∑ _d ∈ (Finset.Ioc (x / m) ((x + y) / m)).filter (fun d => t ≤ d), g m := by
    simp_rw [← Finset.sum_filter]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun z => (⟨z.2.2, z.2.1⟩ : Σ _ : ℕ, ℕ))
      (fun w => (⟨w.2 * w.1, (w.2, w.1)⟩ : Σ _ : ℕ, ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨n, d, m⟩ hz
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Ioc,
        Nat.mem_divisorsAntidiagonal] at hz
      obtain ⟨⟨hx1, hx2⟩, ⟨hdm, hn0⟩, htd⟩ := hz
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · rw [mul_zero] at hdm
          exact absurd hdm.symm hn0
        · exact h
      refine Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨hm0, ?_⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le ht]
        calc m * t ≤ m * d := Nat.mul_le_mul_left m htd
          _ = n := by rw [mul_comm]; exact hdm
          _ ≤ x + y := hx2
      · refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, htd⟩
        · rw [Nat.div_lt_iff_lt_mul hm0]
          rw [← hdm] at hx1
          exact hx1
        · rw [Nat.le_div_iff_mul_le hm0, hdm]
          exact hx2
    · rintro ⟨m, d⟩ hw
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Ioc] at hw
      obtain ⟨⟨hm0, hmM⟩, ⟨hd1, hd2⟩, htd⟩ := hw
      have hxlt : x < d * m := (Nat.div_lt_iff_lt_mul hm0).mp hd1
      have hdm2 : d * m ≤ x + y := (Nat.le_div_iff_mul_le hm0).mp hd2
      have hne : d * m ≠ 0 := by omega
      refine Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨hxlt, hdm2⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hne⟩, htd⟩
    · rintro ⟨n, d, m⟩ hz
      simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hz
      obtain ⟨-, ⟨hdm, -⟩, -⟩ := hz
      simp only []
      rw [hdm]
    · rintro ⟨m, d⟩ _
      rfl
    · rintro ⟨n, d, m⟩ _
      rfl
  rw [key]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [Finset.sum_const, smul_eq_mul, mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  calc #((Finset.Ioc (x / m) ((x + y) / m)).filter (fun d => t ≤ d))
      ≤ #(Finset.Ioc (x / m) ((x + y) / m)) := Finset.card_filter_le _ _
    _ = (x + y) / m - x / m := Nat.card_Ioc _ _

/-! ## The `(ζ^k)` summatory ladder -/

private lemma log_natCast_le_log_natCast {a b : ℕ} (h : a ≤ b) :
    Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

private lemma sum_inv_le_one_add_log (n : ℕ) :
    ∑ e ∈ Finset.Ioc 0 n, ((e : ℝ))⁻¹ ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have hset : Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset]
  exact h

/-- Hyperbola re-indexing: a double sum over ordered factorizations `d·e = m ≤ N` is the double sum
over `d ≤ N` and `e ≤ N/d`. -/
private lemma sum_AD_hyperbola {M : Type*} [AddCommMonoid M] (N : ℕ) (G : ℕ → ℕ → M) :
    ∑ m ∈ Finset.Ioc 0 N, ∑ p ∈ m.divisorsAntidiagonal, G p.1 p.2
      = ∑ d ∈ Finset.Ioc 0 N, ∑ e ∈ Finset.Ioc 0 (N / d), G d e := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun z => (⟨z.2.1, z.2.2⟩ : Σ _ : ℕ, ℕ))
    (fun w => (⟨w.1 * w.2, (w.1, w.2)⟩ : Σ _ : ℕ, ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, d, e⟩ hz
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisorsAntidiagonal] at hz
    obtain ⟨⟨hm0, hmN⟩, hde, hn0⟩ := hz
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · rw [zero_mul] at hde
        exact absurd hde.symm hn0
      · exact h
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · rw [mul_zero] at hde
        exact absurd hde.symm hn0
      · exact h
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨hd0, ?_⟩, Finset.mem_Ioc.mpr ⟨he0, ?_⟩⟩
    · calc d ≤ d * e := Nat.le_mul_of_pos_right d he0
        _ = m := hde
        _ ≤ N := hmN
    · rw [Nat.le_div_iff_mul_le hd0, Nat.mul_comm, hde]
      exact hmN
  · rintro ⟨d, e⟩ hw
    simp only [Finset.mem_sigma, Finset.mem_Ioc] at hw
    obtain ⟨⟨hd0, hdN⟩, he0, heN⟩ := hw
    have hde : d * e ≤ N := by
      rw [Nat.le_div_iff_mul_le hd0] at heN
      rw [Nat.mul_comm]
      exact heN
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hd0 he0, hde⟩, ?_⟩
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (Nat.mul_pos hd0 he0).ne'⟩
  · rintro ⟨m, d, e⟩ hz
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hz
    obtain ⟨-, hde, -⟩ := hz
    simp only []
    rw [hde]
  · rintro ⟨d, e⟩ _
    rfl
  · rintro ⟨m, d, e⟩ _
    rfl

/-- Ladder, divided form: `∑_{m ≤ N} (ζ^j) m / m ≤ (1 + log N)^j`. -/
private lemma zetaPow_ladder_div : ∀ (j N : ℕ),
    ∑ m ∈ Finset.Ioc 0 N, ((ζ ^ j) m : ℝ) / m ≤ (1 + Real.log N) ^ j := by
  intro j
  induction j with
  | zero =>
    intro N
    have hcong : ∀ m ∈ Finset.Ioc 0 N,
        (((ζ ^ 0) m : ℕ) : ℝ) / (m : ℝ) = if m = 1 then (1 : ℝ) else 0 := by
      intro m _
      by_cases h1 : m = 1
      · subst h1
        simp
      · simp [h1]
    rw [Finset.sum_congr rfl hcong, pow_zero]
    simp only [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  | succ j ih =>
    intro N
    have hlog : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
    have hstep : ∑ m ∈ Finset.Ioc 0 N, ((ζ ^ (j + 1)) m : ℝ) / m
        = ∑ d ∈ Finset.Ioc 0 N, ∑ e ∈ Finset.Ioc 0 (N / d), ((ζ ^ j) d : ℝ) / (d * e) := by
      rw [← sum_AD_hyperbola N (fun d e => ((ζ ^ j) d : ℝ) / (d * e))]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm0 : m ≠ 0 := (Finset.mem_Ioc.mp hm).1.ne'
      rw [zetaPow_succ_apply_right j hm0]
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hp1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      rw [← hp1]
      push_cast
      ring
    rw [hstep]
    have hfac : ∀ d e : ℕ, ((ζ ^ j) d : ℝ) / (d * e) = (((ζ ^ j) d : ℝ) / d) * (e : ℝ)⁻¹ := by
      intro d e
      rw [div_mul_eq_div_div, div_eq_mul_inv]
    calc ∑ d ∈ Finset.Ioc 0 N, ∑ e ∈ Finset.Ioc 0 (N / d), ((ζ ^ j) d : ℝ) / (d * e)
        = ∑ d ∈ Finset.Ioc 0 N, (((ζ ^ j) d : ℝ) / d) * ∑ e ∈ Finset.Ioc 0 (N / d), (e : ℝ)⁻¹ := by
          simp_rw [hfac, ← Finset.mul_sum]
      _ ≤ ∑ d ∈ Finset.Ioc 0 N, (((ζ ^ j) d : ℝ) / d) * (1 + Real.log N) := by
          refine Finset.sum_le_sum fun d _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans (sum_inv_le_one_add_log (N / d)) ?_
          have := log_natCast_le_log_natCast (Nat.div_le_self N d)
          linarith
      _ = (∑ d ∈ Finset.Ioc 0 N, ((ζ ^ j) d : ℝ) / d) * (1 + Real.log N) := by
          rw [Finset.sum_mul]
      _ ≤ (1 + Real.log N) ^ j * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_right (ih N) (by linarith)
      _ = (1 + Real.log N) ^ (j + 1) := by ring

/-- Ladder, plain form: `∑_{m ≤ N} (ζ^{j+1}) m ≤ N (1 + log N)^j`. -/
private lemma zetaPow_ladder_sum (j N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, ((ζ ^ (j + 1)) m : ℝ) ≤ N * (1 + Real.log N) ^ j := by
  have h1 : ∑ m ∈ Finset.Ioc 0 N, ((ζ ^ (j + 1)) m : ℝ)
      = ∑ d ∈ Finset.Ioc 0 N, ∑ e ∈ Finset.Ioc 0 (N / d), ((ζ ^ j) d : ℝ) := by
    rw [← sum_AD_hyperbola N (fun d _ => ((ζ ^ j) d : ℝ))]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := (Finset.mem_Ioc.mp hm).1.ne'
    rw [zetaPow_succ_apply_right j hm0]
    push_cast
    ring
  rw [h1]
  have h2 : ∀ d ∈ Finset.Ioc 0 N, ∑ _e ∈ Finset.Ioc 0 (N / d), ((ζ ^ j) d : ℝ)
      ≤ (N : ℝ) * (((ζ ^ j) d : ℝ) / d) := by
    intro d _
    rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
    have hcast : (((N / d : ℕ)) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    have hnn : (0 : ℝ) ≤ ((ζ ^ j) d : ℝ) := by positivity
    calc (((N / d : ℕ)) : ℝ) * ((ζ ^ j) d : ℝ) ≤ ((N : ℝ) / d) * ((ζ ^ j) d : ℝ) := by
          exact mul_le_mul_of_nonneg_right hcast hnn
      _ = (N : ℝ) * (((ζ ^ j) d : ℝ) / d) := by ring
  calc ∑ d ∈ Finset.Ioc 0 N, ∑ _e ∈ Finset.Ioc 0 (N / d), ((ζ ^ j) d : ℝ)
      ≤ ∑ d ∈ Finset.Ioc 0 N, (N : ℝ) * (((ζ ^ j) d : ℝ) / d) := Finset.sum_le_sum h2
    _ = (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, ((ζ ^ j) d : ℝ) / d := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * (1 + Real.log N) ^ j :=
        mul_le_mul_of_nonneg_left (zetaPow_ladder_div j N) (by positivity)

/-! ## Counting multiples in a short interval -/

/-- `#{d : x < d·m ≤ x+y} = (x+y)/m − x/m ≤ y/m + 1`. -/
private lemma count_multiples_le (x y m : ℕ) (hm : 0 < m) :
    (((x + y) / m - x / m : ℕ) : ℝ) ≤ (y : ℝ) / m + 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : x / m ≤ (x + y) / m := Nat.div_le_div_right (Nat.le_add_right x y)
  rw [Nat.cast_sub hle]
  have h1 : (((x + y) / m : ℕ) : ℝ) ≤ ((x : ℝ) + y) / m := by
    have h := (Nat.cast_div_le (α := ℝ) (m := x + y) (n := m))
    push_cast at h
    exact h
  have h2 : (x : ℝ) / m - 1 ≤ ((x / m : ℕ) : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hmR]
    have hdm : m * (x / m) + x % m = x := Nat.div_add_mod x m
    have hmod : x % m < m := Nat.mod_lt _ hm
    have hx : x ≤ m * (x / m) + m := by omega
    calc (x : ℝ) ≤ ((m * (x / m) + m : ℕ) : ℝ) := by exact_mod_cast hx
      _ = (((x / m : ℕ) : ℝ) + 1) * m := by push_cast; ring
  have h3 : ((x : ℝ) + y) / m - ((x : ℝ) / m - 1) = (y : ℝ) / m + 1 := by
    field_simp
    ring
  linarith
/-! ## The ℕ-level max-coordinate bound over a short interval -/

/-- **Max-coordinate split, summed over `(x, x+y]`.**  Any `F` dominated pointwise by `ζ^{k+1}`
has short-interval sum at most `(k+1) · ∑_{m ≤ (x+y)/t} (ζ^k) m · #{multiples of m in (x, x+y]}`,
provided the threshold satisfies `t^{k+1} ≤ x`. -/
private lemma maxCoord_split_sum {t x y M k : ℕ} (ht0 : 0 < t) (htk : t ^ (k + 1) ≤ x)
    (hM : M = (x + y) / t) (F : ℕ → ℕ) (hF : ∀ n : ℕ, n ≠ 0 → F n ≤ (ζ ^ (k + 1)) n) :
    ∑ n ∈ Finset.Ioc x (x + y), F n
      ≤ (k + 1) * ∑ m ∈ Finset.Ioc 0 M, (ζ ^ k) m * ((x + y) / m - x / m) := by
  have h1 : ∑ n ∈ Finset.Ioc x (x + y), F n
      ≤ ∑ n ∈ Finset.Ioc x (x + y),
          (k + 1) * ∑ p ∈ n.divisorsAntidiagonal, (if t ≤ p.1 then (ζ ^ k) p.2 else 0) := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, -⟩ := Finset.mem_Ioc.mp hn
    have hn0 : n ≠ 0 := by omega
    refine le_trans (hF n hn0) ?_
    have h := zetaPow_le_maxCoord t k n hn0 (by omega)
    rwa [bigIndicator_mul_apply t k hn0] at h
  refine le_trans h1 ?_
  rw [← Finset.mul_sum, hM]
  exact Nat.mul_le_mul_left _ (sum_interval_maxCoord t x y ht0 (fun m => (ζ ^ k) m))

/-! ## The ℝ-level ladder bound -/

/-- Feeding the re-grouped double count to the summatory ladder: the `y/m` part contributes
`y (1 + log M)^{k+1}` and the `+1` part contributes `M (1 + log M)^k`. -/
private lemma maxCoord_ladder_bound (x y M k : ℕ) :
    ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ (k + 1)) m : ℝ) * (((x + y) / m - x / m : ℕ) : ℝ)
      ≤ (y : ℝ) * (1 + Real.log M) ^ (k + 1) + (M : ℝ) * (1 + Real.log M) ^ k := by
  have hstep : ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ (k + 1)) m : ℝ) * (((x + y) / m - x / m : ℕ) : ℝ)
      ≤ ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ (k + 1)) m : ℝ) * ((y : ℝ) / m + 1) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm0 : 0 < m := (Finset.mem_Ioc.mp hm).1
    exact mul_le_mul_of_nonneg_left (count_multiples_le x y m hm0) (by positivity)
  refine le_trans hstep ?_
  have hsplit : ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ (k + 1)) m : ℝ) * ((y : ℝ) / m + 1)
      = (y : ℝ) * (∑ m ∈ Finset.Ioc 0 M, ((ζ ^ (k + 1)) m : ℝ) / m)
        + ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ (k + 1)) m : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hsplit]
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := by positivity
  have hlad1 : ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ (k + 1)) m : ℝ) / m ≤ (1 + Real.log M) ^ (k + 1) :=
    zetaPow_ladder_div (k + 1) M
  have hlad2 : ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ (k + 1)) m : ℝ) ≤ (M : ℝ) * (1 + Real.log M) ^ k :=
    zetaPow_ladder_sum k M
  have := mul_le_mul_of_nonneg_left hlad1 hy0
  linarith

/-! ## The root threshold and the shape of the outer range -/

/-- A `2^r`-th root threshold: an integer `t ≥ 1` with `t^{2^r} ≤ x < (t+1)^{2^r}`, obtained by
iterating `Nat.sqrt` (`r` times). -/
private lemma exists_root_threshold {x : ℕ} (hx : 0 < x) (r : ℕ) :
    ∃ t : ℕ, 0 < t ∧ t ^ 2 ^ r ≤ x ∧ x + 1 ≤ (t + 1) ^ 2 ^ r := by
  induction r with
  | zero => exact ⟨x, hx, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨u, hu0, hu1, hu2⟩ := ih
    have hs1 : Nat.sqrt u * Nat.sqrt u ≤ u := Nat.sqrt_le u
    have hs2 : u < (Nat.sqrt u + 1) * (Nat.sqrt u + 1) := Nat.lt_succ_sqrt u
    have hs0 : 0 < Nat.sqrt u := by
      rcases Nat.eq_zero_or_pos (Nat.sqrt u) with h | h
      · rw [h] at hs2
        omega
      · exact h
    have hexp : (2 : ℕ) ^ (r + 1) = 2 * 2 ^ r := by
      rw [pow_succ]
      ring
    refine ⟨Nat.sqrt u, hs0, ?_, ?_⟩
    · calc Nat.sqrt u ^ 2 ^ (r + 1) = Nat.sqrt u ^ (2 * 2 ^ r) := by rw [hexp]
        _ = (Nat.sqrt u ^ 2) ^ 2 ^ r := by rw [pow_mul]
        _ ≤ u ^ 2 ^ r := Nat.pow_le_pow_left (by nlinarith) _
        _ ≤ x := hu1
    · calc x + 1 ≤ (u + 1) ^ 2 ^ r := hu2
        _ ≤ ((Nat.sqrt u + 1) ^ 2) ^ 2 ^ r := Nat.pow_le_pow_left (by nlinarith) _
        _ = (Nat.sqrt u + 1) ^ 2 ^ (r + 1) := by rw [hexp, pow_mul]

/-- The two facts the assembly needs about the outer range `M = (x+y)/t`: it is `≤ 4y`, and its
logarithm is within a factor `2` of `1 + log x`. -/
private lemma maxCoord_setup {x y t M : ℕ} (hx : 0 < x) (hyx : y ≤ x) (ht0 : 0 < t)
    (hM : M = (x + y) / t) (hkey : 2 * x ≤ 4 * y * t) :
    (M : ℝ) ≤ 4 * (y : ℝ) ∧ 1 + Real.log M ≤ 2 * (1 + Real.log x) := by
  have hx0R : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  constructor
  · have hkeyR : 2 * (x : ℝ) ≤ 4 * (y : ℝ) * (t : ℝ) := by exact_mod_cast hkey
    have hMle : (M : ℝ) ≤ ((x : ℝ) + (y : ℝ)) / (t : ℝ) := by
      have h := (Nat.cast_div_le (α := ℝ) (m := x + y) (n := t))
      push_cast at h
      rw [hM]
      exact h
    have hxy : ((x : ℝ) + (y : ℝ)) / (t : ℝ) ≤ 4 * (y : ℝ) := by
      rw [div_le_iff₀ htR]
      have hyxR : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hyx
      linarith
    linarith
  · have hMx : M ≤ 2 * x := by
      have h1 : M ≤ x + y := by
        rw [hM]
        exact Nat.div_le_self _ _
      omega
    have h1 : Real.log M ≤ Real.log ((2 * x : ℕ) : ℝ) := log_natCast_le_log_natCast hMx
    have h2 : Real.log ((2 * x : ℕ) : ℝ) = Real.log 2 + Real.log x := by
      push_cast
      rw [Real.log_mul (by norm_num) (ne_of_gt hx0R)]
    have h3 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
      linarith
    have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_natCast_nonneg x
    linarith

/-! ## Assembly: the `τ²` short-interval bound -/

/-- **Shiu-type short-interval bound for `τ²`, sharp log exponent `3 = 2² − 1`.**

For `x ≥ 1` and `x^{3/4} ≤ y ≤ x`,
`∑_{x < n ≤ x+y} τ(n)² ≤ 400 · y · (1 + log x)³`.

Max-coordinate / divisor-splitting argument, classical (cf. proofs of Shiu-type theorems for `τ^k`
in short intervals); the log exponent `3` is sharp. -/
theorem maxCoord_tau_sq_short_interval {x y : ℕ} (hx : 0 < x)
    (hy : (x : ℝ) ^ (3 / 4 : ℝ) ≤ (y : ℝ)) (hyx : y ≤ x) :
    ∑ n ∈ Finset.Ioc x (x + y), ((σ 0 n : ℕ) : ℝ) ^ 2
      ≤ 400 * (y : ℝ) * (1 + Real.log x) ^ 3 := by
  have hx0R : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hy0R : (0 : ℝ) ≤ (y : ℝ) := by positivity
  -- the fourth-root threshold `t`
  obtain ⟨t, ht0, htA, htB⟩ := exists_root_threshold hx 2
  norm_num at htA htB
  have htbig : x < 16 * t ^ 4 := by
    have h3 : t + 1 ≤ 2 * t := by omega
    have h4 : (t + 1) ^ 4 ≤ (2 * t) ^ 4 := Nat.pow_le_pow_left h3 4
    have h5 : (2 * t) ^ 4 = 16 * t ^ 4 := by ring
    omega
  -- `y⁴ ≥ x³`, from the hypothesis `y ≥ x^{3/4}`
  have hxy4 : x ^ 3 ≤ y ^ 4 := by
    have h34 : ((x : ℝ) ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = (x : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul hx0R.le]
      norm_num
    have hR : (x : ℝ) ^ (3 : ℕ) ≤ (y : ℝ) ^ (4 : ℕ) := by
      rw [← h34]
      exact pow_le_pow_left₀ (by positivity) hy 4
    exact_mod_cast hR
  have hkey : 2 * x ≤ 4 * y * t := by
    have hpow : (2 * x) ^ 4 ≤ (4 * y * t) ^ 4 := by
      calc (2 * x) ^ 4 = 16 * (x ^ 3 * x) := by ring
        _ ≤ 16 * (y ^ 4 * (16 * t ^ 4)) :=
            Nat.mul_le_mul_left 16 (Nat.mul_le_mul hxy4 (le_of_lt htbig))
        _ = (4 * y * t) ^ 4 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hpow
  set M := (x + y) / t with hM_def
  obtain ⟨hMy, hlogMx⟩ := maxCoord_setup hx hyx ht0 hM_def hkey
  -- the split, cast to `ℝ`, and the ladder
  have hNat : ∑ n ∈ Finset.Ioc x (x + y), σ 0 n ^ 2
      ≤ 4 * ∑ m ∈ Finset.Ioc 0 M, (ζ ^ 3) m * ((x + y) / m - x / m) := by
    have h := maxCoord_split_sum (k := 3) (t := t) (M := M) ht0 (by simpa using htA) hM_def
      (fun n => σ 0 n ^ 2) (fun n hn => by simpa using tau_sq_le_zetaPow_four hn)
    simpa using h
  have hcast : ∑ n ∈ Finset.Ioc x (x + y), ((σ 0 n : ℕ) : ℝ) ^ 2
      ≤ 4 * ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ 3) m : ℝ) * (((x + y) / m - x / m : ℕ) : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hNat
    push_cast at h
    exact h
  have hlad : ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ 3) m : ℝ) * (((x + y) / m - x / m : ℕ) : ℝ)
      ≤ (y : ℝ) * (1 + Real.log M) ^ 3 + (M : ℝ) * (1 + Real.log M) ^ 2 := by
    simpa using maxCoord_ladder_bound x y M 2
  -- numerics
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_natCast_nonneg x
  have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_natCast_nonneg M
  have hL0 : (0 : ℝ) ≤ 1 + Real.log M := by linarith
  have hLx1 : (1 : ℝ) ≤ 1 + Real.log x := by linarith
  have h3 : (1 + Real.log M) ^ 3 ≤ 8 * (1 + Real.log x) ^ 3 := by
    calc (1 + Real.log M) ^ 3 ≤ (2 * (1 + Real.log x)) ^ 3 := pow_le_pow_left₀ hL0 hlogMx 3
      _ = 8 * (1 + Real.log x) ^ 3 := by ring
  have h2 : (1 + Real.log M) ^ 2 ≤ 4 * (1 + Real.log x) ^ 3 := by
    have e2 : (1 + Real.log x) ^ 2 ≤ (1 + Real.log x) ^ 3 :=
      pow_le_pow_right₀ hLx1 (by norm_num)
    calc (1 + Real.log M) ^ 2 ≤ (2 * (1 + Real.log x)) ^ 2 := pow_le_pow_left₀ hL0 hlogMx 2
      _ = 4 * (1 + Real.log x) ^ 2 := by ring
      _ ≤ 4 * (1 + Real.log x) ^ 3 := by linarith
  have t1 : (y : ℝ) * (1 + Real.log M) ^ 3 ≤ (y : ℝ) * (8 * (1 + Real.log x) ^ 3) :=
    mul_le_mul_of_nonneg_left h3 hy0R
  have t2 : (M : ℝ) * (1 + Real.log M) ^ 2 ≤ (4 * (y : ℝ)) * (4 * (1 + Real.log x) ^ 3) := by
    calc (M : ℝ) * (1 + Real.log M) ^ 2 ≤ (4 * (y : ℝ)) * (1 + Real.log M) ^ 2 :=
          mul_le_mul_of_nonneg_right hMy (by positivity)
      _ ≤ (4 * (y : ℝ)) * (4 * (1 + Real.log x) ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
  have hnn : (0 : ℝ) ≤ (y : ℝ) * (1 + Real.log x) ^ 3 :=
    mul_nonneg hy0R (pow_nonneg (by linarith) 3)
  refine le_trans hcast ?_
  linarith

/-! ## The `τ⁴` chain: sixteen coordinates -/

/-- The arithmetic core of the τ⁴ ratio induction, stated for plain variables (`a = C(m+3,3)`,
`b = C(m+4,3)`, `c = C(m+15,15)`, `d = C(m+16,15)`) so that the ring normalization never sees a
`Nat.choose` term: cross-multiplying by `(m+1)²` reduces the step to `(m+4)² ≤ (m+16)(m+1)`, i.e.
`0 ≤ 9m`. -/
private lemma ratio_step {a b c d m : ℕ} (ih : a ^ 2 ≤ c)
    (hA : a * (m + 4) = b * (m + 1)) (hB : c * (m + 16) = d * (m + 1)) :
    b ^ 2 ≤ d := by
  have hstep : b ^ 2 * (m + 1) ^ 2 ≤ d * (m + 1) ^ 2 :=
    calc b ^ 2 * (m + 1) ^ 2 = (b * (m + 1)) ^ 2 := by ring
      _ = (a * (m + 4)) ^ 2 := by rw [hA]
      _ = a ^ 2 * (m + 4) ^ 2 := by ring
      _ ≤ c * (m + 4) ^ 2 := Nat.mul_le_mul_right _ ih
      _ ≤ c * ((m + 16) * (m + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          nlinarith
      _ = c * (m + 16) * (m + 1) := by ring
      _ = d * (m + 1) * (m + 1) := by rw [hB]
      _ = d * (m + 1) ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right hstep (by positivity)

/-- `C(m+3,3)² ≤ C(m+15,15)`: the τ⁴ prime-power comparison, by the ratio induction of
`ratio_step`. -/
private lemma choose_three_sq_le_choose_fifteen (m : ℕ) :
    ((m + 3).choose 3) ^ 2 ≤ (m + 15).choose 15 := by
  induction m with
  | zero => simp [Nat.choose_self]
  | succ m ih =>
    have hA : (m + 3).choose 3 * (m + 4) = (m + 4).choose 3 * (m + 1) := by
      have h := Nat.choose_mul_succ_eq (m + 3) 3
      have e1 : m + 3 + 1 = m + 4 := by omega
      have e2 : m + 3 + 1 - 3 = m + 1 := by omega
      rw [e1, e2] at h
      exact h
    have hB : (m + 15).choose 15 * (m + 16) = (m + 16).choose 15 * (m + 1) := by
      have h := Nat.choose_mul_succ_eq (m + 15) 15
      have e1 : m + 15 + 1 = m + 16 := by omega
      have e2 : m + 15 + 1 - 15 = m + 1 := by omega
      rw [e1, e2] at h
      exact h
    have e3 : m + 1 + 3 = m + 4 := by omega
    have e15 : m + 1 + 15 = m + 16 := by omega
    rw [e3, e15]
    exact ratio_step ih hA hB

/-- Pointwise: `τ(n)⁴ ≤ (ζ^16) n` for `n ≠ 0`.  Both sides are multiplicative; on prime powers this
is `(m+1)⁴ ≤ C(m+3,3)² ≤ C(m+15,15)`. -/
private lemma tau_fourth_le_zetaPow_sixteen {n : ℕ} (hn : n ≠ 0) : σ 0 n ^ 4 ≤ (ζ ^ 16) n := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn,
    (isMultiplicative_zeta.pow (k := 16)).multiplicative_factorization _ hn]
  rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
  refine Finset.prod_le_prod' fun q hq => ?_
  have hq' : q.Prime := Nat.prime_of_mem_primeFactors (by
    rwa [Nat.support_factorization] at hq)
  rw [sigma_zero_apply_prime_pow hq']
  have h16 : (ζ ^ 16) (q ^ n.factorization q) = (n.factorization q + 15).choose 15 :=
    zetaPow_apply_prime_pow 15 hq' _
  rw [h16]
  calc (n.factorization q + 1) ^ 4 = ((n.factorization q + 1) ^ 2) ^ 2 := by ring
    _ ≤ ((n.factorization q + 3).choose 3) ^ 2 :=
        Nat.pow_le_pow_left (succ_sq_le_choose _) 2
    _ ≤ (n.factorization q + 15).choose 15 := choose_three_sq_le_choose_fifteen _

/-- **Shiu-type short-interval bound for `τ⁴`, sharp log exponent `15 = 2⁴ − 1`.**

For `x ≥ 1` and `x^{15/16} ≤ y ≤ x`,
`∑_{x < n ≤ x+y} τ(n)⁴ ≤ 2097152 · y · (1 + log x)^15`.

Same max-coordinate / divisor-splitting argument as `maxCoord_tau_sq_short_interval`, now split at
sixteen coordinates; the log exponent `15` is sharp. -/
theorem maxCoord_tau_fourth_short_interval {x y : ℕ} (hx : 0 < x)
    (hy : (x : ℝ) ^ (15 / 16 : ℝ) ≤ (y : ℝ)) (hyx : y ≤ x) :
    ∑ n ∈ Finset.Ioc x (x + y), ((σ 0 n : ℕ) : ℝ) ^ 4
      ≤ 2097152 * (y : ℝ) * (1 + Real.log x) ^ 15 := by
  have hx0R : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hy0R : (0 : ℝ) ≤ (y : ℝ) := by positivity
  -- the sixteenth-root threshold `t`
  obtain ⟨t, ht0, htA, htB⟩ := exists_root_threshold hx 4
  norm_num at htA htB
  have htbig : x < 65536 * t ^ 16 := by
    have h3 : t + 1 ≤ 2 * t := by omega
    have h4 : (t + 1) ^ 16 ≤ (2 * t) ^ 16 := Nat.pow_le_pow_left h3 16
    have h5 : (2 * t) ^ 16 = 65536 * t ^ 16 := by ring
    omega
  -- `y^16 ≥ x^15`, from the hypothesis `y ≥ x^{15/16}`
  have hxy16 : x ^ 15 ≤ y ^ 16 := by
    have h34 : ((x : ℝ) ^ (15 / 16 : ℝ)) ^ (16 : ℕ) = (x : ℝ) ^ (15 : ℕ) := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ (15 / 16 : ℝ)) 16, ← Real.rpow_mul hx0R.le]
      norm_num
    have hR : (x : ℝ) ^ (15 : ℕ) ≤ (y : ℝ) ^ (16 : ℕ) := by
      rw [← h34]
      exact pow_le_pow_left₀ (by positivity) hy 16
    exact_mod_cast hR
  have hkey : 2 * x ≤ 4 * y * t := by
    have hpow : (2 * x) ^ 16 ≤ (4 * y * t) ^ 16 := by
      calc (2 * x) ^ 16 = 65536 * (x ^ 15 * x) := by ring
        _ ≤ 65536 * (y ^ 16 * (65536 * t ^ 16)) :=
            Nat.mul_le_mul_left 65536 (Nat.mul_le_mul hxy16 (le_of_lt htbig))
        _ = (4 * y * t) ^ 16 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hpow
  set M := (x + y) / t with hM_def
  obtain ⟨hMy, hlogMx⟩ := maxCoord_setup hx hyx ht0 hM_def hkey
  -- the split, cast to `ℝ`, and the ladder
  have hNat : ∑ n ∈ Finset.Ioc x (x + y), σ 0 n ^ 4
      ≤ 16 * ∑ m ∈ Finset.Ioc 0 M, (ζ ^ 15) m * ((x + y) / m - x / m) := by
    have h := maxCoord_split_sum (k := 15) (t := t) (M := M) ht0 (by simpa using htA) hM_def
      (fun n => σ 0 n ^ 4) (fun n hn => by simpa using tau_fourth_le_zetaPow_sixteen hn)
    simpa using h
  have hcast : ∑ n ∈ Finset.Ioc x (x + y), ((σ 0 n : ℕ) : ℝ) ^ 4
      ≤ 16 * ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ 15) m : ℝ) * (((x + y) / m - x / m : ℕ) : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hNat
    push_cast at h
    exact h
  have hlad : ∑ m ∈ Finset.Ioc 0 M, ((ζ ^ 15) m : ℝ) * (((x + y) / m - x / m : ℕ) : ℝ)
      ≤ (y : ℝ) * (1 + Real.log M) ^ 15 + (M : ℝ) * (1 + Real.log M) ^ 14 := by
    simpa using maxCoord_ladder_bound x y M 14
  -- numerics
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_natCast_nonneg x
  have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_natCast_nonneg M
  have hL0 : (0 : ℝ) ≤ 1 + Real.log M := by linarith
  have hLx1 : (1 : ℝ) ≤ 1 + Real.log x := by linarith
  have h15 : (1 + Real.log M) ^ 15 ≤ 32768 * (1 + Real.log x) ^ 15 := by
    calc (1 + Real.log M) ^ 15 ≤ (2 * (1 + Real.log x)) ^ 15 := pow_le_pow_left₀ hL0 hlogMx 15
      _ = 32768 * (1 + Real.log x) ^ 15 := by ring
  have h14 : (1 + Real.log M) ^ 14 ≤ 16384 * (1 + Real.log x) ^ 15 := by
    have e2 : (1 + Real.log x) ^ 14 ≤ (1 + Real.log x) ^ 15 :=
      pow_le_pow_right₀ hLx1 (by norm_num)
    calc (1 + Real.log M) ^ 14 ≤ (2 * (1 + Real.log x)) ^ 14 := pow_le_pow_left₀ hL0 hlogMx 14
      _ = 16384 * (1 + Real.log x) ^ 14 := by ring
      _ ≤ 16384 * (1 + Real.log x) ^ 15 := by linarith
  have t1 : (y : ℝ) * (1 + Real.log M) ^ 15 ≤ (y : ℝ) * (32768 * (1 + Real.log x) ^ 15) :=
    mul_le_mul_of_nonneg_left h15 hy0R
  have t2 : (M : ℝ) * (1 + Real.log M) ^ 14
      ≤ (4 * (y : ℝ)) * (16384 * (1 + Real.log x) ^ 15) := by
    calc (M : ℝ) * (1 + Real.log M) ^ 14 ≤ (4 * (y : ℝ)) * (1 + Real.log M) ^ 14 :=
          mul_le_mul_of_nonneg_right hMy (by positivity)
      _ ≤ (4 * (y : ℝ)) * (16384 * (1 + Real.log x) ^ 15) :=
          mul_le_mul_of_nonneg_left h14 (by linarith)
  have hnn : (0 : ℝ) ≤ (y : ℝ) * (1 + Real.log x) ^ 15 :=
    mul_nonneg hy0R (pow_nonneg (by linarith) 15)
  refine le_trans hcast ?_
  linarith

end Shiu
end Zeta85
end RH

#print axioms RH.Zeta85.Shiu.maxCoord_tau_sq_short_interval
#print axioms RH.Zeta85.Shiu.maxCoord_tau_fourth_short_interval
