/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Shiu/ProgressionCount.lean — residue-class counting for the Shiu majorant campaign.

The campaign's clean home for counting an arithmetic progression inside an initial segment:

* `progCount_le` / `progCount_ge` / `progCount_le_two_div` — the count of
  `{n ∈ [1, N] : n ≡ r (mod q)}` is `N/q + O(1)`, with the `O(1)` explicit in both directions
  and a `2N/q` form valid once `q ≤ N`.  ℕ-exact forms (`Nat` division, no error term) are
  provided as `progCount_le_nat` / `progCount_ge_nat`.
* `progCount_totient` — the `φ`-form on the repo's window `[1, ⌈2P⌉]`: the class has at most
  `4·P/φ(q)` elements once `1 ≤ P` and `q ≤ P` (constant `4`, via
  `⌈2P⌉/q + 1 ≤ (2P+1+q)/q ≤ 4P/q ≤ 4P/φ(q)`).
* `progCount_coprime_partition` — the coprime integers of `[1, N]` partition by residue class.
* the `progressionSum` interface every majorant route consumes: monotonicity, subadditivity,
  scaling, nonnegativity, and the keystone reduction `progressionSum_le_of_divisorBounded`
  sending an arbitrary divisor-bounded family to a `τ^k` sum over the class
  (elementary; cf. Shiu 1980 §2 reduction).

Everything below is unconditional and elementary: the counts are proved by the explicit
div/mod bijection `n ↦ n / q` (upper bound) and `t ↦ q·t + b`, `b ≡ r (mod q)`, `1 ≤ b ≤ q`
(lower bound) — no appeal to any campaign hypothesis.
-/
import RH.Zeta85.Arith

open scoped BigOperators

namespace RH
namespace Zeta85
namespace Shiu

/-! ## 1. Counting a residue class in an initial segment

The class `{n ∈ [1, N] : n ≡ r (mod q)}` has `N/q + O(1)` elements.  We record ℕ-exact
one-sided bounds first (`Nat` division, no error term), then the real forms. -/

/-- ℕ-exact upper bound: `#{n ∈ [1, N] : n ≡ r (mod q)} ≤ N/q + 1` (`Nat` division).
Holds for every `q`, including `q = 0` (where the class is the single point `r`).
Proof: `n ↦ n / q` is injective on the class, with values `< N/q + 1`. -/
lemma progCount_le_nat (q r N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card ≤ N / q + 1 := by
  have h : ((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card
      ≤ (Finset.range (N / q + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => n / q) ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
      simp only [Finset.mem_coe, Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2)
    · intro n hn m hm hnm
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn hm
      have hd : n / q = m / q := hnm
      have hmod : n % q = m % q := by rw [hn.2, hm.2]
      calc n = q * (n / q) + n % q := (Nat.div_add_mod n q).symm
        _ = q * (m / q) + m % q := by rw [hd, hmod]
        _ = m := Nat.div_add_mod m q
  simpa using h

/-- The injection step of the lower bound, for a representative `b` of the class with
`1 ≤ b ≤ q`: the map `t ↦ q·t + b` sends `{0, …, N/q − 1}` into the class in `[1, N]`. -/
private lemma progCount_ge_aux {q b : ℕ} (hq : 0 < q) (hb1 : 1 ≤ b) (hbq : b ≤ q)
    {r : ℕ} (hbmod : b % q = r % q) (N : ℕ) :
    N / q ≤ ((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card := by
  have h : (Finset.range (N / q)).card
      ≤ ((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card := by
    refine Finset.card_le_card_of_injOn (fun t => q * t + b) ?_ ?_
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_range] at ht
      have hqN : q * (N / q) ≤ N := Nat.le.intro (Nat.div_add_mod N q)
      have hmul : q * (t + 1) ≤ q * (N / q) := Nat.mul_le_mul le_rfl ht
      have hexp : q * (t + 1) = q * t + q := by ring
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.mul_add_mod, hbmod]
    · intro t ht t' ht' hEq
      have h' : q * t + b = q * t' + b := hEq
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel h')
  simpa using h

/-- ℕ-exact lower bound: `N/q ≤ #{n ∈ [1, N] : n ≡ r (mod q)}` (`Nat` division), for `0 < q`.
Proof: `t ↦ q·t + b` with `b` the representative of `r`'s class in `[1, q]` injects
`{0, …, N/q − 1}` into the class. -/
lemma progCount_ge_nat {q : ℕ} (hq : 0 < q) (r N : ℕ) :
    N / q ≤ ((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card := by
  rcases Nat.eq_zero_or_pos (r % q) with h0 | h0
  · refine progCount_ge_aux hq hq le_rfl ?_ N
    rw [Nat.mod_self, h0]
  · exact progCount_ge_aux hq h0 (Nat.mod_lt r hq).le
      (Nat.mod_eq_of_lt (Nat.mod_lt r hq)) N

/-- **Initial-segment upper count.**  `#{n ∈ [1, N] : n ≡ r (mod q)} ≤ N/q + 1`, real
division.  Stated without a positivity hypothesis on `q`: for `q = 0` the class is a single
point and the right side is `1`. -/
lemma progCount_le (q r N : ℕ) :
    (((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card : ℝ) ≤ (N : ℝ) / q + 1 := by
  have h : (((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card : ℝ)
      ≤ ((N / q + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (progCount_le_nat q r N)
  have h2 : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / (q : ℝ) := Nat.cast_div_le
  push_cast at h
  linarith

/-- **Initial-segment lower count.**  `N/q − 1 ≤ #{n ∈ [1, N] : n ≡ r (mod q)}`, real
division, for `0 < q`. -/
lemma progCount_ge {q : ℕ} (hq : 0 < q) (r N : ℕ) :
    (N : ℝ) / q - 1 ≤ (((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard : ((N / q : ℕ) : ℝ)
      ≤ (((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card : ℝ) :=
    Nat.cast_le.mpr (progCount_ge_nat hq r N)
  have hkey : (N : ℝ) / q < ((N / q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hqR]
    have h1 : N < q * (N / q + 1) := by
      have h2 := Nat.div_add_mod N q
      have h3 : N % q < q := Nat.mod_lt N hq
      have h4 : q * (N / q + 1) = q * (N / q) + q := by ring
      omega
    calc (N : ℝ) < ((q * (N / q + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (((N / q : ℕ) : ℝ) + 1) * q := by push_cast; ring
  linarith

/-- **Two-over-`q` form.**  Once `q ≤ N`, the additive `+1` can be absorbed:
`#{n ∈ [1, N] : n ≡ r (mod q)} ≤ 2N/q`. -/
lemma progCount_le_two_div {q : ℕ} (hq : 0 < q) (r : ℕ) {N : ℕ} (hqN : (q : ℝ) ≤ (N : ℝ)) :
    (((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card : ℝ) ≤ 2 * N / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : (1 : ℝ) ≤ (N : ℝ) / q := (one_le_div₀ hqR).mpr hqN
  have h := progCount_le q r N
  have h2 : 2 * (N : ℝ) / q = (N : ℝ) / q + (N : ℝ) / q := by ring
  linarith

/-! ## 2. The `φ`-form on the repo's window -/

/-- **`φ`-form for the window `[1, ⌈2P⌉]`** (constant `4`): for `0 < q`, `1 ≤ P`, `q ≤ P`,

  `#{n ∈ [1, ⌈2P⌉] : n ≡ r (mod q)} ≤ 4·P/φ(q)`.

Route: `card ≤ ⌈2P⌉/q + 1 ≤ (2P + 1 + q)/q ≤ 4P/q ≤ 4P/φ(q)`, using `⌈2P⌉ < 2P + 1`,
`1 ≤ P`, `q ≤ P`, and `φ(q) ≤ q` (`Nat.totient_le`).  This is the crude count feeding the
`q ≤ P^{1−η}` regime of the corrected Shiu interface; no coprimality of `r` is needed. -/
lemma progCount_totient {q : ℕ} (hq : 0 < q) (r : ℕ) {P : ℝ} (hP : 1 ≤ P)
    (hqP : (q : ℝ) ≤ P) :
    (((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun n => n % q = r % q)).card : ℝ)
      ≤ 4 * P / (Nat.totient q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htotpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have htotle : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hceil : (⌈2 * P⌉₊ : ℝ) ≤ 2 * P + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have h0 := progCount_le q r ⌈2 * P⌉₊
  have h1 : (⌈2 * P⌉₊ : ℝ) / q ≤ (2 * P + 1) / q :=
    div_le_div_of_nonneg_right hceil hqR.le
  have h2 : (2 * P + 1 + q) / q = (2 * P + 1) / q + 1 := by
    rw [add_div, div_self (ne_of_gt hqR)]
  have h3 : (2 * P + 1 + q) / q ≤ 4 * P / q :=
    div_le_div_of_nonneg_right (by linarith) hqR.le
  have h4 : 4 * P / q ≤ 4 * P / (Nat.totient q : ℝ) :=
    div_le_div_of_nonneg_left (by linarith) htotpos htotle
  linarith

/-! ## 3. Partition of the coprime classes -/

/-- Coprimality only depends on the residue: `gcd(n mod q, q) = gcd(n, q)`. -/
private lemma coprime_mod_left {n q : ℕ} : Nat.Coprime (n % q) q ↔ Nat.Coprime n q := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]

/-- **Coprime-class partition.**  The integers of `[1, N]` coprime to `q` partition by
residue class mod `q`:

  `#{n ∈ [1, N] : (n, q) = 1} = Σ_{r < q, (r,q)=1} #{n ∈ [1, N] : n ≡ r (mod q)}`.

This is the identity behind every reduction of a coprime-restricted sum to per-class
counts (elementary; cf. Shiu 1980 §2 reduction). -/
lemma progCount_coprime_partition {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n q)).card
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          ((Finset.Icc 1 N).filter (fun n => n % q = r)).card := by
  classical
  have hmaps : Set.MapsTo (fun n => n % q)
      ↑((Finset.Icc 1 N).filter (fun n => Nat.Coprime n q))
      ↑((Finset.range q).filter (fun r => Nat.Coprime r q)) := by
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hn ⊢
    exact ⟨Nat.mod_lt n hq, coprime_mod_left.mpr hn.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hr
  congr 1
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun n _ => ?_
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    refine coprime_mod_left.mp ?_
    rw [h]
    exact hr.2

/-! ## 4. The `progressionSum` interface

`progressionSum c P q r = Σ_{p ∈ [1, ⌈2P⌉], p ≡ r (q)} |c p|` is the object the Shiu-type
majorant bounds.  The four structural lemmas below, plus the divisor-bounded reduction,
are the complete bridge from an arbitrary coefficient family to the counting section
above. -/

/-- `progressionSum` is monotone under pointwise domination of absolute values. -/
theorem progressionSum_mono {c c' : ℕ → ℝ} (h : ∀ n, |c n| ≤ |c' n|) (P : ℝ) (q r : ℕ) :
    progressionSum c P q r ≤ progressionSum c' P q r := by
  unfold progressionSum
  exact Finset.sum_le_sum fun p _ => h p

/-- `progressionSum` is subadditive in the coefficient family. -/
theorem progressionSum_add_le (c c' : ℕ → ℝ) (P : ℝ) (q r : ℕ) :
    progressionSum (fun n => c n + c' n) P q r
      ≤ progressionSum c P q r + progressionSum c' P q r := by
  unfold progressionSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun p _ => abs_add_le _ _

/-- `progressionSum` scales by `|a|` under `c ↦ a·c`. -/
theorem progressionSum_smul (a : ℝ) (c : ℕ → ℝ) (P : ℝ) (q r : ℕ) :
    progressionSum (fun n => a * c n) P q r = |a| * progressionSum c P q r := by
  unfold progressionSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => abs_mul a (c p)

/-- `progressionSum` is nonnegative. -/
theorem progressionSum_nonneg (c : ℕ → ℝ) (P : ℝ) (q r : ℕ) :
    0 ≤ progressionSum c P q r := by
  unfold progressionSum
  exact Finset.sum_nonneg fun p _ => abs_nonneg _

/-- **Reduction to the `τ^k` class sum** (keystone).  A `DivisorBounded` family reduces,
uniformly over the class, to the divisor-power sum:

  `Σ_{p ≡ r (q), p ≤ ⌈2P⌉} |c p| ≤ Kc · Σ_{p ≡ r (q), p ≤ ⌈2P⌉} τ(p)^k`.

Every route to the corrected Shiu interface factors through this and then bounds the
right side (elementary; cf. Shiu 1980 §2 reduction).  No sign condition on `Kc` is
needed: the pointwise bound `|c p| ≤ Kc·τ(p)^k` is summed as-is. -/
theorem progressionSum_le_of_divisorBounded {c : ℕ → ℝ} {Kc : ℝ} {k : ℕ}
    (hc : DivisorBounded c Kc k) (P : ℝ) (q r : ℕ) :
    progressionSum c P q r
      ≤ Kc * ∑ p ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q),
          ((ArithmeticFunction.sigma 0 p : ℕ) : ℝ) ^ k := by
  unfold progressionSum
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ => hc p

/-- **`k = 0` corollary: reduction to the class count.**  `DivisorBounded c Kc 0` says
literally `|c n| ≤ Kc · τ(n)^0 = Kc` for every `n` — including `n = 0`, where
`τ(0) = 0` but `τ(0)^0 = 1`, so the hypothesis is an honest uniform bound and no
positivity of the class members is needed. -/
theorem progressionSum_le_card_mul {c : ℕ → ℝ} {Kc : ℝ} (hc : DivisorBounded c Kc 0)
    (P : ℝ) (q r : ℕ) :
    progressionSum c P q r
      ≤ Kc * (((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q)).card : ℝ) := by
  have hb : ∀ n : ℕ, |c n| ≤ Kc := fun n => by simpa using hc n
  unfold progressionSum
  calc ∑ p ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q), |c p|
      ≤ ∑ _p ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q), Kc :=
        Finset.sum_le_sum fun p _ => hb p
    _ = (((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q)).card : ℝ) * Kc := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = Kc * (((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q)).card : ℝ) :=
        mul_comm _ _

/-- **Demonstration corollary**: for a `k = 0` (uniformly bounded) family with `Kc ≥ 0`,
the full `φ`-form of the majorant already holds unconditionally, with constant `4` and
no logarithm: `progressionSum c P q r ≤ Kc · (4·P/φ(q))` for `0 < q ≤ P`, `1 ≤ P`. -/
theorem progressionSum_le_totient {c : ℕ → ℝ} {Kc : ℝ} (hc : DivisorBounded c Kc 0)
    (hKc : 0 ≤ Kc) {q : ℕ} (hq : 0 < q) (r : ℕ) {P : ℝ} (hP : 1 ≤ P)
    (hqP : (q : ℝ) ≤ P) :
    progressionSum c P q r ≤ Kc * (4 * P / (Nat.totient q : ℝ)) :=
  le_trans (progressionSum_le_card_mul hc P q r)
    (mul_le_mul_of_nonneg_left (progCount_totient hq r hP hqP) hKc)

/-! ## Axiom audit -/

#print axioms progCount_le
#print axioms progCount_ge
#print axioms progCount_le_two_div
#print axioms progCount_totient
#print axioms progCount_coprime_partition
#print axioms progressionSum_mono
#print axioms progressionSum_add_le
#print axioms progressionSum_smul
#print axioms progressionSum_nonneg
#print axioms progressionSum_le_of_divisorBounded
#print axioms progressionSum_le_card_mul
#print axioms progressionSum_le_totient

end Shiu
end Zeta85
end RH
