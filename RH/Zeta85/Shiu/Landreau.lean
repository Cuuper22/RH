/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The Landreau/Lay small-divisor inequality

This file proves an explicit form of **Landreau's inequality** for the divisor function
`τ = ArithmeticFunction.sigma 0` (so `τ n = n.divisors.card`):

* B. Landreau, *Majorations de fonctions arithmétiques en moyenne sur des ensembles de
  faible densité*, Bull. Soc. Math. France **117** (1989), 1–12;
* explicit version: N. Lay, arXiv:1711.05924.

The inequality converts the pointwise value `τ n` into a sum over the **small** divisors
`d ∣ n` with `d ^ 4 ≤ n` (i.e. `d ≤ n ^ (1/4)`), which is what makes short-interval sums
of `τ`-powers interchange-friendly in Shiu-type majorant arguments.

## Main results

* `landreau_exists_small_divisor`: for `n ≥ 1` there is a single divisor `d ∣ n` with
  `d ^ 4 ≤ n` and `τ n ≤ 8 * τ d ^ 7` (max-block form, Lay's constants `(A, B) = (8, 7)`);
* `landreau_tau_le`: `τ n ≤ 8 * ∑_{d ∣ n, d ^ 4 ≤ n} τ d ^ 7`;
* `landreau_tau_pow_four_le`: `τ n ^ 4 ≤ 4096 * ∑_{d ∣ n, d ^ 4 ≤ n} τ d ^ 28`
  (the form consumed downstream; `4096 = 8 ^ 4`, `28 = 4 * 7`).

In the two summed forms the small-divisor condition is spelled over `ℝ` as
`(d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)`, the clean rendering of `d ≤ n ^ (1/4)`; it is equivalent
to the `ℕ` inequality `d ^ 4 ≤ n` by `Nat.cast_le`.

## Proof sketch

Write `n = m * h`, where `h` collects the prime powers `p ^ a ∥ n` whose base is *huge*
(`p ^ 4 > n`) and `m` is the remaining smooth part.

* Since `h ∣ n` and every prime factor of `h` exceeds `n ^ (1/4)`, at most three prime
  factors of `h` (counted with multiplicity) fit below `n`; hence
  `τ h ≤ ∏ (a_p + 1) ≤ 2 ^ Ω(h) ≤ 2 ^ 3 = 8`.
* For the smooth part, a greedy block decomposition applies: peel primes off the current
  piece one at a time; the first time the remaining part `r` satisfies `r ^ 4 ≤ n`, the
  last peeled prime `p` and `r` form **two** legal blocks (`p ^ 4 ≤ n`, `r ^ 4 ≤ n`)
  whose *product* is large (`(p * r) ^ 4 > n`).  Each such extraction removes a factor
  `> n ^ (1/4)` from `m ≤ n`, so at most `3` extractions occur before the remainder is
  itself a legal block: `m` is a product of at most `2 * 3 + 1 = 7` divisors `D` with
  `D ^ 4 ≤ n`.
* Submultiplicativity of `τ` (`Nat.divisors_mul` + `Finset.card_mul_le`) and replacing
  every block by the block `d` with the largest `τ`-value give `τ m ≤ τ d ^ 7`, whence
  `τ n ≤ τ h * τ m ≤ 8 * τ d ^ 7`.  The summed forms follow by dominating the single
  term `τ d ^ B` by the full (nonnegative) sum over small divisors.
-/

namespace RH
namespace Zeta85
namespace Shiu

/-- Submultiplicativity of the divisor-counting function, `τ (a * b) ≤ τ a * τ b`,
via `Nat.divisors_mul` and `Finset.card_mul_le`. -/
private lemma landreau_card_divisors_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

/-- Iterated submultiplicativity of `τ` over a finite product. -/
private lemma landreau_card_divisors_prod_le (s : Finset ℕ) (f : ℕ → ℕ) :
    (∏ p ∈ s, f p).divisors.card ≤ ∏ p ∈ s, (f p).divisors.card := by
  induction s using Finset.cons_induction with
  | empty => simp [Nat.divisors_one]
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    exact (landreau_card_divisors_mul_le _ _).trans (Nat.mul_le_mul le_rfl ih)

/-- **Greedy pair extraction.**  If every prime factor of `m` is small (`p ^ 4 ≤ n`) but
`m` itself is large (`n < m ^ 4`), then `m = D₁ * D₂ * m'` where the two blocks
`D₁, D₂` are individually legal (`Dᵢ ^ 4 ≤ n`) and jointly large (`n < (D₁ * D₂) ^ 4`).

Proof: peel the least prime factor off `m` repeatedly (fuel `k` bounds the recursion);
the first time the remaining part `r` satisfies `r ^ 4 ≤ n`, the last peeled prime and
`r` are the two blocks. -/
private lemma landreau_extract (n : ℕ) (hn : 1 ≤ n) :
    ∀ k m, m ≤ k → (∀ p : ℕ, p.Prime → p ∣ m → p ^ 4 ≤ n) → n < m ^ 4 →
      ∃ D₁ D₂ m', m = D₁ * D₂ * m' ∧ D₁ ^ 4 ≤ n ∧ D₂ ^ 4 ≤ n ∧ n < (D₁ * D₂) ^ 4 := by
  intro k
  induction k with
  | zero =>
    intro m hm _ hbig
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    rw [show (0 : ℕ) ^ 4 = 0 from by norm_num] at hbig
    exact absurd hbig (Nat.not_lt_zero n)
  | succ k ih =>
    intro m hmk hprimes hbig
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [show (0 : ℕ) ^ 4 = 0 from by norm_num] at hbig
      exact absurd hbig (Nat.not_lt_zero n)
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [one_pow] at hbig
      omega
    have hp : m.minFac.Prime := Nat.minFac_prime hm1
    have hpd : m.minFac ∣ m := Nat.minFac_dvd m
    have hm_eq : m = m.minFac * (m / m.minFac) := (Nat.mul_div_cancel' hpd).symm
    have hlt : m / m.minFac < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hp.one_lt
    have hdvd_m : m / m.minFac ∣ m := ⟨m.minFac, (Nat.div_mul_cancel hpd).symm⟩
    have hprimes' : ∀ q : ℕ, q.Prime → q ∣ m / m.minFac → q ^ 4 ≤ n := fun q hq hqd =>
      hprimes q hq (hqd.trans hdvd_m)
    by_cases hcase : n < (m / m.minFac) ^ 4
    · obtain ⟨D₁, D₂, m'', h_eq, h1, h2, h3⟩ :=
        ih (m / m.minFac) (by omega) hprimes' hcase
      refine ⟨D₁, D₂, m.minFac * m'', ?_, h1, h2, h3⟩
      calc m = m.minFac * (m / m.minFac) := hm_eq
        _ = m.minFac * (D₁ * D₂ * m'') := by rw [h_eq]
        _ = D₁ * D₂ * (m.minFac * m'') := by ring
    · refine ⟨m.minFac, m / m.minFac, 1, by rw [mul_one]; exact hm_eq,
        hprimes m.minFac hp hpd, Nat.not_lt.mp hcase, ?_⟩
      rw [← hm_eq]
      exact hbig

/-- **Block decomposition, max form.**  If every prime factor of `m` satisfies
`p ^ 4 ≤ n` and `m ^ 4 ≤ n ^ (t + 1)`, then a single divisor `d ∣ m` with `d ^ 4 ≤ n`
controls `τ m`: `τ m ≤ τ d ^ (2 * t + 1)`.

Each `landreau_extract` round removes two blocks whose product exceeds `n ^ (1/4)`,
dropping the size exponent `t` by one, so at most `2 * t + 1` blocks appear in total. -/
private lemma landreau_smooth (n : ℕ) (hn : 1 ≤ n) :
    ∀ t m, (∀ p : ℕ, p.Prime → p ∣ m → p ^ 4 ≤ n) → m ^ 4 ≤ n ^ (t + 1) →
      ∃ d, d ∣ m ∧ d ^ 4 ≤ n ∧ m.divisors.card ≤ d.divisors.card ^ (2 * t + 1) := by
  intro t
  induction t with
  | zero =>
    intro m _ hsize
    rw [pow_one] at hsize
    exact ⟨m, dvd_rfl, hsize, Nat.le_self_pow (by omega) _⟩
  | succ t ih =>
    intro m hprimes hsize
    by_cases hbig : n < m ^ 4
    · obtain ⟨D₁, D₂, m', hm_eq, hD₁, hD₂, hDD⟩ :=
        landreau_extract n hn m m le_rfl hprimes hbig
      -- size bound for the remainder `m'`: cancel one factor of `n`
      have e1 : (D₁ * D₂) ^ 4 * m' ^ 4 = m ^ 4 := by rw [hm_eq]; ring
      have h2 : (n + 1) * m' ^ 4 ≤ m ^ 4 := by
        rw [← e1]
        exact Nat.mul_le_mul (Nat.succ_le_of_lt hDD) le_rfl
      have h3 : (n + 1) * m' ^ 4 ≤ (n + 1) * n ^ (t + 1) := by
        calc (n + 1) * m' ^ 4 ≤ m ^ 4 := h2
          _ ≤ n ^ (t + 1 + 1) := hsize
          _ = n ^ (t + 1) * n := by ring
          _ ≤ (n + 1) * n ^ (t + 1) := by
              rw [mul_comm (n ^ (t + 1)) n]
              exact Nat.mul_le_mul (Nat.le_succ n) le_rfl
      have hm'_size : m' ^ 4 ≤ n ^ (t + 1) :=
        Nat.le_of_mul_le_mul_left h3 (by omega)
      have hm'_dvd : m' ∣ m := ⟨D₁ * D₂, by rw [hm_eq]; ring⟩
      have hprimes' : ∀ q : ℕ, q.Prime → q ∣ m' → q ^ 4 ≤ n := fun q hq hqd =>
        hprimes q hq (hqd.trans hm'_dvd)
      obtain ⟨d', hd'm', hd'4, hτ'⟩ := ih m' hprimes' hm'_size
      have hD₁m : D₁ ∣ m := ⟨D₂ * m', by rw [hm_eq]; ring⟩
      have hD₂m : D₂ ∣ m := ⟨D₁ * m', by rw [hm_eq]; ring⟩
      have hd'm : d' ∣ m := hd'm'.trans hm'_dvd
      -- the block with the largest τ-value dominates all three
      obtain ⟨e, hem, he4, hb1, hb2, hb3⟩ :
          ∃ e, e ∣ m ∧ e ^ 4 ≤ n ∧ D₁.divisors.card ≤ e.divisors.card ∧
            D₂.divisors.card ≤ e.divisors.card ∧ d'.divisors.card ≤ e.divisors.card := by
        rcases le_total D₁.divisors.card D₂.divisors.card with h12 | h12
        · rcases le_total D₂.divisors.card d'.divisors.card with h23 | h23
          · exact ⟨d', hd'm, hd'4, h12.trans h23, h23, le_rfl⟩
          · exact ⟨D₂, hD₂m, hD₂, h12, le_rfl, h23⟩
        · rcases le_total D₁.divisors.card d'.divisors.card with h13 | h13
          · exact ⟨d', hd'm, hd'4, h13, h12.trans h13, le_rfl⟩
          · exact ⟨D₁, hD₁m, hD₁, le_rfl, h12, h13⟩
      refine ⟨e, hem, he4, ?_⟩
      calc m.divisors.card
          = (D₁ * D₂ * m').divisors.card := by rw [← hm_eq]
        _ ≤ (D₁ * D₂).divisors.card * m'.divisors.card :=
            landreau_card_divisors_mul_le _ _
        _ ≤ D₁.divisors.card * D₂.divisors.card * m'.divisors.card :=
            Nat.mul_le_mul (landreau_card_divisors_mul_le _ _) le_rfl
        _ ≤ e.divisors.card * e.divisors.card * e.divisors.card ^ (2 * t + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul hb1 hb2)
              (hτ'.trans (Nat.pow_le_pow_left hb3 _))
        _ = e.divisors.card ^ (2 * (t + 1) + 1) := by ring
    · exact ⟨m, dvd_rfl, Nat.not_lt.mp hbig, Nat.le_self_pow (by omega) _⟩

/-- **Peeling the huge primes.**  Every `n ≥ 1` factors as `n = m * h` where all prime
factors of `m` are small (`p ^ 4 ≤ n`) and the huge-prime part `h` satisfies `τ h ≤ 8`:
at most three huge prime factors, counted with multiplicity, fit below `n`. -/
private lemma landreau_peel (n : ℕ) (hn : 1 ≤ n) :
    ∃ m h : ℕ, n = m * h ∧ (∀ p : ℕ, p.Prime → p ∣ m → p ^ 4 ≤ n) ∧
      h.divisors.card ≤ 8 := by
  have hn0 : n ≠ 0 := by omega
  set S : Finset ℕ := n.primeFactors.filter (fun p => ¬ p ^ 4 ≤ n) with hS_def
  set h : ℕ := ∏ p ∈ S, p ^ n.factorization p with hh_def
  set m : ℕ := ∏ p ∈ n.primeFactors.filter (fun p => p ^ 4 ≤ n), p ^ n.factorization p
    with hm_def
  have hprod : m * h = n := by
    rw [hm_def, hh_def, hS_def,
      Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ^ 4 ≤ n)]
    exact (Nat.prod_primeFactors_pow_factorization hn0).symm
  have hh_dvd : h ∣ n := ⟨m, by rw [← hprod]; ring⟩
  have hh_le : h ≤ n := Nat.le_of_dvd (by omega) hh_dvd
  -- the huge part has at most `3` prime factors with multiplicity
  have hpow : (n + 1) ^ (∑ p ∈ S, n.factorization p) ≤ h ^ 4 := by
    calc (n + 1) ^ (∑ p ∈ S, n.factorization p)
        = ∏ p ∈ S, (n + 1) ^ n.factorization p :=
          (Finset.prod_pow_eq_pow_sum S _ _).symm
      _ ≤ ∏ p ∈ S, (p ^ 4) ^ n.factorization p := by
          apply Finset.prod_le_prod'
          intro p hp
          have hlarge : n < p ^ 4 := Nat.not_le.mp (Finset.mem_filter.mp hp).2
          exact Nat.pow_le_pow_left (Nat.succ_le_of_lt hlarge) _
      _ = ∏ p ∈ S, (p ^ n.factorization p) ^ 4 :=
          Finset.prod_congr rfl fun p _ => pow_right_comm p 4 (n.factorization p)
      _ = h ^ 4 := by rw [hh_def]; exact Finset.prod_pow S 4 _
  have hΩ : (∑ p ∈ S, n.factorization p) ≤ 3 := by
    by_contra hc
    have hc' : 4 ≤ ∑ p ∈ S, n.factorization p := Nat.not_le.mp hc
    have h1 : (n + 1) ^ 4 ≤ (n + 1) ^ (∑ p ∈ S, n.factorization p) :=
      Nat.pow_le_pow_right (by omega) hc'
    have h2 : h ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left hh_le 4
    have h3 : n ^ 4 < (n + 1) ^ 4 := Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by norm_num)
    exact absurd ((h1.trans hpow).trans h2) (Nat.not_le.mpr h3)
  have hτh : h.divisors.card ≤ 8 := by
    calc h.divisors.card
        ≤ ∏ p ∈ S, (p ^ n.factorization p).divisors.card := by
          rw [hh_def]; exact landreau_card_divisors_prod_le S _
      _ ≤ ∏ p ∈ S, 2 ^ n.factorization p := by
          apply Finset.prod_le_prod'
          intro p hp
          have hp_prime : p.Prime :=
            Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
          have hcard : (p ^ n.factorization p).divisors.card = n.factorization p + 1 := by
            have hσ := ArithmeticFunction.sigma_zero_apply_prime_pow
              (p := p) (i := n.factorization p) hp_prime
            rwa [ArithmeticFunction.sigma_zero_apply] at hσ
          rw [hcard]
          exact Nat.lt_two_pow_self
      _ = 2 ^ (∑ p ∈ S, n.factorization p) := Finset.prod_pow_eq_pow_sum S _ _
      _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) hΩ
      _ = 8 := by norm_num
  have hm_primes : ∀ p : ℕ, p.Prime → p ∣ m → p ^ 4 ≤ n := by
    intro p hp hpd
    rw [hm_def] at hpd
    obtain ⟨q, hq_mem, hpq⟩ := hp.prime.exists_mem_finset_dvd hpd
    have hq_filter := Finset.mem_filter.mp hq_mem
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_filter.1
    have hpq_eq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (hp.dvd_of_dvd_pow hpq)
    rw [hpq_eq]
    exact hq_filter.2
  exact ⟨m, h, hprod.symm, hm_primes, hτh⟩

/-- **Landreau's inequality, max-block form** (explicit constants of Lay,
arXiv:1711.05924; original: Landreau, BSMF **117** (1989)):  every `n ≥ 1` has a single
divisor `d ∣ n` with `d ^ 4 ≤ n` and `τ n ≤ 8 * τ d ^ 7`, where
`τ = ArithmeticFunction.sigma 0`. -/
theorem landreau_exists_small_divisor (n : ℕ) (hn : 1 ≤ n) :
    ∃ d, d ∣ n ∧ d ^ 4 ≤ n ∧
      ArithmeticFunction.sigma 0 n ≤ 8 * ArithmeticFunction.sigma 0 d ^ 7 := by
  obtain ⟨m, h, hprod, hm_primes, hτh⟩ := landreau_peel n hn
  have hm_dvd : m ∣ n := ⟨h, hprod⟩
  have hm_le : m ≤ n := Nat.le_of_dvd (by omega) hm_dvd
  have hm_size : m ^ 4 ≤ n ^ (3 + 1) := Nat.pow_le_pow_left hm_le 4
  obtain ⟨d, hdm, hd4, hτ⟩ := landreau_smooth n hn 3 m hm_primes hm_size
  refine ⟨d, hdm.trans hm_dvd, hd4, ?_⟩
  simp only [ArithmeticFunction.sigma_zero_apply]
  calc n.divisors.card
      = (m * h).divisors.card := by rw [← hprod]
    _ ≤ m.divisors.card * h.divisors.card := landreau_card_divisors_mul_le m h
    _ ≤ d.divisors.card ^ 7 * 8 := Nat.mul_le_mul (by simpa using hτ) hτh
    _ = 8 * d.divisors.card ^ 7 := by ring

/-- **The Landreau/Lay small-divisor inequality**: for `n ≥ 1`,
`τ n ≤ 8 * ∑_{d ∣ n, d ^ 4 ≤ n} τ d ^ 7` with `τ = ArithmeticFunction.sigma 0`
(Landreau, BSMF **117** (1989); explicit constants from Lay, arXiv:1711.05924).
The filter `(d : ℝ) ^ 4 ≤ n` is the real-number spelling of `d ≤ n ^ (1/4)`. -/
theorem landreau_tau_le (n : ℕ) (hn : 1 ≤ n) :
    ArithmeticFunction.sigma 0 n ≤
      8 * ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)),
        ArithmeticFunction.sigma 0 d ^ 7 := by
  obtain ⟨d, hdn, hd4, hτ⟩ := landreau_exists_small_divisor n hn
  have hmem : d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdn, by omega⟩, by exact_mod_cast hd4⟩
  refine hτ.trans (Nat.mul_le_mul le_rfl ?_)
  exact Finset.single_le_sum (f := fun d : ℕ => ArithmeticFunction.sigma 0 d ^ 7)
    (fun i _ => Nat.zero_le _) hmem

/-- **Fourth-power variant** of the Landreau/Lay inequality, the form consumed by
short-interval `τ ^ 4` bounds: for `n ≥ 1`,
`τ n ^ 4 ≤ 4096 * ∑_{d ∣ n, d ^ 4 ≤ n} τ d ^ 28`, with `τ = ArithmeticFunction.sigma 0`,
`4096 = 8 ^ 4` and `28 = 4 * 7`.  Obtained by raising the max-block form to the fourth
power *before* passing to the sum (the summed form itself does not interchange). -/
theorem landreau_tau_pow_four_le (n : ℕ) (hn : 1 ≤ n) :
    ArithmeticFunction.sigma 0 n ^ 4 ≤
      4096 * ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)),
        ArithmeticFunction.sigma 0 d ^ 28 := by
  obtain ⟨d, hdn, hd4, hτ⟩ := landreau_exists_small_divisor n hn
  have hmem : d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdn, by omega⟩, by exact_mod_cast hd4⟩
  have h1 : ArithmeticFunction.sigma 0 n ^ 4 ≤
      4096 * ArithmeticFunction.sigma 0 d ^ 28 := by
    calc ArithmeticFunction.sigma 0 n ^ 4
        ≤ (8 * ArithmeticFunction.sigma 0 d ^ 7) ^ 4 := Nat.pow_le_pow_left hτ 4
      _ = 4096 * ArithmeticFunction.sigma 0 d ^ 28 := by ring
  refine h1.trans (Nat.mul_le_mul le_rfl ?_)
  exact Finset.single_le_sum (f := fun d : ℕ => ArithmeticFunction.sigma 0 d ^ 28)
    (fun i _ => Nat.zero_le _) hmem

end Shiu
end Zeta85
end RH

#print axioms RH.Zeta85.Shiu.landreau_exists_small_divisor
#print axioms RH.Zeta85.Shiu.landreau_tau_le
#print axioms RH.Zeta85.Shiu.landreau_tau_pow_four_le
