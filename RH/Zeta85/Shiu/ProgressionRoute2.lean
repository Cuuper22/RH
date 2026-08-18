/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Shiu.Landreau
import RH.Zeta85.Shiu.TauSummatory
import RH.Zeta85.Shiu.TauPointwise
import RH.Zeta85.Shiu.ProgressionCount
import RH.Zeta85.Shiu.ShortInterval

/-!
# Route 2: divisor-power sums over an arithmetic progression

`RH/Zeta85/Shiu/AllTheta.lean` bounds `∑_{x < n ≤ x + y} τ(n)^4` over an *interval*.  The
Shiu-type progression majorant needs the same estimate over a *residue class*,
`∑_{n ≤ N, n ≡ r (q)} τ(n)^k`.  That conversion is the content of this file, and it is a
genuine argument, not a corollary of the interval bound: the interval count `y/d + O(1)` of
multiples of `d` gets replaced by the CRT count `N/(dq) + O(1)` of the simultaneous
conditions `n ≡ r (mod q)`, `d ∣ n`.

## The mechanism

1. **Landreau at an arbitrary power** (`progRoute2_landreau_pow`).  Lay's explicit max-block
   form (`RH.Zeta85.Shiu.landreau_exists_small_divisor`, Landreau BSMF **117** (1989);
   explicit constants from Lay, arXiv:1711.05924) gives a single divisor `d ∣ n` with
   `d^4 ≤ n` and `τ n ≤ 8·τ(d)^7`.  Raising to the `k`-th power *before* passing to the sum,

   `τ(n)^k ≤ 8^k · ∑_{d ∣ n, d^4 ≤ n} τ(d)^{7k}`.

   (At `k = 4` this is exactly `landreau_tau_pow_four_le`, with `8^4 = 4096`, `7·4 = 28`.)

2. **The CRT counting core** (`progRoute2_count_dvd_ap_coprime`).  For `gcd(d, q) = 1` the
   two conditions `n ≡ r (mod q)` and `d ∣ n` cut out a *single* class mod `dq`, so

   `#{n ≤ N : n ≡ r (q), d ∣ n} ≤ N/(dq) + 1`.

   When `gcd(r, q) = 1` every `d` that occurs is automatically coprime to `q`
   (`progRoute2_coprime_of_mem`), so the coprime case is the only case
   (`progRoute2_count_dvd_ap`); the degenerate `d` are handled by
   `progRoute2_count_dvd_ap_empty` (the class is empty unless `gcd(d,q) ∣ r`) and by the
   crude `N/d + 1` bound `progRoute2_count_dvd_ap_crude`.

3. **The interchange** (`progRoute2_interchange`).  Every surviving `d` has `d^4 ≤ n ≤ N`,
   hence `d ≤ ⌊N^{1/4}⌋ =: D` (`progRoute2_quartRoot`), so summing 1. over the class and
   swapping the order of summation gives

   `∑_{n ≤ N, n ≡ r (q)} τ(n)^k ≤ 8^k · ∑_{d ≤ D} τ(d)^{7k} · #{n ≤ N : n ≡ r (q), d ∣ n}`.

4. **Summing the two terms.**  With `E := 2^{7k}` and `τ(d)^{7k} ≤ ζ^E(d)`
   (`RH.Zeta85.Shiu.tau_pow_le_tauPow`), `RH.Zeta85.Shiu.tauSum_div_le` and
   `RH.Zeta85.Shiu.tauSum_le` give
   `∑_{d ≤ D} τ(d)^{7k}/d ≤ (1 + log D)^E` and `∑_{d ≤ D} τ(d)^{7k} ≤ D·(1 + log D)^{E-1}`.
   So the `N/(dq)` main terms contribute `(N/q)·(1 + log D)^E` and the `+1` error terms
   contribute `D·(1 + log D)^{E-1}`.

5. **Where the modulus range comes from.**  The error term is absorbed exactly when
   `D ≤ N/q`.  Since `D^4 ≤ N`, the clean sufficient condition is `q^4 ≤ N^3`, i.e.

   `q ≤ N^{3/4}`,

   because then `(qD)^4 = q^4·D^4 ≤ N^3·N = N^4`.  **This is the honest modulus range of
   this file**, and it is what a `1/4 < η` Shiu exponent needs: `q ≤ P^{1-η}` with
   `η ≥ 1/4` implies `q ≤ P^{3/4}` for `P ≥ 1`.

## Main results

* `progRoute2_count_dvd_ap_coprime` — the CRT count `≤ N/(dq) + 1` for `gcd(d,q) = 1`;
* `progRoute2_count_dvd_ap_empty` — the class is empty unless `gcd(d,q) ∣ r`;
* `progRoute2_count_dvd_ap_crude` — the unconditional crude count `≤ N/d + 1`;
* `progRoute2_landreau_pow` — Landreau's inequality at an arbitrary power `k`;
* `progRoute2_tau_pow_progression` — the main theorem, for `1 ≤ N`, `0 < q`,
  `gcd(r,q) = 1` and `q^4 ≤ N^3`:
  `∑_{n ≤ N, n ≡ r (q)} τ(n)^k ≤ 2·8^k · (N/q) · (1 + log N)^{2^{7k}}`;
* `progRoute2_tau_pow_four_progression` — the `k = 4` case, constants `8192` and `2^28`;
* `progRoute2_tau_pow_totient`, `progRoute2_tau_pow_four_totient` — the same with `N/q`
  replaced by `N/φ(q)`, the shape the corrected Shiu interface wants;
* `progRoute2_progressionSum_pow_k`, `progRoute2_progressionSum_pow_four` — the
  `progressionSum` form: for any `DivisorBounded c Kc k` family and `q^4 ≤ P^3`,
  `progressionSum c P q r ≤ Kc·(6·8^k)·(P/φ(q))·(3 + log P)^{2^{7k}}`;
* `progRoute2_range_of_rpow` — the range conversion `q ≤ P^{1-η}`, `η ≥ 1/4` ⟹ `q^4 ≤ P^3`;
* `progRoute2_shiu_shape` — the whole thing packaged in the shape a Shiu-type majorant
  consumes: explicit `C = 2^{7k}`, `K = Kc·(6·8^k)·2^{2^{7k}}` and `P₁ = e^3` with
  `progressionSum c P q r ≤ K·(P/φ(q))·(log P)^C` for `P ≥ P₁` and `q ≤ P^{1-η}`.

All constants are explicit.  They are astronomical (`2^{7k}` in the exponent, `2^28` at
`k = 4`) — that is the price of the Landreau route and is expected; nothing here is
asymptotic or hidden.

## What is *not* here

The estimate is uniform in `q` only over `q ≤ N^{3/4}`.  That range comes from
`progRoute2_mul_quartRoot_le` and from nothing else — neither divisor-sum lemma below
affects it — so pushing past `3/4` needs a different treatment of the error terms, not a
better summatory bound.

The logarithmic exponent `2^{7k}` comes from the crude pointwise majorant
`τ(d)^j ≤ ζ^{2^j}(d)` of `RH.Zeta85.Shiu.tau_pow_le_tauPow`, and it is **not** improved by
swapping in the factorially sharper `RH.Zeta85.Shiu.tauSum_div_le_factorial`: that lemma
bounds `∑_{m ≤ N} τ_K(m)/m` by `(log N + K)^K / K!`, whose exponent is still `K`, and this
file feeds it `K = 2^{7k}`.  The swap buys a constant, not an exponent; reducing the
exponent needs a summatory bound for `τ(d)^j` itself rather than for its `ζ^{2^j}` majorant.

That distinction matters downstream.  `RH/Zeta85/Discharge/LogBudget.lean` proves
(`verdict_all`) that at a logarithmic exponent `C ≥ 3` all three accounting models exceed
the trace budget; the exponent delivered here is `2^{7k}`, far above that threshold.  So
this file closes the *progression-versus-interval* gap it was written to close, and it does
**not** by itself make the Landreau route budget-feasible.

**Note for the merge.**  Nothing imports `RH.Zeta85.Shiu.ProgressionRoute2` yet, so CI does
not type-check it on this branch; reaching it from a build target is a coordinator-level
follow-up, and until then the `#print axioms` audit at the bottom of this file runs only
when the module is elaborated by hand (it has been, and every entry reports exactly
`propext`, `Classical.choice`, `Quot.sound`).  The interface-shaped result
`progRoute2_shiu_shape` deliberately spells its existential out rather than naming a
`ShiuMajorant₂` predicate, so that this file compiles whether or not that definition has
landed; binding it to the named predicate is likewise a coordinator step.
-/

open scoped BigOperators

namespace RH
namespace Zeta85
namespace Shiu

/-! ## 1. The quartic-root cutoff `⌊N^{1/4}⌋` -/

/-- `progRoute2_quartRoot N = ⌊N^{1/4}⌋`, realised as the iterated integer square root.
Every divisor `d` with `d^4 ≤ N` satisfies `d ≤ progRoute2_quartRoot N`
(`progRoute2_le_quartRoot`), and conversely `(progRoute2_quartRoot N)^4 ≤ N`
(`progRoute2_quartRoot_pow_four_le`). -/
def progRoute2_quartRoot (N : ℕ) : ℕ := Nat.sqrt (Nat.sqrt N)

/-- `⌊N^{1/4}⌋^4 ≤ N`. -/
lemma progRoute2_quartRoot_pow_four_le (N : ℕ) : progRoute2_quartRoot N ^ 4 ≤ N := by
  have h1 : progRoute2_quartRoot N ^ 2 ≤ Nat.sqrt N := Nat.sqrt_le' (Nat.sqrt N)
  calc progRoute2_quartRoot N ^ 4
      = (progRoute2_quartRoot N ^ 2) ^ 2 := by ring
    _ ≤ (Nat.sqrt N) ^ 2 := Nat.pow_le_pow_left h1 2
    _ ≤ N := Nat.sqrt_le' N

/-- Any `d` with `d^4 ≤ N` is at most `⌊N^{1/4}⌋`. -/
lemma progRoute2_le_quartRoot {d N : ℕ} (h : d ^ 4 ≤ N) : d ≤ progRoute2_quartRoot N := by
  have h2 : d ^ 2 ≤ Nat.sqrt N := by
    refine Nat.le_sqrt'.mpr ?_
    calc (d ^ 2) ^ 2 = d ^ 4 := by ring
      _ ≤ N := h
  exact Nat.le_sqrt'.mpr h2

/-- `⌊N^{1/4}⌋ ≥ 1` as soon as `N ≥ 1`. -/
lemma progRoute2_one_le_quartRoot {N : ℕ} (hN : 1 ≤ N) : 1 ≤ progRoute2_quartRoot N := by
  have h1 : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr hN
  exact Nat.sqrt_pos.mpr h1

/-- `⌊N^{1/4}⌋ ≤ N`. -/
lemma progRoute2_quartRoot_le_self (N : ℕ) : progRoute2_quartRoot N ≤ N :=
  le_trans (Nat.sqrt_le_self _) (Nat.sqrt_le_self _)

/-- **The modulus range, in arithmetic form.**  `q ≤ N^{3/4}` (spelled `q^4 ≤ N^3`) forces
`q·⌊N^{1/4}⌋ ≤ N`, which is exactly the inequality that absorbs the `+1` error terms of the
CRT count into the main term. -/
lemma progRoute2_mul_quartRoot_le {q N : ℕ} (hqN : q ^ 4 ≤ N ^ 3) :
    q * progRoute2_quartRoot N ≤ N := by
  by_contra hcon
  have hlt : N < q * progRoute2_quartRoot N := Nat.lt_of_not_le hcon
  have h1 : N ^ 4 < (q * progRoute2_quartRoot N) ^ 4 :=
    Nat.pow_lt_pow_left hlt (by norm_num)
  have h2 : (q * progRoute2_quartRoot N) ^ 4 ≤ N ^ 3 * N := by
    calc (q * progRoute2_quartRoot N) ^ 4 = q ^ 4 * progRoute2_quartRoot N ^ 4 := by
          rw [Nat.mul_pow]
      _ ≤ N ^ 3 * N := Nat.mul_le_mul hqN (progRoute2_quartRoot_pow_four_le N)
  have h3 : N ^ 3 * N = N ^ 4 := by ring
  omega

/-! ## 2. Counting `{n ≤ N : n ≡ r (mod q), d ∣ n}` -/

/-- **The CRT counting core.**  If `gcd(d, q) = 1` then the two conditions `n ≡ r (mod q)`
and `d ∣ n` cut out a single residue class modulo `d·q`, so the class has at most
`N/(dq) + 1` members in `[1, N]`.

Proof: if the set is nonempty, pick a member `n₀`; every other member `n` is congruent to
`n₀` both mod `q` (both are `≡ r`) and mod `d` (both are `≡ 0`), hence mod `dq` by
`Nat.modEq_and_modEq_iff_modEq_mul`.  Then `progCount_le_nat` applies at modulus `dq`. -/
theorem progRoute2_count_dvd_ap_coprime {q d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (hdq : Nat.Coprime d q) (r N : ℕ) :
    ((((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card : ℝ))
      ≤ (N : ℝ) / ((d : ℝ) * q) + 1 := by
  have hdq0 : (0 : ℝ) ≤ (N : ℝ) / ((d : ℝ) * q) := by positivity
  rcases Finset.eq_empty_or_nonempty
      ((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)) with hE | ⟨n₀, hn₀⟩
  · rw [hE]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · have hn₀' := Finset.mem_filter.mp hn₀
    have hsub : (Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)
        ⊆ (Finset.Icc 1 N).filter (fun n => n % (d * q) = n₀ % (d * q)) := by
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨hn'.1, ?_⟩
      have hmq : n ≡ n₀ [MOD q] := by
        show n % q = n₀ % q
        rw [hn'.2.1, hn₀'.2.1]
      have hmd : n ≡ n₀ [MOD d] := by
        have h1 : n ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hn'.2.2
        have h2 : n₀ ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hn₀'.2.2
        exact h1.trans h2.symm
      exact (Nat.modEq_and_modEq_iff_modEq_mul hdq).mp ⟨hmd, hmq⟩
    have hcard : ((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card
        ≤ N / (d * q) + 1 :=
      le_trans (Finset.card_le_card hsub) (progCount_le_nat (d * q) n₀ N)
    have hcast : (((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card : ℝ)
        ≤ ((N / (d * q) : ℕ) : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      push_cast at this
      linarith
    have hdiv : ((N / (d * q) : ℕ) : ℝ) ≤ (N : ℝ) / ((d : ℝ) * q) := by
      have h := Nat.cast_div_le (α := ℝ) (m := N) (n := d * q)
      push_cast at h
      exact h
    linarith

/-- **Vacuity off the `gcd`.**  If `gcd(d, q) ∤ r` then no `n` satisfies both
`n ≡ r (mod q)` and `d ∣ n`: reducing the first congruence mod `g := gcd(d, q)` and using
`g ∣ d ∣ n` gives `r ≡ n ≡ 0 (mod g)`, i.e. `g ∣ r`. -/
theorem progRoute2_count_dvd_ap_empty {q d r N : ℕ} (h : ¬ (Nat.gcd d q ∣ r)) :
    (Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n) = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun n hn => h ?_
  have hn' := Finset.mem_filter.mp hn
  have hgq : Nat.gcd d q ∣ q := Nat.gcd_dvd_right d q
  have hgn : Nat.gcd d q ∣ n := (Nat.gcd_dvd_left d q).trans hn'.2.2
  have hmq : n ≡ r [MOD q] := hn'.2.1
  have hmg : n ≡ r [MOD Nat.gcd d q] := hmq.of_dvd hgq
  have hzero : n ≡ 0 [MOD Nat.gcd d q] := Nat.modEq_zero_iff_dvd.mpr hgn
  exact Nat.modEq_zero_iff_dvd.mp (hmg.symm.trans hzero)

/-- **The crude count**, valid for every `d` with no coprimality assumption: forgetting the
congruence leaves the multiples of `d`, of which `[1, N]` holds at most `N/d + 1`.  This is
the fallback used when `d` and `q` share a factor; under `gcd(r, q) = 1` it is never needed,
since then every `d` occurring is coprime to `q` (`progRoute2_coprime_of_mem`). -/
theorem progRoute2_count_dvd_ap_crude (d q r N : ℕ) :
    ((((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card : ℝ))
      ≤ (N : ℝ) / (d : ℝ) + 1 := by
  have hsub : (Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)
      ⊆ (Finset.Icc 1 N).filter (fun n => n % d = 0 % d) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hn'.1, ?_⟩
    rw [Nat.zero_mod]
    exact Nat.dvd_iff_mod_eq_zero.mp hn'.2.2
  have hcard : ((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card ≤ N / d + 1 :=
    le_trans (Finset.card_le_card hsub) (progCount_le_nat d 0 N)
  have hcast : (((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card : ℝ)
      ≤ ((N / d : ℕ) : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at this
    linarith
  have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  linarith

/-- If `gcd(r, q) = 1` and `n ≡ r (mod q)`, then every divisor of `n` is coprime to `q`:
`gcd(q, n) = gcd(n % q, q) = gcd(r % q, q) = gcd(q, r) = 1` by `Nat.gcd_rec`. -/
theorem progRoute2_coprime_of_mem {q r n d : ℕ} (hrq : Nat.Coprime r q)
    (hn : n % q = r % q) (hdn : d ∣ n) : Nat.Coprime d q := by
  have h1 : Nat.gcd q n = Nat.gcd (n % q) q := Nat.gcd_rec q n
  have h2 : Nat.gcd q r = Nat.gcd (r % q) q := Nat.gcd_rec q r
  have h3 : Nat.gcd q r = 1 := Nat.coprime_comm.mp hrq
  have hqn : Nat.Coprime q n := by
    show Nat.gcd q n = 1
    rw [h1, hn, ← h2, h3]
  exact Nat.Coprime.coprime_dvd_left hdn hqn.symm

/-- **The counting bound used by the main theorem.**  For `gcd(r, q) = 1` the CRT count
applies to *every* `d ≥ 1`: either the class is empty, or it contains some `n` and then
`gcd(d, q) ∣ gcd(n, q) = 1`, so `progRoute2_count_dvd_ap_coprime` fires. -/
theorem progRoute2_count_dvd_ap {q d : ℕ} (hq : 0 < q) (hd : 0 < d) {r : ℕ}
    (hrq : Nat.Coprime r q) (N : ℕ) :
    ((((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card : ℝ))
      ≤ (N : ℝ) / ((d : ℝ) * q) + 1 := by
  rcases Finset.eq_empty_or_nonempty
      ((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)) with hE | ⟨n, hn⟩
  · have hdq0 : (0 : ℝ) ≤ (N : ℝ) / ((d : ℝ) * q) := by positivity
    rw [hE]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · have hn' := Finset.mem_filter.mp hn
    exact progRoute2_count_dvd_ap_coprime hq hd
      (progRoute2_coprime_of_mem hrq hn'.2.1 hn'.2.2) r N

/-! ## 3. Landreau's inequality at an arbitrary power -/

/-- **Landreau's inequality at the `k`-th power.**  For `n ≥ 1`,
`τ(n)^k ≤ 8^k · ∑_{d ∣ n, d^4 ≤ n} τ(d)^{7k}` with `τ = ArithmeticFunction.sigma 0`
(Landreau, BSMF **117** (1989); explicit constants from Lay, arXiv:1711.05924).  Obtained
from the max-block form `RH.Zeta85.Shiu.landreau_exists_small_divisor` by raising
`τ n ≤ 8·τ(d)^7` to the `k`-th power *before* passing to the sum (the summed form itself
does not interchange).  At `k = 4` this is `RH.Zeta85.Shiu.landreau_tau_pow_four_le`. -/
theorem progRoute2_landreau_pow (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ArithmeticFunction.sigma 0 n ^ k ≤
      8 ^ k * ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)),
        ArithmeticFunction.sigma 0 d ^ (7 * k) := by
  obtain ⟨d, hdn, hd4, hτ⟩ := landreau_exists_small_divisor n hn
  have hmem : d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdn, by omega⟩, by exact_mod_cast hd4⟩
  have h1 : ArithmeticFunction.sigma 0 n ^ k
      ≤ 8 ^ k * ArithmeticFunction.sigma 0 d ^ (7 * k) := by
    calc ArithmeticFunction.sigma 0 n ^ k
        ≤ (8 * ArithmeticFunction.sigma 0 d ^ 7) ^ k := Nat.pow_le_pow_left hτ k
      _ = 8 ^ k * ArithmeticFunction.sigma 0 d ^ (7 * k) := by
          rw [Nat.mul_pow, ← pow_mul]
  refine h1.trans (Nat.mul_le_mul le_rfl ?_)
  exact Finset.single_le_sum (f := fun d : ℕ => ArithmeticFunction.sigma 0 d ^ (7 * k))
    (fun i _ => Nat.zero_le _) hmem

/-! ## 4. The interchange and the divisor-sum inputs -/

/-- **The interchange.**  Summing a divisor-indexed weight over a residue class and swapping
the order of summation replaces the inner divisor sum by a count of the class members
divisible by `d`. -/
theorem progRoute2_interchange (N D q r : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n), f d
      = ∑ d ∈ Finset.Icc 1 D,
          f d * ((((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card : ℝ)) := by
  have hinner : ∀ n : ℕ, ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n), f d
      = ∑ d ∈ Finset.Icc 1 D, (if d ∣ n then f d else 0) := fun n => Finset.sum_filter _ _
  rw [Finset.sum_congr rfl (fun n _ => hinner n), Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- `∑_{d ≤ D} τ(d)^j / d ≤ (1 + log D)^{2^j}`: combine the pointwise
`τ(d)^j ≤ ζ^{2^j}(d)` (`RH.Zeta85.Shiu.tau_pow_le_tauPow`) with the logarithmic-average
bound `RH.Zeta85.Shiu.tauSum_div_le`. -/
theorem progRoute2_tauSum_div (j D : ℕ) (hD : 1 ≤ D) :
    ∑ d ∈ Finset.Icc 1 D, ((ArithmeticFunction.sigma 0 d : ℕ) : ℝ) ^ j / (d : ℝ)
      ≤ (1 + Real.log D) ^ (2 ^ j) := by
  refine le_trans (Finset.sum_le_sum ?_) (tauSum_div_le (2 ^ j) D hD)
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hd0 : d ≠ 0 := by omega
  have hpt : ((ArithmeticFunction.sigma 0 d : ℕ) : ℝ) ^ j
      ≤ (((ArithmeticFunction.zeta ^ (2 ^ j)) d : ℕ) : ℝ) := by
    exact_mod_cast tau_pow_le_tauPow hd0 j
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hpt (by positivity)

/-- `∑_{d ≤ D} τ(d)^j ≤ D·(1 + log D)^{2^j - 1}`: combine the pointwise
`τ(d)^j ≤ ζ^{2^j}(d)` with the summatory bound `RH.Zeta85.Shiu.tauSum_le`. -/
theorem progRoute2_tauSum (j D : ℕ) (hD : 1 ≤ D) :
    ∑ d ∈ Finset.Icc 1 D, ((ArithmeticFunction.sigma 0 d : ℕ) : ℝ) ^ j
      ≤ (D : ℝ) * (1 + Real.log D) ^ (2 ^ j - 1) := by
  refine le_trans (Finset.sum_le_sum ?_) (tauSum_le (2 ^ j) D Nat.one_le_two_pow hD)
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hd0 : d ≠ 0 := by omega
  exact_mod_cast tau_pow_le_tauPow hd0 j

/-! ## 5. The main theorem -/

set_option maxHeartbeats 2000000 in
/-- **Route 2, main theorem: `τ^k` over a residue class.**

For `N ≥ 1`, `q ≥ 1`, `gcd(r, q) = 1` and `q^4 ≤ N^3` (that is, `q ≤ N^{3/4}`),

  `∑_{n ≤ N, n ≡ r (mod q)} τ(n)^k ≤ 2·8^k · (N/q) · (1 + log N)^{2^{7k}}`.

The proof is the four-step mechanism described in the module docstring: Landreau at the
`k`-th power (`progRoute2_landreau_pow`), restriction of the small divisors to
`[1, ⌊N^{1/4}⌋]`, the interchange (`progRoute2_interchange`), the CRT count
(`progRoute2_count_dvd_ap`), and the two divisor-sum bounds (`progRoute2_tauSum_div`,
`progRoute2_tauSum`).  The hypothesis `q^4 ≤ N^3` enters exactly once, through
`progRoute2_mul_quartRoot_le`, to absorb the `+1` error terms of the count into the main
term (`⌊N^{1/4}⌋ ≤ N/q`). -/
theorem progRoute2_tau_pow_progression (k : ℕ) {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (hrq : Nat.Coprime r q) (hqN : q ^ 4 ≤ N ^ 3) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
      ≤ 2 * 8 ^ k * ((N : ℝ) / (q : ℝ)) * (1 + Real.log N) ^ (2 ^ (7 * k)) := by
  classical
  set D := progRoute2_quartRoot N
  set f : ℕ → ℝ := fun d => ((ArithmeticFunction.sigma 0 d : ℕ) : ℝ) ^ (7 * k) with hfdef
  set E : ℕ := 2 ^ (7 * k)
  have hD1 : 1 ≤ D := progRoute2_one_le_quartRoot hN
  have hDN : D ≤ N := progRoute2_quartRoot_le_self N
  have hqD : q * D ≤ N := progRoute2_mul_quartRoot_le hqN
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hNq0 : (0 : ℝ) ≤ (N : ℝ) / (q : ℝ) := by positivity
  have hfnn : ∀ d : ℕ, 0 ≤ f d := fun d => by simp only [hfdef]; positivity
  -- Step 1: the pointwise Landreau bound, with the small divisors placed in `[1, D]`.
  have step1 : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
      ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
        ≤ 8 ^ k * ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n), f d := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn'.1).1
    have hn2 : n ≤ N := (Finset.mem_Icc.mp hn'.1).2
    have hLR : ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
        ≤ 8 ^ k * ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)), f d := by
      simp only [hfdef]
      exact_mod_cast progRoute2_landreau_pow k hn1
    refine hLR.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hfnn i)
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd'.1
    have hddvd : d ∣ n := (Nat.mem_divisors.mp hd'.1).1
    have hd4 : d ^ 4 ≤ n := by exact_mod_cast hd'.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos, ?_⟩, hddvd⟩
    exact progRoute2_le_quartRoot (hd4.trans hn2)
  -- Step 2: sum the pointwise bound over the class.
  have step2 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
      ≤ 8 ^ k * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n), f d := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum step1
  -- Step 3: the CRT count, applied termwise after the interchange.
  have step3 : ∑ d ∈ Finset.Icc 1 D,
        f d * ((((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 D, f d * ((N : ℝ) / ((d : ℝ) * q) + 1) := by
    refine Finset.sum_le_sum fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    exact mul_le_mul_of_nonneg_left (progRoute2_count_dvd_ap hq hd1 hrq N) (hfnn d)
  -- Step 4: split the resulting sum into the main term and the error term.
  have step4 : ∑ d ∈ Finset.Icc 1 D, f d * ((N : ℝ) / ((d : ℝ) * q) + 1)
      = ((N : ℝ) / (q : ℝ)) * (∑ d ∈ Finset.Icc 1 D, f d / (d : ℝ))
        + ∑ d ∈ Finset.Icc 1 D, f d := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  -- Step 5: the two divisor sums.
  have hmain : ∑ d ∈ Finset.Icc 1 D, f d / (d : ℝ) ≤ (1 + Real.log D) ^ E :=
    progRoute2_tauSum_div (7 * k) D hD1
  have herr : ∑ d ∈ Finset.Icc 1 D, f d ≤ (D : ℝ) * (1 + Real.log D) ^ (E - 1) :=
    progRoute2_tauSum (7 * k) D hD1
  -- Step 6: the logarithmic and size comparisons.
  have hlogD : (0 : ℝ) ≤ Real.log D := Real.log_natCast_nonneg D
  have hLD1 : (1 : ℝ) ≤ 1 + Real.log D := by linarith
  have hLD0 : (0 : ℝ) ≤ 1 + Real.log D := by linarith
  have hlogDN : Real.log D ≤ Real.log N := by
    have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
    exact Real.log_le_log hD0 (by exact_mod_cast hDN)
  have hpowLN : (1 + Real.log D) ^ E ≤ (1 + Real.log N) ^ E :=
    pow_le_pow_left₀ hLD0 (by linarith) E
  have hpowE : (1 + Real.log D) ^ (E - 1) ≤ (1 + Real.log D) ^ E :=
    pow_le_pow_right₀ hLD1 (Nat.sub_le _ _)
  have hDq : (D : ℝ) ≤ (N : ℝ) / (q : ℝ) := by
    rw [le_div_iff₀ hq0]
    have : D * q ≤ N := by rw [Nat.mul_comm] at hqD; exact hqD
    exact_mod_cast this
  -- Step 7: assemble.
  have hA1 : ((N : ℝ) / (q : ℝ)) * (∑ d ∈ Finset.Icc 1 D, f d / (d : ℝ))
      ≤ ((N : ℝ) / (q : ℝ)) * (1 + Real.log N) ^ E :=
    mul_le_mul_of_nonneg_left (hmain.trans hpowLN) hNq0
  have hA2 : ∑ d ∈ Finset.Icc 1 D, f d ≤ ((N : ℝ) / (q : ℝ)) * (1 + Real.log N) ^ E := by
    refine herr.trans (mul_le_mul hDq (hpowE.trans hpowLN) (by positivity) hNq0)
  calc ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
      ≤ 8 ^ k * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n), f d := step2
    _ = 8 ^ k * ∑ d ∈ Finset.Icc 1 D,
          f d * ((((Finset.Icc 1 N).filter (fun n => n % q = r % q ∧ d ∣ n)).card : ℝ)) := by
        rw [progRoute2_interchange N D q r f]
    _ ≤ 8 ^ k * ∑ d ∈ Finset.Icc 1 D, f d * ((N : ℝ) / ((d : ℝ) * q) + 1) :=
        mul_le_mul_of_nonneg_left step3 (by positivity)
    _ = 8 ^ k * (((N : ℝ) / (q : ℝ)) * (∑ d ∈ Finset.Icc 1 D, f d / (d : ℝ))
          + ∑ d ∈ Finset.Icc 1 D, f d) := by rw [step4]
    _ ≤ 8 ^ k * (((N : ℝ) / (q : ℝ)) * (1 + Real.log N) ^ E
          + ((N : ℝ) / (q : ℝ)) * (1 + Real.log N) ^ E) :=
        mul_le_mul_of_nonneg_left (add_le_add hA1 hA2) (by positivity)
    _ = 2 * 8 ^ k * ((N : ℝ) / (q : ℝ)) * (1 + Real.log N) ^ E := by ring

/-- **The `k = 4` case**, the exponent the Shiu majorant consumes: for `N ≥ 1`, `q ≥ 1`,
`gcd(r, q) = 1` and `q ≤ N^{3/4}`,
`∑_{n ≤ N, n ≡ r (q)} τ(n)^4 ≤ 8192·(N/q)·(1 + log N)^{2^28}`
(`8192 = 2·8^4` and `2^28 = 2^{7·4}`). -/
theorem progRoute2_tau_pow_four_progression {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (hrq : Nat.Coprime r q) (hqN : q ^ 4 ≤ N ^ 3) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 4
      ≤ 8192 * ((N : ℝ) / (q : ℝ)) * (1 + Real.log N) ^ (2 ^ 28) := by
  have h := progRoute2_tau_pow_progression 4 hN hq hrq hqN
  have hc : (2 : ℝ) * 8 ^ (4 : ℕ) = 8192 := by norm_num
  rw [hc] at h
  simpa using h

/-! ## 6. The `φ`-form -/

/-- **The `φ`-form of the main theorem**, the shape the corrected Shiu interface wants:
since `φ(q) ≤ q`, the bound `N/q` may be relaxed to `N/φ(q)`. -/
theorem progRoute2_tau_pow_totient (k : ℕ) {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (hrq : Nat.Coprime r q) (hqN : q ^ 4 ≤ N ^ 3) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
      ≤ 2 * 8 ^ k * ((N : ℝ) / (Nat.totient q : ℝ)) * (1 + Real.log N) ^ (2 ^ (7 * k)) := by
  refine (progRoute2_tau_pow_progression k hN hq hrq hqN).trans ?_
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hφle : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hdiv : (N : ℝ) / (q : ℝ) ≤ (N : ℝ) / (Nat.totient q : ℝ) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) hφpos hφle
  have hlog : (0 : ℝ) ≤ (1 + Real.log N) ^ (2 ^ (7 * k)) := by
    have : (0 : ℝ) ≤ 1 + Real.log N := by
      have := Real.log_natCast_nonneg N; linarith
    positivity
  have hpre : (0 : ℝ) ≤ 2 * 8 ^ k := by positivity
  calc 2 * 8 ^ k * ((N : ℝ) / (q : ℝ)) * (1 + Real.log N) ^ (2 ^ (7 * k))
      ≤ 2 * 8 ^ k * ((N : ℝ) / (Nat.totient q : ℝ)) * (1 + Real.log N) ^ (2 ^ (7 * k)) := by
        have := mul_le_mul_of_nonneg_left hdiv hpre
        exact mul_le_mul_of_nonneg_right this hlog

/-- **The `φ`-form at `k = 4`**: `∑_{n ≤ N, n ≡ r (q)} τ(n)^4 ≤ 8192·(N/φ(q))·(1+log N)^{2^28}`
for `q ≤ N^{3/4}` and `gcd(r, q) = 1`. -/
theorem progRoute2_tau_pow_four_totient {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (hrq : Nat.Coprime r q) (hqN : q ^ 4 ≤ N ^ 3) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 4
      ≤ 8192 * ((N : ℝ) / (Nat.totient q : ℝ)) * (1 + Real.log N) ^ (2 ^ 28) := by
  have h := progRoute2_tau_pow_totient 4 hN hq hrq hqN
  have hc : (2 : ℝ) * 8 ^ (4 : ℕ) = 8192 := by norm_num
  rw [hc] at h
  simpa using h

/-! ## 7. The `progressionSum` form -/

/-- A `DivisorBounded` family has a nonnegative constant: evaluating at `n = 1` gives
`0 ≤ |c 1| ≤ Kc·τ(1)^k = Kc`. -/
theorem progRoute2_divisorBounded_nonneg {c : ℕ → ℝ} {Kc : ℝ} {k : ℕ}
    (hc : DivisorBounded c Kc k) : 0 ≤ Kc := by
  have h := hc 1
  have h1 : ((ArithmeticFunction.sigma 0 1 : ℕ) : ℝ) = 1 := by simp
  rw [h1, one_pow, mul_one] at h
  exact le_trans (abs_nonneg _) h

set_option maxHeartbeats 2000000 in
/-- **Route 2 for `progressionSum`, general `k`.**  For every divisor-bounded family
`|c n| ≤ Kc·τ(n)^k`, every `P ≥ 1` and every modulus `q` with `gcd(r, q) = 1` in the range
`q^4 ≤ P^3` (that is, `q ≤ P^{3/4}`),

  `progressionSum c P q r ≤ Kc·(6·8^k)·(P/φ(q))·(3 + log P)^{2^{7k}}`.

This is a genuine instance of the corrected Shiu-interface shape: the modulus range
`q ≤ P^{3/4}` covers `q ≤ P^{1-η}` for every `η ≥ 1/4`.  Constants: `6·8^k` and the
logarithmic exponent `2^{7k}`; the shift `3 + log P` absorbs the window
`⌈2P⌉ ≤ 3P` through `log 3 ≤ 2`. -/
theorem progRoute2_progressionSum_pow_k {c : ℕ → ℝ} {Kc : ℝ} {k : ℕ}
    (hc : DivisorBounded c Kc k) {P : ℝ} (hP : 1 ≤ P) {q r : ℕ} (hq : 0 < q)
    (hrq : Nat.Coprime r q) (hqP : (q : ℝ) ^ 4 ≤ P ^ 3) :
    progressionSum c P q r
      ≤ Kc * (6 * 8 ^ k) * (P / (Nat.totient q : ℝ)) * (3 + Real.log P) ^ (2 ^ (7 * k)) := by
  have hKc : 0 ≤ Kc := progRoute2_divisorBounded_nonneg hc
  set N : ℕ := ⌈2 * P⌉₊
  have hP0 : (0 : ℝ) < P := by linarith
  have hNlow : 2 * P ≤ (N : ℝ) := shortInt_two_mul_le_ceil P
  have hNhigh : (N : ℝ) ≤ 3 * P := shortInt_ceil_le_three_mul P hP
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hNpos
  -- the modulus range transfers from `P` to the window `N = ⌈2P⌉`
  have hqN : q ^ 4 ≤ N ^ 3 := by
    have hPN : P ≤ (N : ℝ) := by linarith
    have h1 : (q : ℝ) ^ 4 ≤ (N : ℝ) ^ 3 :=
      hqP.trans (pow_le_pow_left₀ (le_of_lt hP0) hPN 3)
    exact_mod_cast h1
  -- the τ^k class sum, in `φ`-form
  have hclass := progRoute2_tau_pow_totient k hN1 hq hrq hqN
  have hred := progressionSum_le_of_divisorBounded hc P q r
  -- window comparisons
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  have hL0 : (0 : ℝ) ≤ 1 + Real.log N := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := (3 : ℝ)) (by norm_num)
    linarith
  have hlogNP : 1 + Real.log N ≤ 3 + Real.log P := by
    have h3P : Real.log ((3 : ℝ) * P) = Real.log 3 + Real.log P :=
      Real.log_mul (by norm_num) (ne_of_gt hP0)
    have hmono : Real.log N ≤ Real.log ((3 : ℝ) * P) :=
      Real.log_le_log (by linarith) hNhigh
    rw [h3P] at hmono
    linarith
  have hpow : (1 + Real.log N) ^ (2 ^ (7 * k)) ≤ (3 + Real.log P) ^ (2 ^ (7 * k)) :=
    pow_le_pow_left₀ hL0 hlogNP _
  have hNφ : (N : ℝ) / (Nat.totient q : ℝ) ≤ 3 * P / (Nat.totient q : ℝ) :=
    div_le_div_of_nonneg_right hNhigh (le_of_lt hφpos)
  -- assemble
  have hchain : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
      ≤ (6 * 8 ^ k) * (P / (Nat.totient q : ℝ)) * (3 + Real.log P) ^ (2 ^ (7 * k)) := by
    refine hclass.trans ?_
    have hpre : (0 : ℝ) ≤ 2 * 8 ^ k := by positivity
    have h1 : 2 * 8 ^ k * ((N : ℝ) / (Nat.totient q : ℝ))
        ≤ 2 * 8 ^ k * (3 * P / (Nat.totient q : ℝ)) :=
      mul_le_mul_of_nonneg_left hNφ hpre
    have h2 : (0 : ℝ) ≤ 2 * 8 ^ k * (3 * P / (Nat.totient q : ℝ)) := by positivity
    have h3 : 2 * 8 ^ k * ((N : ℝ) / (Nat.totient q : ℝ)) * (1 + Real.log N) ^ (2 ^ (7 * k))
        ≤ 2 * 8 ^ k * (3 * P / (Nat.totient q : ℝ)) * (3 + Real.log P) ^ (2 ^ (7 * k)) := by
      refine mul_le_mul h1 hpow (by positivity) h2
    exact h3.trans (le_of_eq (by ring))
  calc progressionSum c P q r
      ≤ Kc * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q),
          ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k := hred
    _ ≤ Kc * ((6 * 8 ^ k) * (P / (Nat.totient q : ℝ)) * (3 + Real.log P) ^ (2 ^ (7 * k))) :=
        mul_le_mul_of_nonneg_left hchain hKc
    _ = Kc * (6 * 8 ^ k) * (P / (Nat.totient q : ℝ)) * (3 + Real.log P) ^ (2 ^ (7 * k)) := by
        ring

/-- **Route 2 for `progressionSum` at `k = 4`.**  For every family with
`|c n| ≤ Kc·τ(n)^4`, every `P ≥ 1`, and every `q` with `gcd(r, q) = 1` and `q ≤ P^{3/4}`,

  `progressionSum c P q r ≤ Kc·24576·(P/φ(q))·(3 + log P)^{2^28}`

(`24576 = 6·8^4`).  This is the corrected Shiu-interface shape at `k = 4`, with an explicit
constant, an explicit logarithmic exponent, and the honest modulus range `q ≤ P^{3/4}`. -/
theorem progRoute2_progressionSum_pow_four {c : ℕ → ℝ} {Kc : ℝ}
    (hc : DivisorBounded c Kc 4) {P : ℝ} (hP : 1 ≤ P) {q r : ℕ} (hq : 0 < q)
    (hrq : Nat.Coprime r q) (hqP : (q : ℝ) ^ 4 ≤ P ^ 3) :
    progressionSum c P q r
      ≤ Kc * 24576 * (P / (Nat.totient q : ℝ)) * (3 + Real.log P) ^ (2 ^ 28) := by
  have h := progRoute2_progressionSum_pow_k hc hP hq hrq hqP
  have hcst : (6 : ℝ) * 8 ^ (4 : ℕ) = 24576 := by norm_num
  rw [hcst] at h
  simpa using h

/-! ## 8. Bridging to the interface's modulus range and logarithmic shape -/

/-- **The modulus range, in interface form.**  `q ≤ P^{1-η}` with `η ≥ 1/4` and `P ≥ 1`
implies the arithmetic range `q^4 ≤ P^3` used throughout this file, because
`(P^{1-η})^4 = P^{4(1-η)} ≤ P^3`.  Here `P ^ (1 - η)` is `Real.rpow`. -/
theorem progRoute2_range_of_rpow {P : ℝ} (hP : 1 ≤ P) {η : ℝ} (hη : 1 / 4 ≤ η) {q : ℕ}
    (hqP : (q : ℝ) ≤ P ^ (1 - η)) : (q : ℝ) ^ 4 ≤ P ^ 3 := by
  have hP0 : (0 : ℝ) ≤ P := le_trans zero_le_one hP
  have h1 : (q : ℝ) ^ (4 : ℕ) ≤ (P ^ (1 - η)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg q) hqP 4
  have h2 : (P ^ (1 - η)) ^ (4 : ℕ) = P ^ ((1 - η) * 4) := by
    rw [← Real.rpow_natCast (P ^ (1 - η)) 4, ← Real.rpow_mul hP0]
    norm_num
  have h3 : P ^ ((1 - η) * 4) ≤ P ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have h4 : P ^ (3 : ℝ) = P ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast P 3]
    norm_num
  calc (q : ℝ) ^ 4 ≤ (P ^ (1 - η)) ^ (4 : ℕ) := h1
    _ = P ^ ((1 - η) * 4) := h2
    _ ≤ P ^ (3 : ℝ) := h3
    _ = P ^ (3 : ℕ) := h4

set_option maxHeartbeats 2000000 in
/-- **The corrected-interface shape, unpacked.**  For a divisor-bounded family of order `k`
with constant `Kc`, Route 2 supplies explicit `C`, `K` and a threshold `P₁ = e^3` with

  `progressionSum c P q r ≤ K · (P/φ(q)) · (log P)^C`

for every `P ≥ P₁`, every `q > 0` with `gcd(r, q) = 1`, and every modulus in the range
`q ≤ P^{1-η}` for any fixed `η ≥ 1/4`.  Here `C = 2^{7k}` and
`K = Kc · (6·8^k) · 2^{2^{7k}}`, and `(log P)^C` is `Real.rpow`.  The passage from
`(3 + log P)^{2^{7k}}` of `progRoute2_progressionSum_pow_k` to
`2^{2^{7k}}·(log P)^{2^{7k}}` is just `3 + log P ≤ 2·log P`, valid because `P ≥ e^3` forces
`log P ≥ 3`; and the modulus range converts by `progRoute2_range_of_rpow`.

This is the statement a `1/4 < η` Shiu-type majorant needs, with every constant explicit
and no asymptotic step anywhere in its derivation. -/
theorem progRoute2_shiu_shape (Kc : ℝ) (k : ℕ) {η : ℝ} (hη : 1 / 4 ≤ η) :
    ∃ C K P₁ : ℝ, ∀ P : ℝ, P₁ ≤ P → ∀ c : ℕ → ℝ, DivisorBounded c Kc k →
      ∀ q r : ℕ, 0 < q → Nat.Coprime r q → (q : ℝ) ≤ P ^ (1 - η) →
        progressionSum c P q r ≤ K * (P / (Nat.totient q : ℝ)) * (Real.log P) ^ C := by
  refine ⟨((2 ^ (7 * k) : ℕ) : ℝ), Kc * (6 * 8 ^ k) * 2 ^ (2 ^ (7 * k)), Real.exp 3, ?_⟩
  intro P hP c hc q r hq hrq hqP
  have hKc : 0 ≤ Kc := progRoute2_divisorBounded_nonneg hc
  have he3 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ)
    linarith
  have hP1 : (1 : ℝ) ≤ P := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hlogP : (3 : ℝ) ≤ Real.log P := by
    have h := Real.log_le_log (Real.exp_pos 3) hP
    rwa [Real.log_exp] at h
  have hrange : (q : ℝ) ^ 4 ≤ P ^ 3 := progRoute2_range_of_rpow hP1 hη hqP
  have hbase := progRoute2_progressionSum_pow_k hc hP1 hq hrq hrange
  have hshift : (3 + Real.log P) ^ (2 ^ (7 * k))
      ≤ 2 ^ (2 ^ (7 * k)) * Real.log P ^ (2 ^ (7 * k)) := by
    calc (3 + Real.log P) ^ (2 ^ (7 * k))
        ≤ (2 * Real.log P) ^ (2 ^ (7 * k)) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = 2 ^ (2 ^ (7 * k)) * Real.log P ^ (2 ^ (7 * k)) := by rw [mul_pow]
  have hrpow : (Real.log P) ^ (((2 ^ (7 * k) : ℕ) : ℝ)) = Real.log P ^ (2 ^ (7 * k)) :=
    Real.rpow_natCast _ _
  rw [hrpow]
  have hPφ : (0 : ℝ) ≤ P / (Nat.totient q : ℝ) :=
    div_nonneg (le_of_lt hP0) (Nat.cast_nonneg _)
  have hcoef : (0 : ℝ) ≤ Kc * (6 * 8 ^ k) := mul_nonneg hKc (by positivity)
  calc progressionSum c P q r
      ≤ Kc * (6 * 8 ^ k) * (P / (Nat.totient q : ℝ))
          * (3 + Real.log P) ^ (2 ^ (7 * k)) := hbase
    _ ≤ Kc * (6 * 8 ^ k) * (P / (Nat.totient q : ℝ))
          * (2 ^ (2 ^ (7 * k)) * Real.log P ^ (2 ^ (7 * k))) :=
        mul_le_mul_of_nonneg_left hshift (mul_nonneg hcoef hPφ)
    _ = Kc * (6 * 8 ^ k) * 2 ^ (2 ^ (7 * k)) * (P / (Nat.totient q : ℝ))
          * Real.log P ^ (2 ^ (7 * k)) := by ring

/-! ## Axiom audit -/

#print axioms progRoute2_quartRoot_pow_four_le
#print axioms progRoute2_le_quartRoot
#print axioms progRoute2_one_le_quartRoot
#print axioms progRoute2_quartRoot_le_self
#print axioms progRoute2_mul_quartRoot_le
#print axioms progRoute2_count_dvd_ap_coprime
#print axioms progRoute2_count_dvd_ap_empty
#print axioms progRoute2_count_dvd_ap_crude
#print axioms progRoute2_coprime_of_mem
#print axioms progRoute2_count_dvd_ap
#print axioms progRoute2_landreau_pow
#print axioms progRoute2_interchange
#print axioms progRoute2_tauSum_div
#print axioms progRoute2_tauSum
#print axioms progRoute2_tau_pow_progression
#print axioms progRoute2_tau_pow_four_progression
#print axioms progRoute2_tau_pow_totient
#print axioms progRoute2_tau_pow_four_totient
#print axioms progRoute2_divisorBounded_nonneg
#print axioms progRoute2_progressionSum_pow_k
#print axioms progRoute2_progressionSum_pow_four
#print axioms progRoute2_range_of_rpow
#print axioms progRoute2_shiu_shape

end Shiu
end Zeta85
end RH
