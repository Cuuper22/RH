/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Brun pure-sieve core: Bonferroni truncation and a Mertens-free product bound

This file plants the two elementary ingredients of Brun's *pure* sieve from which a
Shiu-type `1/log z` saving on rough numbers is born (Route 3 of the corrected Shiu
majorant, following the explicit Bordellès-style treatment, arXiv:2402.12333):

* **Bonferroni inequalities / truncated Möbius.**  The alternating partial sums of
  binomial coefficients satisfy `∑_{j ≤ m} (-1)^j C(t, j) = (-1)^m C(t-1, m)` for
  `t ≥ 1` (`brun_alternating_partial`), so every *even* truncation dominates the
  indicator `[t = 0]` (`brun_bonferroni_even`).  In sieve form: for a finite set of
  primes `P`, the indicator of "`n` is coprime to every `p ∈ P`" is bounded above by
  the inclusion–exclusion sum restricted to subsets `S ⊆ P` of size `≤ 2k`
  (`brun_indicator_le`).  This is Brun's pure sieve, in the subset (squarefree
  divisor) formulation; no Möbius function is needed.

* **A Mertens-free product bound** (`brun_prod_one_sub_le`):
  `∏_{p ≤ z} (1 - 1/p) ≤ 1 / log z` for `z ≥ 2`, obtained by harmonic comparison:
  every `n ≤ z` is `(z+1)`-smooth, so
  `log z ≤ ∑_{n ≤ z} 1/n ≤ ∏_{p ≤ z} (1 - 1/p)⁻¹` via the finite Euler product over
  smooth numbers (`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`)
  and the lower bound `log ≤` harmonic from `Mathlib.NumberTheory.Harmonic.Bounds`.
  No Mertens-type theorem is used.

As a stretch prefix towards the rough-number count in an interval, we also provide the
exact divisor count on `(u, u+v]` (`brun_Ioc_filter_dvd_card`), its real-valued error
form, and the interval-sum interchange (`brun_interval_sieve`) which bounds the number
of `P`-rough integers in `(u, u+v]` by the signed sum of divisor counts over subsets
`S ⊆ P` with `|S| ≤ 2k`.

## References

* V. Brun, *Le crible d'Eratosthène et le théorème de Goldbach* (1919): the pure sieve.
* C. E. Bonferroni, *Teoria statistica delle classi e calcolo delle probabilità* (1936):
  the truncated inclusion–exclusion inequalities.
* O. Bordellès, arXiv:2402.12333: explicit Shiu-type bounds (Route 3 context).
* P. Shiu, *A Brun–Titchmarsh theorem for multiplicative functions*,
  J. reine angew. Math. 313 (1980): the target majorant.
-/

namespace RH
namespace Zeta85
namespace Shiu

open Finset

/-! ## Part (a): Bonferroni / truncated Möbius inequalities -/

/-- **Alternating partial sums of binomial coefficients** (`t ≥ 1`):
`∑_{j=0}^{m} (-1)^j C(t, j) = (-1)^m C(t-1, m)`.  Induction on `m` via Pascal's rule.
This identity is the engine of the Bonferroni inequalities. -/
theorem brun_alternating_partial (t m : ℕ) (ht : 1 ≤ t) :
    ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ j * (t.choose j)
      = (-1 : ℤ) ^ m * ((t - 1).choose m) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, (Nat.succ_pred_eq_of_pos ht).symm⟩
  rw [Nat.add_sub_cancel]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' s m]
    push_cast
    ring

/-- Degenerate case of `brun_alternating_partial`: at `t = 0` the alternating partial
sum equals `1` for every truncation length. -/
theorem brun_alternating_partial_zero (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ j * ((0 : ℕ).choose j) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_eq_zero_of_lt m.succ_pos]
    simp

/-- **Bonferroni inequality, even truncation**: for all `t k : ℕ`,
`[t = 0] ≤ ∑_{j=0}^{2k} (-1)^j C(t, j)`.
For `t ≥ 1` the partial sum equals `C(t-1, 2k) ≥ 0`, and at `t = 0` it equals `1`. -/
theorem brun_bonferroni_even (t k : ℕ) :
    (if t = 0 then (1 : ℤ) else 0)
      ≤ ∑ j ∈ Finset.range (2 * k + 1), (-1 : ℤ) ^ j * (t.choose j) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [if_pos rfl]
    exact (brun_alternating_partial_zero (2 * k)).ge
  · rw [if_neg ht.ne', brun_alternating_partial t (2 * k) ht, pow_mul, neg_one_sq, one_pow,
      one_mul]
    positivity

/-- Summing `(-1)^|S|` over the subsets of `T` of size at most `M` collapses, by
cardinality, to the alternating partial sum of binomial coefficients. -/
theorem brun_sum_powerset_filter_card (T : Finset ℕ) (M : ℕ) :
    ∑ S ∈ T.powerset.filter (fun S => S.card ≤ M), (-1 : ℤ) ^ S.card
      = ∑ j ∈ Finset.range (M + 1), (-1 : ℤ) ^ j * (T.card.choose j) := by
  have hsplit : T.powerset.filter (fun S => S.card ≤ M)
      = (Finset.range (M + 1)).biUnion (fun j => Finset.powersetCard j T) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hsub, hcard⟩
      exact ⟨S.card, hcard, hsub, rfl⟩
    · rintro ⟨j, hj, hsub, rfl⟩
      exact ⟨hsub, hj⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (M + 1)) : Set ℕ)
      (fun j => Finset.powersetCard j T) := by
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun {S} hSa hSb => hab ?_
    rw [← (Finset.mem_powersetCard.mp hSa).2]
    exact (Finset.mem_powersetCard.mp hSb).2
  rw [hsplit, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ S ∈ Finset.powersetCard j T, (-1 : ℤ) ^ S.card
      = ∑ S ∈ Finset.powersetCard j T, (-1 : ℤ) ^ j :=
        Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]
    _ = (Finset.powersetCard j T).card • (-1 : ℤ) ^ j := Finset.sum_const _
    _ = (-1 : ℤ) ^ j * (T.card.choose j) := by
        rw [Finset.card_powersetCard, nsmul_eq_mul, mul_comm]

/-- **Brun's pure sieve, upper-bound form (truncated Möbius over subsets).**
For a finite set `P` of primes and `n ≥ 1`, the indicator of
"`n` is divisible by no `p ∈ P`" is at most the inclusion–exclusion sum truncated at
even level `2k`, running over subsets `S ⊆ P` all of whose elements divide `n`:
`[∀ p ∈ P, p ∤ n] ≤ ∑_{S ⊆ P, |S| ≤ 2k, S ∣ n} (-1)^{|S|}`.
The proof is purely combinatorial (the primality and positivity hypotheses are kept
only for interface faithfulness): with `T := {p ∈ P : p ∣ n}` and `t := |T|`, the
right-hand side is `∑_{j ≤ 2k} (-1)^j C(t, j)` and `brun_bonferroni_even` applies. -/
theorem brun_indicator_le (P : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime) (n : ℕ) (_hn : 1 ≤ n)
    (k : ℕ) :
    (if ∀ p ∈ P, ¬ p ∣ n then (1 : ℤ) else 0)
      ≤ ∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * k ∧ ∀ p ∈ S, p ∣ n),
          (-1 : ℤ) ^ S.card := by
  have hset : P.powerset.filter (fun S => S.card ≤ 2 * k ∧ ∀ p ∈ S, p ∣ n)
      = (P.filter (· ∣ n)).powerset.filter (fun S => S.card ≤ 2 * k) := by
    ext S
    constructor
    · intro hS
      obtain ⟨hpow, hcard, hdvd⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr fun x hx =>
          Finset.mem_filter.mpr ⟨Finset.mem_powerset.mp hpow hx, hdvd x hx⟩, hcard⟩
    · intro hS
      obtain ⟨hpow, hcard⟩ := Finset.mem_filter.mp hS
      have hsub := Finset.mem_powerset.mp hpow
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr fun x hx => (Finset.mem_filter.mp (hsub hx)).1,
         hcard, fun p hp => (Finset.mem_filter.mp (hsub hp)).2⟩
  rw [hset, brun_sum_powerset_filter_card]
  have hiff : (∀ p ∈ P, ¬ p ∣ n) ↔ (P.filter (· ∣ n)).card = 0 :=
    ⟨fun h => Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun x hx => h x hx),
     fun h p hp hdvd => Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp h) hp hdvd⟩
  rw [if_congr hiff rfl rfl]
  exact brun_bonferroni_even _ k

/-! ## Part (b): the Mertens-free product bound `∏_{p ≤ z} (1 - 1/p) ≤ 1 / log z` -/

/-- **Mertens-free product bound via harmonic comparison.**
For `z ≥ 2`: `∏_{p ≤ z} (1 - 1/p) ≤ 1 / log z`.

Proof: each `n` with `1 ≤ n ≤ z` is `(z+1)`-smooth, so by the finite Euler product over
smooth numbers (a convergent geometric series for each prime `p ≤ z`),
`∑_{n ≤ z} 1/n ≤ ∑_{n (z+1)-smooth} 1/n = ∏_{p ≤ z} (1 - 1/p)⁻¹`,
while `log z ≤ ∑_{n ≤ z} 1/n` by the integral comparison recorded in
`Mathlib.NumberTheory.Harmonic.Bounds`.  Inverting (all quantities positive) gives the
claim.  No Mertens-type estimate enters; this is the bound that feeds the `1/log z`
saving of Shiu's majorant on rough numbers. -/
theorem brun_prod_one_sub_le (z : ℕ) (hz : 2 ≤ z) :
    ∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ 1 / Real.log z := by
  rw [← Nat.primesBelow_eq_filter_range]
  -- positivity of every factor, hence of the product
  have hfac_pos : ∀ p ∈ Nat.primesBelow (z + 1), 0 < 1 - 1 / (p : ℝ) := by
    intro p hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have h1 : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one (by linarith)]
      exact hp1
    linarith
  have hB : 0 < ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)) :=
    Finset.prod_pos hfac_pos
  -- the Euler product over `(z+1)`-smooth numbers for the function `n ↦ 1/n`
  have hf₁ : (fun n : ℕ => (1 : ℝ) / n) 1 = 1 := by norm_num
  have hmul : ∀ {a b : ℕ}, Nat.Coprime a b →
      (fun n : ℕ => (1 : ℝ) / n) (a * b)
        = (fun n : ℕ => (1 : ℝ) / n) a * (fun n : ℕ => (1 : ℝ) / n) b := by
    intro a b _
    simp only [Nat.cast_mul, one_div, mul_inv]
  have hsump : ∀ {p : ℕ}, p.Prime →
      Summable (fun e : ℕ => ‖(fun n : ℕ => (1 : ℝ) / n) (p ^ e)‖) := by
    intro p hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hfe : (fun e : ℕ => ‖(fun n : ℕ => (1 : ℝ) / n) (p ^ e)‖)
        = fun e : ℕ => ((1 : ℝ) / p) ^ e := by
      funext e
      simp only [Real.norm_eq_abs, Nat.cast_pow]
      rw [one_div_pow]
      exact abs_of_nonneg (by positivity)
    rw [hfe]
    refine summable_geometric_of_lt_one (by positivity) ?_
    rw [div_lt_one (by linarith)]
    exact hp1
  obtain ⟨-, hHasSum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := fun n : ℕ => (1 : ℝ) / n) hf₁ hmul hsump (z + 1)
  -- each geometric factor sums to `(1 - 1/p)⁻¹`
  have hprodval : ∏ p ∈ Nat.primesBelow (z + 1), (∑' e : ℕ, (fun n : ℕ => (1 : ℝ) / n) (p ^ e))
      = ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))⁻¹ := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have h1 : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one (by linarith)]
      exact hp1
    calc ∑' e : ℕ, (fun n : ℕ => (1 : ℝ) / n) (p ^ e)
        = ∑' e : ℕ, ((1 : ℝ) / p) ^ e := by
          refine tsum_congr fun e => ?_
          simp only [Nat.cast_pow]
          rw [one_div_pow]
      _ = (1 - 1 / (p : ℝ))⁻¹ := tsum_geometric_of_lt_one (by positivity) h1
  rw [hprodval] at hHasSum
  -- pass from the subtype sum to the indicator sum on `ℕ`
  have hInd : HasSum (Set.indicator (Nat.smoothNumbers (z + 1)) (fun n : ℕ => (1 : ℝ) / n))
      (∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))⁻¹) :=
    (hasSum_subtype_iff_indicator
      (f := fun n : ℕ => (1 : ℝ) / n) (s := Nat.smoothNumbers (z + 1))).mp hHasSum
  -- finite comparison over `1 ≤ n ≤ z`
  have hle : ∑ i ∈ Finset.Icc 1 z,
        Set.indicator (Nat.smoothNumbers (z + 1)) (fun n : ℕ => (1 : ℝ) / n) i
      ≤ ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))⁻¹ :=
    sum_le_hasSum (Finset.Icc 1 z)
      (fun i _ => Set.indicator_nonneg (fun m _ => by positivity) i) hInd
  have hIccsum : ∑ i ∈ Finset.Icc 1 z,
        Set.indicator (Nat.smoothNumbers (z + 1)) (fun n : ℕ => (1 : ℝ) / n) i
      = ∑ i ∈ Finset.Icc 1 z, (1 : ℝ) / i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    exact Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt h1 (Nat.lt_succ_of_le h2)) _
  -- the harmonic lower bound `log z ≤ ∑_{n ≤ z} 1/n`
  have hharm : Real.log (z : ℝ) ≤ ∑ i ∈ Finset.Icc 1 z, (1 : ℝ) / i := by
    have h1 := log_le_harmonic_floor (z : ℝ) (Nat.cast_nonneg z)
    rw [Nat.floor_natCast] at h1
    refine h1.trans (le_of_eq ?_)
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl fun i _ => (one_div _).symm
  -- assemble and invert
  have hkey : Real.log (z : ℝ)
      ≤ (∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    calc Real.log (z : ℝ) ≤ ∑ i ∈ Finset.Icc 1 z, (1 : ℝ) / i := hharm
      _ = ∑ i ∈ Finset.Icc 1 z,
            Set.indicator (Nat.smoothNumbers (z + 1)) (fun n : ℕ => (1 : ℝ) / n) i :=
          hIccsum.symm
      _ ≤ ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))⁻¹ := hle
  have hlogpos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hz)
  rw [le_div_iff₀ hlogpos]
  calc (∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))) * Real.log (z : ℝ)
      ≤ (∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)))
          * (∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hkey hB.le
    _ = 1 := mul_inv_cancel₀ hB.ne'

/-! ## Part (c), stretch prefix: divisor counts in an interval and the sieve interchange -/

/-- Exact count of multiples of `d` in the half-open interval `(u, u+v]`:
`#{n ∈ (u, u+v] : d ∣ n} = ⌊(u+v)/d⌋ - ⌊u/d⌋` (natural-number division). -/
theorem brun_Ioc_filter_dvd_card (u v d : ℕ) :
    ((Finset.Ioc u (u + v)).filter (fun x => d ∣ x)).card = (u + v) / d - u / d := by
  have hdisj : Disjoint (Finset.Ioc 0 u) (Finset.Ioc u (u + v)) :=
    Finset.disjoint_left.mpr fun x hx hx' =>
      absurd (Finset.mem_Ioc.mp hx).2 (not_le.mpr (Finset.mem_Ioc.mp hx').1)
  have h := Nat.Ioc_filter_dvd_card_eq_div (u + v) d
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le u) (Nat.le_add_right u v),
    Finset.filter_union,
    Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    Nat.Ioc_filter_dvd_card_eq_div u d] at h
  omega

/-- Cast comparison for natural division, lower bound: `m/d < ⌊m/d⌋ + 1` in `ℝ`. -/
theorem brun_cast_div_lt_succ (m d : ℕ) (hd : 0 < d) :
    (m : ℝ) / (d : ℝ) < ((m / d : ℕ) : ℝ) + 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_iff₀ hd0]
  have hnat : m < (m / d + 1) * d := by
    have hmod : m % d < d := Nat.mod_lt _ hd
    have hdm : d * (m / d) + m % d = m := Nat.div_add_mod m d
    calc m = d * (m / d) + m % d := hdm.symm
      _ < d * (m / d) + d := by omega
      _ = (m / d + 1) * d := by ring
  exact_mod_cast hnat

/-- The count of multiples of `d` in `(u, u+v]` differs from `v/d` by at most `1`
(real-valued form of `brun_Ioc_filter_dvd_card`). -/
theorem brun_Ioc_filter_dvd_card_error (u v d : ℕ) (hd : 0 < d) :
    |((((Finset.Ioc u (u + v)).filter (fun x => d ∣ x)).card : ℝ)) - (v : ℝ) / (d : ℝ)| ≤ 1 := by
  have hle : u / d ≤ (u + v) / d := Nat.div_le_div_right (Nat.le_add_right u v)
  have hupA : (((u + v) / d : ℕ) : ℝ) ≤ ((u + v : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hupB : ((u / d : ℕ) : ℝ) ≤ (u : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hlowA : ((u + v : ℕ) : ℝ) / (d : ℝ) < (((u + v) / d : ℕ) : ℝ) + 1 :=
    brun_cast_div_lt_succ (u + v) d hd
  have hlowB : (u : ℝ) / (d : ℝ) < ((u / d : ℕ) : ℝ) + 1 :=
    brun_cast_div_lt_succ u d hd
  have hsplit : ((u + v : ℕ) : ℝ) / (d : ℝ) = (u : ℝ) / (d : ℝ) + (v : ℝ) / (d : ℝ) := by
    push_cast
    rw [add_div]
  rw [brun_Ioc_filter_dvd_card, Nat.cast_sub hle, abs_le]
  constructor
  · linarith
  · linarith

/-- **Interval-sum interchange for the truncated sieve.**  The number of `P`-rough
integers in `(u, u+v]` is at most the signed sum, over the subsets `S ⊆ P` with
`|S| ≤ 2k`, of the counts of multiples of `∏ S` in the interval.  This is the pointwise
Bonferroni bound `brun_indicator_le` summed over the interval, with the order of
summation exchanged. -/
theorem brun_interval_sieve (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (u v k : ℕ) :
    (((Finset.Ioc u (u + v)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℤ)
      ≤ ∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * k),
          (-1 : ℤ) ^ S.card
            * (((Finset.Ioc u (u + v)).filter (fun m => S.prod id ∣ m)).card : ℤ) := by
  calc (((Finset.Ioc u (u + v)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℤ)
      = ∑ m ∈ Finset.Ioc u (u + v), (if ∀ p ∈ P, ¬ p ∣ m then (1 : ℤ) else 0) :=
        Finset.natCast_card_filter _ _
    _ ≤ ∑ m ∈ Finset.Ioc u (u + v),
          ∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * k ∧ ∀ p ∈ S, p ∣ m),
            (-1 : ℤ) ^ S.card :=
        Finset.sum_le_sum fun m hm =>
          brun_indicator_le P hP m (by have h := (Finset.mem_Ioc.mp hm).1; omega) k
    _ = ∑ m ∈ Finset.Ioc u (u + v),
          ∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * k),
            (if ∀ p ∈ S, p ∣ m then (-1 : ℤ) ^ S.card else 0) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Finset.filter_filter, Finset.sum_filter]
    _ = ∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * k),
          ∑ m ∈ Finset.Ioc u (u + v),
            (if ∀ p ∈ S, p ∣ m then (-1 : ℤ) ^ S.card else 0) := Finset.sum_comm
    _ = ∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * k),
          (-1 : ℤ) ^ S.card
            * (((Finset.Ioc u (u + v)).filter (fun m => S.prod id ∣ m)).card : ℤ) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        have hSsub : S ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
        have hcond : ∀ m : ℕ, (∀ p ∈ S, p ∣ m) ↔ S.prod id ∣ m := by
          intro m
          constructor
          · intro h
            exact Finset.prod_primes_dvd m (fun p hp => (hP p (hSsub hp)).prime) h
          · intro h p hp
            exact dvd_trans (Finset.dvd_prod_of_mem id hp) h
        calc ∑ m ∈ Finset.Ioc u (u + v), (if ∀ p ∈ S, p ∣ m then (-1 : ℤ) ^ S.card else 0)
            = ∑ m ∈ Finset.Ioc u (u + v),
                (if S.prod id ∣ m then (-1 : ℤ) ^ S.card else 0) :=
              Finset.sum_congr rfl fun m _ => if_congr (hcond m) rfl rfl
          _ = ∑ m ∈ (Finset.Ioc u (u + v)).filter (fun m => S.prod id ∣ m),
                (-1 : ℤ) ^ S.card := by rw [Finset.sum_filter]
          _ = ((Finset.Ioc u (u + v)).filter (fun m => S.prod id ∣ m)).card
                • (-1 : ℤ) ^ S.card := Finset.sum_const _
          _ = (-1 : ℤ) ^ S.card
                * (((Finset.Ioc u (u + v)).filter (fun m => S.prod id ∣ m)).card : ℤ) := by
              rw [nsmul_eq_mul, mul_comm]

/-- A signed rounding step: if `|x - y| ≤ 1` then `(-1)^c x ≤ (-1)^c y + 1`. -/
theorem brun_signed_error_le {x y : ℝ} (c : ℕ) (h : |x - y| ≤ 1) :
    (-1 : ℝ) ^ c * x ≤ (-1 : ℝ) ^ c * y + 1 := by
  have h1 : (-1 : ℝ) ^ c * (x - y) ≤ 1 := by
    calc (-1 : ℝ) ^ c * (x - y) ≤ |(-1 : ℝ) ^ c * (x - y)| := le_abs_self _
      _ = |(-1 : ℝ) ^ c| * |x - y| := abs_mul _ _
      _ = |x - y| := by rw [abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ 1 := h
  have h2 : (-1 : ℝ) ^ c * x - (-1 : ℝ) ^ c * y ≤ 1 := by
    have hexp : (-1 : ℝ) ^ c * x - (-1 : ℝ) ^ c * y = (-1 : ℝ) ^ c * (x - y) := by ring
    rw [hexp]
    exact h1
  linarith

/-- **Rough-number count in an interval, with explicit truncation error.**
For a finite set `P` of primes, the number of `P`-rough integers in `(u, u+v]` is at
most the signed density sum `∑_{S ⊆ P, |S| ≤ 2k} (-1)^{|S|} · v/∏S` plus one unit of
rounding error per subset, i.e. plus `#{S ⊆ P : |S| ≤ 2k}`.  The identification of the
signed main term with `v · ∏_{p ∈ P} (1 - 1/p)` up to the Bonferroni tail is the next,
separate step of the Route 3 assembly (it consumes `brun_prod_one_sub_le`). -/
theorem brun_rough_count_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (u v k : ℕ) :
    (((Finset.Ioc u (u + v)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ)
      ≤ (∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * k),
            (-1 : ℝ) ^ S.card * ((v : ℝ) / ((S.prod id : ℕ) : ℝ)))
          + ((P.powerset.filter (fun S => S.card ≤ 2 * k)).card : ℝ) := by
  have hR : (((Finset.Ioc u (u + v)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ)
      ≤ ∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * k),
          (-1 : ℝ) ^ S.card
            * (((Finset.Ioc u (u + v)).filter (fun m => S.prod id ∣ m)).card : ℝ) := by
    exact_mod_cast brun_interval_sieve P hP u v k
  refine hR.trans ?_
  have hcardsum : ((P.powerset.filter (fun S => S.card ≤ 2 * k)).card : ℝ)
      = ∑ _S ∈ P.powerset.filter (fun S => S.card ≤ 2 * k), (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcardsum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S hS => ?_
  have hSsub : S ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hD : 0 < S.prod id := Finset.prod_pos fun p hp => (hP p (hSsub hp)).pos
  exact brun_signed_error_le S.card (brun_Ioc_filter_dvd_card_error u v (S.prod id) hD)

end Shiu
end Zeta85
end RH
