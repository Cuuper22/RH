/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Shiu/AllTheta.lean — Route 2 assembly: an ALL-θ short-interval bound for the fourth
moment of the divisor function, conditional on a single named Landreau-type hypothesis.

**Main theorem** (`allTheta_tau_pow_four_short_interval`).  Assume the Landreau-type small-divisor
inequality `hL` with constants `(A, B)`:

    τ(n)^4 ≤ A · ∑_{d ∣ n, d^4 ≤ n} τ(d)^B        (τ = `ArithmeticFunction.sigma 0`).

Then for every fixed `θ` with `1/4 < θ` (in particular for the whole classical range
`1/2 < θ < 1`, with *no* θ-wall), every `x ≥ allTheta_x₀ θ` and every interval length `y` with
`x^θ ≤ y ≤ x`:

    ∑_{x < n ≤ x+y} τ(n)^4 ≤ A · 2^(2^B + 1) · y · (1 + log x)^(2^B).

All constants are explicit: `E = 2^B`, `C = A · 2^(2^B + 1)` (independent of θ), and the
threshold is `allTheta_x₀ θ = max 2 ⌈2^(1/(θ − 1/4))⌉₊`, which is exactly what makes
`(2x)^(1/4) ≤ x^θ` hold (from `x^(θ − 1/4) ≥ 2`).  The exponent `E = 2^B` is *not* sharp; the
point of this unit is the absence of any restriction `θ > θ₀ > 1/4`.

**Method** (interchange / small-divisor method for short-interval divisor moments).  Insert `hL`
pointwise and swap the double sum over pairs `(n, d)`: every divisor `d` that survives the filter
satisfies `d^4 ≤ n ≤ x + y ≤ 2x`, so `d ≤ D := √√(2x)`, and

    ∑_{x<n≤x+y} τ(n)^4 ≤ A · ∑_{d ≤ D} τ(d)^B · #{n ∈ (x, x+y] : d ∣ n}.

The multiples count is `(x+y)/d − x/d ≤ y/d + 1`; the `y/d` part is controlled by the summatory
bound `∑_{d ≤ N} τ(d)^B/d ≤ (1 + log N)^(2^B)` (proved below by induction on `B` via the
hyperbola reindexing `∑_{m ≤ N} ∑_{de = m} = ∑_{d ≤ N} ∑_{e ≤ N/d}`, submultiplicativity of τ,
and the harmonic-sum bound `∑_{e ≤ L} 1/e ≤ 1 + log L`), while the `+1` part is absorbed since
`D ≤ (2x)^(1/4) ≤ x^θ ≤ y` — this is the only place θ and `x₀(θ)` enter, and it is where the
classical θ-wall disappears.

**Conditionality.**  The ONLY named hypothesis is `hL` (Landreau's inequality with small
divisors `d^4 ≤ n`); it is realizable with explicit constants `(A, B) = (4096, 28)` by the
max-block argument — sibling unit U8 (branch `shiu/u08-landreau`) proves exactly this as
`landreau_tau_pow_four_le`: `τ(n)^4 ≤ 4096 · ∑_{d ∣ n, d^4 ≤ n} τ(d)^28`, following Lay's
constants — and units never import each other, so it enters here as a hypothesis and the
coordinator wires the two.  Everything downstream of `hL` in this file is unconditional Lean:
no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.

References:
* B. Landreau, *Majorations de fonctions arithmétiques en moyenne sur des ensembles de faible
  densité*, Sém. Théorie des Nombres de Bordeaux (1989) — the small-divisor inequality.
* A. Lay, arXiv:1711.05924 — short-interval divisor moments via the small-divisor method.
* P. Shiu, *A Brun–Titchmarsh theorem for multiplicative functions* — the classical θ-restricted
  route this unit replaces.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

noncomputable section

namespace RH
namespace Zeta85
namespace Shiu

/-! ## Counting multiples in a short interval -/

/-- Exactly `(x+y)/d − x/d` integers in `(x, x+y]` are multiples of `d`. -/
private lemma allTheta_card_multiples (d x y : ℕ) :
    ((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card = (x + y) / d - x / d := by
  have hsplit : Finset.Ioc 0 x ∪ Finset.Ioc x (x + y) = Finset.Ioc 0 (x + y) :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) (Nat.le_add_right x y)
  have hdisj : Disjoint ((Finset.Ioc 0 x).filter (fun n => d ∣ n))
      ((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)) :=
    Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)
  have hcard : (x + y) / d
      = x / d + ((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div (x + y) d, ← hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint hdisj, Nat.Ioc_filter_dvd_card_eq_div]
  omega

/-- The number of multiples of `d ≥ 1` in `(x, x+y]` is at most `y/d + 1` (real division). -/
private lemma allTheta_card_multiples_le (d x y : ℕ) (hd : 0 < d) :
    (((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card : ℝ) ≤ (y : ℝ) / d + 1 := by
  have h2 : (x + y) / d ≤ x / d + (y / d + 1) := by
    rw [Nat.add_div hd]
    split <;> omega
  have h1 : ((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card ≤ y / d + 1 := by
    rw [allTheta_card_multiples]
    calc (x + y) / d - x / d ≤ x / d + (y / d + 1) - x / d := Nat.sub_le_sub_right h2 _
      _ = y / d + 1 := Nat.add_sub_cancel_left (x / d) (y / d + 1)
  calc (((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card : ℝ)
      ≤ ((y / d + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((y / d : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (y : ℝ) / d + 1 := by
        have h3 : ((y / d : ℕ) : ℝ) ≤ (y : ℝ) / (d : ℝ) := Nat.cast_div_le
        linarith

/-- Absorb the count bound: `c · t ≤ (y + D) · (t/d)` whenever `c ≤ y/d + 1`, `0 ≤ t` and
`1 ≤ d ≤ D` — the `y/d` part directly, the `+1` part via `t = (t/d)·d ≤ (t/d)·D`. -/
private lemma allTheta_weight_le (c t : ℝ) (y D d : ℕ) (hd : 1 ≤ d) (hdD : d ≤ D)
    (ht : 0 ≤ t) (hc : c ≤ (y : ℝ) / d + 1) :
    c * t ≤ ((y : ℝ) + D) * (t / d) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq0 : (0 : ℝ) ≤ t / d := div_nonneg ht hdpos.le
  have h1 : t = t / d * d := (div_mul_cancel₀ t (ne_of_gt hdpos)).symm
  have h2 : t / d * (d : ℝ) ≤ t / d * (D : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hdD) hq0
  calc c * t ≤ ((y : ℝ) / d + 1) * t := mul_le_mul_of_nonneg_right hc ht
    _ = (y : ℝ) * (t / d) + t := by ring
    _ = (y : ℝ) * (t / d) + t / d * d := by rw [← h1]
    _ ≤ (y : ℝ) * (t / d) + t / d * D := by linarith
    _ = ((y : ℝ) + D) * (t / d) := by ring

/-! ## Harmonic and logarithm helpers -/

/-- Harmonic-sum bound `∑_{1 ≤ e ≤ L} 1/e ≤ 1 + log L`, from
`Mathlib.NumberTheory.Harmonic.Bounds`. -/
private lemma allTheta_harmonic_le (L : ℕ) :
    ∑ e ∈ Finset.Icc 1 L, (1 : ℝ) / e ≤ 1 + Real.log L := by
  have h1 : ∑ e ∈ Finset.Icc 1 L, (1 : ℝ) / e = ((harmonic L : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp [one_div]
  rw [h1]
  exact_mod_cast harmonic_le_one_add_log L

/-- `log` is monotone on the (cast) naturals, with no positivity side condition. -/
private lemma allTheta_log_nat_mono {a b : ℕ} (h : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

private lemma allTheta_one_add_log_nonneg (n : ℕ) : (0 : ℝ) ≤ 1 + Real.log n := by
  have := Real.log_natCast_nonneg n
  linarith

/-! ## Submultiplicativity of the divisor function -/

/-- `τ(ab) ≤ τ(a)·τ(b)`, via `Nat.divisors_mul` and `Finset.card_mul_le`. -/
private lemma allTheta_card_divisors_mul_le (a b : ℕ) :
    (((a * b).divisors.card : ℕ) : ℝ) ≤ (a.divisors.card : ℝ) * (b.divisors.card : ℝ) := by
  have h : (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
    rw [Nat.divisors_mul]
    exact Finset.card_mul_le
  exact_mod_cast h

private lemma allTheta_card_divisorsAntidiagonal (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]

/-! ## The hyperbola (Dirichlet) reindexing -/

/-- Hyperbola reindexing: summing over `m ≤ N` and factorizations `de = m` is summing over
`d ≤ N`, `e ≤ N/d`. -/
private lemma allTheta_hyperbola (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ m.divisorsAntidiagonal, F p.1 p.2
      = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), F d e := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun z => ⟨z.2.1, z.2.2⟩) (fun z => ⟨z.1 * z.2, (z.1, z.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, d, e⟩ hz
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hz ⊢
    obtain ⟨⟨-, hmN⟩, hde, hm0⟩ := hz
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hde
      exact hm0 hde.symm
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hde
      exact hm0 hde.symm
    refine ⟨⟨Nat.pos_of_ne_zero hd0, ?_⟩, Nat.pos_of_ne_zero he0, ?_⟩
    · calc d ≤ d * e := Nat.le_mul_of_pos_right d (Nat.pos_of_ne_zero he0)
        _ = m := hde
        _ ≤ N := hmN
    · rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd0)]
      calc e * d = d * e := Nat.mul_comm e d
        _ = m := hde
        _ ≤ N := hmN
  · rintro ⟨d, e⟩ hz
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hz
    obtain ⟨⟨hd1, hdN⟩, he1, heN⟩ := hz
    have hde0 : d * e ≠ 0 := Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hd1)
      (Nat.pos_iff_ne_zero.mp he1)
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hde0, ?_⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hde0⟩⟩
    calc d * e = e * d := Nat.mul_comm d e
      _ ≤ N := (Nat.le_div_iff_mul_le hd1).mp heN
  · rintro ⟨m, d, e⟩ hz
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hz
    obtain ⟨-, hde, -⟩ := hz
    subst hde
    rfl
  · rintro ⟨d, e⟩ _
    rfl
  · rintro ⟨m, d, e⟩ _
    rfl

/-! ## The summatory bound `∑_{d ≤ N} τ(d)^B / d ≤ (1 + log N)^(2^B)` -/

/-- Summatory bound for powers of the divisor function, weighted by `1/d`:
`∑_{d ≤ N} τ(d)^B / d ≤ (1 + log N)^(2^B)`.  Induction on `B`: the case `B = 0` is the harmonic
bound, and the step combines submultiplicativity `τ(de) ≤ τ(d)τ(e)` with the hyperbola
reindexing, doubling the exponent.  (This is the `∑_{m ≤ N} (ζ^K) m / m ≤ (1 + log N)^K` ladder
specialized along `τ^B ≤ ζ^(2^B)`; here it is proved directly, unconditionally.) -/
private lemma allTheta_sum_tau_pow_div_le : ∀ B N : ℕ,
    ∑ d ∈ Finset.Icc 1 N, ((d.divisors.card : ℕ) : ℝ) ^ B / d
      ≤ (1 + Real.log N) ^ 2 ^ B := by
  intro B
  induction B with
  | zero =>
    intro N
    simp only [pow_zero, pow_one]
    exact allTheta_harmonic_le N
  | succ B ih =>
    intro N
    have step1 : ∀ d ∈ Finset.Icc 1 N,
        ((d.divisors.card : ℕ) : ℝ) ^ (B + 1) / d
          = ∑ _p ∈ d.divisorsAntidiagonal, ((d.divisors.card : ℕ) : ℝ) ^ B / d := by
      intro d _
      rw [Finset.sum_const, allTheta_card_divisorsAntidiagonal, nsmul_eq_mul, pow_succ]
      ring
    calc ∑ d ∈ Finset.Icc 1 N, ((d.divisors.card : ℕ) : ℝ) ^ (B + 1) / d
        = ∑ d ∈ Finset.Icc 1 N, ∑ _p ∈ d.divisorsAntidiagonal,
            ((d.divisors.card : ℕ) : ℝ) ^ B / d := Finset.sum_congr rfl step1
      _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ p ∈ d.divisorsAntidiagonal,
            (((p.1.divisors.card : ℕ) : ℝ) ^ B / p.1)
              * (((p.2.divisors.card : ℕ) : ℝ) ^ B / p.2) := by
          refine Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hd
          have hmem := Nat.mem_divisorsAntidiagonal.mp hp
          obtain ⟨hde, hd0⟩ := hmem
          have hp1 : 0 < p.1 := Nat.pos_of_ne_zero fun h => hd0 (by rw [← hde, h, zero_mul])
          have hp2 : 0 < p.2 := Nat.pos_of_ne_zero fun h => hd0 (by rw [← hde, h, mul_zero])
          have hsub : ((d.divisors.card : ℕ) : ℝ)
              ≤ (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) := by
            rw [← hde]
            exact allTheta_card_divisors_mul_le p.1 p.2
          have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
          calc ((d.divisors.card : ℕ) : ℝ) ^ B / d
              ≤ ((p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ)) ^ B / d :=
                div_le_div_of_nonneg_right
                  (pow_le_pow_left₀ (Nat.cast_nonneg _) hsub B) hdpos.le
            _ = (((p.1.divisors.card : ℕ) : ℝ) ^ B / p.1)
                  * (((p.2.divisors.card : ℕ) : ℝ) ^ B / p.2) := by
                rw [← hde, mul_pow, div_mul_div_comm]
                push_cast
                ring
      _ = ∑ a ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / a),
            (((a.divisors.card : ℕ) : ℝ) ^ B / a) * (((e.divisors.card : ℕ) : ℝ) ^ B / e) :=
          allTheta_hyperbola N fun a e =>
            (((a.divisors.card : ℕ) : ℝ) ^ B / a) * (((e.divisors.card : ℕ) : ℝ) ^ B / e)
      _ ≤ ∑ a ∈ Finset.Icc 1 N,
            (((a.divisors.card : ℕ) : ℝ) ^ B / a) * (1 + Real.log N) ^ 2 ^ B := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [← Finset.mul_sum]
          have h1 : ∑ e ∈ Finset.Icc 1 (N / a), ((e.divisors.card : ℕ) : ℝ) ^ B / e
              ≤ (1 + Real.log (N / a : ℕ)) ^ 2 ^ B := ih (N / a)
          have h2 : (1 + Real.log (N / a : ℕ)) ^ 2 ^ B ≤ (1 + Real.log N) ^ 2 ^ B := by
            refine pow_le_pow_left₀ (allTheta_one_add_log_nonneg _) ?_ _
            have := allTheta_log_nat_mono (Nat.div_le_self N a)
            linarith
          have h3 : (0 : ℝ) ≤ ((a.divisors.card : ℕ) : ℝ) ^ B / a := by positivity
          exact mul_le_mul_of_nonneg_left (h1.trans h2) h3
      _ = (∑ a ∈ Finset.Icc 1 N, ((a.divisors.card : ℕ) : ℝ) ^ B / a)
            * (1 + Real.log N) ^ 2 ^ B := by
          rw [← Finset.sum_mul]
      _ ≤ (1 + Real.log N) ^ 2 ^ B * (1 + Real.log N) ^ 2 ^ B :=
          mul_le_mul_of_nonneg_right (ih N)
            (pow_nonneg (allTheta_one_add_log_nonneg N) _)
      _ = (1 + Real.log N) ^ 2 ^ (B + 1) := by
          rw [← pow_add]
          congr 1
          rw [pow_succ, mul_two]

/-! ## The threshold `x₀(θ)` and the divisor cutoff `D ≤ y` -/

/-- Explicit threshold `x₀(θ) = max 2 ⌈2^(1/(θ − 1/4))⌉₊`: for `x ≥ x₀(θ)` one has
`x^(θ − 1/4) ≥ 2`, hence `(2x)^(1/4) ≤ x^θ`.  For `θ ≥ 1/2` this is at most `⌈4⌉₊ = 4`. -/
noncomputable def allTheta_x₀ (θ : ℝ) : ℕ := max 2 ⌈(2 : ℝ) ^ (θ - 1 / 4)⁻¹⌉₊

/-- The divisor cutoff `D = ⌊√⌊√(2x)⌋⌋` satisfies `D ≤ (2x)^(1/4) ≤ x^θ ≤ y`: the small
divisors fit inside the interval length.  This is the only use of `θ > 1/4` and `x ≥ x₀(θ)`. -/
private lemma allTheta_sqrt_sqrt_le (θ : ℝ) (hθ : 1 / 4 < θ) (x y : ℕ)
    (hx : allTheta_x₀ θ ≤ x) (hy : (x : ℝ) ^ θ ≤ (y : ℝ)) :
    ((Nat.sqrt (Nat.sqrt (2 * x)) : ℕ) : ℝ) ≤ y := by
  have hs : 0 < θ - 1 / 4 := by linarith
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : (0 : ℝ) < x := by
    have : 0 < x := lt_of_lt_of_le (by norm_num) hx2
    exact_mod_cast this
  have hxc : (2 : ℝ) ^ (θ - 1 / 4)⁻¹ ≤ (x : ℝ) := by
    have h1 : (⌈(2 : ℝ) ^ (θ - 1 / 4)⁻¹⌉₊ : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hx
    exact le_trans (Nat.le_ceil _) h1
  have hkey : (2 : ℝ) ≤ (x : ℝ) ^ (θ - 1 / 4) := by
    have h1 : ((2 : ℝ) ^ (θ - 1 / 4)⁻¹) ^ (θ - 1 / 4) ≤ (x : ℝ) ^ (θ - 1 / 4) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hxc hs.le
    rwa [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), inv_mul_cancel₀ hs.ne',
      Real.rpow_one] at h1
  set D := Nat.sqrt (Nat.sqrt (2 * x)) with hD
  have hD4 : D ^ 4 ≤ 2 * x := by
    have h1 : D * D ≤ Nat.sqrt (2 * x) := Nat.sqrt_le _
    have h2 : Nat.sqrt (2 * x) * Nat.sqrt (2 * x) ≤ 2 * x := Nat.sqrt_le _
    calc D ^ 4 = (D * D) * (D * D) := by ring
      _ ≤ Nat.sqrt (2 * x) * Nat.sqrt (2 * x) := Nat.mul_le_mul h1 h1
      _ ≤ 2 * x := h2
  have hD14 : (D : ℝ) ≤ ((2 * x : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (((D : ℝ) ^ (4 : ℕ)) : ℝ) ^ ((1 : ℝ) / 4)
        ≤ (((2 * x : ℕ)) : ℝ) ^ ((1 : ℝ) / 4) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      exact_mod_cast hD4
    calc (D : ℝ) = ((D : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast (D : ℝ) 4, ← Real.rpow_mul (Nat.cast_nonneg D),
            show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one]
      _ ≤ _ := h1
  have hfinal : ((2 * x : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ θ := by
    have hcast : ((2 * x : ℕ) : ℝ) = 2 * (x : ℝ) := by push_cast; ring
    rw [hcast, Real.mul_rpow (by norm_num) hxpos.le]
    have h214 : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hsplit : (x : ℝ) ^ θ = (x : ℝ) ^ (θ - 1 / 4) * (x : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    rw [hsplit]
    have hx14 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hxpos.le _
    calc (2 : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((1 : ℝ) / 4)
        ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_right h214 hx14
      _ ≤ (x : ℝ) ^ (θ - 1 / 4) * (x : ℝ) ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hkey hx14
  calc (D : ℝ) ≤ ((2 * x : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := hD14
    _ ≤ (x : ℝ) ^ θ := hfinal
    _ ≤ y := hy

/-! ## Main theorem -/

/-- **All-θ short-interval bound for the fourth moment of the divisor function** (Route 2
assembly; interchange/small-divisor method for short-interval divisor moments).

Conditional on the single named Landreau-type hypothesis `hL` — the small-divisor inequality
`τ(n)^4 ≤ A · ∑_{d ∣ n, d^4 ≤ n} τ(d)^B` (Landreau 1989; cf. Lay, arXiv:1711.05924), which is
realizable with the explicit constants `(A, B) = (4096, 28)` by the max-block argument and is
proved unconditionally by sibling unit U8 (`landreau_tau_pow_four_le`, branch
`shiu/u08-landreau`) — for every `θ > 1/4` (so in particular the entire
classical range `1/2 < θ < 1`: no θ-wall), every `x ≥ allTheta_x₀ θ`, and every interval length
`y` with `x^θ ≤ y ≤ x`:

    ∑_{x < n ≤ x+y} τ(n)^4 ≤ A · 2^(2^B + 1) · y · (1 + log x)^(2^B),

with fully explicit constants `C = A · 2^(2^B + 1)` and `E = 2^B` (the exponent `E` enters via
`τ(d)^B ≤ (ζ^(2^B)) d` pointwise; here the equivalent summatory ladder is proved directly).
Everything besides `hL` is proved in this file. -/
theorem allTheta_tau_pow_four_short_interval
    (A B : ℕ) (θ : ℝ) (hθ : 1 / 4 < θ)
    (hL : ∀ n : ℕ, 1 ≤ n →
      ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 4
        ≤ (A : ℝ) * ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)),
            ((ArithmeticFunction.sigma 0 d : ℕ) : ℝ) ^ B)
    (x y : ℕ) (hx : allTheta_x₀ θ ≤ x) (hylo : (x : ℝ) ^ θ ≤ (y : ℝ)) (hyhi : y ≤ x) :
    ∑ n ∈ Finset.Ioc x (x + y), ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 4
      ≤ (A : ℝ) * 2 ^ (2 ^ B + 1) * (y : ℝ) * (1 + Real.log x) ^ 2 ^ B := by
  classical
  set D := Nat.sqrt (Nat.sqrt (2 * x)) with hD
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast le_trans (by norm_num) hx2
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hDy : (D : ℝ) ≤ (y : ℝ) := allTheta_sqrt_sqrt_le θ hθ x y hx hylo
  -- Step 1: pointwise Landreau inequality, then enlarge the divisor range to `Icc 1 D`.
  have step1 : ∑ n ∈ Finset.Ioc x (x + y), ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 4
      ≤ (A : ℝ) * ∑ n ∈ Finset.Ioc x (x + y),
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n),
            ((d.divisors.card : ℕ) : ℝ) ^ B := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hxn, hnxy⟩ := Finset.mem_Ioc.mp hn
    have hn1 : 1 ≤ n := by omega
    refine (hL n hn1).trans ?_
    simp only [ArithmeticFunction.sigma_zero_apply]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg A)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, hn0⟩, hd4⟩ := hd
      have hd4n : d ^ 4 ≤ n := by exact_mod_cast hd4
      have hd1 : 0 < d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hdvd, hn0⟩)
      have hdD : d ≤ D := by
        rw [hD, Nat.le_sqrt, Nat.le_sqrt]
        calc d * d * (d * d) = d ^ 4 := by ring
          _ ≤ n := hd4n
          _ ≤ x + y := hnxy
          _ ≤ 2 * x := by omega
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hd1, hdD⟩, hdvd⟩
    · intro i _ _
      positivity
  -- Step 2: interchange the double sum (the pairs `(n, d)` with `d ∣ n`).
  have step2 : ∑ n ∈ Finset.Ioc x (x + y),
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n), ((d.divisors.card : ℕ) : ℝ) ^ B
      = ∑ d ∈ Finset.Icc 1 D,
          ((((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card : ℕ) : ℝ)
            * ((d.divisors.card : ℕ) : ℝ) ^ B := by
    have hcond : ∀ (n d : ℕ),
        n ∈ Finset.Ioc x (x + y) ∧ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n)
          ↔ n ∈ (Finset.Ioc x (x + y)).filter (fun n => d ∣ n) ∧ d ∈ Finset.Icc 1 D := by
      intro n d
      simp only [Finset.mem_filter]
      tauto
    rw [Finset.sum_comm' hcond]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  -- The weighted summatory quantity.
  set S : ℝ := ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) ^ B / d with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun d _ => by positivity
  -- Step 3: multiples count `≤ y/d + 1`, and `τ(d)^B ≤ D · τ(d)^B/d` for the `+1` part.
  have step3 : ∑ d ∈ Finset.Icc 1 D,
        ((((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card : ℕ) : ℝ)
          * ((d.divisors.card : ℕ) : ℝ) ^ B
      ≤ (2 * (y : ℝ)) * S := by
    have hstep : ∑ d ∈ Finset.Icc 1 D,
          ((((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card : ℕ) : ℝ)
            * ((d.divisors.card : ℕ) : ℝ) ^ B
        ≤ ∑ d ∈ Finset.Icc 1 D,
            ((y : ℝ) + D) * (((d.divisors.card : ℕ) : ℝ) ^ B / d) := by
      refine Finset.sum_le_sum fun d hd => ?_
      obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
      have ht0 : (0 : ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) ^ B := by positivity
      exact allTheta_weight_le _ _ y D d hd1 hdD ht0 (allTheta_card_multiples_le d x y hd1)
    calc ∑ d ∈ Finset.Icc 1 D,
          ((((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card : ℕ) : ℝ)
            * ((d.divisors.card : ℕ) : ℝ) ^ B
        ≤ ∑ d ∈ Finset.Icc 1 D,
            ((y : ℝ) + D) * (((d.divisors.card : ℕ) : ℝ) ^ B / d) := hstep
      _ = ((y : ℝ) + D) * S := by rw [← Finset.mul_sum]
      _ ≤ (2 * (y : ℝ)) * S := by
          refine mul_le_mul_of_nonneg_right ?_ hS0
          linarith
  -- Step 4: the summatory bound and `log D ≤ 1 + log x`.
  have hSbound : S ≤ (1 + Real.log D) ^ 2 ^ B := allTheta_sum_tau_pow_div_le B D
  have hlogD : 1 + Real.log D ≤ 2 * (1 + Real.log x) := by
    have h1 : Real.log D ≤ Real.log ((2 * x : ℕ)) := by
      refine allTheta_log_nat_mono ?_
      calc D ≤ Nat.sqrt (2 * x) := Nat.sqrt_le_self _
        _ ≤ 2 * x := Nat.sqrt_le_self _
    have h2 : Real.log ((2 * x : ℕ) : ℝ) = Real.log 2 + Real.log x := by
      push_cast
      exact Real.log_mul two_ne_zero (ne_of_gt (lt_of_lt_of_le one_pos hx1))
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
      linarith
    rw [h2] at h1
    linarith
  have hpow : (1 + Real.log D) ^ 2 ^ B ≤ 2 ^ 2 ^ B * (1 + Real.log x) ^ 2 ^ B := by
    calc (1 + Real.log D) ^ 2 ^ B ≤ (2 * (1 + Real.log x)) ^ 2 ^ B :=
          pow_le_pow_left₀ (allTheta_one_add_log_nonneg D) hlogD _
      _ = 2 ^ 2 ^ B * (1 + Real.log x) ^ 2 ^ B := mul_pow 2 (1 + Real.log x) (2 ^ B)
  -- Assemble.
  calc ∑ n ∈ Finset.Ioc x (x + y), ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 4
      ≤ (A : ℝ) * ∑ n ∈ Finset.Ioc x (x + y),
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n),
            ((d.divisors.card : ℕ) : ℝ) ^ B := step1
    _ = (A : ℝ) * ∑ d ∈ Finset.Icc 1 D,
          ((((Finset.Ioc x (x + y)).filter (fun n => d ∣ n)).card : ℕ) : ℝ)
            * ((d.divisors.card : ℕ) : ℝ) ^ B := by rw [step2]
    _ ≤ (A : ℝ) * ((2 * (y : ℝ)) * S) :=
        mul_le_mul_of_nonneg_left step3 (Nat.cast_nonneg A)
    _ ≤ (A : ℝ) * ((2 * (y : ℝ)) * ((1 + Real.log D) ^ 2 ^ B)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg A)
        exact mul_le_mul_of_nonneg_left hSbound (by positivity : (0 : ℝ) ≤ 2 * (y : ℝ))
    _ ≤ (A : ℝ) * ((2 * (y : ℝ)) * (2 ^ 2 ^ B * (1 + Real.log x) ^ 2 ^ B)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg A)
        exact mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 2 * (y : ℝ))
    _ = (A : ℝ) * 2 ^ (2 ^ B + 1) * (y : ℝ) * (1 + Real.log x) ^ 2 ^ B := by
        rw [pow_succ]
        ring

#print axioms allTheta_card_multiples
#print axioms allTheta_hyperbola
#print axioms allTheta_sum_tau_pow_div_le
#print axioms allTheta_sqrt_sqrt_le
#print axioms allTheta_tau_pow_four_short_interval

end Shiu
end Zeta85
end RH

end
