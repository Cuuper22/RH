/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Rat.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Summatory bounds for the generalized divisor functions `τ_K`

Write `τ_K = ArithmeticFunction.zeta ^ K` for the `K`-th Dirichlet-convolution power of the
arithmetic zeta function, so `τ_K m` counts the ordered `K`-tuples of positive integers with
product `m` (`τ_2 = τ`, the usual divisor-counting function).  This file proves the
constant-explicit, uniform-in-`K` summatory ladder

* `tauSum_convolution_swap` — the hyperbola reindexing
  `∑_{m ≤ N} ∑_{de = m} f(d)·g(e) = ∑_{d ≤ N} ∑_{e ≤ N/d} f(d)·g(e)` (ℕ-division `N / d`),
  the single combinatorial engine behind both inductions below;
* `tauSum_div_le` — `∑_{m ≤ N} τ_K(m)/m ≤ (1 + log N)^K`;
* `tauSum_le` — `∑_{m ≤ N} τ_K(m) ≤ N·(1 + log N)^(K-1)` for `K ≥ 1`.

Both bounds follow the standard divisor-sum induction; cf. Shiu 1980 Lemma-style bounds.
All constants are absolute and explicit, and the uniformity in `K` is needed for the
Landreau-route exponents (these bounds get used at `K = 4096`).
-/

namespace RH
namespace Zeta85
namespace Shiu

open ArithmeticFunction

/-- The harmonic sum over `Finset.Icc 1 M`, in ℝ, is at most `1 + log M`.  This is Mathlib's
`harmonic_le_one_add_log` transported from ℚ; it also holds (trivially) at `M = 0`. -/
private lemma tauSum_harmonic_icc_le (M : ℕ) :
    ∑ e ∈ Finset.Icc 1 M, (1 : ℝ) / e ≤ 1 + Real.log M := by
  refine le_trans (le_of_eq ?_) (harmonic_le_one_add_log M)
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Monotonicity of `Real.log` along the ℕ-division `N / d ≤ N`, including the degenerate
case `N / d = 0` (where `log 0 = 0 ≤ log N`). -/
private lemma tauSum_log_natCast_div_le (N d : ℕ) :
    Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos (N / d) with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast h) (Nat.cast_le.mpr (Nat.div_le_self N d))

/-- `τ_K m` is a natural number, so its real cast is nonnegative. -/
private lemma tauSum_zeta_pow_apply_nonneg (K m : ℕ) : (0 : ℝ) ≤ ((zeta ^ K) m : ℝ) :=
  Nat.cast_nonneg _

/-- `τ_1 = ζ` takes the value `1` at every `m ≠ 0`. -/
private lemma tauSum_zeta_pow_one_apply {m : ℕ} (hm : m ≠ 0) : (zeta ^ 1) m = 1 := by
  rw [pow_one, ArithmeticFunction.zeta_apply_ne hm]

/-- **Hyperbola reindexing.**  Summing `f(p.1) * g(p.2)` over the divisor antidiagonals of all
`m ∈ [1, N]` is the same as summing over `d ∈ [1, N]` and `e ∈ [1, N / d]` (ℕ-division):
the pairs `(d, e)` with `1 ≤ d`, `1 ≤ e`, `d * e ≤ N` are counted exactly once on both sides.
This single reindexing powers both summatory inductions below; cf. Shiu 1980
Lemma-style bounds. -/
theorem tauSum_convolution_swap (N : ℕ) (f g : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ m.divisorsAntidiagonal, f p.1 * g p.2
      = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), f d * g e :=
  calc ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ m.divisorsAntidiagonal, f p.1 * g p.2
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun m => m.divisorsAntidiagonal),
          f x.2.1 * g x.2.2 :=
        (Finset.sum_sigma (Finset.Icc 1 N) (fun m => m.divisorsAntidiagonal)
          (fun x => f x.2.1 * g x.2.2)).symm
    _ = ∑ y ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)), f y.1 * g y.2 := by
        refine Finset.sum_nbij' (fun x => ⟨x.2.1, x.2.2⟩) (fun y => ⟨y.1 * y.2, (y.1, y.2)⟩)
          ?_ ?_ ?_ ?_ ?_
        · -- forward membership: a divisor pair of `m ≤ N` lands in the hyperbola region
          rintro ⟨m, p⟩ hx
          simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hx ⊢
          obtain ⟨⟨-, hmN⟩, hprod, hm0⟩ := hx
          have hp1 : 0 < p.1 := by
            rcases Nat.eq_zero_or_pos p.1 with h | h
            · exfalso; rw [h, Nat.zero_mul] at hprod; exact hm0 hprod.symm
            · exact h
          have hp2 : 0 < p.2 := by
            rcases Nat.eq_zero_or_pos p.2 with h | h
            · exfalso; rw [h, Nat.mul_zero] at hprod; exact hm0 hprod.symm
            · exact h
          refine ⟨⟨hp1, ?_⟩, hp2, ?_⟩
          · calc p.1 = p.1 * 1 := (Nat.mul_one p.1).symm
              _ ≤ p.1 * p.2 := Nat.mul_le_mul (Nat.le_refl p.1) hp2
              _ = m := hprod
              _ ≤ N := hmN
          · rw [Nat.le_div_iff_mul_le hp1]
            calc p.2 * p.1 = p.1 * p.2 := Nat.mul_comm p.2 p.1
              _ = m := hprod
              _ ≤ N := hmN
        · -- backward membership: a hyperbola point gives a divisor pair of `d * e ≤ N`
          rintro ⟨d, e⟩ hy
          simp only [Finset.mem_sigma, Finset.mem_Icc] at hy
          obtain ⟨⟨hd1, hdN⟩, he1, heN⟩ := hy
          have hpos : 0 < d * e := Nat.mul_pos hd1 he1
          have hde : d * e ≤ N := by
            calc d * e = e * d := Nat.mul_comm d e
              _ ≤ N := (Nat.le_div_iff_mul_le hd1).mp heN
          exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hde⟩,
            Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.pos_iff_ne_zero.mp hpos⟩⟩
        · -- left inverse
          rintro ⟨m, p⟩ hx
          simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
          obtain ⟨-, hprod, -⟩ := hx
          subst hprod
          rfl
        · -- right inverse
          intro y _
          rfl
        · -- the summands agree
          intro x _
          rfl
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), f d * g e :=
        Finset.sum_sigma (Finset.Icc 1 N) (fun d => Finset.Icc 1 (N / d))
          (fun y => f y.1 * g y.2)

/-- **Logarithmic-average bound for `τ_K`, uniform in `K`.**
`∑_{m ≤ N} τ_K(m)/m ≤ (1 + log N)^K` for every `K` and every `N ≥ 1`, with an absolute,
explicit constant (namely `1`): the standard divisor-sum induction on `K`, each step
reindexing by `tauSum_convolution_swap` and estimating the inner harmonic sum by
`1 + log (N/d) ≤ 1 + log N`; cf. Shiu 1980 Lemma-style bounds.  The uniformity in `K` is
needed for the Landreau-route exponents (`K = 4096`). -/
theorem tauSum_div_le (K N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, ((zeta ^ K) m : ℝ) / m ≤ (1 + Real.log N) ^ K := by
  induction K with
  | zero =>
    -- `τ_0` is the convolution identity: value `1` at `m = 1`, value `0` elsewhere.
    have hone : ∀ m ∈ Finset.Icc 1 N, ((zeta ^ 0) m : ℝ) / m
        = if m = 1 then (1 : ℝ) else 0 := by
      intro m _
      rcases eq_or_ne m 1 with rfl | hne
      · simp
      · simp [hne]
    calc ∑ m ∈ Finset.Icc 1 N, ((zeta ^ 0) m : ℝ) / m
        = ∑ m ∈ Finset.Icc 1 N, if m = 1 then (1 : ℝ) else 0 := Finset.sum_congr rfl hone
      _ = 1 := by simp [hN]
      _ = (1 + Real.log N) ^ 0 := (pow_zero _).symm
      _ ≤ (1 + Real.log N) ^ 0 := le_rfl
  | succ K ih =>
    have hlog : (0 : ℝ) ≤ 1 + Real.log N := add_nonneg zero_le_one (Real.log_natCast_nonneg N)
    calc ∑ m ∈ Finset.Icc 1 N, ((zeta ^ (K + 1)) m : ℝ) / m
        = ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ m.divisorsAntidiagonal,
            (((zeta ^ K) p.1 : ℝ) / p.1) * ((1 : ℝ) / p.2) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [pow_succ, ArithmeticFunction.mul_apply, Nat.cast_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun p hp => ?_
          obtain ⟨hprod, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
          have hp2 : p.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
          rw [Nat.cast_mul, ArithmeticFunction.zeta_apply_ne hp2, Nat.cast_one, mul_one,
            ← hprod, Nat.cast_mul, div_mul_div_comm, mul_one]
      _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d),
            (((zeta ^ K) d : ℝ) / d) * ((1 : ℝ) / e) :=
          tauSum_convolution_swap N (fun d => ((zeta ^ K) d : ℝ) / d) (fun e => (1 : ℝ) / e)
      _ = ∑ d ∈ Finset.Icc 1 N,
            (((zeta ^ K) d : ℝ) / d) * ∑ e ∈ Finset.Icc 1 (N / d), (1 : ℝ) / e := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (((zeta ^ K) d : ℝ) / d) * (1 + Real.log N) := by
          refine Finset.sum_le_sum fun d _ => ?_
          have hnn : (0 : ℝ) ≤ ((zeta ^ K) d : ℝ) / d :=
            div_nonneg (tauSum_zeta_pow_apply_nonneg K d) (Nat.cast_nonneg d)
          refine mul_le_mul_of_nonneg_left ?_ hnn
          calc ∑ e ∈ Finset.Icc 1 (N / d), (1 : ℝ) / e
              ≤ 1 + Real.log ((N / d : ℕ) : ℝ) := tauSum_harmonic_icc_le (N / d)
            _ ≤ 1 + Real.log N := add_le_add le_rfl (tauSum_log_natCast_div_le N d)
      _ = (∑ d ∈ Finset.Icc 1 N, ((zeta ^ K) d : ℝ) / d) * (1 + Real.log N) := by
          rw [Finset.sum_mul]
      _ ≤ (1 + Real.log N) ^ K * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_right ih hlog
      _ = (1 + Real.log N) ^ (K + 1) := (pow_succ _ _).symm

/-- **Summatory bound for `τ_K`, uniform in `K`.**
`∑_{m ≤ N} τ_K(m) ≤ N · (1 + log N)^(K-1)` for every `K ≥ 1` and `N ≥ 1`, with an absolute,
explicit constant: one application of `tauSum_convolution_swap` turns the sum into
`∑_{d ≤ N} τ_(K-1)(d) · ⌊N/d⌋`, and `⌊N/d⌋ ≤ N/d` reduces to `tauSum_div_le`; the standard
divisor-sum induction, cf. Shiu 1980 Lemma-style bounds.  The uniformity in `K` is needed
for the Landreau-route exponents (`K = 4096`). -/
theorem tauSum_le (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, ((zeta ^ K) m : ℝ) ≤ N * (1 + Real.log N) ^ (K - 1) := by
  obtain ⟨J, rfl⟩ : ∃ J, K = J + 1 := ⟨K - 1, (Nat.succ_pred_eq_of_pos hK).symm⟩
  rw [Nat.add_sub_cancel]
  calc ∑ m ∈ Finset.Icc 1 N, ((zeta ^ (J + 1)) m : ℝ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ m.divisorsAntidiagonal,
          ((zeta ^ J) p.1 : ℝ) * (1 : ℝ) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [pow_succ, ArithmeticFunction.mul_apply, Nat.cast_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp2 : p.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
        rw [Nat.cast_mul, ArithmeticFunction.zeta_apply_ne hp2, Nat.cast_one]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), ((zeta ^ J) d : ℝ) * (1 : ℝ) :=
        tauSum_convolution_swap N (fun d => ((zeta ^ J) d : ℝ)) (fun _ => (1 : ℝ))
    _ = ∑ d ∈ Finset.Icc 1 N, ((zeta ^ J) d : ℝ) * ((N / d : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, mul_comm]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ((zeta ^ J) d : ℝ) * ((N : ℝ) / d) := by
        refine Finset.sum_le_sum fun d _ => ?_
        exact mul_le_mul_of_nonneg_left Nat.cast_div_le (tauSum_zeta_pow_apply_nonneg J d)
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, ((zeta ^ J) d : ℝ) / d := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [mul_div_assoc', mul_div_assoc', mul_comm]
    _ ≤ (N : ℝ) * (1 + Real.log N) ^ J :=
        mul_le_mul_of_nonneg_left (tauSum_div_le J N hN) (Nat.cast_nonneg N)

/-! ## Sanity checks: the `K = 1` specializations

At `K = 1` the two bounds specialize to the harmonic-sum bound and the trivial count:
`τ_1(m) = 1` for `m ≥ 1`, so `tauSum_div_le` reduces to `∑_{m ≤ N} 1/m ≤ 1 + log N` and
`tauSum_le` reduces to `∑_{m ≤ N} 1 = N`. -/

example (N : ℕ) : ∑ m ∈ Finset.Icc 1 N, ((zeta ^ 1) m : ℝ) = N := by
  have h : ∀ m ∈ Finset.Icc 1 N, ((zeta ^ 1) m : ℝ) = 1 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [tauSum_zeta_pow_one_apply (Nat.one_le_iff_ne_zero.mp hm.1), Nat.cast_one]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul, mul_one]

example (N : ℕ) (hN : 1 ≤ N) : ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m ≤ 1 + Real.log N := by
  have h := tauSum_div_le 1 N hN
  have he : ∑ m ∈ Finset.Icc 1 N, ((zeta ^ 1) m : ℝ) / m
      = ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    rw [tauSum_zeta_pow_one_apply (Nat.one_le_iff_ne_zero.mp hm.1), Nat.cast_one]
  rw [he, pow_one] at h
  exact h

example (N : ℕ) (hN : 1 ≤ N) : ∑ m ∈ Finset.Icc 1 N, ((zeta ^ 1) m : ℝ) ≤ N := by
  have h := tauSum_le 1 N le_rfl hN
  simpa using h

end Shiu
end Zeta85
end RH

#print axioms RH.Zeta85.Shiu.tauSum_convolution_swap
#print axioms RH.Zeta85.Shiu.tauSum_div_le
#print axioms RH.Zeta85.Shiu.tauSum_le
