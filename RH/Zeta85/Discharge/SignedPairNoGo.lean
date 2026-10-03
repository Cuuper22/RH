/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Arith

/-!
# The frozen signed-pair trace-grade predicate is false

`SignedPairTraceGrade σ` quantifies the main-term integral `IV` independently
of the weight `V`.  Taking `IV = 0` and `w = V = 1` removes the singular-series
main term, so the predicate would bound the raw positive aggregate

  `Σ_{1 ≤ h ≤ ⌈2H⌉} Σ_{1 ≤ n ≤ ⌈2X⌉} Λ(n) Λ(n+h)`,   `X = T^σ`, `H = T^(σ-1)`,

by `K·X/log T`.  Partition `[0, Jm)` into `J ≈ X/m` blocks of length
`m = ⌊H⌋`.  Cauchy–Schwarz over the blocks and Chebyshev's lower bound
`ψ(X) ≫ X` show that the aggregate is `≫ X·m` once `m ≫ log X`, which
contradicts the asserted bound because `H` is a positive power of `T`.

This formalizes the ordinary refutation recorded in
`docs/research/research_20260905.md`.  It uses only Mathlib; in particular it
does not use any axiom of `RH/Zeta85/Hypotheses.lean`.
-/

open scoped BigOperators
open Finset Filter

noncomputable section

namespace RH
namespace Zeta85
namespace SignedPairNoGo

/-! ## Finite combinatorics -/

/-- The ordered half of a square: `(Σ b)² / 2 ≤ Σ_i b_i Σ_{i ≤ k < m} b_k`.
No sign condition is needed. -/
theorem half_sq_le_tail (b : ℕ → ℝ) : ∀ m : ℕ,
    (∑ i ∈ range m, b i) ^ 2 / 2 ≤ ∑ i ∈ range m, b i * ∑ k ∈ Ico i m, b k
  | 0 => by simp
  | m + 1 => by
    have ih := half_sq_le_tail b m
    have hsplit : ∑ i ∈ range m, b i * ∑ k ∈ Ico i (m + 1), b k
        = ∑ i ∈ range m, b i * ∑ k ∈ Ico i m, b k + (∑ i ∈ range m, b i) * b m := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_Ico_succ_top (Finset.mem_range.1 hi).le]
      ring
    have hlast : ∑ k ∈ Ico m (m + 1), b k = b m := by
      rw [Finset.sum_Ico_succ_top (le_refl m), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hsplit, hlast]
    nlinarith [sq_nonneg (b m)]

/-- The tail of a block starting at `i` is dominated by `b i` plus the
forward window of length `m` after `i`. -/
theorem tail_le_window (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) {i m : ℕ} (hi : i < m) :
    ∑ k ∈ Ico i m, b k ≤ b i + ∑ d ∈ range m, b (i + 1 + d) := by
  rw [Finset.sum_Ico_eq_sum_range]
  obtain ⟨r, hr⟩ : ∃ r, m - i = r + 1 := ⟨m - i - 1, by omega⟩
  rw [hr, Finset.sum_range_succ']
  have hshift : ∑ k ∈ range r, b (i + (k + 1)) = ∑ k ∈ range r, b (i + 1 + k) :=
    Finset.sum_congr rfl fun k _ => by rw [show i + (k + 1) = i + 1 + k by omega]
  have hsub : ∑ k ∈ range r, b (i + 1 + k) ≤ ∑ d ∈ range m, b (i + 1 + d) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => hb _)
  rw [hshift, add_zero]
  linarith

/-- Summing over `J` consecutive blocks of length `m`. -/
theorem sum_blocks (f : ℕ → ℝ) (m : ℕ) : ∀ J : ℕ,
    ∑ j ∈ range J, ∑ i ∈ range m, f (j * m + i) = ∑ n ∈ range (J * m), f n
  | 0 => by simp
  | J + 1 => by
    rw [Finset.sum_range_succ, sum_blocks f m J, add_one_mul, Finset.sum_range_add]

/-- Block pigeonhole: for nonnegative `a`, the square of the total mass on
`[0, Jm)` is at most `2J` times the diagonal plus the forward window pairs. -/
theorem sq_sum_le_blocks (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (m J : ℕ) :
    (∑ n ∈ range (J * m), a n) ^ 2 ≤
      2 * J * ∑ n ∈ range (J * m), a n * (a n + ∑ d ∈ range m, a (n + 1 + d)) := by
  have hblock : ∀ j : ℕ, (∑ i ∈ range m, a (j * m + i)) ^ 2 ≤
      2 * ∑ i ∈ range m, a (j * m + i) *
        (a (j * m + i) + ∑ d ∈ range m, a (j * m + i + 1 + d)) := by
    intro j
    have h1 : (∑ i ∈ range m, a (j * m + i)) ^ 2 / 2 ≤
        ∑ i ∈ range m, a (j * m + i) * ∑ k ∈ Ico i m, a (j * m + k) :=
      half_sq_le_tail (fun i => a (j * m + i)) m
    have h2 : ∑ i ∈ range m, a (j * m + i) * ∑ k ∈ Ico i m, a (j * m + k) ≤
        ∑ i ∈ range m, a (j * m + i) *
          (a (j * m + i) + ∑ d ∈ range m, a (j * m + i + 1 + d)) := by
      refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (ha _)
      have := tail_le_window (fun k => a (j * m + k)) (fun _ => ha _) (Finset.mem_range.1 hi)
      simpa only [add_assoc] using this
    linarith
  have hcs : (∑ j ∈ range J, ∑ i ∈ range m, a (j * m + i)) ^ 2 ≤
      (J : ℝ) * ∑ j ∈ range J, (∑ i ∈ range m, a (j * m + i)) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := range J)
      (f := fun j => ∑ i ∈ range m, a (j * m + i))
  have htot := sum_blocks a m J
  have hsum := sum_blocks (fun n => a n * (a n + ∑ d ∈ range m, a (n + 1 + d))) m J
  rw [← htot, ← hsum]
  calc (∑ j ∈ range J, ∑ i ∈ range m, a (j * m + i)) ^ 2
      ≤ (J : ℝ) * ∑ j ∈ range J, (∑ i ∈ range m, a (j * m + i)) ^ 2 := hcs
    _ ≤ (J : ℝ) * ∑ j ∈ range J, 2 * ∑ i ∈ range m, a (j * m + i) *
          (a (j * m + i) + ∑ d ∈ range m, a (j * m + i + 1 + d)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hblock j) (by positivity)
    _ = 2 * J * ∑ j ∈ range J, ∑ i ∈ range m, a (j * m + i) *
          (a (j * m + i) + ∑ d ∈ range m, a (j * m + i + 1 + d)) := by
        rw [← Finset.mul_sum]; ring

/-- The forward window pairs are a sub-sum of the shifted pair aggregate. -/
theorem window_le_pairs (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)
    {N M m L : ℕ} (hL : L ≤ N + 1) (hm : m ≤ M) :
    ∑ n ∈ range L, a n * ∑ d ∈ range m, a (n + 1 + d) ≤
      ∑ h ∈ Icc 1 M, ∑ n ∈ Icc 1 N, a n * a (n + h) := by
  rw [Finset.sum_comm]
  set G : ℕ → ℝ := fun n => ∑ h ∈ Icc 1 M, a n * a (n + h) with hG
  have hGnn : ∀ n, 0 ≤ G n := fun n =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (ha _) (ha _)
  have hinner : ∀ n, a n * ∑ d ∈ range m, a (n + 1 + d) ≤ G n := by
    intro n
    simp only [hG, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (ha n)
    have hre : ∑ d ∈ range m, a (n + 1 + d) = ∑ h ∈ Ico 1 (m + 1), a (n + h) := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      exact Finset.sum_congr rfl fun d _ => by rw [add_assoc]
    rw [hre]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => ha _)
    intro h hh
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hh ⊢
    omega
  have hG0 : G 0 = 0 := by simp [hG, ha0]
  calc ∑ n ∈ range L, a n * ∑ d ∈ range m, a (n + 1 + d)
      ≤ ∑ n ∈ range L, G n := Finset.sum_le_sum fun n _ => hinner n
    _ ≤ ∑ n ∈ insert 0 (Icc 1 N), G n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hGnn _)
        intro n hn
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc] at hn ⊢
        omega
    _ = ∑ n ∈ Icc 1 N, G n := by
        rw [Finset.sum_insert (by simp), hG0, zero_add]

/-! ## The refutation -/

set_option maxHeartbeats 1000000 in
/-- The literal frozen predicate is false at every connected support `σ > 1`. -/
theorem not_signedPairTraceGrade {σ : ℝ} (hσ : 1 < σ) : ¬ SignedPairTraceGrade σ := by
  rintro ⟨S, hS⟩
  obtain ⟨K, T₁, hK⟩ :=
    hS (fun _ => 1) (fun _ => 1) (by simp) (by simp) 0 (by simp) 1 one_pos
  set a : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n with ha_def
  have ha : ∀ n, 0 ≤ a n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  have ha0 : a 0 = 0 := by simp [ha_def]
  have hr : 0 < σ - 1 := by linarith
  have hσ0 : 0 < σ := by linarith
  set c₀ : ℝ := 2 + 64 * Real.log 2 + 512 * |K| with hc₀
  -- Eventual facts in `T`.
  have hE1 : ∀ᶠ T : ℝ in atTop, T₁ ≤ T ∧ 1 ≤ T := by
    filter_upwards [eventually_ge_atTop T₁, eventually_ge_atTop 1] with T h1 h2 using ⟨h1, h2⟩
  have hE2 : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hE3 : ∀ᶠ T : ℝ in atTop, 4 ≤ T ^ σ := (tendsto_rpow_atTop hσ0).eventually_ge_atTop 4
  have hE4 : ∀ᶠ T : ℝ in atTop, ‖Real.log (T ^ σ + 1)‖ ≤ (1 / 8) * ‖T ^ σ + 1‖ := by
    have hlo := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 8 by norm_num)
    have htend : Tendsto (fun T : ℝ => T ^ σ + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_rpow_atTop hσ0)
    exact htend.eventually hlo
  have hE5 : ∀ᶠ T : ℝ in atTop,
      ‖Real.log T‖ ≤ (1 / (128 * σ)) * ‖T ^ (σ - 1)‖ :=
    (isLittleO_log_rpow_atTop hr).bound (by positivity)
  have hE6 : ∀ᶠ T : ℝ in atTop, 2 * c₀ ≤ T ^ (σ - 1) :=
    (tendsto_rpow_atTop hr).eventually_ge_atTop _
  obtain ⟨T, ⟨hT₁, hT1⟩, hlogT, hX4, hlogX, hlogTr, hTr⟩ :=
    (hE1.and (hE2.and (hE3.and (hE4.and (hE5.and hE6))))).exists
  have hT0 : 0 < T := by linarith
  set X : ℝ := T ^ σ with hX
  set H : ℝ := T ^ (σ - 1) with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow hT1 hr.le
  have hHX : H ≤ X := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hX0 : 0 < X := by linarith
  -- the logarithmic bound at `X + 1`
  have hlogX' : Real.log (X + 1) ≤ X / 4 := by
    have hpos : 0 < X + 1 := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hlogX
    have := le_abs_self (Real.log (X + 1))
    linarith
  -- `64 σ log T ≤ H / 2`
  have hlogTr' : 64 * σ * Real.log T ≤ H / 2 := by
    have hH0 : 0 ≤ H := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hH0,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log T)] at hlogTr
    have h := mul_le_mul_of_nonneg_left hlogTr (by positivity : (0 : ℝ) ≤ 64 * σ)
    have hσne : (128 * σ) ≠ 0 := by positivity
    calc 64 * σ * Real.log T ≤ 64 * σ * (1 / (128 * σ) * H) := h
      _ = H / 2 := by field_simp; ring
  -- block length and number of blocks
  set m : ℕ := ⌊H⌋₊ with hm
  have hmH : (m : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hmH' : H - 1 < (m : ℝ) := Nat.sub_one_lt_floor H
  have hm0 : (0 : ℝ) < m := by linarith
  set J : ℕ := ⌊X / m⌋₊ + 1 with hJ
  have hJlo : X / m < (J : ℝ) := by
    rw [hJ]; push_cast; exact Nat.lt_floor_add_one _
  have hJhi : (J : ℝ) ≤ X / m + 1 := by
    rw [hJ]; push_cast
    linarith [Nat.floor_le (div_nonneg hX0.le hm0.le)]
  have hJm_gt : X < (J : ℝ) * m := by
    have := (div_lt_iff₀ hm0).1 hJlo; linarith
  have hJm_le : (J : ℝ) * m ≤ 2 * X := by
    have h := mul_le_mul_of_nonneg_right hJhi hm0.le
    have : (X / m + 1) * m = X + m := by field_simp
    linarith
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  set L : ℕ := J * m with hL
  have hLcast : (L : ℝ) = J * m := by rw [hL]; push_cast; ring
  -- the aggregate dominates the forward window pairs
  have hagg := hK T hT₁
  have hagg_eq : signedPairAggregate (fun _ => 1) (fun _ => 1) S 0 X H =
      ∑ h ∈ Icc 1 ⌈2 * H⌉₊, ∑ n ∈ Icc 1 ⌈2 * X⌉₊, a n * a (n + h) := by
    simp [signedPairAggregate, pairCorr, ha_def]
  have hLN : L ≤ ⌈2 * X⌉₊ + 1 := by
    have : (L : ℝ) ≤ ⌈2 * X⌉₊ := by
      rw [hLcast]; exact hJm_le.trans (Nat.le_ceil _)
    have : L ≤ ⌈2 * X⌉₊ := by exact_mod_cast this
    omega
  have hmM : m ≤ ⌈2 * H⌉₊ := by
    have : (m : ℝ) ≤ ⌈2 * H⌉₊ := by
      have := Nat.le_ceil (2 * H); linarith
    exact_mod_cast this
  have hwin := window_le_pairs a ha ha0 hLN hmM
  set P : ℝ := ∑ n ∈ range L, a n * ∑ d ∈ range m, a (n + 1 + d) with hP
  set B : ℝ := K * X * Real.log T ^ (-(1 : ℝ)) with hB
  have hPB : P ≤ B := by
    rw [hagg_eq] at hagg
    exact hwin.trans ((le_abs_self _).trans hagg)
  have hBK : B ≤ |K| * X := by
    have hinv : Real.log T ^ (-(1 : ℝ)) = (Real.log T)⁻¹ := Real.rpow_neg_one _
    have hl0 : 0 < Real.log T := by linarith
    have hinv1 : (Real.log T)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlogT
    have hinv0 : 0 ≤ (Real.log T)⁻¹ := inv_nonneg.2 hl0.le
    rw [hB, hinv]
    calc K * X * (Real.log T)⁻¹ ≤ |K| * X * (Real.log T)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self K) hX0.le) hinv0
      _ ≤ |K| * X * 1 :=
          mul_le_mul_of_nonneg_left hinv1 (mul_nonneg (abs_nonneg K) hX0.le)
      _ = |K| * X := mul_one _
  -- Chebyshev lower bound for the block mass
  set Ψ : ℝ := ∑ n ∈ range L, a n with hΨ
  set N₀ : ℕ := ⌊X⌋₊ with hN₀
  have hN₀X : (N₀ : ℝ) ≤ X := Nat.floor_le hX0.le
  have hN₀X' : X - 1 < (N₀ : ℝ) := Nat.sub_one_lt_floor X
  have hN₀L : N₀ < L := by
    have : (N₀ : ℝ) < L := by rw [hLcast]; linarith
    exact_mod_cast this
  have hpsiΨ : Chebyshev.psi N₀ ≤ Ψ := by
    rw [Chebyshev.psi, Nat.floor_natCast]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => ha _)
    intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_range] at hn ⊢
    omega
  have hpsi := Chebyshev.psi_ge N₀
  have hΨX : X / 8 ≤ Ψ := by
    have hlog2 : (0.69 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
    have hlogN : Real.log ((N₀ : ℝ) + 1) ≤ Real.log (X + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have h1 : (X - 1) * Real.log 2 ≤ (N₀ : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hN₀X'.le (Real.log_nonneg (by norm_num))
    have h2 : (X - 1) * 0.69 ≤ (X - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2.le (by linarith)
    linarith
  -- each coefficient is at most `log (2X)`
  set Lg : ℝ := Real.log 2 + σ * Real.log T with hLg
  have hLg_eq : Real.log (2 * X) = Lg := by
    rw [Real.log_mul (by norm_num) hX0.ne', hX, Real.log_rpow hT0]
  have ha_le : ∀ n ∈ range L, a n ≤ Lg := by
    intro n hn
    rw [← hLg_eq]
    have hnL : (n : ℝ) < L := by exact_mod_cast Finset.mem_range.1 hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; rw [ha0]; exact Real.log_nonneg (by linarith)
    · calc a n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
        _ ≤ Real.log (2 * X) :=
          Real.log_le_log (by exact_mod_cast hpos) (by rw [hLcast] at hnL; linarith)
  have hdiag : ∑ n ∈ range L, a n * a n ≤ Lg * Ψ := by
    rw [hΨ, Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn => by
      rw [mul_comm Lg]; exact mul_le_mul_of_nonneg_left (ha_le n hn) (ha n)
  -- the block inequality
  have hblocks := sq_sum_le_blocks a ha m J
  rw [← hL] at hblocks
  have hsplit : ∑ n ∈ range L, a n * (a n + ∑ d ∈ range m, a (n + 1 + d)) =
      ∑ n ∈ range L, a n * a n + P := by
    rw [hP, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsplit] at hblocks
  -- size of the block length
  have hLg0 : 0 ≤ Lg := by
    have : 0 ≤ Real.log T := by linarith
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hm_big : 64 * Lg + 512 * |K| + 1 ≤ (m : ℝ) := by
    have : 64 * Lg = 64 * Real.log 2 + 64 * σ * Real.log T := by rw [hLg]; ring
    linarith
  have hJLg : 2 * (J : ℝ) * Lg ≤ X / 16 := by
    have h := mul_le_mul_of_nonneg_left
      (show 64 * Lg ≤ (m : ℝ) by linarith [abs_nonneg K]) hJ0
    linarith
  have hΨ0 : 0 ≤ Ψ := by linarith
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun n _ =>
    mul_nonneg (ha n) (Finset.sum_nonneg fun _ _ => ha _)
  -- `Ψ² ≤ 4 J B`
  have hkey : Ψ ^ 2 ≤ 4 * J * (|K| * X) := by
    have h1 : Ψ ^ 2 ≤ 2 * J * (Lg * Ψ + B) := by
      calc Ψ ^ 2 ≤ 2 * J * (∑ n ∈ range L, a n * a n + P) := hblocks
        _ ≤ 2 * J * (Lg * Ψ + B) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
    have h2 : 2 * J * Lg * Ψ ≤ Ψ / 2 * Ψ :=
      mul_le_mul_of_nonneg_right (by linarith) hΨ0
    have h3 : 2 * (J : ℝ) * B ≤ 2 * J * (|K| * X) :=
      mul_le_mul_of_nonneg_left hBK (by positivity)
    linarith
  -- contradiction: `X m / 64 ≤ 4 J m |K| ≤ 8 X |K|` forces `m ≤ 512 |K|`
  have h1 : (X / 8) ^ 2 ≤ 4 * J * (|K| * X) :=
    (pow_le_pow_left₀ (by positivity) hΨX 2).trans hkey
  have h2 : X / 64 ≤ 4 * J * |K| := by
    have : X * (X / 64) ≤ X * (4 * J * |K|) :=
      calc X * (X / 64) = (X / 8) ^ 2 := by ring
        _ ≤ 4 * J * (|K| * X) := h1
        _ = X * (4 * J * |K|) := by ring
    exact le_of_mul_le_mul_left this hX0
  have h3 : X / 64 * m ≤ 4 * |K| * (J * m) := by
    have := mul_le_mul_of_nonneg_right h2 hm0.le
    linarith
  have h4 : 4 * |K| * (J * m) ≤ 4 * |K| * (2 * X) :=
    mul_le_mul_of_nonneg_left hJm_le (by positivity)
  have h5 : X * (m : ℝ) ≤ X * (512 * |K|) := by linarith only [h3, h4]
  have h6 : (m : ℝ) ≤ 512 * |K| := le_of_mul_le_mul_left h5 hX0
  linarith

end SignedPairNoGo

export SignedPairNoGo (not_signedPairTraceGrade)

end Zeta85
end RH

end
