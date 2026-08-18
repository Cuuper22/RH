/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Arith

/-!
# The frozen Shiu interface is inconsistent

`ShiuMajorant` fixes `T` before quantifying the interval scale `P`, but its
right-hand side contains only powers of `log T`.  We exploit that quantifier
order with the divisor-counting coefficient at a single prime power.  A
power-of-two modulus isolates the spike in a progression whose normalized
length is bounded independently of the prime-power exponent.
-/

open scoped BigOperators ArithmeticFunction
open Finset

noncomputable section

namespace RH
namespace Zeta85

/-- The frozen progression-majorant interface fails already at `η = 1/4`. -/
theorem not_shiuMajorant_quarter : ¬ ShiuMajorant (1 / 4 : ℝ) := by
  intro hshiu
  let c : ℕ → ℝ := fun n ↦ ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ)
  have hc : DivisorBounded c 1 1 := by
    intro n
    simp [c]
  obtain ⟨C, K, T₁, hbound⟩ := hshiu c 1 1 hc

  let T : ℝ := max T₁ 1 + 1
  have hTT₁ : T₁ ≤ T := by
    dsimp [T]
    linarith [le_max_left T₁ (1 : ℝ)]
  have hTone : 1 ≤ T := by
    dsimp [T]
    linarith [le_max_right T₁ (1 : ℝ)]
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone

  let B : ℝ := K * (2 * T) * (Real.log T) ^ C
  obtain ⟨m, hm⟩ := exists_nat_gt (max B 1)
  have hmB : B < (m : ℝ) := (le_max_left B 1).trans_lt hm
  have hmoneR : (1 : ℝ) < m := (le_max_right B 1).trans_lt hm
  have hmpos : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)

  let n : ℕ := 3 ^ m
  have hn_gt : 1 < n := by
    dsimp [n]
    exact one_lt_pow₀ (by norm_num) hmpos.ne'
  let e : ℕ := Nat.clog 2 n
  have he : 0 < e := Nat.clog_pos Nat.one_lt_two hn_gt
  let q : ℕ := 2 ^ e
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hnq : n ≤ q := by
    dsimp [q, e]
    exact Nat.le_pow_clog Nat.one_lt_two n
  have hcop : Nat.Coprime n q := by
    dsimp [n, q]
    exact Nat.coprime_pow_primes m e Nat.prime_three Nat.prime_two (by norm_num)

  let P : ℝ := (q : ℝ) * T
  have hPone : 1 ≤ P := by
    dsimp [P]
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
    nlinarith
  have hscale : (q : ℝ) ≤ P * T ^ (-(1 / 4 : ℝ)) := by
    have hpow : 1 ≤ T ^ (3 / 4 : ℝ) := Real.one_le_rpow hTone (by norm_num)
    have hcombine : T * T ^ (-(1 / 4 : ℝ)) = T ^ (3 / 4 : ℝ) := by
      calc
        T * T ^ (-(1 / 4 : ℝ)) =
            T ^ (1 : ℝ) * T ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_one]
        _ = T ^ ((1 : ℝ) + -(1 / 4 : ℝ)) :=
          (Real.rpow_add hTpos _ _).symm
        _ = T ^ (3 / 4 : ℝ) := by norm_num
    dsimp [P]
    rw [mul_assoc, hcombine]
    exact le_mul_of_one_le_right (Nat.cast_nonneg q) hpow

  have hmajor := hbound T hTT₁ P hPone q n hqpos hcop hscale

  have hnP : (n : ℝ) ≤ P := by
    calc
      (n : ℝ) ≤ q := by exact_mod_cast hnq
      _ ≤ (q : ℝ) * T := by
        exact le_mul_of_one_le_right (Nat.cast_nonneg q) hTone
      _ = P := rfl
  have hnceil : n ≤ ⌈2 * P⌉₊ := by
    have hPnonneg : 0 ≤ P := le_trans zero_le_one hPone
    have hcast : (n : ℝ) ≤ (⌈2 * P⌉₊ : ℕ) := by
      exact hnP.trans ((by linarith : P ≤ 2 * P).trans (Nat.le_ceil (2 * P)))
    exact_mod_cast hcast
  have hnmem : n ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p ↦ p % q = n % q) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hnceil⟩, trivial⟩
  have hlower : |c n| ≤ progressionSum c P q n := by
    unfold progressionSum
    exact Finset.single_le_sum (fun p _ ↦ abs_nonneg (c p)) hnmem

  have hcval : |c n| = (m + 1 : ℕ) := by
    dsimp [c, n]
    rw [ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_three]
    rw [abs_of_nonneg]
    positivity

  have htotient : Nat.totient q = 2 ^ (e - 1) := by
    dsimp [q]
    simpa using Nat.totient_prime_pow Nat.prime_two he
  have hq_twice_totient : q = 2 * Nat.totient q := by
    dsimp [q]
    rw [htotient]
    calc
      2 ^ e = 2 ^ ((e - 1) + 1) := by congr 1; omega
      _ = 2 ^ (e - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (e - 1) := by omega
  have htotientPos : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  have hratio : (q : ℝ) / (Nat.totient q : ℝ) = 2 := by
    have hqR : (q : ℝ) = 2 * (Nat.totient q : ℝ) := by
      exact_mod_cast hq_twice_totient
    rw [hqR]
    field_simp
  have hright :
      K * (P / (Nat.totient q : ℝ)) * (Real.log T) ^ C = B := by
    dsimp [P, B]
    rw [show (q : ℝ) * T / (Nat.totient q : ℝ) = 2 * T by
      calc
        (q : ℝ) * T / (Nat.totient q : ℝ) =
            ((q : ℝ) / (Nat.totient q : ℝ)) * T := by ring
        _ = 2 * T := by rw [hratio]]

  rw [hcval] at hlower
  rw [hright] at hmajor
  have hm_le_B : ((m + 1 : ℕ) : ℝ) ≤ B := hlower.trans hmajor
  exact (not_lt_of_ge hm_le_B) (hmB.trans (by exact_mod_cast Nat.lt_succ_self m))

end Zeta85
end RH

end
