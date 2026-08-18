/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Shiu/BoundedCoefficients.lean — the `k = 0` inhabitation theorem for the corrected
Shiu-type progression-majorant interface.

For coefficient sequences that are merely *bounded* (`|c n| ≤ K`, i.e. the `k = 0` divisor-bounded
class), the progression majorant is a genuine **theorem**, with explicit constants and no
logarithmic loss: uniformly in the full modulus range `q ≤ P`,

  `Σ_{p ≤ ⌈2P⌉, p ≡ r (q)} |c p| ≤ 5·K·(P/φ(q))`.

This is the sanity check that the corrected interface shape — `progressionSum c P q r ≤
K'·(P/φ(q))·(log P)^C` for `q ≤ P^{1-η}` — is inhabitable: the `k = 0` class inhabits it with the
explicit witnesses `(C, K', P₁) = (0, 5·K, 1)`, coprimality unused, full modulus range.  The real
content of the corrected interface is entirely in `k ≥ 1`, where the divisor function forces the
`φ(q)` saving and the logarithmic factor; here `φ(q) ≤ q` is thrown away, not exploited.

The counting core (kept `private`: a sibling unit owns the public counting API) is the trivial
residue-class count `#{n ∈ [1, ⌈2P⌉] : n ≡ r (q)} ≤ ⌈2P⌉/q + 1 ≤ 4·P/q` for `1 ≤ q ≤ P ≤ …`,
so the internal constant is in fact `4`; the public statements are relaxed to the target
constant `5`.
-/
import RH.Zeta85.Arith

namespace RH
namespace Zeta85
namespace Shiu

/-! ## Private counting core

`#{n ∈ [1, N] : n ≡ r (q)} ≤ N/q + 1`, by injecting the residue class into `[0, N/q]` via
`n ↦ n / q`; then the cast version `≤ 4·P/q` at `N = ⌈2P⌉₊`, `1 ≤ q ≤ P`. -/

/-- Residue-class count in `Finset.Icc 1 N`: at most `N / q + 1` (ℕ-division).  The map
`n ↦ n / q` is injective on a fixed residue class and lands in `Finset.range (N / q + 1)`. -/
private lemma boundedCoeff_count_le (q r N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card ≤ N / q + 1 := by
  have h : ((Finset.Icc 1 N).filter (fun n => n % q = r % q)).card
      ≤ (Finset.range (N / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n / q)
    · intro n hn
      have hn' : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).1
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp hn').2)))
    · intro a ha b hb hab
      have ha' : a % q = r % q := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb' : b % q = r % q := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have hab' : a / q = b / q := hab
      calc a = q * (a / q) + a % q := (Nat.div_add_mod a q).symm
        _ = q * (b / q) + b % q := by rw [hab', ha', hb']
        _ = b := Nat.div_add_mod b q
  simpa using h

/-- Cast counting bound: for `0 < q`, `1 ≤ P`, `(q : ℝ) ≤ P`, the residue-class count in
`Finset.Icc 1 ⌈2P⌉₊` is at most `4·P/q`, via `⌈2P⌉₊ ≤ 2P + 1` and `1 + q ≤ 2P`. -/
private lemma boundedCoeff_card_le (q r : ℕ) (hq : 0 < q) (P : ℝ) (hP : 1 ≤ P)
    (hqP : (q : ℝ) ≤ P) :
    ((((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun n => n % q = r % q)).card : ℕ) : ℝ)
      ≤ 4 * P / q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hceil : ((⌈2 * P⌉₊ : ℕ) : ℝ) ≤ 2 * P + 1 :=
    (Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * P)).le
  calc ((((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun n => n % q = r % q)).card : ℕ) : ℝ)
      ≤ ((⌈2 * P⌉₊ / q + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr (boundedCoeff_count_le q r ⌈2 * P⌉₊)
    _ = ((⌈2 * P⌉₊ / q : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ ((⌈2 * P⌉₊ : ℕ) : ℝ) / (q : ℝ) + 1 :=
        add_le_add
          (Nat.cast_div_le : ((⌈2 * P⌉₊ / q : ℕ) : ℝ) ≤ ((⌈2 * P⌉₊ : ℕ) : ℝ) / (q : ℝ)) le_rfl
    _ = (((⌈2 * P⌉₊ : ℕ) : ℝ) + (q : ℝ)) / (q : ℝ) := div_add_one hq0.ne'
    _ ≤ 4 * P / q :=
        -- `⌈2P⌉₊ + q ≤ (2P + 1) + q ≤ 4P`, using `1 ≤ P` and `q ≤ P`
        div_le_div_of_nonneg_right (by linarith) hq0.le

/-! ## The `k = 0` progression majorant -/

/-- **The `k = 0` progression majorant, full modulus range.**  If `|c n| ≤ K` for all `n`
(`K ≥ 0`), then uniformly for all moduli `1 ≤ q ≤ P` (with `1 ≤ P`) and all residues `r`,

  `progressionSum c P q r ≤ 5·K·(P/φ(q))`.

No coprimality of `r` and `q` is needed, and there is no logarithmic loss: the private counting
core gives the count `≤ 4·P/q`, and `φ(q) ≤ q` relaxes `P/q` to `P/φ(q)` (the stated constant is
the interface target `5`).  This is the `k = 0` instance of the corrected Shiu-type interface,
proved outright. -/
theorem boundedCoeff_progression_majorant (c : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ n, |c n| ≤ K) (q r : ℕ) (hq : 0 < q) (P : ℝ) (hP : 1 ≤ P)
    (hqP : (q : ℝ) ≤ P) :
    progressionSum c P q r ≤ 5 * K * (P / (Nat.totient q : ℝ)) := by
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hφ0 : (0 : ℝ) < (Nat.totient q : ℝ) := Nat.cast_pos.mpr hφ
  have hφq : (Nat.totient q : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr (Nat.totient_le q)
  have hP0 : (0 : ℝ) ≤ P := le_trans zero_le_one hP
  -- Step 1: the sum is at most `K` times the cardinality of the progression.
  have h1 : progressionSum c P q r
      ≤ ((((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q)).card : ℕ) : ℝ) * K := by
    have h := Finset.sum_le_card_nsmul
      ((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q))
      (fun p => |c p|) K (fun x _ => hc x)
    rw [nsmul_eq_mul] at h
    exact h
  -- Step 2: the cardinality is at most `4·P/q`.
  have h2 : ((((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q)).card : ℕ) : ℝ)
      ≤ 4 * P / q := boundedCoeff_card_le q r hq P hP hqP
  -- Step 3: assemble, trading `q` for `φ(q)` and `4` for the target constant `5`.
  calc progressionSum c P q r
      ≤ ((((Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q)).card : ℕ) : ℝ) * K := h1
    _ ≤ 4 * P / q * K := mul_le_mul_of_nonneg_right h2 hK
    _ = 4 * K * (P / (q : ℝ)) := by ring
    _ ≤ 4 * K * (P / (Nat.totient q : ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hP0 hφ0 hφq) (by linarith)
    _ ≤ 5 * K * (P / (Nat.totient q : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hP0 hφ0.le)

/-! ## The interface-shaped corollary -/

/-- **The corrected Shiu interface is inhabited at `k = 0`.**  This is
`boundedCoeff_progression_majorant` restated in the exact shape of the corrected Shiu-type
interface, with logarithmic exponent `C = 0`: for `0 < η < 1/2`, uniformly for all `P ≥ 1`,
all bounded `c`, and all moduli in the interface range `(q : ℝ) ≤ P^(1-η)` with `r` coprime
to `q`,

  `progressionSum c P q r ≤ 5·K·(P/φ(q))·(log P)^(0 : ℝ)`.

It exhibits the explicit witnesses `(C, K', P₁) = (0, 5·K, 1)` for the `k = 0` class of the
corrected Shiu interface — full modulus range (the interface range `q ≤ P^(1-η) ≤ P` is not even
needed in full), no logarithmic loss.  The hypotheses `0 < η < 1/2` and `Nat.Coprime r q` are
carried only to match the interface signature; the proof never uses them (`P^(1-η) ≤ P` for
`P ≥ 1` already reduces to the main theorem).  `Real.rpow_zero` makes the trailing factor `1`
unconditionally, even when `log P = 0`. -/
theorem boundedCoeff_shiu_shape (η : ℝ) (hη : 0 < η) (_hη2 : η < 1 / 2)
    (c : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hc : ∀ n, |c n| ≤ K)
    (q r : ℕ) (hq : 0 < q) (_hrq : Nat.Coprime r q)
    (P : ℝ) (hP : 1 ≤ P) (hqP : (q : ℝ) ≤ P ^ (1 - η)) :
    progressionSum c P q r ≤ 5 * K * (P / (Nat.totient q : ℝ)) * (Real.log P) ^ (0 : ℝ) := by
  have hqP' : (q : ℝ) ≤ P := by
    refine le_trans hqP ?_
    calc P ^ (1 - η) ≤ P ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
      _ = P := Real.rpow_one P
  rw [Real.rpow_zero, mul_one]
  exact boundedCoeff_progression_majorant c K hK hc q r hq P hP hqP'

/-- The `DivisorBounded` phrasing of `boundedCoeff_shiu_shape`: a sequence that is
divisor-bounded of order `k = 0` with constant `Kc ≥ 0` satisfies `|c n| ≤ Kc·τ(n)^0 = Kc`
for every `n` (including `n = 0`, since `x ^ (0 : ℕ) = 1` unconditionally), so the corrected
Shiu interface at `k = 0` holds for it with witnesses `(C, K', P₁) = (0, 5·Kc, 1)`. -/
theorem boundedCoeff_of_divisorBounded_zero (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2)
    (c : ℕ → ℝ) (Kc : ℝ) (hKc : 0 ≤ Kc) (hc : DivisorBounded c Kc 0)
    (q r : ℕ) (hq : 0 < q) (hrq : Nat.Coprime r q)
    (P : ℝ) (hP : 1 ≤ P) (hqP : (q : ℝ) ≤ P ^ (1 - η)) :
    progressionSum c P q r ≤ 5 * Kc * (P / (Nat.totient q : ℝ)) * (Real.log P) ^ (0 : ℝ) := by
  have hc' : ∀ n, |c n| ≤ Kc := fun n => by simpa using hc n
  exact boundedCoeff_shiu_shape η hη hη2 c Kc hKc hc' q r hq hrq P hP hqP

end Shiu
end Zeta85
end RH

#print axioms RH.Zeta85.Shiu.boundedCoeff_progression_majorant
#print axioms RH.Zeta85.Shiu.boundedCoeff_shiu_shape
#print axioms RH.Zeta85.Shiu.boundedCoeff_of_divisorBounded_zero
