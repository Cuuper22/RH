/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Shiu/TauPointwise.lean — the pointwise calculus of the generalized divisor
functions τ_K = ζ^K, where `ArithmeticFunction.zeta ^ K` is the K-th power of the
constant-one arithmetic function in the Dirichlet-convolution monoid, so that
`(ζ^K) n` counts the ordered factorizations `n = d₁ * ⋯ * d_K`.  This file is
standalone (Mathlib-only imports, everything unconditional and fully proved); it is the
shared pointwise keystone for the Shiu-type majorant estimates on `∑ τ(n)^k` over
arithmetic progressions.

Contents:

* `tauPow_succ_apply`        : `ζ^(K+1) n = ∑_{d ∣ n} ζ^K d` (convolution recursion);
* `tauPow_two_eq_sigma_zero` : `ζ^2 n = ArithmeticFunction.sigma 0 n = τ(n)`;
* `tauPow_isMultiplicative`  : `ζ^K` is multiplicative;
* `tauPow_apply_prime_pow`   : `ζ^K (p^m) = (m + K - 1).choose (K - 1)` for `p` prime,
  `1 ≤ K` (the classical formula for τ_K at prime powers);
* `tau_submultiplicative`    : `τ(m*n) ≤ τ(m) * τ(n)`;
* `tauPow_mul_le` (keystone) : `ζ^a n * ζ^b n ≤ ζ^(a*b) n` for `1 ≤ a`, `1 ≤ b` — the
  standard pointwise inequality `τ_a · τ_b ≤ τ_{a·b}` used in Landreau-type arguments;
* consumable corollaries `tau_sq_le_tauPow_four` (`τ(n)^2 ≤ ζ^4 n`),
  `tau_pow_four_le_tauPow_sixteen` (`τ(n)^4 ≤ ζ^16 n`), and
  `tau_pow_le_tauPow` (`τ(n)^j ≤ ζ^(2^j) n` for `n ≠ 0`).

References: P. Shiu, *A Brun–Titchmarsh theorem for multiplicative functions*, J. reine
angew. Math. 313 (1980), 161–170; B. Landreau, *Majorations de fonctions arithmétiques
en moyenne sur des ensembles de faible densité*, Sém. Théorie des Nombres Bordeaux
(1987/88); Iwaniec–Kowalski, *Analytic Number Theory*, §1.6.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

namespace RH
namespace Zeta85
namespace Shiu

open ArithmeticFunction

/-! ### Unfolding `ζ ^ K` -/

/-- Convolution-with-`ζ` recursion for the generalized divisor functions: applying one more
convolution factor of `ζ` sums the previous one over the divisors.  Standard; this is the
Dirichlet-series identity `ζ(s)^{K+1} = ζ(s) · ζ(s)^K` read off coefficientwise. -/
theorem tauPow_succ_apply (K n : ℕ) :
    (ArithmeticFunction.zeta ^ (K + 1)) n
      = ∑ d ∈ n.divisors, (ArithmeticFunction.zeta ^ K) d := by
  rw [pow_succ', zeta_mul_apply]

/-- `ζ^2` is the ordinary divisor-counting function `τ = σ₀`:
`ζ^2 n = ArithmeticFunction.sigma 0 n` for every `n` (both sides vanish at `0`). -/
theorem tauPow_two_eq_sigma_zero (n : ℕ) :
    (ArithmeticFunction.zeta ^ 2) n = ArithmeticFunction.sigma 0 n := by
  rw [sigma_zero_apply, pow_two, zeta_mul_apply, Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun d hd => zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne'

/-! ### Multiplicativity -/

/-- Every convolution power `ζ^K` of the multiplicative function `ζ` is multiplicative
(`K = 0` is the convolution identity). -/
theorem tauPow_isMultiplicative (K : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ K).IsMultiplicative :=
  isMultiplicative_zeta.pow

/-! ### Values at prime powers -/

/-- Hockey-stick identity in the form needed for the prime-power evaluation of `ζ^K`:
`∑_{j ≤ m} C(j + K, K) = C(m + K + 1, K + 1)`. -/
theorem tau_sum_range_choose (m K : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (j + K).choose K = (m + K + 1).choose (K + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, show m + 1 + K = m + K + 1 from by omega,
        Nat.choose_succ_succ' (m + K + 1) K]
      omega

/-- Value of `ζ^(K+1)` at a prime power, subtraction-free form:
`ζ^(K+1) (p^m) = C(m + K, K)`, the number of ways to write `p^m` as an ordered product of
`K + 1` factors (stars and bars). -/
theorem tauPow_apply_prime_pow_succ {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∀ m : ℕ, (ArithmeticFunction.zeta ^ (K + 1)) (p ^ m) = (m + K).choose K := by
  induction K with
  | zero =>
      intro m
      simp only [Nat.zero_add, pow_one, Nat.add_zero, Nat.choose_zero_right]
      exact zeta_apply_ne (pow_ne_zero m hp.ne_zero)
  | succ K ih =>
      intro m
      rw [tauPow_succ_apply, Nat.sum_divisors_prime_pow hp]
      simp only [ih]
      rw [tau_sum_range_choose]
      congr 1

/-- Value of the generalized divisor function at a prime power: for `p` prime and `1 ≤ K`,
`ζ^K (p^m) = (m + K - 1).choose (K - 1)`.  Classical; cf. Iwaniec–Kowalski §1.6. -/
theorem tauPow_apply_prime_pow {p : ℕ} (hp : p.Prime) {K : ℕ} (hK : 1 ≤ K) (m : ℕ) :
    (ArithmeticFunction.zeta ^ K) (p ^ m) = (m + K - 1).choose (K - 1) := by
  obtain ⟨K', rfl⟩ := Nat.exists_eq_add_of_le' hK
  rw [tauPow_apply_prime_pow_succ hp]
  congr 1

/-! ### Submultiplicativity of τ -/

/-- `τ` is submultiplicative: `τ(m*n) ≤ τ(m) * τ(n)` for all `m`, `n` (a divisor of `m*n`
is a product of a divisor of `m` and a divisor of `n`). -/
theorem tau_submultiplicative (m n : ℕ) :
    ArithmeticFunction.sigma 0 (m * n)
      ≤ ArithmeticFunction.sigma 0 m * ArithmeticFunction.sigma 0 n := by
  rw [sigma_zero_apply, sigma_zero_apply, sigma_zero_apply, Nat.divisors_mul]
  exact Finset.card_mul_le

/-! ### The keystone: `τ_a · τ_b ≤ τ_{a·b}` pointwise -/

/-- Ratio identity for binomial coefficients, in pure `ℕ` (no division):
`C(m + 1 + K, K) * (m + 1) = C(m + K, K) * (m + K + 1)`. -/
theorem tau_choose_ratio (m K : ℕ) :
    (m + 1 + K).choose K * (m + 1) = (m + K).choose K * (m + K + 1) := by
  have h1 : (m + 1 + K).choose K = (m + K + 1).choose (m + 1) := by
    rw [show m + 1 + K = K + (m + 1) from by omega, Nat.choose_symm_add,
      show K + (m + 1) = m + K + 1 from by omega]
  have h2 : (m + K + 1) * (m + K).choose m = (m + K + 1).choose (m + 1) * (m + 1) :=
    Nat.add_one_mul_choose_eq (m + K) m
  have h3 : (m + K).choose m = (m + K).choose K := Nat.choose_symm_add
  calc (m + 1 + K).choose K * (m + 1)
      = (m + K + 1).choose (m + 1) * (m + 1) := by rw [h1]
    _ = (m + K + 1) * (m + K).choose m := h2.symm
    _ = (m + K + 1) * (m + K).choose K := by rw [h3]
    _ = (m + K).choose K * (m + K + 1) := Nat.mul_comm _ _

/-- Combinatorial core of the keystone at a prime power, in the subtraction-free
parametrization `a = A + 1`, `b = B + 1`, `a*b = (A*B + A + B) + 1`:
`C(m + A, A) * C(m + B, B) ≤ C(m + A*B + A + B, A*B + A + B)`.
Induction on `m` via `tau_choose_ratio`; the cross-multiplied step reduces to
`(m + A + 1) * (m + B + 1) ≤ (m + C + 1) * (m + 1)` with `C = A*B + A + B`, which holds
because the difference of the two sides is `m * A * B ≥ 0`. -/
theorem tau_choose_mul_le_choose (A B m : ℕ) :
    (m + A).choose A * (m + B).choose B
      ≤ (m + (A * B + A + B)).choose (A * B + A + B) := by
  induction m with
  | zero => simp [Nat.choose_self]
  | succ m IH =>
      set C := A * B + A + B with hC
      have harith : (m + A + 1) * (m + B + 1) ≤ (m + C + 1) * (m + 1) :=
        Nat.le.intro (k := m * (A * B)) (by rw [hC]; ring)
      have key : ((m + 1 + A).choose A * (m + 1 + B).choose B) * ((m + 1) * (m + 1))
          ≤ (m + 1 + C).choose C * ((m + 1) * (m + 1)) := by
        calc ((m + 1 + A).choose A * (m + 1 + B).choose B) * ((m + 1) * (m + 1))
            = ((m + 1 + A).choose A * (m + 1)) * ((m + 1 + B).choose B * (m + 1)) := by
              ring
          _ = ((m + A).choose A * (m + A + 1)) * ((m + B).choose B * (m + B + 1)) := by
              rw [tau_choose_ratio, tau_choose_ratio]
          _ = ((m + A).choose A * (m + B).choose B) * ((m + A + 1) * (m + B + 1)) := by
              ring
          _ ≤ (m + C).choose C * ((m + C + 1) * (m + 1)) := Nat.mul_le_mul IH harith
          _ = ((m + C).choose C * (m + C + 1)) * (m + 1) := by ring
          _ = ((m + 1 + C).choose C * (m + 1)) * (m + 1) := by rw [tau_choose_ratio]
          _ = (m + 1 + C).choose C * ((m + 1) * (m + 1)) := by ring
      exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos m.succ_pos m.succ_pos)

/-- **Keystone**: the generalized divisor functions are pointwise supermultiplicative in
the order, `ζ^a n * ζ^b n ≤ ζ^(a*b) n` for `1 ≤ a`, `1 ≤ b` and every `n`.  Standard;
cf. the Dirichlet-series identity `τ_a · τ_b ≤ τ_{a·b}` pointwise, used in Landreau-type
arguments.  Both sides are multiplicative in `n`, so the proof reduces to prime powers,
where it is `tau_choose_mul_le_choose`. -/
theorem tauPow_mul_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ) :
    (ArithmeticFunction.zeta ^ a) n * (ArithmeticFunction.zeta ^ b) n
      ≤ (ArithmeticFunction.zeta ^ (a * b)) n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [ArithmeticFunction.map_zero]
  | one =>
      rw [(tauPow_isMultiplicative a).map_one, (tauPow_isMultiplicative b).map_one,
        (tauPow_isMultiplicative (a * b)).map_one]
      omega
  | prime_pow p m hp hm =>
      obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le' ha
      obtain ⟨B, rfl⟩ := Nat.exists_eq_add_of_le' hb
      rw [show (A + 1) * (B + 1) = A * B + A + B + 1 from by ring,
        tauPow_apply_prime_pow_succ hp, tauPow_apply_prime_pow_succ hp,
        tauPow_apply_prime_pow_succ hp]
      exact tau_choose_mul_le_choose A B m
  | coprime x y hx hy hxy IHx IHy =>
      rw [(tauPow_isMultiplicative a).map_mul_of_coprime hxy,
        (tauPow_isMultiplicative b).map_mul_of_coprime hxy,
        (tauPow_isMultiplicative (a * b)).map_mul_of_coprime hxy,
        mul_mul_mul_comm]
      exact Nat.mul_le_mul IHx IHy

/-! ### Consumable corollaries -/

/-- `τ(n)^2 ≤ ζ^4 n` for every `n`: the keystone at `(a, b) = (2, 2)` together with
`τ = ζ^2`. -/
theorem tau_sq_le_tauPow_four (n : ℕ) :
    ArithmeticFunction.sigma 0 n ^ 2 ≤ (ArithmeticFunction.zeta ^ 4) n := by
  rw [← tauPow_two_eq_sigma_zero n, pow_two]
  exact tauPow_mul_le (by omega) (by omega) n

/-- `τ(n)^4 ≤ ζ^16 n` for every `n`: square `tau_sq_le_tauPow_four` and apply the
keystone at `(a, b) = (4, 4)`. -/
theorem tau_pow_four_le_tauPow_sixteen (n : ℕ) :
    ArithmeticFunction.sigma 0 n ^ 4 ≤ (ArithmeticFunction.zeta ^ 16) n := by
  calc ArithmeticFunction.sigma 0 n ^ 4
      = (ArithmeticFunction.sigma 0 n ^ 2) ^ 2 := by ring
    _ ≤ ((ArithmeticFunction.zeta ^ 4) n) ^ 2 :=
        Nat.pow_le_pow_left (tau_sq_le_tauPow_four n) 2
    _ = (ArithmeticFunction.zeta ^ 4) n * (ArithmeticFunction.zeta ^ 4) n := pow_two _
    _ ≤ (ArithmeticFunction.zeta ^ 16) n := tauPow_mul_le (by omega) (by omega) n

/-- General iterate of the keystone: `τ(n)^j ≤ ζ^(2^j) n` for `n ≠ 0` and every `j`
(the hypothesis `n ≠ 0` is needed at `j = 0`, where the right-hand side is `ζ n`). -/
theorem tau_pow_le_tauPow {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    ArithmeticFunction.sigma 0 n ^ j ≤ (ArithmeticFunction.zeta ^ (2 ^ j)) n := by
  induction j with
  | zero => simp [pow_zero, pow_one, zeta_apply_ne hn]
  | succ j ih =>
      calc ArithmeticFunction.sigma 0 n ^ (j + 1)
          = ArithmeticFunction.sigma 0 n ^ j * ArithmeticFunction.sigma 0 n :=
            pow_succ _ _
        _ ≤ (ArithmeticFunction.zeta ^ (2 ^ j)) n * (ArithmeticFunction.zeta ^ 2) n :=
            Nat.mul_le_mul ih (le_of_eq (tauPow_two_eq_sigma_zero n).symm)
        _ ≤ (ArithmeticFunction.zeta ^ (2 ^ j * 2)) n :=
            tauPow_mul_le (Nat.one_le_two_pow) (by omega) n
        _ = (ArithmeticFunction.zeta ^ (2 ^ (j + 1))) n := by rw [pow_succ]

end Shiu
end Zeta85
end RH

#print axioms RH.Zeta85.Shiu.tauPow_succ_apply
#print axioms RH.Zeta85.Shiu.tauPow_two_eq_sigma_zero
#print axioms RH.Zeta85.Shiu.tauPow_isMultiplicative
#print axioms RH.Zeta85.Shiu.tauPow_apply_prime_pow
#print axioms RH.Zeta85.Shiu.tau_submultiplicative
#print axioms RH.Zeta85.Shiu.tauPow_mul_le
#print axioms RH.Zeta85.Shiu.tau_sq_le_tauPow_four
#print axioms RH.Zeta85.Shiu.tau_pow_four_le_tauPow_sixteen
#print axioms RH.Zeta85.Shiu.tau_pow_le_tauPow
