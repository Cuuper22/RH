/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.HBDepthFour
import RH.Zeta85.Discharge.BBLRGCDAllocation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.CardIntervalMod

/-!
# Divisor-dependent refinement of a terminal coefficient

The fixed asymmetric support box killed by `EtaSuperpositionObstruction`
cannot represent integers which have no divisor in that box.  This module
changes the order of operations: for each integer it first selects the
largest divisor below the requested cutoff, and only then forms the
convolution piece.

The resulting identity is pointwise and exact for an arbitrary coefficient.
It loses no prime, prime-square, logarithmic, or Möbius contribution.  The
selected divisor satisfies a sharp alternative: it is within the requested
multiplicative scale, or every prime in the complementary factor is larger
than the scale tolerance.  Thus the former balanced block is split into a
literal asymmetric convolution family plus an explicit rough-cofactor
family, rather than being discarded or replaced by a majorant.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace RH
namespace Zeta85
namespace EtaDivisorRefinement

/-- The largest divisor of `n` not exceeding `R`.  The value is total; the
theorems below use the natural nondegenerate hypotheses `n != 0`, `0 < R`. -/
def canonicalDivisor (n R : ℕ) : ℕ :=
  Nat.findGreatest (fun d => d ∣ n) R

theorem canonicalDivisor_le (n R : ℕ) : canonicalDivisor n R ≤ R := by
  exact Nat.findGreatest_le R

theorem canonicalDivisor_pos {n R : ℕ} (hR : 0 < R) :
    0 < canonicalDivisor n R := by
  rw [canonicalDivisor, Nat.findGreatest_pos]
  exact ⟨1, by norm_num, hR, one_dvd n⟩

theorem canonicalDivisor_dvd {n R : ℕ} (hR : 0 < R) :
    canonicalDivisor n R ∣ n := by
  unfold canonicalDivisor
  exact Nat.findGreatest_spec (P := fun d => d ∣ n) (m := 1) hR (one_dvd n)

theorem divisor_le_canonical {n R d : ℕ} (hdR : d ≤ R) (hdn : d ∣ n) :
    d ≤ canonicalDivisor n R := by
  exact Nat.le_findGreatest hdR hdn

/-- The complementary factor associated to the canonical divisor. -/
def canonicalCofactor (n R : ℕ) : ℕ := n / canonicalDivisor n R

theorem canonical_factorization {n R : ℕ} (hR : 0 < R) :
    canonicalDivisor n R * canonicalCofactor n R = n := by
  exact Nat.mul_div_cancel' (canonicalDivisor_dvd hR)

theorem canonicalCofactor_pos {n R : ℕ} (hn : n ≠ 0) (hR : 0 < R) :
    0 < canonicalCofactor n R := by
  have hdpos := canonicalDivisor_pos (n := n) hR
  have hdle : canonicalDivisor n R ≤ n :=
    Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hn) (canonicalDivisor_dvd hR)
  exact Nat.div_pos hdle hdpos

theorem canonicalCofactor_one_lt {n R : ℕ} (hnR : R < n) (hR : 0 < R) :
    1 < canonicalCofactor n R := by
  have hn : n ≠ 0 := Nat.ne_zero_of_lt (hR.trans hnR)
  have hqpos := canonicalCofactor_pos hn hR
  by_contra hq
  have hqone : canonicalCofactor n R = 1 := by omega
  have hfactor := canonical_factorization (n := n) hR
  rw [hqone, mul_one] at hfactor
  have hdle := canonicalDivisor_le n R
  omega

/-- Multiplying the selected divisor by any prime from its cofactor crosses
the cutoff.  This is the maximal-divisor mechanism behind the refinement. -/
theorem cutoff_lt_mul_prime_of_dvd_cofactor {n R q : ℕ} (hR : 0 < R)
    (hqprime : q.Prime) (hq : q ∣ canonicalCofactor n R) :
    R < canonicalDivisor n R * q := by
  let d := canonicalDivisor n R
  have hdpos : 0 < d := canonicalDivisor_pos (n := n) hR
  have hfactor : d * canonicalCofactor n R = n :=
    canonical_factorization (n := n) hR
  have hdq_dvd : d * q ∣ n := by
    obtain ⟨k, hk⟩ := hq
    refine ⟨k, ?_⟩
    rw [← hfactor, hk]
    ac_rfl
  by_contra hcut
  have hdq_le : d * q ≤ R := Nat.le_of_not_gt hcut
  have hmax : d * q ≤ d := divisor_le_canonical hdq_le hdq_dvd
  have hqone : 1 < q := hqprime.one_lt
  nlinarith

/-- Exact regular/rough dichotomy.  Either the chosen divisor is within a
factor `B` of the cutoff, or the complementary factor is `B`-rough. -/
theorem canonical_regular_or_rough {n R B : ℕ} (hR : 0 < R) :
    R < canonicalDivisor n R * B ∨
      ∀ q : ℕ, q.Prime → q ∣ canonicalCofactor n R → B < q := by
  by_cases hregular : R < canonicalDivisor n R * B
  · exact Or.inl hregular
  · right
    intro q hqprime hq
    have hcross := cutoff_lt_mul_prime_of_dvd_cofactor hR hqprime hq
    have hupper : canonicalDivisor n R * B ≤ R := Nat.le_of_not_gt hregular
    have hdpos := canonicalDivisor_pos (n := n) hR
    nlinarith

/-- A rough number below the square of the roughness threshold is prime. -/
theorem prime_of_rough_of_lt_sq {s B : ℕ} (hs : 1 < s)
    (hrough : ∀ q : ℕ, q.Prime → q ∣ s → B < q)
    (hsize : s < (B + 1) ^ 2) : s.Prime := by
  by_contra hprime
  obtain ⟨a, b, ha_lt, hb_lt, hab⟩ :=
    (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hprime
  have ha_one : a ≠ 1 := by
    intro ha
    subst a
    simp at hab
    omega
  have hb_one : b ≠ 1 := by
    intro hb
    subst b
    simp at hab
    omega
  have ha_pos : 0 < a := by
    by_contra ha0
    simp_all
  have hb_pos : 0 < b := by
    by_contra hb0
    simp_all
  obtain ⟨p, hpprime, hpa⟩ := Nat.exists_prime_and_dvd ha_one
  obtain ⟨q, hqprime, hqb⟩ := Nat.exists_prime_and_dvd hb_one
  have hpas : p ∣ s := hpa.trans ⟨b, hab.symm⟩
  have hqbs : q ∣ s := hqb.trans ⟨a, by simpa [mul_comm] using hab.symm⟩
  have hBp' : B < p := hrough p hpprime hpas
  have hBq' : B < q := hrough q hqprime hqbs
  have hBp : B + 1 ≤ p := by omega
  have hBq : B + 1 ≤ q := by omega
  have hp_le : p ≤ a := Nat.le_of_dvd ha_pos hpa
  have hq_le : q ≤ b := Nat.le_of_dvd hb_pos hqb
  have hsquare_le : (B + 1) ^ 2 ≤ s := by
    calc
      (B + 1) ^ 2 = (B + 1) * (B + 1) := by ring
      _ ≤ p * q := Nat.mul_le_mul hBp hBq
      _ ≤ a * b := Nat.mul_le_mul hp_le hq_le
      _ = s := hab
  omega

/-- Roughness passes to every positive divisor. -/
theorem rough_of_dvd {r s B : ℕ}
    (hrough : ∀ q : ℕ, q.Prime → q ∣ s → B < q) (hrs : r ∣ s) :
    ∀ q : ℕ, q.Prime → q ∣ r → B < q := by
  intro q hqprime hqr
  exact hrough q hqprime (hqr.trans hrs)

/-- A nontrivial rough number itself crosses the roughness threshold. -/
theorem threshold_lt_of_rough {s B : ℕ} (hs : 1 < s)
    (hrough : ∀ q : ℕ, q.Prime → q ∣ s → B < q) : B < s := by
  obtain ⟨p, hpprime, hps⟩ := Nat.exists_prime_and_dvd (by omega : s ≠ 1)
  exact (hrough p hpprime hps).trans_le (Nat.le_of_dvd (by omega) hps)

/-- A rough number below the cube of the threshold has at most two prime
factors: it is prime or the product of two primes. -/
theorem prime_or_product_of_two_primes_of_rough_of_lt_cube {s B : ℕ}
    (hs : 1 < s)
    (hrough : ∀ q : ℕ, q.Prime → q ∣ s → B < q)
    (hsize : s < (B + 1) ^ 3) :
    s.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ s = p * q := by
  by_cases hsprime : s.Prime
  · exact Or.inl hsprime
  · right
    obtain ⟨a, b, ha_lt, hb_lt, hab⟩ :=
      (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hsprime
    have ha_one : a ≠ 1 := by
      intro ha
      subst a
      simp at hab
      omega
    have hb_one : b ≠ 1 := by
      intro hb
      subst b
      simp at hab
      omega
    have ha_pos : 0 < a := by
      by_contra ha0
      simp_all
    have hb_pos : 0 < b := by
      by_contra hb0
      simp_all
    have ha_one_lt : 1 < a := by omega
    have hb_one_lt : 1 < b := by omega
    have ha_dvd : a ∣ s := ⟨b, hab.symm⟩
    have hb_dvd : b ∣ s := ⟨a, by simpa [mul_comm] using hab.symm⟩
    have hrough_a := rough_of_dvd hrough ha_dvd
    have hrough_b := rough_of_dvd hrough hb_dvd
    have hBa : B + 1 ≤ a := by
      have := threshold_lt_of_rough ha_one_lt hrough_a
      omega
    have hBb : B + 1 ≤ b := by
      have := threshold_lt_of_rough hb_one_lt hrough_b
      omega
    have ha_sq : a < (B + 1) ^ 2 := by
      by_contra hnot
      have hsq : (B + 1) ^ 2 ≤ a := Nat.le_of_not_gt hnot
      have hcube : (B + 1) ^ 3 ≤ s := by
        calc
          (B + 1) ^ 3 = (B + 1) ^ 2 * (B + 1) := by ring
          _ ≤ a * b := Nat.mul_le_mul hsq hBb
          _ = s := hab
      omega
    have hb_sq : b < (B + 1) ^ 2 := by
      by_contra hnot
      have hsq : (B + 1) ^ 2 ≤ b := Nat.le_of_not_gt hnot
      have hcube : (B + 1) ^ 3 ≤ s := by
        calc
          (B + 1) ^ 3 = (B + 1) * (B + 1) ^ 2 := by ring
          _ ≤ a * b := Nat.mul_le_mul hBa hsq
          _ = s := hab
      omega
    exact ⟨a, b, prime_of_rough_of_lt_sq ha_one_lt hrough_a ha_sq,
      prime_of_rough_of_lt_sq hb_one_lt hrough_b hb_sq, hab.symm⟩

/-- Every prime factor in a rough number crosses the threshold. -/
theorem threshold_succ_le_of_mem_primeFactorsList {s B p : ℕ}
    (hrough : ∀ q : ℕ, q.Prime → q ∣ s → B < q)
    (hp : p ∈ s.primeFactorsList) : B + 1 ≤ p := by
  have hpprime := Nat.prime_of_mem_primeFactorsList hp
  have hpdvd := Nat.dvd_of_mem_primeFactorsList hp
  have hBp := hrough p hpprime hpdvd
  omega

theorem pow_length_le_list_prod {L : List ℕ} {B : ℕ}
    (hL : ∀ p ∈ L, B + 1 ≤ p) : (B + 1) ^ L.length ≤ L.prod := by
  induction L with
  | nil => simp
  | cons p ps ih =>
      calc
        (B + 1) ^ (p :: ps).length =
            (B + 1) * (B + 1) ^ ps.length := by simp [pow_succ']
        _ ≤ p * ps.prod := Nat.mul_le_mul (hL p (by simp))
          (ih (fun q hq => hL q (by simp [hq])))
        _ = (p :: ps).prod := by simp

/-- The product of the prime-factor list of a `B`-rough integer is bounded
below by `(B+1)` to the number of factors, with multiplicity. -/
theorem rough_pow_cardFactors_le {s B : ℕ} (hs : s ≠ 0)
    (hrough : ∀ q : ℕ, q.Prime → q ∣ s → B < q) :
    (B + 1) ^ s.primeFactorsList.length ≤ s := by
  calc
    (B + 1) ^ s.primeFactorsList.length ≤ s.primeFactorsList.prod :=
      pow_length_le_list_prod
        (fun p hp => threshold_succ_le_of_mem_primeFactorsList hrough hp)
    _ = s := Nat.prod_primeFactorsList hs

/-- Uniform retained-prime depth: below the `r`th threshold power a rough
integer has strictly fewer than `r` prime factors, counted with multiplicity. -/
theorem cardFactors_lt_of_rough_of_lt_pow {s B r : ℕ} (hs : s ≠ 0)
    (hrough : ∀ q : ℕ, q.Prime → q ∣ s → B < q)
    (hsize : s < (B + 1) ^ r) : s.primeFactorsList.length < r := by
  by_contra hnot
  have hrle : r ≤ s.primeFactorsList.length := Nat.le_of_not_gt hnot
  have hpow : (B + 1) ^ r ≤ (B + 1) ^ s.primeFactorsList.length :=
    Nat.pow_le_pow_right (by omega) hrle
  exact (not_le_of_gt hsize) (hpow.trans (rough_pow_cardFactors_le hs hrough))

/-! ## Divisor-bound transport through a retained fiber -/

/-- Allocate a divisor of `m * s` between the fixed retained factor `m` and
the running factor `s`. -/
def divisorSplit (m d : ℕ) : ℕ × ℕ :=
  (m.gcd d, d / m.gcd d)

theorem divisorSplit_mem_product {m s d : ℕ} (hm : m ≠ 0) (hs : s ≠ 0)
    (hd : d ∈ (m * s).divisors) :
    divisorSplit m d ∈ m.divisors ×ˢ s.divisors := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdmul : d ∣ m * s := Nat.dvd_of_mem_divisors hd
  apply Finset.mem_product.mpr
  constructor
  · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left m d, hm⟩
  · apply Nat.mem_divisors.mpr
    refine ⟨?_, hs⟩
    exact RH.Zeta85.BBLRGCDAllocation.quotient_gcd_dvd_inner hdpos
      ⟨m, s, hdmul⟩

theorem divisorSplit_injOn (m n : ℕ) :
    Set.InjOn (divisorSplit m) (n.divisors : Set ℕ) := by
  intro d hd e he hde
  have hdprod : (divisorSplit m d).1 * (divisorSplit m d).2 = d := by
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right m d)
  have heprod : (divisorSplit m e).1 * (divisorSplit m e).2 = e := by
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right m e)
  calc
    d = (divisorSplit m d).1 * (divisorSplit m d).2 := hdprod.symm
    _ = (divisorSplit m e).1 * (divisorSplit m e).2 := congrArg (fun x => x.1 * x.2) hde
    _ = e := heprod

/-- The divisor-counting function is submultiplicative.  The proof uses the
same canonical gcd allocation that underlies the BBLR change of variables. -/
theorem card_divisors_mul_le (m s : ℕ) :
    (m * s).divisors.card ≤ m.divisors.card * s.divisors.card := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hs : s = 0
  · simp [hs]
  calc
    (m * s).divisors.card ≤ (m.divisors ×ˢ s.divisors).card := by
      exact Finset.card_le_card_of_injOn (divisorSplit m)
        (fun d hd => divisorSplit_mem_product hm hs hd)
        (divisorSplit_injOn m (m * s))
    _ = m.divisors.card * s.divisors.card := Finset.card_product _ _

theorem sigma_zero_mul_le (m s : ℕ) :
    ArithmeticFunction.sigma 0 (m * s) ≤
      ArithmeticFunction.sigma 0 m * ArithmeticFunction.sigma 0 s := by
  simpa only [ArithmeticFunction.sigma_zero_apply] using card_divisors_mul_le m s

theorem card_divisors_list_prod_le_two_pow_length (L : List ℕ)
    (hprime : ∀ p ∈ L, p.Prime) :
    L.prod.divisors.card ≤ 2 ^ L.length := by
  induction L with
  | nil => simp
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hpcard : p.divisors.card = 2 := by
        rw [hp.divisors]
        exact Finset.card_pair (Ne.symm hp.ne_one)
      calc
        (p :: ps).prod.divisors.card = (p * ps.prod).divisors.card := by simp
        _ ≤ p.divisors.card * ps.prod.divisors.card :=
          card_divisors_mul_le p ps.prod
        _ ≤ 2 * 2 ^ ps.length := by
          exact Nat.mul_le_mul hpcard.le (ih hps)
        _ = 2 ^ (p :: ps).length := by simp [pow_succ']

/-- The divisor count of a nonzero integer is at most two to its number of
prime factors, counted with multiplicity. -/
theorem card_divisors_le_two_pow_cardFactors {s : ℕ} (hs : s ≠ 0) :
    s.divisors.card ≤ 2 ^ s.primeFactorsList.length := by
  calc
    s.divisors.card = s.primeFactorsList.prod.divisors.card := by
      rw [Nat.prod_primeFactorsList hs]
    _ ≤ 2 ^ s.primeFactorsList.length :=
      card_divisors_list_prod_le_two_pow_length s.primeFactorsList
        (fun p hp => Nat.prime_of_mem_primeFactorsList hp)

/-- A divisor-bounded coefficient becomes uniformly bounded on a set of
bounded prime depth. -/
theorem abs_le_of_divisorBounded_of_prime_depth {c : ℕ → ℝ} {K : ℝ}
    {k s r : ℕ} (hK : 0 ≤ K) (hc : DivisorBounded c K k)
    (hs : s ≠ 0) (hdepth : s.primeFactorsList.length < r) :
    |c s| ≤ K * (((2 : ℕ) ^ r : ℕ) : ℝ) ^ k := by
  have htauNat : ArithmeticFunction.sigma 0 s ≤ 2 ^ r := by
    rw [ArithmeticFunction.sigma_zero_apply]
    exact (card_divisors_le_two_pow_cardFactors hs).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt hdepth))
  have htau :
      ((ArithmeticFunction.sigma 0 s : ℕ) : ℝ) ≤ (((2 : ℕ) ^ r : ℕ) : ℝ) := by
    exact_mod_cast htauNat
  exact (hc s).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) htau k) hK)

theorem sigma_zero_le_of_dvd {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    ArithmeticFunction.sigma 0 d ≤ ArithmeticFunction.sigma 0 n := by
  simpa only [ArithmeticFunction.sigma_zero_apply] using
    Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd)

theorem divisorBounded_mul {f g : HBDepthFour.AF} {K L : ℝ} {k l : ℕ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hf : DivisorBounded f K k) (hg : DivisorBounded g L l) :
    DivisorBounded (f * g : HBDepthFour.AF) (K * L) (k + l + 1) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ArithmeticFunction.mul_apply]
    let tau : ℝ := ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ)
    have htau0 : 0 ≤ tau := by positivity
    calc
      |∑ xy ∈ n.divisorsAntidiagonal, f xy.1 * g xy.2| ≤
          ∑ xy ∈ n.divisorsAntidiagonal, |f xy.1 * g xy.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _xy ∈ n.divisorsAntidiagonal,
          (K * tau ^ k) * (L * tau ^ l) := by
        gcongr with xy hxy
        obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hxy
        have hx_dvd : xy.1 ∣ n := ⟨xy.2, hprod.symm⟩
        have hy_dvd : xy.2 ∣ n :=
          ⟨xy.1, by simpa [mul_comm] using hprod.symm⟩
        have htxNat := sigma_zero_le_of_dvd hn hx_dvd
        have htyNat := sigma_zero_le_of_dvd hn hy_dvd
        have htx :
            ((ArithmeticFunction.sigma 0 xy.1 : ℕ) : ℝ) ≤ tau := by
          dsimp only [tau]
          exact_mod_cast htxNat
        have hty :
            ((ArithmeticFunction.sigma 0 xy.2 : ℕ) : ℝ) ≤ tau := by
          dsimp only [tau]
          exact_mod_cast htyNat
        have hfx : |f xy.1| ≤ K * tau ^ k :=
          (hf xy.1).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) htx k) hK)
        have hgy : |g xy.2| ≤ L * tau ^ l :=
          (hg xy.2).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hty l) hL)
        rw [abs_mul]
        exact mul_le_mul hfx hgy (abs_nonneg _) (mul_nonneg hK (pow_nonneg htau0 k))
      _ = (K * L) * tau ^ (k + l + 1) := by
        rw [Nat.sum_divisorsAntidiagonal
          (fun _ _ => (K * tau ^ k) * (L * tau ^ l))]
        simp only [Finset.sum_const, nsmul_eq_mul]
        dsimp only [tau]
        rw [← ArithmeticFunction.sigma_zero_apply]
        ring

theorem divisorBounded_smul {f : HBDepthFour.AF} {K : ℝ} {k : ℕ}
    (r : ℝ) (hf : DivisorBounded f K k) :
    DivisorBounded (r • f : HBDepthFour.AF) (|r| * K) k := by
  intro n
  change |r * f n| ≤ (|r| * K) * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
  rw [abs_mul]
  calc
    |r| * |f n| ≤ |r| *
        (K * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left (hf n) (abs_nonneg r)
    _ = (|r| * K) * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k := by ring

theorem divisorBounded_add {f g : HBDepthFour.AF} {K L : ℝ} {k : ℕ}
    (hf : DivisorBounded f K k) (hg : DivisorBounded g L k) :
    DivisorBounded (f + g : HBDepthFour.AF) (K + L) k := by
  intro n
  change |f n + g n| ≤
    (K + L) * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
  calc
    |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ K * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k +
        L * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k :=
      add_le_add (hf n) (hg n)
    _ = (K + L) * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k := by ring

theorem divisorBounded_sub {f g : HBDepthFour.AF} {K L : ℝ} {k : ℕ}
    (hf : DivisorBounded f K k) (hg : DivisorBounded g L k) :
    DivisorBounded (f - g : HBDepthFour.AF) (K + L) k := by
  intro n
  change |f n - g n| ≤
    (K + L) * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k
  calc
    |f n - g n| ≤ |f n| + |g n| := abs_sub _ _
    _ ≤ K * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k +
        L * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k :=
      add_le_add (hf n) (hg n)
    _ = (K + L) * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ k := by ring

theorem divisorBounded_mono_exponent {f : HBDepthFour.AF} {K : ℝ} {k l : ℕ}
    (hK : 0 ≤ K) (hf : DivisorBounded f K k) (hkl : k ≤ l) :
    DivisorBounded f K l := by
  intro n
  by_cases hn : n = 0
  · subst n
    have hnonneg : (0 : ℝ) ≤ K * 0 ^ l :=
      mul_nonneg hK (pow_nonneg (by norm_num) l)
    simpa using hnonneg
  · have htau :
        (1 : ℝ) ≤ ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) := by
      exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn
    exact (hf n).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ htau hkl) hK)

/-! ## The log-free depth-four coefficient -/

/-- The depth-four Heath--Brown coefficient before its final literal
logarithm convolution. -/
def hb4Core (Z : ℕ) : HBDepthFour.AF :=
  (4 : ℝ) • HBDepthFour.muCut Z
    - (6 : ℝ) • ((HBDepthFour.muCut Z) ^ 2 *
        (ArithmeticFunction.zeta : HBDepthFour.AF))
    + (4 : ℝ) • ((HBDepthFour.muCut Z) ^ 3 *
        (ArithmeticFunction.zeta : HBDepthFour.AF) ^ 2)
    - ((HBDepthFour.muCut Z) ^ 4 *
        (ArithmeticFunction.zeta : HBDepthFour.AF) ^ 3)

/-- Exact source-weight separation: the unbounded logarithm remains a
literal final convolution factor rather than being hidden in an arbitrary
coefficient. -/
theorem hb4_eq_core_mul_log (Z : ℕ) :
    HBDepthFour.hb4 Z = hb4Core Z * ArithmeticFunction.log := by
  unfold HBDepthFour.hb4 hb4Core
  simp only [Algebra.smul_def]
  rw [show algebraMap ℝ HBDepthFour.AF (4 : ℝ) = (4 : HBDepthFour.AF) by
      exact map_natCast (algebraMap ℝ HBDepthFour.AF) 4]
  rw [show algebraMap ℝ HBDepthFour.AF (6 : ℝ) = (6 : HBDepthFour.AF) by
      exact map_natCast (algebraMap ℝ HBDepthFour.AF) 6]
  ring

theorem muCut_divisorBounded (Z : ℕ) :
    DivisorBounded (HBDepthFour.muCut Z) 1 0 := by
  intro n
  simpa using HBDepthFour.abs_muCut_le_one Z n

theorem zeta_divisorBounded :
    DivisorBounded (ArithmeticFunction.zeta : HBDepthFour.AF) 1 0 := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [ArithmeticFunction.zeta_apply_ne hn]

/-- The log-free depth-four coefficient has a completely explicit fixed
divisor majorant. -/
theorem hb4Core_divisorBounded (Z : ℕ) :
    DivisorBounded (hb4Core Z) 15 6 := by
  let mu : HBDepthFour.AF := HBDepthFour.muCut Z
  let zeta : HBDepthFour.AF := ArithmeticFunction.zeta
  have hmu : DivisorBounded mu 1 0 := muCut_divisorBounded Z
  have hzeta : DivisorBounded zeta 1 0 := zeta_divisorBounded
  have hmu2 : DivisorBounded (mu ^ 2 : HBDepthFour.AF) 1 1 := by
    convert divisorBounded_mul (f := mu) (g := mu)
      (K := 1) (L := 1) (k := 0) (l := 0)
      (by norm_num) (by norm_num) hmu hmu using 1 <;> norm_num [pow_two]
  have hmu3 : DivisorBounded (mu ^ 3 : HBDepthFour.AF) 1 2 := by
    convert divisorBounded_mul (f := (mu ^ 2 : HBDepthFour.AF)) (g := mu)
      (K := 1) (L := 1) (k := 1) (l := 0)
      (by norm_num) (by norm_num) hmu2 hmu using 1 <;> norm_num [pow_succ]
  have hmu4 : DivisorBounded (mu ^ 4 : HBDepthFour.AF) 1 3 := by
    convert divisorBounded_mul (f := (mu ^ 3 : HBDepthFour.AF)) (g := mu)
      (K := 1) (L := 1) (k := 2) (l := 0)
      (by norm_num) (by norm_num) hmu3 hmu using 1 <;> norm_num [pow_succ]
  have hzeta2 : DivisorBounded (zeta ^ 2 : HBDepthFour.AF) 1 1 := by
    convert divisorBounded_mul (f := zeta) (g := zeta)
      (K := 1) (L := 1) (k := 0) (l := 0)
      (by norm_num) (by norm_num) hzeta hzeta using 1 <;> norm_num [pow_two]
  have hzeta3 : DivisorBounded (zeta ^ 3 : HBDepthFour.AF) 1 2 := by
    convert divisorBounded_mul (f := (zeta ^ 2 : HBDepthFour.AF)) (g := zeta)
      (K := 1) (L := 1) (k := 1) (l := 0)
      (by norm_num) (by norm_num) hzeta2 hzeta using 1 <;> norm_num [pow_succ]
  have hbase1 : DivisorBounded mu 1 6 :=
    divisorBounded_mono_exponent (by norm_num) hmu (by norm_num)
  have hbase2raw : DivisorBounded (mu ^ 2 * zeta : HBDepthFour.AF) 1 2 := by
    simpa using divisorBounded_mul (K := 1) (L := 1) (k := 1) (l := 0)
      (by norm_num) (by norm_num) hmu2 hzeta
  have hbase2 : DivisorBounded (mu ^ 2 * zeta : HBDepthFour.AF) 1 6 :=
    divisorBounded_mono_exponent (by norm_num) hbase2raw (by norm_num)
  have hbase3raw : DivisorBounded (mu ^ 3 * zeta ^ 2 : HBDepthFour.AF) 1 4 := by
    simpa using divisorBounded_mul (K := 1) (L := 1) (k := 2) (l := 1)
      (by norm_num) (by norm_num) hmu3 hzeta2
  have hbase3 : DivisorBounded (mu ^ 3 * zeta ^ 2 : HBDepthFour.AF) 1 6 :=
    divisorBounded_mono_exponent (by norm_num) hbase3raw (by norm_num)
  have hbase4 : DivisorBounded (mu ^ 4 * zeta ^ 3 : HBDepthFour.AF) 1 6 := by
    simpa using divisorBounded_mul (K := 1) (L := 1) (k := 3) (l := 2)
      (by norm_num) (by norm_num) hmu4 hzeta3
  have hterm1 : DivisorBounded ((4 : ℝ) • mu : HBDepthFour.AF) 4 6 := by
    simpa using divisorBounded_smul (4 : ℝ) hbase1
  have hterm2 :
      DivisorBounded ((6 : ℝ) • (mu ^ 2 * zeta) : HBDepthFour.AF) 6 6 := by
    simpa using divisorBounded_smul (6 : ℝ) hbase2
  have hterm3 :
      DivisorBounded ((4 : ℝ) • (mu ^ 3 * zeta ^ 2) : HBDepthFour.AF) 4 6 := by
    simpa using divisorBounded_smul (4 : ℝ) hbase3
  have h12 : DivisorBounded
      ((4 : ℝ) • mu - (6 : ℝ) • (mu ^ 2 * zeta) : HBDepthFour.AF) 10 6 := by
    have h := divisorBounded_sub hterm1 hterm2
    norm_num at h
    exact h
  have h123 : DivisorBounded
      ((4 : ℝ) • mu - (6 : ℝ) • (mu ^ 2 * zeta) +
        (4 : ℝ) • (mu ^ 3 * zeta ^ 2) : HBDepthFour.AF) 14 6 := by
    have h := divisorBounded_add h12 hterm3
    norm_num at h
    exact h
  change DivisorBounded
    ((4 : ℝ) • mu - (6 : ℝ) • (mu ^ 2 * zeta) +
      (4 : ℝ) • (mu ^ 3 * zeta ^ 2) - mu ^ 4 * zeta ^ 3 : HBDepthFour.AF) 15 6
  have h := divisorBounded_sub h123 hbase4
  norm_num at h
  exact h

/-- A singleton left sequence for the divisor-indexed convolution. -/
def leftSelector (a d : ℕ) : ℝ := if d = a then 1 else 0

/-- The matching right sequence.  It retains the original coefficient only
when `a` is the canonical divisor of the reconstructed integer. -/
def rightSelector (c : ℕ → ℝ) (R a s : ℕ) : ℝ :=
  if canonicalDivisor (a * s) R = a then c (a * s) else 0

theorem abs_rightSelector_le (c : ℕ → ℝ) (R a s : ℕ) :
    |rightSelector c R a s| ≤ |c (a * s)| := by
  simp only [rightSelector]
  split <;> simp

/-- Retaining a fixed divisor does not increase the divisor-bound order.
Only the named constant acquires the fixed factor `tau(a)^k`. -/
theorem rightSelector_divisorBounded {c : ℕ → ℝ} {K : ℝ} {k R a : ℕ}
    (hK : 0 ≤ K) (hc : DivisorBounded c K k) :
    DivisorBounded (rightSelector c R a)
      (K * ((ArithmeticFunction.sigma 0 a : ℕ) : ℝ) ^ k) k := by
  intro s
  have htauNat := sigma_zero_mul_le a s
  have htau :
      ((ArithmeticFunction.sigma 0 (a * s) : ℕ) : ℝ) ≤
        ((ArithmeticFunction.sigma 0 a : ℕ) : ℝ) *
          ((ArithmeticFunction.sigma 0 s : ℕ) : ℝ) := by
    exact_mod_cast htauNat
  calc
    |rightSelector c R a s| ≤ |c (a * s)| := abs_rightSelector_le c R a s
    _ ≤ K * ((ArithmeticFunction.sigma 0 (a * s) : ℕ) : ℝ) ^ k := hc (a * s)
    _ ≤ K *
        (((ArithmeticFunction.sigma 0 a : ℕ) : ℝ) *
          ((ArithmeticFunction.sigma 0 s : ℕ) : ℝ)) ^ k := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) htau k) hK
    _ = (K * ((ArithmeticFunction.sigma 0 a : ℕ) : ℝ) ^ k) *
        ((ArithmeticFunction.sigma 0 s : ℕ) : ℝ) ^ k := by ring

/-- The exact divisor weight moved from the running coefficient to the
singleton retained factor. -/
def divisorScale (a k : ℕ) : ℝ :=
  ((ArithmeticFunction.sigma 0 a : ℕ) : ℝ) ^ k

theorem divisorScale_pos {a k : ℕ} (ha : a ≠ 0) : 0 < divisorScale a k := by
  have htau : 0 < ((ArithmeticFunction.sigma 0 a : ℕ) : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 a ha
  exact pow_pos htau k

def weightedLeftSelector (a k d : ℕ) : ℝ :=
  divisorScale a k * leftSelector a d

def normalizedRightSelector (c : ℕ → ℝ) (R a k s : ℕ) : ℝ :=
  rightSelector c R a s / divisorScale a k

theorem weightedLeft_mul_normalizedRight (c : ℕ → ℝ) (R k d s : ℕ)
    {a : ℕ} (ha : a ≠ 0) :
    weightedLeftSelector a k d * normalizedRightSelector c R a k s =
      leftSelector a d * rightSelector c R a s := by
  have hscale : divisorScale a k ≠ 0 := (divisorScale_pos ha).ne'
  unfold weightedLeftSelector normalizedRightSelector
  field_simp [hscale]

/-- After normalization the running factor has the original uniform
divisor-bound constant `K`; all dependence on `a` is on the singleton side. -/
theorem normalizedRightSelector_divisorBounded
    {c : ℕ → ℝ} {K : ℝ} {k R a : ℕ}
    (ha : a ≠ 0) (hK : 0 ≤ K) (hc : DivisorBounded c K k) :
    DivisorBounded (normalizedRightSelector c R a k) K k := by
  intro s
  have hscale : 0 < divisorScale a k := divisorScale_pos ha
  have hbound := rightSelector_divisorBounded (R := R) (a := a) hK hc s
  rw [normalizedRightSelector, abs_div, abs_of_pos hscale, div_le_iff₀ hscale]
  simpa only [divisorScale] using
    (hbound.trans_eq (by ring))

theorem abs_weightedLeftSelector_le (a k d : ℕ) :
    |weightedLeftSelector a k d| ≤ divisorScale a k := by
  have hscale : 0 ≤ divisorScale a k := by
    exact pow_nonneg (by positivity) k
  by_cases hda : d = a
  · simp [weightedLeftSelector, leftSelector, hda, abs_of_nonneg hscale]
  · simp [weightedLeftSelector, leftSelector, hda, hscale]

theorem weightedLeftSelector_support {a k d : ℕ}
    (hcoeff : weightedLeftSelector a k d ≠ 0) : d = a := by
  by_contra hda
  exact hcoeff (by simp [weightedLeftSelector, leftSelector, hda])

theorem normalizedRightSelector_support {c : ℕ → ℝ} {R a k s : ℕ}
    (hcoeff : normalizedRightSelector c R a k s ≠ 0) :
    canonicalDivisor (a * s) R = a := by
  by_contra hcanon
  exact hcoeff (by simp [normalizedRightSelector, rightSelector, hcanon])

theorem canonicalCofactor_eq_of_normalizedRightSelector_ne_zero
    {c : ℕ → ℝ} {R a k s : ℕ} (hR : 0 < R)
    (hcoeff : normalizedRightSelector c R a k s ≠ 0) :
    canonicalCofactor (a * s) R = s := by
  have hcanon := normalizedRightSelector_support hcoeff
  have ha : 0 < a := by
    rw [← hcanon]
    exact canonicalDivisor_pos (n := a * s) hR
  unfold canonicalCofactor
  rw [hcanon]
  simpa [Nat.mul_comm] using Nat.mul_div_left s ha

/-- On a nonregular fiber, the running sequence is supported only on
`B`-rough integers. -/
theorem normalizedRightSelector_rough_support
    {c : ℕ → ℝ} {R B a k s : ℕ} (hR : 0 < R)
    (hrough : ¬R < a * B)
    (hcoeff : normalizedRightSelector c R a k s ≠ 0) :
    ∀ q : ℕ, q.Prime → q ∣ s → B < q := by
  have hcanon := normalizedRightSelector_support hcoeff
  have hcofactor := canonicalCofactor_eq_of_normalizedRightSelector_ne_zero hR hcoeff
  obtain hregular | hroughCofactor :=
    canonical_regular_or_rough (n := a * s) (B := B) hR
  · rw [hcanon] at hregular
    exact (hrough hregular).elim
  · intro q hqprime hqs
    apply hroughCofactor q hqprime
    rwa [hcofactor]

theorem normalizedRightSelector_prime_support
    {c : ℕ → ℝ} {R B a k s : ℕ} (hR : 0 < R)
    (hrough : ¬R < a * B)
    (hs : 1 < s) (hsize : s < (B + 1) ^ 2)
    (hcoeff : normalizedRightSelector c R a k s ≠ 0) : s.Prime := by
  exact prime_of_rough_of_lt_sq hs
    (normalizedRightSelector_rough_support hR hrough hcoeff) hsize

theorem normalizedRightSelector_prime_or_semiprime_support
    {c : ℕ → ℝ} {R B a k s : ℕ} (hR : 0 < R)
    (hrough : ¬R < a * B)
    (hs : 1 < s) (hsize : s < (B + 1) ^ 3)
    (hcoeff : normalizedRightSelector c R a k s ≠ 0) :
    s.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ s = p * q := by
  exact prime_or_product_of_two_primes_of_rough_of_lt_cube hs
    (normalizedRightSelector_rough_support hR hrough hcoeff) hsize

theorem normalizedRightSelector_bounded_prime_depth
    {c : ℕ → ℝ} {R B a k s r : ℕ} (hR : 0 < R)
    (hrough : ¬R < a * B)
    (hs : s ≠ 0) (hsize : s < (B + 1) ^ r)
    (hcoeff : normalizedRightSelector c R a k s ≠ 0) :
    s.primeFactorsList.length < r := by
  exact cardFactors_lt_of_rough_of_lt_pow hs
    (normalizedRightSelector_rough_support hR hrough hcoeff) hsize

/-- The existing Shiu progression theorem applies to every normalized
running fiber with the same input constant and divisor exponent. -/
theorem shiu_normalizedRightSelector {eta : ℝ}
    (hshiu : ShiuMajorant eta) {c : ℕ → ℝ} {K : ℝ} {k R a : ℕ}
    (ha : a ≠ 0) (hK : 0 ≤ K) (hc : DivisorBounded c K k) :
    ∃ C K' T₁ : ℝ, ∀ T ≥ T₁, ∀ P : ℝ, 1 ≤ P →
      ∀ q r : ℕ, 0 < q → Nat.Coprime r q →
        (q : ℝ) ≤ P * T ^ (-eta) →
          progressionSum (normalizedRightSelector c R a k) P q r ≤
            K' * (P / (Nat.totient q : ℝ)) * (Real.log T) ^ C := by
  exact hshiu (normalizedRightSelector c R a k) K k
    (normalizedRightSelector_divisorBounded ha hK hc)

theorem hb4Core_normalizedRightSelector_divisorBounded
    (Z : ℕ) {R a : ℕ} (ha : a ≠ 0) :
    DivisorBounded (normalizedRightSelector (hb4Core Z) R a 6) 15 6 := by
  exact normalizedRightSelector_divisorBounded ha (by norm_num)
    (hb4Core_divisorBounded Z)

/-- Shiu applies to the actual normalized depth-four core with no generic
coefficient-admissibility premise left. -/
theorem shiu_hb4Core_normalizedRightSelector {eta : ℝ}
    (hshiu : ShiuMajorant eta) (Z : ℕ) {R a : ℕ} (ha : a ≠ 0) :
    ∃ C K' T₁ : ℝ, ∀ T ≥ T₁, ∀ P : ℝ, 1 ≤ P →
      ∀ q r : ℕ, 0 < q → Nat.Coprime r q →
        (q : ℝ) ≤ P * T ^ (-eta) →
          progressionSum (normalizedRightSelector (hb4Core Z) R a 6) P q r ≤
            K' * (P / (Nat.totient q : ℝ)) * (Real.log T) ^ C := by
  exact hshiu (normalizedRightSelector (hb4Core Z) R a 6) 15 6
    (hb4Core_normalizedRightSelector_divisorBounded Z ha)

/-- One literal Dirichlet-convolution piece. -/
def convolutionPiece (c : ℕ → ℝ) (R a n : ℕ) : ℝ :=
  ∑ ds ∈ n.divisorsAntidiagonal,
    leftSelector a ds.1 * rightSelector c R a ds.2

/-- The uniformly normalized literal convolution. -/
def normalizedConvolutionPiece (c : ℕ → ℝ) (R a k n : ℕ) : ℝ :=
  ∑ ds ∈ n.divisorsAntidiagonal,
    weightedLeftSelector a k ds.1 * normalizedRightSelector c R a k ds.2

theorem normalizedConvolutionPiece_eq (c : ℕ → ℝ) (R k n : ℕ)
    {a : ℕ} (ha : a ≠ 0) :
    normalizedConvolutionPiece c R a k n = convolutionPiece c R a n := by
  apply Finset.sum_congr rfl
  intro ds hds
  exact weightedLeft_mul_normalizedRight c R k ds.1 ds.2 ha

/-- Package a normalized fiber as an arithmetic function so the remaining
literal smooth factors can be convolved after the refinement. -/
def normalizedConvolutionAF (c : HBDepthFour.AF) (R a k : ℕ) : HBDepthFour.AF :=
  ⟨fun n => normalizedConvolutionPiece c R a k n, by
    simp [normalizedConvolutionPiece]⟩

@[simp]
theorem normalizedConvolutionAF_apply (c : HBDepthFour.AF) (R a k n : ℕ) :
    normalizedConvolutionAF c R a k n = normalizedConvolutionPiece c R a k n := rfl

theorem arithmeticFunction_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → HBDepthFour.AF) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- The coefficient assigned directly to one canonical-divisor fiber. -/
def canonicalPiece (c : ℕ → ℝ) (R a n : ℕ) : ℝ :=
  if canonicalDivisor n R = a then c n else 0

/-- Each canonical fiber is exactly a Dirichlet convolution; this is not a
support-only or summed identity. -/
theorem convolutionPiece_eq_canonicalPiece (c : ℕ → ℝ) {R a n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) :
    convolutionPiece c R a n = canonicalPiece c R a n := by
  rw [convolutionPiece,
    Nat.sum_divisorsAntidiagonal
      (fun d s => leftSelector a d * rightSelector c R a s)]
  by_cases hcanon : canonicalDivisor n R = a
  · have ha_dvd : a ∣ n := by
      rw [← hcanon]
      exact canonicalDivisor_dvd hR
    have ha_mem : a ∈ n.divisors := Nat.mem_divisors.mpr ⟨ha_dvd, hn⟩
    rw [canonicalPiece, if_pos hcanon]
    calc
      ∑ d ∈ n.divisors, leftSelector a d * rightSelector c R a (n / d) =
          leftSelector a a * rightSelector c R a (n / a) := by
        exact Finset.sum_eq_single_of_mem a ha_mem
          (by
            intro b hb hba
            simp [leftSelector, hba])
      _ = c n := by
        simp [leftSelector, rightSelector, Nat.mul_div_cancel' ha_dvd, hcanon]
  · rw [canonicalPiece, if_neg hcanon]
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hda : d = a
    · subst d
      have ha_dvd : a ∣ n := Nat.dvd_of_mem_divisors hd
      simp [leftSelector, rightSelector, Nat.mul_div_cancel' ha_dvd, hcanon]
    · simp [leftSelector, hda]

theorem normalizedConvolutionPiece_eq_canonicalPiece (c : ℕ → ℝ)
    {R a k n : ℕ} (ha : a ≠ 0) (hn : n ≠ 0) (hR : 0 < R) :
    normalizedConvolutionPiece c R a k n = canonicalPiece c R a n := by
  rw [normalizedConvolutionPiece_eq c R k n ha,
    convolutionPiece_eq_canonicalPiece c hn hR]

/-- A regular normalized fiber is a literal convolution with all algebraic
data needed at the analytic boundary: terminal-band singleton support,
uniform divisor bound on the running factor, and exact source coefficient. -/
theorem regular_normalized_fiber_data
    {c : ℕ → ℝ} {K : ℝ} {k R B a n : ℕ}
    (ha : a ∈ (Finset.Icc 1 R).filter (fun d => R < d * B))
    (hK : 0 ≤ K) (hc : DivisorBounded c K k)
    (hn : n ≠ 0) (hR : 0 < R) :
    1 ≤ a ∧ a ≤ R ∧ R < a * B ∧
      (∀ d : ℕ, weightedLeftSelector a k d ≠ 0 → d = a) ∧
      DivisorBounded (normalizedRightSelector c R a k) K k ∧
      normalizedConvolutionPiece c R a k n = canonicalPiece c R a n := by
  have haData := Finset.mem_filter.mp ha
  have haIcc := Finset.mem_Icc.mp haData.1
  have ha0 : a ≠ 0 := Nat.ne_of_gt haIcc.1
  exact ⟨haIcc.1, haIcc.2, haData.2,
    fun d hd => weightedLeftSelector_support hd,
    normalizedRightSelector_divisorBounded ha0 hK hc,
    normalizedConvolutionPiece_eq_canonicalPiece c ha0 hn hR⟩

/-- The canonical divisor lies in the finite index set used by the
superposition. -/
theorem canonicalDivisor_mem_Icc {n R : ℕ} (hR : 0 < R) :
    canonicalDivisor n R ∈ Finset.Icc 1 R := by
  exact Finset.mem_Icc.mpr
    ⟨canonicalDivisor_pos (n := n) hR, canonicalDivisor_le n R⟩

/-- Pointwise exact coefficient refinement.  The finite family of literal
convolutions reconstructs any coefficient without a majorant or an omitted
exceptional integer. -/
theorem sum_convolutionPiece (c : ℕ → ℝ) {R n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) :
    ∑ a ∈ Finset.Icc 1 R, convolutionPiece c R a n = c n := by
  simp_rw [convolutionPiece_eq_canonicalPiece c hn hR]
  calc
    ∑ a ∈ Finset.Icc 1 R, canonicalPiece c R a n =
        canonicalPiece c R (canonicalDivisor n R) n := by
      exact Finset.sum_eq_single_of_mem _ (canonicalDivisor_mem_Icc hR)
        (by
          intro a ha hne
          simp [canonicalPiece, Ne.symm hne])
    _ = c n := by simp [canonicalPiece]

theorem sum_normalizedConvolutionPiece (c : ℕ → ℝ) (k : ℕ) {R n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) :
    ∑ a ∈ Finset.Icc 1 R, normalizedConvolutionPiece c R a k n = c n := by
  calc
    ∑ a ∈ Finset.Icc 1 R, normalizedConvolutionPiece c R a k n =
        ∑ a ∈ Finset.Icc 1 R, convolutionPiece c R a n := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [normalizedConvolutionPiece_eq c R k n]
      exact Nat.ne_of_gt (Finset.mem_Icc.mp ha).1
    _ = c n := sum_convolutionPiece c hn hR

theorem sum_normalizedConvolutionAF (c : HBDepthFour.AF) (k : ℕ) {R : ℕ}
    (hR : 0 < R) :
    ∑ a ∈ Finset.Icc 1 R, normalizedConvolutionAF c R a k = c := by
  ext n
  rw [arithmeticFunction_sum_apply]
  by_cases hn : n = 0
  · subst n
    simp
  · simpa using sum_normalizedConvolutionPiece c k hn hR

/-- The canonical fibers do not multiply any pointwise cost which vanishes at
zero.  In particular, the number of divisor fibers creates no pointwise
`L1` or `L2` loss. -/
theorem sum_map_convolutionPiece (c : ℕ → ℝ) (Phi : ℝ → ℝ)
    (hPhi : Phi 0 = 0) {R n : ℕ} (hn : n ≠ 0) (hR : 0 < R) :
    ∑ a ∈ Finset.Icc 1 R, Phi (convolutionPiece c R a n) = Phi (c n) := by
  simp_rw [convolutionPiece_eq_canonicalPiece c hn hR]
  calc
    ∑ a ∈ Finset.Icc 1 R, Phi (canonicalPiece c R a n) =
        Phi (canonicalPiece c R (canonicalDivisor n R) n) := by
      exact Finset.sum_eq_single_of_mem _ (canonicalDivisor_mem_Icc hR)
        (by
          intro a ha hne
          simp [canonicalPiece, Ne.symm hne, hPhi])
    _ = Phi (c n) := by simp [canonicalPiece]

theorem sum_map_normalizedConvolutionPiece (c : ℕ → ℝ) (k : ℕ)
    (Phi : ℝ → ℝ) (hPhi : Phi 0 = 0) {R n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) :
    ∑ a ∈ Finset.Icc 1 R, Phi (normalizedConvolutionPiece c R a k n) = Phi (c n) := by
  calc
    ∑ a ∈ Finset.Icc 1 R, Phi (normalizedConvolutionPiece c R a k n) =
        ∑ a ∈ Finset.Icc 1 R, Phi (convolutionPiece c R a n) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [normalizedConvolutionPiece_eq c R k n]
      exact Nat.ne_of_gt (Finset.mem_Icc.mp ha).1
    _ = Phi (c n) := sum_map_convolutionPiece c Phi hPhi hn hR

/-! ## Exact recombination over arbitrary outer scales -/

/-- The contribution assigned to one user-chosen outer scale.  The map
`block` may encode dyadic scales or any other finite scale partition. -/
def blockRefinement {ι : Type*} [DecidableEq ι]
    (c : ℕ → ℝ) (R k : ℕ) (block : ℕ → ι) (i : ι) (n : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Icc 1 R).filter (fun a => block a = i),
    normalizedConvolutionPiece c R a k n

theorem blockRefinement_eq {ι : Type*} [DecidableEq ι]
    (c : ℕ → ℝ) (k : ℕ) (block : ℕ → ι) (i : ι)
    {R n : ℕ} (hn : n ≠ 0) (hR : 0 < R) :
    blockRefinement c R k block i n =
      if block (canonicalDivisor n R) = i then c n else 0 := by
  let d := canonicalDivisor n R
  have hdmem : d ∈ Finset.Icc 1 R := canonicalDivisor_mem_Icc hR
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hdmem).1
  by_cases hi : block d = i
  · rw [if_pos hi]
    unfold blockRefinement
    have hdfilter : d ∈ (Finset.Icc 1 R).filter (fun a => block a = i) :=
      Finset.mem_filter.mpr ⟨hdmem, hi⟩
    calc
      ∑ a ∈ (Finset.Icc 1 R).filter (fun a => block a = i),
          normalizedConvolutionPiece c R a k n =
          normalizedConvolutionPiece c R d k n := by
        exact Finset.sum_eq_single_of_mem d hdfilter
          (by
            intro a ha hne
            have haIcc := (Finset.mem_filter.mp ha).1
            have ha0 : a ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp haIcc).1
            rw [normalizedConvolutionPiece_eq_canonicalPiece c ha0 hn hR]
            simp [canonicalPiece, d, Ne.symm hne])
      _ = canonicalPiece c R d n :=
        normalizedConvolutionPiece_eq_canonicalPiece c hd0 hn hR
      _ = c n := by simp [canonicalPiece, d]
  · rw [if_neg hi]
    unfold blockRefinement
    apply Finset.sum_eq_zero
    intro a ha
    have haData := Finset.mem_filter.mp ha
    have ha0 : a ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp haData.1).1
    have hne : d ≠ a := by
      intro hda
      subst a
      exact hi haData.2
    rw [normalizedConvolutionPiece_eq_canonicalPiece c ha0 hn hR]
    simp [canonicalPiece, d, hne]

/-- Any finite outer-scale partition recombines exactly before absolute
values.  Only the block containing the canonical divisor contributes. -/
theorem sum_blockRefinement {ι : Type*} [DecidableEq ι]
    (c : ℕ → ℝ) (k : ℕ) (block : ℕ → ι) (I : Finset ι)
    {R n : ℕ} (hn : n ≠ 0) (hR : 0 < R)
    (hcover : block (canonicalDivisor n R) ∈ I) :
    ∑ i ∈ I, blockRefinement c R k block i n = c n := by
  simp_rw [blockRefinement_eq c k block _ hn hR]
  calc
    ∑ i ∈ I, (if block (canonicalDivisor n R) = i then c n else 0) =
        (if block (canonicalDivisor n R) = block (canonicalDivisor n R) then c n else 0) := by
      exact Finset.sum_eq_single_of_mem _ hcover
        (by
          intro i hi hne
          simp [Ne.symm hne])
    _ = c n := by simp

theorem sum_map_blockRefinement {ι : Type*} [DecidableEq ι]
    (c : ℕ → ℝ) (k : ℕ) (block : ℕ → ι) (I : Finset ι)
    (Phi : ℝ → ℝ) (hPhi : Phi 0 = 0)
    {R n : ℕ} (hn : n ≠ 0) (hR : 0 < R)
    (hcover : block (canonicalDivisor n R) ∈ I) :
    ∑ i ∈ I, Phi (blockRefinement c R k block i n) = Phi (c n) := by
  simp_rw [blockRefinement_eq c k block _ hn hR]
  calc
    ∑ i ∈ I, Phi (if block (canonicalDivisor n R) = i then c n else 0) =
        Phi (if block (canonicalDivisor n R) = block (canonicalDivisor n R) then c n else 0) := by
      exact Finset.sum_eq_single_of_mem _ hcover
        (by
          intro i hi hne
          simp [Ne.symm hne, hPhi])
    _ = Phi (c n) := by simp

theorem sum_abs_convolutionPiece (c : ℕ → ℝ) {R n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) :
    ∑ a ∈ Finset.Icc 1 R, |convolutionPiece c R a n| = |c n| := by
  exact sum_map_convolutionPiece c abs (abs_zero) hn hR

theorem sum_sq_convolutionPiece (c : ℕ → ℝ) {R n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) :
    ∑ a ∈ Finset.Icc 1 R, (convolutionPiece c R a n) ^ 2 = (c n) ^ 2 := by
  exact sum_map_convolutionPiece c (fun x => x ^ 2) (zero_pow (by norm_num)) hn hR

/-- The refinement applied to the actual depth-four Heath--Brown coefficient,
removing the source-identification gap left by the support obstruction. -/
theorem hb4_sum_convolutionPiece (Z : ℕ) {R n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) :
    ∑ a ∈ Finset.Icc 1 R,
      convolutionPiece (fun m => HBDepthFour.hb4 Z m) R a n =
        HBDepthFour.hb4 Z n := by
  exact sum_convolutionPiece (fun m => HBDepthFour.hb4 Z m) hn hR

/-- Exact `(EF_eta)`-side identity with the logarithm preserved on its
literal convolution slot.  Refinement happens on the divisor-bounded core;
only afterwards is each fiber convolved with `log`. -/
theorem hb4_eq_sum_normalizedCore_mul_log (Z : ℕ) {R : ℕ} (hR : 0 < R) :
    HBDepthFour.hb4 Z =
      ∑ a ∈ Finset.Icc 1 R,
        normalizedConvolutionAF (hb4Core Z) R a 6 * ArithmeticFunction.log := by
  calc
    HBDepthFour.hb4 Z = hb4Core Z * ArithmeticFunction.log :=
      hb4_eq_core_mul_log Z
    _ = (∑ a ∈ Finset.Icc 1 R,
          normalizedConvolutionAF (hb4Core Z) R a 6) *
          ArithmeticFunction.log := by
      rw [sum_normalizedConvolutionAF (hb4Core Z) 6 hR]
    _ = ∑ a ∈ Finset.Icc 1 R,
          normalizedConvolutionAF (hb4Core Z) R a 6 *
            ArithmeticFunction.log := by
      rw [Finset.sum_mul]

theorem hb4_apply_eq_sum_normalizedCore_mul_log
    (Z : ℕ) {R n : ℕ} (hR : 0 < R) :
    HBDepthFour.hb4 Z n =
      ∑ a ∈ Finset.Icc 1 R,
        (normalizedConvolutionAF (hb4Core Z) R a 6 * ArithmeticFunction.log) n := by
  rw [← arithmeticFunction_sum_apply]
  exact DFunLike.congr_fun (hb4_eq_sum_normalizedCore_mul_log Z hR) n

/-- The terminal fibers whose retained divisor reaches the requested scale
within the multiplicative tolerance `B`, summed before restoring `log`. -/
def regularCoreAF (Z R B : ℕ) : HBDepthFour.AF :=
  ∑ a ∈ (Finset.Icc 1 R).filter (fun a => R < a * B),
    normalizedConvolutionAF (hb4Core Z) R a 6

/-- The complementary log-free source.  Every individual running fiber in
this sum is supported on `B`-rough integers. -/
def roughCoreAF (Z R B : ℕ) : HBDepthFour.AF :=
  ∑ a ∈ (Finset.Icc 1 R).filter (fun a => ¬R < a * B),
    normalizedConvolutionAF (hb4Core Z) R a 6

/-- Every summand of the regular source has the retained singleton in the
terminal band and the same explicit divisor majorant on its running side. -/
theorem regularCoreAF_fiber_data (Z : ℕ) {R B a : ℕ}
    (ha : a ∈ (Finset.Icc 1 R).filter (fun d => R < d * B)) :
    1 ≤ a ∧ a ≤ R ∧ R < a * B ∧
      (∀ d : ℕ, weightedLeftSelector a 6 d ≠ 0 → d = a) ∧
      DivisorBounded (normalizedRightSelector (hb4Core Z) R a 6) 15 6 := by
  have haData := Finset.mem_filter.mp ha
  have haIcc := Finset.mem_Icc.mp haData.1
  have ha0 : a ≠ 0 := Nat.ne_of_gt haIcc.1
  exact ⟨haIcc.1, haIcc.2, haData.2,
    fun d hd => weightedLeftSelector_support hd,
    hb4Core_normalizedRightSelector_divisorBounded Z ha0⟩

/-- Every summand of the exceptional source has the same explicit divisor
majorant, while every nonzero running coefficient is supported on a
`B`-rough integer. -/
theorem roughCoreAF_fiber_data (Z : ℕ) {R B a : ℕ} (hR : 0 < R)
    (ha : a ∈ (Finset.Icc 1 R).filter (fun d => ¬R < d * B)) :
    1 ≤ a ∧ a ≤ R ∧ ¬R < a * B ∧
      DivisorBounded (normalizedRightSelector (hb4Core Z) R a 6) 15 6 ∧
      ∀ s : ℕ, normalizedRightSelector (hb4Core Z) R a 6 s ≠ 0 →
        ∀ q : ℕ, q.Prime → q ∣ s → B < q := by
  have haData := Finset.mem_filter.mp ha
  have haIcc := Finset.mem_Icc.mp haData.1
  have ha0 : a ≠ 0 := Nat.ne_of_gt haIcc.1
  exact ⟨haIcc.1, haIcc.2, haData.2,
    hb4Core_normalizedRightSelector_divisorBounded Z ha0,
    fun s hs => normalizedRightSelector_rough_support hR haData.2 hs⟩

/-- Below the `r`th roughness power, every nonzero running coefficient in an
exceptional depth-four fiber has fewer than `r` prime factors, with
multiplicity. -/
theorem roughCoreAF_fiber_bounded_prime_depth (Z : ℕ) {R B a s r : ℕ}
    (hR : 0 < R)
    (ha : a ∈ (Finset.Icc 1 R).filter (fun d => ¬R < d * B))
    (hs : s ≠ 0) (hsize : s < (B + 1) ^ r)
    (hcoeff : normalizedRightSelector (hb4Core Z) R a 6 s ≠ 0) :
    s.primeFactorsList.length < r := by
  exact normalizedRightSelector_bounded_prime_depth hR
    (Finset.mem_filter.mp ha).2 hs hsize hcoeff

/-- The exceptional running coefficient is uniformly bounded once its size
forces bounded prime depth.  The bound is independent of the retained
divisor and of the running integer. -/
theorem abs_roughCoreAF_fiber_le (Z : ℕ) {R B a s r : ℕ}
    (hR : 0 < R)
    (ha : a ∈ (Finset.Icc 1 R).filter (fun d => ¬R < d * B))
    (hs : s ≠ 0) (hsize : s < (B + 1) ^ r) :
    |normalizedRightSelector (hb4Core Z) R a 6 s| ≤
      15 * (((2 : ℕ) ^ r : ℕ) : ℝ) ^ 6 := by
  by_cases hcoeff : normalizedRightSelector (hb4Core Z) R a 6 s = 0
  · simp [hcoeff]
  apply abs_le_of_divisorBounded_of_prime_depth (by norm_num)
    (hb4Core_normalizedRightSelector_divisorBounded Z
      (Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1)) hs
  exact roughCoreAF_fiber_bounded_prime_depth Z hR ha hs hsize
    hcoeff

/-- An elementary progression-cardinality bound.  Once coefficients are
uniformly bounded, no Shiu estimate is needed: a residue class contains at
most five times the expected `P / phi(q)` number of integers in `[1,2P]`. -/
theorem progression_filter_card_le_five {P : ℝ} {q r : ℕ}
    (hP : 1 ≤ P) (hq : 0 < q) (hqP : (q : ℝ) ≤ P) :
    (((Finset.Icc 1 ⌈2 * P⌉₊).filter
      (fun p => p % q = r % q)).card : ℝ) ≤
        5 * (P / (Nat.totient q : ℝ)) := by
  let N : ℕ := ⌈2 * P⌉₊
  let S : Finset ℕ :=
    (Finset.Icc 1 N).filter (fun p => p % q = r % q)
  have hsubset : S ⊆
      (Finset.range (N + 1)).filter (fun p => p ≡ r [MOD q]) := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpIcc := Finset.mem_Icc.mp hpData.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), hpData.2⟩
  have hcard : S.card ≤ (N + 1) / q + 1 := by
    calc
      S.card ≤ ((Finset.range (N + 1)).filter
          (fun p => p ≡ r [MOD q])).card := Finset.card_le_card hsubset
      _ = (N + 1).count (fun p => p ≡ r [MOD q]) := by
        rw [Nat.count_eq_card_filter_range]
      _ ≤ (N + 1) / q + 1 := by
        rw [Nat.count_modEq_card (N + 1) hq r]
        split <;> omega
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hphiReal : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hphiLe : (Nat.totient q : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.totient_le q
  have hNreal : (N : ℝ) ≤ 2 * P + 1 := by
    dsimp [N]
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * P)).le
  have hNplus : ((N + 1 : ℕ) : ℝ) ≤ 2 * P + 2 := by
    norm_num
    linarith
  have hnum : 2 * P + 2 + (q : ℝ) ≤ 5 * P := by
    nlinarith
  have hPnonneg : 0 ≤ P := by linarith
  change (S.card : ℝ) ≤ 5 * (P / (Nat.totient q : ℝ))
  calc
    (S.card : ℝ) ≤ (((N + 1) / q + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ = (((N + 1) / q : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ ((N + 1 : ℕ) : ℝ) / (q : ℝ) + 1 := by
      exact add_le_add Nat.cast_div_le le_rfl
    _ ≤ (2 * P + 2) / (q : ℝ) + 1 := by
      exact add_le_add ((div_le_div_iff_of_pos_right hqReal).2 hNplus) le_rfl
    _ = (2 * P + 2 + (q : ℝ)) / (q : ℝ) := by
      field_simp
    _ ≤ (5 * P) / (q : ℝ) :=
      (div_le_div_iff_of_pos_right hqReal).2 hnum
    _ = 5 * (P / (q : ℝ)) := by ring
    _ ≤ 5 * (P / (Nat.totient q : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hPnonneg hphiReal hphiLe) (by norm_num)

/-- Summing a uniformly bounded coefficient over a progression costs only
the progression cardinality. -/
theorem progressionSum_le_of_uniform_bound {c : ℕ → ℝ} {P M : ℝ}
    {q r : ℕ}
    (hbound : ∀ p ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter
      (fun p => p % q = r % q), |c p| ≤ M) :
    progressionSum c P q r ≤
      (((Finset.Icc 1 ⌈2 * P⌉₊).filter
        (fun p => p % q = r % q)).card : ℝ) * M := by
  unfold progressionSum
  calc
    ∑ p ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter
        (fun p => p % q = r % q), |c p| ≤
      ∑ p ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter
        (fun p => p % q = r % q), M := by
          exact Finset.sum_le_sum fun p hp => hbound p hp
    _ = (((Finset.Icc 1 ⌈2 * P⌉₊).filter
        (fun p => p % q = r % q)).card : ℝ) * M := by simp

/-- Direct progression majorant for every bounded-depth exceptional fiber.
This is the rough-family replacement for the blanket Shiu premise. -/
theorem progressionSum_roughCoreAF_fiber_le (Z : ℕ) {R B a r q v : ℕ}
    {P : ℝ} (hR : 0 < R)
    (ha : a ∈ (Finset.Icc 1 R).filter (fun d => ¬R < d * B))
    (hP : 1 ≤ P) (hq : 0 < q) (hqP : (q : ℝ) ≤ P)
    (hsize : ⌈2 * P⌉₊ < (B + 1) ^ r) :
    progressionSum (normalizedRightSelector (hb4Core Z) R a 6) P q v ≤
      (5 * (15 * (((2 : ℕ) ^ r : ℕ) : ℝ) ^ 6)) *
        (P / (Nat.totient q : ℝ)) := by
  let M : ℝ := 15 * (((2 : ℕ) ^ r : ℕ) : ℝ) ^ 6
  have hM : 0 ≤ M := by positivity
  have hsum :
      progressionSum (normalizedRightSelector (hb4Core Z) R a 6) P q v ≤
        (((Finset.Icc 1 ⌈2 * P⌉₊).filter
          (fun p => p % q = v % q)).card : ℝ) * M := by
    apply progressionSum_le_of_uniform_bound
    intro p hp
    have hpIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    exact abs_roughCoreAF_fiber_le Z hR ha (Nat.ne_of_gt hpIcc.1)
      (hpIcc.2.trans_lt hsize)
  calc
    progressionSum (normalizedRightSelector (hb4Core Z) R a 6) P q v ≤
        (((Finset.Icc 1 ⌈2 * P⌉₊).filter
          (fun p => p % q = v % q)).card : ℝ) * M := hsum
    _ ≤ (5 * (P / (Nat.totient q : ℝ))) * M := by
      exact mul_le_mul_of_nonneg_right
        (progression_filter_card_le_five hP hq hqP) hM
    _ = (5 * (15 * (((2 : ℕ) ^ r : ℕ) : ℝ) ^ 6)) *
        (P / (Nat.totient q : ℝ)) := by
      unfold M
      ring

/-- Shiu-shaped zero-logarithm estimate for the bounded-depth exceptional
family.  The usual modulus range is used only to deduce `q ≤ P`; coprimality
is harmless and no generic majorant hypothesis remains. -/
theorem roughCoreAF_fiber_zero_log_majorant {eta : ℝ} (heta : 0 ≤ eta)
    (Z : ℕ) {R B a r : ℕ} (hR : 0 < R)
    (ha : a ∈ (Finset.Icc 1 R).filter (fun d => ¬R < d * B)) :
    ∃ K T₁ : ℝ, ∀ T ≥ T₁, ∀ P : ℝ, 1 ≤ P →
      ⌈2 * P⌉₊ < (B + 1) ^ r →
      ∀ q v : ℕ, 0 < q → Nat.Coprime v q →
        (q : ℝ) ≤ P * T ^ (-eta) →
        progressionSum (normalizedRightSelector (hb4Core Z) R a 6) P q v ≤
          K * (P / (Nat.totient q : ℝ)) * (Real.log T) ^ (0 : ℝ) := by
  refine ⟨5 * (15 * (((2 : ℕ) ^ r : ℕ) : ℝ) ^ 6), 1, ?_⟩
  intro T hT P hP hsize q v hq hcoprime hqRange
  have hpow : T ^ (-eta) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hT (neg_nonpos.mpr heta)
  have hPnonneg : 0 ≤ P := by linarith
  have hqP : (q : ℝ) ≤ P := by
    exact hqRange.trans
      (calc
        P * T ^ (-eta) ≤ P * 1 := mul_le_mul_of_nonneg_left hpow hPnonneg
        _ = P := mul_one P)
  simpa using progressionSum_roughCoreAF_fiber_le Z hR ha hP hq hqP hsize

/-- Exact regular/rough partition at the arithmetic-function level, before
absolute values and before the final logarithm convolution. -/
theorem regularCoreAF_add_roughCoreAF (Z B : ℕ) {R : ℕ} (hR : 0 < R) :
    regularCoreAF Z R B + roughCoreAF Z R B = hb4Core Z := by
  unfold regularCoreAF roughCoreAF
  rw [Finset.sum_filter_add_sum_filter_not]
  exact sum_normalizedConvolutionAF (hb4Core Z) 6 hR

/-- Exact source split for the literal Heath--Brown coefficient.  Both
families are formed first; only then is `log` convolved onto them. -/
theorem hb4_eq_regularCore_mul_log_add_roughCore_mul_log
    (Z B : ℕ) {R : ℕ} (hR : 0 < R) :
    HBDepthFour.hb4 Z =
      regularCoreAF Z R B * ArithmeticFunction.log +
        roughCoreAF Z R B * ArithmeticFunction.log := by
  calc
    HBDepthFour.hb4 Z = hb4Core Z * ArithmeticFunction.log :=
      hb4_eq_core_mul_log Z
    _ = (regularCoreAF Z R B + roughCoreAF Z R B) *
          ArithmeticFunction.log := by
      rw [regularCoreAF_add_roughCoreAF Z B hR]
    _ = regularCoreAF Z R B * ArithmeticFunction.log +
          roughCoreAF Z R B * ArithmeticFunction.log := by
      rw [add_mul]

/-- On the depth-four range, the same pre-logarithm split reconstructs the
actual von Mangoldt coefficient pointwise. -/
theorem vonMangoldt_eq_regularCore_mul_log_add_roughCore_mul_log_apply
    (Z B : ℕ) {R n : ℕ} (hR : 0 < R) (hnZ : n ≤ Z ^ 4) :
    ArithmeticFunction.vonMangoldt n =
      (regularCoreAF Z R B * ArithmeticFunction.log) n +
        (roughCoreAF Z R B * ArithmeticFunction.log) n := by
  rw [← HBDepthFour.hb4_eq_vonMangoldt Z n hnZ]
  exact DFunLike.congr_fun
    (hb4_eq_regularCore_mul_log_add_roughCore_mul_log Z B hR) n

/-- On the certified range of the depth-four identity, the divisor-dependent
convolution family reconstructs the von Mangoldt coefficient itself. -/
theorem sum_convolutionPiece_eq_vonMangoldt (Z : ℕ) {R n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) (hnZ : n ≤ Z ^ 4) :
    ∑ a ∈ Finset.Icc 1 R,
      convolutionPiece (fun m => HBDepthFour.hb4 Z m) R a n =
        ArithmeticFunction.vonMangoldt n := by
  rw [hb4_sum_convolutionPiece Z hn hR, HBDepthFour.hb4_eq_vonMangoldt Z n hnZ]

/-- The actual Heath--Brown coefficient can be recombined over arbitrary
outer scales, in the order required by a retained-variable estimate. -/
theorem hb4_sum_blockRefinement {ι : Type*} [DecidableEq ι]
    (Z k : ℕ) (block : ℕ → ι) (I : Finset ι)
    {R n : ℕ} (hn : n ≠ 0) (hR : 0 < R)
    (hcover : block (canonicalDivisor n R) ∈ I) :
    ∑ i ∈ I,
      blockRefinement (fun m => HBDepthFour.hb4 Z m) R k block i n =
        HBDepthFour.hb4 Z n := by
  exact sum_blockRefinement (fun m => HBDepthFour.hb4 Z m) k block I hn hR hcover

theorem sum_blockRefinement_eq_vonMangoldt {ι : Type*} [DecidableEq ι]
    (Z k : ℕ) (block : ℕ → ι) (I : Finset ι)
    {R n : ℕ} (hn : n ≠ 0) (hR : 0 < R) (hnZ : n ≤ Z ^ 4)
    (hcover : block (canonicalDivisor n R) ∈ I) :
    ∑ i ∈ I,
      blockRefinement (fun m => HBDepthFour.hb4 Z m) R k block i n =
        ArithmeticFunction.vonMangoldt n := by
  rw [hb4_sum_blockRefinement Z k block I hn hR hcover,
    HBDepthFour.hb4_eq_vonMangoldt Z n hnZ]

/-- The regular fibers, whose first factor is within multiplicative tolerance
`B` of the target cutoff. -/
def regularRefinement (c : ℕ → ℝ) (R B n : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Icc 1 R).filter (fun a => R < a * B),
    convolutionPiece c R a n

/-- The complementary fibers.  Every contributing cofactor is `B`-rough. -/
def roughRefinement (c : ℕ → ℝ) (R B n : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Icc 1 R).filter (fun a => ¬R < a * B),
    convolutionPiece c R a n

/-- Exact pointwise split into the terminal-scale family and the rough
exceptional family. -/
theorem regular_add_rough (c : ℕ → ℝ) {R B n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) :
    regularRefinement c R B n + roughRefinement c R B n = c n := by
  rw [regularRefinement, roughRefinement]
  rw [Finset.sum_filter_add_sum_filter_not]
  exact sum_convolutionPiece c hn hR

theorem hb4_regular_add_rough (Z : ℕ) {R B n : ℕ}
    (hn : n ≠ 0) (hR : 0 < R) :
    regularRefinement (fun m => HBDepthFour.hb4 Z m) R B n +
      roughRefinement (fun m => HBDepthFour.hb4 Z m) R B n =
        HBDepthFour.hb4 Z n := by
  exact regular_add_rough (fun m => HBDepthFour.hb4 Z m) hn hR

/-- A nonzero rough fiber has exactly the promised rough complementary
factor.  This is the explicit exceptional support which the fixed-box
superposition lacked. -/
theorem rough_fiber_cofactor {c : ℕ → ℝ} {R B a n : ℕ}
    (hR : 0 < R) (hpiece : convolutionPiece c R a n ≠ 0)
    (hrough : ¬R < a * B) :
    ∀ q : ℕ, q.Prime → q ∣ canonicalCofactor n R → B < q := by
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    simp [convolutionPiece] at hpiece
  have hcanonPiece := convolutionPiece_eq_canonicalPiece c (a := a) hn hR
  have hcanon : canonicalDivisor n R = a := by
    by_contra hne
    rw [hcanonPiece, canonicalPiece, if_neg hne] at hpiece
    exact hpiece rfl
  obtain hregular | hcofactor := canonical_regular_or_rough (n := n) (B := B) hR
  · rw [hcanon] at hregular
    exact (hrough hregular).elim
  · exact hcofactor

/-- In the first exceptional size range the rough complementary factor is a
single prime, so it can be retained as a prime variable rather than treated
as an uncontrolled balanced coefficient. -/
theorem rough_fiber_cofactor_prime {c : ℕ → ℝ} {R B a n : ℕ}
    (hnR : R < n) (hR : 0 < R)
    (hpiece : convolutionPiece c R a n ≠ 0)
    (hrough : ¬R < a * B)
    (hsize : canonicalCofactor n R < (B + 1) ^ 2) :
    (canonicalCofactor n R).Prime := by
  apply prime_of_rough_of_lt_sq (canonicalCofactor_one_lt hnR hR)
  · exact rough_fiber_cofactor hR hpiece hrough
  · exact hsize

/-- In the next exceptional size range the retained cofactor is still fully
structured: it is prime or a product of two primes. -/
theorem rough_fiber_cofactor_prime_or_product_of_two_primes
    {c : ℕ → ℝ} {R B a n : ℕ}
    (hnR : R < n) (hR : 0 < R)
    (hpiece : convolutionPiece c R a n ≠ 0)
    (hrough : ¬R < a * B)
    (hsize : canonicalCofactor n R < (B + 1) ^ 3) :
    (canonicalCofactor n R).Prime ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ canonicalCofactor n R = p * q := by
  exact prime_or_product_of_two_primes_of_rough_of_lt_cube
    (canonicalCofactor_one_lt hnR hR)
    (rough_fiber_cofactor hR hpiece hrough) hsize

end EtaDivisorRefinement
end Zeta85
end RH

end
