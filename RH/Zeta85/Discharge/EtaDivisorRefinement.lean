/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.HBDepthFour
import RH.Zeta85.Discharge.BBLRGCDAllocation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Prime.Basic

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
