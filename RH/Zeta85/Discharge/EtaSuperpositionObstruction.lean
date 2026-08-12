/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/EtaSuperpositionObstruction.lean

A finite support-model obstruction relevant to a pointwise asymmetric
superposition in the eta > 1/2 route.

At eta = 3/4 and base scale T = 5^4 = 625, the balanced square-root boxes
[25,50] x [25,50] contain the ordered products 29*31 and 31*29, both 899.
The proposed short box [5,10], of T^(1/4)-scale, contains no divisor of 899.
Consequently every finite signed sum of Dirichlet convolutions whose first
factor is supported in [5,10] vanishes at 899, while the balanced-box model
coefficient is nonzero there.  Thus a pointwise finite superposition with a
common asymmetric support cannot refactor even this finite support model.

No theorem here identifies this model coefficient with an actual terminal
Heath--Brown coefficient or proves that such a coefficient is nonzero at the
witness.  The result therefore does not by itself kill `(EF_eta)`.  It does
show what extra source identification `(EF_eta)` would have to survive.
Pieces whose first support remains in the same divisor-free box are killed
even if signed, overlapping, or scale-dependent.  A surviving construction
must leave that box (for example through divisor-dependent or exceptional
support), retain the original variables, or be non-pointwise.
-/
import Mathlib

open scoped BigOperators
open Finset

noncomputable section

namespace RH.Zeta85.EtaSuperpositionObstruction

/-- The indicator of a closed natural-number box, with integer values so
finite superpositions may have arbitrary signs. -/
def boxIndicator (lo hi n : ℕ) : ℤ :=
  if n ∈ Finset.Icc lo hi then 1 else 0

/-- A finite Dirichlet-convolution coefficient. -/
def convolutionCoeff (u v : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ xy ∈ n.divisorsAntidiagonal, u xy.1 * v xy.2

/-- A finite signed superposition of convolution coefficients. -/
def finiteSuperposition {ι : Type*} (I : Finset ι)
    (u v : ι → ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ I, convolutionCoeff (u i) (v i) n

/-- The concrete balanced-box model coefficient at the eta=3/4 witness. -/
def balancedBoxModelCoeff (n : ℕ) : ℤ :=
  convolutionCoeff (boxIndicator 25 50) (boxIndicator 25 50) n

/-- A single balanced atom used to state the scale-free prime-square
version of the obstruction. -/
def pointIndicator (q n : ℕ) : ℤ :=
  if n = q then 1 else 0

/-- Generic support obstruction: a Dirichlet convolution vanishes at `n`
if no point in the support of its first factor divides `n`. -/
theorem convolutionCoeff_eq_zero_of_no_supported_divisor
    (u v : ℕ → ℤ) (n : ℕ)
    (havoid : ∀ r, u r ≠ 0 → ¬r ∣ n) :
    convolutionCoeff u v n = 0 := by
  unfold convolutionCoeff
  apply Finset.sum_eq_zero
  intro xy hxy
  have hprod : xy.1 * xy.2 = n :=
    (Nat.mem_divisorsAntidiagonal.mp hxy).1
  by_cases huz : u xy.1 = 0
  · simp [huz]
  · have hdvd : xy.1 ∣ n := ⟨xy.2, hprod.symm⟩
    exact (havoid xy.1 huz hdvd).elim

/-- A prime square has no divisor strictly between `1` and its prime
square root.  This is the scale-free form of the support gap. -/
theorem no_prime_sq_divisor_between {q r : ℕ} (hq : q.Prime)
    (hr1 : 1 < r) (hrq : r < q) : ¬r ∣ q ^ 2 := by
  intro hdvd
  obtain ⟨k, hk, hkr⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  interval_cases k <;> subst r
  · norm_num at hr1
  · simp at hrq
  · nlinarith [hq.two_le]

/-- The point-support model coefficient is nonzero at the prime square. -/
theorem pointIndicator_convolution_sq {q : ℕ} (hq : 0 < q) :
    convolutionCoeff (pointIndicator q) (pointIndicator q) (q ^ 2) = 1 := by
  classical
  unfold convolutionCoeff
  have hmem : (q, q) ∈ (q ^ 2).divisorsAntidiagonal := by
    apply Nat.mem_divisorsAntidiagonal.mpr
    exact ⟨by simp [pow_two], pow_ne_zero 2 hq.ne'⟩
  calc
    ∑ xy ∈ (q ^ 2).divisorsAntidiagonal,
        pointIndicator q xy.1 * pointIndicator q xy.2 =
        pointIndicator q q * pointIndicator q q := by
      apply Finset.sum_eq_single (q, q)
      · intro xy hxy hne
        by_cases hleft : xy.1 = q
        · by_cases hright : xy.2 = q
          · exact (hne (Prod.ext hleft hright)).elim
          · simp [pointIndicator, hright]
        · simp [pointIndicator, hleft]
      · exact fun hnot => (hnot hmem).elim
    _ = 1 := by simp [pointIndicator]

/-- At every prime-square scale, no finite signed superposition supported
strictly below the model prime can equal its point-support model coefficient.
For `T=q^2` and `eta=3/4`, the usual short dyadic box is eventually a
subset of this broad interval `1 < r < q`. -/
theorem no_primePointModel_finiteSuperposition {ι : Type*} (I : Finset ι)
    (u v : ι → ℕ → ℤ) {q : ℕ} (hq : q.Prime)
    (hu : ∀ i ∈ I, ∀ n, u i n ≠ 0 → 1 < n ∧ n < q) :
    (fun n => finiteSuperposition I u v n) ≠
      convolutionCoeff (pointIndicator q) (pointIndicator q) := by
  intro heq
  have hzero : finiteSuperposition I u v (q ^ 2) = 0 := by
    unfold finiteSuperposition
    apply Finset.sum_eq_zero
    intro i hi
    apply convolutionCoeff_eq_zero_of_no_supported_divisor
    intro r hur
    exact no_prime_sq_divisor_between hq (hu i hi r hur).1 (hu i hi r hur).2
  have hsq := congrFun heq (q ^ 2)
  rw [hzero, pointIndicator_convolution_sq hq.pos] at hsq
  norm_num at hsq

/-- The target short box contains no divisor of 899. -/
theorem no_short_box_divisor :
    ∀ r ∈ Finset.Icc 5 10, ¬r ∣ 899 := by
  decide

/-- Any convolution whose first factor is supported in the short box
vanishes at the support-model semiprime witness, independently of its second
factor. -/
theorem convolutionCoeff_899_eq_zero
    (u v : ℕ → ℤ)
    (hu : ∀ n, u n ≠ 0 → n ∈ Finset.Icc 5 10) :
    convolutionCoeff u v 899 = 0 := by
  apply convolutionCoeff_eq_zero_of_no_supported_divisor
  intro r hur
  exact no_short_box_divisor r (hu r hur)

/-- Hence every finite signed superposition with the same short support
vanishes at 899.  No cardinality or coefficient-size hypothesis is used. -/
theorem finiteSuperposition_899_eq_zero {ι : Type*} (I : Finset ι)
    (u v : ι → ℕ → ℤ)
    (hu : ∀ i ∈ I, ∀ n, u i n ≠ 0 → n ∈ Finset.Icc 5 10) :
    finiteSuperposition I u v 899 = 0 := by
  unfold finiteSuperposition
  apply Finset.sum_eq_zero
  intro i hi
  exact convolutionCoeff_899_eq_zero (u i) (v i) (hu i hi)

/-- The balanced-box model coefficient is nonzero at the same integer: the
two ordered factorizations are 29*31 and 31*29. -/
theorem balancedBoxModelCoeff_899 : balancedBoxModelCoeff 899 = 2 := by
  set_option maxRecDepth 100000 in
    decide

/-- Exact finite obstruction to a pointwise finite signed asymmetric
superposition with common short support. -/
theorem no_balancedBoxModel_finiteSuperposition {ι : Type*} (I : Finset ι)
    (u v : ι → ℕ → ℤ)
    (hu : ∀ i ∈ I, ∀ n, u i n ≠ 0 → n ∈ Finset.Icc 5 10) :
    (fun n => finiteSuperposition I u v n) ≠ balancedBoxModelCoeff := by
  intro h
  have h899 := congrFun h 899
  rw [finiteSuperposition_899_eq_zero I u v hu, balancedBoxModelCoeff_899] at h899
  norm_num at h899

/-! ## Exact power saving demanded by a retained-variable theorem -/

/-- On the balanced eta > 1/2 block, the positive progression term `PQ`
has exponent `1+2*eta`, so its excess over trace `1+eta` is exactly eta. -/
theorem balanced_progression_PQ_excess (eta : ℝ) :
    (1 + 2 * eta) - (1 + eta) = eta := by ring

/-- The `PH` term has exponent `1/2+2*eta`, leaving excess eta-1/2. -/
theorem balanced_progression_PH_excess (eta : ℝ) :
    (1 / 2 + 2 * eta) - (1 + eta) = eta - 1 / 2 := by ring

/-- Thus a retained-variable estimate cannot be obtained from the same
positive progression majorant anywhere in the audited interval. -/
theorem balanced_progression_requires_cancellation {eta : ℝ}
    (heta : 1 / 2 < eta) :
    1 + eta < 1 + 2 * eta ∧ 1 + eta < 1 / 2 + 2 * eta := by
  constructor <;> linarith

end RH.Zeta85.EtaSuperpositionObstruction

end
