/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Inputs95
import Zeta23.Taper.GevreyRamps
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Deterministic Rudnick--Sarnak contraction reduction

This file proves the finite and scalar part of R3 without adding an analytic
input.  It does four things.

* `gaugeFixedCyclicSymbol` is a compactly supported gauge fixing of the
  cyclic symbol in formula (23), identical to it on every RS argument.
* `rsMainTerm_k1`--`rsMainTerm_k4` enumerate every disjoint pairing in the
  existing `rsMainTerm` interface: `0`, `1`, `3`, and `6 + 3` contractions.
* `centeredContraction_eq_formula18` proves that the uncentered contraction
  formula (27), after the binomial centering in (28), is formula (18).
* `topHat_centeredContraction_eq_formula21` specializes those scalar terms to
  the already proved Mathlib integrals in `TopHatMoments` and obtains the
  repository's `formula21Moment` for every `k <= 4`.

The exact analytic bridge still needed here is an equality between the
evaluated RS main term and `uncenteredContractionMoment`.  Applying that
equality to an actual block additionally requires common height smoothing, the
`log T` versus `l T` normalization, complex-frequency Poisson summability at
off-line zeros, and the missing `k = 3, 4` finite-grid/Fubini/end estimates.
The existing `RS1996ZetaInputs.theorem31` and the real-frequency `k = 2`
Poisson/EndsCore API do not provide those steps.
-/

open MeasureTheory Set
open scoped BigOperators Matrix ContDiff Convolution

noncomputable section

namespace RH
namespace Zeta85
namespace RSReduction

/-! ## The gauge-fixed weighted cyclic symbol -/

/-- The partial sum `s_a = xi_0 + ... + xi_{a-1}` used in formula (23).
In particular, `cyclicPartialSum xi 0 = 0`. -/
def cyclicPartialSum {k : ℕ} (xi : Fin k -> ℝ) (a : Fin k) : ℝ :=
  ∑ j with j < a, xi j

/-- Formula (23), with the real scalar integral coerced to `Complex`.
This raw form is constant in the redundant gauge direction. -/
def weightedCyclicSymbol {k : ℕ} (mu : ℝ) (r : ℝ -> ℝ)
    (xi : Fin k -> ℝ) : ℂ :=
  (mu * ∫ x : ℝ,
    ∏ a : Fin k, r (x + cyclicPartialSum xi a / mu) : ℝ)

/-- At zero frequency, formula (23) is `mu * integral r^k`. -/
theorem weightedCyclicSymbol_zero {k : ℕ} (mu : ℝ) (r : ℝ -> ℝ) :
    weightedCyclicSymbol (k := k) mu r 0 =
      (mu * ∫ x : ℝ, r x ^ k : ℝ) := by
  simp [weightedCyclicSymbol, cyclicPartialSum]

/-- The real integrand in the cyclic symbol, exposed for the parametric
convolution argument. -/
def cyclicIntegrand {k : ℕ} (mu : ℝ) (r : ℝ → ℝ)
    (xi : Fin k → ℝ) (x : ℝ) : ℝ :=
  ∏ a : Fin k, r (x + cyclicPartialSum xi a / mu)

/-- A concrete smooth cutoff in the redundant total-frequency direction. -/
def rsGaugeCutoff (delta : ℝ) : ℝ → ℝ :=
  Zeta23.Taper.phi Zeta23.Taper.rhoTwo (2 * delta) delta

theorem rsGaugeCutoff_zero {delta : ℝ} (hdelta : 0 < delta) :
    rsGaugeCutoff delta 0 = 1 := by
  apply Zeta23.Taper.phi_eq_one Zeta23.Taper.rhoTwo_taper hdelta
  simp

theorem rsGaugeCutoff_support {delta : ℝ} (hdelta : 0 < delta) :
    Function.support (rsGaugeCutoff delta) ⊆ Set.Icc (-delta) delta := by
  simpa [rsGaugeCutoff] using
    (Zeta23.Taper.phi_support_subset
      (L := 2 * delta) Zeta23.Taper.rhoTwo_taper hdelta)

theorem rsGaugeCutoff_contDiff {delta : ℝ} (hdelta : 0 < delta) :
    ContDiff ℝ ∞ (rsGaugeCutoff delta) := by
  have hprod : rsGaugeCutoff delta =
      Zeta23.Taper.fP Zeta23.Taper.rhoTwo (2 * delta) delta *
        Zeta23.Taper.fM Zeta23.Taper.rhoTwo (2 * delta) delta := by
    funext u
    exact Zeta23.Taper.phi_eq_mul Zeta23.Taper.rhoTwo_taper
      hdelta le_rfl u
  rw [hprod]
  exact (Zeta23.Taper.fP_contDiff Zeta23.Taper.gevreyProfile_rhoTwo).mul
    (Zeta23.Taper.fM_contDiff Zeta23.Taper.gevreyProfile_rhoTwo)

/-- Multiplying only in the total-sum direction repairs compact support while
leaving the zero-sum hyperplane untouched. -/
def gaugeFixedCyclicSymbol {k : ℕ} (delta mu : ℝ) (r : ℝ → ℝ)
    (xi : Fin k → ℝ) : ℂ :=
  (rsGaugeCutoff delta (∑ j, xi j) : ℂ) * weightedCyclicSymbol mu r xi

/-- `rsZeroSumLift` lands exactly on the zero-sum hyperplane. -/
theorem rsZeroSumLift_sum {n : ℕ} (xi : Fin n → ℝ) :
    ∑ j : Fin (n + 1), rsZeroSumLift xi j = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp [rsZeroSumLift]

/-- The cyclic integrand is jointly smooth in all frequencies and the
integration variable. -/
theorem cyclicIntegrand_contDiff {k : ℕ} (mu : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (Function.uncurry (cyclicIntegrand (k := k) mu r)) := by
  unfold cyclicIntegrand cyclicPartialSum
  fun_prop

/-- The cyclic index zero factor gives support in the integration variable
which is uniform over all frequency parameters. -/
theorem cyclicIntegral_contDiff {n : ℕ} (mu : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hrc : HasCompactSupport r) :
    ContDiff ℝ ∞ (fun xi : Fin (n + 1) → ℝ =>
      ∫ x : ℝ, cyclicIntegrand mu r xi x) := by
  have hzero : ∀ (xi : Fin (n + 1) → ℝ) (x : ℝ),
      x ∉ tsupport r → cyclicIntegrand mu r xi x = 0 := by
    intro xi x hx
    have hrx : r x = 0 := by
      by_contra hne
      exact hx (subset_closure hne)
    unfold cyclicIntegrand
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n + 1)))
    simpa [cyclicPartialSum] using hrx
  have hconv : ContDiffOn ℝ ∞
      (fun xi : Fin (n + 1) → ℝ =>
        ((cyclicIntegrand mu r xi) ⋆[ContinuousLinearMap.mul ℝ ℝ]
          (fun _ : ℝ => (1 : ℝ))) 0) univ := by
    apply contDiffOn_convolution_left_with_param_comp
      (ContinuousLinearMap.mul ℝ ℝ) contDiffOn_const isOpen_univ
      hrc.isCompact
    · intro xi x _ hx
      exact hzero xi x hx
    · exact locallyIntegrable_const 1
    · exact (cyclicIntegrand_contDiff mu r hr).contDiffOn
  rw [← contDiffOn_univ]
  convert hconv using 1
  funext xi
  simp only [convolution, ContinuousLinearMap.mul_apply', mul_one]

theorem weightedCyclicSymbol_contDiff {n : ℕ} (mu : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hrc : HasCompactSupport r) :
    ContDiff ℝ ∞ (weightedCyclicSymbol (k := n + 1) mu r) := by
  change ContDiff ℝ ∞ (fun xi : Fin (n + 1) → ℝ =>
    ((mu * ∫ x : ℝ, cyclicIntegrand mu r xi x : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (cyclicIntegral_contDiff mu r hr hrc))

theorem gaugeFixedCyclicSymbol_contDiff {n : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (mu : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hrc : HasCompactSupport r) :
    ContDiff ℝ ∞ (gaugeFixedCyclicSymbol (k := n + 1) delta mu r) := by
  apply ContDiff.mul
  · apply Complex.ofRealCLM.contDiff.comp
    apply (rsGaugeCutoff_contDiff hdelta).comp
    fun_prop
  · exact weightedCyclicSymbol_contDiff mu r hr hrc

theorem gaugeFixedCyclicSymbol_rsZeroSumLift {n : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (mu : ℝ) (r : ℝ → ℝ) (xi : Fin n → ℝ) :
    gaugeFixedCyclicSymbol delta mu r (rsZeroSumLift xi) =
      weightedCyclicSymbol mu r (rsZeroSumLift xi) := by
  simp [gaugeFixedCyclicSymbol, rsZeroSumLift_sum,
    rsGaugeCutoff_zero hdelta]

theorem cyclicPartialSum_succ {n : ℕ} (xi : Fin (n + 1) → ℝ)
    (j : Fin n) :
    cyclicPartialSum xi j.succ =
      cyclicPartialSum xi j.castSucc + xi j.castSucc := by
  unfold cyclicPartialSum
  have heq :
      (Finset.univ.filter (fun a : Fin (n + 1) => a < j.succ)) =
        insert j.castSucc
          (Finset.univ.filter (fun a : Fin (n + 1) => a < j.castSucc)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro h
      by_cases ha : a = j.castSucc
      · exact Or.inl ha
      · right
        have hval : a.val ≠ j.val := by
          intro hv
          apply ha
          exact Fin.ext hv
        change a.val < j.val
        change a.val < j.val + 1 at h
        omega
    · rintro (rfl | h)
      · simp
      · exact h.trans (by simp)
  rw [heq, Finset.sum_insert]
  · ring
  · simp

theorem cyclicPartialSum_last {n : ℕ} (xi : Fin (n + 1) → ℝ) :
    cyclicPartialSum xi (Fin.last n) = ∑ j : Fin n, xi j.castSucc := by
  unfold cyclicPartialSum
  have heq :
      (Finset.univ.filter (fun a : Fin (n + 1) => a < Fin.last n)) =
        Finset.univ.map Fin.castSuccEmb := by
    calc
      _ = Finset.Iio (Fin.last n) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_Iio]
      _ = _ := Fin.Iio_last_eq_map
  rw [heq, Finset.sum_map]
  rfl

theorem sum_eq_cyclicPartialSum_last_add {n : ℕ}
    (xi : Fin (n + 1) → ℝ) :
    ∑ j : Fin (n + 1), xi j =
      cyclicPartialSum xi (Fin.last n) + xi (Fin.last n) := by
  rw [Fin.sum_univ_castSucc, cyclicPartialSum_last]

/-- Point support of the repaired cyclic symbol satisfies the sharp path
variation bound `(n+1) mu + delta`. -/
theorem gaugeFixedCyclicSymbol_support_subset {n : ℕ} {delta mu : ℝ}
    (hdelta : 0 < delta) (hmu : 0 < mu) (r : ℝ → ℝ)
    (hrsupp : Function.support r ⊆ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    Function.support
        (gaugeFixedCyclicSymbol (k := n + 1) delta mu r) ⊆
      {xi | ∑ j : Fin (n + 1), |xi j| ≤ (n + 1 : ℝ) * mu + delta} := by
  intro xi hxi
  have hgauge : rsGaugeCutoff delta (∑ j, xi j) ≠ 0 := by
    intro hz
    apply hxi
    simp [gaugeFixedCyclicSymbol, hz]
  have hweighted : weightedCyclicSymbol mu r xi ≠ 0 := by
    intro hz
    apply hxi
    simp [gaugeFixedCyclicSymbol, hz]
  have hsum_mem : (∑ j, xi j) ∈ Set.Icc (-delta) delta :=
    rsGaugeCutoff_support hdelta hgauge
  have hsum_abs : |∑ j, xi j| ≤ delta := abs_le.mpr hsum_mem
  have hint : (∫ x : ℝ,
      ∏ a : Fin (n + 1), r (x + cyclicPartialSum xi a / mu)) ≠ 0 := by
    intro hz
    apply hweighted
    simp [weightedCyclicSymbol, hz]
  obtain ⟨x, hx⟩ : ∃ x : ℝ,
      (∏ a : Fin (n + 1), r (x + cyclicPartialSum xi a / mu)) ≠ 0 := by
    by_contra h
    push Not at h
    simp_rw [h] at hint
    exact hint (by simp)
  have hfactor (a : Fin (n + 1)) :
      r (x + cyclicPartialSum xi a / mu) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hx a (Finset.mem_univ a)
  have hpoint (a : Fin (n + 1)) :
      x + cyclicPartialSum xi a / mu ∈
        Set.Icc (-(1 : ℝ) / 2) (1 / 2) :=
    hrsupp (hfactor a)
  have hdiff (a b : Fin (n + 1)) :
      |cyclicPartialSum xi a - cyclicPartialSum xi b| ≤ mu := by
    have ha := hpoint a
    have hb := hpoint b
    have hid :
        (cyclicPartialSum xi a - cyclicPartialSum xi b) / mu =
          (x + cyclicPartialSum xi a / mu) -
            (x + cyclicPartialSum xi b / mu) := by
      ring
    have hdiv :
        |(cyclicPartialSum xi a - cyclicPartialSum xi b) / mu| ≤ 1 := by
      rw [hid, abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    rw [abs_div, abs_of_pos hmu] at hdiv
    have hmul := (div_le_iff₀ hmu).mp hdiv
    nlinarith
  have hstep (j : Fin n) : |xi j.castSucc| ≤ mu := by
    simpa [cyclicPartialSum_succ] using hdiff j.succ j.castSucc
  have hlastPartial : |cyclicPartialSum xi (Fin.last n)| ≤ mu := by
    simpa [cyclicPartialSum] using hdiff (Fin.last n) 0
  have hlastEq :
      xi (Fin.last n) =
        (∑ j : Fin (n + 1), xi j) - cyclicPartialSum xi (Fin.last n) := by
    linarith [sum_eq_cyclicPartialSum_last_add xi]
  have hlast : |xi (Fin.last n)| ≤ delta + mu := by
    rw [hlastEq]
    exact (abs_sub _ _).trans (add_le_add hsum_abs hlastPartial)
  change (∑ j : Fin (n + 1), |xi j|) ≤ (n + 1 : ℝ) * mu + delta
  rw [Fin.sum_univ_castSucc]
  calc
    (∑ j : Fin n, |xi j.castSucc|) + |xi (Fin.last n)| ≤
        (∑ _j : Fin n, mu) + (delta + mu) :=
      add_le_add (Finset.sum_le_sum fun j _ => hstep j) hlast
    _ = (n + 1 : ℝ) * mu + delta := by simp; ring

/-- Closing the point support preserves the same non-strict budget; a strict
numeric budget therefore supplies exactly the support hypothesis of RS 3.1. -/
theorem gaugeFixedCyclicSymbol_tsupport_subset {n : ℕ} {delta mu : ℝ}
    (hdelta : 0 < delta) (hmu : 0 < mu) (r : ℝ → ℝ)
    (hrsupp : Function.support r ⊆ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    tsupport (gaugeFixedCyclicSymbol (k := n + 1) delta mu r) ⊆
      {xi | ∑ j : Fin (n + 1), |xi j| < 2} := by
  have hclosed : IsClosed
      {xi : Fin (n + 1) → ℝ |
        ∑ j : Fin (n + 1), |xi j| ≤ (n + 1 : ℝ) * mu + delta} := by
    apply isClosed_le
    · fun_prop
    · fun_prop
  have hclosure := closure_minimal
    (gaugeFixedCyclicSymbol_support_subset hdelta hmu r hrsupp) hclosed
  intro xi hxi
  exact lt_of_le_of_lt (hclosure hxi) hbudget

theorem rsGaugeTest_gaugeFixed {n : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (mu : ℝ) (r : ℝ → ℝ)
    (x : Fin (n + 1) → ℂ) :
    rsGaugeTest (gaugeFixedCyclicSymbol delta mu r) x =
      rsGaugeTest (weightedCyclicSymbol mu r) x := by
  unfold rsGaugeTest
  simp_rw [gaugeFixedCyclicSymbol_rsZeroSumLift hdelta mu r]

/-- Every vector used by a disjoint-pair contraction is exactly zero-sum.
This requires no disjointness hypothesis: each contraction variable occurs
once with each sign by construction. -/
theorem rsPairVector_sum {n q : ℕ}
    (pairing : (Fin q -> Fin (n + 1)) × (Fin q -> Fin (n + 1)))
    (w : Fin q -> ℝ) :
    ∑ i : Fin (n + 1), rsPairVector pairing w i = 0 := by
  have hsum (i0 : Fin (n + 1)) (c : ℝ) :
      ∑ i : Fin (n + 1), (if i0 = i then c else 0) = c := by
    simp
  have hpos :
      (∑ i : Fin (n + 1), ∑ a : Fin q,
        if pairing.1 a = i then w a else 0) = ∑ a : Fin q, w a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => hsum (pairing.1 a) (w a))
  have hneg :
      (∑ i : Fin (n + 1), ∑ a : Fin q,
        if pairing.2 a = i then w a else 0) = ∑ a : Fin q, w a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => hsum (pairing.2 a) (w a))
  simp only [rsPairVector, Finset.sum_sub_distrib]
  rw [hpos, hneg, sub_self]

theorem gaugeFixedCyclicSymbol_rsPairVector {n q : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (mu : ℝ) (r : ℝ → ℝ)
    (pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1)))
    (w : Fin q → ℝ) :
    gaugeFixedCyclicSymbol delta mu r (rsPairVector pairing w) =
      weightedCyclicSymbol mu r (rsPairVector pairing w) := by
  simp [gaugeFixedCyclicSymbol, rsPairVector_sum,
    rsGaugeCutoff_zero hdelta]

theorem rsPairIntegral_gaugeFixed {n q : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (mu : ℝ) (r : ℝ → ℝ)
    (pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))) :
    rsPairIntegral (gaugeFixedCyclicSymbol delta mu r) pairing =
      rsPairIntegral (weightedCyclicSymbol mu r) pairing := by
  unfold rsPairIntegral
  simp_rw [gaugeFixedCyclicSymbol_rsPairVector hdelta mu r pairing]

/-- Gauge repair preserves the complete bracketed RS main term exactly. -/
theorem rsMainTerm_gaugeFixed {n : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (mu : ℝ) (r : ℝ → ℝ) :
    rsMainTerm (n := n)
        (gaugeFixedCyclicSymbol (k := n + 1) delta mu r) =
      rsMainTerm (n := n) (weightedCyclicSymbol (k := n + 1) mu r) := by
  unfold rsMainTerm
  rw [show gaugeFixedCyclicSymbol delta mu r 0 =
      weightedCyclicSymbol mu r 0 by
    simp [gaugeFixedCyclicSymbol, rsGaugeCutoff_zero hdelta]
    rfl]
  simp_rw [rsPairIntegral_gaugeFixed (n := n) hdelta mu r]

/-- RS Theorem 3.1 applied through the compact gauge repair, then rewritten
back to the original cyclic symbol in both the tuple sum and its main term. -/
theorem RS1996ZetaInputs.theorem31_weightedCyclicSymbol
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (g : Fin (n + 1) → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j))
    {delta mu : ℝ} (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hrc : HasCompactSupport r)
    (hrsupp : Function.support r ⊆ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 ≤ T₀ ∧ ∀ T ≥ T₀,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := n + 1) mu r) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := n + 1) mu r) T rho) -
          rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
            rsMainTerm (weightedCyclicSymbol (k := n + 1) mu r)‖ ≤ C * T := by
  obtain ⟨C, T₀, hC, hT₀, hmain⟩ := hRS.theorem31 n g
    (gaugeFixedCyclicSymbol (k := n + 1) delta mu r) hg
    ((gaugeFixedCyclicSymbol_contDiff hdelta mu r hr hrc).of_le
      (by exact_mod_cast le_top))
    (gaugeFixedCyclicSymbol_tsupport_subset hdelta hmu r hrsupp hbudget)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T hT
  have hterm :
      rsZeroTupleTerm Z g
          (gaugeFixedCyclicSymbol (k := n + 1) delta mu r) T =
        rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := n + 1) mu r) T := by
    funext rho
    unfold rsZeroTupleTerm
    rw [rsGaugeTest_gaugeFixed hdelta]
  simpa only [hterm, rsMainTerm_gaugeFixed hdelta mu r] using hmain T hT

/-! ## Exact enumeration of the RS disjoint-pair main term -/

/-- The `k = 1` (`n = 0`) main term has no contraction. -/
theorem rsMainTerm_k1 (Phi : (Fin 1 -> ℝ) -> ℂ) :
    rsMainTerm (n := 0) Phi = Phi 0 := by
  simp [rsMainTerm]

/-- The `k = 2` (`n = 1`) main term has its unique one-pair contraction. -/
theorem rsMainTerm_k2 (Phi : (Fin 2 -> ℝ) -> ℂ) :
    rsMainTerm (n := 1) Phi =
      Phi 0 + rsPairIntegral Phi (![0], ![1]) := by
  rw [rsMainTerm]
  norm_num
  rw [show rsPairings 1 1 = {(![0], ![1])} by decide]
  simp

/-- The `k = 3` (`n = 2`) main term has all three one-pair contractions. -/
theorem rsMainTerm_k3 (Phi : (Fin 3 -> ℝ) -> ℂ) :
    rsMainTerm (n := 2) Phi =
      Phi 0 +
        (rsPairIntegral Phi (![0], ![1]) +
         rsPairIntegral Phi (![0], ![2]) +
         rsPairIntegral Phi (![1], ![2])) := by
  rw [rsMainTerm]
  norm_num
  rw [show rsPairings 2 1 =
    {(![0], ![1]), (![0], ![2]), (![1], ![2])} by decide]
  simp
  ring

/-- The `k = 4` (`n = 3`) main term has six one-pair contractions and the
three perfect matchings.  The order below is the canonical order encoded by
`rsPairings`; no symmetry of `Phi` is assumed. -/
theorem rsMainTerm_k4 (Phi : (Fin 4 -> ℝ) -> ℂ) :
    rsMainTerm (n := 3) Phi = Phi 0 +
      (rsPairIntegral Phi (![0], ![1]) +
       rsPairIntegral Phi (![0], ![2]) +
       rsPairIntegral Phi (![0], ![3]) +
       rsPairIntegral Phi (![1], ![2]) +
       rsPairIntegral Phi (![1], ![3]) +
       rsPairIntegral Phi (![2], ![3])) +
      (rsPairIntegral Phi (![0, 1], ![2, 3]) +
       rsPairIntegral Phi (![0, 1], ![3, 2]) +
       rsPairIntegral Phi (![0, 2], ![1, 3])) := by
  rw [rsMainTerm]
  rw [show Finset.Icc 1 2 = {1, 2} by decide]
  norm_num
  rw [show rsPairings 3 1 =
    {(![0], ![1]), (![0], ![2]), (![0], ![3]),
     (![1], ![2]), (![1], ![3]), (![2], ![3])} by decide]
  rw [show rsPairings 3 2 =
    {(![0, 1], ![2, 3]), (![0, 1], ![3, 2]),
     (![0, 2], ![1, 3])} by decide]
  simp
  ring

/-! ## Formula (27) to formula (18) -/

/-- The ten scalar terms remaining after the individual pair integrals have
been evaluated.  The names are the literal terms in formula (18):

* `qMomentj = integral q^j`;
* `rh`, `qrh`, and `qSquaredRh` are `integral r h`, `integral q r h`, and
  `integral q^2 r h`;
* `doubleQr` is the two-variable `q r` distance contraction;
* `rSquaredHSquared` and `crossing` are the two `mu^4` contractions.

This is scalar data, not a proposition about an RS tuple sum or a finite
matrix block. -/
structure R3ScalarTerms where
  qMoment1 : ℝ
  qMoment2 : ℝ
  qMoment3 : ℝ
  qMoment4 : ℝ
  rh : ℝ
  qrh : ℝ
  qSquaredRh : ℝ
  doubleQr : ℝ
  rSquaredHSquared : ℝ
  crossing : ℝ

/-- Formula (27), rewritten using `r = q + 1` before centering.
For example, `integral r^3 h = qSquaredRh + 2 * qrh + rh`, while the
opposite-pair term is `doubleQr + 2 * qrh + rh`. -/
def uncenteredContractionMoment (d : R3ScalarTerms) (mu : ℝ) : ℕ -> ℝ
  | 0 => 1
  | 1 => 1 + d.qMoment1
  | 2 => 1 + 2 * d.qMoment1 + d.qMoment2 + mu ^ 2 * d.rh
  | 3 => 1 + 3 * d.qMoment1 + 3 * d.qMoment2 + d.qMoment3 +
      3 * mu ^ 2 * (d.qrh + d.rh)
  | 4 => 1 + 4 * d.qMoment1 + 6 * d.qMoment2 + 4 * d.qMoment3 + d.qMoment4 +
      4 * mu ^ 2 * (d.qSquaredRh + 2 * d.qrh + d.rh) +
      2 * mu ^ 2 * (d.doubleQr + 2 * d.qrh + d.rh) +
      2 * mu ^ 4 * d.rSquaredHSquared + mu ^ 4 * d.crossing
  | _ => 0

/-- The exact binomial centering transform in formula (28). -/
def centeredTransform (c : ℕ -> ℝ) (k : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ (k - a) * (Nat.choose k a : ℝ) * c a

/-- The right side of formula (18), degree by degree. -/
def formula18Moment (d : R3ScalarTerms) (mu : ℝ) : ℕ -> ℝ
  | 0 => 1
  | 1 => d.qMoment1
  | 2 => d.qMoment2 + mu ^ 2 * d.rh
  | 3 => d.qMoment3 + 3 * mu ^ 2 * d.qrh
  | 4 => d.qMoment4 +
      4 * mu ^ 2 * d.qSquaredRh +
      2 * mu ^ 2 * d.doubleQr +
      2 * mu ^ 4 * d.rSquaredHSquared + mu ^ 4 * d.crossing
  | _ => 0

/-- Machine-checked R3 centering: formula (27) implies formula (18) for
every degree through four.  This is a polynomial identity and assumes no
analytic or matrix conclusion. -/
theorem centeredContraction_eq_formula18
    (d : R3ScalarTerms) (mu : ℝ) (k : ℕ) (hk : k <= 4) :
    centeredTransform (uncenteredContractionMoment d mu) k =
      formula18Moment d mu k := by
  interval_cases k <;>
    norm_num [centeredTransform, uncenteredContractionMoment, formula18Moment,
      Finset.sum_range_succ, Nat.choose] <;> ring

/-! ## Formula (21): the constructed top-hat scalar specialization -/

/-- The explicit formula-(18) scalar terms constructed from the actual
Mathlib integrals already proved in `TopHatMoments`. -/
def topHatR3Terms (p : ℝ) : R3ScalarTerms where
  qMoment1 := TopHatMoments.centeredMoment 1 p
  qMoment2 := TopHatMoments.centeredMoment 2 p
  qMoment3 := TopHatMoments.centeredMoment 3 p
  qMoment4 := TopHatMoments.centeredMoment 4 p
  rh := TopHatMoments.rDistanceIntegral p
  qrh := TopHatMoments.qrDistanceIntegral p
  qSquaredRh := TopHatMoments.qSquaredRDistanceIntegral p
  doubleQr := TopHatMoments.doubleQrDistanceIntegral p
  rSquaredHSquared := TopHatMoments.squaredPotentialIntegral p
  crossing := TopHatMoments.formulaCrossingIntegral p

/-- Formula (18) for the constructed top-hat terms is exactly the
repository's formula (21), for `1 <= k <= 4`. -/
theorem topHat_formula18_eq_formula21 {p mu : ℝ}
    (hp : 0 < p) (hp1 : p <= 1) (k : ℕ) (hk1 : 1 <= k) (hk4 : k <= 4) :
    formula18Moment (topHatR3Terms p) mu k = formula21Moment k mu p := by
  interval_cases k <;>
    simp [formula18Moment, topHatR3Terms, formula21Moment,
      TopHatMoments.formula21M2Integral,
      TopHatMoments.formula21M3Integral,
      TopHatMoments.formula21M4Integral,
      TopHatMoments.centeredMoment_one hp hp1]

/-- The complete unconditional scalar specialization: centering the
formula-(27) contractions built from the proved top-hat integrals yields
formula (21) through degree four. -/
theorem topHat_centeredContraction_eq_formula21 {p mu : ℝ}
    (hp : 0 < p) (hp1 : p <= 1) (k : ℕ) (hk1 : 1 <= k) (hk4 : k <= 4) :
    centeredTransform (uncenteredContractionMoment (topHatR3Terms p) mu) k =
      formula21Moment k mu p := by
  calc
    centeredTransform (uncenteredContractionMoment (topHatR3Terms p) mu) k =
        formula18Moment (topHatR3Terms p) mu k :=
      centeredContraction_eq_formula18 (topHatR3Terms p) mu k hk4
    _ = formula21Moment k mu p :=
      topHat_formula18_eq_formula21 hp hp1 k hk1 hk4

end RSReduction
end Zeta85
end RH

end
