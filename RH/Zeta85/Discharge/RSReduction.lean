/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import RH.Zeta85.Inputs95

/-!
# Deterministic Rudnick--Sarnak contraction reduction

This file proves the finite and scalar part of R3 without adding an analytic
input.  It does four things.

* `weightedCyclicSymbol` is the gauge-fixed cyclic symbol in formula (23).
* `rsMainTerm_k1`--`rsMainTerm_k4` enumerate every disjoint pairing in the
  existing `rsMainTerm` interface: `0`, `1`, `3`, and `6 + 3` contractions.
* `centeredContraction_eq_formula18` proves that the uncentered contraction
  formula (27), after the binomial centering in (28), is formula (18).
* `topHat_centeredContraction_eq_formula21` specializes those scalar terms to
  the already proved Mathlib integrals in `TopHatMoments` and obtains the
  repository's `formula21Moment` for every `k <= 4`.

The exact analytic bridge deliberately absent here is an equality between
`rsMainTerm (weightedCyclicSymbol ...)` and `uncenteredContractionMoment`.
Proving it requires smoothness and strict-support lemmas for the symbol and
evaluation of the displayed `rsPairIntegral`s.  Applying that equality to an
actual block additionally requires common height smoothing, the
`log T` versus `l T` normalization, complex-frequency Poisson summability at
off-line zeros, and the missing `k = 3, 4` finite-grid/Fubini/end estimates.
The existing `RS1996ZetaInputs.theorem31` and the real-frequency `k = 2`
Poisson/EndsCore API do not provide those steps.
-/

open MeasureTheory Zeta23
open scoped BigOperators Matrix Convolution ContDiff

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
No smoothness or support claim is bundled into this definition. -/
def weightedCyclicSymbol {k : ℕ} (mu : ℝ) (r : ℝ -> ℝ)
    (xi : Fin k -> ℝ) : ℂ :=
  (mu * ∫ x : ℝ,
    ∏ a : Fin k, r (x + cyclicPartialSum xi a / mu) : ℝ)

/-- At zero frequency, formula (23) is `mu * integral r^k`. -/
theorem weightedCyclicSymbol_zero {k : ℕ} (mu : ℝ) (r : ℝ -> ℝ) :
    weightedCyclicSymbol (k := k) mu r 0 =
      (mu * ∫ x : ℝ, r x ^ k : ℝ) := by
  simp [weightedCyclicSymbol, cyclicPartialSum]

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

/-! ## Strict cyclic support at order four -/

/-- Two points in the same closed interval differ by at most its width. -/
theorem abs_sub_le_interval_width {a b x y : ℝ}
    (hxa : a ≤ x) (hxb : x ≤ b) (hya : a ≤ y) (hyb : y ≤ b) :
    |x - y| ≤ b - a := by
  rw [abs_le]
  constructor <;> linarith

/-- If a profile is supported in one interval, a nonzero quartic cyclic
symbol has total frequency at most four bandwidths, plus the displacement
normal to the zero-sum hyperplane. -/
theorem weightedCyclicSymbol_k4_l1_bound
    (mu a b : ℝ) (r : ℝ -> ℝ) (hmu : 0 < mu)
    (hr : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (xi : Fin 4 -> ℝ)
    (hPhi : weightedCyclicSymbol (k := 4) mu r xi ≠ 0) :
    ∑ i : Fin 4, |xi i| ≤
      4 * mu * (b - a) + |∑ i : Fin 4, xi i| := by
  let I : ℝ -> ℝ := fun x =>
    ∏ j : Fin 4, r (x + cyclicPartialSum xi j / mu)
  have hint : (∫ x : ℝ, I x) ≠ 0 := by
    intro hz
    apply hPhi
    simp [weightedCyclicSymbol, I, hz]
  have hex : ∃ x : ℝ, I x ≠ 0 := by
    by_contra hx
    push_neg at hx
    apply hint
    calc
      (∫ x : ℝ, I x) = ∫ _x : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hx x
      _ = 0 := by simp
  rcases hex with ⟨x, hx⟩
  have hfactor (j : Fin 4) :
      r (x + cyclicPartialSum xi j / mu) ≠ 0 := by
    intro h
    apply hx
    dsimp only [I]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h
  have hcp1 : cyclicPartialSum xi (1 : Fin 4) = xi 0 := by
    rw [cyclicPartialSum,
      show Finset.filter (fun j : Fin 4 => j < (1 : Fin 4))
          Finset.univ = {0} by decide]
    simp
  have hcp2 : cyclicPartialSum xi (2 : Fin 4) = xi 0 + xi 1 := by
    rw [cyclicPartialSum,
      show Finset.filter (fun j : Fin 4 => j < (2 : Fin 4))
          Finset.univ = {0, 1} by decide]
    simp
  have hcp3 :
      cyclicPartialSum xi (3 : Fin 4) = xi 0 + xi 1 + xi 2 := by
    rw [cyclicPartialSum,
      show Finset.filter (fun j : Fin 4 => j < (3 : Fin 4))
          Finset.univ = {0, 1, 2} by decide]
    simp
    ring
  have hr0 : r x ≠ 0 := by
    simpa [cyclicPartialSum] using hfactor (0 : Fin 4)
  have hr1 : r (x + xi 0 / mu) ≠ 0 := by
    simpa only [hcp1] using hfactor (1 : Fin 4)
  have hr2 : r (x + (xi 0 + xi 1) / mu) ≠ 0 := by
    simpa only [hcp2] using hfactor (2 : Fin 4)
  have hr3 : r (x + (xi 0 + xi 1 + xi 2) / mu) ≠ 0 := by
    simpa only [hcp3] using hfactor (3 : Fin 4)
  rcases hr x hr0 with ⟨hx0a, hx0b⟩
  rcases hr (x + xi 0 / mu) hr1 with ⟨hx1a, hx1b⟩
  rcases hr (x + (xi 0 + xi 1) / mu) hr2 with ⟨hx2a, hx2b⟩
  rcases hr (x + (xi 0 + xi 1 + xi 2) / mu) hr3
    with ⟨hx3a, hx3b⟩
  have h0 : |xi 0| ≤ mu * (b - a) := by
    have hd := abs_sub_le_interval_width hx1a hx1b hx0a hx0b
    have heq :
        xi 0 = mu * ((x + xi 0 / mu) - x) := by
      field_simp [ne_of_gt hmu]
      ring
    rw [heq, abs_mul, abs_of_pos hmu]
    exact mul_le_mul_of_nonneg_left hd hmu.le
  have h1 : |xi 1| ≤ mu * (b - a) := by
    have hd := abs_sub_le_interval_width hx2a hx2b hx1a hx1b
    have heq :
        xi 1 = mu *
          ((x + (xi 0 + xi 1) / mu) - (x + xi 0 / mu)) := by
      field_simp [ne_of_gt hmu]
      ring
    rw [heq, abs_mul, abs_of_pos hmu]
    exact mul_le_mul_of_nonneg_left hd hmu.le
  have h2 : |xi 2| ≤ mu * (b - a) := by
    have hd := abs_sub_le_interval_width hx3a hx3b hx2a hx2b
    have heq :
        xi 2 = mu *
          ((x + (xi 0 + xi 1 + xi 2) / mu) -
            (x + (xi 0 + xi 1) / mu)) := by
      field_simp [ne_of_gt hmu]
      ring
    rw [heq, abs_mul, abs_of_pos hmu]
    exact mul_le_mul_of_nonneg_left hd hmu.le
  have hcycle : |xi 0 + xi 1 + xi 2| ≤ mu * (b - a) := by
    have hd := abs_sub_le_interval_width hx3a hx3b hx0a hx0b
    have heq :
        xi 0 + xi 1 + xi 2 =
          mu * ((x + (xi 0 + xi 1 + xi 2) / mu) - x) := by
      field_simp [ne_of_gt hmu]
      ring
    rw [heq, abs_mul, abs_of_pos hmu]
    exact mul_le_mul_of_nonneg_left hd hmu.le
  have hsum :
      (∑ i : Fin 4, xi i) = xi 0 + xi 1 + xi 2 + xi 3 := by
    norm_num [Fin.sum_univ_succ]
    rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide]
    ring
  have hlastEq :
      xi 3 = (∑ i : Fin 4, xi i) - (xi 0 + xi 1 + xi 2) := by
    linarith
  have hlast :
      |xi 3| ≤ |∑ i : Fin 4, xi i| + mu * (b - a) := by
    rw [hlastEq]
    calc
      |(∑ i : Fin 4, xi i) - (xi 0 + xi 1 + xi 2)| ≤
          |∑ i : Fin 4, xi i| + |xi 0 + xi 1 + xi 2| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le (∑ i : Fin 4, xi i) (-(xi 0 + xi 1 + xi 2))
      _ ≤ |∑ i : Fin 4, xi i| + mu * (b - a) :=
        add_le_add (le_refl _) hcycle
  have habssum :
      (∑ i : Fin 4, |xi i|) =
        |xi 0| + |xi 1| + |xi 2| + |xi 3| := by
    norm_num [Fin.sum_univ_succ]
    rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide]
    ring
  rw [habssum]
  nlinarith

/-! ## Compact normal-coordinate extension

The cyclic symbol is only used on the zero-sum hyperplane.  Multiplying by a
cutoff in the normal coordinate gives a genuinely compactly supported test
without changing the gauge integral or any RS contraction. -/

/-- Multiply a Fourier test by a cutoff in the coordinate normal to the
zero-sum hyperplane. -/
def normalCutoffSymbol {k : ℕ} (chi : ℝ -> ℂ)
    (Phi : (Fin k -> ℝ) -> ℂ) (xi : Fin k -> ℝ) : ℂ :=
  chi (∑ i, xi i) * Phi xi

/-- A normalized normal cutoff is invisible on the zero-sum hyperplane. -/
theorem normalCutoffSymbol_eq_of_sum_eq_zero {k : ℕ}
    (chi : ℝ -> ℂ) (Phi : (Fin k -> ℝ) -> ℂ) (hchi : chi 0 = 1)
    {xi : Fin k -> ℝ} (hxi : ∑ i, xi i = 0) :
    normalCutoffSymbol chi Phi xi = Phi xi := by
  simp [normalCutoffSymbol, hxi, hchi]

/-- The canonical gauge lift lands exactly on the zero-sum hyperplane. -/
theorem rsZeroSumLift_sum {n : ℕ} (xi : Fin n -> ℝ) :
    ∑ j : Fin (n + 1), rsZeroSumLift xi j = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp [rsZeroSumLift]

/-- Normal cutoff does not change the gauge-fixed Fourier test. -/
theorem rsGaugeTest_normalCutoffSymbol {n : ℕ}
    (chi : ℝ -> ℂ) (Phi : (Fin (n + 1) -> ℝ) -> ℂ)
    (hchi : chi 0 = 1) (x : Fin (n + 1) -> ℂ) :
    rsGaugeTest (normalCutoffSymbol chi Phi) x = rsGaugeTest Phi x := by
  unfold rsGaugeTest
  apply integral_congr_ae
  filter_upwards [] with xi
  rw [normalCutoffSymbol_eq_of_sum_eq_zero chi Phi hchi
    (rsZeroSumLift_sum xi)]

/-- Normal cutoff does not change any disjoint-pair contraction. -/
theorem rsPairIntegral_normalCutoffSymbol {n q : ℕ}
    (chi : ℝ -> ℂ) (Phi : (Fin (n + 1) -> ℝ) -> ℂ)
    (hchi : chi 0 = 1)
    (pairing : (Fin q -> Fin (n + 1)) × (Fin q -> Fin (n + 1))) :
    rsPairIntegral (normalCutoffSymbol chi Phi) pairing =
      rsPairIntegral Phi pairing := by
  unfold rsPairIntegral
  apply integral_congr_ae
  filter_upwards [] with w
  rw [normalCutoffSymbol_eq_of_sum_eq_zero chi Phi hchi
    (rsPairVector_sum pairing w)]

/-- Consequently the full RS main term is invariant under normal cutoff. -/
theorem rsMainTerm_normalCutoffSymbol {n : ℕ}
    (chi : ℝ -> ℂ) (Phi : (Fin (n + 1) -> ℝ) -> ℂ)
    (hchi : chi 0 = 1) :
    rsMainTerm (normalCutoffSymbol chi Phi) = rsMainTerm Phi := by
  unfold rsMainTerm
  rw [normalCutoffSymbol_eq_of_sum_eq_zero chi Phi hchi (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro pairing hpairing
  exact rsPairIntegral_normalCutoffSymbol chi Phi hchi pairing

/-- Smoothness of the tangential test and the one-dimensional cutoff
combine to give smoothness of the compact extension. -/
theorem normalCutoffSymbol_contDiff {k : ℕ} {m : ℕ∞}
    (chi : ℝ -> ℂ) (Phi : (Fin k -> ℝ) -> ℂ)
    (hchi : ContDiff ℝ m chi) (hPhi : ContDiff ℝ m Phi) :
    ContDiff ℝ m (normalCutoffSymbol chi Phi) := by
  unfold normalCutoffSymbol
  fun_prop

/-- Abstract closed support bound for the normal-cutoff construction.

The tangential estimate is allowed one copy of the normal displacement.
This is the exact form produced by closing the cyclic polygon. -/
theorem normalCutoffSymbol_tsupport_subset {k : ℕ}
    (chi : ℝ -> ℂ) (Phi : (Fin k -> ℝ) -> ℂ) (A eps : ℝ)
    (hchi : ∀ s, chi s ≠ 0 -> |s| ≤ eps)
    (hPhi : ∀ xi, Phi xi ≠ 0 ->
      ∑ i : Fin k, |xi i| ≤ A + |∑ i : Fin k, xi i|) :
    tsupport (normalCutoffSymbol chi Phi) ⊆
      {xi | ∑ i : Fin k, |xi i| ≤ A + eps} := by
  change closure (Function.support (normalCutoffSymbol chi Phi)) ⊆ _
  apply closure_minimal
  · intro xi hxi
    have hprod : chi (∑ i : Fin k, xi i) * Phi xi ≠ 0 := by
      simpa only [Function.mem_support, normalCutoffSymbol] using hxi
    have hc : chi (∑ i : Fin k, xi i) ≠ 0 := by
      intro hz
      apply hprod
      rw [hz, zero_mul]
    have hp : Phi xi ≠ 0 := by
      intro hz
      apply hprod
      rw [hz, mul_zero]
    have ht := hPhi xi hp
    have hn := hchi (∑ i : Fin k, xi i) hc
    exact ht.trans (by simpa [add_comm] using add_le_add_left hn A)
  · exact isClosed_le (by fun_prop) (by fun_prop)

/-- A strict numerical margin converts the closed support bound into the
strict total Fourier support required by RS Theorem 3.1. -/
theorem normalCutoffSymbol_strictSupport {k : ℕ}
    (chi : ℝ -> ℂ) (Phi : (Fin k -> ℝ) -> ℂ) (A eps : ℝ)
    (hchi : ∀ s, chi s ≠ 0 -> |s| ≤ eps)
    (hPhi : ∀ xi, Phi xi ≠ 0 ->
      ∑ i : Fin k, |xi i| ≤ A + |∑ i : Fin k, xi i|)
    (hmargin : A + eps < 2) :
    tsupport (normalCutoffSymbol chi Phi) ⊆
      {xi | ∑ i : Fin k, |xi i| < 2} := by
  intro xi hxi
  exact lt_of_le_of_lt
    (normalCutoffSymbol_tsupport_subset chi Phi A eps hchi hPhi hxi)
    hmargin

/-- The quartic cyclic symbol, capped in the unused normal direction,
satisfies the strict RS support condition whenever the four-bandwidth budget
and cutoff radius leave a positive margin below two. -/
theorem normalCutoffWeightedCyclicSymbol_k4_strictSupport
    (mu a b eps : ℝ) (r : ℝ -> ℝ) (chi : ℝ -> ℂ)
    (hmu : 0 < mu)
    (hr : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (hchi : ∀ s, chi s ≠ 0 -> |s| ≤ eps)
    (hmargin : 4 * mu * (b - a) + eps < 2) :
    tsupport
        (normalCutoffSymbol chi (weightedCyclicSymbol (k := 4) mu r)) ⊆
      {xi | ∑ i : Fin 4, |xi i| < 2} := by
  exact normalCutoffSymbol_strictSupport
    chi (weightedCyclicSymbol (k := 4) mu r)
    (4 * mu * (b - a)) eps hchi
    (weightedCyclicSymbol_k4_l1_bound mu a b r hmu hr) hmargin

/-- There is a normalized smooth cutoff in every positive normal radius. -/
theorem exists_smooth_normalCutoff (eps : ℝ) (heps : 0 < eps) :
    ∃ chi : ℝ -> ℂ,
      chi 0 = 1 ∧ ContDiff ℝ ∞ chi ∧
        ∀ s, chi s ≠ 0 -> |s| ≤ eps := by
  obtain ⟨f, hsupport, _hcompact, hsmooth, _hrange, hzero⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (Metric.ball_mem_nhds (0 : ℝ) heps)
  refine ⟨Complex.ofRealCLM ∘ f, ?_, ?_, ?_⟩
  · simp [hzero]
  · exact Complex.ofRealCLM.contDiff.comp hsmooth
  · intro s hs
    have hfs : f s ≠ 0 := by
      intro hz
      apply hs
      simp [Function.comp_apply, hz]
    have hball := hsupport (subset_tsupport f hfs)
    have hdist : dist s 0 < eps := Metric.mem_ball.mp hball
    have habs : |s| < eps := by
      simpa [Real.dist_eq] using hdist
    exact habs.le

/-- Smooth compactly supported profiles produce a smooth cyclic symbol
in every positive degree.  The factor at cyclic position zero supplies one
compact integration domain independently of all frequency parameters. -/
theorem weightedCyclicSymbol_contDiff
    {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (r : ℝ -> ℝ)
    (hrc : HasCompactSupport r) (hr : ContDiff ℝ 1 r) :
    ContDiff ℝ 1 (weightedCyclicSymbol (k := k) mu r) := by
  let j0 : Fin k := ⟨0, hk⟩
  let g : (Fin k -> ℝ) -> ℝ -> ℝ := fun xi y =>
    ∏ j : Fin k, r (-y + cyclicPartialSum xi j / mu)
  let K : Set ℝ := -tsupport r
  have hK : IsCompact K := by
    dsimp only [K]
    exact hrc.isCompact.neg
  have hgs :
      ∀ xi : Fin k -> ℝ, ∀ y : ℝ,
        xi ∈ (Set.univ : Set (Fin k -> ℝ)) -> y ∉ K -> g xi y = 0 := by
    intro xi y _hy hyK
    have hneg : -y ∉ tsupport r := by
      intro h
      apply hyK
      dsimp only [K]
      simpa using (Set.neg_mem_neg.mpr h)
    dsimp only [g]
    apply Finset.prod_eq_zero (Finset.mem_univ j0)
    have hpartial : cyclicPartialSum xi j0 = 0 := by
      simp [cyclicPartialSum, j0]
    rw [hpartial, zero_div, add_zero]
    exact image_eq_zero_of_notMem_tsupport hneg
  have hg : ContDiff ℝ 1 ↿g := by
    change ContDiff ℝ 1 (fun q : (Fin k -> ℝ) × ℝ =>
      ∏ j : Fin k, r (-q.2 + cyclicPartialSum q.1 j / mu))
    simp only [cyclicPartialSum]
    fun_prop
  have hconv :=
    MeasureTheory.contDiffOn_convolution_right_with_param
      (f := fun _x : ℝ => (1 : ℝ)) (g := g)
      (s := Set.univ) (k := K) (μ := volume)
      (ContinuousLinearMap.mul ℝ ℝ)
      isOpen_univ hK hgs (locallyIntegrable_const (1 : ℝ)) hg.contDiffOn
  have hconv' :
      ContDiff ℝ 1 (fun q : (Fin k -> ℝ) × ℝ =>
        ((fun _x : ℝ => (1 : ℝ)) ⋆[
          ContinuousLinearMap.mul ℝ ℝ, volume] g q.1) q.2) := by
    rw [← contDiffOn_univ]
    simpa using hconv
  have heval :
      ContDiff ℝ 1 (fun xi : Fin k -> ℝ =>
        ((fun _x : ℝ => (1 : ℝ)) ⋆[
          ContinuousLinearMap.mul ℝ ℝ, volume] g xi) 0) := by
    simpa [Function.comp_def] using
      hconv'.comp
        (by fun_prop :
          ContDiff ℝ 1 (fun xi : Fin k -> ℝ => (xi, (0 : ℝ))))
  have hintegral :
      ContDiff ℝ 1 (fun xi : Fin k -> ℝ =>
        ∫ x : ℝ, ∏ j : Fin k,
          r (x + cyclicPartialSum xi j / mu)) := by
    simpa [MeasureTheory.convolution_def, g] using heval
  have hreal :
      ContDiff ℝ 1 (fun xi : Fin k -> ℝ =>
        mu * ∫ x : ℝ, ∏ j : Fin k,
          r (x + cyclicPartialSum xi j / mu)) :=
    contDiff_const.mul hintegral
  change ContDiff ℝ 1 (fun xi : Fin k -> ℝ =>
    ((mu * ∫ x : ℝ, ∏ j : Fin k,
      r (x + cyclicPartialSum xi j / mu) : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp hreal

/-- In degree one the total-frequency coordinate is the only
coordinate, so a normal cutoff alone gives the strict RS support bound. -/
theorem normalCutoffWeightedCyclicSymbol_k1_strictSupport
    (mu eps : ℝ) (r : ℝ -> ℝ) (chi : ℝ -> ℂ)
    (hchi : ∀ s, chi s ≠ 0 -> |s| ≤ eps)
    (heps : eps < 2) :
    tsupport
        (normalCutoffSymbol chi
          (weightedCyclicSymbol (k := 1) mu r)) ⊆
      {xi | ∑ i : Fin 1, |xi i| < 2} := by
  apply normalCutoffSymbol_strictSupport
    chi (weightedCyclicSymbol (k := 1) mu r) 0 eps hchi
  · intro xi _hxi
    simp
  · linarith

/-- Every smooth compactly supported profile supplies an admissible
degree-one RS test; no tangential bandwidth budget is needed in this
degree. -/
theorem exists_frozenLinearRSTest
    (mu : ℝ) (r : ℝ -> ℝ)
    (hrc : HasCompactSupport r) (hrSmooth : ContDiff ℝ 1 r) :
    ∃ Phi : (Fin 1 -> ℝ) -> ℂ,
      ContDiff ℝ 1 Phi ∧
      tsupport Phi ⊆ {xi | ∑ i : Fin 1, |xi i| < 2} ∧
      (∀ x : Fin 1 -> ℂ,
        rsGaugeTest Phi x =
          rsGaugeTest
            (weightedCyclicSymbol (k := 1) mu r) x) ∧
      rsMainTerm Phi =
        rsMainTerm (weightedCyclicSymbol (k := 1) mu r) := by
  obtain ⟨chi, hchi0, hchiSmooth, hchiSupport⟩ :=
    exists_smooth_normalCutoff (1 : ℝ) (by norm_num)
  refine ⟨normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 1) mu r), ?_, ?_, ?_, ?_⟩
  · apply normalCutoffSymbol_contDiff
    · exact hchiSmooth.of_le (by norm_num)
    · exact weightedCyclicSymbol_contDiff
        (k := 1) (by norm_num) mu r hrc hrSmooth
  · exact normalCutoffWeightedCyclicSymbol_k1_strictSupport
      mu 1 r chi hchiSupport (by norm_num)
  · intro x
    exact rsGaugeTest_normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 1) mu r) hchi0 x
  · exact rsMainTerm_normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 1) mu r) hchi0

/-- RS Theorem 3.1 applies directly to every fixed smooth
degree-one cyclic profile after the normal cutoff is eliminated from both
the tuple sum and the main term. -/
theorem RS1996ZetaInputs.frozenLinear
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (mu : ℝ) (r : ℝ -> ℝ)
    (hrc : HasCompactSupport r) (hrSmooth : ContDiff ℝ 1 r)
    (g : Fin 1 -> ℝ -> ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T ≥ T0,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := 1) mu r) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 1) mu r) T rho) -
        rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
          rsMainTerm
            (weightedCyclicSymbol (k := 1) mu r)‖ ≤ C * T := by
  obtain ⟨Phi, hPhiSmooth, hPhiSupport, hGauge, hMain⟩ :=
    exists_frozenLinearRSTest mu r hrc hrSmooth
  obtain ⟨C, T0, hC, hT0, hRS⟩ :=
    hrs.theorem31 0 g Phi hg hPhiSmooth hPhiSupport
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT
  obtain ⟨hSummable, hBound⟩ := hRS T hT
  have hterm (rho : Fin 1 -> Z.carrier) :
      rsZeroTupleTerm Z g Phi T rho =
        rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 1) mu r) T rho := by
    unfold rsZeroTupleTerm
    rw [hGauge]
  refine ⟨hSummable.congr hterm, ?_⟩
  simpa only [tsum_congr hterm, hMain] using hBound

/-- A nonzero degree-two cyclic symbol has at most two
bandwidths of tangential variation, plus its normal displacement. -/
theorem weightedCyclicSymbol_k2_l1_bound
    (mu a b : ℝ) (r : ℝ -> ℝ) (hmu : 0 < mu)
    (hr : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (xi : Fin 2 -> ℝ)
    (hPhi : weightedCyclicSymbol (k := 2) mu r xi ≠ 0) :
    ∑ i : Fin 2, |xi i| ≤
      2 * mu * (b - a) + |∑ i : Fin 2, xi i| := by
  let I : ℝ -> ℝ := fun x =>
    ∏ j : Fin 2, r (x + cyclicPartialSum xi j / mu)
  have hint : (∫ x : ℝ, I x) ≠ 0 := by
    intro hz
    apply hPhi
    have hz' :
        (∫ x : ℝ,
          ∏ j : Fin 2, r (x + cyclicPartialSum xi j / mu)) = 0 := by
      simpa only [I] using hz
    simp only [weightedCyclicSymbol, hz', mul_zero, Complex.ofReal_zero]
  have hex : ∃ x : ℝ, I x ≠ 0 := by
    by_contra hx
    push_neg at hx
    apply hint
    calc
      (∫ x : ℝ, I x) = ∫ _x : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hx x
      _ = 0 := by simp
  rcases hex with ⟨x, hx⟩
  have hfactor (j : Fin 2) :
      r (x + cyclicPartialSum xi j / mu) ≠ 0 := by
    intro h
    apply hx
    dsimp only [I]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h
  have hcp1 : cyclicPartialSum xi (1 : Fin 2) = xi 0 := by
    rw [cyclicPartialSum,
      show Finset.filter (fun j : Fin 2 => j < (1 : Fin 2))
          Finset.univ = {0} by decide]
    simp
  have hr0 : r x ≠ 0 := by
    simpa [cyclicPartialSum] using hfactor (0 : Fin 2)
  have hr1 : r (x + xi 0 / mu) ≠ 0 := by
    simpa only [hcp1] using hfactor (1 : Fin 2)
  rcases hr x hr0 with ⟨hx0a, hx0b⟩
  rcases hr (x + xi 0 / mu) hr1 with ⟨hx1a, hx1b⟩
  have h0 : |xi 0| ≤ mu * (b - a) := by
    have hd := abs_sub_le_interval_width hx1a hx1b hx0a hx0b
    have heq :
        xi 0 = mu * ((x + xi 0 / mu) - x) := by
      field_simp [ne_of_gt hmu]
      ring
    rw [heq, abs_mul, abs_of_pos hmu]
    exact mul_le_mul_of_nonneg_left hd hmu.le
  have hsum :
      (∑ i : Fin 2, xi i) = xi 0 + xi 1 := by
    norm_num [Fin.sum_univ_succ]
  have hlastEq :
      xi 1 = (∑ i : Fin 2, xi i) - xi 0 := by
    linarith
  have hlast :
      |xi 1| ≤ |∑ i : Fin 2, xi i| + mu * (b - a) := by
    rw [hlastEq]
    calc
      |(∑ i : Fin 2, xi i) - xi 0| ≤
          |∑ i : Fin 2, xi i| + |xi 0| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le (∑ i : Fin 2, xi i) (-xi 0)
      _ ≤ |∑ i : Fin 2, xi i| + mu * (b - a) :=
        add_le_add (le_refl _) h0
  have habssum :
      (∑ i : Fin 2, |xi i|) = |xi 0| + |xi 1| := by
    norm_num [Fin.sum_univ_succ]
  rw [habssum]
  nlinarith

/-- The degree-two cyclic test meets strict RS support whenever its two
tangential bandwidths and the normal cutoff leave margin below two. -/
theorem normalCutoffWeightedCyclicSymbol_k2_strictSupport
    (mu a b eps : ℝ) (r : ℝ -> ℝ) (chi : ℝ -> ℂ)
    (hmu : 0 < mu)
    (hr : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (hchi : ∀ s, chi s ≠ 0 -> |s| ≤ eps)
    (hmargin : 2 * mu * (b - a) + eps < 2) :
    tsupport
        (normalCutoffSymbol chi
          (weightedCyclicSymbol (k := 2) mu r)) ⊆
      {xi | ∑ i : Fin 2, |xi i| < 2} := by
  exact normalCutoffSymbol_strictSupport
    chi (weightedCyclicSymbol (k := 2) mu r)
    (2 * mu * (b - a)) eps hchi
    (weightedCyclicSymbol_k2_l1_bound mu a b r hmu hr) hmargin

/-- Every smooth degree-two cyclic profile satisfying the two-bandwidth
budget has an admissible compact RS extension. -/
theorem exists_frozenQuadraticRSTest
    (mu a b eps : ℝ) (r : ℝ -> ℝ)
    (hmu : 0 < mu)
    (hrc : HasCompactSupport r) (hrSmooth : ContDiff ℝ 1 r)
    (hrSupport : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (heps : 0 < eps)
    (hmargin : 2 * mu * (b - a) + eps < 2) :
    ∃ Phi : (Fin 2 -> ℝ) -> ℂ,
      ContDiff ℝ 1 Phi ∧
      tsupport Phi ⊆ {xi | ∑ i : Fin 2, |xi i| < 2} ∧
      (∀ x : Fin 2 -> ℂ,
        rsGaugeTest Phi x =
          rsGaugeTest
            (weightedCyclicSymbol (k := 2) mu r) x) ∧
      rsMainTerm Phi =
        rsMainTerm (weightedCyclicSymbol (k := 2) mu r) := by
  obtain ⟨chi, hchi0, hchiSmooth, hchiSupport⟩ :=
    exists_smooth_normalCutoff eps heps
  refine ⟨normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 2) mu r), ?_, ?_, ?_, ?_⟩
  · apply normalCutoffSymbol_contDiff
    · exact hchiSmooth.of_le (by norm_num)
    · exact weightedCyclicSymbol_contDiff
        (k := 2) (by norm_num) mu r hrc hrSmooth
  · exact normalCutoffWeightedCyclicSymbol_k2_strictSupport
      mu a b eps r chi hmu hrSupport hchiSupport hmargin
  · intro x
    exact rsGaugeTest_normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 2) mu r) hchi0 x
  · exact rsMainTerm_normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 2) mu r) hchi0

/-- RS Theorem 3.1 applies directly to every fixed admissible degree-two
cyclic profile. -/
theorem RS1996ZetaInputs.frozenQuadratic
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (mu a b eps : ℝ) (r : ℝ -> ℝ)
    (hmu : 0 < mu)
    (hrc : HasCompactSupport r) (hrSmooth : ContDiff ℝ 1 r)
    (hrSupport : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (heps : 0 < eps)
    (hmargin : 2 * mu * (b - a) + eps < 2)
    (g : Fin 2 -> ℝ -> ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T ≥ T0,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := 2) mu r) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 2) mu r) T rho) -
        rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
          rsMainTerm
            (weightedCyclicSymbol (k := 2) mu r)‖ ≤ C * T := by
  obtain ⟨Phi, hPhiSmooth, hPhiSupport, hGauge, hMain⟩ :=
    exists_frozenQuadraticRSTest
      mu a b eps r hmu hrc hrSmooth hrSupport heps hmargin
  obtain ⟨C, T0, hC, hT0, hRS⟩ :=
    hrs.theorem31 1 g Phi hg hPhiSmooth hPhiSupport
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT
  obtain ⟨hSummable, hBound⟩ := hRS T hT
  have hterm (rho : Fin 2 -> Z.carrier) :
      rsZeroTupleTerm Z g Phi T rho =
        rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 2) mu r) T rho := by
    unfold rsZeroTupleTerm
    rw [hGauge]
  refine ⟨hSummable.congr hterm, ?_⟩
  simpa only [tsum_congr hterm, hMain] using hBound

/-- A nonzero degree-three cyclic symbol has at most three
bandwidths of tangential variation, plus its normal displacement. -/
theorem weightedCyclicSymbol_k3_l1_bound
    (mu a b : ℝ) (r : ℝ -> ℝ) (hmu : 0 < mu)
    (hr : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (xi : Fin 3 -> ℝ)
    (hPhi : weightedCyclicSymbol (k := 3) mu r xi ≠ 0) :
    ∑ i : Fin 3, |xi i| ≤
      3 * mu * (b - a) + |∑ i : Fin 3, xi i| := by
  let I : ℝ -> ℝ := fun x =>
    ∏ j : Fin 3, r (x + cyclicPartialSum xi j / mu)
  have hint : (∫ x : ℝ, I x) ≠ 0 := by
    intro hz
    apply hPhi
    simp [weightedCyclicSymbol, I, hz]
  have hex : ∃ x : ℝ, I x ≠ 0 := by
    by_contra hx
    push_neg at hx
    apply hint
    calc
      (∫ x : ℝ, I x) = ∫ _x : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hx x
      _ = 0 := by simp
  rcases hex with ⟨x, hx⟩
  have hfactor (j : Fin 3) :
      r (x + cyclicPartialSum xi j / mu) ≠ 0 := by
    intro h
    apply hx
    dsimp only [I]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h
  have hcp1 : cyclicPartialSum xi (1 : Fin 3) = xi 0 := by
    rw [cyclicPartialSum,
      show Finset.filter (fun j : Fin 3 => j < (1 : Fin 3))
          Finset.univ = {0} by decide]
    simp
  have hcp2 : cyclicPartialSum xi (2 : Fin 3) = xi 0 + xi 1 := by
    rw [cyclicPartialSum,
      show Finset.filter (fun j : Fin 3 => j < (2 : Fin 3))
          Finset.univ = {0, 1} by decide]
    simp
  have hr0 : r x ≠ 0 := by
    simpa [cyclicPartialSum] using hfactor (0 : Fin 3)
  have hr1 : r (x + xi 0 / mu) ≠ 0 := by
    simpa only [hcp1] using hfactor (1 : Fin 3)
  have hr2 : r (x + (xi 0 + xi 1) / mu) ≠ 0 := by
    simpa only [hcp2] using hfactor (2 : Fin 3)
  rcases hr x hr0 with ⟨hx0a, hx0b⟩
  rcases hr (x + xi 0 / mu) hr1 with ⟨hx1a, hx1b⟩
  rcases hr (x + (xi 0 + xi 1) / mu) hr2 with ⟨hx2a, hx2b⟩
  have h0 : |xi 0| ≤ mu * (b - a) := by
    have hd := abs_sub_le_interval_width hx1a hx1b hx0a hx0b
    have heq :
        xi 0 = mu * ((x + xi 0 / mu) - x) := by
      field_simp [ne_of_gt hmu]
      ring
    rw [heq, abs_mul, abs_of_pos hmu]
    exact mul_le_mul_of_nonneg_left hd hmu.le
  have h1 : |xi 1| ≤ mu * (b - a) := by
    have hd := abs_sub_le_interval_width hx2a hx2b hx1a hx1b
    have heq :
        xi 1 = mu *
          ((x + (xi 0 + xi 1) / mu) - (x + xi 0 / mu)) := by
      field_simp [ne_of_gt hmu]
      ring
    rw [heq, abs_mul, abs_of_pos hmu]
    exact mul_le_mul_of_nonneg_left hd hmu.le
  have hcycle : |xi 0 + xi 1| ≤ mu * (b - a) := by
    have hd := abs_sub_le_interval_width hx2a hx2b hx0a hx0b
    have heq :
        xi 0 + xi 1 =
          mu * ((x + (xi 0 + xi 1) / mu) - x) := by
      field_simp [ne_of_gt hmu]
      ring
    rw [heq, abs_mul, abs_of_pos hmu]
    exact mul_le_mul_of_nonneg_left hd hmu.le
  have hsum :
      (∑ i : Fin 3, xi i) = xi 0 + xi 1 + xi 2 := by
    norm_num [Fin.sum_univ_succ]
    ring
  have hlastEq :
      xi 2 = (∑ i : Fin 3, xi i) - (xi 0 + xi 1) := by
    linarith
  have hlast :
      |xi 2| ≤ |∑ i : Fin 3, xi i| + mu * (b - a) := by
    rw [hlastEq]
    calc
      |(∑ i : Fin 3, xi i) - (xi 0 + xi 1)| ≤
          |∑ i : Fin 3, xi i| + |xi 0 + xi 1| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le (∑ i : Fin 3, xi i) (-(xi 0 + xi 1))
      _ ≤ |∑ i : Fin 3, xi i| + mu * (b - a) :=
        add_le_add (le_refl _) hcycle
  have habssum :
      (∑ i : Fin 3, |xi i|) =
        |xi 0| + |xi 1| + |xi 2| := by
    norm_num [Fin.sum_univ_succ]
    ring
  rw [habssum]
  nlinarith

/-- The degree-three cyclic test meets strict RS support whenever its three
tangential bandwidths and the normal cutoff leave margin below two. -/
theorem normalCutoffWeightedCyclicSymbol_k3_strictSupport
    (mu a b eps : ℝ) (r : ℝ -> ℝ) (chi : ℝ -> ℂ)
    (hmu : 0 < mu)
    (hr : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (hchi : ∀ s, chi s ≠ 0 -> |s| ≤ eps)
    (hmargin : 3 * mu * (b - a) + eps < 2) :
    tsupport
        (normalCutoffSymbol chi
          (weightedCyclicSymbol (k := 3) mu r)) ⊆
      {xi | ∑ i : Fin 3, |xi i| < 2} := by
  exact normalCutoffSymbol_strictSupport
    chi (weightedCyclicSymbol (k := 3) mu r)
    (3 * mu * (b - a)) eps hchi
    (weightedCyclicSymbol_k3_l1_bound mu a b r hmu hr) hmargin

/-- Every smooth degree-three cyclic profile satisfying the three-bandwidth
budget has an admissible compact RS extension. -/
theorem exists_frozenCubicRSTest
    (mu a b eps : ℝ) (r : ℝ -> ℝ)
    (hmu : 0 < mu)
    (hrc : HasCompactSupport r) (hrSmooth : ContDiff ℝ 1 r)
    (hrSupport : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (heps : 0 < eps)
    (hmargin : 3 * mu * (b - a) + eps < 2) :
    ∃ Phi : (Fin 3 -> ℝ) -> ℂ,
      ContDiff ℝ 1 Phi ∧
      tsupport Phi ⊆ {xi | ∑ i : Fin 3, |xi i| < 2} ∧
      (∀ x : Fin 3 -> ℂ,
        rsGaugeTest Phi x =
          rsGaugeTest
            (weightedCyclicSymbol (k := 3) mu r) x) ∧
      rsMainTerm Phi =
        rsMainTerm (weightedCyclicSymbol (k := 3) mu r) := by
  obtain ⟨chi, hchi0, hchiSmooth, hchiSupport⟩ :=
    exists_smooth_normalCutoff eps heps
  refine ⟨normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 3) mu r), ?_, ?_, ?_, ?_⟩
  · apply normalCutoffSymbol_contDiff
    · exact hchiSmooth.of_le (by norm_num)
    · exact weightedCyclicSymbol_contDiff
        (k := 3) (by norm_num) mu r hrc hrSmooth
  · exact normalCutoffWeightedCyclicSymbol_k3_strictSupport
      mu a b eps r chi hmu hrSupport hchiSupport hmargin
  · intro x
    exact rsGaugeTest_normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 3) mu r) hchi0 x
  · exact rsMainTerm_normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 3) mu r) hchi0

/-- RS Theorem 3.1 applies directly to every fixed admissible degree-three
cyclic profile. -/
theorem RS1996ZetaInputs.frozenCubic
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (mu a b eps : ℝ) (r : ℝ -> ℝ)
    (hmu : 0 < mu)
    (hrc : HasCompactSupport r) (hrSmooth : ContDiff ℝ 1 r)
    (hrSupport : ∀ x, r x ≠ 0 -> a ≤ x ∧ x ≤ b)
    (heps : 0 < eps)
    (hmargin : 3 * mu * (b - a) + eps < 2)
    (g : Fin 3 -> ℝ -> ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T ≥ T0,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := 3) mu r) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 3) mu r) T rho) -
        rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
          rsMainTerm
            (weightedCyclicSymbol (k := 3) mu r)‖ ≤ C * T := by
  obtain ⟨Phi, hPhiSmooth, hPhiSupport, hGauge, hMain⟩ :=
    exists_frozenCubicRSTest
      mu a b eps r hmu hrc hrSmooth hrSupport heps hmargin
  obtain ⟨C, T0, hC, hT0, hRS⟩ :=
    hrs.theorem31 2 g Phi hg hPhiSmooth hPhiSupport
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT
  obtain ⟨hSummable, hBound⟩ := hRS T hT
  have hterm (rho : Fin 3 -> Z.carrier) :
      rsZeroTupleTerm Z g Phi T rho =
        rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 3) mu r) T rho := by
    unfold rsZeroTupleTerm
    rw [hGauge]
  refine ⟨hSummable.congr hterm, ?_⟩
  simpa only [tsum_congr hterm, hMain] using hBound

/-- Smooth compactly supported profiles produce a smooth quartic cyclic
symbol.  The fixed factor at cyclic position zero supplies one compact
integration domain for every frequency parameter. -/
theorem weightedCyclicSymbol_k4_contDiff
    (mu : ℝ) (r : ℝ -> ℝ)
    (hrc : HasCompactSupport r) (hr : ContDiff ℝ 1 r) :
    ContDiff ℝ 1 (weightedCyclicSymbol (k := 4) mu r) := by
  let g : (Fin 4 -> ℝ) -> ℝ -> ℝ := fun xi y =>
    ∏ j : Fin 4, r (-y + cyclicPartialSum xi j / mu)
  let K : Set ℝ := -tsupport r
  have hK : IsCompact K := by
    dsimp only [K]
    exact hrc.isCompact.neg
  have hgs :
      ∀ xi : Fin 4 -> ℝ, ∀ y : ℝ,
        xi ∈ (Set.univ : Set (Fin 4 -> ℝ)) -> y ∉ K -> g xi y = 0 := by
    intro xi y _hy hyK
    have hneg : -y ∉ tsupport r := by
      intro h
      apply hyK
      dsimp only [K]
      simpa using (Set.neg_mem_neg.mpr h)
    dsimp only [g]
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4))
    simpa [cyclicPartialSum] using
      image_eq_zero_of_notMem_tsupport hneg
  have hg : ContDiff ℝ 1 ↿g := by
    change ContDiff ℝ 1 (fun q : (Fin 4 -> ℝ) × ℝ =>
      ∏ j : Fin 4, r (-q.2 + cyclicPartialSum q.1 j / mu))
    simp only [cyclicPartialSum]
    fun_prop
  have hconv :=
    MeasureTheory.contDiffOn_convolution_right_with_param
      (f := fun _x : ℝ => (1 : ℝ)) (g := g)
      (s := Set.univ) (k := K) (μ := volume)
      (ContinuousLinearMap.mul ℝ ℝ)
      isOpen_univ hK hgs (locallyIntegrable_const (1 : ℝ)) hg.contDiffOn
  have hconv' :
      ContDiff ℝ 1 (fun q : (Fin 4 -> ℝ) × ℝ =>
        ((fun _x : ℝ => (1 : ℝ)) ⋆[
          ContinuousLinearMap.mul ℝ ℝ, volume] g q.1) q.2) := by
    rw [← contDiffOn_univ]
    simpa using hconv
  have heval :
      ContDiff ℝ 1 (fun xi : Fin 4 -> ℝ =>
        ((fun _x : ℝ => (1 : ℝ)) ⋆[
          ContinuousLinearMap.mul ℝ ℝ, volume] g xi) 0) := by
    simpa [Function.comp_def] using
      hconv'.comp
        (by fun_prop :
          ContDiff ℝ 1 (fun xi : Fin 4 -> ℝ => (xi, (0 : ℝ))))
  have hintegral :
      ContDiff ℝ 1 (fun xi : Fin 4 -> ℝ =>
        ∫ x : ℝ, ∏ j : Fin 4,
          r (x + cyclicPartialSum xi j / mu)) := by
    simpa [MeasureTheory.convolution_def, g] using heval
  have hreal :
      ContDiff ℝ 1 (fun xi : Fin 4 -> ℝ =>
        mu * ∫ x : ℝ, ∏ j : Fin 4,
          r (x + cyclicPartialSum xi j / mu)) :=
    contDiff_const.mul hintegral
  change ContDiff ℝ 1 (fun xi : Fin 4 -> ℝ =>
    ((mu * ∫ x : ℝ, ∏ j : Fin 4,
      r (x + cyclicPartialSum xi j / mu) : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp hreal

/-- At the frozen bandwidth, the quartic cyclic test has a smooth compact
extension meeting the strict RS support threshold.  The extension agrees
with the original test in both places consumed by Theorem 3.1. -/
theorem exists_frozenQuarticRSTest
    (r : ℝ -> ℝ)
    (hr : ∀ x, r x ≠ 0 -> (0 : ℝ) ≤ x ∧ x ≤ 1)
    (hsmooth :
      ContDiff ℝ 1
        (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r)) :
    ∃ Phi : (Fin 4 -> ℝ) -> ℂ,
      ContDiff ℝ 1 Phi ∧
      tsupport Phi ⊆ {xi | ∑ i : Fin 4, |xi i| < 2} ∧
      (∀ x : Fin 4 -> ℂ,
        rsGaugeTest Phi x =
          rsGaugeTest
            (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) x) ∧
      rsMainTerm Phi =
        rsMainTerm
          (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) := by
  obtain ⟨chi, hchi0, hchiSmooth, hchiSupport⟩ :=
    exists_smooth_normalCutoff (1 / 10000 : ℝ) (by norm_num)
  refine ⟨normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r), ?_, ?_, ?_, ?_⟩
  · apply normalCutoffSymbol_contDiff
    · exact hchiSmooth.of_le (by norm_num)
    · exact hsmooth
  · exact normalCutoffWeightedCyclicSymbol_k4_strictSupport
      (4999 / 10000 : ℝ) 0 1 (1 / 10000 : ℝ) r chi
      (by norm_num) hr hchiSupport (by norm_num)
  · intro x
    exact rsGaugeTest_normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) hchi0 x
  · exact rsMainTerm_normalCutoffSymbol chi
      (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) hchi0

/-- Smooth compact support now discharges the last premise of the frozen
quartic test construction. -/
theorem exists_frozenQuarticRSTest_of_smoothCompact
    (r : ℝ -> ℝ)
    (hrc : HasCompactSupport r) (hrSmooth : ContDiff ℝ 1 r)
    (hrSupport : ∀ x, r x ≠ 0 -> (0 : ℝ) ≤ x ∧ x ≤ 1) :
    ∃ Phi : (Fin 4 -> ℝ) -> ℂ,
      ContDiff ℝ 1 Phi ∧
      tsupport Phi ⊆ {xi | ∑ i : Fin 4, |xi i| < 2} ∧
      (∀ x : Fin 4 -> ℂ,
        rsGaugeTest Phi x =
          rsGaugeTest
            (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) x) ∧
      rsMainTerm Phi =
        rsMainTerm
          (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) :=
  exists_frozenQuarticRSTest r hrSupport
    (weightedCyclicSymbol_k4_contDiff
      (4999 / 10000 : ℝ) r hrc hrSmooth)

/-- A literal smooth profile supported in the unit interval. -/
def unitIntervalBump : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The real function underlying the literal unit-interval bump. -/
def unitIntervalProfile : ℝ -> ℝ := fun x => unitIntervalBump x

theorem unitIntervalProfile_contDiff :
    ContDiff ℝ ∞ unitIntervalProfile := by
  change ContDiff ℝ ∞ (unitIntervalBump : ℝ -> ℝ)
  exact unitIntervalBump.contDiff

theorem unitIntervalProfile_hasCompactSupport :
    HasCompactSupport unitIntervalProfile := by
  change HasCompactSupport (unitIntervalBump : ℝ -> ℝ)
  exact unitIntervalBump.hasCompactSupport

theorem unitIntervalProfile_support
    (x : ℝ) (hx : unitIntervalProfile x ≠ 0) :
    (0 : ℝ) ≤ x ∧ x ≤ 1 := by
  change unitIntervalBump x ≠ 0 at hx
  have hxball0 :
      x ∈ Metric.ball (1 / 2 : ℝ) unitIntervalBump.rOut := by
    rw [← unitIntervalBump.support_eq]
    exact hx
  have hxball : x ∈ Metric.ball (1 / 2 : ℝ) (1 / 2 : ℝ) := by
    simpa [unitIntervalBump] using hxball0
  have habs : |x - 1 / 2| < (1 / 2 : ℝ) := by
    simpa [Real.dist_eq] using hxball
  rw [abs_lt] at habs
  constructor <;> linarith

/-- A completely explicit smooth quartic test at the frozen bandwidth,
with no remaining support or regularity premise. -/
theorem exists_unitInterval_frozenQuarticRSTest :
    ∃ Phi : (Fin 4 -> ℝ) -> ℂ,
      ContDiff ℝ 1 Phi ∧
      tsupport Phi ⊆ {xi | ∑ i : Fin 4, |xi i| < 2} ∧
      (∀ x : Fin 4 -> ℂ,
        rsGaugeTest Phi x =
          rsGaugeTest
            (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ)
              unitIntervalProfile) x) ∧
      rsMainTerm Phi =
        rsMainTerm
          (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ)
            unitIntervalProfile) := by
  apply exists_frozenQuarticRSTest_of_smoothCompact
  · exact unitIntervalProfile_hasCompactSupport
  · exact (unitIntervalProfile_contDiff).of_le (by norm_num)
  · exact unitIntervalProfile_support

/-- RS Theorem 3.1 now applies directly to the explicit frozen quartic
cyclic test.  The compact extension disappears from both the zero-tuple sum
and the displayed main term. -/
theorem RS1996ZetaInputs.unitIntervalQuartic
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (g : Fin 4 -> ℝ -> ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T ≥ T0,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ)
          unitIntervalProfile) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ)
            unitIntervalProfile) T rho) -
        rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
          rsMainTerm
            (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ)
              unitIntervalProfile)‖ ≤ C * T := by
  obtain ⟨Phi, hPhiSmooth, hPhiSupport, hGauge, hMain⟩ :=
    exists_unitInterval_frozenQuarticRSTest
  obtain ⟨C, T0, hC, hT0, hRS⟩ :=
    hrs.theorem31 3 g Phi hg hPhiSmooth hPhiSupport
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT
  obtain ⟨hSummable, hBound⟩ := hRS T hT
  have hterm (rho : Fin 4 -> Z.carrier) :
      rsZeroTupleTerm Z g Phi T rho =
        rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ)
            unitIntervalProfile) T rho := by
    unfold rsZeroTupleTerm
    rw [hGauge]
  refine ⟨hSummable.congr hterm, ?_⟩
  simpa only [tsum_congr hterm, hMain] using hBound

/-- RS Theorem 3.1 applies to every smooth profile in the unit interval at
the frozen bandwidth.  The compact extension is eliminated from both the
zero-tuple sum and the main term. -/
theorem RS1996ZetaInputs.frozenQuartic
    {Z : ZeroConfig} (hrs : RS1996ZetaInputs Z)
    (r : ℝ -> ℝ) (hrc : HasCompactSupport r)
    (hrSmooth : ContDiff ℝ 1 r)
    (hrSupport : ∀ x, r x ≠ 0 -> (0 : ℝ) ≤ x ∧ x ≤ 1)
    (g : Fin 4 -> ℝ -> ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T ≥ T0,
      Summable (rsZeroTupleTerm Z g
        (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) T) ∧
      ‖(∑' rho, rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) T rho) -
        rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
          rsMainTerm
            (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r)‖ ≤
        C * T := by
  obtain ⟨Phi, hPhiSmooth, hPhiSupport, hGauge, hMain⟩ :=
    exists_frozenQuarticRSTest_of_smoothCompact
      r hrc hrSmooth hrSupport
  obtain ⟨C, T0, hC, hT0, hRS⟩ :=
    hrs.theorem31 3 g Phi hg hPhiSmooth hPhiSupport
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT
  obtain ⟨hSummable, hBound⟩ := hRS T hT
  have hterm (rho : Fin 4 -> Z.carrier) :
      rsZeroTupleTerm Z g Phi T rho =
        rsZeroTupleTerm Z g
          (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ) r) T rho := by
    unfold rsZeroTupleTerm
    rw [hGauge]
  refine ⟨hSummable.congr hterm, ?_⟩
  simpa only [tsum_congr hterm, hMain] using hBound

/-- The complete multiplicity-weighted zero-tuple summand is unchanged. -/
theorem rsZeroTupleTerm_normalCutoffSymbol (Z : ZeroConfig) {n : ℕ}
    (g : Fin (n + 1) -> ℝ -> ℂ)
    (chi : ℝ -> ℂ) (Phi : (Fin (n + 1) -> ℝ) -> ℂ)
    (hchi : chi 0 = 1) (T : ℝ)
    (rho : Fin (n + 1) -> Z.carrier) :
    rsZeroTupleTerm Z g (normalCutoffSymbol chi Phi) T rho =
      rsZeroTupleTerm Z g Phi T rho := by
  unfold rsZeroTupleTerm
  rw [rsGaugeTest_normalCutoffSymbol chi Phi hchi]

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
