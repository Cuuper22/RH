/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSReduction
import Zeta23.Taper.Fourier
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Fourier evaluation of cyclic Rudnick--Sarnak tests

This module evaluates the gauge-fixed Fourier test of the weighted cyclic
symbol.  The degree-two identity is valid at arbitrary complex arguments;
in particular, it applies directly to zeta-zero ordinates without assuming
that they are real.
-/

open MeasureTheory Set Filter
open scoped BigOperators Convolution

noncomputable section

namespace RH.Zeta85.RSReduction

open Zeta23

/-- The degree-one cyclic test is just the zero-frequency Fourier transform. -/
theorem rsGaugeTest_weightedCyclicSymbol_one
    {mu : ℝ} (r : ℝ → ℝ) (x : Fin 1 → ℂ) :
    rsGaugeTest (n := 0) (weightedCyclicSymbol (k := 1) mu r) x =
      (mu : ℂ) * paperFT (fun u => (r u : ℂ)) 0 := by
  have hlift (xi : Fin 0 → ℝ) : rsZeroSumLift xi = 0 := by
    funext i
    have hi : i = Fin.last 0 := Fin.eq_zero i
    subst i
    unfold rsZeroSumLift
    rw [Fin.lastCases_last]
    simp
  unfold rsGaugeTest weightedCyclicSymbol cyclicPartialSum paperFT
  simp_rw [hlift]
  rw [MeasureTheory.Measure.volume_pi_eq_dirac]
  simp [integral_complex_ofReal]

private lemma integral_fin_one (f : (Fin 1 → ℝ) → ℂ) :
    (∫ xi : Fin 1 → ℝ, f xi) = ∫ t : ℝ, f (fun _ => t) := by
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hp := (volume_preserving_funUnique (Fin 1) ℝ).symm e
  have h := hp.integral_comp e.symm.measurableEmbedding f
  calc
    (∫ xi : Fin 1 → ℝ, f xi) = ∫ t : ℝ, f (e.symm t) := h.symm
    _ = ∫ t : ℝ, f (fun _ => t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      congr 1

private lemma lift_fin_one_zero (t : ℝ) :
    rsZeroSumLift (fun _ : Fin 1 => t) (0 : Fin 2) = t := by
  change Fin.lastCases (-∑ _i : Fin 1, t) (fun _i => t)
      (Fin.castSucc (0 : Fin 1)) = t
  rw [Fin.lastCases_castSucc]

private lemma lift_fin_one_one (t : ℝ) :
    rsZeroSumLift (fun _ : Fin 1 => t) (1 : Fin 2) = -t := by
  change Fin.lastCases (-∑ _i : Fin 1, t) (fun _i => t) (Fin.last 1) = -t
  rw [Fin.lastCases_last]
  simp

private lemma weighted_fin_two {mu : ℝ} (r : ℝ → ℝ) (t : ℝ) :
    weightedCyclicSymbol (k := 2) mu r
        (rsZeroSumLift (fun _ : Fin 1 => t)) =
      (mu : ℂ) * (Zeta23.Params.autocorr r (t / mu) : ℝ) := by
  have hpartial0 : cyclicPartialSum
      (rsZeroSumLift (fun _ : Fin 1 => t)) (0 : Fin 2) = 0 := by
    simp [cyclicPartialSum]
  have hpartial1 : cyclicPartialSum
      (rsZeroSumLift (fun _ : Fin 1 => t)) (1 : Fin 2) = t := by
    unfold cyclicPartialSum
    rw [show (Finset.univ.filter fun x : Fin 2 => x < (1 : Fin 2)) = {0} by
      ext i
      fin_cases i <;> simp]
    simp [lift_fin_one_zero]
  unfold weightedCyclicSymbol Zeta23.Params.autocorr
  norm_cast
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Fin.prod_univ_two]
  rw [hpartial0, hpartial1]
  simp

/-- Fourier transform of the autocorrelation at an arbitrary complex
argument.  Compact support makes every exponentially weighted integral
converge, so the usual real-frequency identity extends verbatim. -/
theorem paperFT_autocorr_complex {r : ℝ → ℝ}
    (heven : ∀ u, r (-u) = r u) (hcont : Continuous r)
    (hcompact : HasCompactSupport r) (z : ℂ) :
    paperFT (fun y => (Zeta23.Params.autocorr r y : ℂ)) z =
      paperFT (fun u => (r u : ℂ)) z ^ 2 := by
  let R : ℝ → ℂ := fun u => (r u : ℂ)
  let e : ℝ → ℂ := fun u => Complex.exp (Complex.I * z * (u : ℂ))
  let f : ℝ → ℂ := fun u => R u * e u
  have hRc : Continuous R := Complex.continuous_ofReal.comp hcont
  have hRs : HasCompactSupport R := hcompact.comp_left Complex.ofReal_zero
  have hec : Continuous e := by
    dsimp [e]
    fun_prop
  have hfc : Continuous f := hRc.mul hec
  have hfs : HasCompactSupport f := by
    apply hRs.mono
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu ⊢
    intro hzero
    apply hu
    simp [f, hzero]
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hfs
  have hconv (y : ℝ) :
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
        ((R ⋆[ContinuousLinearMap.mul ℂ ℂ] R) y) * e y := by
    unfold convolution
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [f, e]
    have hexp :
        Complex.exp (Complex.I * z * (u : ℂ)) *
            Complex.exp (Complex.I * z * ((y - u : ℝ) : ℂ)) =
          Complex.exp (Complex.I * z * (y : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [show R u * Complex.exp (Complex.I * z * (u : ℂ)) *
          (R (y - u) * Complex.exp (Complex.I * z * ((y - u : ℝ) : ℂ))) =
        (R u * R (y - u)) *
          (Complex.exp (Complex.I * z * (u : ℂ)) *
            Complex.exp (Complex.I * z * ((y - u : ℝ) : ℂ))) by ring,
      hexp]
  rw [Zeta23.Taper.ofReal_autocorr_eq_convolution heven]
  unfold paperFT
  calc
    (∫ y : ℝ, (R ⋆[ContinuousLinearMap.mul ℂ ℂ] R) y * e y) =
        ∫ y : ℝ, (f ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact (hconv y).symm
    _ = (∫ u : ℝ, f u) * ∫ u : ℝ, f u :=
      MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hfi hfi
    _ = paperFT (fun u => (r u : ℂ)) z ^ 2 := by
      simp only [paperFT, f, R, e, pow_two]

private lemma integral_scaled_paperFT (F : ℝ → ℂ) {mu : ℝ}
    (hmu : 0 < mu) (z : ℂ) :
    (∫ t : ℝ, (mu : ℂ) * F (t / mu) *
        Complex.exp (Complex.I * z * (t : ℂ))) =
      (mu : ℂ) ^ 2 * paperFT F ((mu : ℂ) * z) := by
  let g : ℝ → ℂ := fun y =>
    F y * Complex.exp (Complex.I * ((mu : ℂ) * z) * (y : ℂ))
  have hfun : (fun t : ℝ =>
      F (t / mu) * Complex.exp (Complex.I * z * (t : ℂ))) =
      fun t : ℝ => g (t / mu) := by
    funext t
    dsimp [g]
    congr 2
    push_cast
    field_simp [hmu.ne']
  rw [show (fun t : ℝ => (mu : ℂ) * F (t / mu) *
      Complex.exp (Complex.I * z * (t : ℂ))) =
      fun t => (mu : ℂ) *
        (F (t / mu) * Complex.exp (Complex.I * z * (t : ℂ))) by
      funext t
      ring]
  rw [integral_const_mul, hfun,
    MeasureTheory.Measure.integral_comp_div g mu, abs_of_pos hmu]
  simp only [Complex.real_smul, paperFT, g]
  ring

private lemma gauge_phase_fin_two (x : Fin 2 → ℂ) (t : ℝ) :
    (∑ j : Fin 2, x j *
      (rsZeroSumLift (fun _ : Fin 1 => t) j : ℂ)) =
      (x 0 - x 1) * (t : ℂ) := by
  rw [Fin.sum_univ_two, lift_fin_one_zero, lift_fin_one_one]
  push_cast
  ring

/-- Exact Fourier evaluation of the degree-two cyclic RS test at complex
arguments. -/
theorem rsGaugeTest_weightedCyclicSymbol_two
    {mu : ℝ} (hmu : 0 < mu) (r : ℝ → ℝ)
    (heven : ∀ u, r (-u) = r u) (hcont : Continuous r)
    (hcompact : HasCompactSupport r) (x : Fin 2 → ℂ) :
    rsGaugeTest (n := 1) (weightedCyclicSymbol (k := 2) mu r) x =
      (mu : ℂ) ^ 2 *
        paperFT (fun u => (r u : ℂ))
          ((mu : ℂ) * (2 * Real.pi : ℂ) * (x 1 - x 0)) ^ 2 := by
  let A : ℝ → ℂ := fun y => (Zeta23.Params.autocorr r y : ℂ)
  let z : ℂ := (2 * Real.pi : ℂ) * (x 1 - x 0)
  unfold rsGaugeTest
  rw [integral_fin_one]
  simp_rw [weighted_fin_two (mu := mu) r]
  conv_lhs =>
    enter [2, t]
    rw [gauge_phase_fin_two x t]
  change (∫ t : ℝ, (mu : ℂ) * A (t / mu) *
      Complex.exp (-2 * Real.pi * Complex.I *
        ((x 0 - x 1) * (t : ℂ)))) = _
  calc
    (∫ t : ℝ, (mu : ℂ) * A (t / mu) *
        Complex.exp (-2 * Real.pi * Complex.I *
          ((x 0 - x 1) * (t : ℂ)))) =
        ∫ t : ℝ, (mu : ℂ) * A (t / mu) *
          Complex.exp (Complex.I * z * (t : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      congr 2
      dsimp [z]
      push_cast
      ring
    _ = (mu : ℂ) ^ 2 * paperFT A ((mu : ℂ) * z) :=
      integral_scaled_paperFT A hmu z
    _ = (mu : ℂ) ^ 2 *
        paperFT (fun u => (r u : ℂ)) ((mu : ℂ) * z) ^ 2 := by
      rw [paperFT_autocorr_complex heven hcont hcompact]
    _ = (mu : ℂ) ^ 2 *
        paperFT (fun u => (r u : ℂ))
          ((mu : ℂ) * (2 * Real.pi : ℂ) * (x 1 - x 0)) ^ 2 := by
      dsimp [z]
      ring

/-! ## Degree three: simultaneous path-coordinate factorization -/

/-- Exact multivariate change of variables for an invertible real matrix
with positive determinant. -/
private lemma integral_linear_change {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hdet : 0 < M.det)
    (f : (Fin n → ℝ) → ℂ) :
    (∫ q : Fin n → ℝ, f q) =
      (M.det : ℂ) * ∫ y : Fin n → ℝ, f (Matrix.toLin' M y) := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' M
  have hLdet : LinearMap.det L = M.det := by
    simp [L]
  have hL : LinearMap.det L ≠ 0 := by
    rw [hLdet]
    exact hdet.ne'
  let eL : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    L.equivOfDetNeZero hL
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    eL.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = L := by
    rfl
  have hmap : Measure.map e volume =
      ENNReal.ofReal (abs (M.det)⁻¹) • volume := by
    rw [he]
    simpa only [hLdet] using
      (Real.map_linearMap_volume_pi_eq_smul_volume_pi hL)
  have hint := integral_map_equiv (μ := volume) e f
  rw [hmap, integral_smul_measure] at hint
  have hreal :
      (ENNReal.ofReal (abs (M.det)⁻¹)).toReal = (M.det)⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    · rw [abs_of_pos (inv_pos.mpr hdet)]
    · positivity
  rw [hreal, Complex.real_smul] at hint
  rw [he] at hint
  have hint' : (M.det : ℂ)⁻¹ * (∫ q : Fin n → ℝ, f q) =
      ∫ y : Fin n → ℝ, f (Matrix.toLin' M y) := by
    simpa [L] using hint
  calc
    (∫ q : Fin n → ℝ, f q) =
        (M.det : ℂ) * ((M.det : ℂ)⁻¹ *
          ∫ q : Fin n → ℝ, f q) := by
      field_simp [hdet.ne']
    _ = (M.det : ℂ) *
        ∫ y : Fin n → ℝ, f (Matrix.toLin' M y) := by
      rw [hint']

/-- Integrability is invariant under the same invertible linear change. -/
private lemma integrable_linear_change_iff {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hdet : M.det ≠ 0)
    (f : (Fin n → ℝ) → ℂ) :
    Integrable (fun y => f (Matrix.toLin' M y)) ↔ Integrable f := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' M
  have hLdet : LinearMap.det L = M.det := by
    simp [L]
  have hL : LinearMap.det L ≠ 0 := by
    simpa only [hLdet] using hdet
  let eL : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    L.equivOfDetNeZero hL
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    eL.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = L := by
    rfl
  have hmap : Measure.map e volume =
      ENNReal.ofReal (abs (M.det)⁻¹) • volume := by
    rw [he]
    simpa only [hLdet] using
      (Real.map_linearMap_volume_pi_eq_smul_volume_pi hL)
  have hc0 : ENNReal.ofReal (abs (M.det)⁻¹) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    positivity
  have hctop : ENNReal.ofReal (abs (M.det)⁻¹) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  calc
    Integrable (fun y => f (Matrix.toLin' M y)) =
        Integrable (f ∘ e) := by
      congr
    _ ↔ Integrable f (Measure.map e volume) :=
      (integrable_map_equiv e f).symm
    _ ↔ Integrable f
        (ENNReal.ofReal (abs (M.det)⁻¹) • volume) := by
      rw [hmap]
    _ ↔ Integrable f := integrable_smul_measure hc0 hctop

private def cycleMatrixThree (mu : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 0, 0], ![-mu, mu, 0], ![0, -mu, mu]]

private lemma cycleMatrixThree_apply (mu : ℝ) (y : Fin 3 → ℝ) :
    Matrix.toLin' (cycleMatrixThree mu) y =
      ![y 0, mu * (y 1 - y 0), mu * (y 2 - y 1)] := by
  funext i
  change Matrix.mulVec (cycleMatrixThree mu) y i = _
  fin_cases i <;>
    simp [cycleMatrixThree, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

private lemma cycleMatrixThree_det (mu : ℝ) :
    (cycleMatrixThree mu).det = mu ^ 2 := by
  rw [Matrix.det_fin_three]
  simp [cycleMatrixThree]
  ring

/-- The three Fourier frequencies obtained by orienting the cyclic path. -/
def cyclicFrequencyThree (mu : ℝ) (x : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(2 * Real.pi : ℂ) * (mu : ℂ) * (x 0 - x 2),
    (2 * Real.pi : ℂ) * (mu : ℂ) * (x 1 - x 0),
    (2 * Real.pi : ℂ) * (mu : ℂ) * (x 2 - x 1)]

private def cyclicSourceThree (mu : ℝ) (r : ℝ → ℝ)
    (x : Fin 3 → ℂ) (q : Fin 3 → ℝ) : ℂ :=
  (mu : ℂ) * (r (q 0) : ℂ) * (r (q 0 + q 1 / mu) : ℂ) *
    (r (q 0 + (q 1 + q 2) / mu) : ℂ) *
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
        ((x 0 - x 2) * (q 1 : ℂ) +
          (x 1 - x 2) * (q 2 : ℂ)))

private lemma cyclicSourceThree_comp_matrix {mu : ℝ} (hmu : 0 < mu)
    (r : ℝ → ℝ) (x : Fin 3 → ℂ) (y : Fin 3 → ℝ) :
    cyclicSourceThree mu r x (Matrix.toLin' (cycleMatrixThree mu) y) =
      (mu : ℂ) * ∏ j : Fin 3,
        (r (y j) : ℂ) * Complex.exp
          (Complex.I * cyclicFrequencyThree mu x j * (y j : ℂ)) := by
  rw [cycleMatrixThree_apply, Fin.prod_univ_three]
  simp only [cyclicSourceThree, cyclicFrequencyThree]
  simp
  have hy1 : y 0 + mu * (y 1 - y 0) / mu = y 1 := by
    field_simp [hmu.ne']
    ring
  have hy2 : y 0 +
      (mu * (y 1 - y 0) + mu * (y 2 - y 1)) / mu = y 2 := by
    field_simp [hmu.ne']
    ring
  rw [hy1, hy2]
  rw [show
      (mu : ℂ) *
        ((r (y 0) : ℂ) *
            Complex.exp (Complex.I * ((2 * Real.pi : ℂ) * (mu : ℂ) *
              (x 0 - x 2)) * (y 0 : ℂ)) *
          ((r (y 1) : ℂ) *
            Complex.exp (Complex.I * ((2 * Real.pi : ℂ) * (mu : ℂ) *
              (x 1 - x 0)) * (y 1 : ℂ))) *
          ((r (y 2) : ℂ) *
            Complex.exp (Complex.I * ((2 * Real.pi : ℂ) * (mu : ℂ) *
              (x 2 - x 1)) * (y 2 : ℂ)))) =
        (mu : ℂ) * (r (y 0) : ℂ) * (r (y 1) : ℂ) *
          (r (y 2) : ℂ) *
          (Complex.exp (Complex.I * ((2 * Real.pi : ℂ) * (mu : ℂ) *
              (x 0 - x 2)) * (y 0 : ℂ)) *
            Complex.exp (Complex.I * ((2 * Real.pi : ℂ) * (mu : ℂ) *
              (x 1 - x 0)) * (y 1 : ℂ)) *
            Complex.exp (Complex.I * ((2 * Real.pi : ℂ) * (mu : ℂ) *
              (x 2 - x 1)) * (y 2 : ℂ))) by
      ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

private lemma paperFTKernel_integrable {r : ℝ → ℝ}
    (hcont : Continuous r) (hcompact : HasCompactSupport r) (z : ℂ) :
    Integrable (fun y : ℝ =>
      (r y : ℂ) * Complex.exp (Complex.I * z * (y : ℂ))) := by
  have hc : Continuous (fun y : ℝ =>
      (r y : ℂ) * Complex.exp (Complex.I * z * (y : ℂ))) := by
    fun_prop
  have hs : HasCompactSupport (fun y : ℝ =>
      (r y : ℂ) * Complex.exp (Complex.I * z * (y : ℂ))) := by
    have hrs : HasCompactSupport (fun y : ℝ => (r y : ℂ)) :=
      hcompact.comp_left Complex.ofReal_zero
    apply hrs.mono
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro hr
    apply hy
    simp [hr]
  exact hc.integrable_of_hasCompactSupport hs

private lemma cyclicSourceThree_integrable {mu : ℝ} (hmu : 0 < mu)
    {r : ℝ → ℝ} (hcont : Continuous r)
    (hcompact : HasCompactSupport r) (x : Fin 3 → ℂ) :
    Integrable (cyclicSourceThree mu r x) := by
  let f : Fin 3 → ℝ → ℂ := fun j y =>
    (r y : ℂ) * Complex.exp
      (Complex.I * cyclicFrequencyThree mu x j * (y : ℂ))
  have hf (j : Fin 3) : Integrable (f j) :=
    paperFTKernel_integrable hcont hcompact _
  have hprod : Integrable (fun y : Fin 3 → ℝ => ∏ j, f j (y j)) :=
    Integrable.fintype_prod hf
  have htrans : Integrable (fun y : Fin 3 → ℝ =>
      cyclicSourceThree mu r x
        (Matrix.toLin' (cycleMatrixThree mu) y)) := by
    have hm := hprod.const_mul (mu : ℂ)
    apply hm.congr
    filter_upwards [] with y
    exact (cyclicSourceThree_comp_matrix hmu r x y).symm
  exact (integrable_linear_change_iff (cycleMatrixThree mu)
    (by rw [cycleMatrixThree_det]; positivity)
    (cyclicSourceThree mu r x)).mp htrans

private lemma cyclicSourceThree_integral {mu : ℝ} (hmu : 0 < mu)
    (r : ℝ → ℝ) (x : Fin 3 → ℂ) :
    (∫ q : Fin 3 → ℝ, cyclicSourceThree mu r x q) =
      (mu : ℂ) ^ 3 * ∏ j : Fin 3,
        paperFT (fun y => (r y : ℂ)) (cyclicFrequencyThree mu x j) := by
  calc
    (∫ q : Fin 3 → ℝ, cyclicSourceThree mu r x q) =
        ((cycleMatrixThree mu).det : ℂ) *
          ∫ y : Fin 3 → ℝ, cyclicSourceThree mu r x
            (Matrix.toLin' (cycleMatrixThree mu) y) :=
      integral_linear_change (cycleMatrixThree mu)
        (by rw [cycleMatrixThree_det]; positivity) _
    _ = (mu : ℂ) ^ 2 *
        ∫ y : Fin 3 → ℝ, (mu : ℂ) * ∏ j : Fin 3,
          (r (y j) : ℂ) * Complex.exp
            (Complex.I * cyclicFrequencyThree mu x j * (y j : ℂ)) := by
      rw [cycleMatrixThree_det]
      push_cast
      congr 2
      funext y
      exact cyclicSourceThree_comp_matrix hmu r x y
    _ = (mu : ℂ) ^ 3 * ∏ j : Fin 3,
        paperFT (fun y => (r y : ℂ))
          (cyclicFrequencyThree mu x j) := by
      rw [integral_const_mul]
      rw [MeasureTheory.integral_fintype_prod_volume_eq_prod
        (fun j : Fin 3 => fun y : ℝ =>
          (r y : ℂ) * Complex.exp
            (Complex.I * cyclicFrequencyThree mu x j * (y : ℂ)))]
      simp only [paperFT]
      ring

private lemma lift_fin_two_zero (xi : Fin 2 → ℝ) :
    rsZeroSumLift xi (0 : Fin 3) = xi 0 := by
  change Fin.lastCases (-∑ i : Fin 2, xi i) (fun i => xi i)
    (Fin.castSucc (0 : Fin 2)) = xi 0
  rw [Fin.lastCases_castSucc]

private lemma lift_fin_two_one (xi : Fin 2 → ℝ) :
    rsZeroSumLift xi (1 : Fin 3) = xi 1 := by
  change Fin.lastCases (-∑ i : Fin 2, xi i) (fun i => xi i)
    (Fin.castSucc (1 : Fin 2)) = xi 1
  rw [Fin.lastCases_castSucc]

private lemma lift_fin_two_two (xi : Fin 2 → ℝ) :
    rsZeroSumLift xi (2 : Fin 3) = -(xi 0 + xi 1) := by
  change Fin.lastCases (-∑ i : Fin 2, xi i) (fun i => xi i)
    (Fin.last 2) = -(xi 0 + xi 1)
  rw [Fin.lastCases_last, Fin.sum_univ_two]

private lemma cyclic_partial_fin_three_zero (xi : Fin 2 → ℝ) :
    cyclicPartialSum (rsZeroSumLift xi) (0 : Fin 3) = 0 := by
  simp [cyclicPartialSum]

private lemma cyclic_partial_fin_three_one (xi : Fin 2 → ℝ) :
    cyclicPartialSum (rsZeroSumLift xi) (1 : Fin 3) = xi 0 := by
  unfold cyclicPartialSum
  rw [show (Finset.univ.filter fun j : Fin 3 => j < (1 : Fin 3)) =
      {0} by
    ext j
    fin_cases j <;> simp]
  simp [lift_fin_two_zero]

private lemma cyclic_partial_fin_three_two (xi : Fin 2 → ℝ) :
    cyclicPartialSum (rsZeroSumLift xi) (2 : Fin 3) = xi 0 + xi 1 := by
  unfold cyclicPartialSum
  rw [show (Finset.univ.filter fun j : Fin 3 => j < (2 : Fin 3)) =
      {0, 1} by
    ext j
    fin_cases j <;> simp]
  simp [lift_fin_two_zero, lift_fin_two_one]

private lemma gauge_phase_fin_three (x : Fin 3 → ℂ) (xi : Fin 2 → ℝ) :
    (∑ j : Fin 3, x j * (rsZeroSumLift xi j : ℂ)) =
      (x 0 - x 2) * (xi 0 : ℂ) +
        (x 1 - x 2) * (xi 1 : ℂ) := by
  rw [Fin.sum_univ_three, lift_fin_two_zero, lift_fin_two_one,
    lift_fin_two_two]
  push_cast
  ring

private lemma integral_fin_three_eq_iterated
    (f : (Fin 3 → ℝ) → ℂ) (hf : Integrable f) :
    (∫ q : Fin 3 → ℝ, f q) =
      ∫ xi : Fin 2 → ℝ, ∫ u : ℝ, f ![u, xi 0, xi 1] := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have hp := volume_preserving_piFinSuccAbove
    (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have hfi : Integrable
      (fun p : ℝ × (Fin 2 → ℝ) => f (e.symm p)) :=
    (hp.symm e).integrable_comp_of_integrable hf
  have hmap := (hp.symm e).integral_comp' f
  change (∫ p : ℝ × (Fin 2 → ℝ), f (e.symm p)
      ∂(volume.prod volume)) = (∫ q : Fin 3 → ℝ, f q) at hmap
  rw [integral_prod_symm _ hfi] at hmap
  rw [← hmap]
  apply integral_congr_ae
  filter_upwards [] with xi
  apply integral_congr_ae
  filter_upwards [] with u
  congr 1
  funext i
  fin_cases i <;> rfl

private lemma rsGaugeTest_weightedCyclicSymbol_three_eq_source
    {mu : ℝ} (hmu : 0 < mu) (r : ℝ → ℝ)
    (hcont : Continuous r) (hcompact : HasCompactSupport r)
    (x : Fin 3 → ℂ) :
    rsGaugeTest (n := 2) (weightedCyclicSymbol (k := 3) mu r) x =
      ∫ q : Fin 3 → ℝ, cyclicSourceThree mu r x q := by
  unfold rsGaugeTest weightedCyclicSymbol
  rw [integral_fin_three_eq_iterated _
    (cyclicSourceThree_integrable hmu hcont hcompact x)]
  apply integral_congr_ae
  filter_upwards [] with xi
  rw [gauge_phase_fin_three]
  simp_rw [Fin.prod_univ_three, cyclic_partial_fin_three_zero,
    cyclic_partial_fin_three_one, cyclic_partial_fin_three_two]
  simp only [zero_div, add_zero]
  unfold cyclicSourceThree
  simp
  rw [← integral_complex_ofReal]
  push_cast
  rw [← integral_const_mul, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with u
  ring

/-- Exact Fourier evaluation of the degree-three cyclic RS test at complex
arguments. -/
theorem rsGaugeTest_weightedCyclicSymbol_three
    {mu : ℝ} (hmu : 0 < mu) (r : ℝ → ℝ)
    (hcont : Continuous r) (hcompact : HasCompactSupport r)
    (x : Fin 3 → ℂ) :
    rsGaugeTest (n := 2) (weightedCyclicSymbol (k := 3) mu r) x =
      (mu : ℂ) ^ 3 * ∏ j : Fin 3,
        paperFT (fun y => (r y : ℂ))
          (cyclicFrequencyThree mu x j) := by
  rw [rsGaugeTest_weightedCyclicSymbol_three_eq_source
    hmu r hcont hcompact x]
  exact cyclicSourceThree_integral hmu r x

end RH.Zeta85.RSReduction
