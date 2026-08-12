/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSReduction
import Zeta23.Taper.Fourier

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

end RH.Zeta85.RSReduction
