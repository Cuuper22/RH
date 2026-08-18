/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Convolution
import RH.Zeta85.Discharge.RSReduction

/-!
# Analytic evaluation of the Rudnick--Sarnak contractions through degree four

This file proves the analytic bridge for every one- and two-pair term in the
weighted cyclic symbol through degree four.  The central one-pair change of
variables is

`w = mu * (y - x)`.

Consequently a one-pair `rsPairIntegral` is `mu ^ 3` times its distance
integral.  Formula (27) uses the explicitly defined `normalizedRSMainTerm`,
which divides the RS main term by `mu`; its one-pair coefficient is therefore
`mu ^ 2`, not `mu ^ 3`.

The hypotheses are literal `Integrable` statements for the displayed two- and
three-variable kernels.  No block limit, height smoothing, Poisson formula, or
top-hat limiting argument is assumed.  The three two-pair symbols at degree
four are classified pointwise as separated, nested, and crossing, then
evaluated by Fubini and two sequential scale changes.  The resulting
`normalizedRSMainTerm_k4` is formula (27) with explicit `mu ^ 2` and `mu ^ 4`
coefficients.
-/

open MeasureTheory Zeta23
open scoped BigOperators Matrix Convolution ContDiff

noncomputable section

namespace RH.Zeta85.RSPairIntegrals

open RSReduction TopHatMoments

lemma integral_abs_mul_shift_div (mu x : ℝ) (f : ℝ → ℝ) (hmu : 0 < mu) :
    (∫ w : ℝ, |w| * f (x + w / mu)) =
      mu ^ 2 * ∫ y : ℝ, |y - x| * f y := by
  let g : ℝ → ℝ := fun t => |t| * f (x + t)
  have habs (w : ℝ) : |w| = mu * |w / mu| := by
    calc
      |w| = |mu * (w / mu)| := by rw [mul_div_cancel₀ w hmu.ne']
      _ = |mu| * |w / mu| := abs_mul _ _
      _ = mu * |w / mu| := by rw [abs_of_pos hmu]
  calc
    (∫ w : ℝ, |w| * f (x + w / mu)) =
        mu * ∫ w : ℝ, g (w / mu) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with w
          rw [habs w]
          simp only [g]
          ring
    _ = mu * (|mu| * ∫ t : ℝ, g t) := by
      rw [Measure.integral_comp_div]
      simp only [smul_eq_mul]
    _ = mu ^ 2 * ∫ t : ℝ, g t := by rw [abs_of_pos hmu]; ring
    _ = mu ^ 2 * ∫ y : ℝ, |y - x| * f y := by
      congr 1
      simpa [g, add_sub_cancel_left] using
        (integral_add_left_eq_self (fun y : ℝ => |y - x| * f y) x)

def onePairIntegrand (mu : ℝ) (f g : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  |z.2| * (mu * (f z.1 * g (z.1 + z.2 / mu)))

def onePairCoordinateIntegral (mu : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ w : ℝ, |w| * (mu * ∫ x : ℝ, f x * g (x + w / mu))

def distanceIntegral (f g : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, f x * ∫ y : ℝ, |y - x| * g y

def distanceKernel (f g : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  |z.2 - z.1| * f z.1 * g z.2

/-- A continuous compactly supported pair of profiles makes the literal
one-pair Fubini kernel integrable. -/
theorem onePairIntegrand_integrable_of_continuous_compact
    (mu : ℝ) (f g : ℝ → ℝ) (hmu : mu ≠ 0)
    (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (onePairIntegrand mu f g) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold onePairIntegrand
    fun_prop
  · let F : ℝ × ℝ → ℝ × ℝ := fun xy =>
      (xy.1, mu * (xy.2 - xy.1))
    apply HasCompactSupport.intro
      ((hfc.isCompact.prod hgc.isCompact).image (by fun_prop : Continuous F))
    intro z hz
    by_cases hfx : f z.1 = 0
    · simp [onePairIntegrand, hfx]
    by_cases hgy : g (z.1 + z.2 / mu) = 0
    · simp [onePairIntegrand, hgy]
    exfalso
    apply hz
    refine ⟨(z.1, z.1 + z.2 / mu), ?_, ?_⟩
    · exact ⟨subset_tsupport f hfx, subset_tsupport g hgy⟩
    · dsimp only [F]
      ext
      · rfl
      · field_simp
        ring

/-- Continuous compactly supported profiles make the literal distance
kernel integrable. -/
theorem distanceKernel_integrable_of_continuous_compact
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (distanceKernel f g) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold distanceKernel
    fun_prop
  · apply HasCompactSupport.intro (hfc.isCompact.prod hgc.isCompact)
    intro z hz
    by_cases hx : z.1 ∈ tsupport f
    · have hy : z.2 ∉ tsupport g := fun hy => hz ⟨hx, hy⟩
      unfold distanceKernel
      rw [image_eq_zero_of_notMem_tsupport hy]
      simp
    · unfold distanceKernel
      rw [image_eq_zero_of_notMem_tsupport hx]
      simp

/-- A positive pointwise power does not enlarge compact support. -/
theorem positivePower_hasCompactSupport (r : ℝ → ℝ) (n : ℕ)
    (hn : 0 < n) (hrc : HasCompactSupport r) :
    HasCompactSupport (fun x => r x ^ n) := by
  apply hrc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hr0
  apply hx
  rw [hr0, zero_pow (Nat.ne_of_gt hn)]

theorem distanceIntegral_comm (f g : ℝ → ℝ)
    (hint : Integrable (distanceKernel f g)) :
    distanceIntegral f g = distanceIntegral g f := by
  have hint' : Integrable (distanceKernel g f) := by
    apply hint.swap.congr
    filter_upwards [] with z
    simp only [Function.comp_apply, distanceKernel, Prod.swap]
    rw [abs_sub_comm]
    ring
  calc
    distanceIntegral f g = ∫ z : ℝ × ℝ, distanceKernel f g z := by
      rw [distanceIntegral, Measure.volume_eq_prod, integral_prod _ hint]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [distanceKernel]
      ring_nf
    _ = ∫ z : ℝ × ℝ, distanceKernel f g z.swap := by
      simp only [Measure.volume_eq_prod]
      exact (integral_prod_swap (μ := volume) (ν := volume) (distanceKernel f g)).symm
    _ = ∫ z : ℝ × ℝ, distanceKernel g f z := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [Prod.swap, distanceKernel]
      rw [abs_sub_comm]
      ring_nf
    _ = distanceIntegral g f := by
      rw [distanceIntegral, Measure.volume_eq_prod, integral_prod _ hint']
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [distanceKernel]
      ring

theorem integral_fin_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin 1 → ℝ) → E) :
    (∫ w : Fin 1 → ℝ, F w) = ∫ x : ℝ, F (fun _ => x) := by
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have h := (volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
    (fun x : ℝ => F (e.symm x))
  calc
    (∫ w : Fin 1 → ℝ, F w) =
        ∫ w : Fin 1 → ℝ, F (e.symm (e w)) := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [e.symm_apply_apply]
    _ = ∫ x : ℝ, F (e.symm x) := h
    _ = ∫ x : ℝ, F (fun _ => x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1

/-- Lebesgue integration on `Fin 2 → ℝ` is integration on the two
explicit coordinates. -/
theorem integral_fin_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin 2 → ℝ) → E) :
    (∫ w : Fin 2 → ℝ, F w) = ∫ z : ℝ × ℝ, F ![z.1, z.2] := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have h := (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).integral_comp'
    (fun z : ℝ × ℝ => F (e.symm z))
  calc
    (∫ w : Fin 2 → ℝ, F w) =
        ∫ w : Fin 2 → ℝ, F (e.symm (e w)) := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [e.symm_apply_apply]
    _ = ∫ z : ℝ × ℝ, F (e.symm z) := h
    _ = ∫ z : ℝ × ℝ, F ![z.1, z.2] := by
      apply integral_congr_ae
      filter_upwards [] with z
      congr 1

theorem onePairCoordinateIntegral_eq (mu : ℝ) (f g : ℝ → ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu f g)) :
    onePairCoordinateIntegral mu f g = mu ^ 3 * distanceIntegral f g := by
  have hswap :
      (∫ w : ℝ, ∫ x : ℝ, onePairIntegrand mu f g (x, w)) =
        ∫ x : ℝ, ∫ w : ℝ, onePairIntegrand mu f g (x, w) := by
    exact integral_integral_swap hint.swap
  calc
    onePairCoordinateIntegral mu f g =
        ∫ w : ℝ, ∫ x : ℝ, onePairIntegrand mu f g (x, w) := by
      apply integral_congr_ae
      filter_upwards [] with w
      calc
        |w| * (mu * ∫ x : ℝ, f x * g (x + w / mu)) =
            (|w| * mu) * ∫ x : ℝ, f x * g (x + w / mu) := by ring
        _ = ∫ x : ℝ, (|w| * mu) * (f x * g (x + w / mu)) := by
          rw [integral_const_mul]
        _ = ∫ x : ℝ, onePairIntegrand mu f g (x, w) := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [onePairIntegrand]
          ring
    _ = ∫ x : ℝ, ∫ w : ℝ, onePairIntegrand mu f g (x, w) := hswap
    _ = ∫ x : ℝ, mu ^ 3 *
        (f x * ∫ y : ℝ, |y - x| * g y) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [onePairIntegrand]
      rw [show (∫ w : ℝ, |w| * (mu * (f x * g (x + w / mu)))) =
          mu * f x * ∫ w : ℝ, |w| * g (x + w / mu) by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with w
        ring]
      rw [integral_abs_mul_shift_div mu x g hmu]
      ring
    _ = mu ^ 3 * distanceIntegral f g := by
      rw [integral_const_mul]
      rfl

theorem rsPairIntegral_one_eq_coordinate {n : ℕ}
    (Phi : (Fin (n + 1) → ℝ) → ℂ)
    (pairing : (Fin 1 → Fin (n + 1)) × (Fin 1 → Fin (n + 1)))
    (mu : ℝ) (f g : ℝ → ℝ)
    (hPhi : ∀ w : ℝ,
      Phi (rsPairVector pairing (fun _ => w)) =
        (mu * ∫ x : ℝ, f x * g (x + w / mu) : ℝ)) :
    rsPairIntegral Phi pairing = (onePairCoordinateIntegral mu f g : ℝ) := by
  simp only [rsPairIntegral, Fin.prod_univ_succ, Fin.prod_univ_zero]
  rw [integral_fin_one]
  calc
    (∫ w : ℝ, (((|w| * 1 : ℝ) : ℝ) : ℂ) *
        Phi (rsPairVector pairing (fun _ => w))) =
      ∫ w : ℝ, ((|w| * (mu * ∫ x : ℝ,
        f x * g (x + w / mu)) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [hPhi w]
      norm_cast
      ring
    _ = (onePairCoordinateIntegral mu f g : ℝ) := by
      unfold onePairCoordinateIntegral
      convert (integral_ofReal (𝕜 := ℂ) (μ := volume)
        (f := fun w : ℝ => |w| * (mu * ∫ x : ℝ,
          f x * g (x + w / mu)))) using 1 <;> rfl

theorem rsPairIntegral_one_eq_distance {n : ℕ}
    (Phi : (Fin (n + 1) → ℝ) → ℂ)
    (pairing : (Fin 1 → Fin (n + 1)) × (Fin 1 → Fin (n + 1)))
    (mu : ℝ) (f g : ℝ → ℝ) (hmu : 0 < mu)
    (hPhi : ∀ w : ℝ,
      Phi (rsPairVector pairing (fun _ => w)) =
        (mu * ∫ x : ℝ, f x * g (x + w / mu) : ℝ))
    (hint : Integrable (onePairIntegrand mu f g)) :
    rsPairIntegral Phi pairing = (mu ^ 3 * distanceIntegral f g : ℝ) := by
  rw [rsPairIntegral_one_eq_coordinate Phi pairing mu f g hPhi,
    onePairCoordinateIntegral_eq mu f g hmu hint]

/-- A two-pair contraction written on its two explicit coordinates. -/
def twoPairCoordinateIntegral (core : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, |z.1| * |z.2| * core z.1 z.2

/-- Convert a `q = 2` `rsPairIntegral` into a literal two-dimensional
coordinate integral.  This is a measure-preserving coordinate
identification, not yet the three-variable Fubini evaluation. -/
theorem rsPairIntegral_two_eq_coordinate {n : ℕ}
    (Phi : (Fin (n + 1) → ℝ) → ℂ)
    (pairing : (Fin 2 → Fin (n + 1)) × (Fin 2 → Fin (n + 1)))
    (core : ℝ → ℝ → ℝ)
    (hPhi : ∀ u v : ℝ,
      Phi (rsPairVector pairing ![u, v]) = (core u v : ℝ)) :
    rsPairIntegral Phi pairing = (twoPairCoordinateIntegral core : ℝ) := by
  simp only [rsPairIntegral]
  rw [integral_fin_two]
  calc
    (∫ z : ℝ × ℝ,
      (((∏ a : Fin 2, |![z.1, z.2] a| : ℝ) : ℝ) : ℂ) *
        Phi (rsPairVector pairing ![z.1, z.2])) =
      ∫ z : ℝ × ℝ, ((|z.1| * |z.2| * core z.1 z.2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hPhi z.1 z.2]
      norm_cast
      norm_num [Fin.prod_univ_two]
    _ = (twoPairCoordinateIntegral core : ℝ) := by
      unfold twoPairCoordinateIntegral
      convert (integral_ofReal (𝕜 := ℂ) (μ := volume)
        (f := fun z : ℝ × ℝ => |z.1| * |z.2| * core z.1 z.2)) using 1 <;> rfl

theorem rsPairIntegral_k2_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu r r)) :
    rsPairIntegral (weightedCyclicSymbol (k := 2) mu r)
        (![↑(0 : Fin 2)], ![↑(1 : Fin 2)]) =
      (mu ^ 3 * distanceIntegral r r : ℝ) := by
  apply rsPairIntegral_one_eq_distance _ _ mu r r hmu _ hint
  intro w
  simpa using
    (show weightedCyclicSymbol (k := 2) mu r
        (rsPairVector (![↑(0 : Fin 2)], ![↑(1 : Fin 2)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x * r (x + w / mu) : ℝ) by
        simp [weightedCyclicSymbol, cyclicPartialSum, rsPairVector])

theorem weightedCyclicSymbol_k3_01 (mu : ℝ) (r : ℝ → ℝ) (w : ℝ) :
    weightedCyclicSymbol (k := 3) mu r
        (rsPairVector (![↑(0 : Fin 3)], ![↑(1 : Fin 3)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x ^ 2 * r (x + w / mu) : ℝ) := by
  simp only [weightedCyclicSymbol, cyclicPartialSum, rsPairVector]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Fin.prod_univ_succ]
  ring_nf

theorem weightedCyclicSymbol_k3_02 (mu : ℝ) (r : ℝ → ℝ) (w : ℝ) :
    weightedCyclicSymbol (k := 3) mu r
        (rsPairVector (![↑(0 : Fin 3)], ![↑(2 : Fin 3)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x * r (x + w / mu) ^ 2 : ℝ) := by
  simp only [weightedCyclicSymbol, cyclicPartialSum, rsPairVector]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Fin.prod_univ_succ]
  ring_nf
  tauto

theorem weightedCyclicSymbol_k3_12 (mu : ℝ) (r : ℝ → ℝ) (w : ℝ) :
    weightedCyclicSymbol (k := 3) mu r
        (rsPairVector (![↑(1 : Fin 3)], ![↑(2 : Fin 3)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x ^ 2 * r (x + w / mu) : ℝ) := by
  simp only [weightedCyclicSymbol, cyclicPartialSum, rsPairVector]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Fin.prod_univ_succ]
  ring

theorem rsPairIntegral_k3_01_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu (fun x => r x ^ 2) r)) :
    rsPairIntegral (weightedCyclicSymbol (k := 3) mu r)
        (![↑(0 : Fin 3)], ![↑(1 : Fin 3)]) =
      (mu ^ 3 * distanceIntegral (fun x => r x ^ 2) r : ℝ) := by
  exact rsPairIntegral_one_eq_distance _ _ mu _ _ hmu
    (weightedCyclicSymbol_k3_01 mu r) hint

theorem rsPairIntegral_k3_02_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu r (fun x => r x ^ 2))) :
    rsPairIntegral (weightedCyclicSymbol (k := 3) mu r)
        (![↑(0 : Fin 3)], ![↑(2 : Fin 3)]) =
      (mu ^ 3 * distanceIntegral r (fun x => r x ^ 2) : ℝ) := by
  exact rsPairIntegral_one_eq_distance _ _ mu _ _ hmu
    (weightedCyclicSymbol_k3_02 mu r) hint

theorem rsPairIntegral_k3_12_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu (fun x => r x ^ 2) r)) :
    rsPairIntegral (weightedCyclicSymbol (k := 3) mu r)
        (![↑(1 : Fin 3)], ![↑(2 : Fin 3)]) =
      (mu ^ 3 * distanceIntegral (fun x => r x ^ 2) r : ℝ) := by
  exact rsPairIntegral_one_eq_distance _ _ mu _ _ hmu
    (weightedCyclicSymbol_k3_12 mu r) hint

theorem weightedCyclicSymbol_k4_01 (mu : ℝ) (r : ℝ → ℝ) (w : ℝ) :
    weightedCyclicSymbol (k := 4) mu r
        (rsPairVector (![↑(0 : Fin 4)], ![↑(1 : Fin 4)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x ^ 3 * r (x + w / mu) : ℝ) := by
  simp only [weightedCyclicSymbol, cyclicPartialSum, rsPairVector]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Fin.prod_univ_succ]
  ring_nf

theorem weightedCyclicSymbol_k4_02 (mu : ℝ) (r : ℝ → ℝ) (w : ℝ) :
    weightedCyclicSymbol (k := 4) mu r
        (rsPairVector (![↑(0 : Fin 4)], ![↑(2 : Fin 4)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x ^ 2 * r (x + w / mu) ^ 2 : ℝ) := by
  simp only [weightedCyclicSymbol, cyclicPartialSum, rsPairVector]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Fin.prod_univ_succ]
  ring_nf

theorem weightedCyclicSymbol_k4_03 (mu : ℝ) (r : ℝ → ℝ) (w : ℝ) :
    weightedCyclicSymbol (k := 4) mu r
        (rsPairVector (![↑(0 : Fin 4)], ![↑(3 : Fin 4)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x * r (x + w / mu) ^ 3 : ℝ) := by
  simp only [weightedCyclicSymbol, cyclicPartialSum, rsPairVector]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Fin.prod_univ_succ]
  ring_nf
  tauto

theorem weightedCyclicSymbol_k4_12 (mu : ℝ) (r : ℝ → ℝ) (w : ℝ) :
    weightedCyclicSymbol (k := 4) mu r
        (rsPairVector (![↑(1 : Fin 4)], ![↑(2 : Fin 4)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x ^ 3 * r (x + w / mu) : ℝ) := by
  simp only [weightedCyclicSymbol, cyclicPartialSum, rsPairVector]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Fin.prod_univ_succ]
  ring_nf

theorem weightedCyclicSymbol_k4_13 (mu : ℝ) (r : ℝ → ℝ) (w : ℝ) :
    weightedCyclicSymbol (k := 4) mu r
        (rsPairVector (![↑(1 : Fin 4)], ![↑(3 : Fin 4)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x ^ 2 * r (x + w / mu) ^ 2 : ℝ) := by
  simp only [weightedCyclicSymbol, cyclicPartialSum, rsPairVector]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Fin.prod_univ_succ]
  ring_nf

theorem weightedCyclicSymbol_k4_23 (mu : ℝ) (r : ℝ → ℝ) (w : ℝ) :
    weightedCyclicSymbol (k := 4) mu r
        (rsPairVector (![↑(2 : Fin 4)], ![↑(3 : Fin 4)]) (fun _ => w)) =
      (mu * ∫ x : ℝ, r x ^ 3 * r (x + w / mu) : ℝ) := by
  simp only [weightedCyclicSymbol, cyclicPartialSum, rsPairVector]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Fin.prod_univ_succ]
  ring_nf

/-! ## Evaluated degree-four one-pair terms -/

/-- The `(0,1)` contraction is an adjacent distance integral. -/
theorem rsPairIntegral_k4_01_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu (fun x => r x ^ 3) r)) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4)], ![↑(1 : Fin 4)]) =
      (mu ^ 3 * distanceIntegral (fun x => r x ^ 3) r : ℝ) := by
  exact rsPairIntegral_one_eq_distance _ _ mu _ _ hmu
    (weightedCyclicSymbol_k4_01 mu r) hint

/-- The `(0,2)` contraction is an opposite distance integral. -/
theorem rsPairIntegral_k4_02_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu (fun x => r x ^ 2) (fun x => r x ^ 2))) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4)], ![↑(2 : Fin 4)]) =
      (mu ^ 3 * distanceIntegral (fun x => r x ^ 2) (fun x => r x ^ 2) : ℝ) := by
  exact rsPairIntegral_one_eq_distance _ _ mu _ _ hmu
    (weightedCyclicSymbol_k4_02 mu r) hint

/-- The `(0,3)` contraction is the reversed adjacent distance integral. -/
theorem rsPairIntegral_k4_03_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu r (fun x => r x ^ 3))) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4)], ![↑(3 : Fin 4)]) =
      (mu ^ 3 * distanceIntegral r (fun x => r x ^ 3) : ℝ) := by
  exact rsPairIntegral_one_eq_distance _ _ mu _ _ hmu
    (weightedCyclicSymbol_k4_03 mu r) hint

/-- The `(1,2)` contraction is an adjacent distance integral. -/
theorem rsPairIntegral_k4_12_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu (fun x => r x ^ 3) r)) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(1 : Fin 4)], ![↑(2 : Fin 4)]) =
      (mu ^ 3 * distanceIntegral (fun x => r x ^ 3) r : ℝ) := by
  exact rsPairIntegral_one_eq_distance _ _ mu _ _ hmu
    (weightedCyclicSymbol_k4_12 mu r) hint

/-- The `(1,3)` contraction is an opposite distance integral. -/
theorem rsPairIntegral_k4_13_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu (fun x => r x ^ 2) (fun x => r x ^ 2))) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(1 : Fin 4)], ![↑(3 : Fin 4)]) =
      (mu ^ 3 * distanceIntegral (fun x => r x ^ 2) (fun x => r x ^ 2) : ℝ) := by
  exact rsPairIntegral_one_eq_distance _ _ mu _ _ hmu
    (weightedCyclicSymbol_k4_13 mu r) hint

/-- The `(2,3)` contraction is an adjacent distance integral. -/
theorem rsPairIntegral_k4_23_distance (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu (fun x => r x ^ 3) r)) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(2 : Fin 4)], ![↑(3 : Fin 4)]) =
      (mu ^ 3 * distanceIntegral (fun x => r x ^ 3) r : ℝ) := by
  exact rsPairIntegral_one_eq_distance _ _ mu _ _ hmu
    (weightedCyclicSymbol_k4_23 mu r) hint

/-- The six degree-four one-pair contractions, divided by `mu`, have the
formula-(27) coefficient `mu ^ 2 * (4 * adjacent + 2 * opposite)`. -/
theorem normalized_k4_onePairSum (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (h31 : Integrable (onePairIntegrand mu (fun x => r x ^ 3) r))
    (h13 : Integrable (onePairIntegrand mu r (fun x => r x ^ 3)))
    (h22 : Integrable
      (onePairIntegrand mu (fun x => r x ^ 2) (fun x => r x ^ 2)))
    (hdist : Integrable (distanceKernel (fun x => r x ^ 3) r)) :
    (rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4)], ![↑(1 : Fin 4)]) +
      rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4)], ![↑(2 : Fin 4)]) +
      rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4)], ![↑(3 : Fin 4)]) +
      rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(1 : Fin 4)], ![↑(2 : Fin 4)]) +
      rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(1 : Fin 4)], ![↑(3 : Fin 4)]) +
      rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(2 : Fin 4)], ![↑(3 : Fin 4)])) / (mu : ℂ) =
      (mu ^ 2 *
        (4 * distanceIntegral (fun x => r x ^ 3) r +
          2 * distanceIntegral (fun x => r x ^ 2) (fun x => r x ^ 2)) : ℝ) := by
  rw [rsPairIntegral_k4_01_distance mu r hmu h31,
    rsPairIntegral_k4_02_distance mu r hmu h22,
    rsPairIntegral_k4_03_distance mu r hmu h13,
    rsPairIntegral_k4_12_distance mu r hmu h31,
    rsPairIntegral_k4_13_distance mu r hmu h22,
    rsPairIntegral_k4_23_distance mu r hmu h31,
    ← distanceIntegral_comm (fun x => r x ^ 3) r hdist]
  norm_cast
  field_simp [hmu.ne']
  ring

theorem weightedCyclicSymbol_k4_separated (mu : ℝ) (r : ℝ → ℝ)
    (w : Fin 2 → ℝ) :
    weightedCyclicSymbol (k := 4) mu r
        (rsPairVector (![↑(0 : Fin 4), ↑(2 : Fin 4)],
          ![↑(1 : Fin 4), ↑(3 : Fin 4)]) w) =
      (mu * ∫ x : ℝ,
        r x ^ 2 * r (x + w 0 / mu) * r (x + w 1 / mu) : ℝ) := by
  let xi := rsPairVector (![↑(0 : Fin 4), ↑(2 : Fin 4)],
    ![↑(1 : Fin 4), ↑(3 : Fin 4)]) w
  have hs0 : cyclicPartialSum xi 0 = 0 := by
    simp [cyclicPartialSum]
  have hs1 : cyclicPartialSum xi 1 = w 0 := by
    simp only [cyclicPartialSum]
    rw [show Finset.univ.filter (fun j : Fin 4 => j < 1) = {0} by decide]
    simp [xi, rsPairVector, Fin.sum_univ_two]
  have hs2 : cyclicPartialSum xi 2 = 0 := by
    simp only [cyclicPartialSum]
    rw [show Finset.univ.filter (fun j : Fin 4 => j < 2) = {0, 1} by decide]
    simp [xi, rsPairVector, Fin.sum_univ_two]
  have hs3 : cyclicPartialSum xi 3 = w 1 := by
    simp only [cyclicPartialSum]
    rw [show Finset.univ.filter (fun j : Fin 4 => j < 3) = {0, 1, 2} by decide]
    simp [xi, rsPairVector, Fin.sum_univ_two]
  change weightedCyclicSymbol mu r xi = _
  simp only [weightedCyclicSymbol]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Fin.prod_univ_four, hs0, hs1, hs2, hs3]
  simp only [add_zero, zero_div]
  ring_nf

theorem weightedCyclicSymbol_k4_nested (mu : ℝ) (r : ℝ → ℝ)
    (w : Fin 2 → ℝ) :
    weightedCyclicSymbol (k := 4) mu r
        (rsPairVector (![↑(0 : Fin 4), ↑(1 : Fin 4)],
          ![↑(3 : Fin 4), ↑(2 : Fin 4)]) w) =
      (mu * ∫ x : ℝ,
        r x * r (x + w 0 / mu) ^ 2 *
          r (x + (w 0 + w 1) / mu) : ℝ) := by
  let xi := rsPairVector (![↑(0 : Fin 4), ↑(1 : Fin 4)],
    ![↑(3 : Fin 4), ↑(2 : Fin 4)]) w
  have hs0 : cyclicPartialSum xi 0 = 0 := by simp [cyclicPartialSum]
  have hs1 : cyclicPartialSum xi 1 = w 0 := by
    simp only [cyclicPartialSum]
    rw [show Finset.univ.filter (fun j : Fin 4 => j < 1) = {0} by decide]
    simp [xi, rsPairVector, Fin.sum_univ_two]
  have hs2 : cyclicPartialSum xi 2 = w 0 + w 1 := by
    simp only [cyclicPartialSum]
    rw [show Finset.univ.filter (fun j : Fin 4 => j < 2) = {0, 1} by decide]
    simp [xi, rsPairVector, Fin.sum_univ_two]
  have hs3 : cyclicPartialSum xi 3 = w 0 := by
    simp only [cyclicPartialSum]
    rw [show Finset.univ.filter (fun j : Fin 4 => j < 3) = {0, 1, 2} by decide]
    simp [xi, rsPairVector, Fin.sum_univ_two]
  change weightedCyclicSymbol mu r xi = _
  simp only [weightedCyclicSymbol]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Fin.prod_univ_four, hs0, hs1, hs2, hs3]
  simp only [add_zero, zero_div]
  ring_nf

theorem weightedCyclicSymbol_k4_crossing (mu : ℝ) (r : ℝ → ℝ)
    (w : Fin 2 → ℝ) :
    weightedCyclicSymbol (k := 4) mu r
        (rsPairVector (![↑(0 : Fin 4), ↑(1 : Fin 4)],
          ![↑(2 : Fin 4), ↑(3 : Fin 4)]) w) =
      (mu * ∫ x : ℝ,
        r x * r (x + w 0 / mu) * r (x + (w 0 + w 1) / mu) *
          r (x + w 1 / mu) : ℝ) := by
  let xi := rsPairVector (![↑(0 : Fin 4), ↑(1 : Fin 4)],
    ![↑(2 : Fin 4), ↑(3 : Fin 4)]) w
  have hs0 : cyclicPartialSum xi 0 = 0 := by simp [cyclicPartialSum]
  have hs1 : cyclicPartialSum xi 1 = w 0 := by
    simp only [cyclicPartialSum]
    rw [show Finset.univ.filter (fun j : Fin 4 => j < 1) = {0} by decide]
    simp [xi, rsPairVector, Fin.sum_univ_two]
  have hs2 : cyclicPartialSum xi 2 = w 0 + w 1 := by
    simp only [cyclicPartialSum]
    rw [show Finset.univ.filter (fun j : Fin 4 => j < 2) = {0, 1} by decide]
    simp [xi, rsPairVector, Fin.sum_univ_two]
  have hs3 : cyclicPartialSum xi 3 = w 1 := by
    simp only [cyclicPartialSum]
    rw [show Finset.univ.filter (fun j : Fin 4 => j < 3) = {0, 1, 2} by decide]
    simp [xi, rsPairVector, Fin.sum_univ_two]
  change weightedCyclicSymbol mu r xi = _
  simp only [weightedCyclicSymbol]
  norm_cast
  apply congrArg (fun t : ℝ => mu * t)
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Fin.prod_univ_four, hs0, hs1, hs2, hs3]
  simp only [add_zero, zero_div]

/-! ## Exact evaluation of the three degree-four two-pair terms -/

/-- Coordinate core for the separated matching `(0,1)(2,3)`. -/
def separatedTwoPairCore (mu : ℝ) (r : ℝ → ℝ) (u v : ℝ) : ℝ :=
  mu * ∫ x : ℝ, r x ^ 2 * r (x + u / mu) * r (x + v / mu)

/-- Coordinate core for the nested matching `(0,3)(1,2)`. -/
def nestedTwoPairCore (mu : ℝ) (r : ℝ → ℝ) (u v : ℝ) : ℝ :=
  mu * ∫ x : ℝ,
    r x * r (x + u / mu) ^ 2 * r (x + (u + v) / mu)

/-- Coordinate core for the crossing matching `(0,2)(1,3)`. -/
def crossingTwoPairCore (mu : ℝ) (r : ℝ → ℝ) (u v : ℝ) : ℝ :=
  mu * ∫ x : ℝ,
    r x * r (x + u / mu) * r (x + (u + v) / mu) * r (x + v / mu)

/-- The distance potential generated by a symbolic profile. -/
def pairDistancePotential (r : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, |y - x| * r y

/-- The noncrossing two-pair functional in formula (27). -/
def pairSquaredPotentialIntegral (r : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, r x ^ 2 * pairDistancePotential r x ^ 2

/-- Literal three-variable kernel whose first two coordinates are the two
RS contraction variables and whose last coordinate is the cyclic-symbol
integration variable. -/
def separatedTwoPairFubiniKernel (mu : ℝ) (r : ℝ → ℝ)
    (z : (ℝ × ℝ) × ℝ) : ℝ :=
  |z.1.1| * |z.1.2| *
    (mu * (r z.2 ^ 2 * r (z.2 + z.1.1 / mu) * r (z.2 + z.1.2 / mu)))

/-- Evaluation of a fixed-`x` separated two-pair section.  The sole
hypothesis is integrability of that literal two-variable section. -/
theorem separatedTwoPairSection_eq (mu : ℝ) (r : ℝ → ℝ) (x : ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (fun uv : ℝ × ℝ =>
      separatedTwoPairFubiniKernel mu r (uv, x))) :
    (∫ uv : ℝ × ℝ, separatedTwoPairFubiniKernel mu r (uv, x)) =
      mu ^ 5 * (r x ^ 2 * pairDistancePotential r x ^ 2) := by
  have hint' : Integrable (fun uv : ℝ × ℝ =>
      separatedTwoPairFubiniKernel mu r (uv, x)) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hint
  rw [Measure.volume_eq_prod, integral_prod _ hint']
  calc
    (∫ u : ℝ, ∫ v : ℝ,
      separatedTwoPairFubiniKernel mu r ((u, v), x)) =
        ∫ u : ℝ,
          (|u| * mu * r x ^ 2 * r (x + u / mu)) *
            (∫ v : ℝ, |v| * r (x + v / mu)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [separatedTwoPairFubiniKernel]
      ring
    _ = ∫ u : ℝ,
          (|u| * mu * r x ^ 2 * r (x + u / mu)) *
            (mu ^ 2 * pairDistancePotential r x) := by
      rw [integral_abs_mul_shift_div mu x r hmu]
      rfl
    _ = (mu ^ 3 * r x ^ 2 * pairDistancePotential r x) *
          (∫ u : ℝ, |u| * r (x + u / mu)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      ring
    _ = (mu ^ 3 * r x ^ 2 * pairDistancePotential r x) *
          (mu ^ 2 * pairDistancePotential r x) := by
      rw [integral_abs_mul_shift_div mu x r hmu]
      rfl
    _ = mu ^ 5 * (r x ^ 2 * pairDistancePotential r x ^ 2) := by ring

/-- The separated two-pair coordinate integral is `mu ^ 5` times the
formula-(27) squared-potential functional. -/
theorem separatedTwoPairCoordinateIntegral_eq (mu : ℝ) (r : ℝ → ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (separatedTwoPairFubiniKernel mu r)) :
    twoPairCoordinateIntegral (separatedTwoPairCore mu r) =
      mu ^ 5 * pairSquaredPotentialIntegral r := by
  have hint' : Integrable (separatedTwoPairFubiniKernel mu r)
      (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hint
  have hsections : ∀ᵐ x : ℝ ∂volume,
      Integrable (fun uv : ℝ × ℝ => separatedTwoPairFubiniKernel mu r (uv, x)) :=
    hint'.prod_left_ae
  calc
    twoPairCoordinateIntegral (separatedTwoPairCore mu r) =
        ∫ uv : ℝ × ℝ, ∫ x : ℝ,
          separatedTwoPairFubiniKernel mu r (uv, x) := by
      apply integral_congr_ae
      filter_upwards [] with uv
      simp only [separatedTwoPairCore]
      calc
        |uv.1| * |uv.2| *
            (mu * ∫ x : ℝ,
              r x ^ 2 * r (x + uv.1 / mu) * r (x + uv.2 / mu)) =
            (|uv.1| * |uv.2| * mu) *
              ∫ x : ℝ,
                r x ^ 2 * r (x + uv.1 / mu) * r (x + uv.2 / mu) := by ring
        _ = ∫ x : ℝ, separatedTwoPairFubiniKernel mu r (uv, x) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [separatedTwoPairFubiniKernel]
          ring
    _ = ∫ x : ℝ, ∫ uv : ℝ × ℝ,
          separatedTwoPairFubiniKernel mu r (uv, x) := by
      exact integral_integral_swap hint'
    _ = ∫ x : ℝ,
          mu ^ 5 * (r x ^ 2 * pairDistancePotential r x ^ 2) := by
      apply integral_congr_ae
      filter_upwards [hsections] with x hx
      exact separatedTwoPairSection_eq mu r x hmu hx
    _ = mu ^ 5 * pairSquaredPotentialIntegral r := by
      rw [integral_const_mul]
      rfl

/-- The profile that appears after evaluating the inner contraction in the
nested two-pair term. -/
def nestedAuxProfile (r : ℝ → ℝ) (y : ℝ) : ℝ :=
  r y ^ 2 * pairDistancePotential r y

/-- Literal three-variable kernel for the nested two-pair contraction. -/
def nestedTwoPairFubiniKernel (mu : ℝ) (r : ℝ → ℝ)
    (z : (ℝ × ℝ) × ℝ) : ℝ :=
  |z.1.1| * |z.1.2| *
    (mu * (r z.2 * r (z.2 + z.1.1 / mu) ^ 2 *
      r (z.2 + (z.1.1 + z.1.2) / mu)))

/-- Evaluation of a fixed-`x` nested two-pair section. -/
theorem nestedTwoPairSection_eq (mu : ℝ) (r : ℝ → ℝ) (x : ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (fun uv : ℝ × ℝ =>
      nestedTwoPairFubiniKernel mu r (uv, x))) :
    (∫ uv : ℝ × ℝ, nestedTwoPairFubiniKernel mu r (uv, x)) =
      mu ^ 5 * (r x * pairDistancePotential (nestedAuxProfile r) x) := by
  have hint' : Integrable (fun uv : ℝ × ℝ =>
      nestedTwoPairFubiniKernel mu r (uv, x)) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hint
  rw [Measure.volume_eq_prod, integral_prod _ hint']
  calc
    (∫ u : ℝ, ∫ v : ℝ,
      nestedTwoPairFubiniKernel mu r ((u, v), x)) =
        ∫ u : ℝ,
          (|u| * mu * r x * r (x + u / mu) ^ 2) *
            (∫ v : ℝ, |v| * r ((x + u / mu) + v / mu)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [nestedTwoPairFubiniKernel]
      ring_nf
    _ = ∫ u : ℝ,
          (|u| * mu * r x * r (x + u / mu) ^ 2) *
            (mu ^ 2 * pairDistancePotential r (x + u / mu)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_abs_mul_shift_div mu (x + u / mu) r hmu]
      rfl
    _ = (mu ^ 3 * r x) *
          (∫ u : ℝ, |u| * nestedAuxProfile r (x + u / mu)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [nestedAuxProfile]
      ring
    _ = (mu ^ 3 * r x) *
          (mu ^ 2 * pairDistancePotential (nestedAuxProfile r) x) := by
      rw [integral_abs_mul_shift_div mu x (nestedAuxProfile r) hmu]
      rfl
    _ = mu ^ 5 * (r x * pairDistancePotential (nestedAuxProfile r) x) := by ring

/-- The nested two-pair coordinate integral is the second copy of the
formula-(27) squared-potential functional. -/
theorem nestedTwoPairCoordinateIntegral_eq (mu : ℝ) (r : ℝ → ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (nestedTwoPairFubiniKernel mu r))
    (hdist : Integrable (distanceKernel r (nestedAuxProfile r))) :
    twoPairCoordinateIntegral (nestedTwoPairCore mu r) =
      mu ^ 5 * pairSquaredPotentialIntegral r := by
  have hint' : Integrable (nestedTwoPairFubiniKernel mu r)
      (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hint
  have hsections : ∀ᵐ x : ℝ ∂volume,
      Integrable (fun uv : ℝ × ℝ => nestedTwoPairFubiniKernel mu r (uv, x)) :=
    hint'.prod_left_ae
  calc
    twoPairCoordinateIntegral (nestedTwoPairCore mu r) =
        ∫ uv : ℝ × ℝ, ∫ x : ℝ,
          nestedTwoPairFubiniKernel mu r (uv, x) := by
      apply integral_congr_ae
      filter_upwards [] with uv
      simp only [nestedTwoPairCore]
      calc
        |uv.1| * |uv.2| *
            (mu * ∫ x : ℝ,
              r x * r (x + uv.1 / mu) ^ 2 *
                r (x + (uv.1 + uv.2) / mu)) =
            (|uv.1| * |uv.2| * mu) *
              ∫ x : ℝ,
                r x * r (x + uv.1 / mu) ^ 2 *
                  r (x + (uv.1 + uv.2) / mu) := by ring
        _ = ∫ x : ℝ, nestedTwoPairFubiniKernel mu r (uv, x) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [nestedTwoPairFubiniKernel]
          ring
    _ = ∫ x : ℝ, ∫ uv : ℝ × ℝ,
          nestedTwoPairFubiniKernel mu r (uv, x) := by
      exact integral_integral_swap hint'
    _ = ∫ x : ℝ,
          mu ^ 5 * (r x * pairDistancePotential (nestedAuxProfile r) x) := by
      apply integral_congr_ae
      filter_upwards [hsections] with x hx
      exact nestedTwoPairSection_eq mu r x hmu hx
    _ = mu ^ 5 * distanceIntegral r (nestedAuxProfile r) := by
      rw [integral_const_mul]
      rfl
    _ = mu ^ 5 * distanceIntegral (nestedAuxProfile r) r := by
      rw [distanceIntegral_comm r (nestedAuxProfile r) hdist]
    _ = mu ^ 5 * pairSquaredPotentialIntegral r := by
      congr 1
      unfold distanceIntegral nestedAuxProfile pairSquaredPotentialIntegral
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [pairDistancePotential]
      ring

/-- Formula-(27) crossing functional, in the exact variables obtained from
the cyclic partial sums. -/
def crossingFunctional (r : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, r x * ∫ y : ℝ, |y - x| * r y *
    ∫ z : ℝ, |z - y| * r z * r (x + z - y)

/-- Literal three-variable kernel before the two crossing scale changes. -/
def crossingRawKernel (mu : ℝ) (r : ℝ → ℝ)
    (p : (ℝ × ℝ) × ℝ) : ℝ :=
  |p.1.1| * |p.1.2| *
    (mu * (r p.2 * r (p.2 + p.1.1 / mu) *
      r (p.2 + (p.1.1 + p.1.2) / mu) *
      r (p.2 + p.1.2 / mu)))

/-- The distance potential of a continuous compactly supported profile is
continuous.  It is its convolution with the continuous function `abs`. -/
theorem pairDistancePotential_continuous (r : ℝ → ℝ)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    Continuous (pairDistancePotential r) := by
  have hconv : Continuous
      (convolution r abs (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hrc.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hr
      continuous_abs.locallyIntegrable
  apply hconv.congr
  intro x
  unfold pairDistancePotential convolution
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.mul_apply']
  rw [abs_sub_comm]
  ring

/-- The auxiliary nested profile is continuous for a continuous compactly
supported base profile. -/
theorem nestedAuxProfile_continuous (r : ℝ → ℝ)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    Continuous (nestedAuxProfile r) := by
  unfold nestedAuxProfile
  exact (hr.pow 2).mul (pairDistancePotential_continuous r hr hrc)

/-- The auxiliary nested profile is supported wherever the base profile is
supported. -/
theorem nestedAuxProfile_hasCompactSupport (r : ℝ → ℝ)
    (hrc : HasCompactSupport r) : HasCompactSupport (nestedAuxProfile r) := by
  unfold nestedAuxProfile
  apply hrc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  by_contra hr0
  simp [hr0] at hx

/-- Continuous compact support also discharges the distance-kernel premise
used to exchange the two nested variables. -/
theorem nestedDistanceKernel_integrable_of_continuous_compact
    (r : ℝ → ℝ) (hr : Continuous r) (hrc : HasCompactSupport r) :
    Integrable (distanceKernel r (nestedAuxProfile r)) :=
  distanceKernel_integrable_of_continuous_compact r (nestedAuxProfile r)
    hr (nestedAuxProfile_continuous r hr hrc) hrc
    (nestedAuxProfile_hasCompactSupport r hrc)

/-- A continuous compactly supported profile discharges the separated
three-variable Fubini premise. -/
theorem separatedTwoPairFubiniKernel_integrable_of_continuous_compact
    (mu : ℝ) (r : ℝ → ℝ) (hmu : mu ≠ 0)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    Integrable (separatedTwoPairFubiniKernel mu r) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold separatedTwoPairFubiniKernel
    fun_prop
  · let F : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p =>
      ((mu * (p.1.1 - p.2), mu * (p.1.2 - p.2)), p.2)
    apply HasCompactSupport.intro
      (((hrc.isCompact.prod hrc.isCompact).prod hrc.isCompact).image
        (by fun_prop : Continuous F))
    intro z hz
    by_cases hx : r z.2 = 0
    · simp [separatedTwoPairFubiniKernel, hx]
    by_cases hy : r (z.2 + z.1.1 / mu) = 0
    · simp [separatedTwoPairFubiniKernel, hy]
    by_cases hw : r (z.2 + z.1.2 / mu) = 0
    · simp [separatedTwoPairFubiniKernel, hw]
    exfalso
    apply hz
    refine ⟨((z.2 + z.1.1 / mu, z.2 + z.1.2 / mu), z.2), ?_, ?_⟩
    · exact ⟨⟨subset_tsupport r hy, subset_tsupport r hw⟩,
        subset_tsupport r hx⟩
    · dsimp only [F]
      ext <;> field_simp <;> ring

/-- A continuous compactly supported profile discharges the nested
three-variable Fubini premise. -/
theorem nestedTwoPairFubiniKernel_integrable_of_continuous_compact
    (mu : ℝ) (r : ℝ → ℝ) (hmu : mu ≠ 0)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    Integrable (nestedTwoPairFubiniKernel mu r) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold nestedTwoPairFubiniKernel
    fun_prop
  · let F : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p =>
      ((mu * (p.1.1 - p.2), mu * (p.1.2 - p.1.1)), p.2)
    apply HasCompactSupport.intro
      (((hrc.isCompact.prod hrc.isCompact).prod hrc.isCompact).image
        (by fun_prop : Continuous F))
    intro z hz
    by_cases hx : r z.2 = 0
    · simp [nestedTwoPairFubiniKernel, hx]
    by_cases hy : r (z.2 + z.1.1 / mu) = 0
    · simp [nestedTwoPairFubiniKernel, hy]
    by_cases hw : r (z.2 + (z.1.1 + z.1.2) / mu) = 0
    · simp [nestedTwoPairFubiniKernel, hw]
    exfalso
    apply hz
    refine ⟨((z.2 + z.1.1 / mu,
      z.2 + (z.1.1 + z.1.2) / mu), z.2), ?_, ?_⟩
    · exact ⟨⟨subset_tsupport r hy, subset_tsupport r hw⟩,
        subset_tsupport r hx⟩
    · dsimp only [F]
      ext <;> field_simp <;> ring

/-- A continuous compactly supported profile discharges the crossing
three-variable Fubini premise. -/
theorem crossingRawKernel_integrable_of_continuous_compact
    (mu : ℝ) (r : ℝ → ℝ) (hmu : mu ≠ 0)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    Integrable (crossingRawKernel mu r) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold crossingRawKernel
    fun_prop
  · let F : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p =>
      ((mu * (p.1.1 - p.2), mu * (p.1.2 - p.2)), p.2)
    apply HasCompactSupport.intro
      (((hrc.isCompact.prod hrc.isCompact).prod hrc.isCompact).image
        (by fun_prop : Continuous F))
    intro z hz
    by_cases hx : r z.2 = 0
    · simp [crossingRawKernel, hx]
    by_cases hy : r (z.2 + z.1.1 / mu) = 0
    · simp [crossingRawKernel, hy]
    by_cases hw : r (z.2 + z.1.2 / mu) = 0
    · simp [crossingRawKernel, hw]
    exfalso
    apply hz
    refine ⟨((z.2 + z.1.1 / mu, z.2 + z.1.2 / mu), z.2), ?_, ?_⟩
    · exact ⟨⟨subset_tsupport r hy, subset_tsupport r hw⟩,
        subset_tsupport r hx⟩
    · dsimp only [F]
      ext <;> field_simp <;> ring

private theorem crossingSlice_eq (mu x : ℝ) (r : ℝ → ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (fun p : ℝ × ℝ => crossingRawKernel mu r (p, x))) :
    (∫ p : ℝ × ℝ, crossingRawKernel mu r (p, x)) =
      mu ^ 5 * (r x * ∫ y : ℝ, |y - x| * r y *
        ∫ z : ℝ, |z - y| * r z * r (x + z - y)) := by
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  calc
    (∫ u : ℝ, ∫ v : ℝ, crossingRawKernel mu r ((u, v), x)) =
        ∫ u : ℝ, mu * r x * |u| *
          (∫ v : ℝ, |v| *
            (r (x + u / mu) * r (x + (u + v) / mu) *
              r (x + v / mu))) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [crossingRawKernel]
      ring
    _ = ∫ u : ℝ, mu ^ 3 * r x * |u| *
          (r (x + u / mu) *
            ∫ z : ℝ, |z - (x + u / mu)| * r z *
              r (x + z - (x + u / mu))) := by
      apply integral_congr_ae
      filter_upwards [] with u
      let f : ℝ → ℝ := fun z => r z * r (x + z - (x + u / mu))
      have hv := integral_abs_mul_shift_div mu (x + u / mu) f hmu
      have harg (v : ℝ) :
          f (x + u / mu + v / mu) =
            r (x + (u + v) / mu) * r (x + v / mu) := by
        dsimp only [f]
        congr 2
        · field_simp [hmu.ne']
          ring
        · field_simp [hmu.ne']
          ring
      rw [show (∫ v : ℝ, |v| *
          (r (x + u / mu) * r (x + (u + v) / mu) * r (x + v / mu))) =
          r (x + u / mu) * ∫ v : ℝ, |v| * f (x + u / mu + v / mu) by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with v
        rw [harg v]
        ring]
      rw [hv]
      dsimp only [f]
      ring_nf
    _ = mu ^ 5 * (r x * ∫ y : ℝ, |y - x| * r y *
          ∫ z : ℝ, |z - y| * r z * r (x + z - y)) := by
      let f : ℝ → ℝ := fun y => r y *
        ∫ z : ℝ, |z - y| * r z * r (x + z - y)
      have hu := integral_abs_mul_shift_div mu x f hmu
      rw [show (∫ u : ℝ, mu ^ 3 * r x * |u| *
          (r (x + u / mu) *
            ∫ z : ℝ, |z - (x + u / mu)| * r z *
              r (x + z - (x + u / mu)))) =
          mu ^ 3 * r x * ∫ u : ℝ, |u| * f (x + u / mu) by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with u
        dsimp only [f]
        ring]
      rw [hu]
      dsimp only [f]
      have hi :
          (∫ y : ℝ, |y - x| *
            (r y * ∫ z : ℝ, |z - y| * r z * r (x + z - y))) =
          ∫ y : ℝ, |y - x| * r y *
            ∫ z : ℝ, |z - y| * r z * r (x + z - y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      rw [hi]
      ring

/-- The crossing two-pair coordinate integral is `mu ^ 5` times the exact
formula-(27) crossing functional. -/
theorem crossingTwoPairCoordinateIntegral_eq (mu : ℝ) (r : ℝ → ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (crossingRawKernel mu r)) :
    twoPairCoordinateIntegral (crossingTwoPairCore mu r) =
      mu ^ 5 * crossingFunctional r := by
  have hswap :
      (∫ p : ℝ × ℝ, ∫ x : ℝ, crossingRawKernel mu r (p, x)) =
        ∫ x : ℝ, ∫ p : ℝ × ℝ, crossingRawKernel mu r (p, x) := by
    exact integral_integral_swap hint
  calc
    twoPairCoordinateIntegral (crossingTwoPairCore mu r) =
        ∫ p : ℝ × ℝ, ∫ x : ℝ, crossingRawKernel mu r (p, x) := by
      unfold twoPairCoordinateIntegral crossingTwoPairCore
      apply integral_congr_ae
      filter_upwards [] with p
      calc
        |p.1| * |p.2| * (mu * ∫ x : ℝ,
            r x * r (x + p.1 / mu) * r (x + (p.1 + p.2) / mu) *
              r (x + p.2 / mu)) =
            (|p.1| * |p.2| * mu) * ∫ x : ℝ,
              r x * r (x + p.1 / mu) * r (x + (p.1 + p.2) / mu) *
                r (x + p.2 / mu) := by ring
        _ = ∫ x : ℝ, (|p.1| * |p.2| * mu) *
              (r x * r (x + p.1 / mu) * r (x + (p.1 + p.2) / mu) *
                r (x + p.2 / mu)) := by
          rw [integral_const_mul]
        _ = ∫ x : ℝ, crossingRawKernel mu r (p, x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [crossingRawKernel]
          ring
    _ = ∫ x : ℝ, ∫ p : ℝ × ℝ, crossingRawKernel mu r (p, x) := hswap
    _ = ∫ x : ℝ, mu ^ 5 * (r x * ∫ y : ℝ, |y - x| * r y *
          ∫ z : ℝ, |z - y| * r z * r (x + z - y)) := by
      apply integral_congr_ae
      filter_upwards [hint.prod_left_ae] with x hx
      exact crossingSlice_eq mu x r hmu hx
    _ = mu ^ 5 * crossingFunctional r := by
      rw [integral_const_mul]
      rfl

/-- The separated RS contraction is exactly its displayed two-coordinate
integral. -/
theorem rsPairIntegral_k4_separated_coordinate (mu : ℝ) (r : ℝ → ℝ) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4), ↑(2 : Fin 4)],
          ![↑(1 : Fin 4), ↑(3 : Fin 4)]) =
      (twoPairCoordinateIntegral (separatedTwoPairCore mu r) : ℝ) := by
  apply rsPairIntegral_two_eq_coordinate
  intro u v
  unfold separatedTwoPairCore
  have h := weightedCyclicSymbol_k4_separated mu r ![u, v]
  norm_num at h
  simpa only [Complex.ofReal_mul] using h

/-- The nested RS contraction is exactly its displayed two-coordinate
integral. -/
theorem rsPairIntegral_k4_nested_coordinate (mu : ℝ) (r : ℝ → ℝ) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4), ↑(1 : Fin 4)],
          ![↑(3 : Fin 4), ↑(2 : Fin 4)]) =
      (twoPairCoordinateIntegral (nestedTwoPairCore mu r) : ℝ) := by
  apply rsPairIntegral_two_eq_coordinate
  intro u v
  unfold nestedTwoPairCore
  have h := weightedCyclicSymbol_k4_nested mu r ![u, v]
  norm_num at h
  simpa only [Complex.ofReal_mul] using h

/-- The crossing RS contraction is exactly its displayed two-coordinate
integral. -/
theorem rsPairIntegral_k4_crossing_coordinate (mu : ℝ) (r : ℝ → ℝ) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4), ↑(1 : Fin 4)],
          ![↑(2 : Fin 4), ↑(3 : Fin 4)]) =
      (twoPairCoordinateIntegral (crossingTwoPairCore mu r) : ℝ) := by
  apply rsPairIntegral_two_eq_coordinate
  intro u v
  unfold crossingTwoPairCore
  have h := weightedCyclicSymbol_k4_crossing mu r ![u, v]
  norm_num at h
  simpa only [Complex.ofReal_mul] using h

/-- Exact unnormalized evaluation of the separated degree-four
two-pair contraction. -/
theorem rsPairIntegral_k4_separated_eq (mu : ℝ) (r : ℝ → ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (separatedTwoPairFubiniKernel mu r)) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4), ↑(2 : Fin 4)],
          ![↑(1 : Fin 4), ↑(3 : Fin 4)]) =
      (mu ^ 5 * pairSquaredPotentialIntegral r : ℝ) := by
  rw [rsPairIntegral_k4_separated_coordinate,
    separatedTwoPairCoordinateIntegral_eq mu r hmu hint]

/-- Exact unnormalized evaluation of the nested degree-four
two-pair contraction. -/
theorem rsPairIntegral_k4_nested_eq (mu : ℝ) (r : ℝ → ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (nestedTwoPairFubiniKernel mu r))
    (hdist : Integrable (distanceKernel r (nestedAuxProfile r))) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4), ↑(1 : Fin 4)],
          ![↑(3 : Fin 4), ↑(2 : Fin 4)]) =
      (mu ^ 5 * pairSquaredPotentialIntegral r : ℝ) := by
  rw [rsPairIntegral_k4_nested_coordinate,
    nestedTwoPairCoordinateIntegral_eq mu r hmu hint hdist]

/-- Exact unnormalized evaluation of the crossing degree-four
two-pair contraction. -/
theorem rsPairIntegral_k4_crossing_eq (mu : ℝ) (r : ℝ → ℝ)
    (hmu : 0 < mu)
    (hint : Integrable (crossingRawKernel mu r)) :
    rsPairIntegral (weightedCyclicSymbol (k := 4) mu r)
        (![↑(0 : Fin 4), ↑(1 : Fin 4)],
          ![↑(2 : Fin 4), ↑(3 : Fin 4)]) =
      (mu ^ 5 * crossingFunctional r : ℝ) := by
  rw [rsPairIntegral_k4_crossing_coordinate,
    crossingTwoPairCoordinateIntegral_eq mu r hmu hint]

def normalizedRSMainTerm {n : ℕ} (mu : ℝ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ) : ℂ :=
  rsMainTerm Phi / (mu : ℂ)

theorem normalizedRSMainTerm_k1 (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu) :
    normalizedRSMainTerm mu (weightedCyclicSymbol (k := 1) mu r) =
      ((∫ x : ℝ, r x) : ℝ) := by
  rw [normalizedRSMainTerm, RSReduction.rsMainTerm_k1,
    RSReduction.weightedCyclicSymbol_zero]
  norm_cast
  field_simp [hmu.ne']

theorem normalizedRSMainTerm_k2 (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hint : Integrable (onePairIntegrand mu r r)) :
    normalizedRSMainTerm mu (weightedCyclicSymbol (k := 2) mu r) =
      ((∫ x : ℝ, r x ^ 2) + mu ^ 2 * distanceIntegral r r : ℝ) := by
  rw [normalizedRSMainTerm, RSReduction.rsMainTerm_k2,
    RSReduction.weightedCyclicSymbol_zero,
    rsPairIntegral_k2_distance mu r hmu hint]
  norm_cast
  field_simp [hmu.ne']

theorem normalizedRSMainTerm_k3 (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (h21 : Integrable (onePairIntegrand mu (fun x => r x ^ 2) r))
    (h12 : Integrable (onePairIntegrand mu r (fun x => r x ^ 2)))
    (hdist : Integrable (distanceKernel (fun x => r x ^ 2) r)) :
    normalizedRSMainTerm mu (weightedCyclicSymbol (k := 3) mu r) =
      ((∫ x : ℝ, r x ^ 3) +
        3 * mu ^ 2 * distanceIntegral (fun x => r x ^ 2) r : ℝ) := by
  rw [normalizedRSMainTerm, RSReduction.rsMainTerm_k3,
    RSReduction.weightedCyclicSymbol_zero,
    rsPairIntegral_k3_01_distance mu r hmu h21,
    rsPairIntegral_k3_02_distance mu r hmu h12,
    rsPairIntegral_k3_12_distance mu r hmu h21,
    ← distanceIntegral_comm (fun x => r x ^ 2) r hdist]
  norm_cast
  field_simp [hmu.ne']
  ring

/-- Formula (27) in degree four, with every one- and two-pair contraction
evaluated and the RS main term divided by the block fraction `mu`. -/
theorem normalizedRSMainTerm_k4 (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (h31 : Integrable (onePairIntegrand mu (fun x => r x ^ 3) r))
    (h13 : Integrable (onePairIntegrand mu r (fun x => r x ^ 3)))
    (h22 : Integrable
      (onePairIntegrand mu (fun x => r x ^ 2) (fun x => r x ^ 2)))
    (hdist31 : Integrable (distanceKernel (fun x => r x ^ 3) r))
    (hseparated : Integrable (separatedTwoPairFubiniKernel mu r))
    (hnested : Integrable (nestedTwoPairFubiniKernel mu r))
    (hdistNested : Integrable (distanceKernel r (nestedAuxProfile r)))
    (hcrossing : Integrable (crossingRawKernel mu r)) :
    normalizedRSMainTerm mu (weightedCyclicSymbol (k := 4) mu r) =
      ((∫ x : ℝ, r x ^ 4) +
        mu ^ 2 * (4 * distanceIntegral (fun x => r x ^ 3) r +
          2 * distanceIntegral (fun x => r x ^ 2) (fun x => r x ^ 2)) +
        mu ^ 4 * (2 * pairSquaredPotentialIntegral r + crossingFunctional r) : ℝ) := by
  rw [normalizedRSMainTerm, RSReduction.rsMainTerm_k4,
    RSReduction.weightedCyclicSymbol_zero,
    rsPairIntegral_k4_01_distance mu r hmu h31,
    rsPairIntegral_k4_02_distance mu r hmu h22,
    rsPairIntegral_k4_03_distance mu r hmu h13,
    rsPairIntegral_k4_12_distance mu r hmu h31,
    rsPairIntegral_k4_13_distance mu r hmu h22,
    rsPairIntegral_k4_23_distance mu r hmu h31,
    rsPairIntegral_k4_crossing_eq mu r hmu hcrossing,
    rsPairIntegral_k4_nested_eq mu r hmu hnested hdistNested,
    rsPairIntegral_k4_separated_eq mu r hmu hseparated,
    ← distanceIntegral_comm (fun x => r x ^ 3) r hdist31]
  norm_cast
  field_simp [hmu.ne']
  ring

/-! ## Usable continuous compact-support specialization -/

/-- Degree two with all analytic integrability premises derived from a
continuous compactly supported profile. -/
theorem normalizedRSMainTerm_k2_of_continuous_compactSupport
    (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    normalizedRSMainTerm mu (weightedCyclicSymbol (k := 2) mu r) =
      ((∫ x : ℝ, r x ^ 2) + mu ^ 2 * distanceIntegral r r : ℝ) :=
  normalizedRSMainTerm_k2 mu r hmu
    (onePairIntegrand_integrable_of_continuous_compact mu r r hmu.ne'
      hr hr hrc hrc)

/-- Degree three with all analytic integrability premises derived from a
continuous compactly supported profile. -/
theorem normalizedRSMainTerm_k3_of_continuous_compactSupport
    (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    normalizedRSMainTerm mu (weightedCyclicSymbol (k := 3) mu r) =
      ((∫ x : ℝ, r x ^ 3) +
        3 * mu ^ 2 * distanceIntegral (fun x => r x ^ 2) r : ℝ) :=
  normalizedRSMainTerm_k3 mu r hmu
    (onePairIntegrand_integrable_of_continuous_compact mu
      (fun x => r x ^ 2) r hmu.ne' (hr.pow 2) hr
      (positivePower_hasCompactSupport r 2 (by norm_num) hrc) hrc)
    (onePairIntegrand_integrable_of_continuous_compact mu r
      (fun x => r x ^ 2) hmu.ne' hr (hr.pow 2) hrc
      (positivePower_hasCompactSupport r 2 (by norm_num) hrc))
    (distanceKernel_integrable_of_continuous_compact
      (fun x => r x ^ 2) r (hr.pow 2) hr
      (positivePower_hasCompactSupport r 2 (by norm_num) hrc) hrc)

/-- Degree four, including all three two-pair evaluations, with every
literal integrability premise derived from continuity and compact support. -/
theorem normalizedRSMainTerm_k4_of_continuous_compactSupport
    (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    normalizedRSMainTerm mu (weightedCyclicSymbol (k := 4) mu r) =
      ((∫ x : ℝ, r x ^ 4) +
        mu ^ 2 * (4 * distanceIntegral (fun x => r x ^ 3) r +
          2 * distanceIntegral (fun x => r x ^ 2) (fun x => r x ^ 2)) +
        mu ^ 4 * (2 * pairSquaredPotentialIntegral r + crossingFunctional r) : ℝ) :=
  normalizedRSMainTerm_k4 mu r hmu
    (onePairIntegrand_integrable_of_continuous_compact mu
      (fun x => r x ^ 3) r hmu.ne' (hr.pow 3) hr
      (positivePower_hasCompactSupport r 3 (by norm_num) hrc) hrc)
    (onePairIntegrand_integrable_of_continuous_compact mu r
      (fun x => r x ^ 3) hmu.ne' hr (hr.pow 3) hrc
      (positivePower_hasCompactSupport r 3 (by norm_num) hrc))
    (onePairIntegrand_integrable_of_continuous_compact mu
      (fun x => r x ^ 2) (fun x => r x ^ 2) hmu.ne' (hr.pow 2) (hr.pow 2)
      (positivePower_hasCompactSupport r 2 (by norm_num) hrc)
      (positivePower_hasCompactSupport r 2 (by norm_num) hrc))
    (distanceKernel_integrable_of_continuous_compact
      (fun x => r x ^ 3) r (hr.pow 3) hr
      (positivePower_hasCompactSupport r 3 (by norm_num) hrc) hrc)
    (separatedTwoPairFubiniKernel_integrable_of_continuous_compact
      mu r hmu.ne' hr hrc)
    (nestedTwoPairFubiniKernel_integrable_of_continuous_compact
      mu r hmu.ne' hr hrc)
    (nestedDistanceKernel_integrable_of_continuous_compact r hr hrc)
    (crossingRawKernel_integrable_of_continuous_compact mu r hmu.ne' hr hrc)


/-! ## Concrete quartic scalar carried by the frozen smooth test -/

/-- The real scalar appearing in the normalized quartic RS main term. -/
def quarticRSScalar (mu : ℝ) (r : ℝ -> ℝ) : ℝ :=
  (∫ x : ℝ, r x ^ 4) +
    mu ^ 2 * (4 * distanceIntegral (fun x => r x ^ 3) r +
      2 * distanceIntegral (fun x => r x ^ 2) (fun x => r x ^ 2)) +
    mu ^ 4 * (2 * pairSquaredPotentialIntegral r + crossingFunctional r)

/-- The normalized quartic main term is exactly the displayed real
contraction scalar. -/
theorem normalizedRSMainTerm_k4_eq_quarticRSScalar
    (mu : ℝ) (r : ℝ -> ℝ) (hmu : 0 < mu)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    normalizedRSMainTerm mu (weightedCyclicSymbol (k := 4) mu r) =
      (quarticRSScalar mu r : ℝ) := by
  simpa only [quarticRSScalar] using
    normalizedRSMainTerm_k4_of_continuous_compactSupport mu r hmu hr hrc

/-- Undoing the normalization exposes the literal scalar multiplying the
height factor in the four-point theorem. -/
theorem rsMainTerm_k4_eq_mu_mul_quarticRSScalar
    (mu : ℝ) (r : ℝ -> ℝ) (hmu : 0 < mu)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    rsMainTerm (weightedCyclicSymbol (k := 4) mu r) =
      (mu * quarticRSScalar mu r : ℝ) := by
  have h :=
    normalizedRSMainTerm_k4_eq_quarticRSScalar mu r hmu hr hrc
  change rsMainTerm (weightedCyclicSymbol (k := 4) mu r) / (mu : ℂ) =
    (quarticRSScalar mu r : ℂ) at h
  have hmuC : (mu : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hmu.ne'
  have hm := (div_eq_iff hmuC).mp h
  simpa [mul_comm] using hm

/-- The literal profile used by the frozen strict-support construction has a
fully evaluated quartic RS main term. -/
theorem unitIntervalProfile_rsMainTerm :
    rsMainTerm
        (weightedCyclicSymbol (k := 4) (4999 / 10000 : ℝ)
          unitIntervalProfile) =
      ((4999 / 10000 : ℝ) *
        quarticRSScalar (4999 / 10000 : ℝ) unitIntervalProfile : ℝ) := by
  apply rsMainTerm_k4_eq_mu_mul_quarticRSScalar
  · norm_num
  · exact unitIntervalProfile_contDiff.continuous
  · exact unitIntervalProfile_hasCompactSupport

/-- The four-point RS theorem for the frozen smooth test, with its main term
rewritten as the concrete quartic contraction scalar. -/
theorem RS1996ZetaInputs.unitIntervalQuartic_evaluated
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
          (((4999 / 10000 : ℝ) *
            quarticRSScalar (4999 / 10000 : ℝ)
              unitIntervalProfile : ℝ) : ℂ)‖ ≤ C * T := by
  obtain ⟨C, T0, hC, hT0, hRS⟩ := RSReduction.RS1996ZetaInputs.unitIntervalQuartic hrs g hg
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT
  obtain ⟨hSummable, hBound⟩ := hRS T hT
  refine ⟨hSummable, ?_⟩
  rw [unitIntervalProfile_rsMainTerm] at hBound
  exact hBound


/-- The four-point theorem for an arbitrary smooth unit-interval profile,
with the main term completely reduced to the quartic contraction scalar. -/
theorem RS1996ZetaInputs.frozenQuartic_evaluated
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
          (((4999 / 10000 : ℝ) *
            quarticRSScalar (4999 / 10000 : ℝ) r : ℝ) : ℂ)‖ ≤ C * T := by
  obtain ⟨C, T0, hC, hT0, hRS⟩ :=
    RSReduction.RS1996ZetaInputs.frozenQuartic hrs r hrc hrSmooth hrSupport g hg
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT
  obtain ⟨hSummable, hBound⟩ := hRS T hT
  refine ⟨hSummable, ?_⟩
  rw [rsMainTerm_k4_eq_mu_mul_quarticRSScalar
    (4999 / 10000 : ℝ) r (by norm_num)
    hrSmooth.continuous hrc] at hBound
  exact hBound

/-! ## Exact sharp top-hat contractions -/

open RSReduction TopHatMoments

theorem integral_topHat_pow_univ {p : ℝ} {k : ℕ}
    (hp : 0 < p) (hk : k ≠ 0) :
    (∫ x : ℝ, topHat p x ^ k) = p * (1 / p) ^ k := by
  have heq : (fun x : ℝ => topHat p x ^ k) =
      (topHatSupport p).indicator (fun _ => (1 / p) ^ k) := by
    funext x
    by_cases hx : x ∈ topHatSupport p
    · simp [topHat, hx]
    · simp [topHat, hx, hk]
  rw [heq]
  unfold topHatSupport
  rw [integral_indicator_const _ measurableSet_Icc]
  rw [Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
  ring

theorem integral_topHat_univ {p : ℝ} (hp : 0 < p) :
    (∫ x : ℝ, topHat p x) = 1 := by
  rw [show (fun x : ℝ => topHat p x) = fun x => topHat p x ^ 1 by
    funext x; simp]
  rw [integral_topHat_pow_univ hp (by norm_num)]
  field_simp [ne_of_gt hp]

theorem pairDistancePotential_topHat {p : ℝ} (hp : 0 < p) (x : ℝ) :
    pairDistancePotential (topHat p) x = distancePotential p x := by
  have heq : (fun y : ℝ => |y - x| * topHat p y) =
      (topHatSupport p).indicator (fun y => |y - x| * (1 / p)) := by
    funext y
    by_cases hy : y ∈ topHatSupport p
    · simp [topHat, hy]
    · simp [topHat, hy]
  unfold pairDistancePotential
  rw [heq]
  unfold topHatSupport distancePotential
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc]
  simpa [abs_sub_comm, div_eq_mul_inv] using
    (intervalIntegral.integral_of_le (μ := MeasureTheory.volume)
      (a := -p / 2) (b := p / 2)
      (f := fun y : ℝ => |y - x| * (1 / p)) (by linarith)).symm

theorem distanceIntegral_topHat {p : ℝ} (hp : 0 < p) :
    distanceIntegral (topHat p) (topHat p) = rDistanceIntegral p := by
  unfold distanceIntegral
  change (∫ x : ℝ,
    topHat p x * pairDistancePotential (topHat p) x) = rDistanceIntegral p
  simp_rw [pairDistancePotential_topHat hp]
  have heq : (fun x : ℝ => topHat p x * distancePotential p x) =
      (topHatSupport p).indicator
        (fun x => (1 / p) * distancePotential p x) := by
    funext x
    by_cases hx : x ∈ topHatSupport p
    · simp [topHat, hx]
    · simp [topHat, hx]
  rw [heq]
  unfold topHatSupport rDistanceIntegral
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc]
  simpa using
    (intervalIntegral.integral_of_le (μ := MeasureTheory.volume)
      (a := -p / 2) (b := p / 2)
      (f := fun x : ℝ => (1 / p) * distancePotential p x)
        (by linarith)).symm

theorem pairSquaredPotential_topHat {p : ℝ} (hp : 0 < p) :
    pairSquaredPotentialIntegral (topHat p) = squaredPotentialIntegral p := by
  unfold pairSquaredPotentialIntegral
  simp_rw [pairDistancePotential_topHat hp]
  have heq :
      (fun x : ℝ => topHat p x ^ 2 * distancePotential p x ^ 2) =
        (topHatSupport p).indicator
          (fun x => (1 / p) ^ 2 * distancePotential p x ^ 2) := by
    funext x
    by_cases hx : x ∈ topHatSupport p
    · simp [topHat, hx]
    · simp [topHat, hx]
  rw [heq]
  unfold topHatSupport squaredPotentialIntegral
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (μ := MeasureTheory.volume)
    (a := -p / 2) (b := p / 2)
    (f := fun x : ℝ => (1 / p) ^ 2 * distancePotential p x ^ 2)
      (by linarith)]

theorem distanceIntegral_const_mul_left (c : ℝ) (f g : ℝ → ℝ) :
    distanceIntegral (fun x => c * f x) g = c * distanceIntegral f g := by
  unfold distanceIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem distanceIntegral_const_mul_right (c : ℝ) (f g : ℝ → ℝ) :
    distanceIntegral f (fun x => c * g x) = c * distanceIntegral f g := by
  unfold distanceIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hinner : (∫ y : ℝ, |y - x| * (c * g y)) =
      c * ∫ y : ℝ, |y - x| * g y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [hinner]
  ring

theorem topHat_pow_eq_mul {p : ℝ} {k : ℕ} (hk : 0 < k) (x : ℝ) :
    topHat p x ^ k = (1 / p) ^ (k - 1) * topHat p x := by
  cases k with
  | zero => omega
  | succ k =>
      by_cases hx : x ∈ topHatSupport p
      · simp [topHat, hx, pow_succ]
      · simp [topHat, hx]

theorem distanceIntegral_topHat_powers {p : ℝ} (hp : 0 < p)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    distanceIntegral (fun x => topHat p x ^ a) (fun x => topHat p x ^ b) =
      (1 / p) ^ (a - 1) * (1 / p) ^ (b - 1) * rDistanceIntegral p := by
  simp_rw [topHat_pow_eq_mul ha, topHat_pow_eq_mul hb]
  rw [distanceIntegral_const_mul_left,
    distanceIntegral_const_mul_right,
    distanceIntegral_topHat hp]
  ring

theorem distanceIntegral_topHat_power_left {p : ℝ} (hp : 0 < p)
    {a : ℕ} (ha : 0 < a) :
    distanceIntegral (fun x => topHat p x ^ a) (topHat p) =
      (1 / p) ^ (a - 1) * rDistanceIntegral p := by
  simpa only [pow_one, Nat.reduceSub, pow_zero, mul_one] using
    (distanceIntegral_topHat_powers (p := p) hp
      (a := a) (b := 1) ha (by norm_num))

theorem integral_eq_baseInterval_of_eq_zero_outside
    (f : ℝ → ℝ)
    (hzero : ∀ x ∉ baseWindow, f x = 0) :
    (∫ x : ℝ, f x) =
      ∫ x in (-(1 : ℝ) / 2)..(1 / 2), f x := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  unfold baseWindow
  rw [integral_Icc_eq_integral_Ioc]
  simpa using
    (intervalIntegral.integral_of_le (μ := MeasureTheory.volume)
      (a := (-(1 : ℝ) / 2)) (b := (1 / 2)) (f := f) (by norm_num)).symm

theorem topHat_eq_zero_outside_base {p x : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hx : x ∉ baseWindow) :
    topHat p x = 0 := by
  have hnot : x ∉ topHatSupport p := by
    intro hxsupp
    apply hx
    unfold topHatSupport at hxsupp
    unfold baseWindow
    constructor <;> linarith [hxsupp.1, hxsupp.2]
  rw [topHat, Set.indicator_of_notMem hnot]

theorem baseIndicator_topHat {p A w : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    baseWindow.indicator (fun z => A * topHat p z) w = A * topHat p w := by
  by_cases hw : w ∈ baseWindow
  · rw [Set.indicator_of_mem hw]
  · rw [Set.indicator_of_notMem hw, topHat_eq_zero_outside_base hp hp1 hw,
      mul_zero]

theorem crossingFunctional_topHat {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    crossingFunctional (topHat p) = formulaCrossingIntegral p := by
  unfold crossingFunctional formulaCrossingIntegral
  calc
    (∫ x : ℝ, topHat p x *
        ∫ y : ℝ, |y - x| * topHat p y *
          ∫ z : ℝ, |z - y| * topHat p z * topHat p (x + z - y)) =
      ∫ x in (-(1 : ℝ) / 2)..(1 / 2), topHat p x *
        ∫ y : ℝ, |y - x| * topHat p y *
          ∫ z : ℝ, |z - y| * topHat p z * topHat p (x + z - y) := by
      apply integral_eq_baseInterval_of_eq_zero_outside
      intro x hx
      rw [topHat_eq_zero_outside_base hp hp1 hx, zero_mul]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      calc
        topHat p x *
            ∫ y : ℝ, |y - x| * topHat p y *
              ∫ z : ℝ, |z - y| * topHat p z * topHat p (x + z - y) =
          ∫ y : ℝ, topHat p x *
            (|y - x| * topHat p y *
              ∫ z : ℝ, |z - y| * topHat p z * topHat p (x + z - y)) := by
            rw [integral_const_mul]
        _ = ∫ y in (-(1 : ℝ) / 2)..(1 / 2), topHat p x *
            (|y - x| * topHat p y *
              ∫ z : ℝ, |z - y| * topHat p z * topHat p (x + z - y)) := by
          apply integral_eq_baseInterval_of_eq_zero_outside
          intro y hy
          rw [topHat_eq_zero_outside_base hp hp1 hy]
          ring
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro y hy
          calc
            topHat p x * (|y - x| * topHat p y *
                ∫ z : ℝ, |z - y| * topHat p z * topHat p (x + z - y)) =
              ∫ z : ℝ,
                (topHat p x * |y - x| * topHat p y) *
                  (|z - y| * topHat p z * topHat p (x + z - y)) := by
              rw [integral_const_mul]
              ring
            _ = ∫ z in (-(1 : ℝ) / 2)..(1 / 2),
                (topHat p x * |y - x| * topHat p y) *
                  (|z - y| * topHat p z * topHat p (x + z - y)) := by
              apply integral_eq_baseInterval_of_eq_zero_outside
              intro z hz
              rw [topHat_eq_zero_outside_base hp hp1 hz]
              ring
            _ = _ := by
              apply intervalIntegral.integral_congr
              intro z hz
              change _ = baseWindow.indicator
                (fun w =>
                  (|x - y| * |y - z| * topHat p x * topHat p y *
                    topHat p z) * topHat p w) (x + z - y)
              rw [baseIndicator_topHat (p := p) (hp := hp)
                (hp1 := hp1)]
              change topHat p x * |y - x| * topHat p y *
                    (|z - y| * topHat p z * topHat p (x + z - y)) =
                  |x - y| * |y - z| * topHat p x * topHat p y *
                    topHat p z * topHat p (x + z - y)
              rw [abs_sub_comm y x, abs_sub_comm z y]
              ring



/-! ## The evaluated RS theorem through degree four -/

/-- The four uncentered cyclic moments produced by the evaluated RS
contractions. -/
def cyclicUncenteredMoment (mu : ℝ) (r : ℝ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => ∫ x : ℝ, r x
  | 2 => (∫ x : ℝ, r x ^ 2) + mu ^ 2 * distanceIntegral r r
  | 3 => (∫ x : ℝ, r x ^ 3) +
      3 * mu ^ 2 * distanceIntegral (fun x => r x ^ 2) r
  | 4 => (∫ x : ℝ, r x ^ 4) +
      mu ^ 2 * (4 * distanceIntegral (fun x => r x ^ 3) r +
        2 * distanceIntegral (fun x => r x ^ 2) (fun x => r x ^ 2)) +
      mu ^ 4 * (2 * pairSquaredPotentialIntegral r + crossingFunctional r)
  | _ => 0

theorem cyclicUncenteredMoment_topHat_eq_uncenteredContractionMoment
    {p mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    cyclicUncenteredMoment mu (topHat p) k =
      uncenteredContractionMoment (topHatR3Terms p) mu k := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  interval_cases k
  · simp only [cyclicUncenteredMoment, uncenteredContractionMoment,
      topHatR3Terms]
    rw [integral_topHat_univ hp,
      centeredMoment_one hp hp1]
    field_simp [hp0]
    ring
  · simp only [cyclicUncenteredMoment, uncenteredContractionMoment,
      topHatR3Terms]
    rw [integral_topHat_pow_univ hp (by norm_num),
      distanceIntegral_topHat hp,
      centeredMoment_one hp hp1, centeredMoment_two hp hp1]
    norm_num [one_div] at *
    field_simp [hp0]
    ring
  · simp only [cyclicUncenteredMoment, uncenteredContractionMoment,
      topHatR3Terms]
    rw [integral_topHat_pow_univ hp (by norm_num),
      distanceIntegral_topHat_power_left hp (a := 2) (by norm_num),
      centeredMoment_one hp hp1, centeredMoment_two hp hp1,
      centeredMoment_three hp hp1,
      rDistanceIntegral_eq hp, qrDistanceIntegral_eq hp]
    norm_num [one_div] at *
    field_simp [hp0]
    ring
  · simp only [cyclicUncenteredMoment, uncenteredContractionMoment,
      topHatR3Terms]
    rw [integral_topHat_pow_univ hp (by norm_num),
      distanceIntegral_topHat_power_left hp (a := 3) (by norm_num),
      distanceIntegral_topHat_powers hp (a := 2) (b := 2)
        (by norm_num) (by norm_num),
      pairSquaredPotential_topHat hp,
      crossingFunctional_topHat hp hp1,
      centeredMoment_one hp hp1, centeredMoment_two hp hp1,
      centeredMoment_three hp hp1, centeredMoment_four hp hp1,
      rDistanceIntegral_eq hp, qrDistanceIntegral_eq hp,
      qSquaredRDistanceIntegral_eq hp, doubleQrDistanceIntegral_eq hp,
      squaredPotentialIntegral_eq hp, crossingReduction hp hp1,
      crossingSimplexIntegral_eq hp]
    norm_num [one_div] at *
    field_simp [hp0]
    ring

/-- One statement packages every contraction evaluation in degrees one
through four. -/
theorem normalizedRSMainTerm_eq_cyclicUncenteredMoment
    {n : ℕ} (hn : n ≤ 3) (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    normalizedRSMainTerm mu (weightedCyclicSymbol (k := n + 1) mu r) =
      (cyclicUncenteredMoment mu r (n + 1) : ℝ) := by
  interval_cases n
  · exact normalizedRSMainTerm_k1 mu r hmu
  · exact normalizedRSMainTerm_k2_of_continuous_compactSupport
      mu r hmu hr hrc
  · exact normalizedRSMainTerm_k3_of_continuous_compactSupport
      mu r hmu hr hrc
  · exact normalizedRSMainTerm_k4_of_continuous_compactSupport
      mu r hmu hr hrc

private theorem rsMainTerm_eq_mu_mul_of_normalized_eq
    {n : ℕ} {mu : ℝ} (hmu : 0 < mu)
    (Phi : (Fin (n + 1) → ℝ) → ℂ) (a : ℂ)
    (h : normalizedRSMainTerm mu Phi = a) :
    rsMainTerm Phi = (mu : ℂ) * a := by
  unfold normalizedRSMainTerm at h
  have hu := (div_eq_iff (Complex.ofReal_ne_zero.mpr hmu.ne')).mp h
  rw [hu]
  ring

theorem rsMainTerm_eq_cyclicUncenteredMoment
    {n : ℕ} (hn : n ≤ 3) (mu : ℝ) (r : ℝ → ℝ) (hmu : 0 < mu)
    (hr : Continuous r) (hrc : HasCompactSupport r) :
    rsMainTerm (weightedCyclicSymbol (k := n + 1) mu r) =
      (mu : ℂ) * (cyclicUncenteredMoment mu r (n + 1) : ℝ) := by
  apply rsMainTerm_eq_mu_mul_of_normalized_eq hmu
  exact normalizedRSMainTerm_eq_cyclicUncenteredMoment
    hn mu r hmu hr hrc

/-- The published all-tuples theorem with its main term completely evaluated
through degree four.  The compact gauge repair is absent from the conclusion
because it is exactly equal to the raw cyclic test on every consumed vector. -/
theorem theorem31_cyclicUncenteredMoment
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3) (g : Fin (n + 1) → ℝ → ℂ)
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
            ((mu : ℂ) * (cyclicUncenteredMoment mu r (n + 1) : ℝ))‖ ≤
        C * T := by
  obtain ⟨C, T₀, hC, hT₀, hmain⟩ :=
    RSReduction.RS1996ZetaInputs.theorem31_weightedCyclicSymbol
      hRS n g hg r hr hrc hrsupp hdelta hmu hbudget
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T hT
  simpa only [rsMainTerm_eq_cyclicUncenteredMoment
    hn mu r hmu hr.continuous hrc] using hmain T hT

end RH.Zeta85.RSPairIntegrals
