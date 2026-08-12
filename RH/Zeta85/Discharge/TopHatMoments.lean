/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/TopHatMoments.lean — actual interval-integral
calculations for the top-hat specialization of formula (21).

The first calculation starts from the integral definition of the distance
potential, not from a moment-input bridge.  The second is the two-dimensional
simplex integral obtained after the crossing change of variables.  The full
determinant-one reduction from the original four-window crossing integral is
proved separately below before the moments are assembled.
-/
import Mathlib

namespace RH
namespace Zeta85
namespace TopHatMoments

noncomputable section

/-! ## The sharp top hat and its centered scalar moments -/

/-- The unit base interval in formula (21). -/
def baseWindow : Set ℝ := Set.Icc (-(1 : ℝ) / 2) (1 / 2)

/-- The centered support interval of a top hat of width `p`. -/
def topHatSupport (p : ℝ) : Set ℝ := Set.Icc (-p / 2) (p / 2)

/-- The mean-one sharp top hat of width `p`. -/
def topHat (p x : ℝ) : ℝ :=
  (topHatSupport p).indicator (fun _ => 1 / p) x

/-- The centered top-hat symbol `q_p = r_p - 1` on the base interval. -/
def centeredTopHat (p x : ℝ) : ℝ := topHat p x - 1

/-- The actual Mathlib interval integral of the `k`th centered scalar moment. -/
def centeredMoment (k : ℕ) (p : ℝ) : ℝ :=
  ∫ x in (-(1 : ℝ) / 2)..(1 / 2), centeredTopHat p x ^ k

private theorem topHatSupport_subset_baseWindow {p : ℝ} (hp1 : p ≤ 1) :
    topHatSupport p ⊆ baseWindow := by
  intro x hx
  rw [topHatSupport, Set.mem_Icc] at hx
  rw [baseWindow, Set.mem_Icc]
  constructor <;> linarith

private theorem topHat_pow_eq_indicator {p : ℝ} {k : ℕ} (hk : k ≠ 0) (x : ℝ) :
    topHat p x ^ k =
      (topHatSupport p).indicator (fun _ => (1 / p) ^ k) x := by
  by_cases hx : x ∈ topHatSupport p
  · simp [topHat, hx]
  · simp [topHat, hx, hk]

private theorem topHat_pow_intervalIntegrable {p : ℝ} {k : ℕ} (hk : k ≠ 0)
    (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => topHat p x ^ k) MeasureTheory.volume a b := by
  have hi : MeasureTheory.Integrable
      ((topHatSupport p).indicator (fun _ : ℝ => (1 / p) ^ k)) :=
    (MeasureTheory.integrableOn_const (s := topHatSupport p)
      (by simp [topHatSupport, Real.volume_Icc])).integrable_indicator measurableSet_Icc
  exact (hi.congr (Filter.Eventually.of_forall
    (fun x => (topHat_pow_eq_indicator hk x).symm))).intervalIntegrable

/-- Every positive power of the sharp top hat has its expected exact
interval integral, `∫_I r_p^k = p(1/p)^k`. -/
theorem integral_topHat_pow {p : ℝ} {k : ℕ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hk : k ≠ 0) :
    (∫ x in (-(1 : ℝ) / 2)..(1 / 2), topHat p x ^ k) =
      p * (1 / p) ^ k := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2)]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun x _ => topHat_pow_eq_indicator hk x)]
  rw [MeasureTheory.setIntegral_indicator (t := topHatSupport p) measurableSet_Icc]
  change (∫ x in baseWindow ∩ topHatSupport p, (1 / p) ^ k) = p * (1 / p) ^ k
  rw [Set.inter_eq_right.mpr (topHatSupport_subset_baseWindow hp1)]
  rw [MeasureTheory.setIntegral_const]
  unfold topHatSupport
  rw [Real.volume_real_Icc_of_le (by linarith : -p / 2 ≤ p / 2)]
  simp only [smul_eq_mul]
  ring

/-- The sharp top hat has mean one on the base interval. -/
theorem integral_topHat {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫ x in (-(1 : ℝ) / 2)..(1 / 2), topHat p x) = 1 := by
  simpa only [pow_one, one_div, mul_inv_cancel₀ (ne_of_gt hp)] using
    (integral_topHat_pow hp hp1 (by norm_num : (1 : ℕ) ≠ 0))

/-- `∫_I q_p = 0`, from the actual sharp top-hat interval integral. -/
theorem centeredMoment_one {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    centeredMoment 1 p = 0 := by
  have h1 := topHat_pow_intervalIntegrable (p := p) (k := 1) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have h1' : IntervalIntegrable (topHat p) MeasureTheory.volume (-(1 : ℝ) / 2) (1 / 2) := by
    simpa only [pow_one] using h1
  simp only [centeredMoment, centeredTopHat, pow_one]
  rw [intervalIntegral.integral_sub h1' intervalIntegrable_const]
  rw [integral_topHat hp hp1]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp [ne_of_gt hp]
  ring

/-- `∫_I q_p² = (1-p)/p`. -/
theorem centeredMoment_two {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    centeredMoment 2 p = (1 - p) / p := by
  have h1 := topHat_pow_intervalIntegrable (p := p) (k := 1) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have h1' : IntervalIntegrable (topHat p) MeasureTheory.volume (-(1 : ℝ) / 2) (1 / 2) := by
    simpa only [pow_one] using h1
  have h2 := topHat_pow_intervalIntegrable (p := p) (k := 2) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have heq : ∀ x : ℝ, centeredTopHat p x ^ 2 =
      topHat p x ^ 2 - 2 * topHat p x + 1 := by
    intro x
    simp only [centeredTopHat]
    ring
  simp only [centeredMoment, heq]
  rw [intervalIntegral.integral_add (h2.sub (h1'.const_mul 2)) intervalIntegrable_const,
    intervalIntegral.integral_sub h2 (h1'.const_mul 2),
    intervalIntegral.integral_const_mul]
  rw [integral_topHat_pow hp hp1 (by norm_num : (2 : ℕ) ≠ 0),
    integral_topHat hp hp1]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp [ne_of_gt hp]
  ring

/-- `∫_I q_p³ = (1-p)³/p² - (1-p)`. -/
theorem centeredMoment_three {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    centeredMoment 3 p = (1 - p) ^ 3 / p ^ 2 - (1 - p) := by
  have h1 := topHat_pow_intervalIntegrable (p := p) (k := 1) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have h1' : IntervalIntegrable (topHat p) MeasureTheory.volume (-(1 : ℝ) / 2) (1 / 2) := by
    simpa only [pow_one] using h1
  have h2 := topHat_pow_intervalIntegrable (p := p) (k := 2) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have h3 := topHat_pow_intervalIntegrable (p := p) (k := 3) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have heq : ∀ x : ℝ, centeredTopHat p x ^ 3 =
      (topHat p x ^ 3 - 3 * topHat p x ^ 2) + 3 * topHat p x - 1 := by
    intro x
    simp only [centeredTopHat]
    ring
  simp only [centeredMoment, heq]
  rw [intervalIntegral.integral_sub
      ((h3.sub (h2.const_mul 3)).add (h1'.const_mul 3)) intervalIntegrable_const,
    intervalIntegral.integral_add (h3.sub (h2.const_mul 3)) (h1'.const_mul 3),
    intervalIntegral.integral_sub h3 (h2.const_mul 3),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_topHat_pow hp hp1 (by norm_num : (3 : ℕ) ≠ 0),
    integral_topHat_pow hp hp1 (by norm_num : (2 : ℕ) ≠ 0),
    integral_topHat hp hp1]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp [ne_of_gt hp]
  ring

/-- `∫_I q_p⁴ = (1-p)⁴/p³ + (1-p)`. -/
theorem centeredMoment_four {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    centeredMoment 4 p = (1 - p) ^ 4 / p ^ 3 + (1 - p) := by
  have h1 := topHat_pow_intervalIntegrable (p := p) (k := 1) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have h1' : IntervalIntegrable (topHat p) MeasureTheory.volume (-(1 : ℝ) / 2) (1 / 2) := by
    simpa only [pow_one] using h1
  have h2 := topHat_pow_intervalIntegrable (p := p) (k := 2) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have h3 := topHat_pow_intervalIntegrable (p := p) (k := 3) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have h4 := topHat_pow_intervalIntegrable (p := p) (k := 4) (by norm_num) (-(1 : ℝ) / 2) (1 / 2)
  have heq : ∀ x : ℝ, centeredTopHat p x ^ 4 =
      ((topHat p x ^ 4 - 4 * topHat p x ^ 3) + 6 * topHat p x ^ 2) -
        4 * topHat p x + 1 := by
    intro x
    simp only [centeredTopHat]
    ring
  simp only [centeredMoment, heq]
  rw [intervalIntegral.integral_add
      (((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)).sub (h1'.const_mul 4))
      intervalIntegrable_const,
    intervalIntegral.integral_sub
      ((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)) (h1'.const_mul 4),
    intervalIntegral.integral_add (h4.sub (h3.const_mul 4)) (h2.const_mul 6),
    intervalIntegral.integral_sub h4 (h3.const_mul 4),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [integral_topHat_pow hp hp1 (by norm_num : (4 : ℕ) ≠ 0),
    integral_topHat_pow hp hp1 (by norm_num : (3 : ℕ) ≠ 0),
    integral_topHat_pow hp hp1 (by norm_num : (2 : ℕ) ≠ 0),
    integral_topHat hp hp1]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp [ne_of_gt hp]
  ring

/-! ## The distance potential and the `7p/60` integral -/

/-- The distance potential of the mean-one top hat of width `p`, evaluated
at `x`.  The density `1 / p` is included in the integrand. -/
def distancePotential (p x : ℝ) : ℝ :=
  ∫ y in (-p / 2)..(p / 2), |x - y| / p

private def leftPrimitive (p x y : ℝ) : ℝ :=
  (x * y - y ^ 2 / 2) / p

private def rightPrimitive (p x y : ℝ) : ℝ :=
  (y ^ 2 / 2 - x * y) / p

private theorem hasDerivAt_leftPrimitive {p x : ℝ} (_hp : p ≠ 0) (y : ℝ) :
    HasDerivAt (leftPrimitive p x) ((x - y) / p) y := by
  have hxy : HasDerivAt (fun z : ℝ => x * z) x y := by
    simpa using (hasDerivAt_id y).const_mul x
  have h := (hxy.sub (((hasDerivAt_id y).pow 2).div_const 2)).div_const p
  norm_num [leftPrimitive, id_eq] at h ⊢
  exact h

private theorem hasDerivAt_rightPrimitive {p x : ℝ} (_hp : p ≠ 0) (y : ℝ) :
    HasDerivAt (rightPrimitive p x) ((y - x) / p) y := by
  have hxy : HasDerivAt (fun z : ℝ => x * z) x y := by
    simpa using (hasDerivAt_id y).const_mul x
  have h := ((((hasDerivAt_id y).pow 2).div_const 2).sub hxy).div_const p
  norm_num [rightPrimitive, id_eq] at h ⊢
  exact h

/-- On its support, the top-hat distance potential is the quadratic
`x²/p + p/4`. -/
theorem distancePotential_eq {p x : ℝ} (hp : 0 < p)
    (hx0 : -p / 2 ≤ x) (hx1 : x ≤ p / 2) :
    distancePotential p x = x ^ 2 / p + p / 4 := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hcont : ∀ a b : ℝ,
      IntervalIntegrable (fun y : ℝ => |x - y| / p) MeasureTheory.volume a b :=
    fun a b => (Continuous.intervalIntegrable (by fun_prop) a b)
  have hsplit :
      ∫ y in (-p / 2)..(p / 2), |x - y| / p =
        (∫ y in (-p / 2)..x, |x - y| / p) +
          ∫ y in x..(p / 2), |x - y| / p :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont _ _) (hcont _ _)).symm
  have hleft :
      ∫ y in (-p / 2)..x, |x - y| / p =
        ∫ y in (-p / 2)..x, (x - y) / p := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx0] at hy
    change |x - y| / p = (x - y) / p
    rw [abs_of_nonneg (sub_nonneg.mpr hy.2)]
  have hright :
      ∫ y in x..(p / 2), |x - y| / p =
        ∫ y in x..(p / 2), (y - x) / p := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx1] at hy
    change |x - y| / p = (y - x) / p
    rw [abs_of_nonpos (sub_nonpos.mpr hy.1), neg_sub]
  have hleftEval :
      ∫ y in (-p / 2)..x, (x - y) / p =
        leftPrimitive p x x - leftPrimitive p x (-p / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hasDerivAt_leftPrimitive hp0 y)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hrightEval :
      ∫ y in x..(p / 2), (y - x) / p =
        rightPrimitive p x (p / 2) - rightPrimitive p x x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hasDerivAt_rightPrimitive hp0 y)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [distancePotential, hsplit, hleft, hright, hleftEval, hrightEval]
  unfold leftPrimitive rightPrimitive
  field_simp [hp0]
  ring

/-- On the support, `q_p` is the constant `(1-p)/p`. -/
theorem centeredTopHat_eq_on_support {p x : ℝ} (hp : 0 < p)
    (hx : x ∈ topHatSupport p) :
    centeredTopHat p x = (1 - p) / p := by
  simp only [centeredTopHat, topHat, Set.indicator_of_mem hx]
  field_simp [ne_of_gt hp]

/-- The actual interval integral `∫ r_p h_p`. -/
def rDistanceIntegral (p : ℝ) : ℝ :=
  ∫ x in (-p / 2)..(p / 2), (1 / p) * distancePotential p x

/-- The actual interval integral `∫ q_p r_p h_p`. -/
def qrDistanceIntegral (p : ℝ) : ℝ :=
  ∫ x in (-p / 2)..(p / 2),
    centeredTopHat p x * (1 / p) * distancePotential p x

/-- The actual interval integral `∫ q_p² r_p h_p`. -/
def qSquaredRDistanceIntegral (p : ℝ) : ℝ :=
  ∫ x in (-p / 2)..(p / 2),
    centeredTopHat p x ^ 2 * (1 / p) * distancePotential p x

/-- The actual nested interval integral
`∫∫ q_p(x)r_p(x)q_p(y)r_p(y)|x-y| dx dy`. -/
def doubleQrDistanceIntegral (p : ℝ) : ℝ :=
  ∫ x in (-p / 2)..(p / 2),
    ∫ y in (-p / 2)..(p / 2),
      centeredTopHat p x * (1 / p) * centeredTopHat p y * (1 / p) * |x - y|

/-- `∫ r_p h_p = p/3`. -/
theorem rDistanceIntegral_eq {p : ℝ} (hp : 0 < p) :
    rDistanceIntegral p = p / 3 := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hpoly : rDistanceIntegral p =
      ∫ x in (-p / 2)..(p / 2), (1 / p ^ 2) * x ^ 2 + 1 / 4 := by
    unfold rDistanceIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -p / 2 ≤ p / 2)] at hx
    change (1 / p) * distancePotential p x = (1 / p ^ 2) * x ^ 2 + 1 / 4
    rw [distancePotential_eq hp hx.1 hx.2]
    field_simp [hp0]
  rw [hpoly]
  rw [intervalIntegral.integral_add
    ((intervalIntegral.intervalIntegrable_pow 2).const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    integral_pow]
  simp only [smul_eq_mul]
  field_simp [hp0]
  ring

/-- `∫ q_p r_p h_p = (1-p)/3`. -/
theorem qrDistanceIntegral_eq {p : ℝ} (hp : 0 < p) :
    qrDistanceIntegral p = (1 - p) / 3 := by
  let c : ℝ := (1 - p) / p
  calc
    qrDistanceIntegral p =
        ∫ x in (-p / 2)..(p / 2), c * ((1 / p) * distancePotential p x) := by
      unfold qrDistanceIntegral
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : -p / 2 ≤ p / 2)] at hx
      change centeredTopHat p x * (1 / p) * distancePotential p x =
        c * ((1 / p) * distancePotential p x)
      rw [centeredTopHat_eq_on_support hp (by simpa [topHatSupport] using hx)]
      dsimp [c]
      ring
    _ = c * rDistanceIntegral p := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = (1 - p) / 3 := by
      rw [rDistanceIntegral_eq hp]
      dsimp [c]
      field_simp [ne_of_gt hp]

/-- `∫ q_p² r_p h_p = (1-p)²/(3p)`. -/
theorem qSquaredRDistanceIntegral_eq {p : ℝ} (hp : 0 < p) :
    qSquaredRDistanceIntegral p = (1 - p) ^ 2 / (3 * p) := by
  let c : ℝ := (1 - p) / p
  calc
    qSquaredRDistanceIntegral p =
        ∫ x in (-p / 2)..(p / 2), c ^ 2 * ((1 / p) * distancePotential p x) := by
      unfold qSquaredRDistanceIntegral
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : -p / 2 ≤ p / 2)] at hx
      change centeredTopHat p x ^ 2 * (1 / p) * distancePotential p x =
        c ^ 2 * ((1 / p) * distancePotential p x)
      rw [centeredTopHat_eq_on_support hp (by simpa [topHatSupport] using hx)]
      dsimp [c]
      ring
    _ = c ^ 2 * rDistanceIntegral p := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = (1 - p) ^ 2 / (3 * p) := by
      rw [rDistanceIntegral_eq hp]
      dsimp [c]
      field_simp [ne_of_gt hp]

/-- The double distance term is the same scalar:
`∫∫ q_p r_p q_p r_p |x-y| = (1-p)²/(3p)`. -/
theorem doubleQrDistanceIntegral_eq {p : ℝ} (hp : 0 < p) :
    doubleQrDistanceIntegral p = (1 - p) ^ 2 / (3 * p) := by
  let c : ℝ := (1 - p) / p
  have hinner : ∀ x ∈ Set.uIcc (-p / 2) (p / 2),
      (∫ y in (-p / 2)..(p / 2),
        centeredTopHat p x * (1 / p) * centeredTopHat p y * (1 / p) * |x - y|) =
        c ^ 2 / p * distancePotential p x := by
    intro x hx
    have hxp : x ∈ topHatSupport p := by
      rw [Set.uIcc_of_le (by linarith : -p / 2 ≤ p / 2)] at hx
      simpa [topHatSupport] using hx
    calc
      (∫ y in (-p / 2)..(p / 2),
        centeredTopHat p x * (1 / p) * centeredTopHat p y * (1 / p) * |x - y|) =
          ∫ y in (-p / 2)..(p / 2), (c ^ 2 / p) * (|x - y| / p) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le (by linarith : -p / 2 ≤ p / 2)] at hy
        change centeredTopHat p x * (1 / p) * centeredTopHat p y * (1 / p) * |x - y| =
          (c ^ 2 / p) * (|x - y| / p)
        rw [centeredTopHat_eq_on_support hp hxp,
          centeredTopHat_eq_on_support hp (by simpa [topHatSupport] using hy)]
        dsimp [c]
        ring
      _ = c ^ 2 / p * distancePotential p x := by
        rw [intervalIntegral.integral_const_mul]
        rfl
  calc
    doubleQrDistanceIntegral p =
        ∫ x in (-p / 2)..(p / 2), c ^ 2 * ((1 / p) * distancePotential p x) := by
      unfold doubleQrDistanceIntegral
      apply intervalIntegral.integral_congr
      intro x hx
      change (∫ y in (-p / 2)..(p / 2),
        centeredTopHat p x * (1 / p) * centeredTopHat p y * (1 / p) * |x - y|) =
          c ^ 2 * ((1 / p) * distancePotential p x)
      rw [hinner x hx]
      ring
    _ = c ^ 2 * rDistanceIntegral p := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = (1 - p) ^ 2 / (3 * p) := by
      rw [rDistanceIntegral_eq hp]
      dsimp [c]
      field_simp [ne_of_gt hp]

/-- The complete fourth-moment `μ²` contribution in (21). -/
theorem combinedFourthMuSquared {p mu : ℝ} (hp : 0 < p) :
    4 * mu ^ 2 * qSquaredRDistanceIntegral p +
        2 * mu ^ 2 * doubleQrDistanceIntegral p =
      2 * mu ^ 2 * (1 - p) ^ 2 / p := by
  rw [qSquaredRDistanceIntegral_eq hp, doubleQrDistanceIntegral_eq hp]
  field_simp [ne_of_gt hp]
  ring

/-- The actual interval integral `∫ r_p(x)² h_p(x)² dx`; outside the
displayed interval the top-hat density is zero. -/
def squaredPotentialIntegral (p : ℝ) : ℝ :=
  ∫ x in (-p / 2)..(p / 2), (1 / p) ^ 2 * distancePotential p x ^ 2

private def squaredPotentialPrimitive (p x : ℝ) : ℝ :=
  x ^ 5 / (5 * p ^ 4) + x ^ 3 / (6 * p ^ 2) + x / 16

private theorem hasDerivAt_squaredPotentialPrimitive {p : ℝ} (_hp : p ≠ 0) (x : ℝ) :
    HasDerivAt (squaredPotentialPrimitive p)
      (x ^ 4 / p ^ 4 + x ^ 2 / (2 * p ^ 2) + 1 / 16) x := by
  have h5 := ((hasDerivAt_id x).pow 5).div_const (5 * p ^ 4)
  have h3 := ((hasDerivAt_id x).pow 3).div_const (6 * p ^ 2)
  have h1 := (hasDerivAt_id x).div_const 16
  have h := (h5.add h3).add h1
  norm_num [squaredPotentialPrimitive, id_eq] at h ⊢
  exact h.congr_deriv (by ring)

/-- The first nontrivial formula-(21) constant, proved from the nested
interval integral: `∫ r_p² h_p² = 7p/60`. -/
theorem squaredPotentialIntegral_eq {p : ℝ} (hp : 0 < p) :
    squaredPotentialIntegral p = 7 * p / 60 := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hpoly :
      squaredPotentialIntegral p =
        ∫ x in (-p / 2)..(p / 2),
          (x ^ 4 / p ^ 4 + x ^ 2 / (2 * p ^ 2) + 1 / 16) := by
    unfold squaredPotentialIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -p / 2 ≤ p / 2)] at hx
    change (1 / p) ^ 2 * distancePotential p x ^ 2 =
      x ^ 4 / p ^ 4 + x ^ 2 / (2 * p ^ 2) + 1 / 16
    rw [distancePotential_eq hp hx.1 hx.2]
    field_simp [hp0]
    ring
  rw [hpoly]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_squaredPotentialPrimitive hp0 x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  unfold squaredPotentialPrimitive
  field_simp [hp0]
  ring

/-! ## The reduced crossing integral -/

/-- The original three-dimensional crossing functional in formula (21),
specialized to the sharp top hat.  The outer three interval integrals are
over `I = [-1/2,1/2]`; the indicator is the condition
`x + z - y ∈ I`; and all four top-hat factors are present explicitly. -/
def formulaCrossingIntegral (p : ℝ) : ℝ :=
  ∫ x in (-(1 : ℝ) / 2)..(1 / 2),
    ∫ y in (-(1 : ℝ) / 2)..(1 / 2),
      ∫ z in (-(1 : ℝ) / 2)..(1 / 2),
        baseWindow.indicator
          (fun w => |x - y| * |y - z| *
            topHat p x * topHat p y * topHat p z * topHat p w)
          (x + z - y)

/-- The positive-quadrant simplex integral obtained from the crossing term
by `u = x-y`, `v = y-z`, followed by the four sign quadrants. -/
def crossingSimplexIntegral (p : ℝ) : ℝ :=
  4 / p ^ 4 *
    ∫ u in 0..p, ∫ v in 0..(p - u), u * v * (p - u - v)

private def crossingInnerPrimitive (p u v : ℝ) : ℝ :=
  u * (p - u) * v ^ 2 / 2 - u * v ^ 3 / 3

private theorem hasDerivAt_crossingInnerPrimitive (p u v : ℝ) :
    HasDerivAt (crossingInnerPrimitive p u) (u * v * (p - u - v)) v := by
  have h2 := ((hasDerivAt_id v).pow 2).const_mul (u * (p - u)) |>.div_const 2
  have h3 := ((hasDerivAt_id v).pow 3).const_mul u |>.div_const 3
  have h := h2.sub h3
  norm_num [crossingInnerPrimitive, id_eq] at h ⊢
  exact h.congr_deriv (by ring)

private def crossingOuterPrimitive (p u : ℝ) : ℝ :=
  p ^ 3 * u ^ 2 / 12 - p ^ 2 * u ^ 3 / 6 + p * u ^ 4 / 8 - u ^ 5 / 30

private theorem hasDerivAt_crossingOuterPrimitive (p u : ℝ) :
    HasDerivAt (crossingOuterPrimitive p) (u * (p - u) ^ 3 / 6) u := by
  have h2 := ((hasDerivAt_id u).pow 2).const_mul (p ^ 3) |>.div_const 12
  have h3 := ((hasDerivAt_id u).pow 3).const_mul (p ^ 2) |>.div_const 6
  have h4 := ((hasDerivAt_id u).pow 4).const_mul p |>.div_const 8
  have h5 := ((hasDerivAt_id u).pow 5).div_const 30
  have h := (((h2.sub h3).add h4).sub h5)
  norm_num [crossingOuterPrimitive, id_eq] at h ⊢
  exact h.congr_deriv (by ring)

private theorem crossing_inner_integral (p u : ℝ) :
    (∫ v in 0..(p - u), u * v * (p - u - v)) = u * (p - u) ^ 3 / 6 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_crossingInnerPrimitive p u v)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  unfold crossingInnerPrimitive
  ring

/-- The reduced crossing integral is exactly `p/30`.  This theorem is an
actual nested Mathlib interval-integral calculation. -/
theorem crossingSimplexIntegral_eq {p : ℝ} (hp : 0 < p) :
    crossingSimplexIntegral p = p / 30 := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  unfold crossingSimplexIntegral
  rw [intervalIntegral.integral_congr (fun u _ => crossing_inner_integral p u)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_crossingOuterPrimitive p u)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  unfold crossingOuterPrimitive
  field_simp [hp0]
  ring

/-! ## Exact evaluation after the determinant-one substitution -/

private def crossingLower (p u v : ℝ) : ℝ :=
  -p / 2 - min 0 u + max 0 v

private def crossingUpper (p u v : ℝ) : ℝ :=
  p / 2 - max 0 u + min 0 v

private theorem four_supports_iff {p u v y : ℝ} :
    y ∈ topHatSupport p ∧ y + u ∈ topHatSupport p ∧
        y - v ∈ topHatSupport p ∧ y + u - v ∈ topHatSupport p ↔
      y ∈ Set.Icc (crossingLower p u v) (crossingUpper p u v) := by
  rcases le_total u 0 with hu | hu <;> rcases le_total v 0 with hv | hv
  · simp only [topHatSupport, Set.mem_Icc, crossingLower, crossingUpper,
      min_eq_right hu, max_eq_left hu, min_eq_right hv, max_eq_left hv]
    constructor
    · rintro ⟨⟨hy0, hy1⟩, ⟨hyu0, hyu1⟩, ⟨hyv0, hyv1⟩, ⟨hyuv0, hyuv1⟩⟩
      constructor <;> linarith
    · rintro ⟨hy0, hy1⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩,
        ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩⟩
  · simp only [topHatSupport, Set.mem_Icc, crossingLower, crossingUpper,
      min_eq_right hu, max_eq_left hu, min_eq_left hv, max_eq_right hv]
    constructor
    · rintro ⟨⟨hy0, hy1⟩, ⟨hyu0, hyu1⟩, ⟨hyv0, hyv1⟩, ⟨hyuv0, hyuv1⟩⟩
      constructor <;> linarith
    · rintro ⟨hy0, hy1⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩,
        ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩⟩
  · simp only [topHatSupport, Set.mem_Icc, crossingLower, crossingUpper,
      min_eq_left hu, max_eq_right hu, min_eq_right hv, max_eq_left hv]
    constructor
    · rintro ⟨⟨hy0, hy1⟩, ⟨hyu0, hyu1⟩, ⟨hyv0, hyv1⟩, ⟨hyuv0, hyuv1⟩⟩
      constructor <;> linarith
    · rintro ⟨hy0, hy1⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩,
        ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩⟩
  · simp only [topHatSupport, Set.mem_Icc, crossingLower, crossingUpper,
      min_eq_left hu, max_eq_right hu, min_eq_left hv, max_eq_right hv]
    constructor
    · rintro ⟨⟨hy0, hy1⟩, ⟨hyu0, hyu1⟩, ⟨hyv0, hyv1⟩, ⟨hyuv0, hyuv1⟩⟩
      constructor <;> linarith
    · rintro ⟨hy0, hy1⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩,
        ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩⟩

private theorem crossing_length (p u v : ℝ) :
    crossingUpper p u v - crossingLower p u v = p - |u| - |v| := by
  rcases le_total u 0 with hu | hu <;> rcases le_total v 0 with hv | hv
  · rw [abs_of_nonpos hu, abs_of_nonpos hv]
    simp [crossingLower, crossingUpper, min_eq_right hu, max_eq_left hu,
      min_eq_right hv, max_eq_left hv]
    ring
  · rw [abs_of_nonpos hu, abs_of_nonneg hv]
    simp [crossingLower, crossingUpper, min_eq_right hu, max_eq_left hu,
      min_eq_left hv, max_eq_right hv]
    ring
  · rw [abs_of_nonneg hu, abs_of_nonpos hv]
    simp [crossingLower, crossingUpper, min_eq_left hu, max_eq_right hu,
      min_eq_right hv, max_eq_left hv]
    ring
  · rw [abs_of_nonneg hu, abs_of_nonneg hv]
    simp [crossingLower, crossingUpper, min_eq_left hu, max_eq_right hu,
      min_eq_left hv, max_eq_right hv]
    ring

/-- The crossing integrand after `(x,y,z) = (y+u,y,y-v)`. -/
def transformedCrossingKernel (p u v y : ℝ) : ℝ :=
  |u| * |v| * topHat p y * topHat p (y + u) *
    topHat p (y - v) * topHat p (y + u - v)

private theorem transformedCrossingKernel_eq_indicator {p : ℝ} (u v y : ℝ) :
    transformedCrossingKernel p u v y =
      (Set.Icc (crossingLower p u v) (crossingUpper p u v)).indicator
        (fun _ => |u| * |v| / p ^ 4) y := by
  by_cases hy : y ∈ topHatSupport p ∧ y + u ∈ topHatSupport p ∧
      y - v ∈ topHatSupport p ∧ y + u - v ∈ topHatSupport p
  · have hy' : y ∈ Set.Icc (crossingLower p u v) (crossingUpper p u v) :=
      four_supports_iff.mp hy
    simp only [transformedCrossingKernel, topHat, Set.indicator_of_mem hy.1,
      Set.indicator_of_mem hy.2.1, Set.indicator_of_mem hy.2.2.1,
      Set.indicator_of_mem hy.2.2.2, Set.indicator_of_mem hy']
    ring
  · have hy' : y ∉ Set.Icc (crossingLower p u v) (crossingUpper p u v) := by
      rwa [← four_supports_iff]
    rw [Set.indicator_of_notMem hy']
    rcases not_and_or.mp hy with hy | hy
    · simp [transformedCrossingKernel, topHat, hy]
    · rcases not_and_or.mp hy with hy | hy
      · simp [transformedCrossingKernel, topHat, hy]
      · rcases not_and_or.mp hy with hy | hy
        · simp [transformedCrossingKernel, topHat, hy]
        · simp [transformedCrossingKernel, topHat, hy]

private theorem transformedCrossingKernel_integral_y (p u v : ℝ) :
    (∫ y : ℝ, transformedCrossingKernel p u v y) =
      |u| * |v| / p ^ 4 * max (p - |u| - |v|) 0 := by
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
    (transformedCrossingKernel_eq_indicator (p := p) u v))]
  rw [MeasureTheory.integral_indicator_const _ measurableSet_Icc]
  rw [Real.volume_real_Icc, crossing_length]
  simp only [smul_eq_mul]
  ring

private def positiveCrossingKernel (p u v : ℝ) : ℝ :=
  u * v / p ^ 4 * max (p - u - v) 0

private def radialCrossingKernel (p u v : ℝ) : ℝ :=
  positiveCrossingKernel p |u| |v|

private theorem transformedCrossingKernel_integral_y_eq_radial (p u v : ℝ) :
    (∫ y : ℝ, transformedCrossingKernel p u v y) = radialCrossingKernel p u v := by
  rw [transformedCrossingKernel_integral_y]
  rfl

private theorem positiveCrossingKernel_inner {p u : ℝ} (_hu0 : 0 < u) (hup : u < p) :
    (∫ v in Set.Ioi (0 : ℝ), positiveCrossingKernel p u v) =
      1 / p ^ 4 * ∫ v in 0..(p - u), u * v * (p - u - v) := by
  have hsub : Set.Ioo (0 : ℝ) (p - u) ⊆ Set.Ioi 0 := by
    intro v hv
    exact hv.1
  rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioi hsub]
  · rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (by linarith : 0 ≤ p - u)]
    calc
      (∫ v in 0..(p - u), positiveCrossingKernel p u v) =
          ∫ v in 0..(p - u), (1 / p ^ 4) * (u * v * (p - u - v)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le (by linarith : 0 ≤ p - u)] at hv
        rcases hv with ⟨hv0, hv1⟩
        simp only [positiveCrossingKernel, max_eq_left (by linarith : 0 ≤ p - u - v)]
        ring
      _ = 1 / p ^ 4 * ∫ v in 0..(p - u), u * v * (p - u - v) := by
        rw [intervalIntegral.integral_const_mul]
  · intro v hv
    have hpv : p - u ≤ v := le_of_not_gt (fun h => hv.2 ⟨hv.1, h⟩)
    simp only [positiveCrossingKernel, max_eq_right (by linarith : p - u - v ≤ 0), mul_zero]

private theorem positiveCrossingKernel_outer_zero {p u : ℝ} (_hu0 : 0 < u)
    (hpu : p ≤ u) :
    (∫ v in Set.Ioi (0 : ℝ), positiveCrossingKernel p u v) = 0 := by
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
  change positiveCrossingKernel p u v = 0
  have hv0 : 0 < v := hv
  simp only [positiveCrossingKernel, max_eq_right (by linarith : p - u - v ≤ 0)]
  ring

private theorem positiveCrossingKernel_double_integral {p : ℝ} (hp : 0 < p) :
    (∫ u in Set.Ioi (0 : ℝ), ∫ v in Set.Ioi (0 : ℝ),
        positiveCrossingKernel p u v) =
      1 / p ^ 4 * ∫ u in 0..p, ∫ v in 0..(p - u), u * v * (p - u - v) := by
  have hsub : Set.Ioo (0 : ℝ) p ⊆ Set.Ioi 0 := by
    intro u hu
    exact hu.1
  rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioi hsub]
  · rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun u hu => positiveCrossingKernel_inner hu.1 hu.2)]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le hp.le]
    rw [← intervalIntegral.integral_const_mul]
  · intro u hu
    exact positiveCrossingKernel_outer_zero hu.1
      (le_of_not_gt (fun h => hu.2 ⟨hu.1, h⟩))

private theorem radialCrossingKernel_double_integral {p : ℝ} (hp : 0 < p) :
    (∫ u : ℝ, ∫ v : ℝ, radialCrossingKernel p u v) =
      crossingSimplexIntegral p := by
  calc
    (∫ u : ℝ, ∫ v : ℝ, radialCrossingKernel p u v) =
        ∫ u : ℝ, 2 * ∫ v in Set.Ioi (0 : ℝ),
          positiveCrossingKernel p |u| v := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      exact integral_comp_abs (f := fun v => positiveCrossingKernel p |u| v)
    _ = 2 * ∫ u : ℝ, ∫ v in Set.Ioi (0 : ℝ),
          positiveCrossingKernel p |u| v := by
      rw [MeasureTheory.integral_const_mul]
    _ = 2 * (2 * ∫ u in Set.Ioi (0 : ℝ), ∫ v in Set.Ioi (0 : ℝ),
          positiveCrossingKernel p u v) := by
      rw [integral_comp_abs
        (f := fun u => ∫ v in Set.Ioi (0 : ℝ), positiveCrossingKernel p u v)]
    _ = crossingSimplexIntegral p := by
      rw [positiveCrossingKernel_double_integral hp]
      unfold crossingSimplexIntegral
      ring

/-- The globally integrated crossing kernel in the new coordinates. -/
def transformedCrossingIntegral (p : ℝ) : ℝ :=
  ∫ u : ℝ, ∫ v : ℝ, ∫ y : ℝ, transformedCrossingKernel p u v y

/-- The transformed crossing functional is exactly the reduced simplex
integral.  This closes the support-intersection and four-quadrant parts of
the crossing calculation. -/
theorem transformedCrossingIntegral_eq {p : ℝ} (hp : 0 < p) :
    transformedCrossingIntegral p = crossingSimplexIntegral p := by
  calc
    transformedCrossingIntegral p =
        ∫ u : ℝ, ∫ v : ℝ, radialCrossingKernel p u v := by
      unfold transformedCrossingIntegral
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v
      exact transformedCrossingKernel_integral_y_eq_radial p u v
    _ = crossingSimplexIntegral p := radialCrossingKernel_double_integral hp

section CrossingChangeOfVariables

open MeasureTheory Matrix Set

private theorem integral_fin3_eq_iterated (f : (Fin 3 → ℝ) → ℝ)
    (hf : Integrable f) :
    (∫ t : Fin 3 → ℝ, f t) = ∫ u : ℝ, ∫ y : ℝ, ∫ v : ℝ, f ![u, y, v] := by
  let e3 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have mp3 := measurePreserving_piFinSuccAbove
    (fun _ : Fin 3 => (volume : Measure ℝ)) (0 : Fin 3)
  have hf3 : Integrable (fun q : ℝ × (Fin 2 → ℝ) => f (e3.symm q)) :=
    (mp3.symm.integrable_comp_emb e3.symm.measurableEmbedding).mpr hf
  calc
    (∫ t : Fin 3 → ℝ, f t) = ∫ q : ℝ × (Fin 2 → ℝ), f (e3.symm q) := by
      simpa only [volume_pi, Measure.volume_eq_prod] using
        (mp3.symm.integral_comp' f).symm
    _ = ∫ u : ℝ, ∫ r : Fin 2 → ℝ, f (e3.symm (u, r)) := by
      rw [Measure.volume_eq_prod, integral_prod _ hf3]
    _ = ∫ u : ℝ, ∫ y : ℝ, ∫ v : ℝ, f ![u, y, v] := by
      apply integral_congr_ae
      filter_upwards [hf3.prod_right_ae] with u hu
      let e2 := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
      have mp2 := measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure ℝ))
      have hu2 : Integrable (fun q : ℝ × ℝ => f (e3.symm (u, e2.symm q))) :=
        (mp2.symm.integrable_comp_emb e2.symm.measurableEmbedding).mpr hu
      calc
        (∫ r : Fin 2 → ℝ, f (e3.symm (u, r))) =
            ∫ q : ℝ × ℝ, f (e3.symm (u, e2.symm q)) := by
          simpa only [volume_pi, Measure.volume_eq_prod] using
            (mp2.symm.integral_comp' (fun r => f (e3.symm (u, r)))).symm
        _ = ∫ y : ℝ, ∫ v : ℝ, f ![u, y, v] := by
          rw [Measure.volume_eq_prod, integral_prod _ hu2]
          apply integral_congr_ae
          filter_upwards with y
          apply integral_congr_ae
          filter_upwards with v
          congr 1
          funext i
          fin_cases i <;> rfl

private def rawCrossingKernel (p x y z : ℝ) : ℝ :=
  baseWindow.indicator
    (fun w => |x - y| * |y - z| *
      topHat p x * topHat p y * topHat p z * topHat p w)
    (x + z - y)

private def extendedCrossingKernel (p : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  baseWindow.indicator (fun x =>
    baseWindow.indicator (fun y =>
      baseWindow.indicator (fun z => rawCrossingKernel p x y z) (t 2)) (t 1)) (t 0)

private theorem interval_base_eq_setIntegral (g : ℝ → ℝ) :
    (∫ x in (-(1 : ℝ) / 2)..(1 / 2), g x) = ∫ x in baseWindow, g x := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2)]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rfl

private theorem formulaCrossingIntegral_eq_iterated_extended (p : ℝ) :
    formulaCrossingIntegral p =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, extendedCrossingKernel p ![x, y, z] := by
  unfold formulaCrossingIntegral
  simp_rw [interval_base_eq_setIntegral]
  unfold baseWindow
  simp_rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)
  · rw [Set.indicator_of_mem hx]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)
    · rw [Set.indicator_of_mem hy]
      apply integral_congr_ae
      filter_upwards with z
      unfold extendedCrossingKernel rawCrossingKernel baseWindow
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
      congr 1
    · rw [Set.indicator_of_notMem hy]
      have hz : ∀ z : ℝ, extendedCrossingKernel p ![x, y, z] = 0 := by
        intro z
        unfold extendedCrossingKernel baseWindow
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
        rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hy]
      simp_rw [hz]
      simp
  · rw [Set.indicator_of_notMem hx]
    have hyz : ∀ y z : ℝ, extendedCrossingKernel p ![x, y, z] = 0 := by
      intro y z
      unfold extendedCrossingKernel baseWindow
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      rw [Set.indicator_of_notMem hx]
    simp_rw [hyz]
    simp

private theorem measurable_extendedCrossingKernel (p : ℝ) :
    Measurable (extendedCrossingKernel p) := by
  classical
  have htop : Measurable (topHat p) := by
    unfold topHat topHatSupport
    exact measurable_const.indicator measurableSet_Icc
  have hraw : Measurable
      (fun t : Fin 3 → ℝ => rawCrossingKernel p (t 0) (t 1) (t 2)) := by
    have harg : Measurable (fun t : Fin 3 → ℝ => t 0 + t 2 - t 1) := by fun_prop
    have hbody : Measurable (fun t : Fin 3 → ℝ =>
        |t 0 - t 1| * |t 1 - t 2| *
          topHat p (t 0) * topHat p (t 1) * topHat p (t 2) *
            topHat p (t 0 + t 2 - t 1)) := by
      fun_prop
    unfold rawCrossingKernel
    simp only [Set.indicator_apply]
    exact Measurable.ite (measurableSet_Icc.preimage harg) hbody measurable_const
  have h0 : MeasurableSet {t : Fin 3 → ℝ |
      t 0 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)} :=
    measurableSet_Icc.preimage (by fun_prop)
  have h1 : MeasurableSet {t : Fin 3 → ℝ |
      t 1 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)} :=
    measurableSet_Icc.preimage (by fun_prop)
  have h2 : MeasurableSet {t : Fin 3 → ℝ |
      t 2 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)} :=
    measurableSet_Icc.preimage (by fun_prop)
  unfold extendedCrossingKernel baseWindow
  simp only [Set.indicator_apply]
  exact Measurable.ite h0 (Measurable.ite h1 (Measurable.ite h2 hraw measurable_const)
    measurable_const) measurable_const

private theorem abs_topHat_le (p x : ℝ) : |topHat p x| ≤ |1 / p| := by
  by_cases hx : x ∈ topHatSupport p
  · simp [topHat, hx]
  · simp [topHat, hx]

private def crossingBaseCube : Set (Fin 3 → ℝ) :=
  Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 : ℝ) / 2) (1 / 2))

private theorem isCompact_crossingBaseCube : IsCompact crossingBaseCube := by
  unfold crossingBaseCube
  exact isCompact_univ_pi (fun _ : Fin 3 => (isCompact_Icc :
    IsCompact (Set.Icc (-(1 : ℝ) / 2) (1 / 2))))

private theorem extendedCrossingKernel_eq_zero_off_baseCube
    {p : ℝ} {t : Fin 3 → ℝ} (ht : t ∉ crossingBaseCube) :
    extendedCrossingKernel p t = 0 := by
  simp only [crossingBaseCube, Set.mem_pi, Set.mem_univ, forall_true_left] at ht
  push Not at ht
  obtain ⟨i, hi⟩ := ht
  fin_cases i
  · unfold extendedCrossingKernel baseWindow
    change t 0 ∉ Set.Icc (-(1 : ℝ) / 2) (1 / 2) at hi
    rw [Set.indicator_of_notMem hi]
  · unfold extendedCrossingKernel baseWindow
    change t 1 ∉ Set.Icc (-(1 : ℝ) / 2) (1 / 2) at hi
    by_cases h0 : t 0 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)
    · rw [Set.indicator_of_mem h0, Set.indicator_of_notMem hi]
    · rw [Set.indicator_of_notMem h0]
  · unfold extendedCrossingKernel baseWindow
    change t 2 ∉ Set.Icc (-(1 : ℝ) / 2) (1 / 2) at hi
    by_cases h0 : t 0 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)
    · rw [Set.indicator_of_mem h0]
      by_cases h1 : t 1 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem hi]
      · rw [Set.indicator_of_notMem h1]
    · rw [Set.indicator_of_notMem h0]

private theorem norm_extendedCrossingKernel_le {p : ℝ} {t : Fin 3 → ℝ}
    (ht : t ∈ crossingBaseCube) :
    ‖extendedCrossingKernel p t‖ ≤ |1 / p| ^ 4 := by
  have hti : ∀ i : Fin 3, t i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
    simpa only [crossingBaseCube, Set.mem_pi, Set.mem_univ, forall_true_left] using ht
  have ht0 := hti 0
  have ht1 := hti 1
  have ht2 := hti 2
  have h01 : |t 0 - t 1| ≤ 1 := (abs_le).2 ⟨by linarith [ht0.1, ht1.2],
    by linarith [ht0.2, ht1.1]⟩
  have h12 : |t 1 - t 2| ≤ 1 := (abs_le).2 ⟨by linarith [ht1.1, ht2.2],
    by linarith [ht1.2, ht2.1]⟩
  have hext : extendedCrossingKernel p t =
      rawCrossingKernel p (t 0) (t 1) (t 2) := by
    unfold extendedCrossingKernel baseWindow
    rw [Set.indicator_of_mem ht0, Set.indicator_of_mem ht1, Set.indicator_of_mem ht2]
  rw [hext]
  by_cases hw : t 0 + t 2 - t 1 ∈ baseWindow
  · unfold rawCrossingKernel
    rw [Set.indicator_of_mem hw]
    simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    have hth0 := abs_topHat_le p (t 0)
    have hth1 := abs_topHat_le p (t 1)
    have hth2 := abs_topHat_le p (t 2)
    have hthw := abs_topHat_le p (t 0 + t 2 - t 1)
    calc
      |t 0 - t 1| * |t 1 - t 2| * |topHat p (t 0)| * |topHat p (t 1)| *
            |topHat p (t 2)| * |topHat p (t 0 + t 2 - t 1)| ≤
          1 * 1 * |1 / p| * |1 / p| * |1 / p| * |1 / p| := by
        gcongr
      _ = |1 / p| ^ 4 := by ring
  · unfold rawCrossingKernel
    rw [Set.indicator_of_notMem hw]
    simp

private theorem integrable_extendedCrossingKernel (p : ℝ) :
    Integrable (extendedCrossingKernel p) := by
  have hbdd : ∀ᵐ t ∂(volume.restrict crossingBaseCube),
      ‖extendedCrossingKernel p t‖ ≤ |1 / p| ^ 4 := by
    filter_upwards [ae_restrict_mem isCompact_crossingBaseCube.measurableSet] with t ht
    exact norm_extendedCrossingKernel_le ht
  have hon : IntegrableOn (extendedCrossingKernel p) crossingBaseCube :=
    Measure.integrableOn_of_bounded (M := |1 / p| ^ 4)
      isCompact_crossingBaseCube.measure_ne_top
      (measurable_extendedCrossingKernel p).aestronglyMeasurable
      hbdd
  have hind : Integrable (crossingBaseCube.indicator (extendedCrossingKernel p)) :=
    hon.integrable_indicator isCompact_crossingBaseCube.measurableSet
  exact hind.congr (Filter.Eventually.of_forall fun t => by
    by_cases ht : t ∈ crossingBaseCube
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht,
        extendedCrossingKernel_eq_zero_off_baseCube ht])

private def crossingMapMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 1; 0, 0, 1; 0, -1, 1]

@[simp] private theorem vec3_apply_two (a b c : ℝ) :
    (![a, b, c] : Fin 3 → ℝ) 2 = c := by
  rfl

private theorem crossingMapMatrix_det : Matrix.det crossingMapMatrix = 1 := by
  norm_num [crossingMapMatrix, Matrix.det_fin_three, Matrix.cons_val_two]

private theorem crossingMap_apply (t : Fin 3 → ℝ) :
    Matrix.toLin' crossingMapMatrix t = ![t 0 + t 2, t 2, t 2 - t 1] := by
  funext i
  fin_cases i
  · simp [crossingMapMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  · simp [crossingMapMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  · simp [crossingMapMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring

private theorem crossingMap_injective :
    Function.Injective (Matrix.toLin' crossingMapMatrix) := by
  intro a b hab
  have hab' : ![a 0 + a 2, a 2, a 2 - a 1] =
      ![b 0 + b 2, b 2, b 2 - b 1] := by
    simpa only [crossingMap_apply] using hab
  have h0 := congrFun hab' 0
  have h1 := congrFun hab' 1
  have h2 := congrFun hab' 2
  norm_num [Matrix.cons_val_two] at h0 h1 h2
  funext i
  fin_cases i
  · change a 0 = b 0
    linarith
  · change a 1 = b 1
    linarith
  · change a 2 = b 2
    linarith

private theorem crossingMap_measurePreserving :
    MeasurePreserving (Matrix.toLin' crossingMapMatrix)
      (volume : Measure (Fin 3 → ℝ)) volume := by
  refine ⟨(LinearMap.continuous_on_pi _).measurable, ?_⟩
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · norm_num [crossingMapMatrix, Matrix.det_fin_three, Matrix.cons_val_two]
  · norm_num [crossingMapMatrix, Matrix.det_fin_three, Matrix.cons_val_two]

private theorem crossing_support_subset_base {p x : ℝ} (hp1 : p ≤ 1)
    (hx : x ∈ topHatSupport p) : x ∈ baseWindow := by
  rw [topHatSupport, Set.mem_Icc] at hx
  rw [baseWindow, Set.mem_Icc]
  constructor <;> linarith

private theorem extendedCrossingKernel_map_eq {p : ℝ} (hp1 : p ≤ 1)
    (u v y : ℝ) :
    extendedCrossingKernel p ![y + u, y, y - v] =
      transformedCrossingKernel p u v y := by
  by_cases hy : y ∈ topHatSupport p
  · by_cases hxu : y + u ∈ topHatSupport p
    · by_cases hzv : y - v ∈ topHatSupport p
      · by_cases hw : y + u - v ∈ topHatSupport p
        · have hyb := crossing_support_subset_base hp1 hy
          have hxb := crossing_support_subset_base hp1 hxu
          have hzb := crossing_support_subset_base hp1 hzv
          have hwb := crossing_support_subset_base hp1 hw
          unfold extendedCrossingKernel
          rw [vec3_apply_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hyb,
            Set.indicator_of_mem hzb]
          unfold rawCrossingKernel
          have harg : y + u + (y - v) - y = y + u - v := by ring
          rw [harg, Set.indicator_of_mem hwb]
          simp only [transformedCrossingKernel, topHat, Set.indicator_of_mem hy,
            Set.indicator_of_mem hxu, Set.indicator_of_mem hzv, Set.indicator_of_mem hw]
          ring_nf
        · have hw' : y + u + (y - v) - y ∉ topHatSupport p := by
            have harg' : y + u + (y - v) - y = y + u - v := by ring
            simpa only [harg'] using hw
          simp [extendedCrossingKernel, rawCrossingKernel, transformedCrossingKernel,
            topHat, hw, hw', vec3_apply_two]
      · simp [extendedCrossingKernel, rawCrossingKernel, transformedCrossingKernel,
          topHat, hzv, vec3_apply_two]
    · simp [extendedCrossingKernel, rawCrossingKernel, transformedCrossingKernel,
        topHat, hxu, vec3_apply_two]
  · simp [extendedCrossingKernel, rawCrossingKernel, transformedCrossingKernel,
      topHat, hy, vec3_apply_two]

/-- The original interval integral equals the globally transformed kernel.
The proof first extends the compact interval kernel by zero, applies Fubini
on `ℝ³`, and then uses the determinant-one map
`(u,v,y) ↦ (y+u,y,y-v)`. -/
theorem formulaCrossingIntegral_eq_transformed {p : ℝ} (hp1 : p ≤ 1) :
    formulaCrossingIntegral p = transformedCrossingIntegral p := by
  let L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' crossingMapMatrix
  let F : (Fin 3 → ℝ) → ℝ := extendedCrossingKernel p
  have hF : Integrable F := integrable_extendedCrossingKernel p
  have hmp : MeasurePreserving L (volume : Measure (Fin 3 → ℝ)) volume := by
    simpa only [L] using crossingMap_measurePreserving
  have hinj : Function.Injective L := by
    simpa only [L] using crossingMap_injective
  have hemb : MeasurableEmbedding L :=
    (LinearMap.continuous_on_pi L).measurableEmbedding hinj
  have hcomp : Integrable (fun t => F (L t)) := by
    simpa only [Function.comp_def] using
      (hmp.integrable_comp_emb hemb).mpr hF
  calc
    formulaCrossingIntegral p =
        ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, F ![x, y, z] := by
      simpa only [F] using formulaCrossingIntegral_eq_iterated_extended p
    _ = ∫ t : Fin 3 → ℝ, F t := (integral_fin3_eq_iterated F hF).symm
    _ = ∫ t : Fin 3 → ℝ, F (L t) :=
      (hmp.integral_comp hemb F).symm
    _ = ∫ u : ℝ, ∫ v : ℝ, ∫ y : ℝ, F (L ![u, v, y]) :=
      integral_fin3_eq_iterated (fun t => F (L t)) hcomp
    _ = transformedCrossingIntegral p := by
      unfold transformedCrossingIntegral
      apply integral_congr_ae
      filter_upwards with u
      apply integral_congr_ae
      filter_upwards with v
      apply integral_congr_ae
      filter_upwards with y
      change extendedCrossingKernel p (Matrix.toLin' crossingMapMatrix ![u, v, y]) =
        transformedCrossingKernel p u v y
      rw [crossingMap_apply]
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, vec3_apply_two, add_comm] using
        extendedCrossingKernel_map_eq hp1 u v y

end CrossingChangeOfVariables

/-- The exact crossing reduction: determinant-one substitution
`(x,y,z) = (y+u,y,y-v)`, integration over the intersection of four
translated top-hat supports, and the four sign quadrants of `(u,v)`. -/
theorem crossingReduction {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    formulaCrossingIntegral p = crossingSimplexIntegral p := by
  rw [formulaCrossingIntegral_eq_transformed hp1, transformedCrossingIntegral_eq hp]

/-! ## Formula (21), assembled from the proved scalar integrals -/

/-- Formula-(21) second moment, written entirely as actual interval
integrals. -/
def formula21M2Integral (mu p : ℝ) : ℝ :=
  centeredMoment 2 p + mu ^ 2 * rDistanceIntegral p

/-- Formula-(21) third moment, written entirely as actual interval
integrals. -/
def formula21M3Integral (mu p : ℝ) : ℝ :=
  centeredMoment 3 p + 3 * mu ^ 2 * qrDistanceIntegral p

/-- Formula-(21) fourth moment with the reduced crossing integral. -/
def formula21M4ReducedIntegral (mu p : ℝ) : ℝ :=
  centeredMoment 4 p +
    4 * mu ^ 2 * qSquaredRDistanceIntegral p +
    2 * mu ^ 2 * doubleQrDistanceIntegral p +
    2 * mu ^ 4 * squaredPotentialIntegral p +
    mu ^ 4 * crossingSimplexIntegral p

/-- Formula-(21) fourth moment with the original three-dimensional
crossing functional. -/
def formula21M4Integral (mu p : ℝ) : ℝ :=
  centeredMoment 4 p +
    4 * mu ^ 2 * qSquaredRDistanceIntegral p +
    2 * mu ^ 2 * doubleQrDistanceIntegral p +
    2 * mu ^ 4 * squaredPotentialIntegral p +
    mu ^ 4 * formulaCrossingIntegral p

/-- Closed form of the actual second-moment integral. -/
theorem formula21M2Integral_eq {p mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    formula21M2Integral mu p = (1 - p) / p + mu ^ 2 * p / 3 := by
  rw [formula21M2Integral, centeredMoment_two hp hp1, rDistanceIntegral_eq hp]
  ring

/-- Closed form of the actual third-moment integral. -/
theorem formula21M3Integral_eq {p mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    formula21M3Integral mu p =
      (1 - p) ^ 3 / p ^ 2 - (1 - p) + mu ^ 2 * (1 - p) := by
  rw [formula21M3Integral, centeredMoment_three hp hp1, qrDistanceIntegral_eq hp]
  ring

/-- The complete `μ⁴` contribution after the explicitly named reduced
crossing calculation. -/
theorem combinedFourthMuFourthReduced {p mu : ℝ} (hp : 0 < p) :
    2 * mu ^ 4 * squaredPotentialIntegral p +
        mu ^ 4 * crossingSimplexIntegral p =
      4 * mu ^ 4 * p / 15 := by
  rw [squaredPotentialIntegral_eq hp, crossingSimplexIntegral_eq hp]
  ring

/-- Closed form of the fourth moment using only proved interval-integral
reductions. -/
theorem formula21M4ReducedIntegral_eq {p mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    formula21M4ReducedIntegral mu p =
      (1 - p) ^ 4 / p ^ 3 + (1 - p) +
        2 * mu ^ 2 * (1 - p) ^ 2 / p + 4 * mu ^ 4 * p / 15 := by
  rw [formula21M4ReducedIntegral, centeredMoment_four hp hp1,
    qSquaredRDistanceIntegral_eq hp, doubleQrDistanceIntegral_eq hp,
    squaredPotentialIntegral_eq hp, crossingSimplexIntegral_eq hp]
  ring

/-- Closed form of the original three-dimensional formula-(21) fourth
moment.  The crossing change of variables is discharged by
`crossingReduction`. -/
theorem formula21M4Integral_eq {p mu : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    formula21M4Integral mu p =
      (1 - p) ^ 4 / p ^ 3 + (1 - p) +
        2 * mu ^ 2 * (1 - p) ^ 2 / p + 4 * mu ^ 4 * p / 15 := by
  unfold formula21M4Integral
  rw [crossingReduction hp hp1, centeredMoment_four hp hp1,
    qSquaredRDistanceIntegral_eq hp, doubleQrDistanceIntegral_eq hp,
    squaredPotentialIntegral_eq hp, crossingSimplexIntegral_eq hp]
  ring

end

end TopHatMoments
end Zeta85
end RH
