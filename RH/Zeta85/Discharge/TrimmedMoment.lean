/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/TrimmedMoment.lean — finite trimmed fourth-moment
duality and the two exact terminal rational quartics.

This file deliberately separates three layers.

1. `finite_trimmed_quartic_dual` is a finite theorem: nonnegative weights,
   an explicitly bounded removed submeasure, four exact moments, and three
   global pointwise inequalities imply the weak dual lower bound.
2. `Terminal9506` and `Terminal8686` verify the two rational quartics from
   terminal file 24 globally, including their factor identities and exact
   fixed-point arithmetic.
3. `TrimmedMomentInputs` is the explicit bridge interface.  Its fields are
   propositions; this file does not assert that a zeta-zero compression
   supplies them.

There is no assertion of primal equality or sharpness here.
-/
import Mathlib

open scoped BigOperators

namespace RH
namespace Zeta85
namespace TrimmedMoment

noncomputable section

/-! ## 1. Generic finite weak duality -/

/-- A quartic polynomial, stored coefficient-first. -/
structure Quartic where
  p0 : ℝ
  p1 : ℝ
  p2 : ℝ
  p3 : ℝ
  p4 : ℝ

/-- Evaluation of a quartic. -/
def Quartic.eval (p : Quartic) (y : ℝ) : ℝ :=
  p.p0 + p.p1 * y + p.p2 * y ^ 2 + p.p3 * y ^ 3 + p.p4 * y ^ 4

/-- Evaluation of its derivative. -/
def Quartic.derivEval (p : Quartic) (y : ℝ) : ℝ :=
  p.p1 + 2 * p.p2 * y + 3 * p.p3 * y ^ 2 + 4 * p.p4 * y ^ 3

/-- The three global pointwise requirements of the trimmed-moment dual. -/
structure DualFeasible (p : Quartic) (cap : ℝ) : Prop where
  cap_nonneg : 0 ≤ cap
  nonpos_on_nonpos : ∀ y : ℝ, y ≤ 0 → p.eval y ≤ 0
  below_square_on_nonneg : ∀ y : ℝ, 0 ≤ y → p.eval y ≤ y ^ 2
  below_cap_on_nonneg : ∀ y : ℝ, 0 ≤ y → p.eval y ≤ cap

/-- Explicit finite bridge data.  `weight` is the full law and `removed`
is the submeasure discarded by the exceptional-rank trim.  Every field is
a proposition, in the house-input style. -/
structure TrimmedMomentInputs {ι : Type*} [Fintype ι]
    (value weight removed : ι → ℝ) (m1 m2 m3 m4 alpha : ℝ) : Prop where
  weight_nonneg : ∀ i, 0 ≤ weight i
  removed_nonneg : ∀ i, 0 ≤ removed i
  removed_le_weight : ∀ i, removed i ≤ weight i
  removed_mass_le : (∑ i, removed i) ≤ alpha
  mass_one : (∑ i, weight i) = 1
  moment_one : (∑ i, weight i * value i) = m1
  moment_two : (∑ i, weight i * value i ^ 2) = m2
  moment_three : (∑ i, weight i * value i ^ 3) = m3
  moment_four : (∑ i, weight i * value i ^ 4) = m4

/-- Residual positive-square energy after the finite trim. -/
def residualTail {ι : Type*} [Fintype ι]
    (value weight removed : ι → ℝ) : ℝ :=
  ∑ i, (weight i - removed i) * (max (value i) 0) ^ 2

/-- The complete finite bridge consumed by a terminal certificate.  It
bundles the exact moments, the exceptional-rank trim fraction, and the
stability-tail upper bound.  All fields are propositions. -/
structure StabilityMomentBridge {ι : Type*} [Fintype ι]
    (value weight removed : ι → ℝ) (m1 m2 m3 m4 alpha mu D epsilon : ℝ) : Prop where
  moments : TrimmedMomentInputs value weight removed m1 m2 m3 m4 alpha
  trim_fraction : alpha ≤ (D - 1 - epsilon) / (2 * mu)
  stability_tail : mu * residualTail value weight removed ≤ epsilon

/-- A quartic expectation is determined by the first four moments. -/
theorem quartic_expectation_of_moments {ι : Type*} [Fintype ι]
    (p : Quartic) (value weight removed : ι → ℝ) (m1 m2 m3 m4 alpha : ℝ)
    (h : TrimmedMomentInputs value weight removed m1 m2 m3 m4 alpha) :
    (∑ i, weight i * p.eval (value i)) =
      p.p0 + p.p1 * m1 + p.p2 * m2 + p.p3 * m3 + p.p4 * m4 := by
  calc
    (∑ i, weight i * p.eval (value i)) =
        ∑ i, (p.p0 * weight i + p.p1 * (weight i * value i) +
          p.p2 * (weight i * value i ^ 2) + p.p3 * (weight i * value i ^ 3) +
          p.p4 * (weight i * value i ^ 4)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Quartic.eval]
      ring
    _ = p.p0 * (∑ i, weight i) + p.p1 * (∑ i, weight i * value i) +
          p.p2 * (∑ i, weight i * value i ^ 2) +
          p.p3 * (∑ i, weight i * value i ^ 3) +
          p.p4 * (∑ i, weight i * value i ^ 4) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = p.p0 + p.p1 * m1 + p.p2 * m2 + p.p3 * m3 + p.p4 * m4 := by
      rw [h.mass_one, h.moment_one, h.moment_two, h.moment_three, h.moment_four]
      ring

private theorem pointwise_trimmed_dual_bound (p : Quartic) (cap : ℝ)
    (hdual : DualFeasible p cap) {y w r : ℝ}
    (hw : 0 ≤ w) (hr0 : 0 ≤ r) (hrw : r ≤ w) :
    w * p.eval y ≤ (w - r) * (max y 0) ^ 2 + r * cap := by
  rcases le_total y 0 with hy | hy
  · have hp : p.eval y ≤ 0 := hdual.nonpos_on_nonpos y hy
    have hwp : w * p.eval y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw hp
    have hrc : 0 ≤ r * cap := mul_nonneg hr0 hdual.cap_nonneg
    rw [max_eq_right hy]
    norm_num
    exact hwp.trans hrc
  · have hwr : 0 ≤ w - r := sub_nonneg.mpr hrw
    calc
      w * p.eval y = (w - r) * p.eval y + r * p.eval y := by ring
      _ ≤ (w - r) * y ^ 2 + r * cap :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hdual.below_square_on_nonneg y hy) hwr)
          (mul_le_mul_of_nonneg_left (hdual.below_cap_on_nonneg y hy) hr0)
      _ = (w - r) * (max y 0) ^ 2 + r * cap := by rw [max_eq_left hy]

/-- **Finite trimmed quartic weak duality.**  No measure theory or limiting
argument is hidden here: this is a sum over a finite type. -/
theorem finite_trimmed_quartic_dual {ι : Type*} [Fintype ι]
    (p : Quartic) (cap : ℝ) (value weight removed : ι → ℝ)
    (m1 m2 m3 m4 alpha : ℝ) (hdual : DualFeasible p cap)
    (h : TrimmedMomentInputs value weight removed m1 m2 m3 m4 alpha) :
    p.p0 + p.p1 * m1 + p.p2 * m2 + p.p3 * m3 + p.p4 * m4 - alpha * cap ≤
      residualTail value weight removed := by
  have hpoint : ∀ i,
      weight i * p.eval (value i) ≤
        (weight i - removed i) * (max (value i) 0) ^ 2 + removed i * cap :=
    fun i => pointwise_trimmed_dual_bound p cap hdual
      (h.weight_nonneg i) (h.removed_nonneg i) (h.removed_le_weight i)
  have hsum :
      (∑ i, weight i * p.eval (value i)) ≤
        residualTail value weight removed + ∑ i, removed i * cap := by
    simpa only [residualTail, Finset.sum_add_distrib] using
      (Finset.sum_le_sum fun i _ => hpoint i)
  have hremoved : (∑ i, removed i * cap) ≤ alpha * cap := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right h.removed_mass_le hdual.cap_nonneg
  have hmain :
      p.p0 + p.p1 * m1 + p.p2 * m2 + p.p3 * m3 + p.p4 * m4 ≤
        residualTail value weight removed + alpha * cap := by
    rw [← quartic_expectation_of_moments p value weight removed m1 m2 m3 m4 alpha h]
    exact hsum.trans (by linarith)
  linarith

/-- Scaling the finite weak bound by a nonnegative block fraction. -/
theorem finite_trimmed_quartic_dual_scaled {ι : Type*} [Fintype ι]
    (p : Quartic) (cap mu : ℝ) (value weight removed : ι → ℝ)
    (m1 m2 m3 m4 alpha : ℝ) (hmu : 0 ≤ mu) (hdual : DualFeasible p cap)
    (h : TrimmedMomentInputs value weight removed m1 m2 m3 m4 alpha) :
    mu * (p.p0 + p.p1 * m1 + p.p2 * m2 + p.p3 * m3 + p.p4 * m4 - alpha * cap) ≤
      mu * residualTail value weight removed :=
  mul_le_mul_of_nonneg_left
    (finite_trimmed_quartic_dual p cap value weight removed m1 m2 m3 m4 alpha hdual h) hmu

/-! ## 2. Elementary polynomial tools -/

/-- A positive-leading quadratic with negative discriminant is positive
on the whole real line. -/
theorem quadratic_pos_of_discriminant_neg (a b c x : ℝ)
    (hc : 0 < c) (hdisc : b ^ 2 < 4 * a * c) :
    0 < a + b * x + c * x ^ 2 := by
  have hs := sq_nonneg (2 * c * x + b)
  nlinarith

/-- The affine fixed-point rearrangement used in terminal file 24 (27). -/
theorem affine_fixed_point {epsilon mu AP cap D : ℝ}
    (_hcap : 0 ≤ cap) (hslope : cap / 2 < 1)
    (h : mu * AP - cap / 2 * (D - 1 - epsilon) ≤ epsilon) :
    (mu * AP - cap / 2 * (D - 1)) / (1 - cap / 2) ≤ epsilon := by
  have hden : 0 < 1 - cap / 2 := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- Finite weak duality plus the explicit trim-fraction and stability
bridges gives the affine inequality used by the fixed-point certificate. -/
theorem affine_bound_of_finite_inputs {ι : Type*} [Fintype ι]
    (p : Quartic) (cap mu D epsilon : ℝ) (value weight removed : ι → ℝ)
    (m1 m2 m3 m4 alpha : ℝ) (hmu : 0 < mu) (hdual : DualFeasible p cap)
    (h : TrimmedMomentInputs value weight removed m1 m2 m3 m4 alpha)
    (halpha : alpha ≤ (D - 1 - epsilon) / (2 * mu))
    (hstability : mu * residualTail value weight removed ≤ epsilon) :
    mu * (p.p0 + p.p1 * m1 + p.p2 * m2 + p.p3 * m3 + p.p4 * m4) -
        cap / 2 * (D - 1 - epsilon) ≤ epsilon := by
  have hscaled := finite_trimmed_quartic_dual_scaled p cap mu value weight removed
    m1 m2 m3 m4 alpha hmu.le hdual h
  have halphaMu : mu * alpha ≤ mu * ((D - 1 - epsilon) / (2 * mu)) :=
    mul_le_mul_of_nonneg_left halpha hmu.le
  have halphaCap : mu * alpha * cap ≤
      mu * ((D - 1 - epsilon) / (2 * mu)) * cap :=
    mul_le_mul_of_nonneg_right halphaMu hdual.cap_nonneg
  have hcancel :
      mu * ((D - 1 - epsilon) / (2 * mu)) * cap =
        cap / 2 * (D - 1 - epsilon) := by
    field_simp [hmu.ne']
  rw [hcancel] at halphaCap
  nlinarith

/-! ## 3. Exact top-hat moments -/

def topHatM2 (mu p : ℝ) : ℝ :=
  (1 - p) / p + mu ^ 2 * p / 3

def topHatM3 (mu p : ℝ) : ℝ :=
  (1 - p) ^ 3 / p ^ 2 - (1 - p) + mu ^ 2 * (1 - p)

def topHatM4 (mu p : ℝ) : ℝ :=
  (1 - p) ^ 4 / p ^ 3 + (1 - p) +
    2 * mu ^ 2 * (1 - p) ^ 2 / p + 4 * mu ^ 4 * p / 15

/-! ## 4. The support-1.9999 terminal quartic -/

namespace Terminal9506

def mu : ℝ := 4999 / 10000
def width : ℝ := 83 / 100
def a : ℝ := -9081 / 10000
def c : ℝ := 113 / 500
def t : ℝ := 4839 / 5000

def dual : Quartic where
  p0 := -(1090848126983561769588327 / 35405502805053456688250000)
  p1 := 9295744984575451767279 / 35405502805053456688250
  p2 := 66948615509905622970 / 141622011220213826753
  p3 := -(11128102684411400000 / 141622011220213826753)
  p4 := -(37369874615000000000 / 141622011220213826753)

def cap : ℝ := 34684079711986262847393 / 95458352130098292500000

def qNeg (y : ℝ) : ℝ :=
  -(5291233537196962800 / 141622011220213826753) +
    (56743063591351600000 / 141622011220213826753) * y -
    (37369874615000000000 / 141622011220213826753) * y ^ 2

def qSquare (y : ℝ) : ℝ :=
  85429409271169376583 / 141622011220213826753 +
    (28019286010391400000 / 141622011220213826753) * y +
    (37369874615000000000 / 141622011220213826753) * y ^ 2

def qCap (y : ℝ) : ℝ :=
  59596943857810532670 / 141622011220213826753 +
    (7587384726291400000 / 12874728292746711523) * y +
    (37369874615000000000 / 141622011220213826753) * y ^ 2

theorem contacts :
    dual.eval a = 0 ∧ dual.derivEval a = 0 ∧
    dual.eval c = c ^ 2 ∧ dual.derivEval c = 2 * c ∧
    dual.eval t = cap ∧ dual.derivEval t = 0 := by
  norm_num [dual, Quartic.eval, Quartic.derivEval, a, c, t, cap]

theorem factor_nonpos (y : ℝ) :
    dual.eval y = (y - a) ^ 2 * qNeg y := by
  norm_num [dual, Quartic.eval, a, qNeg]
  ring

theorem factor_square (y : ℝ) :
    y ^ 2 - dual.eval y = (y - c) ^ 2 * qSquare y := by
  norm_num [dual, Quartic.eval, c, qSquare]
  ring

theorem factor_cap (y : ℝ) :
    cap - dual.eval y = (y - t) ^ 2 * qCap y := by
  norm_num [dual, Quartic.eval, cap, t, qCap]
  ring

private theorem qNeg_nonpos {y : ℝ} (hy : y ≤ 0) : qNeg y ≤ 0 := by
  have hlin :
      (56743063591351600000 / 141622011220213826753 : ℝ) * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) hy
  have hquad :
      -(37369874615000000000 / 141622011220213826753 : ℝ) * y ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg y)
  unfold qNeg
  nlinarith

private theorem qSquare_pos (y : ℝ) : 0 < qSquare y := by
  simpa only [qSquare] using quadratic_pos_of_discriminant_neg
    (85429409271169376583 / 141622011220213826753)
    (28019286010391400000 / 141622011220213826753)
    (37369874615000000000 / 141622011220213826753) y
    (by norm_num) (by norm_num)

private theorem qCap_pos (y : ℝ) : 0 < qCap y := by
  simpa only [qCap] using quadratic_pos_of_discriminant_neg
    (59596943857810532670 / 141622011220213826753)
    (7587384726291400000 / 12874728292746711523)
    (37369874615000000000 / 141622011220213826753) y
    (by norm_num) (by norm_num)

/-- The support-1.9999 rational quartic satisfies all three inequalities
globally, not merely on a grid. -/
theorem dual_feasible : DualFeasible dual cap := by
  refine ⟨by norm_num [cap], ?_, ?_, ?_⟩
  · intro y hy
    rw [factor_nonpos]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (qNeg_nonpos hy)
  · intro y _
    apply sub_nonneg.mp
    rw [factor_square]
    exact mul_nonneg (sq_nonneg _) (qSquare_pos y).le
  · intro y _
    apply sub_nonneg.mp
    rw [factor_cap]
    exact mul_nonneg (sq_nonneg _) (qCap_pos y).le

def m2 : ℝ := topHatM2 mu width
def m3 : ℝ := topHatM3 mu width
def m4 : ℝ := topHatM4 mu width

theorem exact_moments :
    m2 = 682156116889 / 2490000000000 ∧
    m3 = -(8293346012887 / 68890000000000) ∧
    m4 = 434598816917989781038321 / 2144201250000000000000000 := by
  norm_num [m2, m3, m4, topHatM2, topHatM3, topHatM4, mu, width]

def AP : ℝ := dual.p0 + dual.p2 * m2 + dual.p3 * m3 + dual.p4 * m4

theorem AP_exact :
    AP = 2656428028876877176306155297737641 /
      48586574957743442014570566600000000 := by
  norm_num [AP, dual, m2, m3, m4, topHatM2, topHatM3, topHatM4, mu, width]

/-- The finite terminal weak bound under the explicit bridge fields. -/
theorem finite_terminal_bound {ι : Type*} [Fintype ι]
    (value weight removed : ι → ℝ) (alpha : ℝ)
    (h : TrimmedMomentInputs value weight removed 0 m2 m3 m4 alpha) :
    AP - alpha * cap ≤ residualTail value weight removed := by
  simpa only [AP, mul_zero, add_zero] using
    finite_trimmed_quartic_dual dual cap value weight removed 0 m2 m3 m4 alpha dual_feasible h

def costUpper : ℝ := 106772567 / 100000000

def fixedPoint : ℝ :=
  (mu * AP - cap / 2 * (costUpper - 1)) / (1 - cap / 2)

theorem cap_slope : cap / 2 < 1 := by norm_num [cap]

theorem fixedPoint_gt_terminal :
    (1836399187565 / 100000000000000 : ℝ) < fixedPoint := by
  norm_num [fixedPoint, costUpper, AP, dual, cap, m2, m3, m4,
    topHatM2, topHatM3, topHatM4, mu, width]

theorem fixedPoint_le_of_affine {epsilon : ℝ}
    (h : mu * AP - cap / 2 * (costUpper - 1 - epsilon) ≤ epsilon) :
    fixedPoint ≤ epsilon := by
  exact affine_fixed_point (by norm_num [cap]) cap_slope h

/-- Exact arithmetic clears the frozen R-9506 constant, conditional only
on a later bridge supplying the stability and moment premises. -/
theorem density_gt_frozen :
    (95063832187565 / 100000000000000 : ℝ) < 2 - costUpper + fixedPoint := by
  norm_num [fixedPoint, costUpper, AP, dual, cap, m2, m3, m4,
    topHatM2, topHatM3, topHatM4, mu, width]

/-- Full finite certificate assembly under explicit bridge propositions. -/
theorem density_gt_frozen_of_inputs {ι : Type*} [Fintype ι]
    (value weight removed : ι → ℝ) (alpha epsilon : ℝ)
    (h : TrimmedMomentInputs value weight removed 0 m2 m3 m4 alpha)
    (halpha : alpha ≤ (costUpper - 1 - epsilon) / (2 * mu))
    (hstability : mu * residualTail value weight removed ≤ epsilon) :
    (95063832187565 / 100000000000000 : ℝ) < 2 - costUpper + epsilon := by
  have haffine : mu * AP - cap / 2 * (costUpper - 1 - epsilon) ≤ epsilon := by
    simpa only [AP, mul_zero, add_zero] using
      affine_bound_of_finite_inputs dual cap mu costUpper epsilon value weight removed
        0 m2 m3 m4 alpha (by norm_num [mu]) dual_feasible h halpha hstability
  have hfp := fixedPoint_le_of_affine haffine
  linarith [density_gt_frozen]

theorem density_gt_frozen_of_bridge {ι : Type*} [Fintype ι]
    (value weight removed : ι → ℝ) (alpha epsilon : ℝ)
    (h : StabilityMomentBridge value weight removed 0 m2 m3 m4 alpha
      mu costUpper epsilon) :
    (95063832187565 / 100000000000000 : ℝ) < 2 - costUpper + epsilon :=
  density_gt_frozen_of_inputs value weight removed alpha epsilon
    h.moments h.trim_fraction h.stability_tail

end Terminal9506

/-! ## 5. The support-1.4999 terminal quartic -/

namespace Terminal8686

def mu : ℝ := 4999 / 10000
def width : ℝ := 89 / 100
def a : ℝ := -1781 / 2000
def c : ℝ := 911 / 10000
def t : ℝ := 6623 / 10000

def dual : Quartic where
  p0 := -(7292013177270507427703 / 1062484504309186560000000)
  p1 := 943433668075922881 / 6324312525649920000
  p2 := 9043183145019377 / 44270187679549440
  p3 := -(17128802264125 / 118580859855936)
  p4 := -(13671476640625 / 69172168249296)

def cap : ℝ := 204953852069001839 / 2018328905500000000

def qNeg (y : ℝ) : ℝ :=
  -(2298897488736623 / 265621126077296640) +
    (344570365829125 / 1660132037983104) * y -
    (13671476640625 / 69172168249296) * y ^ 2

def qSquare (y : ℝ) : ℝ :=
  43931971701345715 / 53124225215459328 +
    (299585864751875 / 1660132037983104) * y +
    (13671476640625 / 69172168249296) * y ^ 2

def qCap (y : ℝ) : ℝ :=
  65647829049234143 / 265621126077296640 +
    (674424942693875 / 1660132037983104) * y +
    (13671476640625 / 69172168249296) * y ^ 2

theorem contacts :
    dual.eval a = 0 ∧ dual.derivEval a = 0 ∧
    dual.eval c = c ^ 2 ∧ dual.derivEval c = 2 * c ∧
    dual.eval t = cap ∧ dual.derivEval t = 0 := by
  norm_num [dual, Quartic.eval, Quartic.derivEval, a, c, t, cap]

theorem factor_nonpos (y : ℝ) :
    dual.eval y = (y - a) ^ 2 * qNeg y := by
  norm_num [dual, Quartic.eval, a, qNeg]
  ring

theorem factor_square (y : ℝ) :
    y ^ 2 - dual.eval y = (y - c) ^ 2 * qSquare y := by
  norm_num [dual, Quartic.eval, c, qSquare]
  ring

theorem factor_cap (y : ℝ) :
    cap - dual.eval y = (y - t) ^ 2 * qCap y := by
  norm_num [dual, Quartic.eval, cap, t, qCap]
  ring

private theorem qNeg_nonpos {y : ℝ} (hy : y ≤ 0) : qNeg y ≤ 0 := by
  have hlin : (344570365829125 / 1660132037983104 : ℝ) * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) hy
  have hquad : -(13671476640625 / 69172168249296 : ℝ) * y ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg y)
  unfold qNeg
  nlinarith

private theorem qSquare_pos (y : ℝ) : 0 < qSquare y := by
  simpa only [qSquare] using quadratic_pos_of_discriminant_neg
    (43931971701345715 / 53124225215459328)
    (299585864751875 / 1660132037983104)
    (13671476640625 / 69172168249296) y
    (by norm_num) (by norm_num)

private theorem qCap_pos (y : ℝ) : 0 < qCap y := by
  simpa only [qCap] using quadratic_pos_of_discriminant_neg
    (65647829049234143 / 265621126077296640)
    (674424942693875 / 1660132037983104)
    (13671476640625 / 69172168249296) y
    (by norm_num) (by norm_num)

/-- The support-1.4999 rational quartic satisfies all three inequalities
globally. -/
theorem dual_feasible : DualFeasible dual cap := by
  refine ⟨by norm_num [cap], ?_, ?_, ?_⟩
  · intro y hy
    rw [factor_nonpos]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (qNeg_nonpos hy)
  · intro y _
    apply sub_nonneg.mp
    rw [factor_square]
    exact mul_nonneg (sq_nonneg _) (qSquare_pos y).le
  · intro y _
    apply sub_nonneg.mp
    rw [factor_cap]
    exact mul_nonneg (sq_nonneg _) (qCap_pos y).le

def m2 : ℝ := topHatM2 mu width
def m3 : ℝ := topHatM3 mu width
def m4 : ℝ := topHatM4 mu width

theorem exact_moments :
    m2 = 527945797921 / 2670000000000 ∧
    m3 = -(6402596222869 / 79210000000000) ∧
    m4 = 348494870075912117922241 / 2643633750000000000000000 := by
  norm_num [m2, m3, m4, topHatM2, topHatM3, topHatM4, mu, width]

def AP : ℝ := dual.p0 + dual.p2 * m2 + dual.p3 * m3 + dual.p4 * m4

theorem AP_exact :
    AP = 29882276809014040891941502329751 /
      1560455496913214458368000000000000 := by
  norm_num [AP, dual, m2, m3, m4, topHatM2, topHatM3, topHatM4, mu, width]

theorem finite_terminal_bound {ι : Type*} [Fintype ι]
    (value weight removed : ι → ℝ) (alpha : ℝ)
    (h : TrimmedMomentInputs value weight removed 0 m2 m3 m4 alpha) :
    AP - alpha * cap ≤ residualTail value weight removed := by
  simpa only [AP, mul_zero, add_zero] using
    finite_trimmed_quartic_dual dual cap value weight removed 0 m2 m3 m4 alpha dual_feasible h

def costUpper : ℝ := 113434643 / 100000000

def fixedPoint : ℝ :=
  (mu * AP - cap / 2 * (costUpper - 1)) / (1 - cap / 2)

theorem cap_slope : cap / 2 < 1 := by norm_num [cap]

theorem fixedPoint_gt_terminal :
    (28989382854 / 10000000000000 : ℝ) < fixedPoint := by
  norm_num [fixedPoint, costUpper, AP, dual, cap, m2, m3, m4,
    topHatM2, topHatM3, topHatM4, mu, width]

theorem fixedPoint_le_of_affine {epsilon : ℝ}
    (h : mu * AP - cap / 2 * (costUpper - 1 - epsilon) ≤ epsilon) :
    fixedPoint ≤ epsilon := by
  exact affine_fixed_point (by norm_num [cap]) cap_slope h

/-- Exact arithmetic clears the frozen R-8686 constant, conditional only
on a later bridge supplying the stability and moment premises. -/
theorem density_gt_frozen :
    (86855250 / 100000000 : ℝ) < 2 - costUpper + fixedPoint := by
  norm_num [fixedPoint, costUpper, AP, dual, cap, m2, m3, m4,
    topHatM2, topHatM3, topHatM4, mu, width]

theorem density_gt_frozen_of_inputs {ι : Type*} [Fintype ι]
    (value weight removed : ι → ℝ) (alpha epsilon : ℝ)
    (h : TrimmedMomentInputs value weight removed 0 m2 m3 m4 alpha)
    (halpha : alpha ≤ (costUpper - 1 - epsilon) / (2 * mu))
    (hstability : mu * residualTail value weight removed ≤ epsilon) :
    (86855250 / 100000000 : ℝ) < 2 - costUpper + epsilon := by
  have haffine : mu * AP - cap / 2 * (costUpper - 1 - epsilon) ≤ epsilon := by
    simpa only [AP, mul_zero, add_zero] using
      affine_bound_of_finite_inputs dual cap mu costUpper epsilon value weight removed
        0 m2 m3 m4 alpha (by norm_num [mu]) dual_feasible h halpha hstability
  have hfp := fixedPoint_le_of_affine haffine
  linarith [density_gt_frozen]

theorem density_gt_frozen_of_bridge {ι : Type*} [Fintype ι]
    (value weight removed : ι → ℝ) (alpha epsilon : ℝ)
    (h : StabilityMomentBridge value weight removed 0 m2 m3 m4 alpha
      mu costUpper epsilon) :
    (86855250 / 100000000 : ℝ) < 2 - costUpper + epsilon :=
  density_gt_frozen_of_inputs value weight removed alpha epsilon
    h.moments h.trim_fraction h.stability_tail

end Terminal8686

end

end TrimmedMoment
end Zeta85
end RH
