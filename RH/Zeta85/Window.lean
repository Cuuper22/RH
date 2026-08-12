/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Window.lean — **Phase A1**: the support-143/100 window and its three exact moments.

Source: `docs/run/01_certificate_cycle1.md`, equations (7)–(9).

  λ  := 143/100,      v(s) := 1 − (169/100)·s²   on [−1/2, 1/2],
  A  := ∫_{−1/2}^{1/2} v            = 1031/1200,
  B  := ∫_{−1/2}^{1/2} v²           = 1809683/2400000,
  g u := ∫_{−1/2}^{1/2−u} v(s)·v(s+u) ds
       = 1809683/2400000 − (53361/160000)·u − (174239/120000)·u² + (169/150)·u³ − (28561/300000)·u⁵,
  J  := 2·(λ·∫_0^{1/λ} u·g u du + ∫_{1/λ}^{1} g u du) = 970487502160963/3017889594720000.

Everything here is PROVED from Mathlib's interval integration of polynomials — no axioms, no
`sorry`, no numerics.  `Certificate.lean` then assembles `c_pc = λA²/(B + λJ)`.

The identity `J = ∬_{[−1/2,1/2]²} min(λ|s−t|,1)·v(s)·v(t) ds dt`, which is how
`01_certificate_cycle1.md` (9) introduces `J`, is recorded here as the *definition* of `jSat` in the
one-dimensional autocorrelation form the source itself uses ("= 2(λ∫₀^{1/λ} u g(u) du + ∫_{1/λ}^1 g(u)
du)"); the two-dimensional integral is not needed downstream, since the prime-side hypothesis of
`RH/Zeta85/Hypotheses.lean` is stated directly in terms of the normalized cost `D = (B + λJ)/(λA²)`.
See `FINDINGS.md` §2 for why the 1-D form is the faithful reading.
-/
import Mathlib

open intervalIntegral MeasureTheory

noncomputable section

namespace RH
namespace Zeta85

/-! ## 1. The window -/

/-- λ = 143/100, the Fourier support of the certificate  [01_certificate_cycle1.md (7)]. -/
def lam : ℝ := 143 / 100

/-- v(s) = 1 − (169/100)·s², the quadratic profile on [−1/2,1/2]  [01_certificate_cycle1.md (7)]. -/
def vProf (s : ℝ) : ℝ := 1 - (169 / 100) * s ^ 2

lemma lam_pos : 0 < lam := by norm_num [lam]

lemma lam_gt_one : 1 < lam := by norm_num [lam]

/-- The profile is strictly positive on the closed window: `v(±1/2) = 1 − 169/400 > 0`. -/
lemma vProf_pos {s : ℝ} (hs : |s| ≤ 1 / 2) : 0 < vProf s := by
  have h : s ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have := abs_le.mp hs
    nlinarith [this.1, this.2]
  simp only [vProf]
  nlinarith [h]

/-! ## 2. `A = ∫ v` and `B = ∫ v²` -/

/-- A := ∫_{−1/2}^{1/2} v(s) ds = 1031/1200  [01_certificate_cycle1.md (9)]. -/
theorem integral_vProf : (∫ s in (-(1:ℝ)/2)..(1/2), vProf s) = 1031 / 1200 := by
  simp only [vProf]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (((intervalIntegral.intervalIntegrable_pow 2).const_mul _))]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num

/-- B := ∫_{−1/2}^{1/2} v(s)² ds = 1809683/2400000  [01_certificate_cycle1.md (9)]. -/
theorem integral_vProf_sq : (∫ s in (-(1:ℝ)/2)..(1/2), vProf s ^ 2) = 1809683 / 2400000 := by
  have hrw : ∀ s : ℝ, vProf s ^ 2
      = 1 - (169 / 50) * s ^ 2 + (28561 / 10000) * s ^ 4 := by
    intro s; simp only [vProf]; ring
  simp only [hrw]
  rw [intervalIntegral.integral_add
      (((intervalIntegrable_const).sub ((intervalIntegral.intervalIntegrable_pow 2).const_mul _)))
      ((intervalIntegral.intervalIntegrable_pow 4).const_mul _),
    intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegral.intervalIntegrable_pow 2).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num

/-! ## 3. The autocorrelation `g` -/

/-- The explicit quintic of `01_certificate_cycle1.md` (8). -/
def gPoly (u : ℝ) : ℝ :=
  1809683 / 2400000 - (53361 / 160000) * u - (174239 / 120000) * u ^ 2
    + (169 / 150) * u ^ 3 - (28561 / 300000) * u ^ 5

/-- `g(u) = ∫_{−1/2}^{1/2−u} v(s)·v(s+u) ds` equals the quintic `gPoly`
[01_certificate_cycle1.md (8)].  Proved by evaluating the antiderivative of the (bivariate)
polynomial integrand at the two endpoints and expanding. -/
theorem integral_autocorr (u : ℝ) :
    (∫ s in (-(1:ℝ)/2)..(1/2 - u), vProf s * vProf (s + u)) = gPoly u := by
  -- expand the integrand as a polynomial in `s` with coefficients polynomial in `u`
  have hrw : ∀ s : ℝ, vProf s * vProf (s + u)
      = (1 - (169 / 100) * u ^ 2)
        + (-(169 / 50) * u) * s ^ 1
        + (-(169 / 50) + (28561 / 10000) * u ^ 2) * s ^ 2
        + ((28561 / 5000) * u) * s ^ 3
        + (28561 / 10000) * s ^ 4 := by
    intro s; simp only [vProf]; ring
  simp only [hrw]
  have hint : ∀ (c : ℝ) (n : ℕ), IntervalIntegrable (fun s : ℝ => c * s ^ n) volume
      (-(1:ℝ)/2) (1/2 - u) := fun c n => (intervalIntegral.intervalIntegrable_pow n).const_mul c
  rw [intervalIntegral.integral_add
        (((intervalIntegrable_const.add (hint _ 1)).add (hint _ 2)).add (hint _ 3)) (hint _ 4),
      intervalIntegral.integral_add
        ((intervalIntegrable_const.add (hint _ 1)).add (hint _ 2)) (hint _ 3),
      intervalIntegral.integral_add (intervalIntegrable_const.add (hint _ 1)) (hint _ 2),
      intervalIntegral.integral_add intervalIntegrable_const (hint _ 1)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const,
    smul_eq_mul]
  simp only [gPoly]
  ring

/-! ## 4. `J`, the saturated pair term -/

/-- J := 2·(λ·∫_0^{1/λ} u·g(u) du + ∫_{1/λ}^{1} g(u) du)  [01_certificate_cycle1.md (9)]. -/
def jSat : ℝ := 2 * (lam * (∫ u in (0:ℝ)..(1 / lam), u * gPoly u) + ∫ u in (1 / lam)..(1:ℝ), gPoly u)

private lemma integral_gPoly_aux (a b : ℝ) :
    (∫ u in a..b, gPoly u) =
      (1809683 / 2400000 * b - 53361 / 320000 * b ^ 2 - 174239 / 360000 * b ^ 3
        + 169 / 600 * b ^ 4 - 28561 / 1800000 * b ^ 6)
      - (1809683 / 2400000 * a - 53361 / 320000 * a ^ 2 - 174239 / 360000 * a ^ 3
        + 169 / 600 * a ^ 4 - 28561 / 1800000 * a ^ 6) := by
  have hint : ∀ (c : ℝ) (n : ℕ), IntervalIntegrable (fun s : ℝ => c * s ^ n) volume a b :=
    fun c n => (intervalIntegral.intervalIntegrable_pow n).const_mul c
  have hrw : ∀ u : ℝ, gPoly u
      = 1809683 / 2400000 + (-(53361 / 160000)) * u ^ 1 + (-(174239 / 120000)) * u ^ 2
        + (169 / 150) * u ^ 3 + (-(28561 / 300000)) * u ^ 5 := by
    intro u; simp only [gPoly]; ring
  simp only [hrw]
  rw [intervalIntegral.integral_add
        ((((intervalIntegrable_const.add (hint _ 1)).add (hint _ 2)).add (hint _ 3))) (hint _ 5),
      intervalIntegral.integral_add
        (((intervalIntegrable_const.add (hint _ 1)).add (hint _ 2))) (hint _ 3),
      intervalIntegral.integral_add ((intervalIntegrable_const.add (hint _ 1))) (hint _ 2),
      intervalIntegral.integral_add intervalIntegrable_const (hint _ 1)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const,
    smul_eq_mul]
  ring

private lemma integral_u_gPoly_aux (a b : ℝ) :
    (∫ u in a..b, u * gPoly u) =
      (1809683 / 4800000 * b ^ 2 - 53361 / 480000 * b ^ 3 - 174239 / 480000 * b ^ 4
        + 169 / 750 * b ^ 5 - 28561 / 2100000 * b ^ 7)
      - (1809683 / 4800000 * a ^ 2 - 53361 / 480000 * a ^ 3 - 174239 / 480000 * a ^ 4
        + 169 / 750 * a ^ 5 - 28561 / 2100000 * a ^ 7) := by
  have hint : ∀ (c : ℝ) (n : ℕ), IntervalIntegrable (fun s : ℝ => c * s ^ n) volume a b :=
    fun c n => (intervalIntegral.intervalIntegrable_pow n).const_mul c
  have hrw : ∀ u : ℝ, u * gPoly u
      = (1809683 / 2400000) * u ^ 1 + (-(53361 / 160000)) * u ^ 2 + (-(174239 / 120000)) * u ^ 3
        + (169 / 150) * u ^ 4 + (-(28561 / 300000)) * u ^ 6 := by
    intro u; simp only [gPoly]; ring
  simp only [hrw]
  rw [intervalIntegral.integral_add
        (((((hint _ 1).add (hint _ 2)).add (hint _ 3)).add (hint _ 4))) (hint _ 6),
      intervalIntegral.integral_add ((((hint _ 1).add (hint _ 2)).add (hint _ 3))) (hint _ 4),
      intervalIntegral.integral_add (((hint _ 1).add (hint _ 2))) (hint _ 3),
      intervalIntegral.integral_add (hint _ 1) (hint _ 2)]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  ring

/-- J = 970487502160963/3017889594720000  [01_certificate_cycle1.md (9)]. -/
theorem jSat_eq : jSat = 970487502160963 / 3017889594720000 := by
  simp only [jSat, integral_gPoly_aux, integral_u_gPoly_aux, lam]
  norm_num

end Zeta85
end RH

end
