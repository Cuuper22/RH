/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Certificate
import RH.Zeta85.Statement
import Zeta23.XiPrime.Certificate.Poly

/-!
# Exact rational-polynomial witness for R-679

The degree-six Taylor profile

`1 - s^2 + s^4 / 6 - s^6 / 90`

has saturated support-`101/100` cost strictly below the frozen rational
bound.  Adding a nonnegative constant varies the exact cost continuously;
the defect is positive at `0` and negative at `1/100000`.  The intermediate
value theorem therefore supplies a literal profile having exactly the cost
required by `SaturatedWindowCost`.
-/

open Set intervalIntegral MeasureTheory

noncomputable section

namespace RH
namespace Zeta85
namespace Window101

private def sigma : ℝ := 101 / 100

private def base (s : ℝ) : ℝ :=
  1 - s ^ 2 + s ^ 4 / 6 - s ^ 6 / 90

private def profile (d s : ℝ) : ℝ := base s + d

private def baseCoeff : List ℝ :=
  [1, 0, -1, 0, 1 / 6, 0, -(1 / 90)]

private def baseSqCoeff : List ℝ :=
  [1, 0, -2, 0, 4 / 3, 0, -(16 / 45), 0, 1 / 20, 0,
    -(1 / 270), 0, 1 / 8100]

private def profileCoeff (d : ℝ) : List ℝ :=
  [1 + d, 0, -1, 0, 1 / 6, 0, -(1 / 90)]

private def profileSqCoeff (d : ℝ) : List ℝ :=
  [(1 + d) ^ 2, 0, -2 * (1 + d), 0, 4 / 3 + d / 3, 0,
    -(16 / 45) - d / 45, 0, 1 / 20, 0, -(1 / 270), 0, 1 / 8100]

set_option maxRecDepth 100000 in
private theorem base_eq_polyEval :
    base = Zeta23.XiPrime.polyEval baseCoeff := by
  funext s
  simp [base, Zeta23.XiPrime.polyEval, baseCoeff, Finset.sum_range_succ]
  ring

set_option maxRecDepth 100000 in
private theorem base_sq_eq_polyEval :
    (fun s => base s ^ 2) = Zeta23.XiPrime.polyEval baseSqCoeff := by
  funext s
  simp [base, Zeta23.XiPrime.polyEval, baseSqCoeff, Finset.sum_range_succ]
  ring

set_option maxRecDepth 100000 in
private theorem profile_eq_polyEval (d : ℝ) :
    profile d = Zeta23.XiPrime.polyEval (profileCoeff d) := by
  funext s
  simp [profile, base, Zeta23.XiPrime.polyEval, profileCoeff,
    Finset.sum_range_succ]
  ring

set_option maxRecDepth 100000 in
private theorem profile_sq_eq_polyEval (d : ℝ) :
    (fun s => profile d s ^ 2) =
      Zeta23.XiPrime.polyEval (profileSqCoeff d) := by
  funext s
  simp [profile, base, Zeta23.XiPrime.polyEval, profileSqCoeff,
    Finset.sum_range_succ]
  ring

private theorem base_pos {s : ℝ} (hs : |s| ≤ 1 / 2) : 0 < base s := by
  have hs' := abs_le.mp hs
  have hs2 : s ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hbracket : 0 ≤ (1 / 6 : ℝ) - s ^ 2 / 90 := by nlinarith
  have hterm : 0 ≤ s ^ 4 * ((1 / 6 : ℝ) - s ^ 2 / 90) :=
    mul_nonneg (by positivity) hbracket
  have hid : base s = (1 - s ^ 2) + s ^ 4 * (1 / 6 - s ^ 2 / 90) := by
    simp only [base]
    ring
  rw [hid]
  nlinarith

private theorem profile_pos {d s : ℝ} (hd : 0 ≤ d) (hs : |s| ≤ 1 / 2) :
    0 < profile d s := by
  unfold profile
  exact add_pos_of_pos_of_nonneg (base_pos hs) hd

private theorem integral_profile (d : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), profile d s) = 37043 / 40320 + d := by
  rw [profile_eq_polyEval, Zeta23.XiPrime.integral_polyEval]
  simp [Zeta23.XiPrime.polyInt, profileCoeff, Finset.sum_range_succ]
  ring

private theorem integral_profile_sq (d : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), profile d s ^ 2) =
      28203513077 / 33210777600 + 2 * d * (37043 / 40320) + d ^ 2 := by
  rw [profile_sq_eq_polyEval, Zeta23.XiPrime.integral_polyEval]
  simp [Zeta23.XiPrime.polyInt, profileSqCoeff, Finset.sum_range_succ]
  ring

/-! ## Exact autocorrelation -/

private def centeredCoeff (u : ℝ) : List ℝ :=
  [1 - (1 / 2) * u ^ 2 + (1 / 12) * u ^ 4 - (1 / 180) * u ^ 6 +
      (1 / 5120) * u ^ 8 - (1 / 276480) * u ^ 10 + (1 / 33177600) * u ^ 12,
   0,
   -2 - (1 / 2880) * u ^ 6 + (1 / 23040) * u ^ 8 - (1 / 1382400) * u ^ 10,
   0,
   4 / 3 - (1 / 288) * u ^ 4 - (1 / 8640) * u ^ 6 + (1 / 138240) * u ^ 8,
   0,
   -(16 / 45) - (1 / 180) * u ^ 2 - (1 / 2160) * u ^ 4 -
      (1 / 25920) * u ^ 6,
   0,
   1 / 20 + (1 / 360) * u ^ 2 + (1 / 8640) * u ^ 4,
   0,
   -(1 / 270) - (1 / 5400) * u ^ 2,
   0,
   1 / 8100]

private def autocorrCoeff : List ℝ :=
  [28203513077 / 33210777600,
   -(19175641 / 33177600),
   -(108477623 / 127733760),
   1090889 / 2073600,
   1230199 / 8709120,
   -(118001 / 1382400),
   -(37043 / 3628800),
   2 / 315,
   0,
   -(1 / 7560),
   0,
   1 / 623700,
   0,
   -(1 / 97297200)]

private def autocorr (u : ℝ) : ℝ :=
  Zeta23.XiPrime.polyEval autocorrCoeff u

set_option maxRecDepth 100000 in
private theorem centered_product (u t : ℝ) :
    base (t - u / 2) * base (t + u / 2) =
      Zeta23.XiPrime.polyEval (centeredCoeff u) t := by
  simp [base, Zeta23.XiPrime.polyEval, centeredCoeff, Finset.sum_range_succ]
  ring

set_option maxRecDepth 100000 in
private theorem centered_integral (u : ℝ) :
    (∫ t in (-(1 - u) / 2)..((1 - u) / 2),
      base (t - u / 2) * base (t + u / 2)) = autocorr u := by
  rw [intervalIntegral.integral_congr (fun t _ => centered_product u t),
    Zeta23.XiPrime.integral_polyEval]
  simp [Zeta23.XiPrime.polyInt, centeredCoeff, autocorr,
    Zeta23.XiPrime.polyEval, autocorrCoeff, Finset.sum_range_succ]
  ring

private theorem integral_autocorr (u : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u), base s * base (s + u)) =
      autocorr u := by
  calc
    _ = ∫ t in (-(1 : ℝ) / 2 + u / 2)..(1 / 2 - u + u / 2),
        base (t - u / 2) * base (t + u / 2) := by
      rw [← intervalIntegral.integral_comp_add_right
        (f := fun t => base (t - u / 2) * base (t + u / 2)) (u / 2)]
      apply intervalIntegral.integral_congr
      intro s _
      change base s * base (s + u) =
        base (s + u / 2 - u / 2) * base (s + u / 2 + u / 2)
      have hleft : s + u / 2 - u / 2 = s := by ring
      have hright : s + u / 2 + u / 2 = s + u := by ring
      rw [hleft, hright]
    _ = ∫ t in (-(1 - u) / 2)..((1 - u) / 2),
        base (t - u / 2) * base (t + u / 2) := by
      rw [show (-(1 : ℝ) / 2 + u / 2) = -(1 - u) / 2 by ring,
        show (1 / 2 - u + u / 2 : ℝ) = (1 - u) / 2 by ring]
    _ = autocorr u := centered_integral u

private def crossCoeff : List ℝ :=
  [37043 / 40320, -(4379 / 5760), -(147 / 320), 73 / 288,
    11 / 144, -(1 / 40), -(1 / 180), 1 / 630]

private def crossCorr (u : ℝ) : ℝ :=
  Zeta23.XiPrime.polyEval crossCoeff u

private theorem integral_cross_left (u : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u), base s) = crossCorr u := by
  rw [base_eq_polyEval, Zeta23.XiPrime.integral_polyEval]
  simp [Zeta23.XiPrime.polyInt, baseCoeff, crossCorr,
    Zeta23.XiPrime.polyEval, crossCoeff, Finset.sum_range_succ]
  ring

private def shiftedCoeff (u : ℝ) : List ℝ :=
  [1 - u ^ 2 + (1 / 6) * u ^ 4 - (1 / 90) * u ^ 6,
   -2 * u + (2 / 3) * u ^ 3 - (1 / 15) * u ^ 5,
   -1 + u ^ 2 - (1 / 6) * u ^ 4,
   (2 / 3) * u - (2 / 9) * u ^ 3,
   1 / 6 - (1 / 6) * u ^ 2,
   -(1 / 15) * u,
   -(1 / 90)]

set_option maxRecDepth 100000 in
private theorem shifted_eq_polyEval (u : ℝ) :
    (fun s => base (s + u)) = Zeta23.XiPrime.polyEval (shiftedCoeff u) := by
  funext s
  simp [base, Zeta23.XiPrime.polyEval, shiftedCoeff, Finset.sum_range_succ]
  ring

private theorem integral_cross_right (u : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u), base (s + u)) = crossCorr u := by
  rw [shifted_eq_polyEval, Zeta23.XiPrime.integral_polyEval]
  simp [Zeta23.XiPrime.polyInt, shiftedCoeff, crossCorr,
    Zeta23.XiPrime.polyEval, crossCoeff, Finset.sum_range_succ]
  ring

private def perturbedAutocorrCoeff (d : ℝ) : List ℝ :=
  [28203513077 / 33210777600 + (37043 / 20160) * d + d ^ 2,
   -(19175641 / 33177600) - (4379 / 2880) * d - d ^ 2,
   -(108477623 / 127733760) - (147 / 160) * d,
   1090889 / 2073600 + (73 / 144) * d,
   1230199 / 8709120 + (11 / 72) * d,
   -(118001 / 1382400) - (1 / 20) * d,
   -(37043 / 3628800) - (1 / 90) * d,
   2 / 315 + (1 / 315) * d,
   0,
   -(1 / 7560),
   0,
   1 / 623700,
   0,
   -(1 / 97297200)]

private def perturbedAutocorr (d u : ℝ) : ℝ :=
  Zeta23.XiPrime.polyEval (perturbedAutocorrCoeff d) u

set_option maxRecDepth 100000 in
private theorem perturbedAutocorr_closed (d u : ℝ) :
    perturbedAutocorr d u =
      autocorr u + 2 * d * crossCorr u + d ^ 2 * (1 - u) := by
  simp [perturbedAutocorr, autocorr, crossCorr, Zeta23.XiPrime.polyEval,
    perturbedAutocorrCoeff, autocorrCoeff, crossCoeff, Finset.sum_range_succ]
  ring

private theorem integral_profile_autocorr (d u : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u),
      profile d s * profile d (s + u)) = perturbedAutocorr d u := by
  have hbase : IntervalIntegrable (fun s : ℝ => base s * base (s + u)) volume
      (-(1 : ℝ) / 2) (1 / 2 - u) := by
    apply Continuous.intervalIntegrable
    unfold base
    fun_prop
  have hleft : IntervalIntegrable base volume
      (-(1 : ℝ) / 2) (1 / 2 - u) := by
    apply Continuous.intervalIntegrable
    unfold base
    fun_prop
  have hright : IntervalIntegrable (fun s : ℝ => base (s + u)) volume
      (-(1 : ℝ) / 2) (1 / 2 - u) := by
    apply Continuous.intervalIntegrable
    unfold base
    fun_prop
  calc
    _ = ∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u),
        ((base s * base (s + u) + d * base s) + d * base (s + u)) + d ^ 2 := by
      apply intervalIntegral.integral_congr
      intro s _
      simp only [profile]
      ring
    _ = perturbedAutocorr d u := by
      rw [intervalIntegral.integral_add
          ((hbase.add (hleft.const_mul d)).add (hright.const_mul d))
            intervalIntegrable_const,
        intervalIntegral.integral_add (hbase.add (hleft.const_mul d))
          (hright.const_mul d),
        intervalIntegral.integral_add hbase (hleft.const_mul d),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_autocorr, integral_cross_left, integral_cross_right,
        intervalIntegral.integral_const, perturbedAutocorr_closed]
      simp only [smul_eq_mul]
      ring

private def uPerturbedAutocorrCoeff (d : ℝ) : List ℝ :=
  0 :: perturbedAutocorrCoeff d

set_option maxRecDepth 100000 in
private theorem u_mul_perturbedAutocorr (d : ℝ) :
    (fun u => u * perturbedAutocorr d u) =
      Zeta23.XiPrime.polyEval (uPerturbedAutocorrCoeff d) := by
  funext u
  simp [perturbedAutocorr, Zeta23.XiPrime.polyEval, perturbedAutocorrCoeff,
    uPerturbedAutocorrCoeff, Finset.sum_range_succ]
  ring

private theorem satJ_profile (d : ℝ) :
    satJ sigma (profile d) =
      6588996349358144174295937698908010666763 /
          24050207445244879851649505411965871308800 +
        2 * d * (1194128349053946564287 / 3929470413383177066880) +
        d ^ 2 * (10303 / 30603) := by
  simp only [satJ]
  simp_rw [integral_profile_autocorr d]
  rw [u_mul_perturbedAutocorr, Zeta23.XiPrime.integral_polyEval]
  change 2 * (sigma *
      Zeta23.XiPrime.polyInt (uPerturbedAutocorrCoeff d) 0 (1 / sigma) +
      (∫ u in (1 / sigma)..1,
        Zeta23.XiPrime.polyEval (perturbedAutocorrCoeff d) u)) = _
  rw [Zeta23.XiPrime.integral_polyEval]
  simp [sigma, Zeta23.XiPrime.polyInt, uPerturbedAutocorrCoeff,
    perturbedAutocorrCoeff, Finset.sum_range_succ]
  ring

/-! ## Exact crossing of the frozen cost -/

private def defect (d : ℝ) : ℝ :=
  (2 - cRung101) *
      (sigma * (37043 / 40320 + d) ^ 2) -
    (28203513077 / 33210777600 + 2 * d * (37043 / 40320) + d ^ 2 +
      sigma *
        (6588996349358144174295937698908010666763 /
            24050207445244879851649505411965871308800 +
          2 * d * (1194128349053946564287 / 3929470413383177066880) +
          d ^ 2 * (10303 / 30603)))

private theorem defect_pos_zero : 0 < defect 0 := by
  norm_num [defect, sigma, cRung101]

private theorem defect_neg_endpoint : defect (1 / 100000) < 0 := by
  norm_num [defect, sigma, cRung101]

private theorem continuous_defect : Continuous defect := by
  unfold defect sigma cRung101
  fun_prop

private theorem exists_exact_delta :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 / 100000 ∧ defect d = 0 := by
  have hzero : 0 ∈ Set.Icc (defect (1 / 100000)) (defect 0) :=
    ⟨defect_neg_endpoint.le, defect_pos_zero.le⟩
  obtain ⟨d, hd, hdef⟩ :=
    (intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1 / 100000)
      continuous_defect.continuousOn) hzero
  exact ⟨d, hd.1, hd.2, hdef⟩

/-- The support-`101/100` frozen window cost is unconditional. -/
theorem windowCost_101_proved :
    SaturatedWindowCost (101 / 100) (2 - cRung101) := by
  obtain ⟨d, hd0, _hd1, hdef⟩ := exists_exact_delta
  refine ⟨profile d, fun s hs => profile_pos hd0 hs, ?_, ?_⟩
  · rw [integral_profile]
    positivity
  · rw [show (101 / 100 : ℝ) = sigma by rfl]
    rw [integral_profile, integral_profile_sq, satJ_profile]
    have hzero :
        (2 - cRung101) *
            (sigma * (37043 / 40320 + d) ^ 2) -
          (28203513077 / 33210777600 + 2 * d * (37043 / 40320) + d ^ 2 +
            sigma *
              (6588996349358144174295937698908010666763 /
                  24050207445244879851649505411965871308800 +
                2 * d *
                  (1194128349053946564287 / 3929470413383177066880) +
                d ^ 2 * (10303 / 30603))) = 0 := by
      simpa only [defect] using hdef
    exact sub_eq_zero.mp hzero

end Window101
end Zeta85
end RH

end
