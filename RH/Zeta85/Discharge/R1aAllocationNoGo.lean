/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.R1aAllocationCapacity

/-!
# The R1a allocation obstruction at the current interface

This file derives the finite capacity hypotheses from the existing fields of
`PrincipalCyclicBlock`.  It uses only the `k = 1` translated-product clause,
the exact energy-ratio clause, and the almost-everywhere reconstruction
together with the nonnegative square summands in `windowEnergy`.
-/

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace R1aAllocationNoGo

open Zeta23 QuarticWindowWitnesses R1aAllocationCapacity TopHatMoments

private theorem topHat_integrable {p : ℝ} : Integrable (topHat p) := by
  exact (integrableOn_const (s := topHatSupport p)
    (by simp [topHatSupport, Real.volume_Icc])).integrable_indicator measurableSet_Icc

private theorem integral_supported_v8686 :
    (∫ x : ℝ, QuarticGramFamily.supportedFullProfile (v := v8686) x) =
      (3815170470337249 / 3814073303040000 : ℝ) := by
  change (∫ x : ℝ, (Icc (-(1 : ℝ) / 2) (1 / 2)).indicator v8686 x) = _
  rw [integral_indicator measurableSet_Icc]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hv := integral_v8686
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2)] at hv
  exact hv

private theorem integral_supported_v9506 :
    (∫ x : ℝ, QuarticGramFamily.supportedFullProfile (v := v9506) x) =
      (5913507107 / 5913600000 : ℝ) := by
  change (∫ x : ℝ, (Icc (-(1 : ℝ) / 2) (1 / 2)).indicator v9506 x) = _
  rw [integral_indicator measurableSet_Icc]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hv := integral_v9506
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2)] at hv
  exact hv

private theorem no_principal_of_active_capacity
    {Z : ZeroConfig} {sigma mu p A v0 : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hApos : 0 < A) (hqmu : (2 / 5 : ℝ) < mu)
    (hcell : mu * p < sigma)
    (hprofileIntegral :
      (∫ x : ℝ, QuarticGramFamily.supportedFullProfile (v := v) x) = A)
    (hprofileCap : ∀ s : ℝ, |s| ≤ mu * p / (2 * sigma) → v s ≤ v0)
    (hnumeric : mu * p * v0 <
      (99 / 100 : ℝ) * (2 / 5) * sigma * A) :
    ¬ PrincipalCyclicBlock F := by
  intro h
  have hratio : ∀ᶠ T in atTop,
      (2 / 5 : ℝ) < F.channelEnergy T (F.distinguished T) /
        (∫ u : ℝ, F.windowEnergy T u) :=
    h.distinguished_energy_ratio.eventually (eventually_gt_nhds hqmu)
  have htranslated : ∀ᶠ T in atTop,
      Integrable (fun x : ℝ =>
        |F.localProfile T x - topHat p x|) ∧
      (∫ x : ℝ, |F.localProfile T x - topHat p x|) ≤ 1 / 100 := by
    filter_upwards [h.translated_products_locally_uniform 1 (by norm_num) (by norm_num)
      1 (1 / 100) (by norm_num) (by norm_num)] with T hT
    have hT0 := hT (fun _ => 0) (by simp)
    simpa [Fin.prod_univ_succ] using hT0
  have hcommon := Zeta23.Assembly.eventually_l_pos.and h.periods_pos
  have hcommon := hcommon.and h.zero_alias_reconstruction
  have hcommon := hcommon.and h.distinguished_period
  have hcommon := hcommon.and hratio
  have hcommon := hcommon.and h.distinguished_channel_energy_pos
  have hcommon := hcommon.and h.local_profile_integrable
  have hcommon := hcommon.and h.windows_smooth
  have hcommon := hcommon.and h.windows_compact
  have hcommon := hcommon.and htranslated
  rcases hcommon.exists with ⟨T, hcommon⟩
  rcases hcommon with ⟨hcommon, herror⟩
  rcases hcommon with ⟨hcommon, hcompact⟩
  rcases hcommon with ⟨hcommon, hsmooth⟩
  rcases hcommon with ⟨hcommon, hlocalInt⟩
  rcases hcommon with ⟨hcommon, henergyPos⟩
  rcases hcommon with ⟨hcommon, hratioT⟩
  rcases hcommon with ⟨hcommon, hperiod⟩
  rcases hcommon with ⟨hcommon, hreconstruct⟩
  rcases hcommon with ⟨hell, hperiodPos⟩
  let j := F.distinguished T
  let L := F.period T j
  let energy := F.channelEnergy T j
  let total := ∫ u : ℝ, F.windowEnergy T u
  let mass := ∫ x in (-p / 2)..(p / 2), F.localProfile T x
  have hLpos : 0 < L := hperiodPos j
  have hL : L = mu * Zeta23.l T := by simpa [L, j] using hperiod
  have hEpos : 0 < energy := by simpa [energy, j] using henergyPos
  have hfullLengthPos : 0 < QuarticGramFamily.fullLength (σ := sigma) T := by
    dsimp [QuarticGramFamily.fullLength]
    exact mul_pos h.support_pos hell

  have htotal : total = sigma * Zeta23.l T * A := by
    calc
      total = ∫ u : ℝ,
          QuarticGramFamily.supportedFullProfile (v := v)
            (u / QuarticGramFamily.fullLength (σ := sigma) T) := by
        exact integral_congr_ae hreconstruct
      _ = |QuarticGramFamily.fullLength (σ := sigma) T| *
          (∫ x : ℝ, QuarticGramFamily.supportedFullProfile (v := v) x) := by
        simpa only [smul_eq_mul] using
          (MeasureTheory.Measure.integral_comp_div
            (QuarticGramFamily.supportedFullProfile (v := v))
            (QuarticGramFamily.fullLength (σ := sigma) T))
      _ = sigma * Zeta23.l T * A := by
        rw [abs_of_pos hfullLengthPos, hprofileIntegral]
        rfl

  have htotalPos : 0 < total := by
    rw [htotal]
    positivity
  have henergy : (2 / 5 : ℝ) * total < energy := by
    change (2 / 5 : ℝ) < energy / total at hratioT
    exact (lt_div_iff₀ htotalPos).mp hratioT

  have htopInt : IntervalIntegrable (topHat p) volume (-p / 2) (p / 2) :=
    topHat_integrable.intervalIntegrable
  have herrInt : IntervalIntegrable
      (fun x : ℝ => |F.localProfile T x - topHat p x|)
      volume (-p / 2) (p / 2) := herror.1.intervalIntegrable
  have hlowerPoint : ∀ x : ℝ,
      topHat p x - |F.localProfile T x - topHat p x| ≤ F.localProfile T x := by
    intro x
    have habs := neg_le_abs (F.localProfile T x - topHat p x)
    linarith
  have hlowerIntegral :
      (∫ x in (-p / 2)..(p / 2),
        topHat p x - |F.localProfile T x - topHat p x|) ≤ mass := by
    exact intervalIntegral.integral_mono_on (by linarith [h.fill_pos])
      (htopInt.sub herrInt) hlocalInt.intervalIntegrable
      (fun x _ => hlowerPoint x)
  have herrIntervalLe :
      (∫ x in (-p / 2)..(p / 2),
        |F.localProfile T x - topHat p x|) ≤
      ∫ x : ℝ, |F.localProfile T x - topHat p x| := by
    rw [intervalIntegral.integral_of_le (by linarith [h.fill_pos])]
    exact setIntegral_le_integral herror.1
      (Eventually.of_forall fun x => abs_nonneg _)
  have hmass : (99 / 100 : ℝ) ≤ mass := by
    rw [intervalIntegral.integral_sub htopInt herrInt] at hlowerIntegral
    have htopOne :
        (∫ x in (-p / 2)..(p / 2), topHat p x) = 1 := by
      rw [intervalIntegral.integral_of_le (by linarith [h.fill_pos])]
      rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
      have hset :
          (∫ x in Icc (-p / 2) (p / 2), topHat p x) =
            ∫ _x in Icc (-p / 2) (p / 2), (1 / p : ℝ) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro x hx
        simp [topHat, topHatSupport, hx]
      rw [hset, setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith [h.fill_pos])]
      simp only [smul_eq_mul]
      convert mul_inv_cancel₀ h.fill_pos.ne' using 1 <;> ring
    rw [htopOne] at hlowerIntegral
    linarith [herrIntervalLe, herror.2]

  have hwindowInt : Integrable (fun u : ℝ => F.window T j u ^ 2) := by
    exact ((hsmooth j).continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa [pow_two] using
        (HasCompactSupport.mul_left (f := F.window T j) (hcompact j)))
  have hrawLe : ∀ᵐ u : ℝ ∂(volume.restrict
      (Icc (L * (-p / 2)) (L * (p / 2)))),
      F.window T j u ^ 2 ≤ v0 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hreconstruct] with u hu
    intro huInterval
    have hterm : F.window T j u ^ 2 ≤ F.windowEnergy T u := by
      unfold QuarticGramFamily.windowEnergy
      exact Finset.single_le_sum (fun i _ => sq_nonneg (F.window T i u))
        (Finset.mem_univ j)
    rw [hu] at hterm
    have hdenpos : 0 < sigma * Zeta23.l T := mul_pos h.support_pos hell
    have huFull :
        u / QuarticGramFamily.fullLength (σ := sigma) T ∈
          Icc (-(1 : ℝ) / 2) (1 / 2) := by
      rw [Set.mem_Icc] at huInterval ⊢
      dsimp [QuarticGramFamily.fullLength]
      rw [hL] at huInterval
      constructor
      · apply (le_div_iff₀ hdenpos).2
        nlinarith [hcell, h.fill_pos]
      · apply (div_le_iff₀ hdenpos).2
        nlinarith [hcell, h.fill_pos]
    rw [QuarticGramFamily.supportedFullProfile, Set.indicator_of_mem huFull] at hterm
    apply hterm.trans
    apply hprofileCap
    rw [Set.mem_Icc] at huInterval
    rw [hL] at huInterval
    have habsu : |u| ≤ mu * Zeta23.l T * p / 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    dsimp [QuarticGramFamily.fullLength]
    rw [abs_div, abs_of_pos (mul_pos h.support_pos hell)]
    apply (div_le_iff₀ (mul_pos h.support_pos hell)).2
    calc
      |u| ≤ mu * Zeta23.l T * p / 2 := habsu
      _ = mu * p / (2 * sigma) * (sigma * Zeta23.l T) := by
        field_simp [h.support_pos.ne']
  have hphysicalUpper :
      (∫ u in (L * (-p / 2))..(L * (p / 2)), F.window T j u ^ 2) ≤
        L * p * v0 := by
    have hconstInt : IntervalIntegrable (fun _ : ℝ => v0) volume
        (L * (-p / 2)) (L * (p / 2)) := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_ae_restrict
      (show L * (-p / 2) ≤ L * (p / 2) by nlinarith [hLpos, h.fill_pos])
      hwindowInt.intervalIntegrable hconstInt
      hrawLe
    calc
      _ ≤ ∫ _u in (L * (-p / 2))..(L * (p / 2)), v0 := hmono
      _ = L * p * v0 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

  have hmassScale :
      mass * energy =
        ∫ u in (L * (-p / 2))..(L * (p / 2)), F.window T j u ^ 2 := by
    change (∫ x in (-p / 2)..(p / 2),
      L * F.window T j (L * x) ^ 2 / energy) * energy = _
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    rw [div_mul_cancel₀ _ hEpos.ne']
    simpa only [smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := fun u : ℝ => F.window T j u ^ 2) L)
  have hcapacity : mass * energy ≤ L * p * v0 := by
    rw [hmassScale]
    exact hphysicalUpper
  exact no_finite_capacity_configuration sigma mu p A v0 (Zeta23.l T)
    (2 / 5) (1 / 100) total energy L mass hell (by norm_num)
    h.support_pos hApos (by norm_num) htotal hL henergy (by norm_num; exact hmass)
    hcapacity (by norm_num at hnumeric ⊢; exact hnumeric)

/-- No value of the current R1a interface exists for the frozen
support-`14999/10000` family. -/
theorem no_principal14999 {Z : ZeroConfig} (F : Family14999 Z) :
    ¬ PrincipalCyclicBlock F := by
  apply no_principal_of_active_capacity F (by norm_num) (by norm_num) (by norm_num)
    integral_supported_v8686
  · intro s hs
    apply v8686_active_le_center
    norm_num [QuarticWindowWitnesses.edge8686] at hs ⊢
    exact hs
  · exact family14999_capacity_gap

/-- No value of the current R1a interface exists for the frozen
support-`19999/10000` family. -/
theorem no_principal19999 {Z : ZeroConfig} (F : Family19999 Z) :
    ¬ PrincipalCyclicBlock F := by
  apply no_principal_of_active_capacity F (by norm_num) (by norm_num) (by norm_num)
    integral_supported_v9506
  · intro s hs
    apply v9506_active_le_center
    norm_num [QuarticWindowWitnesses.edge9506] at hs ⊢
    exact hs
  · exact family19999_capacity_gap

end R1aAllocationNoGo
end Zeta85
end RH

end
