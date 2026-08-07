/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/LocalCountChi.lean — the two-sided local zero count for L(s,χ)
(piece of H-RvM(χ), see Zeta23/ThmE/RvMChi.lean).
  N_χ(t, t+1] ≤ A₀ log(|t|+3)  for ALL real t  (A₀ depends on q through the growth constants).
Route = Zeta23/RvM/LocalCount.lean with ζ → L(·,χ): halve by Zeta23.ZeroConfig.N_le_two_mul_half
(abstract, applied to LZeros), then the ported PNT+ ZerosBound on g(w) := L(c₀+1.9w,χ)/L(c₀,χ),
c₀ = 2+(t+½)i, r = .84, R = .95, with Zeta23.ThmE.LFunction_growth_right / LFunction_lower_bound_two
(LGrowth.lean); L(·,χ) is entire for χ ≠ 1, so no pole bookkeeping and no |t| ≥ 4 split.
-/
import Zeta23.ThmE.LGrowth
import Zeta23.ThmE.Statement
import Zeta23.RvM.Halving
import Zeta23.RvM.ReZeroCount
import Zeta23.FromPNTPlus.StrongPNTPrefix

open Complex Set DirichletCharacter

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- rescaled L: w ↦ L(c₀ + κ w, χ) · u. -/
def gfunL (χ : DirichletCharacter ℂ q) (c₀ κ u : ℂ) (z : ℂ) : ℂ := χ.LFunction (c₀ + κ * z) * u

lemma gfunL_analyticAt (hχ1 : χ ≠ 1) (c₀ κ u z : ℂ) : AnalyticAt ℂ (gfunL χ c₀ κ u) z := by
  unfold gfunL
  have hL : AnalyticAt ℂ χ.LFunction (c₀ + κ * z) :=
    LFunction_analyticOnNhd hχ1 _ (Set.mem_univ _)
  have haff : AnalyticAt ℂ (fun z : ℂ => c₀ + κ * z) z := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z => χ.LFunction (c₀ + κ * z)) z := hL.comp_of_eq haff rfl
  have hconst : AnalyticAt ℂ (fun _ : ℂ => u) z := analyticAt_const
  exact hcomp.mul hconst

lemma analyticOrderNatAt_gfunL (hχ1 : χ ≠ 1) {c₀ κ u : ℂ} (hκ0 : κ ≠ 0) (hu0 : u ≠ 0) (w : ℂ) :
    analyticOrderNatAt (gfunL χ c₀ κ u) w = zeroMultL χ (c₀ + κ * w) := by
  unfold analyticOrderNatAt zeroMultL gfunL
  congr 1
  have haff : AnalyticAt ℂ (fun z : ℂ => c₀ + κ * z) w := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z => χ.LFunction (c₀ + κ * z)) w := by
    have hL : AnalyticAt ℂ χ.LFunction (c₀ + κ * w) :=
      LFunction_analyticOnNhd hχ1 _ (Set.mem_univ _)
    exact hL.comp_of_eq haff rfl
  have hmul : (fun z ↦ χ.LFunction (c₀ + κ * z) * u) =
      (fun z => χ.LFunction (c₀ + κ * z)) * fun _ => u := rfl
  rw [hmul, analyticOrderAt_mul hcomp analyticAt_const]
  have hconst : analyticOrderAt (fun _ : ℂ => u) w = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr hu0
  rw [hconst, add_zero]
  have hderiv : deriv (fun z : ℂ => c₀ + κ * z) w ≠ 0 := by
    rw [deriv_const_add, deriv_const_mul _ differentiableAt_id, deriv_id'']; simpa using hκ0
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := χ.LFunction) haff hderiv
  simpa [Function.comp_def] using this

set_option maxHeartbeats 1600000 in
/-- **Local count for L(s,χ)**, two-sided. -/
theorem localCountChi (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq hprim
  have hs : LSeam χ := LSeam_of hq hprim
  obtain ⟨A, C, hC, hgrowth⟩ := LFunction_growth_right (χ := χ) hχ1
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  set r : ℝ := 0.84 with hr
  set R : ℝ := 0.95 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  set A₁ : ℝ := 2 * (1 / Real.log (R / r) * (|Real.log (3 * C)| + 2 * A')) with hA₁
  refine ⟨max 1 A₁, le_max_left _ _, fun t => ?_⟩
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  -- halving
  have hhalf : (NcountL χ t (t + 1) : ℝ) ≤
      2 * ∑ᶠ ρ ∈ (LZeros hs).window t (t + 1) ∩ {ρ : ℂ | 1/2 ≤ ρ.re}, ((LZeros hs).mult ρ : ℝ) := by
    have := (LZeros hs).N_le_two_mul_half t (t + 1)
    rwa [LZeros_N] at this
  -- the disc count of the β ≥ 1/2 half
  set c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I with hc₀
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  have hLc₀ : (1/3 : ℝ) ≤ ‖χ.LFunction c₀‖ := LFunction_lower_bound_two (by simp [hc₀])
  have hLc₀ne : χ.LFunction c₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hLc₀; norm_num at hLc₀
  set u : ℂ := (χ.LFunction c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hLc₀ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set G : ℂ → ℂ := gfunL χ c₀ κ u with hG
  have hfAnalytic : AnalyticOnNhd ℂ G (Metric.closedBall (0:ℂ) 1) :=
    fun z _ => gfunL_analyticAt hχ1 c₀ κ u z
  have hG0 : G 0 = 1 := by
    simp only [hG, gfunL, mul_zero, add_zero, hu]
    exact mul_inv_cancel₀ hLc₀ne
  have hfin : (SetOfZeros 1 G).Finite := by
    have h := RvM.finite_zeros_closedBall (f := G) (R := 1.05) (r := 1) (by norm_num)
      (fun z _ => gfunL_analyticAt hχ1 c₀ κ u z) (z₀ := 0) (by simp; norm_num)
      (by rw [hG0]; exact one_ne_zero)
    exact h.subset (by intro z hz; exact hz)
  set B : ℝ := 3 * C * (|t| + 6) ^ A' with hB
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖G z‖ ≤ B := by
    intro z hz
    set s : ℂ := c₀ + κ * z with hs'
    have hκre : κ.re = 1.9 := by rw [hκ]; norm_num [Complex.ofReal_re]
    have hκim : κ.im = 0 := by rw [hκ]; simp
    have hzre := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
    have hzim := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
    rw [hR] at hzre hzim
    have hsre : s.re = 2 + 1.9 * z.re := by
      rw [hs', hc₀]
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.mul_im, hκre, hκim]
      ring
    have hsim : s.im = (t + 1/2) + 1.9 * z.im := by
      rw [hs', hc₀]
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.im_ofNat, Complex.mul_re, hκre, hκim]
      ring
    have h1 : (0.15:ℝ) ≤ s.re := by rw [hsre]; nlinarith
    have h3 := hgrowth s h1
    have hbase1 : (1:ℝ) ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
    have hA'A : (|s.im| + 3) ^ A ≤ (|s.im| + 3) ^ A' :=
      Real.rpow_le_rpow_of_exponent_le hbase1 (le_max_left _ _)
    have hbase : |s.im| + 3 ≤ |t| + 6 := by
      rw [hsim]
      have h4 := abs_add_le (t + 1/2) (1.9 * z.im)
      have h5 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]
        have : |z.im| ≤ 0.95 := abs_le.mpr ⟨hzim.1, hzim.2⟩
        nlinarith
      have h6 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
      linarith
    have hmono : (|s.im| + 3) ^ A' ≤ (|t| + 6) ^ A' :=
      Real.rpow_le_rpow (by positivity) hbase hA'0
    calc ‖G z‖ = ‖χ.LFunction s‖ * ‖u‖ := by rw [hG]; exact norm_mul _ _
      _ ≤ (C * (|t| + 6) ^ A') * 3 := by
          apply mul_le_mul (h3.trans (mul_le_mul_of_nonneg_left (hA'A.trans hmono) hC.le)) hnu
            (norm_nonneg _) (by positivity)
      _ = B := by rw [hB]; ring
  have hrlt1 : r < 1 := by norm_num [hr]
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) hrlt1
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hG0 hfin hfz
  set Z : Finset ℂ := (finiteSetOfZeros_mono hrlt1 hfin).toFinset with hZdef
  -- the half-window injects into Z
  set W : Set ℂ := (LZeros hs).window t (t + 1) ∩ {ρ : ℂ | 1/2 ≤ ρ.re} with hW
  have hWfin : W.Finite := ((LZeros hs).window_finite t (t + 1)).subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have hφinj : Function.Injective φ := by
    intro a b h; simp only [hφ] at h
    have := congrArg (fun w => c₀ + κ * w) h
    simpa [mul_div_cancel₀ _ hκ0] using this
  have hφinv : ∀ ρ, c₀ + κ * φ ρ = ρ := by intro ρ; simp only [hφ]; field_simp; ring
  have hmemS : ∀ ρ ∈ W, φ ρ ∈ Z := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    have hρ : IsNontrivialZeroL χ ρ := by rwa [LZeros_carrier] at hρZ
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · show ‖φ ρ‖ ≤ r
      simp only [hφ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [hc₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [hc₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (0.84 * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have := hρ.2.2; have := hρre.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show G (φ ρ) = 0
      simp only [hG, gfunL, hφinv]
      rw [hρ.1, zero_mul]
  have hmult : ∀ ρ ∈ W, ((LZeros hs).mult ρ : ℝ) = (analyticOrderNatAt G (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨hρZ, -, -⟩, -⟩
    rw [LZeros_mult, hG, analyticOrderNatAt_gfunL hχ1 hκ0 hu0, hφinv]
  have hsum : (∑ᶠ ρ ∈ W, ((LZeros hs).mult ρ : ℝ)) ≤
      ((∑ ρ' ∈ Z, analyticOrderNatAt G ρ' : ℕ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt G w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros; positivity
  have hlog6 : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    apply Real.log_le_log (by positivity); nlinarith [abs_nonneg t]
  have hlogB : Real.log B ≤ (|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3) := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
    have h1 := le_abs_self (Real.log (3 * C))
    have h2 : |Real.log (3 * C)| ≤ |Real.log (3 * C)| * Real.log (|t| + 3) :=
      le_mul_of_one_le_right (abs_nonneg _) hlog3
    have h3 : A' * Real.log (|t| + 6) ≤ A' * (2 * Real.log (|t| + 3)) :=
      mul_le_mul_of_nonneg_left hlog6 hA'0
    linarith
  calc (NcountL χ t (t + 1) : ℝ)
      ≤ 2 * ∑ᶠ ρ ∈ W, ((LZeros hs).mult ρ : ℝ) := hhalf
    _ ≤ 2 * ((∑ ρ' ∈ Z, analyticOrderNatAt G ρ' : ℕ) : ℝ) := by linarith [hsum]
    _ ≤ 2 * (1 / Real.log (R / r) * Real.log B) := by
        have h : ((∑ ρ' ∈ Z, analyticOrderNatAt G ρ' : ℕ) : ℝ) ≤
            1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
        linarith
    _ ≤ max 1 A₁ * Real.log (|t| + 3) := by
        have hstep : 1 / Real.log (R / r) * Real.log B ≤
            1 / Real.log (R / r) * ((|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by positivity)
        calc 2 * (1 / Real.log (R / r) * Real.log B)
            ≤ 2 * (1 / Real.log (R / r) * ((|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3))) := by
              linarith
          _ = A₁ * Real.log (|t| + 3) := by rw [hA₁]; ring
          _ ≤ max 1 A₁ * Real.log (|t| + 3) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

end ThmE
end Zeta23
