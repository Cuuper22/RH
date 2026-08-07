/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/Limit.lean — Theorem D endgame: the exact-constant limit.
 (L1) cRatio at the starred data IS c*_λ;
 (L2) the concrete window data converges: cRatio(λ₁(T), a_D(T), b_D(T), J_D(T)) → c*_λ as T → ∞;
 (L3) the λ → 1⁻ ε-step for the three Theorem-D rates (HD, 2c*−1, c*), by the Lipschitz bound.
-/
import Zeta23.ThmD.Concrete
import Zeta23.Assembly

open Filter Real Topology

noncomputable section

namespace Zeta23
namespace ThmD

/-! ### (L1) the starred ratio -/

theorem cRatio_star {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    cRatio lam (aStar lam) (bStar lam) (jStar lam) = cStar lam := by
  rw [← cFun_vStar h0 h1]
  rfl

/-! ### range facts -/

/-- c* ≥ 1/(2π) on [1/2, 1] (Jordan's inequality for the numerator; denominator ≤ 2). -/
theorem cStar_ge_lb {lam : ℝ} (h0 : 1/2 ≤ lam) (h1 : lam ≤ 1) :
    1 / (2 * Real.pi) ≤ cStar lam := by
  have h0' : (0:ℝ) < lam := by linarith
  have hθ0 : 0 < theta lam := theta_pos h0'
  have hθle : theta lam ≤ (Real.sqrt 2)⁻¹ := theta_le h1 h0'.le
  have hs2 : (1:ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hs2' : (0:ℝ) < Real.sqrt 2 := by linarith
  have hθ1 : theta lam ≤ 1 := hθle.trans (by rw [inv_le_one_iff₀]; right; exact hs2)
  have hθπ : theta lam ≤ Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  have hπ0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hsin := Real.mul_le_sin hθ0.le hθπ
  have hnum : 1 / Real.pi ≤ Real.sqrt 2 * Real.sin (theta lam) := by
    have h2 : Real.sqrt 2 * (2 / Real.pi * theta lam) = 2 * lam / Real.pi := by
      unfold theta
      field_simp
      try ring
    have h3 : Real.sqrt 2 * (2 / Real.pi * theta lam) ≤ Real.sqrt 2 * Real.sin (theta lam) :=
      mul_le_mul_of_nonneg_left hsin hs2'.le
    rw [h2] at h3
    have h4 : 1 / Real.pi ≤ 2 * lam / Real.pi := by gcongr; linarith
    linarith
  have hsin1 : Real.sin (theta lam) ≤ 1 := Real.sin_le_one _
  have hcos1 : Real.cos (theta lam) ≤ 1 := Real.cos_le_one _
  have hden2 : Real.cos (theta lam) + theta lam * Real.sin (theta lam) ≤ 2 := by
    nlinarith [Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by nlinarith [Real.pi_gt_three])]
  have hden34 := cStar_denom_ge h0'.le h1
  unfold cStar
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  have h5 : 2 ≤ Real.sqrt 2 * Real.sin (theta lam) * (2 * Real.pi) := by
    have h6 := mul_le_mul_of_nonneg_right hnum (by positivity : (0:ℝ) ≤ 2*Real.pi)
    have h7 : 1/Real.pi * (2*Real.pi) = 2 := by field_simp
    linarith
  linarith

/-- vStar is nonnegative on the unit window. -/
theorem vStar_nonneg_on {lam s : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hs : s ∈ Set.Icc (-(1:ℝ)/2) (1/2)) : 0 ≤ vStar lam s := by
  unfold vStar
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · have h2 : Real.sqrt 2 * lam * s ≥ -(Real.sqrt 2 * lam * (1/2)) := by
      have := hs.1
      nlinarith [Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) h0]
    have hs2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith [Real.pi_gt_three, mul_nonneg (Real.sqrt_nonneg 2) h0]
  · have hs2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have := hs.2
    nlinarith [Real.pi_gt_three, mul_nonneg (Real.sqrt_nonneg 2) h0,
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) h0) (by linarith [hs.1] : (0:ℝ) ≤ s + 1/2)]
  
/-- J* ≥ 0 (integral of a pointwise-nonnegative kernel). -/
theorem jStar_nonneg {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : 0 ≤ jStar lam := by
  unfold jStar
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro s hs
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro s' hs'
  have h1' := vStar_nonneg_on h0 h1 hs
  have h2' := vStar_nonneg_on h0 h1 hs'
  positivity

/-- the denominator of the starred ratio is strictly positive. -/
theorem star_denom_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    0 < bStar lam + lam ^ 2 * jStar lam := by
  have hb := bStar_ge h0 h1
  have hj := jStar_nonneg h0.le h1
  have hπ := Real.pi_pos
  have h2 : (0:ℝ) < 1/2 + 1/Real.pi := by positivity
  nlinarith

/-! ### (L3) the λ → 1⁻ ε-step -/

/-- generic form: if the target constant is approached from the left in the rate scale, the
ε-statement at every λ < 1 upgrades to the ε-statement at λ = 1. -/
theorem eps_form_of_approx {g : ℝ → ℝ} {N lower : ℝ → ℝ}
    (hg : ∀ δ : ℝ, 0 < δ → ∃ lam : ℝ, 1/2 ≤ lam ∧ lam < 1 ∧ g 1 - δ ≤ g lam)
    (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1/2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (g lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (g 1 - ε) * N T ≤ lower T := by
  intro ε hε
  obtain ⟨lam, hl1, hl2, hg'⟩ := hg (ε/2) (by linarith)
  obtain ⟨T₀, hT₀⟩ := h lam hl1 hl2 (ε/2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hmul : (g 1 - ε) * N T ≤ (g lam - ε/2) * N T := by
    apply mul_le_mul_of_nonneg_right _ (hN T)
    linarith
  linarith

/-- the c*-rate ε-step. -/
theorem eps_form_cStar {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1/2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (cStar lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (cStar 1 - ε) * N T ≤ lower T := by
  apply eps_form_of_approx _ hN h
  intro δ hδ
  refine ⟨max (1/2) (1 - δ/14), le_max_left _ _, ?_, ?_⟩
  · apply max_lt (by norm_num) (by linarith)
  · set lam := max (1/2) (1 - δ/14) with hlam
    have hl0 : (0:ℝ) ≤ lam := le_trans (by norm_num) (le_max_left _ _)
    have hl1 : lam ≤ 1 := by
      apply max_le (by norm_num) (by linarith)
    have hsub : 1 - lam ≤ δ/14 := by
      have := le_max_right (1/2 : ℝ) (1 - δ/14)
      linarith [this.trans_eq hlam.symm]
    have hlip := cStar_lipschitzOn hl0 hl1 (by norm_num : (0:ℝ) ≤ 1) le_rfl
    have habs := abs_le.mp hlip
    have h14 : 14 * |lam - 1| ≤ δ := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    linarith [habs.1, neg_abs_le (cStar lam - cStar 1)]

/-- the (2c* − 1)-rate ε-step. -/
theorem eps_form_twoCStar {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1/2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ((2 * cStar lam - 1) - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ((2 * cStar 1 - 1) - ε) * N T ≤ lower T := by
  have := eps_form_of_approx (g := fun lam => 2 * cStar lam - 1) (N := N) (lower := lower)
  apply this _ hN h
  intro δ hδ
  refine ⟨max (1/2) (1 - δ/28), le_max_left _ _, ?_, ?_⟩
  · apply max_lt (by norm_num) (by linarith)
  · set lam := max (1/2) (1 - δ/28) with hlam
    have hl0 : (0:ℝ) ≤ lam := le_trans (by norm_num) (le_max_left _ _)
    have hl1 : lam ≤ 1 := max_le (by norm_num) (by linarith)
    have hsub : 1 - lam ≤ δ/28 := by
      have := le_max_right (1/2 : ℝ) (1 - δ/28)
      linarith [this.trans_eq hlam.symm]
    have hlip := cStar_lipschitzOn hl0 hl1 (by norm_num : (0:ℝ) ≤ 1) le_rfl
    have habs := abs_le.mp hlip
    have h14 : 14 * |lam - 1| ≤ δ/2 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    have := habs.1
    linarith [neg_abs_le (cStar lam - cStar 1)]

/-- the HD-rate ε-step (HD = 2 − 1/c*; uses the uniform lower bound c* ≥ 1/(2π) on [1/2,1]). -/
theorem eps_form_HD {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1/2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (HD lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (HD 1 - ε) * N T ≤ lower T := by
  apply eps_form_of_approx (g := HD) _ hN h
  intro δ hδ
  -- |1/c*λ − 1/c*1| ≤ (2π)²·14·(1−λ); choose 1 − λ ≤ δ/(56·π²) ≥ δ/(14·(2π)²)
  refine ⟨max (1/2) (1 - δ/(56 * Real.pi^2)), le_max_left _ _, ?_, ?_⟩
  · have hπ := Real.pi_pos
    apply max_lt (by norm_num)
    have : 0 < δ/(56 * Real.pi^2) := by positivity
    linarith
  · set lam := max (1/2) (1 - δ/(56 * Real.pi^2)) with hlam
    have hπ := Real.pi_pos
    have hl05 : (1:ℝ)/2 ≤ lam := le_max_left _ _
    have hl0 : (0:ℝ) ≤ lam := by linarith
    have hl1 : lam ≤ 1 := by
      apply max_le (by norm_num)
      have : 0 < δ/(56 * Real.pi^2) := by positivity
      linarith
    have hsub : 1 - lam ≤ δ/(56 * Real.pi^2) := by
      have := le_max_right (1/2 : ℝ) (1 - δ/(56 * Real.pi^2))
      linarith [this.trans_eq hlam.symm]
    have hclb := cStar_ge_lb hl05 hl1
    have hclb1 := cStar_ge_lb (by norm_num : (1:ℝ)/2 ≤ 1) le_rfl
    have hc0 : (0:ℝ) < cStar lam := lt_of_lt_of_le (by positivity) hclb
    have hc1 : (0:ℝ) < cStar 1 := lt_of_lt_of_le (by positivity) hclb1
    have hlip := cStar_lipschitzOn hl0 hl1 (by norm_num : (0:ℝ) ≤ 1) le_rfl
    have hdiff : |cStar lam - cStar 1| ≤ 14 * (1 - lam) := by
      refine hlip.trans ?_
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    -- 1/c*λ − 1/c*1 = (c*1 − c*λ)/(c*λ c*1) ≤ 14(1−λ)·(2π)²
    unfold HD
    have hprod : 1/(2*Real.pi) * (1/(2*Real.pi)) ≤ cStar lam * cStar 1 := by
      apply mul_le_mul hclb hclb1 (by positivity) (by linarith)
    have hkey : 1 / cStar lam - 1 / cStar 1 ≤ δ := by
      have he : 1 / cStar lam - 1 / cStar 1 = (cStar 1 - cStar lam) / (cStar lam * cStar 1) := by
        field_simp
      rw [he]
      have hnum : cStar 1 - cStar lam ≤ 14 * (1 - lam) :=
        le_trans (le_abs_self _) (by rwa [abs_sub_comm] at hdiff)
      have hpos : (0:ℝ) < cStar lam * cStar 1 := by positivity
      rw [div_le_iff₀ hpos]
      have h2π : 1/(2*Real.pi) * (1/(2*Real.pi)) = 1/(4 * Real.pi^2) := by
        field_simp; ring
      rw [h2π] at hprod
      have h56 : 14 * (1 - lam) ≤ δ/(4 * Real.pi^2) := by
        calc 14 * (1 - lam) ≤ 14 * (δ/(56 * Real.pi^2)) := by
              apply mul_le_mul_of_nonneg_left hsub (by norm_num)
          _ = δ/(4 * Real.pi^2) := by field_simp; ring
      have hδprod : δ/(4 * Real.pi^2) ≤ δ * (cStar lam * cStar 1) := by
        calc δ/(4 * Real.pi^2) = δ * (1/(4 * Real.pi^2)) := by ring
          _ ≤ δ * (cStar lam * cStar 1) := by
              apply mul_le_mul_of_nonneg_left hprod (by linarith)
      linarith
    linarith

/-! ### (L2) convergence of the concrete data -/

/-- λ₁(T) → λ. -/
theorem tendsto_lam1 {P : Params} (hlam : 0 < P.lam) :
    Tendsto (fun T => P.lam1 T) atTop (𝓝 P.lam) := by
  have hl := Assembly.tendsto_l_atTop
  have hbound : ∀ᶠ T in atTop, P.lam - P.lam / l T ≤ P.lam1 T ∧ P.lam1 T ≤ P.lam := by
    filter_upwards [Assembly.eventually_l_pos] with T hlT
    exact ⟨by linarith [Assembly.sub_lam1_le P T hlam.le hlT],
      Assembly.lam1_le P T hlam.le hlT⟩
  have hlow : Tendsto (fun T => P.lam - P.lam / l T) atTop (𝓝 P.lam) := by
    have h0 : Tendsto (fun T => P.lam / l T) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hl
    have := tendsto_const_nhds (x := P.lam) (f := atTop (α := ℝ)) |>.sub h0
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    (hbound.mono fun T h => h.1) (hbound.mono fun T h => h.2)

/-- generic: data within C·w/L of a constant converges to it. -/
theorem tendsto_of_close {P : Params} (hlam : 0 < P.lam) {f : ℝ → ℝ} {c C : ℝ}
    (hclose : ∀ᶠ T in atTop, |f T - c| ≤ C * P.w / P.L T) :
    Tendsto f atTop (𝓝 c) := by
  have hL := Assembly.tendsto_L_atTop P hlam
  have hz : Tendsto (fun T => C * P.w / P.L T) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hL
  have hdiff : Tendsto (fun T => f T - c) atTop (𝓝 0) :=
    squeeze_zero_norm' (hclose.mono fun T h => by simpa [Real.norm_eq_abs] using h) hz
  have := hdiff.add_const c
  simpa using this

/-- the three concrete D-window moment limits, exported standalone. -/
theorem tendsto_aD {P : Params} (hP : P.Valid) :
    Tendsto (fun T => (P.localFunD T).a) atTop (𝓝 (aStar P.lam)) := by
  apply tendsto_of_close hP.lam_pos (C := 4)
  filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)]
    with T hT
  exact aD_close hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w hT

theorem tendsto_bD {P : Params} (hP : P.Valid) :
    Tendsto (fun T => (P.localFunD T).b) atTop (𝓝 (bStar P.lam)) := by
  apply tendsto_of_close hP.lam_pos (C := 4)
  filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)]
    with T hT
  exact bD_close hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w hT

theorem tendsto_JD {P : Params} (hP : P.Valid) :
    Tendsto (fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (P.localFunD T).g y * y) atTop
      (𝓝 (jStar P.lam)) := by
  apply tendsto_of_close hP.lam_pos (C := 16)
  filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)]
    with T hT
  exact jD_close hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w hT

/-- generic ratio limit: any λ₁-like sequence tending to λ and any data tending to the starred
moments give cRatio → c*_λ. -/
theorem tendsto_cRatio_of {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    {lam1f aT bT JT : ℝ → ℝ}
    (hl1 : Tendsto lam1f atTop (𝓝 lam))
    (ha : Tendsto aT atTop (𝓝 (aStar lam))) (hb : Tendsto bT atTop (𝓝 (bStar lam)))
    (hJ : Tendsto JT atTop (𝓝 (jStar lam))) :
    Tendsto (fun T => cRatio (lam1f T) (aT T) (bT T) (JT T)) atTop (𝓝 (cStar lam)) := by
  have hden := star_denom_pos h0 h1
  have hnum : Tendsto (fun T => lam1f T * (aT T) ^ 2) atTop (𝓝 (lam * (aStar lam) ^ 2)) :=
    hl1.mul (ha.pow 2)
  have hdenT : Tendsto (fun T => bT T + (lam1f T) ^ 2 * JT T) atTop
      (𝓝 (bStar lam + lam ^ 2 * jStar lam)) :=
    hb.add ((hl1.pow 2).mul hJ)
  have hlim := hnum.div hdenT (ne_of_gt hden)
  have hfinal : lam * (aStar lam) ^ 2 / (bStar lam + lam ^ 2 * jStar lam)
      = cStar lam := cRatio_star h0 h1
  rw [← hfinal]
  exact hlim

/-- **(L2)**: the concrete Montgomery–Taylor window ratio converges to c*_λ. -/
theorem tendsto_cRatio_concrete {P : Params} (hP : P.Valid) (Z : ZeroConfig) :
    Tendsto (fun T => cRatio (P.lam1 T) ((concreteDataD P Z).aT T) ((concreteDataD P Z).bT T)
      ((concreteDataD P Z).JT T)) atTop (𝓝 (cStar P.lam)) :=
  tendsto_cRatio_of hP.lam_pos hP.lam_le_one (tendsto_lam1 hP.lam_pos)
    (tendsto_aD hP) (tendsto_bD hP) (tendsto_JD hP)

end ThmD
end Zeta23
