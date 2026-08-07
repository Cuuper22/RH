/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/ReZeroCountChi.lean — the Jensen half (J) of Backlund's bound for L(s,χ): the number of
zeros of Re L(σ+iT,χ) on σ ∈ [1/2,2] is ≪_χ log|T|.
The argument follows Zeta23/RvM/ReZeroCount.lean, with the
symmetrised function g(z) := (L(z+iT,χ) + L(z−iT,χ⁻¹))/2 (entire; = Re L(σ+iT,χ) on ℝ by
LFunction_conj), growth for χ and χ⁻¹ from LFunction_growth_right, and no pole
bookkeeping — hence two-sided in the height T.
-/
import Zeta23.ThmE.BacklundChi
import Zeta23.RvM.ReZeroCount

open Complex Set Metric Zeta23.RvM

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- the symmetrised function g_T(z) := (L(z+iT,χ) + L(z−iT,χ⁻¹))/2; equals Re L(σ+iT,χ)
for real σ. -/
def symL (χ : DirichletCharacter ℂ q) (T : ℝ) (z : ℂ) : ℂ :=
  (χ.LFunction (z + T * I) + χ⁻¹.LFunction (z - T * I)) / 2

lemma symL_analyticAt (hχ1 : χ ≠ 1) (T : ℝ) (z : ℂ) : AnalyticAt ℂ (symL χ T) z := by
  have hinv : χ⁻¹ ≠ 1 := fun h => hχ1 (inv_eq_one.mp h)
  unfold symL
  have ha : AnalyticAt ℂ (fun z : ℂ => χ.LFunction (z + T * I)) z :=
    (LFunction_analyticOnNhd hχ1 _ (mem_univ _)).comp_of_eq (by fun_prop) rfl
  have hb : AnalyticAt ℂ (fun z : ℂ => χ⁻¹.LFunction (z - T * I)) z :=
    (LFunction_analyticOnNhd hinv _ (mem_univ _)).comp_of_eq (by fun_prop) rfl
  exact (ha.add hb).div_const

/-- for real σ, g_T(σ) is the real number Re L(σ + iT, χ). -/
lemma symL_ofReal (hχ1 : χ ≠ 1) {T : ℝ} (σ : ℝ) :
    symL χ T σ = (((χ.LFunction ((σ:ℂ) + T * I)).re : ℝ) : ℂ) := by
  unfold symL
  have hconj : χ⁻¹.LFunction ((σ:ℂ) - T * I) = (starRingEnd ℂ) (χ.LFunction ((σ:ℂ) + T * I)) := by
    have h := LFunction_conj hχ1 ((σ:ℂ) - T * I)
    have e : (starRingEnd ℂ) ((σ:ℂ) - T * I) = (σ:ℂ) + T * I := by
      simp [Complex.ext_iff]
    rw [e] at h
    rw [h, Complex.conj_conj]
  rw [hconj, Complex.add_conj]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
/-- **(J) the Jensen half of Backlund's bound for L(s,χ)**: #{σ ∈ [1/2,2] : Re L(σ+iT,χ) = 0} ≪_χ log |T|. -/
theorem reZeroSetL_card_le (hχ1 : χ ≠ 1) : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ |T| →
    (reZeroSetL χ T).Finite ∧ ((reZeroSetL χ T).ncard : ℝ) ≤ C * Real.log |T| := by
  have hinv : χ⁻¹ ≠ 1 := fun h => hχ1 (inv_eq_one.mp h)
  obtain ⟨A₁, C₁, hC₁, hgrowth₁⟩ := LFunction_growth_right hχ1
  obtain ⟨A₂, C₂, hC₂, hgrowth₂⟩ := LFunction_growth_right (χ := χ⁻¹) hinv
  set A' : ℝ := max (max A₁ A₂) 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  set C : ℝ := max C₁ C₂ with hCdef
  have hC : 0 < C := lt_max_of_lt_left hC₁
  set r : ℝ := 0.8 with hr
  set R : ℝ := 0.9 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  refine ⟨1 / Real.log (R / r) * (|Real.log (6 * C)| + 2 * A'), 4, fun T hT => ?_⟩
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  -- the centre value g_T(2) = Re L(2+iT,χ) ≥ 2 − π²/6 > 1/3
  have hsub1 := norm_LFunction_sub_one_le (χ := χ) (s := 2 + T * I) (by simp)
  have hre2 : 2 - Real.pi ^ 2 / 6 ≤ (χ.LFunction (2 + T * I)).re := by
    have h2 : |(χ.LFunction (2 + T * I) - 1).re| ≤ Real.pi ^ 2 / 6 - 1 :=
      (Complex.abs_re_le_norm _).trans hsub1
    have h3 : (χ.LFunction (2 + T * I) - 1).re = (χ.LFunction (2 + T * I)).re - 1 := by simp
    rw [h3] at h2
    linarith [(abs_le.mp h2).1]
  have hthird := one_third_lt_two_sub_pi_sq_div_six
  have hg2 : symL χ T 2 = (((χ.LFunction ((2:ℂ) + T * I)).re : ℝ) : ℂ) := by
    have h := symL_ofReal hχ1 (T := T) 2
    push_cast at h ⊢
    exact h
  have hg2ne : symL χ T 2 ≠ 0 := by
    rw [hg2]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  set u : ℂ := (symL χ T 2)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hg2ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv, inv_le_comm₀ (by positivity) (by norm_num)]
    rw [hg2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  set G : ℂ → ℂ := fun w => symL χ T (2 + κ * w) * u with hG
  have hGanalytic : ∀ w : ℂ, ‖w‖ ≤ 1.05 → AnalyticAt ℂ G w := by
    intro w _
    exact ((symL_analyticAt hχ1 T _).comp_of_eq
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 2 + κ * w) w) rfl).mul analyticAt_const
  have hG0 : G 0 = 1 := by
    simp only [hG, mul_zero, add_zero, hu]
    exact mul_inv_cancel₀ hg2ne
  -- finiteness of the unit-ball zeros
  have hball : AnalyticOnNhd ℂ G (Metric.ball 0 1.05) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hGanalytic w hw.le
  have hfin : (SetOfZeros 1 G).Finite := by
    have h := finite_zeros_closedBall (f := G) (R := 1.05) (r := 1) (by norm_num) hball
      (z₀ := 0) (by simp; norm_num) (by rw [hG0]; exact one_ne_zero)
    exact h.subset (by intro z hz; exact hz)
  -- growth bound on ‖w‖ ≤ R
  set B : ℝ := 6 * C * (|T| + 5) ^ A' with hB
  have hBpos : 0 < B := by positivity
  have hκre : κ.re = 1.9 := by rw [hκ]; norm_num [Complex.ofReal_re]
  have hκim : κ.im = 0 := by rw [hκ]; simp
  have hfz : ∀ w : ℂ, ‖w‖ ≤ R → ‖G w‖ ≤ B := by
    intro w hw
    have hwre := abs_le.mp ((Complex.abs_re_le_norm w).trans hw)
    have hwim := abs_le.mp ((Complex.abs_im_le_norm w).trans hw)
    rw [hR] at hwre hwim
    have hκwre : (κ * w).re = 1.9 * w.re := by
      rw [Complex.mul_re, hκre, hκim]; ring
    have hκwim : (κ * w).im = 1.9 * w.im := by
      rw [Complex.mul_im, hκre, hκim]; ring
    have hgen : ∀ (Lf : ℂ → ℂ) (Aψ Cψ : ℝ), Cψ ≤ C → Aψ ≤ A' →
        (∀ s : ℂ, (0.15:ℝ) ≤ s.re → ‖Lf s‖ ≤ Cψ * (|s.im| + 3) ^ Aψ) →
        ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ‖Lf (2 + κ * w + ε * T * I)‖ ≤ C * (|T| + 5) ^ A' := by
      intro Lf Aψ Cψ hCψ hAψ hg ε hε
      set s : ℂ := 2 + κ * w + ε * T * I with hs
      have hsre : s.re = 2 + 1.9 * w.re := by
        rw [hs]
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.mul_im, hκre, hκim]
        ring
      have hsim : s.im = 1.9 * w.im + ε * T := by
        rw [hs]
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.im_ofNat, Complex.mul_re, hκre, hκim]
        ring
      have h1 : (0.15:ℝ) ≤ s.re := by rw [hsre]; nlinarith
      have h3 := hg s h1
      have hbase1 : (1:ℝ) ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
      have hA'A : (|s.im| + 3) ^ Aψ ≤ (|s.im| + 3) ^ A' :=
        Real.rpow_le_rpow_of_exponent_le hbase1 hAψ
      have hbase : |s.im| + 3 ≤ |T| + 5 := by
        rw [hsim]
        have h4 := abs_add_le (1.9 * w.im) (ε * T)
        have h5 : |1.9 * w.im| ≤ 1.71 := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]
          have : |w.im| ≤ 0.9 := abs_le.mpr ⟨hwim.1, hwim.2⟩
          nlinarith
        have h6 : |ε * T| = |T| := by
          rcases hε with rfl | rfl <;> simp [abs_mul]
        linarith
      have hmono : (|s.im| + 3) ^ A' ≤ (|T| + 5) ^ A' :=
        Real.rpow_le_rpow (by positivity) hbase hA'0
      have hpow0 : 0 ≤ (|s.im| + 3) ^ Aψ := Real.rpow_nonneg (by positivity) _
      calc ‖Lf s‖ ≤ Cψ * (|s.im| + 3) ^ Aψ := h3
        _ ≤ C * (|s.im| + 3) ^ Aψ := mul_le_mul_of_nonneg_right hCψ hpow0
        _ ≤ C * (|T| + 5) ^ A' := mul_le_mul_of_nonneg_left (hA'A.trans hmono) hC.le
    have hgb : ‖symL χ T (2 + κ * w)‖ ≤ C * (|T| + 5) ^ A' := by
      have e1 : (2:ℂ) + κ * w + (1:ℝ) * T * I = 2 + κ * w + T * I := by push_cast; ring
      have e2 : (2:ℂ) + κ * w + (-1:ℝ) * T * I = 2 + κ * w - T * I := by push_cast; ring
      have ha := hgen χ.LFunction A₁ C₁ (le_max_left _ _) ((le_max_left _ _).trans (le_max_left _ _))
        hgrowth₁ 1 (Or.inl rfl)
      have hb := hgen χ⁻¹.LFunction A₂ C₂ (le_max_right _ _) ((le_max_right _ _).trans (le_max_left _ _))
        hgrowth₂ (-1) (Or.inr rfl)
      rw [e1] at ha
      rw [e2] at hb
      unfold symL
      calc ‖(χ.LFunction (2 + κ * w + T * I) + χ⁻¹.LFunction (2 + κ * w - T * I)) / 2‖
          = ‖χ.LFunction (2 + κ * w + T * I) + χ⁻¹.LFunction (2 + κ * w - T * I)‖ / 2 := by
            rw [norm_div]; norm_num
        _ ≤ (‖χ.LFunction (2 + κ * w + T * I)‖ + ‖χ⁻¹.LFunction (2 + κ * w - T * I)‖) / 2 := by
            gcongr
            exact norm_add_le _ _
        _ ≤ C * (|T| + 5) ^ A' := by linarith
    calc ‖G w‖ = ‖symL χ T (2 + κ * w)‖ * ‖u‖ := by rw [hG]; exact norm_mul _ _
      _ ≤ (C * (|T| + 5) ^ A') * 3 := by
          apply mul_le_mul hgb hnu (norm_nonneg _) (by positivity)
      _ ≤ B := by
          rw [hB]
          nlinarith [Real.rpow_nonneg (by positivity : (0:ℝ) ≤ |T| + 5) A']
  -- apply ZerosBound
  have hfAnalytic : AnalyticOnNhd ℂ G (Metric.closedBall (0:ℂ) 1) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    exact hGanalytic w (hw.trans (by norm_num))
  have hrlt1 : r < 1 := by norm_num [hr]
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) hrlt1
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hG0 hfin hfz
  set Z : Finset ℂ := (finiteSetOfZeros_mono hrlt1 hfin).toFinset with hZdef
  have horder : ∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt G ρ := by
    intro ρ hρ
    rw [hZdef, Set.Finite.mem_toFinset] at hρ
    obtain ⟨hρr, hρ0⟩ := hρ
    have hρr' : ‖ρ‖ ≤ r := hρr
    have han : AnalyticAt ℂ G ρ := hGanalytic ρ (by rw [hr] at hρr'; linarith)
    have hne0 : analyticOrderAt G ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr hρ0
    have hnetop : analyticOrderAt G ρ ≠ ⊤ := by
      refine hball.analyticOrderAt_ne_top_of_isPreconnected (convex_ball _ _).isPreconnected
        (x := 0) ?_ ?_ ?_
      · rw [Metric.mem_ball, dist_zero_right]; simp; norm_num
      · rw [Metric.mem_ball, dist_zero_right]; rw [hr] at hρr'; linarith
      · rw [(hGanalytic 0 (by norm_num)).analyticOrderAt_eq_zero.mpr
          (by rw [hG0]; exact one_ne_zero)]
        exact ENat.zero_ne_top
    unfold analyticOrderNatAt
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
    rw [← hn] at hne0 ⊢
    simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
    omega
  -- the real zeros inject into Z
  set φ : ℝ → ℂ := fun σ => ((σ - 2 : ℝ) : ℂ) / κ with hφ
  have hφinj : Set.InjOn φ (reZeroSetL χ T) := by
    intro a _ b _ h
    simp only [hφ] at h
    have h' : ((a - 2 : ℝ) : ℂ) = ((b - 2 : ℝ) : ℂ) := by
      have := congrArg (fun z => z * κ) h
      simpa [div_mul_cancel₀ _ hκ0] using this
    have := Complex.ofReal_inj.mp h'
    linarith
  have hmem : ∀ σ ∈ reZeroSetL χ T, φ σ ∈ SetOfZeros r G := by
    rintro σ ⟨hσI, hσ0⟩
    have hσ1 : (1/2:ℝ) ≤ σ := hσI.1
    have hσ2 : σ ≤ 2 := hσI.2
    constructor
    · show ‖((σ - 2 : ℝ) : ℂ) / κ‖ ≤ r
      rw [norm_div, hnormκ, Complex.norm_real, Real.norm_eq_abs, hr]
      rw [abs_of_nonpos (by linarith)]
      rw [div_le_iff₀ (by norm_num)]
      linarith
    · show G (φ σ) = 0
      have hfix : (2:ℂ) + κ * φ σ = (σ:ℂ) := by
        simp only [hφ]
        field_simp
        push_cast
        ring
      simp only [hG, hfix]
      rw [symL_ofReal hχ1 σ, hσ0]
      simp
  have himg : φ '' (reZeroSetL χ T) ⊆ (↑Z : Set ℂ) := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [hZdef]
    simp only [Set.Finite.coe_toFinset]
    exact hmem σ hσ
  have hfinRe : (reZeroSetL χ T).Finite :=
    Set.Finite.of_finite_image (Z.finite_toSet.subset himg) hφinj
  refine ⟨hfinRe, ?_⟩
  have hcard : ((reZeroSetL χ T).ncard : ℝ) ≤ (Z.card : ℝ) := by
    have h1 : (reZeroSetL χ T).ncard = (φ '' reZeroSetL χ T).ncard :=
      (hφinj.ncard_image).symm
    have h2 : (φ '' reZeroSetL χ T).ncard ≤ (↑Z : Set ℂ).ncard :=
      Set.ncard_le_ncard himg Z.finite_toSet
    rw [Set.ncard_coe_finset] at h2
    exact_mod_cast h1 ▸ h2
  have hsum : (Z.card : ℝ) ≤ ((∑ ρ ∈ Z, analyticOrderNatAt G ρ : ℕ) : ℝ) := by
    have h := (Finset.card_eq_sum_ones Z).le.trans (Finset.sum_le_sum horder)
    exact_mod_cast h
  have hlogT : 1 ≤ Real.log |T| := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlog5 : Real.log (|T| + 5) ≤ 2 * Real.log |T| := by
    rw [← Real.log_rpow (by linarith : (0:ℝ) < |T|), Real.rpow_two]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hlogB : Real.log B ≤ (|Real.log (6 * C)| + 2 * A') * Real.log |T| := by
    rw [hB, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity : (0:ℝ) < |T| + 5)]
    have h1 := le_abs_self (Real.log (6 * C))
    have h2 : |Real.log (6 * C)| ≤ |Real.log (6 * C)| * Real.log |T| :=
      le_mul_of_one_le_right (abs_nonneg _) hlogT
    have h3 : A' * Real.log (|T| + 5) ≤ A' * (2 * Real.log |T|) :=
      mul_le_mul_of_nonneg_left hlog5 hA'0
    linarith
  calc ((reZeroSetL χ T).ncard : ℝ) ≤ (Z.card : ℝ) := hcard
    _ ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 1 / Real.log (R / r) * ((|Real.log (6 * C)| + 2 * A') * Real.log |T|) :=
        mul_le_mul_of_nonneg_left hlogB (by positivity)
    _ = _ := by ring


/-- **Backlund's bound for L(s,χ)**: two-sided in T; constants depend on χ. -/
theorem backlund_horizontalChi (hχ1 : χ ≠ 1) : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ |T| →
    (∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv χ.LFunction (σ + T * I)).im| ≤ C * Real.log |T| :=
  backlund_horizontalChi_of_count hχ1 (reZeroSetL_card_le hχ1)

end ThmE
end Zeta23

end
