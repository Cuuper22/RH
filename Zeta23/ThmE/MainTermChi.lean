/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/MainTermChi.lean — the main term of N_χ(T,2T) (a piece of the Riemann–von Mangoldt
formula for L(s,χ), see Zeta23/ThmE/RvMChi.lean):
  |N_χ(T,2T) − (T/2π)·ell1q q T| ≤ C log T   (T ≥ T₀; C, T₀ depend on q).
The analogue for L(s,χ) of Zeta23/RvM/MainTerm.lean, with Λ_sym = completedLSym
(CountByIntegralChi/FoldChi), the Γ/conductor side gammaSideChi, Backlund's bound for L
(BacklundChi) and the local count localCountChi.
-/
import Zeta23.ThmE.LGrowth
import Zeta23.ThmE.Statement
import Zeta23.ThmE.Hypotheses
import Zeta23.ThmE.LocalCountChi
import Zeta23.ThmE.GammaSideChi
import Zeta23.ThmE.CountByIntegralChi
import Zeta23.ThmE.FoldChi
import Zeta23.ThmE.RvMChiDefs
import Zeta23.Assembly
import Zeta23.ThmE.ReZeroCountChi
import Zeta23.ThmE.GammaFactsChiProof

open Complex Set DirichletCharacter MeasureTheory

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-! ### window helpers (analogues of RvM's private lemmas) -/

lemma zerosInL_subset_of_le {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    zerosInL χ a b ⊆ zerosInL χ c d := by
  rintro ρ ⟨hρ, h1, h2⟩
  exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩

lemma NcountL_le_of_subset (hq : 1 < q) (hprim : χ.IsPrimitive) {a b c d : ℝ}
    (h : zerosInL χ a b ⊆ zerosInL χ c d) : NcountL χ a b ≤ NcountL χ c d := by
  have hs : LSeam χ := LSeam_of hq hprim
  have hsub : (LZeros hs).window a b ⊆ (LZeros hs).window c d := by
    rw [LZeros_window, LZeros_window]
    exact h
  have hmono := (LZeros hs).finsum_mult_mono (T₁ := c) (T₂ := d) hsub subset_rfl
  have e1 := LZeros_N (hs := hs) (T₁ := a) (T₂ := b)
  have e2 := LZeros_N (hs := hs) (T₁ := c) (T₂ := d)
  unfold ZeroConfig.N at e1 e2
  rw [← e1, ← e2]
  exact hmono

lemma NcountL_add (hq : 1 < q) (hprim : χ.IsPrimitive) {T₁ T T₂ : ℝ} (h1 : T₁ ≤ T) (h2 : T ≤ T₂) :
    NcountL χ T₁ T₂ = NcountL χ T₁ T + NcountL χ T T₂ := by
  have hs : LSeam χ := LSeam_of hq hprim
  have := Assembly.N_add (Z := LZeros hs) (a := T₁) (b := T) (c := T₂) h1 h2
  simpa only [LZeros_N] using this

/-- zero-free ordinates for L are dense: every [a, a+1] contains one. -/
lemma exists_goodHeightL (hq : 1 < q) (hprim : χ.IsPrimitive) (a : ℝ) :
    ∃ T ∈ Set.Icc a (a + 1), GoodHeightL χ T := by
  have hs : LSeam χ := LSeam_of hq hprim
  have hfin : (zerosInL χ (a - 1) (a + 2)).Finite := by
    have := (LZeros hs).window_finite (a - 1) (a + 2)
    refine this.subset ?_
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨by rwa [LZeros_carrier], h1, h2⟩
  have hSfin : ((fun ρ : ℂ => ρ.im) '' zerosInL χ (a - 1) (a + 2)).Finite := hfin.image _
  have hinf : (Set.Icc a (a + 1)).Infinite := Set.Icc_infinite (by linarith)
  obtain ⟨T, hTd⟩ := (hinf.diff hSfin).nonempty
  obtain ⟨hT, hTnot⟩ := hTd
  refine ⟨T, hT, fun ρ hρ him => hTnot ?_⟩
  refine ⟨ρ, ⟨hρ, ?_, ?_⟩, him⟩
  · rw [him]; linarith [hT.1]
  · rw [him]; linarith [hT.2]

/-! ### the split along the half-contour -/

/-- L(σ + iT) ≠ 0 on the horizontal segment [1/2, 2] at a zero-free ordinate. -/
private lemma LFunction_ne_zero_on_segment' (hq : 1 < q) (hprim : χ.IsPrimitive) {T σ : ℝ}
    (hσ : (1/2:ℝ) ≤ σ) (hgood : GoodHeightL χ T) : χ.LFunction ((σ:ℂ) + T * I) ≠ 0 := by
  have hχ1 := ne_one_of_primitive hq hprim
  intro h0
  rcases lt_or_ge σ 1 with hσ1 | hσ1
  · exact hgood _ ⟨h0, by simpa using (by linarith : (0:ℝ) < σ), by simpa using hσ1⟩ (by simp)
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simpa using hσ1) h0

/-- continuity of logDeriv L along a segment avoiding zeros (parametrised). -/
lemma continuousOn_logDeriv_LFunction (hχ1 : χ ≠ 1) {S : Set ℂ}
    (hS : ∀ s ∈ S, χ.LFunction s ≠ 0) : ContinuousOn (logDeriv χ.LFunction) S := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  have hd : DifferentiableAt ℂ χ.LFunction s := differentiable_LFunction hχ1 s
  have hderiv : ContinuousAt (deriv χ.LFunction) s := by
    have : AnalyticAt ℂ χ.LFunction s := (differentiable_LFunction hχ1).analyticAt s
    exact (this.deriv).continuousAt
  exact (hderiv.div (hd.continuousAt) (hS s hs))

set_option maxHeartbeats 800000 in
/-- the half-contour split: logDeriv Λ_sym = logDeriv L + logDeriv arch along L. -/
lemma halfContourChi_split (hq : 1 < q) (hprim : χ.IsPrimitive) {κ : ℕ}
    (hκdef : ∀ s, gammaFactor χ s = Complex.Gammaℝ (s + κ)) {T₁ T₂ : ℝ}
    (h1 : 1 ≤ T₁) (h12 : T₁ ≤ T₂) (hg1 : GoodHeightL χ T₁) (hg2 : GoodHeightL χ T₂) :
    RvM.halfContour (logDeriv (completedLSym χ)) T₁ T₂ =
      RvM.halfContour (logDeriv χ.LFunction) T₁ T₂ +
        RvM.halfContour (logDeriv (archChi q κ)) T₁ T₂ := by
  have hχ1 := ne_one_of_primitive hq hprim
  -- pointwise split on Re s ∈ [1/2, 2] with L s ≠ 0
  have hpt : ∀ s : ℂ, (1/2:ℝ) ≤ s.re → 0 < s.re → χ.LFunction s ≠ 0 →
      logDeriv (completedLSym χ) s = logDeriv χ.LFunction s + logDeriv (archChi q κ) s := by
    intro s hσ hσ0 hL
    have h := logDeriv_completedLSym_split hq hχ1 hσ0 hL
    rw [h]
    congr 1
    have : (fun z => (q:ℂ)^(z/2) * gammaFactor χ z) = archChi q κ := by
      funext z
      rw [hκdef z]
      rfl
    rw [this]
  -- segment-wise equality of the three integrals
  have hhor : ∀ T : ℝ, GoodHeightL χ T →
      (∫ σ in (1/2:ℝ)..2, logDeriv (completedLSym χ) ((σ:ℂ) + T * I))
        = (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction ((σ:ℂ) + T * I))
          + ∫ σ in (1/2:ℝ)..2, logDeriv (archChi q κ) ((σ:ℂ) + T * I) := by
    intro T hgood
    have hcongr : ∀ σ ∈ Set.uIcc (1/2:ℝ) 2,
        logDeriv (completedLSym χ) ((σ:ℂ) + T * I)
          = logDeriv χ.LFunction ((σ:ℂ) + T * I) + logDeriv (archChi q κ) ((σ:ℂ) + T * I) := by
      intro σ hσ
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
      exact hpt _ (by simpa using hσ.1) (by simp; linarith [hσ.1])
        (LFunction_ne_zero_on_segment' hq hprim hσ.1 hgood)
    rw [intervalIntegral.integral_congr hcongr]
    apply intervalIntegral.integral_add
    · apply ContinuousOn.intervalIntegrable
      apply (continuousOn_logDeriv_LFunction hχ1 (S := {s : ℂ | (1/2:ℝ) ≤ s.re ∧ s.im = T ∧
          χ.LFunction s ≠ 0}) (fun s hs => hs.2.2)).comp (by fun_prop : Continuous fun σ : ℝ =>
          (σ:ℂ) + T * I).continuousOn ?_
      intro σ hσ
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
      exact ⟨by simpa using hσ.1, by simp, LFunction_ne_zero_on_segment' hq hprim hσ.1 hgood⟩
    · apply ContinuousOn.intervalIntegrable
      apply ((logDeriv_archChi_differentiableOn q κ).continuousOn.comp
        (by fun_prop : Continuous fun σ : ℝ => (σ:ℂ) + T * I).continuousOn ?_)
      intro σ hσ
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
      show (0:ℝ) < ((σ:ℂ) + T * I).re
      simp
      linarith [hσ.1]
  have hvert :
      (∫ t in T₁..T₂, logDeriv (completedLSym χ) ((2:ℂ) + t * I))
        = (∫ t in T₁..T₂, logDeriv χ.LFunction ((2:ℂ) + t * I))
          + ∫ t in T₁..T₂, logDeriv (archChi q κ) ((2:ℂ) + t * I) := by
    have hcongr : ∀ t ∈ Set.uIcc T₁ T₂,
        logDeriv (completedLSym χ) ((2:ℂ) + t * I)
          = logDeriv χ.LFunction ((2:ℂ) + t * I) + logDeriv (archChi q κ) ((2:ℂ) + t * I) := by
      intro t ht
      have hre2 : ((2:ℂ) + t * I).re = 2 := by simp
      exact hpt _ (by rw [hre2]; norm_num) (by rw [hre2]; norm_num)
        (LFunction_ne_zero_of_two_le_re (by rw [hre2]))
    rw [intervalIntegral.integral_congr hcongr]
    apply intervalIntegral.integral_add
    · apply ContinuousOn.intervalIntegrable
      apply (continuousOn_logDeriv_LFunction hχ1 (S := {s : ℂ | s.re = 2})
        (fun s hs => LFunction_ne_zero_of_two_le_re (by rw [hs]))).comp
        (by fun_prop : Continuous fun t : ℝ => (2:ℂ) + t * I).continuousOn ?_
      intro t ht
      show ((2:ℂ) + t * I).re = 2
      simp
    · apply ContinuousOn.intervalIntegrable
      apply ((logDeriv_archChi_differentiableOn q κ).continuousOn.comp
        (by fun_prop : Continuous fun t : ℝ => (2:ℂ) + t * I).continuousOn ?_)
      intro t ht
      show (0:ℝ) < ((2:ℂ) + t * I).re
      simp
  unfold RvM.halfContour
  rw [hhor T₁ hg1, hhor T₂ hg2, hvert]
  ring

/-! ### mu_chi bounds and the assembly -/

/-- |mu_chi(tau)| << log(tau+3) for tau >= 1 (constants depend on q). -/
theorem muq_le_log {κ : ℕ} (hΓχ : GammaFactsChi κ q) : ∃ CM : ℝ, 0 < CM ∧ ∀ τ : ℝ, 1 ≤ τ →
    |muq κ q τ| ≤ CM * Real.log (τ + 3) := by
  obtain ⟨C₀, hC₀⟩ := hΓχ.stirling
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine ⟨1 + |C₀| + |Real.log ((q:ℝ) / (2 * Real.pi))|, by positivity, fun τ hτ => ?_⟩
  have hτ0 : (0:ℝ) < τ := by linarith
  have h1 := hC₀ τ (by rw [abs_of_pos hτ0]; exact hτ)
  rw [abs_of_pos hτ0] at h1
  obtain ⟨hl, hr⟩ := abs_le.mp h1
  have hlog3 : 1 ≤ Real.log (τ + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlogτ0 : 0 ≤ Real.log τ := Real.log_nonneg hτ
  have hlogτ : Real.log τ ≤ Real.log (τ + 3) := Real.log_le_log hτ0 (by linarith)
  have hdiv : Real.log ((q:ℝ) * τ / (2 * Real.pi))
      = Real.log τ + Real.log ((q:ℝ) / (2 * Real.pi)) := by
    rw [show (q:ℝ) * τ / (2 * Real.pi) = τ * ((q:ℝ) / (2 * Real.pi)) by ring]
    rw [Real.log_mul (by positivity) (by positivity)]
  rw [hdiv] at hl hr
  have hC₀τ : |C₀ / τ ^ 2| ≤ |C₀| := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < τ ^ 2)]
    apply div_le_self (abs_nonneg _) (by nlinarith)
  obtain ⟨hCl, hCr⟩ := abs_le.mp hC₀τ
  have h2π : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have h2π0 : 0 < 1 / (2 * Real.pi) := by positivity
  have hlogq := le_abs_self (Real.log ((q:ℝ) / (2 * Real.pi)))
  have hlogq' := neg_abs_le (Real.log ((q:ℝ) / (2 * Real.pi)))
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

set_option maxHeartbeats 1600000 in
/-- The assembly, against the chi-Backlund bounds and H-Gamma(chi) as explicit hypotheses
(instantiated in mainChi). -/
theorem mainChi_aux (hq : 1 < q) (hprim : χ.IsPrimitive) {κ : ℕ}
    (hκdef : ∀ s, gammaFactor χ s = Complex.Gammaℝ (s + κ))
    (hΓχ : GammaFactsChi κ q)
    (backlundχ : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ |T| →
      (∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv χ.LFunction (σ + T * I)).im| ≤ C * Real.log |T|)
    (verticalχ : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I) * I).im| ≤ Real.pi) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T| ≤ C * Real.log T := by
  obtain ⟨CB, TB, hB⟩ := backlundχ
  obtain ⟨A₀, hA₀1, hA₀⟩ := localCountChi hq hprim
  obtain ⟨Cμ, Tμ, hCμ⟩ := hΓχ.int_mu
  obtain ⟨CM, hCM0, hCM⟩ := muq_le_log hΓχ
  have hμc : Continuous (muq κ q) := hΓχ.smooth.continuous
  have hA₀0 : 0 ≤ A₀ := by linarith
  refine ⟨3 * |CB| + 4 + 4 * A₀ + 4 * CM + |Cμ|, max (max (|TB| + 1) (Tμ + 1)) 4,
    fun T hT => ?_⟩
  have hT4 : 4 ≤ T := le_trans (le_max_right _ _) hT
  have hTB : |TB| + 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTμ : Tμ + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlogT0 : 0 < Real.log T := by linarith
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeightL hq hprim (T - 1)
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeightL hq hprim (2 * T)
  have hT₁a : T - 1 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ T := by have := hT₁mem.2; linarith
  have hT₂a : 2 * T ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ 2 * T + 1 := hT₂mem.2
  have h1T₁ : 1 ≤ T₁ := by linarith
  have h12 : T₁ ≤ T₂ := by linarith
  have hN := NcountL_eq_im_halfContour hq hprim h12 hg1 hg2
  have hsplit := halfContourChi_split hq hprim hκdef h1T₁ h12 hg1 hg2
  have hgam := gammaSideChi q κ (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  have hadd : (NcountL χ T₁ T₂ : ℝ)
      = (NcountL χ T₁ T : ℝ) + (NcountL χ T (2*T) : ℝ) + (NcountL χ (2*T) T₂ : ℝ) := by
    have e1 := NcountL_add hq hprim (T₁ := T₁) (T := T) (T₂ := T₂) hT₁b (by linarith)
    have e2 := NcountL_add hq hprim (T₁ := T) (T := 2*T) (T₂ := T₂) (by linarith) hT₂a
    rw [e1, e2]
    push_cast
    ring
  have hlogsq : ∀ x : ℝ, 0 < x → x + 3 ≤ T ^ 2 → Real.log (x + 3) ≤ 2 * Real.log T := by
    intro x hx hxT
    calc Real.log (x + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hxT
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hw1 : (NcountL χ T₁ T : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : NcountL χ T₁ T ≤ NcountL χ T₁ (T₁ + 1) :=
      NcountL_le_of_subset hq hprim (zerosInL_subset_of_le le_rfl (by linarith))
    calc (NcountL χ T₁ T : ℝ) ≤ (NcountL χ T₁ (T₁ + 1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|T₁| + 3) := hA₀ T₁
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : (0:ℝ) < T₁)]
          exact hlogsq T₁ (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  have hw2 : (NcountL χ (2*T) T₂ : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : NcountL χ (2*T) T₂ ≤ NcountL χ (2*T) (2*T + 1) :=
      NcountL_le_of_subset hq hprim (zerosInL_subset_of_le le_rfl hT₂b)
    calc (NcountL χ (2*T) T₂ : ℝ) ≤ (NcountL χ (2*T) (2*T+1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|2*T| + 3) := hA₀ (2*T)
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : (0:ℝ) < 2*T)]
          exact hlogsq (2*T) (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  have habs₁ : |T₁| = T₁ := abs_of_pos (by linarith)
  have habs₂ : |T₂| = T₂ := abs_of_pos (by linarith)
  have hbk1 := hB T₁ (by rw [habs₁]; linarith [le_abs_self TB, neg_abs_le TB]) hg1
  have hbk2 := hB T₂ (by rw [habs₂]; linarith [le_abs_self TB, neg_abs_le TB]) hg2
  rw [habs₁] at hbk1
  rw [habs₂] at hbk2
  have hvert := verticalχ T₁ T₂
  have hlog₁0 : 0 ≤ Real.log T₁ := Real.log_nonneg h1T₁
  have hlog₂0 : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hLbound : |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
      ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
    unfold RvM.halfContour
    have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I))
        + (∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I
        - ∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im
        = (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [eim]
    have hmulI : ((∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I).im
        = (∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I) * I).im :=
      congrArg Complex.im (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume) I
        (fun t : ℝ => logDeriv χ.LFunction (2 + t * I))).symm
    have h1 : |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im|
        ≤ |CB| * Real.log T₁ :=
      hbk1.trans (mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₁0)
    have h2 : |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im|
        ≤ |CB| * Real.log T₂ :=
      hbk2.trans (mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₂0)
    calc |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im|
        ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im|
          + |((∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I).im|
          + |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
          rw [hmulI]
          linarith [hvert]
  have hμint : ∀ a b : ℝ, IntervalIntegrable (muq κ q) MeasureTheory.volume a b :=
    fun a b => hμc.intervalIntegrable a b
  have hμsplit : (∫ t in T₁..T₂, muq κ q t)
      = (∫ t in T₁..T, muq κ q t) + (∫ t in T..(2*T), muq κ q t)
        + ∫ t in (2*T)..T₂, muq κ q t := by
    have e1 : (∫ t in T₁..(2*T), muq κ q t)
        = (∫ t in T₁..T, muq κ q t) + ∫ t in T..(2*T), muq κ q t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ T) (hμint T (2*T))).symm
    have e2 : (∫ t in T₁..T₂, muq κ q t)
        = (∫ t in T₁..(2*T), muq κ q t) + ∫ t in (2*T)..T₂, muq κ q t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ (2*T)) (hμint (2*T) T₂)).symm
    rw [e2, e1]
  have hμwin : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2*T + 1 → |b - a| ≤ 1 →
      |∫ t in a..b, muq κ q t| ≤ 2 * CM * Real.log T := by
    intro a b ha hab hb hba
    have hbound : ∀ t ∈ Set.uIoc a b, ‖muq κ q t‖ ≤ CM * Real.log (2*T + 4) := by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht1 : 1 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2*T + 1 := le_trans ht.2 hb
      rw [Real.norm_eq_abs]
      refine (hCM t ht1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCM0.le
      exact Real.log_le_log (by linarith) (by linarith)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs] at hnorm
    have hlog24 : Real.log (2*T + 4) ≤ 2 * Real.log T := by
      calc Real.log (2*T + 4) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
    calc |∫ t in a..b, muq κ q t| ≤ CM * Real.log (2*T+4) * |b - a| := hnorm
      _ ≤ CM * (2 * Real.log T) * 1 := by
          refine mul_le_mul ?_ hba (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hlog24 hCM0.le
      _ = 2 * CM * Real.log T := by ring
  have hμ1 : |∫ t in T₁..T, muq κ q t| ≤ 2 * CM * Real.log T :=
    hμwin T₁ T h1T₁ hT₁b (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hμ2 : |∫ t in (2*T)..T₂, muq κ q t| ≤ 2 * CM * Real.log T :=
    hμwin (2*T) T₂ (by linarith) hT₂a (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hintmu := hCμ T (by linarith)
  have hCμT : Cμ / T ≤ |Cμ| := by
    calc Cμ / T ≤ |Cμ| / T := by gcongr; exact le_abs_self _
      _ ≤ |Cμ| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          linarith
      _ = |Cμ| := div_one _
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hkey : (NcountL χ T (2*T) : ℝ) - T / (2 * Real.pi) * ell1q q T
      = (1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
        + ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
        + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)))
        - ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ)) := by
    have hΛim : (1/Real.pi) * (RvM.halfContour (logDeriv (completedLSym χ)) T₁ T₂).im
        = (1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
          + (1/Real.pi) * (RvM.halfContour (logDeriv (archChi q κ)) T₁ T₂).im := by
      rw [hsplit, Complex.add_im]
      ring
    have h5 : (NcountL χ T₁ T₂ : ℝ)
        = (1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
          + ∫ t in T₁..T₂, muq κ q t := by
      rw [hN, hΛim, hgam]
    rw [hμsplit] at h5
    have hTell : T / (2 * Real.pi) * ell1q q T = T * ell1q q T / (2 * Real.pi) := by ring
    rw [hTell]
    linarith [hadd]
  have hlogT₁ : Real.log T₁ ≤ Real.log T := Real.log_le_log (by linarith) hT₁b
  have hlogT₂ : Real.log T₂ ≤ 2 * Real.log T := by
    calc Real.log T₂ ≤ Real.log (T^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hA : |(1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
      ≤ (3 * |CB| + 4) * Real.log T := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/Real.pi)]
    have hfrac : (1:ℝ)/Real.pi ≤ 1 := by rw [div_le_one hπ]; exact hπ1
    have step : (1/Real.pi) * |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
        ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
      calc (1/Real.pi) * |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
          ≤ 1 * |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im| :=
            mul_le_mul_of_nonneg_right hfrac (abs_nonneg _)
        _ = |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im| := one_mul _
        _ ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := hLbound
    have hπ4 : Real.pi ≤ 4 * Real.log T := by
      nlinarith [Real.pi_lt_d2]
    have e1 : |CB| * Real.log T₁ ≤ |CB| * Real.log T :=
      mul_le_mul_of_nonneg_left hlogT₁ (abs_nonneg _)
    have e2 : |CB| * Real.log T₂ ≤ |CB| * (2 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlogT₂ (abs_nonneg _)
    nlinarith [abs_nonneg CB]
  have hmid : |(∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)| ≤ |Cμ| * Real.log T := by
    calc |(∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)| ≤ Cμ / T := hintmu
      _ ≤ |Cμ| := hCμT
      _ ≤ |Cμ| * Real.log T := le_mul_of_one_le_right (abs_nonneg _) hlogT
  rw [hkey]
  have hNc1 : (0:ℝ) ≤ (NcountL χ T₁ T : ℝ) := Nat.cast_nonneg _
  have hNc2 : (0:ℝ) ≤ (NcountL χ (2*T) T₂ : ℝ) := Nat.cast_nonneg _
  have htri : |(1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
        + ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
        + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)))
        - ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ))|
      ≤ |(1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
        + (|∫ t in T₁..T, muq κ q t| + |∫ t in (2*T)..T₂, muq κ q t|
        + |(∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)|)
        + ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ)) := by
    have h1 := abs_add_le ((1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im)
      ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
        + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)))
    have h2 := abs_add_le (∫ t in T₁..T, muq κ q t) (∫ t in (2*T)..T₂, muq κ q t)
    have h3 := abs_add_le ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t))
      ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi))
    have h4 := abs_sub (((1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im)
        + ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
        + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi))))
      ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ))
    have h5 : |(NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ)|
        = (NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ) := abs_of_nonneg (by positivity)
    rw [h5] at h4
    linarith
  refine htri.trans ?_
  have hfinal : (NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ) ≤ 4 * A₀ * Real.log T := by
    linarith
  nlinarith [hA, hμ1, hμ2, hmid, hfinal, hlogT0]

/-- mainChi modulo only the σ=2 vertical bound and H-Γ(χ) (both supplied in mainChi). -/
theorem mainChi_of (hq : 1 < q) (hprim : χ.IsPrimitive)
    (hΓχ : ∀ κ : ℕ, κ ≤ 1 → GammaFactsChi κ q)
    (hvert : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I) * I).im| ≤ Real.pi) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T| ≤ C * Real.log T := by
  have hχ1 := ne_one_of_primitive hq hprim
  rcases χ.even_or_odd with he | ho
  · refine mainChi_aux hq hprim (κ := 0) (fun s => ?_) (hΓχ 0 (by norm_num))
      (backlund_horizontalChi hχ1) hvert
    rw [he.gammaFactor_def]
    norm_num
  · refine mainChi_aux hq hprim (κ := 1) (fun s => ?_) (hΓχ 1 le_rfl)
      (backlund_horizontalChi hχ1) hvert
    rw [ho.gammaFactor_def]
    norm_num

/-- mainChi modulo H-Gamma(chi) alone (vertical bound from BacklundChi.vertical_twoChi). -/
theorem mainChi_of_Gamma (hq : 1 < q) (hprim : χ.IsPrimitive)
    (hΓχ : ∀ κ : ℕ, κ ≤ 1 → GammaFactsChi κ q) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T| ≤ C * Real.log T :=
  mainChi_of hq hprim hΓχ (vertical_twoChi (ne_one_of_primitive hq hprim))

/-- **Main term for N_χ(T,2T)**. -/
theorem mainChi (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T| ≤ C * Real.log T :=
  mainChi_of_Gamma hq hprim fun κ hκ => GammaChi.gammaFactsChi hκ (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))

end ThmE
end Zeta23
