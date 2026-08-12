import RH.Zeta85.Discharge.RSRemoteTailSix

/-!
# Vanishing of the completed-to-guarded quartic correction

This module combines sixth-order remote Poisson decay with an explicit
off-critical-line growth bound for the completed balanced kernel.  The
normalized fourth-trace correction then tends to zero.
-/

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

theorem distinguishedWindowFourierMajorantTwelve_le
    {Z : ZeroConfig} {σ μ p c T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 ≤ μ) (hT : 1 < T)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hmass : distinguishedWindowSobolevMassSix F T ≤ c * Zeta23.l T) :
    distinguishedWindowFourierMajorantTwelve F T ≤
      c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2 := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hlogconst : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hlLog : Zeta23.l T ≤ Real.log T := by
    rw [Zeta23.Assembly.log_eq_l_add hT0]
    linarith
  have hexp :
      (Real.exp ((1 / 2 : ℝ) *
        (F.period T (F.distinguished T) / 2))) ^ 2 ≤
        T ^ (μ / 2 : ℝ) := by
    rw [pow_two, ← Real.exp_add]
    rw [hperiod, Real.rpow_def_of_pos hT0]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hlLog
      (show 0 ≤ μ / 2 by positivity)
    nlinarith
  have hmass0 : 0 ≤ distinguishedWindowSobolevMassSix F T := by
    unfold distinguishedWindowSobolevMassSix
    positivity
  have hcl0 : 0 ≤ c * Zeta23.l T := hmass0.trans hmass
  unfold distinguishedWindowFourierMajorantTwelve
  calc
    (Real.exp ((1 / 2 : ℝ) *
          (F.period T (F.distinguished T) / 2)) *
        distinguishedWindowSobolevMassSix F T) ^ 2 =
        (Real.exp ((1 / 2 : ℝ) *
          (F.period T (F.distinguished T) / 2))) ^ 2 *
          distinguishedWindowSobolevMassSix F T ^ 2 := by ring
    _ ≤ T ^ (μ / 2 : ℝ) * (c * Zeta23.l T) ^ 2 :=
      mul_le_mul hexp ((sq_le_sq₀ hmass0 hcl0).2 hmass)
        (sq_nonneg _) (by positivity)
    _ = c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2 := by ring

theorem distinguishedRemoteTailGridFactorTwelve_le
    {Z : ZeroConfig} {σ μ p T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 < μ) (hT : 1 ≤ T) (hl : 1 ≤ Zeta23.l T)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T) :
    (Zeta23.D0 T ^ 8)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 11)⁻¹ := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT0
  have hold := PoissonKernelBridge.distinguishedRemoteTailGridFactor_le
    F hμ hT hl hperiod
  calc
    (Zeta23.D0 T ^ 8)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (Zeta23.D0 T ^ 8)⁻¹ *
        ((1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 3)⁻¹) := by gcongr
    _ = (1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 11)⁻¹ := by
      field_simp [hD.ne']

theorem N_cube_mul_distinguishedRemoteTailScaleTwelve_le
    {Z : ZeroConfig} {σ μ p c T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 < μ) (hT : 1 < T) (hl : 1 ≤ Zeta23.l T)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hN : (Z.N T (2 * T) : ℝ) ≤ T * Zeta23.l T)
    (hMaj : distinguishedWindowFourierMajorantTwelve F T ≤
      c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2)
    (hTail : (Zeta23.D0 T ^ 8)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 11)⁻¹) :
    (Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T ≤
      c ^ 2 * (1 + μ) * T ^ (μ / 2 - 5 / 2 : ℝ) *
        Real.log T ^ 6 := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT0
  have hl0 : 0 ≤ Zeta23.l T := le_trans zero_le_one hl
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (le_of_lt hT)
  have hlogconst : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hlLog : Zeta23.l T ≤ Real.log T := by
    rw [Zeta23.Assembly.log_eq_l_add hT0]
    linarith
  have hgrid : 0 < PoissonKernelBridge.distinguishedGridStep F T := by
    unfold PoissonKernelBridge.distinguishedGridStep
    rw [hperiod]
    positivity
  have htail0 : 0 ≤ (Zeta23.D0 T ^ 8)⁻¹ *
      ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
        (3 * PoissonKernelBridge.distinguishedGridStep F T)) := by positivity
  have hmaj0 : 0 ≤ distinguishedWindowFourierMajorantTwelve F T := by
    unfold distinguishedWindowFourierMajorantTwelve
    positivity
  have hrightMaj0 :
      0 ≤ c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2 := by positivity
  have hNpow : (Z.N T (2 * T) : ℝ) ^ 3 ≤
      (T * Zeta23.l T) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hN 3
  have hraw :
      (Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T ≤
        (T * Zeta23.l T) ^ 3 *
          ((c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2) *
            ((1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 11)⁻¹)) := by
    unfold distinguishedRemoteTailScaleTwelve
    calc
      (Z.N T (2 * T) : ℝ) ^ 3 *
          (distinguishedWindowFourierMajorantTwelve F T *
            ((Zeta23.D0 T ^ 8)⁻¹ *
              ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
                (3 * PoissonKernelBridge.distinguishedGridStep F T)))) ≤
          (T * Zeta23.l T) ^ 3 *
            (distinguishedWindowFourierMajorantTwelve F T *
              ((Zeta23.D0 T ^ 8)⁻¹ *
                ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
                  (3 * PoissonKernelBridge.distinguishedGridStep F T)))) :=
        mul_le_mul_of_nonneg_right hNpow (mul_nonneg hmaj0 htail0)
      _ ≤ (T * Zeta23.l T) ^ 3 *
          ((c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2) *
            ((Zeta23.D0 T ^ 8)⁻¹ *
              ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
                (3 * PoissonKernelBridge.distinguishedGridStep F T)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hMaj htail0) (by positivity)
      _ ≤ (T * Zeta23.l T) ^ 3 *
          ((c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2) *
            ((1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 11)⁻¹)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hTail hrightMaj0) (by positivity)
  have hDsquare : Zeta23.D0 T ^ 2 = T := Real.sq_sqrt hT0.le
  have hD11 : Zeta23.D0 T ^ 11 = Zeta23.D0 T * T ^ 5 := by
    calc
      Zeta23.D0 T ^ 11 = Zeta23.D0 T * (Zeta23.D0 T ^ 2) ^ 5 := by ring
      _ = Zeta23.D0 T * T ^ 5 := by rw [hDsquare]
  have hpower :
      T ^ 3 * T ^ (μ / 2 : ℝ) * (Zeta23.D0 T ^ 11)⁻¹ =
        T ^ (μ / 2 - 5 / 2 : ℝ) := by
    rw [hD11]
    have hcancel :
        T ^ 3 * T ^ (μ / 2 : ℝ) * (Zeta23.D0 T * T ^ 5)⁻¹ =
          T ^ (μ / 2 : ℝ) / (Zeta23.D0 T * T ^ 2) := by
      field_simp
    rw [hcancel, Zeta23.D0, Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast T 2, ← Real.rpow_add hT0]
    rw [← Real.rpow_sub hT0]
    congr 1
    ring
  calc
    (Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T ≤ _ := hraw
    _ = c ^ 2 * (1 + μ) *
          (T ^ 3 * T ^ (μ / 2 : ℝ) * (Zeta23.D0 T ^ 11)⁻¹) *
            Zeta23.l T ^ 6 := by ring
    _ = c ^ 2 * (1 + μ) * T ^ (μ / 2 - 5 / 2 : ℝ) *
          Zeta23.l T ^ 6 := by rw [hpower]
    _ ≤ c ^ 2 * (1 + μ) * T ^ (μ / 2 - 5 / 2 : ℝ) *
          Real.log T ^ 6 := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ hl0 hlLog 6
      · positivity

theorem tendsto_rpow_two_mu_sub_five_halves_mul_log_pow_six
    {μ : ℝ} (hμ : μ < 1) :
    Tendsto (fun T : ℝ =>
      T ^ (2 * μ - 5 / 2 : ℝ) * Real.log T ^ 6) atTop (nhds 0) := by
  let δ : ℝ := 5 / 2 - 2 * μ
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  have ho := isLittleO_log_rpow_rpow_atTop (6 : ℝ) hδ
  have hzero : ∀ᶠ T : ℝ in atTop,
      T ^ δ = 0 → Real.log T ^ (6 : ℝ) = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    intro hpow
    exact (((Real.rpow_ne_zero hT.le hδ.ne').2 hT.ne') hpow).elim
  have hratio : Tendsto
      (fun T : ℝ => Real.log T ^ (6 : ℝ) / T ^ δ)
      atTop (nhds 0) :=
    (Asymptotics.isLittleO_iff_tendsto' hzero).1 ho
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hlogpow : Real.log T ^ (6 : ℝ) = Real.log T ^ (6 : ℕ) :=
    Real.rpow_natCast (Real.log T) 6
  rw [hlogpow]
  have hexp : 2 * μ - 5 / 2 = -δ := by
    dsimp only [δ]
    ring
  rw [hexp, Real.rpow_neg hT0.le]
  simp only [div_eq_mul_inv]
  ring

theorem N_cube_tailTwelve_mul_completedGrowth_le
    {Z : ZeroConfig} {σ μ p c T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 < μ) (hT : 1 < T) (hl : 1 ≤ Zeta23.l T)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hN : (Z.N T (2 * T) : ℝ) ≤ T * Zeta23.l T)
    (hMaj : distinguishedWindowFourierMajorantTwelve F T ≤
      c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2)
    (hTail : (Zeta23.D0 T ^ 8)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 11)⁻¹) :
    ((Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T) *
        T ^ (3 * μ / 2 : ℝ) ≤
      c ^ 2 * (1 + μ) * T ^ (2 * μ - 5 / 2 : ℝ) *
        Real.log T ^ 6 := by
  have hbase := N_cube_mul_distinguishedRemoteTailScaleTwelve_le
    F hμ hT hl hperiod hN hMaj hTail
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  calc
    ((Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T) *
        T ^ (3 * μ / 2 : ℝ) ≤
      (c ^ 2 * (1 + μ) * T ^ (μ / 2 - 5 / 2 : ℝ) *
        Real.log T ^ 6) * T ^ (3 * μ / 2 : ℝ) := by gcongr
    _ = c ^ 2 * (1 + μ) * T ^ (2 * μ - 5 / 2 : ℝ) *
        Real.log T ^ 6 := by
      rw [show T ^ (2 * μ - 5 / 2 : ℝ) =
        T ^ (μ / 2 - 5 / 2 : ℝ) * T ^ (3 * μ / 2 : ℝ) by
          rw [← Real.rpow_add hT0]
          congr 1
          ring]
      ring

theorem tendsto_N_cube_tailTwelve_mul_completedGrowth
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 < μ) (hμ1 : μ < 1) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T =>
      ((Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T) *
        T ^ (3 * μ / 2 : ℝ)) atTop (nhds 0) := by
  obtain ⟨c, hc⟩ := hmass.bound
  have hlim : Tendsto (fun T =>
      c ^ 2 * (1 + μ) *
        (T ^ (2 * μ - 5 / 2 : ℝ) * Real.log T ^ 6))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => c ^ 2 * (1 + μ)) atTop
        (nhds (c ^ 2 * (1 + μ))) := tendsto_const_nhds
    simpa only [mul_zero] using hconst.mul
      (tendsto_rpow_two_mu_sub_five_halves_mul_log_pow_six hμ1)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hperiod, Zeta23.Assembly.eventually_one_le_l,
      eventually_gt_atTop (1 : ℝ)] with T hperiodT hl hT
    have hgrid : 0 < PoissonKernelBridge.distinguishedGridStep F T := by
      unfold PoissonKernelBridge.distinguishedGridStep
      rw [hperiodT]
      positivity
    unfold distinguishedRemoteTailScaleTwelve
    apply mul_nonneg
    · apply mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3)
      apply mul_nonneg
      · unfold distinguishedWindowFourierMajorantTwelve
        positivity
      · apply mul_nonneg
        · exact inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg T) 8)
        · apply add_nonneg
          · exact inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg T) 4)
          · exact div_nonneg
              (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg T) 3))
              (mul_nonneg (by norm_num) hgrid.le)
    · exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hT)) _
  · filter_upwards [hc, hperiod, Zeta23.Assembly.eventually_one_le_l,
      Zeta23.Assembly.eventually_N_le Z hRvM,
      eventually_gt_atTop (1 : ℝ)] with T hmassT hperiodT hl hN hT
    have hmass0 : 0 ≤ distinguishedWindowSobolevMassSix F T := by
      unfold distinguishedWindowSobolevMassSix
      positivity
    have hl0 : 0 ≤ Zeta23.l T := le_trans zero_le_one hl
    have hmassPoint :
        distinguishedWindowSobolevMassSix F T ≤ c * Zeta23.l T := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hmass0,
        abs_of_nonneg hl0] using hmassT
    have hMaj := distinguishedWindowFourierMajorantTwelve_le
      F hμ.le hT hperiodT hmassPoint
    have hTail := distinguishedRemoteTailGridFactorTwelve_le
      F hμ hT.le hl hperiodT
    simpa only [mul_assoc] using N_cube_tailTwelve_mul_completedGrowth_le
      F hμ hT hl hperiodT hN hMaj hTail

theorem remoteLatticePairScaleTwelve_completedGrowth_negligible
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hσ : 0 ≤ σ)
    (hμ : 0 < μ) (hμ1 : μ < 1) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T =>
      ((Z.N T (2 * T) : ℝ) ^ 3 * remoteLatticePairScaleTwelve F T) *
        T ^ (3 * μ / 2 : ℝ)) atTop (nhds 0) := by
  have htail := tendsto_N_cube_tailTwelve_mul_completedGrowth
    F hμ hμ1 hRvM hperiod hmass
  have hconst : Tendsto (fun _ : ℝ => 2 * (σ / μ)) atTop
      (nhds (2 * (σ / μ))) := tendsto_const_nhds
  have hlim := hconst.mul htail
  simpa only [mul_zero] using hlim.congr' (by
    filter_upwards [hperiod, Zeta23.Assembly.eventually_one_le_l]
      with T hperiodT hl
    have hlpos : 0 < Zeta23.l T := lt_of_lt_of_le zero_lt_one hl
    rw [remoteLatticePairScaleTwelve,
      norm_distinguishedLatticeScale_eq_ratio F T hσ hμ hlpos hperiodT]
    ring)

theorem remoteLatticePairScaleTwelve_tendsto_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hσ : 0 ≤ σ)
    (hμ : 0 < μ) (hμ1 : μ < 1) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T => remoteLatticePairScaleTwelve F T) atTop (nhds 0) := by
  have hprod := remoteLatticePairScaleTwelve_completedGrowth_negligible
    F hσ hμ hμ1 hRvM hperiod hmass
  refine squeeze_zero' ?_ ?_ hprod
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hperiod,
      Zeta23.Assembly.eventually_l_pos] with T hT hperiodT hl
    exact remoteLatticePairScaleTwelve_nonneg F T hT (by
      rw [hperiodT]
      exact mul_pos hμ hl)
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hperiod,
      Zeta23.Assembly.eventually_l_pos,
      (Zeta23.Assembly.tendsto_N_atTop Z hRvM).eventually_ge_atTop 1]
      with T hT hperiodT hl hN
    have hT0 : 0 < T := lt_trans zero_lt_one hT
    have hscale : 0 ≤ remoteLatticePairScaleTwelve F T :=
      remoteLatticePairScaleTwelve_nonneg F T hT0 (by
        rw [hperiodT]
        exact mul_pos hμ hl)
    have hN3 : 1 ≤ (Z.N T (2 * T) : ℝ) ^ 3 := by
      nlinarith [pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hN 3]
    have hgrowth : 1 ≤ T ^ (3 * μ / 2 : ℝ) := by
      exact Real.one_le_rpow hT.le (by positivity)
    calc
      remoteLatticePairScaleTwelve F T =
          1 * remoteLatticePairScaleTwelve F T := by ring
      _ ≤ (Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T := by gcongr
      _ = ((Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T) * 1 := by ring
      _ ≤ ((Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T) *
            T ^ (3 * μ / 2 : ℝ) := by gcongr

theorem eventually_balancedRemote_norm_le_twelve
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : PoissonKernelBridge.DistinguishedGuardedPoissonKernelData F)
    (hhat : ∀ᶠ T in atTop, 0 < F.hatDenominator T) :
    ∀ᶠ T in atTop,
      ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
        remoteLatticePairScaleTwelve F T *
          ((Z.NIprime T : ℝ) / F.hatDenominator T) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hguard.periods_pos,
    eventually_remotePair_le_scale_twelve htail hguard, hhat]
      with T hT hperiod hpair hhatT
  have h := norm_balancedKernelMatrix_le
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (remoteLatticePairScaleTwelve_nonneg F T hT
      (hperiod (F.distinguished T))) hpair
  change ‖balancedKernelMatrix
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ))‖ ≤ _
  rw [sum_zeroVertexWeight_norm_sq F T hhatT] at h
  exact h

theorem eventually_balancedFull_norm_le_completedGrowth
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hprincipal : PrincipalCyclicBlock F)
    (hRvM : RiemannVonMangoldt Z) (w c : ℝ)
    (hadm : ∀ᶠ T in atTop,
      AdmWindow (F.window T (F.distinguished T))
        (F.period T (F.distinguished T)) w c)
    (hhat : ∀ᶠ T in atTop, 1 ≤ F.hatDenominator T) :
    ∀ᶠ T in atTop,
      ‖balancedFullLatticeZeroMatrix F T‖ ≤
        2 * (1 + μ) * T ^ (μ / 2 : ℝ) *
          (Z.N T (2 * T) : ℝ) := by
  have hefrac : ∀ᶠ T in atTop,
      distinguishedEnergyFraction F T < μ + 1 :=
    hprincipal.distinguished_energy_ratio.eventually
      (Iio_mem_nhds (by linarith))
  filter_upwards [hadm, hhat, hefrac,
    hprincipal.distinguished_period,
    hprincipal.distinguished_channel_energy_pos,
    hprincipal.local_profile_integrable,
    hprincipal.local_profile_nonneg,
    hprincipal.local_profile_support,
    hprincipal.local_profile_mean_one,
    Zeta23.Assembly.eventually_l_pos,
    eventually_NIprime_le_two_core hRvM,
    eventually_gt_atTop (1 : ℝ)]
      with T hadmT hhatT hefracT hperiodT hE hprofileInt
        hprofileNonneg hprofileSupport hprofileMean hl hNI hT
  have hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T := by
    unfold QuarticGramFamily.fullLength
    exact mul_pos hprincipal.support_pos hl
  have htotal : 0 < ∫ u : ℝ, F.windowEnergy T u := by
    by_contra hnot
    have hnonpos : (∫ u : ℝ, F.windowEnergy T u) ≤ 0 := le_of_not_gt hnot
    have hprod : QuarticGramFamily.fullLength (σ := σ) T *
        (∫ u : ℝ, F.windowEnergy T u) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfull.le hnonpos
    unfold QuarticGramFamily.hatDenominator at hhatT
    linarith
  have hfullNorm := norm_balancedFullLatticeZeroMatrix_le
    F T w c hadmT hfull hE htotal hprofileInt hprofileNonneg
      hprofileSupport hprofileMean
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hlogconst : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hlLog : Zeta23.l T ≤ Real.log T := by
    rw [Zeta23.Assembly.log_eq_l_add hT0]
    linarith
  have hexp : Real.exp (F.period T (F.distinguished T) / 2) ≤
      T ^ (μ / 2 : ℝ) := by
    rw [hperiodT, Real.rpow_def_of_pos hT0]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hlLog hprincipal.bandwidth_pos.le
    nlinarith
  have hefrac0 : 0 ≤ distinguishedEnergyFraction F T := by
    unfold distinguishedEnergyFraction
    exact div_nonneg hE.le htotal.le
  have hN0 : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hmu1 : 0 ≤ 1 + μ := by linarith [hprincipal.bandwidth_pos]
  have hrpow0 : 0 ≤ T ^ (μ / 2 : ℝ) := Real.rpow_nonneg hT0.le _
  calc
    ‖balancedFullLatticeZeroMatrix F T‖ ≤
        distinguishedEnergyFraction F T *
          Real.exp (F.period T (F.distinguished T) / 2) *
            (Z.NIprime T : ℝ) := hfullNorm
    _ ≤ (1 + μ) * T ^ (μ / 2 : ℝ) *
        (2 * (Z.N T (2 * T) : ℝ)) := by
      gcongr
      linarith
    _ = 2 * (1 + μ) * T ^ (μ / 2 : ℝ) *
        (Z.N T (2 * T) : ℝ) := by ring

theorem norm_balancedGuarded_le_full_add_remote
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    ‖balancedGuardedLatticeZeroMatrix F T‖ ≤
      ‖balancedFullLatticeZeroMatrix F T‖ +
        ‖balancedRemoteLatticeZeroMatrix F T‖ := by
  have heq : balancedGuardedLatticeZeroMatrix F T =
      balancedFullLatticeZeroMatrix F T -
        balancedRemoteLatticeZeroMatrix F T := by
    have h := balancedGuarded_add_remote_eq_full F T
    exact eq_sub_of_add_eq h
  rw [heq]
  exact norm_sub_le _ _

theorem remoteCorrection_abs_le_four_mul
    {Z : ZeroConfig} {σ μ p r B : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T)
    (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hremote : ‖balancedRemoteLatticeZeroMatrix F T‖ ≤ r)
    (hfull : ‖balancedFullLatticeZeroMatrix F T‖ ≤ B)
    (hguarded : ‖balancedGuardedLatticeZeroMatrix F T‖ ≤ B) :
    |remoteCorrectionCyclicTrace4 F T| ≤ 4 * r * B ^ 3 := by
  have h := remoteCorrection_abs_le_balanced_frobenius F T hhat
  have h1 : ‖balancedRemoteLatticeZeroMatrix F T‖ *
      ‖balancedFullLatticeZeroMatrix F T‖ ^ 3 ≤ r * B ^ 3 := by
    gcongr
  have h2 : (‖balancedGuardedLatticeZeroMatrix F T‖ *
      ‖balancedRemoteLatticeZeroMatrix F T‖) *
      ‖balancedFullLatticeZeroMatrix F T‖ ^ 2 ≤ r * B ^ 3 := by
    calc
      (‖balancedGuardedLatticeZeroMatrix F T‖ *
          ‖balancedRemoteLatticeZeroMatrix F T‖) *
          ‖balancedFullLatticeZeroMatrix F T‖ ^ 2 ≤
        (B * r) * B ^ 2 := by gcongr
      _ = r * B ^ 3 := by ring
  have h3 : (‖balancedGuardedLatticeZeroMatrix F T‖ ^ 2 *
      ‖balancedRemoteLatticeZeroMatrix F T‖) *
      ‖balancedFullLatticeZeroMatrix F T‖ ≤ r * B ^ 3 := by
    calc
      (‖balancedGuardedLatticeZeroMatrix F T‖ ^ 2 *
          ‖balancedRemoteLatticeZeroMatrix F T‖) *
          ‖balancedFullLatticeZeroMatrix F T‖ ≤
        (B ^ 2 * r) * B := by gcongr
      _ = r * B ^ 3 := by ring
  have h4 : ‖balancedGuardedLatticeZeroMatrix F T‖ ^ 3 *
      ‖balancedRemoteLatticeZeroMatrix F T‖ ≤ r * B ^ 3 := by
    calc
      ‖balancedGuardedLatticeZeroMatrix F T‖ ^ 3 *
          ‖balancedRemoteLatticeZeroMatrix F T‖ ≤ B ^ 3 * r := by gcongr
      _ = r * B ^ 3 := by ring
  calc
    |remoteCorrectionCyclicTrace4 F T| ≤
      ‖balancedRemoteLatticeZeroMatrix F T‖ *
          ‖balancedFullLatticeZeroMatrix F T‖ ^ 3 +
        (‖balancedGuardedLatticeZeroMatrix F T‖ *
          ‖balancedRemoteLatticeZeroMatrix F T‖) *
          ‖balancedFullLatticeZeroMatrix F T‖ ^ 2 +
        (‖balancedGuardedLatticeZeroMatrix F T‖ ^ 2 *
          ‖balancedRemoteLatticeZeroMatrix F T‖) *
          ‖balancedFullLatticeZeroMatrix F T‖ +
        ‖balancedGuardedLatticeZeroMatrix F T‖ ^ 3 *
          ‖balancedRemoteLatticeZeroMatrix F T‖ := h
    _ ≤ r * B ^ 3 + r * B ^ 3 + r * B ^ 3 + r * B ^ 3 :=
      add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = 4 * r * B ^ 3 := by ring

theorem remoteCorrection_div_core_tendsto_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hprincipal : PrincipalCyclicBlock F)
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hRvM : RiemannVonMangoldt Z) (w c : ℝ)
    (hadm : ∀ᶠ T in atTop,
      AdmWindow (F.window T (F.distinguished T))
        (F.period T (F.distinguished T)) w c)
    (hhat : ∀ᶠ T in atTop, 1 ≤ F.hatDenominator T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T => remoteCorrectionCyclicTrace4 F T /
      (Z.N T (2 * T) : ℝ)) atTop (nhds 0) := by
  let A : ℝ := 2 * (1 + μ)
  let C : ℝ := A + 2
  have hguard :=
    PoissonKernelBridge.PrincipalCyclicBlock.toDistinguishedGuardedPoissonKernelData
      hprincipal
  have hhatPos : ∀ᶠ T in atTop, 0 < F.hatDenominator T :=
    hhat.mono fun T hT => lt_of_lt_of_le zero_lt_one hT
  have hremote := eventually_balancedRemote_norm_le_twelve
    htail hguard hhatPos
  have hfull := eventually_balancedFull_norm_le_completedGrowth
    hprincipal hRvM w c hadm hhat
  have hscaleLim := remoteLatticePairScaleTwelve_tendsto_zero
    F hprincipal.support_pos.le hprincipal.bandwidth_pos
      htail.bandwidth_lt_one hRvM hprincipal.distinguished_period hmass
  have hscaleOne : ∀ᶠ T in atTop,
      remoteLatticePairScaleTwelve F T < 1 :=
    hscaleLim.eventually (Iio_mem_nhds zero_lt_one)
  have hmain :=
    remoteLatticePairScaleTwelve_completedGrowth_negligible
      F hprincipal.support_pos.le hprincipal.bandwidth_pos
        htail.bandwidth_lt_one hRvM hprincipal.distinguished_period hmass
  have hconst : Tendsto (fun _ : ℝ => 8 * C ^ 3) atTop
      (nhds (8 * C ^ 3)) := tendsto_const_nhds
  have hupperLim : Tendsto (fun T =>
      (8 * C ^ 3) *
        (((Z.N T (2 * T) : ℝ) ^ 3 * remoteLatticePairScaleTwelve F T) *
          T ^ (3 * μ / 2 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hconst.mul hmain
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hupperLim
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hprincipal.distinguished_period, hhat, hremote, hfull, hscaleOne,
    Zeta23.Assembly.eventually_l_pos,
    eventually_NIprime_le_two_core hRvM,
    (Zeta23.Assembly.tendsto_N_atTop Z hRvM).eventually_gt_atTop 0]
      with T hT hperiodT hhatT hremoteT hfullT hscaleOneT hl hNI hNpos
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hL : 0 < F.period T (F.distinguished T) := by
    rw [hperiodT]
    exact mul_pos hprincipal.bandwidth_pos hl
  have hscale0 : 0 ≤ remoteLatticePairScaleTwelve F T :=
    remoteLatticePairScaleTwelve_nonneg F T hT0 hL
  have hN0 : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hquot : (Z.NIprime T : ℝ) / F.hatDenominator T ≤
      (Z.NIprime T : ℝ) := div_le_self (Nat.cast_nonneg _) hhatT
  have hremoteSharp : ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
      2 * remoteLatticePairScaleTwelve F T *
        (Z.N T (2 * T) : ℝ) := by
    calc
      ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
          remoteLatticePairScaleTwelve F T *
            ((Z.NIprime T : ℝ) / F.hatDenominator T) := hremoteT
      _ ≤ remoteLatticePairScaleTwelve F T * (Z.NIprime T : ℝ) := by
        gcongr
      _ ≤ remoteLatticePairScaleTwelve F T *
          (2 * (Z.N T (2 * T) : ℝ)) := by gcongr
      _ = 2 * remoteLatticePairScaleTwelve F T *
          (Z.N T (2 * T) : ℝ) := by ring
  let g : ℝ := T ^ (μ / 2 : ℝ)
  have hg0 : 0 ≤ g := by
    dsimp only [g]
    exact Real.rpow_nonneg hT0.le _
  have hg1 : 1 ≤ g := by
    dsimp only [g]
    exact Real.one_le_rpow hT.le
      (div_nonneg hprincipal.bandwidth_pos.le (by norm_num))
  have hremoteCoarse : ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
      2 * g * (Z.N T (2 * T) : ℝ) := by
    apply hremoteSharp.trans
    gcongr
    exact hscaleOneT.le.trans hg1
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    linarith [hprincipal.bandwidth_pos]
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    linarith
  have hAC : A ≤ C := by
    dsimp only [C]
    linarith
  have hfullB : ‖balancedFullLatticeZeroMatrix F T‖ ≤
      C * g * (Z.N T (2 * T) : ℝ) := by
    calc
      ‖balancedFullLatticeZeroMatrix F T‖ ≤
          A * g * (Z.N T (2 * T) : ℝ) := hfullT
      _ ≤ C * g * (Z.N T (2 * T) : ℝ) := by gcongr
  have hguardB : ‖balancedGuardedLatticeZeroMatrix F T‖ ≤
      C * g * (Z.N T (2 * T) : ℝ) := by
    calc
      ‖balancedGuardedLatticeZeroMatrix F T‖ ≤
          ‖balancedFullLatticeZeroMatrix F T‖ +
            ‖balancedRemoteLatticeZeroMatrix F T‖ :=
        norm_balancedGuarded_le_full_add_remote F T
      _ ≤ A * g * (Z.N T (2 * T) : ℝ) +
          2 * g * (Z.N T (2 * T) : ℝ) := add_le_add hfullT hremoteCoarse
      _ = C * g * (Z.N T (2 * T) : ℝ) := by
        dsimp only [C]
        ring
  have hcorr := remoteCorrection_abs_le_four_mul
    F T (lt_of_lt_of_le zero_lt_one hhatT)
      (mul_nonneg (mul_nonneg (by norm_num) hscale0) hN0)
      (mul_nonneg (mul_nonneg hC0 hg0) hN0)
      hremoteSharp hfullB hguardB
  have hg3 : g ^ 3 = T ^ (3 * μ / 2 : ℝ) := by
    dsimp only [g]
    calc
      (T ^ (μ / 2 : ℝ)) ^ (3 : ℕ) =
          (T ^ (μ / 2 : ℝ)) ^ (3 : ℝ) :=
        (Real.rpow_natCast (T ^ (μ / 2 : ℝ)) 3).symm
      _ = T ^ ((μ / 2 : ℝ) * 3) :=
        (Real.rpow_mul hT0.le (μ / 2 : ℝ) 3).symm
      _ = T ^ (3 * μ / 2 : ℝ) := by congr 1 <;> ring
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hNpos]
  calc
    |remoteCorrectionCyclicTrace4 F T| / (Z.N T (2 * T) : ℝ) ≤
        (4 * (2 * remoteLatticePairScaleTwelve F T *
          (Z.N T (2 * T) : ℝ)) *
          (C * g * (Z.N T (2 * T) : ℝ)) ^ 3) /
            (Z.N T (2 * T) : ℝ) :=
      div_le_div_of_nonneg_right hcorr hN0
    _ = (8 * C ^ 3) *
        (((Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T) *
            T ^ (3 * μ / 2 : ℝ)) := by
      rw [← hg3]
      field_simp [hNpos.ne']
      ring

/-- The completed and guarded fourth traces therefore have the same
dyadic-count-normalized limit. -/
theorem full_sub_guarded_trace4_div_core_tendsto_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hprincipal : PrincipalCyclicBlock F)
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hRvM : RiemannVonMangoldt Z) (w c : ℝ)
    (hadm : ∀ᶠ T in atTop,
      AdmWindow (F.window T (F.distinguished T))
        (F.period T (F.distinguished T)) w c)
    (hhat : ∀ᶠ T in atTop, 1 ≤ F.hatDenominator T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T =>
      (fullLatticeZeroKernelCyclicTrace4 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace4 F T) /
          (Z.N T (2 * T) : ℝ)) atTop (nhds 0) := by
  have hcorr := remoteCorrection_div_core_tendsto_zero
    hprincipal htail hRvM w c hadm hhat hmass
  apply hcorr.congr'
  filter_upwards [] with T
  have htrace := guardedCyclicTrace4_add_remoteCorrection_eq_full F T
  rw [← htrace]
  ring

theorem full_div_core_sub_guarded_div_core_tendsto_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hprincipal : PrincipalCyclicBlock F)
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hRvM : RiemannVonMangoldt Z) (w c : ℝ)
    (hadm : ∀ᶠ T in atTop,
      AdmWindow (F.window T (F.distinguished T))
        (F.period T (F.distinguished T)) w c)
    (hhat : ∀ᶠ T in atTop, 1 ≤ F.hatDenominator T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T =>
      fullLatticeZeroKernelCyclicTrace4 F T / (Z.N T (2 * T) : ℝ) -
        QuarticTransfer.guardedZeroKernelCyclicTrace4 F T /
          (Z.N T (2 * T) : ℝ)) atTop (nhds 0) := by
  simpa only [sub_div] using
    full_sub_guarded_trace4_div_core_tendsto_zero
      hprincipal htail hRvM w c hadm hhat hmass

end RH.Zeta85.RSPoissonCyclicBridge
