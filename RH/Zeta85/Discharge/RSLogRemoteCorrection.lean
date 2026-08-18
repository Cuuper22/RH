import RH.Zeta85.Discharge.RSFullTraceGauge

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

structure DistinguishedLogGuardedPoissonKernelData
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) : Prop
    extends RH.Zeta85.PoissonKernelBridge.DistinguishedPoissonKernelData F where
  bandwidth_pos : 0 < mu
  distinguished_period_log : ∀ᶠ T in atTop,
    F.period T (F.distinguished T) = mu * Real.log T
  distinguished_grid_count : ∀ᶠ T in atTop,
    F.channelDim T (F.distinguished T) =
      ⌊F.period T (F.distinguished T) * T / (2 * Real.pi)⌋₊

theorem distinguishedWindowFourierMajorantTwelve_le_log
    {Z : ZeroConfig} {sigma mu p c T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hmu : 0 ≤ mu) (hT : 1 < T)
    (hperiod : F.period T (F.distinguished T) = mu * Real.log T)
    (hmass : distinguishedWindowSobolevMassSix F T ≤ c * Zeta23.l T) :
    distinguishedWindowFourierMajorantTwelve F T ≤
      c ^ 2 * T ^ (mu / 2 : ℝ) * Zeta23.l T ^ 2 := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hexp :
      (Real.exp ((1 / 2 : ℝ) *
        (F.period T (F.distinguished T) / 2))) ^ 2 =
        T ^ (mu / 2 : ℝ) := by
    rw [pow_two, ← Real.exp_add, hperiod, Real.rpow_def_of_pos hT0]
    congr 1
    ring
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
    _ ≤ T ^ (mu / 2 : ℝ) * (c * Zeta23.l T) ^ 2 := by
      rw [hexp]
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hmass0 hcl0).2 hmass) (by positivity)
    _ = c ^ 2 * T ^ (mu / 2 : ℝ) * Zeta23.l T ^ 2 := by ring

theorem distinguishedRemoteTailGridFactorTwelve_le_log
    {Z : ZeroConfig} {sigma mu p T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hmu : 0 < mu) (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (hperiod : F.period T (F.distinguished T) = mu * Real.log T) :
    (Zeta23.D0 T ^ 8)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (1 + mu) * Real.log T * (Zeta23.D0 T ^ 11)⁻¹ := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT0
  have hD1 : 1 ≤ Zeta23.D0 T := by
    simpa only [Zeta23.D0, Real.sqrt_one] using Real.sqrt_le_sqrt hT
  have hpow : Zeta23.D0 T ^ 3 ≤ Zeta23.D0 T ^ 4 := by
    nlinarith [pow_pos hD 3]
  have hinv : (Zeta23.D0 T ^ 4)⁻¹ ≤ (Zeta23.D0 T ^ 3)⁻¹ :=
    (inv_le_inv₀ (pow_pos hD 4) (pow_pos hD 3)).2 hpow
  have hmul : 0 < mu * Real.log T :=
    mul_pos hmu (lt_of_lt_of_le zero_lt_one hlog)
  have hgridInv :
      (3 * PoissonKernelBridge.distinguishedGridStep F T)⁻¹ ≤
        mu * Real.log T := by
    have heq :
        (3 * PoissonKernelBridge.distinguishedGridStep F T)⁻¹ =
          mu * Real.log T / (6 * Real.pi) := by
      unfold PoissonKernelBridge.distinguishedGridStep
      rw [hperiod]
      field_simp
      ring
    rw [heq, div_le_iff₀ (by positivity : (0 : ℝ) < 6 * Real.pi)]
    have hpi : 1 ≤ 6 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_nonneg hmul.le (by linarith : 0 ≤ 6 * Real.pi - 1)]
  have hinv3 : 0 ≤ (Zeta23.D0 T ^ 3)⁻¹ :=
    inv_nonneg.mpr (pow_pos hD 3).le
  calc
    (Zeta23.D0 T ^ 8)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (Zeta23.D0 T ^ 8)⁻¹ *
        ((Zeta23.D0 T ^ 3)⁻¹ +
          (Zeta23.D0 T ^ 3)⁻¹ * (mu * Real.log T)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_eq_mul_inv]
      exact add_le_add hinv (mul_le_mul_of_nonneg_left hgridInv hinv3)
    _ = (1 + mu * Real.log T) * (Zeta23.D0 T ^ 11)⁻¹ := by
      field_simp [hD.ne']
    _ ≤ (1 + mu) * Real.log T * (Zeta23.D0 T ^ 11)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith

theorem N_cube_mul_distinguishedRemoteTailScaleTwelve_le_log
    {Z : ZeroConfig} {sigma mu p c T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hmu : 0 < mu) (hT : 1 < T) (hl : 1 ≤ Zeta23.l T)
    (hperiod : F.period T (F.distinguished T) = mu * Real.log T)
    (hN : (Z.N T (2 * T) : ℝ) ≤ T * Zeta23.l T)
    (hMaj : distinguishedWindowFourierMajorantTwelve F T ≤
      c ^ 2 * T ^ (mu / 2 : ℝ) * Zeta23.l T ^ 2)
    (hTail : (Zeta23.D0 T ^ 8)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (1 + mu) * Real.log T * (Zeta23.D0 T ^ 11)⁻¹) :
    (Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T ≤
      c ^ 2 * (1 + mu) * T ^ (mu / 2 - 5 / 2 : ℝ) *
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
    exact div_pos (by positivity) (mul_pos hmu (Real.log_pos hT))
  have htail0 : 0 ≤ (Zeta23.D0 T ^ 8)⁻¹ *
      ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
        (3 * PoissonKernelBridge.distinguishedGridStep F T)) := by positivity
  have hmaj0 : 0 ≤ distinguishedWindowFourierMajorantTwelve F T := by
    unfold distinguishedWindowFourierMajorantTwelve
    positivity
  have hrightMaj0 :
      0 ≤ c ^ 2 * T ^ (mu / 2 : ℝ) * Zeta23.l T ^ 2 := by positivity
  have hNpow : (Z.N T (2 * T) : ℝ) ^ 3 ≤
      (T * Zeta23.l T) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hN 3
  have hraw :
      (Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T ≤
        (T * Zeta23.l T) ^ 3 *
          ((c ^ 2 * T ^ (mu / 2 : ℝ) * Zeta23.l T ^ 2) *
            ((1 + mu) * Real.log T * (Zeta23.D0 T ^ 11)⁻¹)) := by
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
          ((c ^ 2 * T ^ (mu / 2 : ℝ) * Zeta23.l T ^ 2) *
            ((Zeta23.D0 T ^ 8)⁻¹ *
              ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
                (3 * PoissonKernelBridge.distinguishedGridStep F T)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hMaj htail0) (by positivity)
      _ ≤ (T * Zeta23.l T) ^ 3 *
          ((c ^ 2 * T ^ (mu / 2 : ℝ) * Zeta23.l T ^ 2) *
            ((1 + mu) * Real.log T * (Zeta23.D0 T ^ 11)⁻¹)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hTail hrightMaj0) (by positivity)
  have hDsquare : Zeta23.D0 T ^ 2 = T := Real.sq_sqrt hT0.le
  have hD11 : Zeta23.D0 T ^ 11 = Zeta23.D0 T * T ^ 5 := by
    calc
      Zeta23.D0 T ^ 11 = Zeta23.D0 T * (Zeta23.D0 T ^ 2) ^ 5 := by ring
      _ = Zeta23.D0 T * T ^ 5 := by rw [hDsquare]
  have hpower :
      T ^ 3 * T ^ (mu / 2 : ℝ) * (Zeta23.D0 T ^ 11)⁻¹ =
        T ^ (mu / 2 - 5 / 2 : ℝ) := by
    rw [hD11]
    have hcancel :
        T ^ 3 * T ^ (mu / 2 : ℝ) * (Zeta23.D0 T * T ^ 5)⁻¹ =
          T ^ (mu / 2 : ℝ) / (Zeta23.D0 T * T ^ 2) := by
      field_simp
    rw [hcancel, Zeta23.D0, Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast T 2, ← Real.rpow_add hT0]
    rw [← Real.rpow_sub hT0]
    congr 1
    ring
  calc
    (Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T ≤ _ :=
      hraw
    _ = c ^ 2 * (1 + mu) *
          (T ^ 3 * T ^ (mu / 2 : ℝ) * (Zeta23.D0 T ^ 11)⁻¹) *
            (Zeta23.l T ^ 5 * Real.log T) := by ring
    _ = c ^ 2 * (1 + mu) * T ^ (mu / 2 - 5 / 2 : ℝ) *
          (Zeta23.l T ^ 5 * Real.log T) := by rw [hpower]
    _ ≤ c ^ 2 * (1 + mu) * T ^ (mu / 2 - 5 / 2 : ℝ) *
          Real.log T ^ 6 := by
      apply mul_le_mul_of_nonneg_left
      · calc
          Zeta23.l T ^ 5 * Real.log T ≤
              Real.log T ^ 5 * Real.log T := by gcongr
          _ = Real.log T ^ 6 := by ring
      · positivity

theorem N_cube_tailTwelve_mul_completedGrowth_le_log
    {Z : ZeroConfig} {sigma mu p c T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hmu : 0 < mu) (hT : 1 < T) (hl : 1 ≤ Zeta23.l T)
    (hperiod : F.period T (F.distinguished T) = mu * Real.log T)
    (hN : (Z.N T (2 * T) : ℝ) ≤ T * Zeta23.l T)
    (hMaj : distinguishedWindowFourierMajorantTwelve F T ≤
      c ^ 2 * T ^ (mu / 2 : ℝ) * Zeta23.l T ^ 2)
    (hTail : (Zeta23.D0 T ^ 8)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (1 + mu) * Real.log T * (Zeta23.D0 T ^ 11)⁻¹) :
    ((Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T) *
        T ^ (3 * mu / 2 : ℝ) ≤
      c ^ 2 * (1 + mu) * T ^ (2 * mu - 5 / 2 : ℝ) *
        Real.log T ^ 6 := by
  have hbase := N_cube_mul_distinguishedRemoteTailScaleTwelve_le_log
    F hmu hT hl hperiod hN hMaj hTail
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  calc
    ((Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T) *
        T ^ (3 * mu / 2 : ℝ) ≤
      (c ^ 2 * (1 + mu) * T ^ (mu / 2 - 5 / 2 : ℝ) *
        Real.log T ^ 6) * T ^ (3 * mu / 2 : ℝ) := by gcongr
    _ = c ^ 2 * (1 + mu) * T ^ (2 * mu - 5 / 2 : ℝ) *
        Real.log T ^ 6 := by
      rw [show T ^ (2 * mu - 5 / 2 : ℝ) =
        T ^ (mu / 2 - 5 / 2 : ℝ) * T ^ (3 * mu / 2 : ℝ) by
          rw [← Real.rpow_add hT0]
          congr 1
          ring]
      ring

theorem tendsto_N_cube_tailTwelve_mul_completedGrowth_log
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hmu : 0 < mu) (hmu1 : mu < 1) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = mu * Real.log T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T =>
      ((Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleTwelve F T) *
        T ^ (3 * mu / 2 : ℝ)) atTop (nhds 0) := by
  obtain ⟨c, hc⟩ := hmass.bound
  have hlim : Tendsto (fun T =>
      c ^ 2 * (1 + mu) *
        (T ^ (2 * mu - 5 / 2 : ℝ) * Real.log T ^ 6))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => c ^ 2 * (1 + mu)) atTop
        (nhds (c ^ 2 * (1 + mu))) := tendsto_const_nhds
    simpa only [mul_zero] using hconst.mul
      (tendsto_rpow_two_mu_sub_five_halves_mul_log_pow_six hmu1)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hperiod, Zeta23.Assembly.eventually_one_le_l,
      eventually_gt_atTop (1 : ℝ)] with T hperiodT hl hT
    have hgrid : 0 < PoissonKernelBridge.distinguishedGridStep F T := by
      unfold PoissonKernelBridge.distinguishedGridStep
      rw [hperiodT]
      exact div_pos (by positivity) (mul_pos hmu (Real.log_pos hT))
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
    have hMaj := distinguishedWindowFourierMajorantTwelve_le_log
      F hmu.le hT hperiodT hmassPoint
    have hT0 : 0 < T := lt_trans zero_lt_one hT
    have hlogconst : 0 ≤ Real.log (2 * Real.pi) := by
      apply Real.log_nonneg
      nlinarith [Real.pi_gt_three]
    have hlLog : Zeta23.l T ≤ Real.log T := by
      rw [Zeta23.Assembly.log_eq_l_add hT0]
      linarith
    have hTail := distinguishedRemoteTailGridFactorTwelve_le_log
      F hmu hT.le (hl.trans hlLog) hperiodT
    simpa only [mul_assoc] using
      N_cube_tailTwelve_mul_completedGrowth_le_log
        F hmu hT hl hperiodT hN hMaj hTail

theorem norm_distinguishedLatticeScale_eq_log_ratio
    {Z : ZeroConfig} {sigma mu p T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hsigma : 0 ≤ sigma) (hmu : 0 < mu)
    (hl : 0 < Zeta23.l T) (hlog : 0 < Real.log T)
    (hperiod : F.period T (F.distinguished T) = mu * Real.log T) :
    ‖PoissonKernelBridge.distinguishedLatticeScale F T‖ =
      sigma * Zeta23.l T / (mu * Real.log T) := by
  have hratio : QuarticGramFamily.fullLength (σ := sigma) T /
      F.period T (F.distinguished T) =
        sigma * Zeta23.l T / (mu * Real.log T) := by
    unfold QuarticGramFamily.fullLength
    rw [hperiod]
  have hnonneg : 0 ≤ sigma * Zeta23.l T / (mu * Real.log T) :=
    div_nonneg (mul_nonneg hsigma hl.le) (mul_nonneg hmu.le hlog.le)
  unfold PoissonKernelBridge.distinguishedLatticeScale
  rw [hratio, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]

theorem norm_distinguishedLatticeScale_le_log
    {Z : ZeroConfig} {sigma mu p T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hsigma : 0 ≤ sigma) (hmu : 0 < mu)
    (hl : 0 < Zeta23.l T) (hlog : 0 < Real.log T)
    (hlLog : Zeta23.l T ≤ Real.log T)
    (hperiod : F.period T (F.distinguished T) = mu * Real.log T) :
    ‖PoissonKernelBridge.distinguishedLatticeScale F T‖ ≤ sigma / mu := by
  rw [norm_distinguishedLatticeScale_eq_log_ratio
    F hsigma hmu hl hlog hperiod]
  have hratio : Zeta23.l T / Real.log T ≤ 1 :=
    (div_le_one hlog).2 hlLog
  calc
    sigma * Zeta23.l T / (mu * Real.log T) =
        (sigma / mu) * (Zeta23.l T / Real.log T) := by
      field_simp [hmu.ne', hlog.ne']
    _ ≤ (sigma / mu) * 1 := by
      exact mul_le_mul_of_nonneg_left hratio (div_nonneg hsigma hmu.le)
    _ = sigma / mu := by ring

theorem remoteLatticePairScaleTwelve_completedGrowth_negligible_log
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hsigma : 0 ≤ sigma)
    (hmu : 0 < mu) (hmu1 : mu < 1) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = mu * Real.log T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T =>
      ((Z.N T (2 * T) : ℝ) ^ 3 * remoteLatticePairScaleTwelve F T) *
        T ^ (3 * mu / 2 : ℝ)) atTop (nhds 0) := by
  have htail := tendsto_N_cube_tailTwelve_mul_completedGrowth_log
    F hmu hmu1 hRvM hperiod hmass
  have hconst : Tendsto (fun _ : ℝ => 2 * (sigma / mu)) atTop
      (nhds (2 * (sigma / mu))) := tendsto_const_nhds
  have hupper : Tendsto (fun T =>
      (2 * (sigma / mu)) *
        (((Z.N T (2 * T) : ℝ) ^ 3 *
          distinguishedRemoteTailScaleTwelve F T) *
            T ^ (3 * mu / 2 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hconst.mul htail
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hperiod] with T hT hperiodT
    have hT0 : 0 < T := lt_trans zero_lt_one hT
    have hL : 0 < F.period T (F.distinguished T) := by
      rw [hperiodT]
      exact mul_pos hmu (Real.log_pos hT)
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3)
        (remoteLatticePairScaleTwelve_nonneg F T hT0 hL))
      (Real.rpow_nonneg hT0.le _)
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hperiod,
      Zeta23.Assembly.eventually_l_pos] with T hT hperiodT hl
    have hT0 : 0 < T := lt_trans zero_lt_one hT
    have hlog : 0 < Real.log T := Real.log_pos hT
    have hlogconst : 0 ≤ Real.log (2 * Real.pi) := by
      apply Real.log_nonneg
      nlinarith [Real.pi_gt_three]
    have hlLog : Zeta23.l T ≤ Real.log T := by
      rw [Zeta23.Assembly.log_eq_l_add hT0]
      linarith
    have hscale := norm_distinguishedLatticeScale_le_log
      F hsigma hmu hl hlog hlLog hperiodT
    have htail0 : 0 ≤ distinguishedRemoteTailScaleTwelve F T := by
      unfold distinguishedRemoteTailScaleTwelve
        PoissonKernelBridge.distinguishedGridStep
        distinguishedWindowFourierMajorantTwelve
      have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT0
      have hL : 0 < F.period T (F.distinguished T) := by
        rw [hperiodT]
        exact mul_pos hmu hlog
      positivity
    unfold remoteLatticePairScaleTwelve
    have hN3 : 0 ≤ (Z.N T (2 * T) : ℝ) ^ 3 := by positivity
    have hg : 0 ≤ T ^ (3 * mu / 2 : ℝ) := Real.rpow_nonneg hT0.le _
    calc
      ((Z.N T (2 * T) : ℝ) ^ 3 *
          (‖PoissonKernelBridge.distinguishedLatticeScale F T‖ *
            (distinguishedRemoteTailScaleTwelve F T +
              distinguishedRemoteTailScaleTwelve F T))) *
            T ^ (3 * mu / 2 : ℝ) ≤
        ((Z.N T (2 * T) : ℝ) ^ 3 *
          ((sigma / mu) *
            (distinguishedRemoteTailScaleTwelve F T +
              distinguishedRemoteTailScaleTwelve F T))) *
            T ^ (3 * mu / 2 : ℝ) := by gcongr
      _ = (2 * (sigma / mu)) *
          (((Z.N T (2 * T) : ℝ) ^ 3 *
            distinguishedRemoteTailScaleTwelve F T) *
              T ^ (3 * mu / 2 : ℝ)) := by ring

theorem remoteLatticePairScaleTwelve_tendsto_zero_log
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v)
    (hsigma : 0 ≤ sigma)
    (hmu : 0 < mu) (hmu1 : mu < 1) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = mu * Real.log T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T => remoteLatticePairScaleTwelve F T) atTop (nhds 0) := by
  have hprod :=
    remoteLatticePairScaleTwelve_completedGrowth_negligible_log
      F hsigma hmu hmu1 hRvM hperiod hmass
  refine squeeze_zero' ?_ ?_ hprod
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hperiod] with T hT hperiodT
    have hT0 : 0 < T := lt_trans zero_lt_one hT
    exact remoteLatticePairScaleTwelve_nonneg F T hT0 (by
      rw [hperiodT]
      exact mul_pos hmu (Real.log_pos hT))
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hperiod,
      (Zeta23.Assembly.tendsto_N_atTop Z hRvM).eventually_ge_atTop 1]
      with T hT hperiodT hN
    have hT0 : 0 < T := lt_trans zero_lt_one hT
    have hscale : 0 ≤ remoteLatticePairScaleTwelve F T :=
      remoteLatticePairScaleTwelve_nonneg F T hT0 (by
        rw [hperiodT]
        exact mul_pos hmu (Real.log_pos hT))
    have hN3 : 1 ≤ (Z.N T (2 * T) : ℝ) ^ 3 := by
      nlinarith [pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hN 3]
    have hgrowth : 1 ≤ T ^ (3 * mu / 2 : ℝ) :=
      Real.one_le_rpow hT.le (by positivity)
    calc
      remoteLatticePairScaleTwelve F T =
          1 * remoteLatticePairScaleTwelve F T := by ring
      _ ≤ (Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T := by gcongr
      _ = ((Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T) * 1 := by ring
      _ ≤ ((Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T) *
            T ^ (3 * mu / 2 : ℝ) := by gcongr

theorem eventually_remotePair_le_scale_twelve_log
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z sigma mu p v}
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : DistinguishedLogGuardedPoissonKernelData F) :
    ∀ᶠ T in atTop, ∀ rho rho' : ↥(ZeroSide.ZI Z T),
      ‖remoteLatticePairKernel F T (rho : ℂ) (rho' : ℂ)‖ ≤
        remoteLatticePairScaleTwelve F T := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hguard.periods_pos,
    hguard.windows_smooth, hguard.distinguished_grid_count,
    htail.distinguished_support_half]
      with T hT hperiod hsmooth hcount hsupport
  intro rho rho'
  have hwindow : ContDiff ℝ 6
      (fun u => (F.window T (F.distinguished T) u : ℂ)) := by
    change ContDiff ℝ 6
      (Complex.ofRealCLM ∘ F.window T (F.distinguished T))
    exact (Complex.ofRealCLM.contDiff.comp
      (hsmooth (F.distinguished T))).of_le (by
        exact (WithTop.coe_le_coe).2 (show (6 : ℕ∞) ≤ ⊤ from le_top))
  have hsupp : ∀ u,
      (F.window T (F.distinguished T) u : ℂ) ≠ 0 →
        |u| ≤ F.period T (F.distinguished T) / 2 := by
    intro u hu
    apply hsupport u
    simpa only [Complex.ofReal_ne_zero] using hu
  exact remoteLatticePairKernel_norm_le_twelve
    F T hT (hperiod (F.distinguished T)) hcount hwindow hsupp rho rho'

theorem eventually_balancedRemote_norm_le_twelve_log
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z sigma mu p v}
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : DistinguishedLogGuardedPoissonKernelData F)
    (hhat : ∀ᶠ T in atTop, 0 < F.hatDenominator T) :
    ∀ᶠ T in atTop,
      ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
        remoteLatticePairScaleTwelve F T *
          ((Z.NIprime T : ℝ) / F.hatDenominator T) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hguard.periods_pos,
    eventually_remotePair_le_scale_twelve_log htail hguard, hhat]
      with T hT hperiod hpair hhatT
  have h := norm_balancedKernelMatrix_le
    (fun rho rho' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (rho : ℂ) (rho' : ℂ))
    (fun rho : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (rho : ℂ) : ℂ))
    (remoteLatticePairScaleTwelve_nonneg F T hT
      (hperiod (F.distinguished T))) hpair
  change ‖balancedKernelMatrix
    (fun rho rho' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (rho : ℂ) (rho' : ℂ))
    (fun rho : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (rho : ℂ) : ℂ))‖ ≤ _
  rw [sum_zeroVertexWeight_norm_sq F T hhatT] at h
  exact h

theorem eventually_balancedFull_norm_le_completedGrowth_log
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z sigma mu p v}
    (hdata : CompletedTraceKernelData F)
    (hguard : DistinguishedLogGuardedPoissonKernelData F)
    (hRvM : RiemannVonMangoldt Z) (w c : ℝ)
    (hadm : ∀ᶠ T in atTop,
      AdmWindow (F.window T (F.distinguished T))
        (F.period T (F.distinguished T)) w c)
    (hhat : ∀ᶠ T in atTop, 1 ≤ F.hatDenominator T) :
    ∀ᶠ T in atTop,
      ‖balancedFullLatticeZeroMatrix F T‖ ≤
        2 * (1 + mu) * T ^ (mu / 2 : ℝ) *
          (Z.N T (2 * T) : ℝ) := by
  have hefrac : ∀ᶠ T in atTop,
      distinguishedEnergyFraction F T < mu + 1 :=
    hdata.distinguished_energy_ratio.eventually
      (Iio_mem_nhds (by linarith))
  filter_upwards [hadm, hhat, hefrac,
    hguard.distinguished_period_log,
    hdata.distinguished_channel_energy_pos,
    hdata.local_profile_integrable,
    hdata.local_profile_nonneg,
    hdata.local_profile_support,
    hdata.local_profile_mean_one,
    Zeta23.Assembly.eventually_l_pos,
    eventually_NIprime_le_two_core hRvM,
    eventually_gt_atTop (1 : ℝ)]
      with T hadmT hhatT hefracT hperiodT hE hprofileInt
        hprofileNonneg hprofileSupport hprofileMean hl hNI hT
  have hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T := by
    unfold QuarticGramFamily.fullLength
    exact mul_pos hdata.support_pos hl
  have htotal : 0 < ∫ u : ℝ, F.windowEnergy T u := by
    by_contra hnot
    have hnonpos : (∫ u : ℝ, F.windowEnergy T u) ≤ 0 := le_of_not_gt hnot
    have hprod : QuarticGramFamily.fullLength (σ := sigma) T *
        (∫ u : ℝ, F.windowEnergy T u) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfull.le hnonpos
    unfold QuarticGramFamily.hatDenominator at hhatT
    linarith
  have hfullNorm := norm_balancedFullLatticeZeroMatrix_le
    F T w c hadmT hfull hE htotal hprofileInt hprofileNonneg
      hprofileSupport hprofileMean
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hexp : Real.exp (F.period T (F.distinguished T) / 2) =
      T ^ (mu / 2 : ℝ) := by
    rw [hperiodT, Real.rpow_def_of_pos hT0]
    congr 1
    ring
  have hefrac0 : 0 ≤ distinguishedEnergyFraction F T := by
    unfold distinguishedEnergyFraction
    exact div_nonneg hE.le htotal.le
  have hN0 : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hmu1 : 0 ≤ 1 + mu := by linarith [hguard.bandwidth_pos]
  have hrpow0 : 0 ≤ T ^ (mu / 2 : ℝ) := Real.rpow_nonneg hT0.le _
  calc
    ‖balancedFullLatticeZeroMatrix F T‖ ≤
        distinguishedEnergyFraction F T *
          Real.exp (F.period T (F.distinguished T) / 2) *
            (Z.NIprime T : ℝ) := hfullNorm
    _ ≤ (1 + mu) * T ^ (mu / 2 : ℝ) *
        (2 * (Z.N T (2 * T) : ℝ)) := by
      rw [hexp]
      gcongr
      linarith
    _ = 2 * (1 + mu) * T ^ (mu / 2 : ℝ) *
        (Z.N T (2 * T) : ℝ) := by ring

theorem remoteCorrection_div_core_tendsto_zero_log
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z sigma mu p v}
    (hdata : CompletedTraceKernelData F)
    (hguard : DistinguishedLogGuardedPoissonKernelData F)
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
  let A : ℝ := 2 * (1 + mu)
  let C : ℝ := A + 2
  have hhatPos : ∀ᶠ T in atTop, 0 < F.hatDenominator T :=
    hhat.mono fun T hT => lt_of_lt_of_le zero_lt_one hT
  have hremote := eventually_balancedRemote_norm_le_twelve_log
    htail hguard hhatPos
  have hfull := eventually_balancedFull_norm_le_completedGrowth_log
    hdata hguard hRvM w c hadm hhat
  have hscaleLim := remoteLatticePairScaleTwelve_tendsto_zero_log
    F hdata.support_pos.le hguard.bandwidth_pos
      htail.bandwidth_lt_one hRvM hguard.distinguished_period_log hmass
  have hscaleOne : ∀ᶠ T in atTop,
      remoteLatticePairScaleTwelve F T < 1 :=
    hscaleLim.eventually (Iio_mem_nhds zero_lt_one)
  have hmain :=
    remoteLatticePairScaleTwelve_completedGrowth_negligible_log
      F hdata.support_pos.le hguard.bandwidth_pos
        htail.bandwidth_lt_one hRvM hguard.distinguished_period_log hmass
  have hconst : Tendsto (fun _ : ℝ => 8 * C ^ 3) atTop
      (nhds (8 * C ^ 3)) := tendsto_const_nhds
  have hupperLim : Tendsto (fun T =>
      (8 * C ^ 3) *
        (((Z.N T (2 * T) : ℝ) ^ 3 * remoteLatticePairScaleTwelve F T) *
          T ^ (3 * mu / 2 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hconst.mul hmain
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_
    hupperLim
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hguard.distinguished_period_log, hhat, hremote, hfull, hscaleOne,
    Zeta23.Assembly.eventually_l_pos,
    eventually_NIprime_le_two_core hRvM,
    (Zeta23.Assembly.tendsto_N_atTop Z hRvM).eventually_gt_atTop 0]
      with T hT hperiodT hhatT hremoteT hfullT hscaleOneT hl hNI hNpos
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hL : 0 < F.period T (F.distinguished T) := by
    rw [hperiodT]
    exact mul_pos hguard.bandwidth_pos (Real.log_pos hT)
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
  let g : ℝ := T ^ (mu / 2 : ℝ)
  have hg0 : 0 ≤ g := by
    dsimp only [g]
    exact Real.rpow_nonneg hT0.le _
  have hg1 : 1 ≤ g := by
    dsimp only [g]
    exact Real.one_le_rpow hT.le
      (div_nonneg hguard.bandwidth_pos.le (by norm_num))
  have hremoteCoarse : ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
      2 * g * (Z.N T (2 * T) : ℝ) := by
    apply hremoteSharp.trans
    gcongr
    exact hscaleOneT.le.trans hg1
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    linarith [hguard.bandwidth_pos]
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
          2 * g * (Z.N T (2 * T) : ℝ) :=
        add_le_add hfullT hremoteCoarse
      _ = C * g * (Z.N T (2 * T) : ℝ) := by
        dsimp only [C]
        ring
  have hcorr := remoteCorrection_abs_le_four_mul
    F T (lt_of_lt_of_le zero_lt_one hhatT)
      (mul_nonneg (mul_nonneg (by norm_num) hscale0) hN0)
      (mul_nonneg (mul_nonneg hC0 hg0) hN0)
      hremoteSharp hfullB hguardB
  have hg3 : g ^ 3 = T ^ (3 * mu / 2 : ℝ) := by
    dsimp only [g]
    calc
      (T ^ (mu / 2 : ℝ)) ^ (3 : ℕ) =
          (T ^ (mu / 2 : ℝ)) ^ (3 : ℝ) :=
        (Real.rpow_natCast (T ^ (mu / 2 : ℝ)) 3).symm
      _ = T ^ ((mu / 2 : ℝ) * 3) :=
        (Real.rpow_mul hT0.le (mu / 2 : ℝ) 3).symm
      _ = T ^ (3 * mu / 2 : ℝ) := by congr 1 <;> ring
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
            T ^ (3 * mu / 2 : ℝ)) := by
      rw [← hg3]
      field_simp [hNpos.ne']
      ring

theorem full_sub_guarded_trace4_div_core_tendsto_zero_log
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z sigma mu p v}
    (hdata : CompletedTraceKernelData F)
    (hguard : DistinguishedLogGuardedPoissonKernelData F)
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
  have hcorr := remoteCorrection_div_core_tendsto_zero_log
    hdata hguard htail hRvM w c hadm hhat hmass
  apply hcorr.congr'
  filter_upwards [] with T
  have htrace := guardedCyclicTrace4_add_remoteCorrection_eq_full F T
  rw [← htrace]
  ring

theorem full_div_core_sub_guarded_div_core_tendsto_zero_log
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z sigma mu p v}
    (hdata : CompletedTraceKernelData F)
    (hguard : DistinguishedLogGuardedPoissonKernelData F)
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
    full_sub_guarded_trace4_div_core_tendsto_zero_log
      hdata hguard htail hRvM w c hadm hhat hmass

/-- At the RS `log T` normalization, the finite gauge sum and the guarded
quartic trace differ only by the remote correction already proved to
vanish.  This is the direct handoff from Poisson completion to RS 3.1. -/
theorem finiteRSLogGauge_sub_guarded_div_core_tendsto_zero
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z sigma mu p v}
    (hdata : CompletedTraceKernelData F)
    (hguard : DistinguishedLogGuardedPoissonKernelData F)
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hRvM : RiemannVonMangoldt Z) (w c : ℝ)
    (hadm : ∀ᶠ T in atTop,
      AdmWindow (F.window T (F.distinguished T))
        (F.period T (F.distinguished T)) w c)
    (hhat : ∀ᶠ T in atTop, 1 ≤ F.hatDenominator T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T =>
      (distinguishedEnergyFraction F T ^ 4 * finiteRSLogGaugeTrace4 F T -
        mu ^ 4 * QuarticTransfer.guardedZeroKernelCyclicTrace4 F T) /
          (Z.N T (2 * T) : ℝ)) atTop (nhds 0) := by
  have hcorr := full_sub_guarded_trace4_div_core_tendsto_zero_log
    hdata hguard htail hRvM w c hadm hhat hmass
  have hconst : Tendsto (fun _ : ℝ => mu ^ 4) atTop (nhds (mu ^ 4)) :=
    tendsto_const_nhds
  have hscaled : Tendsto (fun T =>
      mu ^ 4 *
        ((fullLatticeZeroKernelCyclicTrace4 F T -
          QuarticTransfer.guardedZeroKernelCyclicTrace4 F T) /
            (Z.N T (2 * T) : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hconst.mul hcorr
  apply hscaled.congr'
  filter_upwards [hadm, hhat, hguard.distinguished_period_log,
    hdata.distinguished_channel_energy_pos,
    Zeta23.Assembly.eventually_l_pos]
      with T hadmT hhatT hperiodT hE hl
  have hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T := by
    unfold QuarticGramFamily.fullLength
    exact mul_pos hdata.support_pos hl
  have htotal : 0 < ∫ u : ℝ, F.windowEnergy T u := by
    by_contra hnot
    have hnonpos : (∫ u : ℝ, F.windowEnergy T u) ≤ 0 := le_of_not_gt hnot
    have hprod : QuarticGramFamily.fullLength (σ := sigma) T *
        (∫ u : ℝ, F.windowEnergy T u) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfull.le hnonpos
    unfold QuarticGramFamily.hatDenominator at hhatT
    linarith
  have hexact := fullLatticeTrace4_eq_finiteRSLogGauge
    F T w c hadmT hfull hE.ne' htotal.ne' hguard.bandwidth_pos hperiodT
  rw [← hexact]
  ring

end RH.Zeta85.RSPoissonCyclicBridge
