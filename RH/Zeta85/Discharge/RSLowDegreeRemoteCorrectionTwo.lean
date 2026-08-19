import RH.Zeta85.Discharge.RSLowDegreeRemoteCorrectionOne

/-!
# Degree-two completed/guarded remote correction

The quadratic trace telescope reduces the degree-two correction to the same
remote-tail/completed-growth product used in the existing quartic argument.
-/

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

/-! ## Degree-two logarithmic remote decay -/

theorem full_sub_guarded_trace2_div_core_tendsto_zero_log
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
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
      (fullLatticeZeroKernelCyclicTrace2 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace2 F T) /
          (Z.N T (2 * T) : ℝ)) atTop (nhds 0) := by
  let A : ℝ := 2 * (1 + μ)
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
  have hconst : Tendsto (fun _ : ℝ => 4 * C) atTop (nhds (4 * C)) :=
    tendsto_const_nhds
  have hupperLim : Tendsto (fun T =>
      (4 * C) *
        (((Z.N T (2 * T) : ℝ) ^ 3 * remoteLatticePairScaleTwelve F T) *
          T ^ (3 * μ / 2 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hconst.mul hmain
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_
    hupperLim
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hguard.distinguished_period_log, hhat, hremote, hfull, hscaleOne,
    eventually_NIprime_le_two_core hRvM,
    (Zeta23.Assembly.tendsto_N_atTop Z hRvM).eventually_ge_atTop 1]
      with T hT hperiodT hhatT hremoteT hfullT hscaleOneT hNI hN1
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hL : 0 < F.period T (F.distinguished T) := by
    rw [hperiodT]
    exact mul_pos hguard.bandwidth_pos (Real.log_pos hT)
  have hscale0 : 0 ≤ remoteLatticePairScaleTwelve F T :=
    remoteLatticePairScaleTwelve_nonneg F T hT0 hL
  have hN0 : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hNpos : 0 < (Z.N T (2 * T) : ℝ) :=
    lt_of_lt_of_le zero_lt_one hN1
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
  have hcorr := full_sub_guarded_trace_two_abs_le_balanced_frobenius
    F T (lt_of_lt_of_le zero_lt_one hhatT)
  have hcorrB :
      |fullLatticeZeroKernelCyclicTrace2 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace2 F T| ≤
        4 * C * remoteLatticePairScaleTwelve F T * g *
          (Z.N T (2 * T) : ℝ) ^ 2 := by
    calc
      |fullLatticeZeroKernelCyclicTrace2 F T -
          QuarticTransfer.guardedZeroKernelCyclicTrace2 F T| ≤
        ‖balancedRemoteLatticeZeroMatrix F T‖ *
            ‖balancedFullLatticeZeroMatrix F T‖ +
          ‖balancedGuardedLatticeZeroMatrix F T‖ *
            ‖balancedRemoteLatticeZeroMatrix F T‖ := hcorr
      _ ≤ (2 * remoteLatticePairScaleTwelve F T *
            (Z.N T (2 * T) : ℝ)) *
          (C * g * (Z.N T (2 * T) : ℝ)) +
        (C * g * (Z.N T (2 * T) : ℝ)) *
          (2 * remoteLatticePairScaleTwelve F T *
            (Z.N T (2 * T) : ℝ)) := by gcongr
      _ = 4 * C * remoteLatticePairScaleTwelve F T * g *
          (Z.N T (2 * T) : ℝ) ^ 2 := by ring
  have hN2 : 1 ≤ (Z.N T (2 * T) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((Z.N T (2 * T) : ℝ) - 1)]
  have hg2 : 1 ≤ g ^ 2 := by
    nlinarith [sq_nonneg (g - 1)]
  have hN2g2 : 1 ≤ (Z.N T (2 * T) : ℝ) ^ 2 * g ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN2) (sub_nonneg.mpr hg2)]
  have hdom :
      remoteLatticePairScaleTwelve F T * g *
          (Z.N T (2 * T) : ℝ) ≤
        ((Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T) * g ^ 3 := by
    calc
      remoteLatticePairScaleTwelve F T * g *
          (Z.N T (2 * T) : ℝ) =
        (remoteLatticePairScaleTwelve F T * g *
          (Z.N T (2 * T) : ℝ)) * 1 := by ring
      _ ≤ (remoteLatticePairScaleTwelve F T * g *
          (Z.N T (2 * T) : ℝ)) *
            ((Z.N T (2 * T) : ℝ) ^ 2 * g ^ 2) := by gcongr
      _ = ((Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T) * g ^ 3 := by ring
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
    |fullLatticeZeroKernelCyclicTrace2 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace2 F T| /
          (Z.N T (2 * T) : ℝ) ≤
      (4 * C * remoteLatticePairScaleTwelve F T * g *
        (Z.N T (2 * T) : ℝ) ^ 2) /
          (Z.N T (2 * T) : ℝ) :=
      div_le_div_of_nonneg_right hcorrB hN0
    _ = (4 * C) *
        (remoteLatticePairScaleTwelve F T * g *
          (Z.N T (2 * T) : ℝ)) := by
      field_simp [hNpos.ne']
      ring
    _ ≤ (4 * C) *
        (((Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T) * g ^ 3) := by gcongr
    _ = (4 * C) *
        (((Z.N T (2 * T) : ℝ) ^ 3 *
          remoteLatticePairScaleTwelve F T) *
            T ^ (3 * μ / 2 : ℝ)) := by rw [hg3]

end RH.Zeta85.RSPoissonCyclicBridge
