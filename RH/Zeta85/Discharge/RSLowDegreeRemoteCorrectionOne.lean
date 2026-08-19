import RH.Zeta85.Discharge.RSLowDegreeRemoteCorrection

/-!
# Degree-one completed/guarded remote correction

The diagonal trace is bounded directly by the pair-kernel tail scale, avoiding
the dimension loss of a generic trace-norm estimate.
-/

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

/-! ## The degree-one correction without dimension loss -/

theorem abs_rtrace_balancedKernelMatrix_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (s : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hK : ∀ i, ‖K i i‖ ≤ C) :
    |RHLinalg.rtrace (balancedKernelMatrix K s)| ≤
      C * ∑ i : ι, ‖s i‖ ^ 2 := by
  calc
    |RHLinalg.rtrace (balancedKernelMatrix K s)| =
        |Complex.re ((balancedKernelMatrix K s).trace)| := rfl
    _ ≤ ‖(balancedKernelMatrix K s).trace‖ :=
      Complex.abs_re_le_norm _
    _ = ‖∑ i : ι, s i * K i i * s i‖ := by
      simp only [Matrix.trace, Matrix.diag_apply, balancedKernelMatrix]
    _ ≤ ∑ i : ι, ‖s i * K i i * s i‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, C * ‖s i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖s i * K i i * s i‖ = ‖s i‖ ^ 2 * ‖K i i‖ := by
          simp only [norm_mul]
          ring
        _ ≤ ‖s i‖ ^ 2 * C := by gcongr
        _ = C * ‖s i‖ ^ 2 := by ring
    _ = C * ∑ i : ι, ‖s i‖ ^ 2 := by
      rw [Finset.mul_sum]

theorem full_sub_guarded_trace_one_eq_balanced_remote_rtrace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    fullLatticeZeroKernelCyclicTrace1 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace1 F T =
      RHLinalg.rtrace (balancedRemoteLatticeZeroMatrix F T) := by
  have h := congrArg (fun A => RHLinalg.rtrace (A ^ 1))
    (balancedGuarded_add_remote_eq_full F T)
  simp only [pow_one, RHLinalg.rtrace_add] at h
  rw [rtrace_balancedFull_pow_one_eq_full F T hhat,
    rtrace_balancedGuarded_pow_one_eq_guarded F T hhat,
    rtrace_fullLatticeZeroMatrix_pow_one_eq_fullTrace,
    rtrace_guardedLatticeZeroMatrix_pow_one_eq_guardedTrace] at h
  linarith

theorem full_sub_guarded_trace_one_abs_le_pairScale
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T C : ℝ)
    (hhat : 0 < F.hatDenominator T) (hC : 0 ≤ C)
    (hpair : ∀ ρ : ↥(ZeroSide.ZI Z T),
      ‖remoteLatticePairKernel F T (ρ : ℂ) (ρ : ℂ)‖ ≤ C) :
    |fullLatticeZeroKernelCyclicTrace1 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace1 F T| ≤
      C * ((Z.NIprime T : ℝ) / F.hatDenominator T) := by
  rw [full_sub_guarded_trace_one_eq_balanced_remote_rtrace F T hhat]
  have h := abs_rtrace_balancedKernelMatrix_le
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ)) hC hpair
  change |RHLinalg.rtrace (balancedKernelMatrix
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ)))| ≤ _
  rw [sum_zeroVertexWeight_norm_sq F T hhat] at h
  exact h

theorem full_sub_guarded_trace1_div_core_tendsto_zero_log
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hdata : CompletedTraceKernelData F)
    (hguard : DistinguishedLogGuardedPoissonKernelData F)
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hRvM : RiemannVonMangoldt Z)
    (hhat : ∀ᶠ T in atTop, 1 ≤ F.hatDenominator T)
    (hmass : (fun T => distinguishedWindowSobolevMassSix F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T =>
      (fullLatticeZeroKernelCyclicTrace1 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace1 F T) /
          (Z.N T (2 * T) : ℝ)) atTop (nhds 0) := by
  have hpair := eventually_remotePair_le_scale_twelve_log htail hguard
  have hscaleLim := remoteLatticePairScaleTwelve_tendsto_zero_log
    F hdata.support_pos.le hguard.bandwidth_pos htail.bandwidth_lt_one
      hRvM hguard.distinguished_period_log hmass
  have hconst : Tendsto (fun _ : ℝ => 2) atTop (nhds 2) :=
    tendsto_const_nhds
  have hupper : Tendsto (fun T =>
      2 * remoteLatticePairScaleTwelve F T) atTop (nhds 0) := by
    simpa only [mul_zero] using hconst.mul hscaleLim
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hupper
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hguard.distinguished_period_log, hhat, hpair,
    eventually_NIprime_le_two_core hRvM,
    (Zeta23.Assembly.tendsto_N_atTop Z hRvM).eventually_gt_atTop 0]
      with T hT hperiodT hhatT hpairT hNI hNpos
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hL : 0 < F.period T (F.distinguished T) := by
    rw [hperiodT]
    exact mul_pos hguard.bandwidth_pos (Real.log_pos hT)
  have hscale0 : 0 ≤ remoteLatticePairScaleTwelve F T :=
    remoteLatticePairScaleTwelve_nonneg F T hT0 hL
  have hhatPos : 0 < F.hatDenominator T :=
    lt_of_lt_of_le zero_lt_one hhatT
  have hcorr := full_sub_guarded_trace_one_abs_le_pairScale
    F T (remoteLatticePairScaleTwelve F T) hhatPos hscale0
      (fun ρ => hpairT ρ ρ)
  have hquot : (Z.NIprime T : ℝ) / F.hatDenominator T ≤
      (Z.NIprime T : ℝ) :=
    div_le_self (Nat.cast_nonneg _) hhatT
  have hN0 : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hN0]
  calc
    |fullLatticeZeroKernelCyclicTrace1 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace1 F T| /
          (Z.N T (2 * T) : ℝ) ≤
      (remoteLatticePairScaleTwelve F T *
        ((Z.NIprime T : ℝ) / F.hatDenominator T)) /
          (Z.N T (2 * T) : ℝ) :=
      div_le_div_of_nonneg_right hcorr hN0
    _ ≤ (remoteLatticePairScaleTwelve F T *
        (2 * (Z.N T (2 * T) : ℝ))) /
          (Z.N T (2 * T) : ℝ) := by
      gcongr
      exact hquot.trans hNI
    _ = 2 * remoteLatticePairScaleTwelve F T := by
      field_simp [hNpos.ne']
      ring

end RH.Zeta85.RSPoissonCyclicBridge
