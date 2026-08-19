import RH.Zeta85.Discharge.RSLowDegreeRemoteCorrectionThree

/-!
# Target-specific completed/guarded remote correction

The four degreewise remote estimates are combined only after the target
quartic has been formed.  The constant term cancels exactly, so the normalized
completed and guarded quartic numerators have the same asymptotic value.
-/

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23 TrimmedMoment

/-- The target quartic evaluated on the completed full-lattice cyclic traces. -/
def fullLatticeZeroKernelQuarticNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  let u := QuarticTransfer.uncenteredQuartic q
  u.p0 * (F.blockDim T : ℝ) +
    u.p1 * fullLatticeZeroKernelCyclicTrace1 F T +
    u.p2 * fullLatticeZeroKernelCyclicTrace2 F T +
    u.p3 * fullLatticeZeroKernelCyclicTrace3 F T +
    u.p4 * fullLatticeZeroKernelCyclicTrace4 F T

/-- At logarithmic period, Poisson completion does not change the normalized
value of any fixed target quartic. -/
theorem full_sub_guarded_quartic_div_core_tendsto_zero_log
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
      Zeta23.l)
    (q : Quartic) :
    Tendsto (fun T =>
      (fullLatticeZeroKernelQuarticNumerator q F T -
        QuarticTransfer.guardedZeroKernelQuarticNumerator q F T) /
          (Z.N T (2 * T) : ℝ)) atTop (nhds 0) := by
  let u := QuarticTransfer.uncenteredQuartic q
  have h1 := full_sub_guarded_trace1_div_core_tendsto_zero_log
    hdata hguard htail hRvM hhat hmass
  have h2 := full_sub_guarded_trace2_div_core_tendsto_zero_log
    hdata hguard htail hRvM w c hadm hhat hmass
  have h3 := full_sub_guarded_trace3_div_core_tendsto_zero_log
    hdata hguard htail hRvM w c hadm hhat hmass
  have h4 := full_sub_guarded_trace4_div_core_tendsto_zero_log
    hdata hguard htail hRvM w c hadm hhat hmass
  have hc1 : Tendsto (fun T =>
      u.p1 * ((fullLatticeZeroKernelCyclicTrace1 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace1 F T) /
          (Z.N T (2 * T) : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul h1)
  have hc2 : Tendsto (fun T =>
      u.p2 * ((fullLatticeZeroKernelCyclicTrace2 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace2 F T) /
          (Z.N T (2 * T) : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul h2)
  have hc3 : Tendsto (fun T =>
      u.p3 * ((fullLatticeZeroKernelCyclicTrace3 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace3 F T) /
          (Z.N T (2 * T) : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul h3)
  have hc4 : Tendsto (fun T =>
      u.p4 * ((fullLatticeZeroKernelCyclicTrace4 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace4 F T) /
          (Z.N T (2 * T) : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul h4)
  have hsum := ((hc1.add hc2).add hc3).add hc4
  apply hsum.congr'
  filter_upwards [] with T
  dsimp only [u, fullLatticeZeroKernelQuarticNumerator,
    QuarticTransfer.guardedZeroKernelQuarticNumerator]
  ring

end RH.Zeta85.RSPoissonCyclicBridge