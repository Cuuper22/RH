import RH.Zeta85.Discharge.RSRemoteCorrection

/-!
# Completed fourth trace as a finite Rudnick--Sarnak gauge sum

The pointwise complex-frequency Poisson identity is summed here only after
its exact quartic form has been established.
-/

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def finiteRSGaugeTrace4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
      ((Z.mult ρ₁ : ℂ) * (Z.mult ρ₂ : ℂ) *
        (Z.mult ρ₃ : ℂ) * (Z.mult ρ₄ : ℂ)) *
      rsGaugeTest (n := 3)
        (RSReduction.weightedCyclicSymbol (k := 4) μ (F.localProfile T))
        ![scaledZeroOrdinate T ρ₁, scaledZeroOrdinate T ρ₄,
          scaledZeroOrdinate T ρ₃, scaledZeroOrdinate T ρ₂])

/-- The finite four-zero gauge sum with the normalization scale exposed.
Taking `s = log T` gives exactly the ordinate normalization used by
`RS1996ZetaInputs`. -/
def finiteRSGaugeTrace4AtScale
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T q s : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
      ((Z.mult ρ₁ : ℂ) * (Z.mult ρ₂ : ℂ) *
        (Z.mult ρ₃ : ℂ) * (Z.mult ρ₄ : ℂ)) *
      rsGaugeTest (n := 3)
        (RSReduction.weightedCyclicSymbol (k := 4) q (F.localProfile T))
        ![scaledZeroOrdinateAtScale s ρ₁,
          scaledZeroOrdinateAtScale s ρ₄,
          scaledZeroOrdinateAtScale s ρ₃,
          scaledZeroOrdinateAtScale s ρ₂])

theorem fullLatticeTrace4_eq_finiteRSGauge_atScale
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c q s : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hq : 0 < q)
    (hperiod : F.period T (F.distinguished T) = q * s) :
    q ^ 4 * fullLatticeZeroKernelCyclicTrace4 F T =
      distinguishedEnergyFraction F T ^ 4 *
        finiteRSGaugeTrace4AtScale F T q s := by
  have hsum :
      (q : ℂ) ^ 4 *
          (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
            ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
              fullLatticeZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄) =
        (distinguishedEnergyFraction F T : ℂ) ^ 4 *
          (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
            ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
              ((Z.mult ρ₁ : ℂ) * (Z.mult ρ₂ : ℂ) *
                (Z.mult ρ₃ : ℂ) * (Z.mult ρ₄ : ℂ)) *
              rsGaugeTest (n := 3)
                (RSReduction.weightedCyclicSymbol (k := 4) q
                  (F.localProfile T))
                ![scaledZeroOrdinateAtScale s ρ₁,
                  scaledZeroOrdinateAtScale s ρ₄,
                  scaledZeroOrdinateAtScale s ρ₃,
                  scaledZeroOrdinateAtScale s ρ₂]) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ₁ hρ₁
    apply Finset.sum_congr rfl
    intro ρ₂ hρ₂
    apply Finset.sum_congr rfl
    intro ρ₃ hρ₃
    apply Finset.sum_congr rfl
    intro ρ₄ hρ₄
    simpa only [mul_assoc] using
      fullLatticeZeroCycle4_eq_rsGaugeTest_atScale
        F T w c q s hadm hfull hE htotal hq hperiod
          ρ₁ ρ₂ ρ₃ ρ₄
  have hqcast : (q : ℂ) ^ 4 = ((q ^ 4 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hecast : (distinguishedEnergyFraction F T : ℂ) ^ 4 =
      ((distinguishedEnergyFraction F T ^ 4 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hqcast, hecast] at hsum
  have hre := congrArg Complex.re hsum
  unfold fullLatticeZeroKernelCyclicTrace4 finiteRSGaugeTrace4AtScale
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hre

/-- The exact finite gauge trace at the `log T` normalization of RS 3.1. -/
def finiteRSLogGaugeTrace4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  finiteRSGaugeTrace4AtScale F T μ (Real.log T)

theorem fullLatticeTrace4_eq_finiteRSLogGauge
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hμ : 0 < μ)
    (hperiod : F.period T (F.distinguished T) = μ * Real.log T) :
    μ ^ 4 * fullLatticeZeroKernelCyclicTrace4 F T =
      distinguishedEnergyFraction F T ^ 4 *
        finiteRSLogGaugeTrace4 F T := by
  exact fullLatticeTrace4_eq_finiteRSGauge_atScale
    F T w c μ (Real.log T) hadm hfull hE htotal hμ hperiod

theorem fullLatticeTrace4_eq_finiteRSGauge
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hμ : 0 < μ)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T) :
    μ ^ 4 * fullLatticeZeroKernelCyclicTrace4 F T =
      distinguishedEnergyFraction F T ^ 4 * finiteRSGaugeTrace4 F T := by
  have hsum :
      (μ : ℂ) ^ 4 *
          (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
            ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
              fullLatticeZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄) =
        (distinguishedEnergyFraction F T : ℂ) ^ 4 *
          (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
            ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
              ((Z.mult ρ₁ : ℂ) * (Z.mult ρ₂ : ℂ) *
                (Z.mult ρ₃ : ℂ) * (Z.mult ρ₄ : ℂ)) *
              rsGaugeTest (n := 3)
                (RSReduction.weightedCyclicSymbol (k := 4) μ
                  (F.localProfile T))
                ![scaledZeroOrdinate T ρ₁, scaledZeroOrdinate T ρ₄,
                  scaledZeroOrdinate T ρ₃, scaledZeroOrdinate T ρ₂]) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ₁ hρ₁
    apply Finset.sum_congr rfl
    intro ρ₂ hρ₂
    apply Finset.sum_congr rfl
    intro ρ₃ hρ₃
    apply Finset.sum_congr rfl
    intro ρ₄ hρ₄
    simpa only [mul_assoc] using fullLatticeZeroCycle4_eq_rsGaugeTest
      F T w c hadm hfull hE htotal hμ hperiod ρ₁ ρ₂ ρ₃ ρ₄
  have hμcast : (μ : ℂ) ^ 4 = ((μ ^ 4 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hecast : (distinguishedEnergyFraction F T : ℂ) ^ 4 =
      ((distinguishedEnergyFraction F T ^ 4 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hμcast, hecast] at hsum
  have hre := congrArg Complex.re hsum
  unfold fullLatticeZeroKernelCyclicTrace4 finiteRSGaugeTrace4
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hre

end RH.Zeta85.RSPoissonCyclicBridge
