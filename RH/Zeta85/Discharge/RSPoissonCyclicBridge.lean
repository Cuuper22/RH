import RH.Zeta85.Discharge.RSCyclicFourierBridge
import RH.Zeta85.Discharge.QuarticTransfer

/-!
# Guarded Poisson to cyclic Rudnick--Sarnak bridge

This module evaluates the full distinguished Poisson lattice in terms of
the literal local profile and matches its quartic zero cycle to the exact
complex-frequency Rudnick--Sarnak test.
-/

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

private theorem paperFT_rescaled_square
    {r : ℝ → ℝ} {L E : ℝ} (hL : 0 < L) (hE : E ≠ 0) (z : ℂ) :
    paperFT (fun x => ((L * r (L * x) ^ 2 / E : ℝ) : ℂ)) (L * z) =
      (E : ℂ)⁻¹ * paperFT (fun u => (r u : ℂ) ^ 2) z := by
  let g : ℝ → ℂ := fun u =>
    ((r u ^ 2 / E : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))
  have hchange := Measure.integral_comp_mul_left g L
  rw [abs_of_pos (inv_pos.mpr hL)] at hchange
  unfold paperFT
  calc
    (∫ x : ℝ, ((L * r (L * x) ^ 2 / E : ℝ) : ℂ) *
        Complex.exp (Complex.I * (L * z) * (x : ℂ))) =
        (L : ℂ) * ∫ x : ℝ, g (L * x) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [g]
          have hexp :
              Complex.exp (Complex.I * (L * z) * (x : ℂ)) =
                Complex.exp (Complex.I * z * ((L * x : ℝ) : ℂ)) := by
            congr 1
            push_cast
            ring
          rw [hexp]
          push_cast
          field_simp [hE]

    _ = (L : ℂ) * ((L⁻¹ : ℝ) • ∫ u : ℝ, g u) := by rw [hchange]
    _ = ∫ u : ℝ, g u := by
      rw [Complex.real_smul]
      push_cast
      field_simp [hL.ne']
    _ = (E : ℂ)⁻¹ * ∫ u : ℝ,
        (r u : ℂ) ^ 2 * Complex.exp (Complex.I * z * (u : ℂ)) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with u
          dsimp [g]
          push_cast
          field_simp [hE]

theorem paperFT_localProfile_scale
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0) (z : ℂ) :
    paperFT (fun x => (F.localProfile T x : ℂ))
        (F.period T (F.distinguished T) * z) =
      ((F.channelEnergy T (F.distinguished T) : ℂ)⁻¹) *
        paperFT
          (fun u => (F.window T (F.distinguished T) u : ℂ) ^ 2) z := by
  simpa only [QuarticGramFamily.localProfile,
    QuarticGramFamily.channelEnergy] using
      (paperFT_rescaled_square
        (r := F.window T (F.distinguished T)) hL hE z)

def fullLatticePairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  PoissonKernelBridge.distinguishedLatticeScale F T *
    ∑' k : ℤ, PoissonKernelBridge.distinguishedLatticeTerm F T
      (gammaOf ρ) (gammaOf ρ') k

def distinguishedEnergyFraction
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  F.channelEnergy T (F.distinguished T) /
    ∫ u : ℝ, F.windowEnergy T u

theorem fullLatticePairKernel_eq_localProfile
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (ρ ρ' : ℂ) :
    fullLatticePairKernel F T ρ ρ' =
      ((QuarticGramFamily.fullLength (σ := σ) T *
        F.channelEnergy T (F.distinguished T) : ℝ) : ℂ) *
        paperFT (fun x => (F.localProfile T x : ℂ))
          (F.period T (F.distinguished T) *
            (gammaOf ρ - gammaOf ρ')) := by
  have hsum := Zeta23.Poisson.hasSum_paperFT_mul_paperFT_complex
    (T := T) hadm.L_pos hadm.vC_contDiff
    (fun u hu => by simp [hadm.support u hu])
    (fun u => by simp [hadm.even u]) (gammaOf ρ) (gammaOf ρ')
  have htsum :
      (∑' k : ℤ, PoissonKernelBridge.distinguishedLatticeTerm F T
        (gammaOf ρ) (gammaOf ρ') k) =
        (F.period T (F.distinguished T) : ℂ) *
          paperFT
            (fun u => (F.window T (F.distinguished T) u : ℂ) ^ 2)
            (gammaOf ρ - gammaOf ρ') := by
    simpa only [PoissonKernelBridge.distinguishedLatticeTerm,
      pow_two] using hsum.tsum_eq
  have hsqrt :
      ((Real.sqrt (QuarticGramFamily.fullLength (σ := σ) T /
        F.period T (F.distinguished T)) : ℂ) ^ 2) =
        ((QuarticGramFamily.fullLength (σ := σ) T /
          F.period T (F.distinguished T) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow,
      Real.sq_sqrt (div_nonneg hfull.le hadm.L_pos.le)]
  rw [fullLatticePairKernel, htsum,
    paperFT_localProfile_scale F T hadm.L_pos hE]
  unfold PoissonKernelBridge.distinguishedLatticeScale
  rw [hsqrt]
  push_cast
  field_simp [hadm.L_pos.ne', hE]

theorem fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (ρ ρ' : ℂ) :
    fullLatticePairKernel F T ρ ρ' *
        QuarticTransfer.zeroEdgeWeight F T ρ =
      (distinguishedEnergyFraction F T : ℂ) * (Z.mult ρ : ℂ) *
        paperFT (fun x => (F.localProfile T x : ℂ))
          (F.period T (F.distinguished T) *
            (gammaOf ρ - gammaOf ρ')) := by
  rw [fullLatticePairKernel_eq_localProfile F T w c hadm hfull hE]
  unfold QuarticTransfer.zeroEdgeWeight QuarticGramFamily.hatDenominator
    distinguishedEnergyFraction
  push_cast
  field_simp [hfull.ne', htotal]

theorem fullLatticePairKernel_comm
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ ρ' : ℂ) :
    fullLatticePairKernel F T ρ ρ' =
      fullLatticePairKernel F T ρ' ρ := by
  unfold fullLatticePairKernel
  congr 1
  apply tsum_congr
  intro k
  unfold PoissonKernelBridge.distinguishedLatticeTerm
  ring

/-- The exact pair error left after replacing the completed lattice by the
finite guarded lattice. -/
def remoteLatticePairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  fullLatticePairKernel F T ρ ρ' -
    PoissonKernelBridge.canonicalGuardedPairKernel F T ρ ρ'

theorem guardedPair_add_remote_eq_full
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ ρ' : ℂ) :
    PoissonKernelBridge.canonicalGuardedPairKernel F T ρ ρ' +
        remoteLatticePairKernel F T ρ ρ' =
      fullLatticePairKernel F T ρ ρ' := by
  unfold remoteLatticePairKernel
  ring

theorem remoteLatticePairKernel_eq_scaled_remoteTails
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ ρ' : ℂ)
    (hsum : Summable (PoissonKernelBridge.distinguishedLatticeTerm F T
      (gammaOf ρ) (gammaOf ρ'))) :
    remoteLatticePairKernel F T ρ ρ' =
      PoissonKernelBridge.distinguishedLatticeScale F T *
        ((∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
          (gammaOf ρ) (gammaOf ρ')
          (-(((PoissonKernelBridge.distinguishedEndpointGuardWidth F T + m : ℕ) : ℤ) + 1))) +
        ∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
          (gammaOf ρ) (gammaOf ρ')
          ((F.channelDim T (F.distinguished T) +
            PoissonKernelBridge.distinguishedEndpointGuardWidth F T + m : ℕ) : ℤ)) := by
  have hguard :=
    PoissonKernelBridge.canonicalGuardedPairKernel_eq_fullLattice_sub_remoteTails
      F T ρ ρ' hsum
  unfold remoteLatticePairKernel fullLatticePairKernel
  rw [hguard]
  ring

theorem localProfile_even
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) (x : ℝ) :
    F.localProfile T (-x) = F.localProfile T x := by
  unfold QuarticGramFamily.localProfile
  dsimp only
  rw [show F.period T (F.distinguished T) * -x =
      -(F.period T (F.distinguished T) * x) by ring,
    hadm.even]

theorem localProfile_continuous
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    Continuous (F.localProfile T) := by
  unfold QuarticGramFamily.localProfile
  dsimp only
  exact (continuous_const.mul
    ((hadm.continuous.comp (continuous_const.mul continuous_id)).pow 2)).div_const _

theorem localProfile_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    HasCompactSupport (F.localProfile T) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Icc (-(1 : ℝ) / 2) (1 / 2)))
  intro x hx
  have habs : 1 / 2 < |x| := by
    by_contra hnot
    have hle : |x| ≤ 1 / 2 := le_of_not_gt hnot
    apply hx
    constructor
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]
  have hbound : F.period T (F.distinguished T) / 2 ≤
      |F.period T (F.distinguished T) * x| := by
    rw [abs_mul, abs_of_pos hadm.L_pos]
    nlinarith [hadm.L_pos]
  unfold QuarticGramFamily.localProfile
  dsimp only
  rw [hadm.support _ hbound]
  ring

def scaledZeroOrdinate (T : ℝ) (ρ : ℂ) : ℂ :=
  ((Zeta23.l T / (2 * Real.pi) : ℝ) : ℂ) * gammaOf ρ

theorem cyclicFrequencyFour_scaled_reversed
    {μ T L : ℝ} (hperiod : L = μ * Zeta23.l T)
    (ρ₁ ρ₂ ρ₃ ρ₄ : ℂ) :
    RSReduction.cyclicFrequencyFour μ
      ![scaledZeroOrdinate T ρ₁, scaledZeroOrdinate T ρ₄,
        scaledZeroOrdinate T ρ₃, scaledZeroOrdinate T ρ₂] =
      ![(L : ℂ) * (gammaOf ρ₁ - gammaOf ρ₂),
        (L : ℂ) * (gammaOf ρ₄ - gammaOf ρ₁),
        (L : ℂ) * (gammaOf ρ₃ - gammaOf ρ₄),
        (L : ℂ) * (gammaOf ρ₂ - gammaOf ρ₃)] := by
  funext j
  fin_cases j <;>
    simp [RSReduction.cyclicFrequencyFour, scaledZeroOrdinate, hperiod] <;>
    field_simp [Real.pi_ne_zero]

def fullLatticeZeroCycle4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (ρ₁ ρ₂ ρ₃ ρ₄ : ℂ) : ℂ :=
  fullLatticePairKernel F T ρ₃ ρ₄ *
    (fullLatticePairKernel F T ρ₁ ρ₂ *
      (fullLatticePairKernel F T ρ₂ ρ₃ *
        (fullLatticePairKernel F T ρ₁ ρ₄ *
          (QuarticTransfer.zeroEdgeWeight F T ρ₁ *
            (QuarticTransfer.zeroEdgeWeight F T ρ₂ *
              (QuarticTransfer.zeroEdgeWeight F T ρ₃ *
                QuarticTransfer.zeroEdgeWeight F T ρ₄))))))

/-- Quartic telescoping correction from the guarded grid to the completed
Poisson lattice.  Every summand contains an explicit remote-tail pair. -/
def remoteCorrectionZeroCycle4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (ρ₁ ρ₂ ρ₃ ρ₄ : ℂ) : ℂ :=
  let G := PoissonKernelBridge.canonicalGuardedPairKernel F T
  let R := remoteLatticePairKernel F T
  let K := fullLatticePairKernel F T
  (R ρ₃ ρ₄ * K ρ₁ ρ₂ * K ρ₂ ρ₃ * K ρ₁ ρ₄ +
    G ρ₃ ρ₄ * R ρ₁ ρ₂ * K ρ₂ ρ₃ * K ρ₁ ρ₄ +
    G ρ₃ ρ₄ * G ρ₁ ρ₂ * R ρ₂ ρ₃ * K ρ₁ ρ₄ +
    G ρ₃ ρ₄ * G ρ₁ ρ₂ * G ρ₂ ρ₃ * R ρ₁ ρ₄) *
      (QuarticTransfer.zeroEdgeWeight F T ρ₁ *
        (QuarticTransfer.zeroEdgeWeight F T ρ₂ *
          (QuarticTransfer.zeroEdgeWeight F T ρ₃ *
            QuarticTransfer.zeroEdgeWeight F T ρ₄)))

theorem guardedZeroCycle4_add_remoteCorrection_eq_full
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (ρ₁ ρ₂ ρ₃ ρ₄ : ℂ) :
    QuarticTransfer.guardedZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄ +
        remoteCorrectionZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄ =
      fullLatticeZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄ := by
  simp only [QuarticTransfer.guardedZeroCycle4,
    remoteCorrectionZeroCycle4, fullLatticeZeroCycle4,
    ← guardedPair_add_remote_eq_full F T]
  ring

def fullLatticeZeroKernelCyclicTrace4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
      fullLatticeZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄)

def remoteCorrectionCyclicTrace4
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  Complex.re (∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
    ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
      remoteCorrectionZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄)

theorem guardedCyclicTrace4_add_remoteCorrection_eq_full
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    QuarticTransfer.guardedZeroKernelCyclicTrace4 F T +
        remoteCorrectionCyclicTrace4 F T =
      fullLatticeZeroKernelCyclicTrace4 F T := by
  unfold QuarticTransfer.guardedZeroKernelCyclicTrace4
    remoteCorrectionCyclicTrace4 fullLatticeZeroKernelCyclicTrace4
  rw [← Complex.add_re, ← Finset.sum_add_distrib]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro ρ₁ hρ₁
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ₂ hρ₂
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ₃ hρ₃
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ₄ hρ₄
  exact guardedZeroCycle4_add_remoteCorrection_eq_full
    F T ρ₁ ρ₂ ρ₃ ρ₄

theorem fullLatticeZeroCycle4_eq_rsGaugeTest
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hμ : 0 < μ)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T)
    (ρ₁ ρ₂ ρ₃ ρ₄ : ℂ) :
    (μ : ℂ) ^ 4 * fullLatticeZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄ =
      (distinguishedEnergyFraction F T : ℂ) ^ 4 *
        ((Z.mult ρ₁ : ℂ) * (Z.mult ρ₂ : ℂ) *
          (Z.mult ρ₃ : ℂ) * (Z.mult ρ₄ : ℂ)) *
        rsGaugeTest (n := 3)
          (RSReduction.weightedCyclicSymbol (k := 4) μ (F.localProfile T))
          ![scaledZeroOrdinate T ρ₁, scaledZeroOrdinate T ρ₄,
            scaledZeroOrdinate T ρ₃, scaledZeroOrdinate T ρ₂] := by
  have hfactor : fullLatticeZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄ =
      (fullLatticePairKernel F T ρ₁ ρ₂ *
        QuarticTransfer.zeroEdgeWeight F T ρ₁) *
      (fullLatticePairKernel F T ρ₂ ρ₃ *
        QuarticTransfer.zeroEdgeWeight F T ρ₂) *
      (fullLatticePairKernel F T ρ₃ ρ₄ *
        QuarticTransfer.zeroEdgeWeight F T ρ₃) *
      (fullLatticePairKernel F T ρ₄ ρ₁ *
        QuarticTransfer.zeroEdgeWeight F T ρ₄) := by
    unfold fullLatticeZeroCycle4
    rw [fullLatticePairKernel_comm F T ρ₁ ρ₄]
    ring
  have h12 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal ρ₁ ρ₂
  have h23 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal ρ₂ ρ₃
  have h34 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal ρ₃ ρ₄
  have h41 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal ρ₄ ρ₁
  have hrs := RSReduction.rsGaugeTest_weightedCyclicSymbol_four
    hμ (F.localProfile T)
      (localProfile_continuous F T w c hadm)
      (localProfile_hasCompactSupport F T w c hadm)
      ![scaledZeroOrdinate T ρ₁, scaledZeroOrdinate T ρ₄,
        scaledZeroOrdinate T ρ₃, scaledZeroOrdinate T ρ₂]
  rw [cyclicFrequencyFour_scaled_reversed hperiod ρ₁ ρ₂ ρ₃ ρ₄,
    Fin.prod_univ_four] at hrs
  simp at hrs
  rw [hfactor, h12, h23, h34, h41, hrs]
  ring_nf

end RH.Zeta85.RSPoissonCyclicBridge
