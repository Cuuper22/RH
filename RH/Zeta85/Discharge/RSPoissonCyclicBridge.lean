import RH.Zeta85.Discharge.RSCyclicFourierBridge
import RH.Zeta85.Discharge.QuarticTransfer

/-!
# Guarded Poisson to cyclic Rudnick--Sarnak bridge

This module evaluates the full distinguished Poisson lattice in terms of
the literal local profile and matches its quartic zero cycle to the exact
complex-frequency Rudnick--Sarnak test.
-/

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

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

theorem remoteLatticePairKernel_norm_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hT : 0 < T)
    (hL : 0 < F.period T (F.distinguished T))
    (hcount : F.channelDim T (F.distinguished T) =
      ⌊F.period T (F.distinguished T) * T / (2 * Real.pi)⌋₊)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupport : ∀ u,
      (F.window T (F.distinguished T) u : ℂ) ≠ 0 →
        |u| ≤ F.period T (F.distinguished T) / 2)
    (ρ ρ' : ↥(Zeta23.ZeroSide.ZI Z T)) :
    ‖remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ)‖ ≤
      ‖PoissonKernelBridge.distinguishedLatticeScale F T‖ *
        (PoissonKernelBridge.distinguishedRemoteTailScale F T +
          PoissonKernelBridge.distinguishedRemoteTailScale F T) := by
  let n := F.channelDim T (F.distinguished T)
  let r := PoissonKernelBridge.distinguishedEndpointGuardWidth F T
  let C := PoissonKernelBridge.distinguishedWindowFourierMajorant F T
  have hn : n = ⌊T / PoissonKernelBridge.distinguishedGridStep F T⌋₊ := by
    exact PoissonKernelBridge.distinguishedChannelDim_eq_floor_gridStep
      F T hL hcount
  have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT
  have hρ : (ρ : ℂ) ∈ Z.ZIprime T :=
    (Zeta23.ZeroSide.mem_ZI Z T).1 ρ.property
  have hρ' : (ρ' : ℂ) ∈ Z.ZIprime T :=
    (Zeta23.ZeroSide.mem_ZI Z T).1 ρ'.property
  have hdist := PoissonKernelBridge.mem_ZIprime_guarded_distances
    F T n hL hn hρ
  have hdist' := PoissonKernelBridge.mem_ZIprime_guarded_distances
    F T n hL hn hρ'
  have hdecay :=
    PoissonKernelBridge.distinguishedLatticeTerm_le_fourierMajorant_on_ZI
      F T hL hwindow hsupport ρ ρ'
  have hlower :=
    PoissonKernelBridge.lowerLatticeTailFrom_bound_of_weightedDecay
      F T (Zeta23.D0 T) C r hL hD
        (PoissonKernelBridge.distinguishedWindowFourierMajorant_nonneg F T)
        (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) hdecay
        (by simpa only [PoissonKernelBridge.distinguishedGridStep] using hdist.1)
        (by simpa only [PoissonKernelBridge.distinguishedGridStep] using hdist'.1)
  have hupper :=
    PoissonKernelBridge.upperLatticeTail_bound_of_weightedDecay
      F T (Zeta23.D0 T) C (n + r) hL hD
        (PoissonKernelBridge.distinguishedWindowFourierMajorant_nonneg F T)
        (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) hdecay
        (by simpa only [n, r, Nat.cast_add,
          PoissonKernelBridge.distinguishedGridStep] using hdist.2)
        (by simpa only [n, r, Nat.cast_add,
          PoissonKernelBridge.distinguishedGridStep] using hdist'.2)
  have hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)) :=
    hasCompactSupport_of_support_subset_abs hsupport
  have hsum : Summable (PoissonKernelBridge.distinguishedLatticeTerm F T
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))) :=
    (PoissonKernelBridge.hasSum_distinguishedLatticeTerm_alias_of_hasCompactSupport
      F T hL hwindow hcompact
        (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))).2.summable
  rw [remoteLatticePairKernel_eq_scaled_remoteTails F T ρ ρ' hsum,
    norm_mul]
  apply mul_le_mul_of_nonneg_left
  · calc
      ‖(∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
            (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))
            (-(((r + m : ℕ) : ℤ) + 1))) +
          ∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
            (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))
            ((n + r + m : ℕ) : ℤ)‖ ≤
          ‖∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
            (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))
            (-(((r + m : ℕ) : ℤ) + 1))‖ +
          ‖∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
            (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))
            ((n + r + m : ℕ) : ℤ)‖ := norm_add_le _ _
      _ ≤ PoissonKernelBridge.distinguishedRemoteTailScale F T +
          PoissonKernelBridge.distinguishedRemoteTailScale F T := by
        gcongr
        · simpa only [C, r, PoissonKernelBridge.distinguishedRemoteTailScale,
            PoissonKernelBridge.distinguishedGridStep] using hlower.2
        · simpa only [C, n, r,
            PoissonKernelBridge.distinguishedRemoteTailScale,
            PoissonKernelBridge.distinguishedGridStep, Nat.add_assoc] using hupper.2
  · exact norm_nonneg _

def remoteLatticePairScale
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  ‖PoissonKernelBridge.distinguishedLatticeScale F T‖ *
    (PoissonKernelBridge.distinguishedRemoteTailScale F T +
      PoissonKernelBridge.distinguishedRemoteTailScale F T)

theorem norm_distinguishedLatticeScale_eq_ratio
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hσ : 0 ≤ σ) (hμ : 0 < μ) (hl : 0 < Zeta23.l T)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T) :
    ‖PoissonKernelBridge.distinguishedLatticeScale F T‖ = σ / μ := by
  have hratio : QuarticGramFamily.fullLength (σ := σ) T /
      F.period T (F.distinguished T) = σ / μ := by
    unfold QuarticGramFamily.fullLength
    rw [hperiod]
    field_simp [hμ.ne', hl.ne']
  have hnonneg : 0 ≤ σ / μ := div_nonneg hσ hμ.le
  unfold PoissonKernelBridge.distinguishedLatticeScale
  rw [hratio, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]

theorem remoteLatticePairScale_negligible
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hσ : 0 ≤ σ)
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : PoissonKernelBridge.DistinguishedGuardedPoissonKernelData F)
    (hRvM : RiemannVonMangoldt Z) :
    Tendsto (fun T => (Z.N T (2 * T) : ℝ) *
      remoteLatticePairScale F T) atTop (nhds 0) := by
  have htail0 := htail.remoteTailScale_negligible hguard hRvM
  have hconst : Tendsto (fun _ : ℝ => 2 * (σ / μ)) atTop
      (nhds (2 * (σ / μ))) := tendsto_const_nhds
  have hscaled : Tendsto (fun T =>
      (2 * (σ / μ)) * ((Z.N T (2 * T) : ℝ) *
        PoissonKernelBridge.distinguishedRemoteTailScale F T))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hconst.mul htail0
  apply hscaled.congr'
  filter_upwards [hguard.distinguished_period,
    Zeta23.Assembly.eventually_l_pos] with T hperiod hl
  rw [remoteLatticePairScale,
    norm_distinguishedLatticeScale_eq_ratio F T hσ
      hguard.bandwidth_pos hl hperiod]
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

/-! ## Sum-first zero-space matrices -/

def fullLatticeZeroMatrix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    Matrix (↥(ZeroSide.ZI Z T)) (↥(ZeroSide.ZI Z T)) ℂ :=
  fun ρ ρ' => fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ) *
    QuarticTransfer.zeroEdgeWeight F T (ρ' : ℂ)

def guardedLatticeZeroMatrix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    Matrix (↥(ZeroSide.ZI Z T)) (↥(ZeroSide.ZI Z T)) ℂ :=
  fun ρ ρ' =>
    PoissonKernelBridge.canonicalGuardedPairKernel F T (ρ : ℂ) (ρ' : ℂ) *
      QuarticTransfer.zeroEdgeWeight F T (ρ' : ℂ)

def remoteLatticeZeroMatrix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    Matrix (↥(ZeroSide.ZI Z T)) (↥(ZeroSide.ZI Z T)) ℂ :=
  fun ρ ρ' => remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ) *
    QuarticTransfer.zeroEdgeWeight F T (ρ' : ℂ)

theorem guardedZeroMatrix_add_remote_eq_full
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    guardedLatticeZeroMatrix F T + remoteLatticeZeroMatrix F T =
      fullLatticeZeroMatrix F T := by
  ext ρ ρ'
  simp only [guardedLatticeZeroMatrix, remoteLatticeZeroMatrix,
    fullLatticeZeroMatrix, Matrix.add_apply,
    ← guardedPair_add_remote_eq_full F T]
  ring

private theorem rtrace_pow_four_eq_cyclic_generic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) :
    RHLinalg.rtrace (B ^ 4) =
      Complex.re (∑ i : ι, ∑ j : ι,
        (∑ k : ι, B i k * B k j) *
          (∑ l : ι, B j l * B l i)) := by
  rw [show B ^ 4 = (B * B) * (B * B) by noncomm_ring]
  simp [RHLinalg.rtrace, Matrix.trace, Matrix.mul_apply]

theorem rtrace_fullLatticeZeroMatrix_pow_four_eq_subtype_sum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 4) =
      Complex.re (∑ ρ₁ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₄ : ↥(ZeroSide.ZI Z T),
          fullLatticeZeroCycle4 F T
            (ρ₁ : ℂ) (ρ₃ : ℂ) (ρ₂ : ℂ) (ρ₄ : ℂ)) := by
  rw [rtrace_pow_four_eq_cyclic_generic]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro ρ₁ hρ₁
  apply Finset.sum_congr rfl
  intro ρ₂ hρ₂
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ₃ hρ₃
  apply Finset.sum_congr rfl
  intro ρ₄ hρ₄
  unfold fullLatticeZeroMatrix fullLatticeZeroCycle4
  rw [fullLatticePairKernel_comm F T (ρ₄ : ℂ) (ρ₁ : ℂ)]
  ring

private theorem sum_finsetSubtype_eq_finset
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) :
    (∑ x : ↥s, f (x : α)) = ∑ x ∈ s, f x := by
  exact (Finset.sum_subtype s (fun _ => Iff.rfl) f).symm

private theorem sum_finsetSubtype2_eq_finset2
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → α → M) :
    (∑ x : ↥s, ∑ y : ↥s, f (x : α) (y : α)) =
      ∑ x ∈ s, ∑ y ∈ s, f x y := by
  calc
    (∑ x : ↥s, ∑ y : ↥s, f (x : α) (y : α)) =
        ∑ x : ↥s, ∑ y ∈ s, f (x : α) y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_finsetSubtype_eq_finset s (f (x : α))
    _ = ∑ x ∈ s, ∑ y ∈ s, f x y :=
      sum_finsetSubtype_eq_finset s (fun x => ∑ y ∈ s, f x y)

private theorem sum_finsetSubtype3_eq_finset3
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → α → α → M) :
    (∑ x : ↥s, ∑ y : ↥s, ∑ z : ↥s,
      f (x : α) (y : α) (z : α)) =
      ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, f x y z := by
  calc
    (∑ x : ↥s, ∑ y : ↥s, ∑ z : ↥s,
        f (x : α) (y : α) (z : α)) =
        ∑ x : ↥s, ∑ y ∈ s, ∑ z ∈ s, f (x : α) y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_finsetSubtype2_eq_finset2 s (f (x : α))
    _ = ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, f x y z :=
      sum_finsetSubtype_eq_finset s
        (fun x => ∑ y ∈ s, ∑ z ∈ s, f x y z)

private theorem sum_finsetSubtype4_eq_finset4
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → α → α → α → M) :
    (∑ x : ↥s, ∑ y : ↥s, ∑ z : ↥s, ∑ t : ↥s,
      f (x : α) (y : α) (z : α) (t : α)) =
      ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, ∑ t ∈ s, f x y z t := by
  calc
    (∑ x : ↥s, ∑ y : ↥s, ∑ z : ↥s, ∑ t : ↥s,
        f (x : α) (y : α) (z : α) (t : α)) =
        ∑ x : ↥s, ∑ y ∈ s, ∑ z ∈ s, ∑ t ∈ s,
          f (x : α) y z t := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_finsetSubtype3_eq_finset3 s (f (x : α))
    _ = ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, ∑ t ∈ s, f x y z t :=
      sum_finsetSubtype_eq_finset s
        (fun x => ∑ y ∈ s, ∑ z ∈ s, ∑ t ∈ s, f x y z t)

theorem rtrace_fullLatticeZeroMatrix_pow_four_eq_fullTrace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 4) =
      fullLatticeZeroKernelCyclicTrace4 F T := by
  rw [rtrace_fullLatticeZeroMatrix_pow_four_eq_subtype_sum]
  unfold fullLatticeZeroKernelCyclicTrace4
  apply congrArg Complex.re
  calc
    (∑ ρ₁ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₄ : ↥(ZeroSide.ZI Z T),
          fullLatticeZeroCycle4 F T
            (ρ₁ : ℂ) (ρ₃ : ℂ) (ρ₂ : ℂ) (ρ₄ : ℂ)) =
        ∑ ρ₁ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₄ : ↥(ZeroSide.ZI Z T),
          fullLatticeZeroCycle4 F T
            (ρ₁ : ℂ) (ρ₂ : ℂ) (ρ₃ : ℂ) (ρ₄ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ₁ hρ₁
      rw [Finset.sum_comm]
    _ = ∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
        ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
          fullLatticeZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄ := by
      exact sum_finsetSubtype4_eq_finset4 (ZeroSide.ZI Z T)
        (fullLatticeZeroCycle4 F T)

theorem guardedLatticePairKernel_comm
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ ρ' : ℂ) :
    PoissonKernelBridge.canonicalGuardedPairKernel F T ρ ρ' =
      PoissonKernelBridge.canonicalGuardedPairKernel F T ρ' ρ := by
  unfold PoissonKernelBridge.canonicalGuardedPairKernel
    PoissonKernelBridge.canonicalGuardedLatticeSegment
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  unfold PoissonKernelBridge.distinguishedLatticeTerm
  ring

theorem rtrace_guardedLatticeZeroMatrix_pow_four_eq_subtype_sum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 4) =
      Complex.re (∑ ρ₁ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₄ : ↥(ZeroSide.ZI Z T),
          QuarticTransfer.guardedZeroCycle4 F T
            (ρ₁ : ℂ) (ρ₃ : ℂ) (ρ₂ : ℂ) (ρ₄ : ℂ)) := by
  rw [rtrace_pow_four_eq_cyclic_generic]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro ρ₁ hρ₁
  apply Finset.sum_congr rfl
  intro ρ₂ hρ₂
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ₃ hρ₃
  apply Finset.sum_congr rfl
  intro ρ₄ hρ₄
  unfold guardedLatticeZeroMatrix QuarticTransfer.guardedZeroCycle4
  rw [guardedLatticePairKernel_comm F T (ρ₄ : ℂ) (ρ₁ : ℂ)]
  ring

theorem rtrace_guardedLatticeZeroMatrix_pow_four_eq_guardedTrace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 4) =
      QuarticTransfer.guardedZeroKernelCyclicTrace4 F T := by
  rw [rtrace_guardedLatticeZeroMatrix_pow_four_eq_subtype_sum]
  unfold QuarticTransfer.guardedZeroKernelCyclicTrace4
  apply congrArg Complex.re
  calc
    (∑ ρ₁ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₄ : ↥(ZeroSide.ZI Z T),
          QuarticTransfer.guardedZeroCycle4 F T
            (ρ₁ : ℂ) (ρ₃ : ℂ) (ρ₂ : ℂ) (ρ₄ : ℂ)) =
        ∑ ρ₁ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₄ : ↥(ZeroSide.ZI Z T),
          QuarticTransfer.guardedZeroCycle4 F T
            (ρ₁ : ℂ) (ρ₂ : ℂ) (ρ₃ : ℂ) (ρ₄ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ₁ hρ₁
      rw [Finset.sum_comm]
    _ = ∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
        ∑ ρ₃ ∈ ZeroSide.ZI Z T, ∑ ρ₄ ∈ ZeroSide.ZI Z T,
          QuarticTransfer.guardedZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄ := by
      exact sum_finsetSubtype4_eq_finset4 (ZeroSide.ZI Z T)
        (QuarticTransfer.guardedZeroCycle4 F T)

theorem remoteCorrectionCyclicTrace4_eq_rtrace_sub
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    remoteCorrectionCyclicTrace4 F T =
      RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 4) -
        RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 4) := by
  rw [rtrace_fullLatticeZeroMatrix_pow_four_eq_fullTrace,
    rtrace_guardedLatticeZeroMatrix_pow_four_eq_guardedTrace]
  have htrace := guardedCyclicTrace4_add_remoteCorrection_eq_full F T
  linarith

/-! ## Frobenius perturbation of the quartic zero trace -/

/-- Hilbert--Schmidt Cauchy--Schwarz in the exact orientation needed for
the cyclic trace telescope. -/
theorem abs_rtrace_mul_le_frobenius
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    |RHLinalg.rtrace (A * B)| ≤ ‖A‖ * ‖B‖ := by
  calc
    |RHLinalg.rtrace (A * B)| = |Complex.re ((A * B).trace)| := rfl
    _ ≤ ‖(A * B).trace‖ := Complex.abs_re_le_norm _
    _ = ‖∑ i : ι, ∑ j : ι, A i j * B j i‖ := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    _ ≤ ∑ i : ι, ∑ j : ι, ‖A i j‖ * ‖B j i‖ := by
      calc
        ‖∑ i : ι, ∑ j : ι, A i j * B j i‖
            ≤ ∑ i : ι, ‖∑ j : ι, A i j * B j i‖ := norm_sum_le _ _
        _ ≤ ∑ i : ι, ∑ j : ι, ‖A i j * B j i‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_sum_le _ _
        _ = ∑ i : ι, ∑ j : ι, ‖A i j‖ * ‖B j i‖ := by
          simp only [norm_mul]
    _ ≤ Real.sqrt (∑ i : ι, ∑ j : ι, ‖A i j‖ ^ 2) *
          Real.sqrt (∑ i : ι, ∑ j : ι, ‖B j i‖ ^ 2) := by
      calc
        (∑ i : ι, ∑ j : ι, ‖A i j‖ * ‖B j i‖) =
            ∑ ij ∈ Finset.univ.product (Finset.univ : Finset ι),
              ‖A ij.1 ij.2‖ * ‖B ij.2 ij.1‖ := by
          exact (Finset.sum_product'
            (Finset.univ : Finset ι) (Finset.univ : Finset ι)
            (fun i j => ‖A i j‖ * ‖B j i‖)).symm
        _ ≤ Real.sqrt
              (∑ ij ∈ Finset.univ.product (Finset.univ : Finset ι),
                ‖A ij.1 ij.2‖ ^ 2) *
              Real.sqrt
              (∑ ij ∈ Finset.univ.product (Finset.univ : Finset ι),
                ‖B ij.2 ij.1‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt
            (Finset.univ.product (Finset.univ : Finset ι))
            (fun ij : ι × ι => ‖A ij.1 ij.2‖)
            (fun ij : ι × ι => ‖B ij.2 ij.1‖)
        _ = Real.sqrt (∑ i : ι, ∑ j : ι, ‖A i j‖ ^ 2) *
              Real.sqrt (∑ i : ι, ∑ j : ι, ‖B j i‖ ^ 2) := by
          congr 1
          · congr 1
            exact Finset.sum_product'
              (Finset.univ : Finset ι) (Finset.univ : Finset ι)
              (fun i j => ‖A i j‖ ^ 2)
          · congr 1
            exact Finset.sum_product'
              (Finset.univ : Finset ι) (Finset.univ : Finset ι)
              (fun i j => ‖B j i‖ ^ 2)
    _ = ‖A‖ * ‖B‖ := by
      have hBsum :
          (∑ i : ι, ∑ j : ι, ‖B j i‖ ^ 2) =
            ∑ i : ι, ∑ j : ι, ‖B i j‖ ^ 2 := by
        rw [Finset.sum_comm]
      rw [Zeta23.Assembly.norm_eq_sqrt_frobSq,
        Zeta23.Assembly.norm_eq_sqrt_frobSq,
        Zeta23.Assembly.frobSq_eq_sum_norm_sq,
        Zeta23.Assembly.frobSq_eq_sum_norm_sq, hBsum]

/-- A noncommutative fourth-power telescope with no dimension loss.  Only
one copy of the perturbation occurs in each term. -/
theorem rtrace_pow_four_add_sub_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G R : Matrix ι ι ℂ) :
    |RHLinalg.rtrace ((G + R) ^ 4) - RHLinalg.rtrace (G ^ 4)| ≤
      ‖R‖ * ‖G + R‖ ^ 3 +
        (‖G‖ * ‖R‖) * ‖G + R‖ ^ 2 +
        (‖G‖ ^ 2 * ‖R‖) * ‖G + R‖ +
        ‖G‖ ^ 3 * ‖R‖ := by
  have hpow2 (X : Matrix ι ι ℂ) : ‖X ^ 2‖ ≤ ‖X‖ ^ 2 := by
    rw [pow_two, pow_two]
    exact Matrix.frobenius_norm_mul X X
  have hpow3 (X : Matrix ι ι ℂ) : ‖X ^ 3‖ ≤ ‖X‖ ^ 3 := by
    rw [show X ^ 3 = X ^ 2 * X by noncomm_ring,
      show ‖X‖ ^ 3 = ‖X‖ ^ 2 * ‖X‖ by ring]
    calc
      ‖X ^ 2 * X‖ ≤ ‖X ^ 2‖ * ‖X‖ :=
        Matrix.frobenius_norm_mul (X ^ 2) X
      _ ≤ ‖X‖ ^ 2 * ‖X‖ := by
        gcongr
        exact hpow2 X
  have hid :
      (G + R) ^ 4 - G ^ 4 =
        R * (G + R) ^ 3 +
          (G * R) * (G + R) ^ 2 +
          (G ^ 2 * R) * (G + R) +
          G ^ 3 * R := by
    noncomm_ring
  have h1 : |RHLinalg.rtrace (R * (G + R) ^ 3)| ≤
      ‖R‖ * ‖G + R‖ ^ 3 := by
    calc
      |RHLinalg.rtrace (R * (G + R) ^ 3)| ≤
          ‖R‖ * ‖(G + R) ^ 3‖ :=
        abs_rtrace_mul_le_frobenius R ((G + R) ^ 3)
      _ ≤ ‖R‖ * ‖G + R‖ ^ 3 := by
        gcongr
        exact hpow3 (G + R)
  have h2 : |RHLinalg.rtrace ((G * R) * (G + R) ^ 2)| ≤
      (‖G‖ * ‖R‖) * ‖G + R‖ ^ 2 := by
    calc
      |RHLinalg.rtrace ((G * R) * (G + R) ^ 2)| ≤
          ‖G * R‖ * ‖(G + R) ^ 2‖ :=
        abs_rtrace_mul_le_frobenius (G * R) ((G + R) ^ 2)
      _ ≤ (‖G‖ * ‖R‖) * ‖G + R‖ ^ 2 := by
        gcongr
        · exact Matrix.frobenius_norm_mul G R
        · exact hpow2 (G + R)
  have h3 : |RHLinalg.rtrace ((G ^ 2 * R) * (G + R))| ≤
      (‖G‖ ^ 2 * ‖R‖) * ‖G + R‖ := by
    calc
      |RHLinalg.rtrace ((G ^ 2 * R) * (G + R))| ≤
          ‖G ^ 2 * R‖ * ‖G + R‖ :=
        abs_rtrace_mul_le_frobenius (G ^ 2 * R) (G + R)
      _ ≤ (‖G‖ ^ 2 * ‖R‖) * ‖G + R‖ := by
        gcongr
        calc
          ‖G ^ 2 * R‖ ≤ ‖G ^ 2‖ * ‖R‖ :=
            Matrix.frobenius_norm_mul (G ^ 2) R
          _ ≤ ‖G‖ ^ 2 * ‖R‖ := by
            gcongr
            exact hpow2 G
  have h4 : |RHLinalg.rtrace (G ^ 3 * R)| ≤
      ‖G‖ ^ 3 * ‖R‖ := by
    calc
      |RHLinalg.rtrace (G ^ 3 * R)| ≤ ‖G ^ 3‖ * ‖R‖ :=
        abs_rtrace_mul_le_frobenius (G ^ 3) R
      _ ≤ ‖G‖ ^ 3 * ‖R‖ := by
        gcongr
        exact hpow3 G
  rw [← RHLinalg.rtrace_sub, hid, RHLinalg.rtrace_add,
    RHLinalg.rtrace_add, RHLinalg.rtrace_add]
  calc
    |RHLinalg.rtrace (R * (G + R) ^ 3) +
        RHLinalg.rtrace ((G * R) * (G + R) ^ 2) +
        RHLinalg.rtrace ((G ^ 2 * R) * (G + R)) +
        RHLinalg.rtrace (G ^ 3 * R)| ≤
      |RHLinalg.rtrace (R * (G + R) ^ 3)| +
        |RHLinalg.rtrace ((G * R) * (G + R) ^ 2)| +
        |RHLinalg.rtrace ((G ^ 2 * R) * (G + R))| +
        |RHLinalg.rtrace (G ^ 3 * R)| := by
      let a := RHLinalg.rtrace (R * (G + R) ^ 3)
      let b := RHLinalg.rtrace ((G * R) * (G + R) ^ 2)
      let c := RHLinalg.rtrace ((G ^ 2 * R) * (G + R))
      let d := RHLinalg.rtrace (G ^ 3 * R)
      change |a + b + c + d| ≤ |a| + |b| + |c| + |d|
      calc
        |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
        _ ≤ (|a + b| + |c|) + |d| := by
          gcongr
          exact abs_add_le _ _
        _ ≤ (|a| + |b| + |c|) + |d| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ ‖R‖ * ‖G + R‖ ^ 3 +
        (‖G‖ * ‖R‖) * ‖G + R‖ ^ 2 +
        (‖G‖ ^ 2 * ‖R‖) * ‖G + R‖ +
        ‖G‖ ^ 3 * ‖R‖ := by
      linarith

/-- The guarded/full quartic correction is controlled by one Frobenius
copy of the remote matrix rather than four independent zero sums. -/
theorem remoteCorrectionCyclicTrace4_abs_le_frobenius
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    |remoteCorrectionCyclicTrace4 F T| ≤
      ‖remoteLatticeZeroMatrix F T‖ * ‖fullLatticeZeroMatrix F T‖ ^ 3 +
        (‖guardedLatticeZeroMatrix F T‖ * ‖remoteLatticeZeroMatrix F T‖) *
          ‖fullLatticeZeroMatrix F T‖ ^ 2 +
        (‖guardedLatticeZeroMatrix F T‖ ^ 2 *
          ‖remoteLatticeZeroMatrix F T‖) * ‖fullLatticeZeroMatrix F T‖ +
        ‖guardedLatticeZeroMatrix F T‖ ^ 3 *
          ‖remoteLatticeZeroMatrix F T‖ := by
  rw [remoteCorrectionCyclicTrace4_eq_rtrace_sub]
  have h := rtrace_pow_four_add_sub_bound
    (guardedLatticeZeroMatrix F T) (remoteLatticeZeroMatrix F T)
  rw [guardedZeroMatrix_add_remote_eq_full] at h
  exact h

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
