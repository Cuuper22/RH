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

/-- A zero ordinate normalized at an arbitrary positive-frequency scale.
This exposes the normalization choice before the cyclic gauge is formed. -/
def scaledZeroOrdinateAtScale (s : ℝ) (ρ : ℂ) : ℂ :=
  ((s / (2 * Real.pi) : ℝ) : ℂ) * gammaOf ρ

theorem cyclicFrequencyFour_scaled_reversed_atScale
    {q s L : ℝ} (hperiod : L = q * s)
    (ρ₁ ρ₂ ρ₃ ρ₄ : ℂ) :
    RSReduction.cyclicFrequencyFour q
      ![scaledZeroOrdinateAtScale s ρ₁,
        scaledZeroOrdinateAtScale s ρ₄,
        scaledZeroOrdinateAtScale s ρ₃,
        scaledZeroOrdinateAtScale s ρ₂] =
      ![(L : ℂ) * (gammaOf ρ₁ - gammaOf ρ₂),
        (L : ℂ) * (gammaOf ρ₄ - gammaOf ρ₁),
        (L : ℂ) * (gammaOf ρ₃ - gammaOf ρ₄),
        (L : ℂ) * (gammaOf ρ₂ - gammaOf ρ₃)] := by
  funext j
  fin_cases j <;>
    simp [RSReduction.cyclicFrequencyFour, scaledZeroOrdinateAtScale,
      hperiod] <;>
    field_simp [Real.pi_ne_zero]

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

/-! ## Balanced zero weights -/

/-- The positive square root of one normalized zero multiplicity.  Splitting
this weight between the two ends of every edge preserves cyclic traces and
makes Frobenius estimates depend on the total multiplicity only. -/
def zeroVertexWeight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ : ℂ) : ℝ :=
  Real.sqrt ((Z.mult ρ : ℝ) / F.hatDenominator T)

theorem zeroVertexWeight_sq
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) (ρ : ℂ) :
    ((zeroVertexWeight F T ρ : ℂ) ^ 2) =
      QuarticTransfer.zeroEdgeWeight F T ρ := by
  have hnonneg : 0 ≤ (Z.mult ρ : ℝ) / F.hatDenominator T := by
    positivity
  unfold zeroVertexWeight
  rw [← Complex.ofReal_pow, Real.sq_sqrt hnonneg]
  unfold QuarticTransfer.zeroEdgeWeight
  push_cast
  field_simp [hhat.ne']

def balancedKernelMatrix
    {ι : Type*} (K : Matrix ι ι ℂ) (s : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => s i * K i j * s j

def rightWeightedKernelMatrix
    {ι : Type*} (K : Matrix ι ι ℂ) (w : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => K i j * w j

/-- Moving a square edge weight half-way to each adjacent vertex leaves the
fourth cyclic trace unchanged. -/
theorem rtrace_balancedKernelMatrix_pow_four_eq_rightWeighted
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (s w : ι → ℂ)
    (hs : ∀ i, s i ^ 2 = w i) :
    RHLinalg.rtrace ((balancedKernelMatrix K s) ^ 4) =
      RHLinalg.rtrace ((rightWeightedKernelMatrix K w) ^ 4) := by
  rw [rtrace_pow_four_eq_cyclic_generic,
    rtrace_pow_four_eq_cyclic_generic]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  unfold balancedKernelMatrix rightWeightedKernelMatrix
  rw [← hs i, ← hs j, ← hs k, ← hs l]
  ring

def balancedFullLatticeZeroMatrix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    Matrix (↥(ZeroSide.ZI Z T)) (↥(ZeroSide.ZI Z T)) ℂ :=
  fun ρ ρ' =>
    (zeroVertexWeight F T (ρ : ℂ) : ℂ) *
      fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ) *
      (zeroVertexWeight F T (ρ' : ℂ) : ℂ)

def balancedGuardedLatticeZeroMatrix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    Matrix (↥(ZeroSide.ZI Z T)) (↥(ZeroSide.ZI Z T)) ℂ :=
  fun ρ ρ' =>
    (zeroVertexWeight F T (ρ : ℂ) : ℂ) *
      PoissonKernelBridge.canonicalGuardedPairKernel F T
        (ρ : ℂ) (ρ' : ℂ) *
      (zeroVertexWeight F T (ρ' : ℂ) : ℂ)

def balancedRemoteLatticeZeroMatrix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    Matrix (↥(ZeroSide.ZI Z T)) (↥(ZeroSide.ZI Z T)) ℂ :=
  fun ρ ρ' =>
    (zeroVertexWeight F T (ρ : ℂ) : ℂ) *
      remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ) *
      (zeroVertexWeight F T (ρ' : ℂ) : ℂ)

theorem balancedGuarded_add_remote_eq_full
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    balancedGuardedLatticeZeroMatrix F T +
        balancedRemoteLatticeZeroMatrix F T =
      balancedFullLatticeZeroMatrix F T := by
  ext ρ ρ'
  simp only [balancedGuardedLatticeZeroMatrix,
    balancedRemoteLatticeZeroMatrix, balancedFullLatticeZeroMatrix,
    Matrix.add_apply, ← guardedPair_add_remote_eq_full F T]
  ring

theorem rtrace_balancedFull_pow_four_eq_full
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    RHLinalg.rtrace ((balancedFullLatticeZeroMatrix F T) ^ 4) =
      RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 4) := by
  exact rtrace_balancedKernelMatrix_pow_four_eq_rightWeighted
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ => (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (fun ρ => QuarticTransfer.zeroEdgeWeight F T (ρ : ℂ))
    (fun ρ => zeroVertexWeight_sq F T hhat (ρ : ℂ))

theorem rtrace_balancedGuarded_pow_four_eq_guarded
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    RHLinalg.rtrace ((balancedGuardedLatticeZeroMatrix F T) ^ 4) =
      RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 4) := by
  exact rtrace_balancedKernelMatrix_pow_four_eq_rightWeighted
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      PoissonKernelBridge.canonicalGuardedPairKernel F T
        (ρ : ℂ) (ρ' : ℂ))
    (fun ρ => (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (fun ρ => QuarticTransfer.zeroEdgeWeight F T (ρ : ℂ))
    (fun ρ => zeroVertexWeight_sq F T hhat (ρ : ℂ))

theorem remoteCorrection_eq_balanced_rtrace_sub
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    remoteCorrectionCyclicTrace4 F T =
      RHLinalg.rtrace ((balancedFullLatticeZeroMatrix F T) ^ 4) -
        RHLinalg.rtrace ((balancedGuardedLatticeZeroMatrix F T) ^ 4) := by
  rw [remoteCorrectionCyclicTrace4_eq_rtrace_sub,
    rtrace_balancedFull_pow_four_eq_full F T hhat,
    rtrace_balancedGuarded_pow_four_eq_guarded F T hhat]

/-- The fourth-trace perturbation bound after exact square-root balancing. -/
theorem remoteCorrection_abs_le_balanced_frobenius
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
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
          ‖balancedRemoteLatticeZeroMatrix F T‖ := by
  rw [remoteCorrection_eq_balanced_rtrace_sub F T hhat]
  have h := rtrace_pow_four_add_sub_bound
    (balancedGuardedLatticeZeroMatrix F T)
    (balancedRemoteLatticeZeroMatrix F T)
  rw [balancedGuarded_add_remote_eq_full] at h
  exact h

theorem sum_zeroMultiplicities_eq_NIprime
    {Z : ZeroConfig} (T : ℝ) :
    (∑ ρ : ↥(ZeroSide.ZI Z T), Z.mult (ρ : ℂ)) = Z.NIprime T := by
  rw [ZeroConfig.NIprime, ZeroConfig.N]
  change _ = ∑ᶠ ρ ∈ Z.ZIprime T, Z.mult ρ
  calc
    (∑ ρ : ↥(ZeroSide.ZI Z T), Z.mult (ρ : ℂ)) =
        ∑ ρ ∈ ZeroSide.ZI Z T, Z.mult ρ :=
      (Finset.sum_subtype (ZeroSide.ZI Z T)
        (fun _ => Iff.rfl) (fun ρ => Z.mult ρ)).symm
    _ = ∑ᶠ ρ ∈ Z.ZIprime T, Z.mult ρ := by
      rw [finsum_mem_eq_finite_toFinset_sum _
        (ZeroSide.ZIprime_finite Z T)]
      rfl

theorem sum_zeroVertexWeight_norm_sq
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    (∑ ρ : ↥(ZeroSide.ZI Z T),
      ‖(zeroVertexWeight F T (ρ : ℂ) : ℂ)‖ ^ 2) =
      (Z.NIprime T : ℝ) / F.hatDenominator T := by
  calc
    (∑ ρ : ↥(ZeroSide.ZI Z T),
        ‖(zeroVertexWeight F T (ρ : ℂ) : ℂ)‖ ^ 2) =
        ∑ ρ : ↥(ZeroSide.ZI Z T),
          (Z.mult (ρ : ℂ) : ℝ) / F.hatDenominator T := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      unfold zeroVertexWeight
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (by positivity)]
    _ = (∑ ρ : ↥(ZeroSide.ZI Z T),
          (Z.mult (ρ : ℂ) : ℝ)) / F.hatDenominator T := by
      rw [Finset.sum_div]
    _ = (Z.NIprime T : ℝ) / F.hatDenominator T := by
      rw [← Nat.cast_sum, sum_zeroMultiplicities_eq_NIprime]

/-- A uniform entry bound for a kernel becomes a total-weight Frobenius
bound after square-root balancing. -/
theorem norm_balancedKernelMatrix_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (s : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hK : ∀ i j, ‖K i j‖ ≤ C) :
    ‖balancedKernelMatrix K s‖ ≤ C * ∑ i : ι, ‖s i‖ ^ 2 := by
  rw [Zeta23.Assembly.norm_eq_sqrt_frobSq, Real.sqrt_le_iff]
  constructor
  · positivity
  rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq]
  calc
    (∑ i : ι, ∑ j : ι, ‖balancedKernelMatrix K s i j‖ ^ 2) ≤
        ∑ i : ι, ∑ j : ι, (‖s i‖ * C * ‖s j‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      unfold balancedKernelMatrix
      rw [norm_mul, norm_mul]
      gcongr
      exact hK i j
    _ = (C * ∑ i : ι, ‖s i‖ ^ 2) ^ 2 := by
      calc
        (∑ i : ι, ∑ j : ι, (‖s i‖ * C * ‖s j‖) ^ 2) =
            ∑ i : ι, (‖s i‖ ^ 2 * C ^ 2) *
              (∑ j : ι, ‖s j‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (∑ i : ι, ‖s i‖ ^ 2) *
            (C ^ 2 * ∑ j : ι, ‖s j‖ ^ 2) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          ring
        _ = (C * ∑ i : ι, ‖s i‖ ^ 2) ^ 2 := by ring

theorem norm_balancedRemoteMatrix_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T)
    (hscale : 0 ≤ remoteLatticePairScale F T)
    (hpair : ∀ ρ ρ' : ↥(ZeroSide.ZI Z T),
      ‖remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ)‖ ≤
        remoteLatticePairScale F T) :
    ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
      remoteLatticePairScale F T *
        ((Z.NIprime T : ℝ) / F.hatDenominator T) := by
  have h := norm_balancedKernelMatrix_le
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    hscale hpair
  change ‖balancedKernelMatrix
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ))‖ ≤ _
  rw [sum_zeroVertexWeight_norm_sq F T hhat] at h
  exact h

theorem remoteLatticePairScale_nonneg
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hT : 0 < T)
    (hL : 0 < F.period T (F.distinguished T)) :
    0 ≤ remoteLatticePairScale F T := by
  unfold remoteLatticePairScale
    PoissonKernelBridge.distinguishedRemoteTailScale
    PoissonKernelBridge.distinguishedGridStep
  have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT
  have hpi : 0 < (2 * Real.pi : ℝ) := by positivity
  have hgrid : 0 < 2 * Real.pi / F.period T (F.distinguished T) :=
    div_pos hpi hL
  have htail : 0 ≤
      PoissonKernelBridge.distinguishedWindowFourierMajorant F T *
        (((Zeta23.D0 T) ^ 4)⁻¹ +
          ((Zeta23.D0 T) ^ 3)⁻¹ /
            (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
    apply mul_nonneg
    · exact PoissonKernelBridge.distinguishedWindowFourierMajorant_nonneg F T
    · apply add_nonneg
      · exact inv_nonneg.mpr (pow_nonneg hD.le 4)
      · exact div_nonneg (inv_nonneg.mpr (pow_nonneg hD.le 3))
          (mul_nonneg (by norm_num) hgrid.le)
  positivity

theorem eventually_remotePair_le_scale
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : PoissonKernelBridge.DistinguishedGuardedPoissonKernelData F) :
    ∀ᶠ T in atTop, ∀ ρ ρ' : ↥(ZeroSide.ZI Z T),
      ‖remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ)‖ ≤
        remoteLatticePairScale F T := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hguard.periods_pos,
    hguard.windows_smooth, hguard.distinguished_grid_count,
    htail.distinguished_support_half]
      with T hT hperiod hsmooth hcount hsupport
  intro ρ ρ'
  have hL : 0 < F.period T (F.distinguished T) :=
    hperiod (F.distinguished T)
  have hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)) := by
    change ContDiff ℝ 2
      (Complex.ofRealCLM ∘ F.window T (F.distinguished T))
    exact (Complex.ofRealCLM.contDiff.comp
      (hsmooth (F.distinguished T))).of_le (by
        exact (WithTop.coe_le_coe).2
          (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hsupp : ∀ u,
      (F.window T (F.distinguished T) u : ℂ) ≠ 0 →
        |u| ≤ F.period T (F.distinguished T) / 2 := by
    intro u hu
    apply hsupport u
    simpa only [Complex.ofReal_ne_zero] using hu
  simpa only [remoteLatticePairScale] using
    remoteLatticePairKernel_norm_le F T hT hL hcount hwindow hsupp ρ ρ'

/-- Eventual Frobenius control of the balanced remote matrix from the
already-proved pairwise Poisson tail estimate. -/
theorem eventually_balancedRemote_norm_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : PoissonKernelBridge.DistinguishedGuardedPoissonKernelData F)
    (hhat : ∀ᶠ T in atTop, 0 < F.hatDenominator T) :
    ∀ᶠ T in atTop,
      ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
        remoteLatticePairScale F T *
          ((Z.NIprime T : ℝ) / F.hatDenominator T) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hguard.periods_pos,
    eventually_remotePair_le_scale htail hguard, hhat]
      with T hT hperiod hpair hhatT
  exact norm_balancedRemoteMatrix_le F T hhatT
    (remoteLatticePairScale_nonneg F T hT
      (hperiod (F.distinguished T))) hpair

theorem edgeCount_isLittleO_core
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) :
    (fun T => (Zeta23.Assembly.NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hRvM.local_count
  obtain ⟨C, hC⟩ := Zeta23.Tail.eventually_NII_le Z hA₀ hloc
  have hO : (fun T => (Zeta23.Assembly.NII Z T : ℝ)) =O[atTop]
      (fun T => Real.sqrt T * Zeta23.l T) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hC, Zeta23.Assembly.eventually_l_pos] with T hCT hlT
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    simpa [mul_assoc] using hCT
  exact hO.trans_isLittleO
    (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM
      Zeta23.Assembly.isLittleO_sqrt_mul_l_Tl)

theorem eventually_NIprime_le_two_core
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) :
    ∀ᶠ T in atTop,
      (Z.NIprime T : ℝ) ≤ 2 * (Z.N T (2 * T) : ℝ) := by
  have hsmall := (Asymptotics.isLittleO_iff.mp
    (edgeCount_isLittleO_core hRvM)) (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with T hsmallT hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Nat.cast_nonneg _), one_mul] at hsmallT
  rw [Zeta23.Assembly.NIprime_eq Z hT]
  push_cast
  linarith

/-- Under the natural lower normalization, the balanced remote matrix
itself converges to zero in Frobenius norm. -/
theorem balancedRemote_norm_tendsto_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hσ : 0 ≤ σ)
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : PoissonKernelBridge.DistinguishedGuardedPoissonKernelData F)
    (hRvM : RiemannVonMangoldt Z)
    (hhat : ∀ᶠ T in atTop, 1 ≤ F.hatDenominator T) :
    Tendsto (fun T => ‖balancedRemoteLatticeZeroMatrix F T‖)
      atTop (nhds 0) := by
  have hhatPos : ∀ᶠ T in atTop, 0 < F.hatDenominator T :=
    hhat.mono fun T h => lt_of_lt_of_le zero_lt_one h
  have hbound := eventually_balancedRemote_norm_le htail hguard hhatPos
  have hupper : ∀ᶠ T in atTop,
      ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
        2 * ((Z.N T (2 * T) : ℝ) * remoteLatticePairScale F T) := by
    filter_upwards [hbound, hhat,
      eventually_NIprime_le_two_core hRvM,
      eventually_gt_atTop (0 : ℝ), hguard.periods_pos]
        with T hboundT hhatT hNI hT hperiod
    have hscale : 0 ≤ remoteLatticePairScale F T :=
      remoteLatticePairScale_nonneg F T hT
        (hperiod (F.distinguished T))
    have hquot : (Z.NIprime T : ℝ) / F.hatDenominator T ≤
        (Z.NIprime T : ℝ) := by
      exact div_le_self (Nat.cast_nonneg _) hhatT
    calc
      ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
          remoteLatticePairScale F T *
            ((Z.NIprime T : ℝ) / F.hatDenominator T) := hboundT
      _ ≤ remoteLatticePairScale F T * (Z.NIprime T : ℝ) := by
        gcongr
      _ ≤ remoteLatticePairScale F T *
          (2 * (Z.N T (2 * T) : ℝ)) := by
        gcongr
      _ = 2 * ((Z.N T (2 * T) : ℝ) *
          remoteLatticePairScale F T) := by ring
  have hlim : Tendsto (fun T =>
      2 * ((Z.N T (2 * T) : ℝ) * remoteLatticePairScale F T))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (remoteLatticePairScale_negligible
        (F := F) hσ htail hguard hRvM).const_mul 2
  exact squeeze_zero'
    (Eventually.of_forall fun T => norm_nonneg _) hupper hlim

/-! ## Eighth-order remote-tail layer -/

/-- The fourth ordinary derivative, packaged for the `paperFT` decay bound. -/
def derivFour (f : ℝ → ℂ) : ℝ → ℂ :=
  deriv (deriv (deriv (deriv f)))

theorem paperFT_derivFour
    {f : ℝ → ℂ} (hf : ContDiff ℝ 4 f)
    (hsupp : HasCompactSupport f) (z : ℂ) :
    paperFT (derivFour f) z = z ^ 4 * paperFT f z := by
  have hf2 : ContDiff ℝ 2 (deriv (deriv f)) := by
    exact hf.deriv'.deriv'
  rw [derivFour,
    Zeta23.paperFT_deriv_deriv hf2 hsupp.deriv.deriv,
    Zeta23.paperFT_deriv_deriv (hf.of_le (by norm_num)) hsupp]
  ring

theorem norm_paperFT_mul_pow_four_le
    {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 4 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ^ 4 ≤
      Real.exp (|z.im| * Λ) * ∫ u, ‖derivFour f u‖ := by
  have hcs : HasCompactSupport f :=
    Zeta23.hasCompactSupport_of_support_subset_abs hsupp
  have hts := Zeta23.tsupport_subset_of_support_subset_abs hsupp
  have hsupp4 : ∀ u, derivFour f u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have hu3 : u ∈ tsupport (deriv (deriv (deriv f))) :=
      support_deriv_subset (Function.mem_support.mpr hu)
    have hu2 : u ∈ tsupport (deriv (deriv f)) :=
      tsupport_deriv_subset hu3
    have hu1 : u ∈ tsupport (deriv f) :=
      tsupport_deriv_subset hu2
    have hu0 : u ∈ tsupport f := tsupport_deriv_subset hu1
    exact abs_le.mpr (hts hu0)
  have hf2 : ContDiff ℝ 2 (deriv (deriv f)) := hf.deriv'.deriv'
  have hint : Integrable (derivFour f) :=
    (hf2.deriv'.continuous_deriv le_rfl).integrable_of_hasCompactSupport
      hcs.deriv.deriv.deriv.deriv
  have h := Zeta23.norm_paperFT_le hint hsupp4 z
  rw [paperFT_derivFour hf hcs z, norm_mul, norm_pow, mul_comm] at h
  exact h

theorem paperFT_horizontal_decay_four_uniform
    {f : ℝ → ℂ} {Λ B : ℝ}
    (hf : ContDiff ℝ 4 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) (_hB : 0 ≤ B)
    (z : ℂ) (hz : |z.im| ≤ B) (s : ℝ) :
    ‖paperFT f (z - s)‖ * (1 + (z.re - s) ^ 4) ≤
      Real.exp (B * Λ) *
        ((∫ u, ‖f u‖) + (∫ u, ‖derivFour f u‖)) := by
  have hcompact : HasCompactSupport f :=
    Zeta23.hasCompactSupport_of_support_subset_abs hsupp
  have hfi : Integrable f :=
    hf.continuous.integrable_of_hasCompactSupport hcompact
  let w : ℂ := z - s
  have h0 := Zeta23.norm_paperFT_le hfi hsupp w
  have h4 := norm_paperFT_mul_pow_four_le hf hsupp w
  have him : w.im = z.im := by simp [w]
  rw [him] at h0 h4
  have hreabs : |z.re - s| ≤ ‖w‖ := by
    have hwre : w.re = z.re - s := by simp [w]
    rw [← hwre]
    exact Complex.abs_re_le_norm w
  have hre : (z.re - s) ^ 4 ≤ ‖w‖ ^ 4 := by
    calc
      (z.re - s) ^ 4 = ((z.re - s) ^ 2) ^ 2 := by ring
      _ = (|z.re - s| ^ 2) ^ 2 := by rw [sq_abs]
      _ = |z.re - s| ^ 4 := by ring
      _ ≤ ‖w‖ ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hreabs 4
  have h4re :
      ‖paperFT f w‖ * (z.re - s) ^ 4 ≤
        Real.exp (|z.im| * Λ) * ∫ u, ‖derivFour f u‖ :=
    (mul_le_mul_of_nonneg_left hre (norm_nonneg _)).trans h4
  have hexp : Real.exp (|z.im| * Λ) ≤ Real.exp (B * Λ) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz hΛ)
  have hfInt : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
  have hdInt : 0 ≤ ∫ u, ‖derivFour f u‖ :=
    integral_nonneg fun _ => norm_nonneg _
  change ‖paperFT f w‖ * (1 + (z.re - s) ^ 4) ≤ _
  calc
    ‖paperFT f w‖ * (1 + (z.re - s) ^ 4) =
        ‖paperFT f w‖ + ‖paperFT f w‖ * (z.re - s) ^ 4 := by ring
    _ ≤ Real.exp (|z.im| * Λ) * (∫ u, ‖f u‖) +
          Real.exp (|z.im| * Λ) * (∫ u, ‖derivFour f u‖) :=
      add_le_add h0 h4re
    _ ≤ Real.exp (B * Λ) * (∫ u, ‖f u‖) +
          Real.exp (B * Λ) * (∫ u, ‖derivFour f u‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hexp hfInt)
        (mul_le_mul_of_nonneg_right hexp hdInt)
    _ = Real.exp (B * Λ) *
          ((∫ u, ‖f u‖) + (∫ u, ‖derivFour f u‖)) := by ring

theorem paperFT_mul_horizontal_decay_four_uniform
    {f : ℝ → ℂ} {Λ B : ℝ}
    (hf : ContDiff ℝ 4 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B)
    (z z' : ℂ) (hz : |z.im| ≤ B) (hz' : |z'.im| ≤ B)
    (s : ℝ) :
    ‖paperFT f (z - s) * paperFT f (z' - s)‖ *
        ((1 + (z.re - s) ^ 4) * (1 + (z'.re - s) ^ 4)) ≤
      (Real.exp (B * Λ) *
        ((∫ u, ‖f u‖) + (∫ u, ‖derivFour f u‖))) ^ 2 := by
  let C : ℝ := Real.exp (B * Λ) *
    ((∫ u, ‖f u‖) + (∫ u, ‖derivFour f u‖))
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hzBound := paperFT_horizontal_decay_four_uniform
    hf hsupp hΛ hB z hz s
  have hz'Bound := paperFT_horizontal_decay_four_uniform
    hf hsupp hΛ hB z' hz' s
  rw [norm_mul]
  change
    (‖paperFT f (z - s)‖ * ‖paperFT f (z' - s)‖) *
        ((1 + (z.re - s) ^ 4) * (1 + (z'.re - s) ^ 4)) ≤ C ^ 2
  calc
    (‖paperFT f (z - s)‖ * ‖paperFT f (z' - s)‖) *
          ((1 + (z.re - s) ^ 4) * (1 + (z'.re - s) ^ 4)) =
        (‖paperFT f (z - s)‖ * (1 + (z.re - s) ^ 4)) *
          (‖paperFT f (z' - s)‖ * (1 + (z'.re - s) ^ 4)) := by ring
    _ ≤ C * C := mul_le_mul hzBound hz'Bound (by positivity) hC0
    _ = C ^ 2 := by ring

theorem summable_and_norm_tsum_le_inv_pow_eight_grid
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {g : ℕ → E} {C D h : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hh : 0 < h)
    (hg : ∀ k : ℕ, ‖g k‖ ≤ C * ((D + k * h) ^ 8)⁻¹) :
    Summable g ∧
      ‖∑' k : ℕ, g k‖ ≤
        (C * (D ^ 4)⁻¹) *
          ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
  have hmajor : ∀ k : ℕ,
      ‖g k‖ ≤ (C * (D ^ 4)⁻¹) * ((D + k * h) ^ 4)⁻¹ := by
    intro k
    apply (hg k).trans
    have hx : D ≤ D + k * h := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [mul_nonneg hk hh.le]
    have hx0 : 0 < D + k * h := lt_of_lt_of_le hD hx
    have hinv : ((D + k * h) ^ 4)⁻¹ ≤ (D ^ 4)⁻¹ := by
      exact inv_anti₀ (pow_pos hD 4) (pow_le_pow_left₀ hD.le hx 4)
    have heq : ((D + k * h) ^ 8)⁻¹ =
        ((D + k * h) ^ 4)⁻¹ * ((D + k * h) ^ 4)⁻¹ := by
      field_simp [hx0.ne']
    rw [heq]
    calc
      C * (((D + k * h) ^ 4)⁻¹ * ((D + k * h) ^ 4)⁻¹) ≤
          C * ((D ^ 4)⁻¹ * ((D + k * h) ^ 4)⁻¹) := by gcongr
      _ = (C * (D ^ 4)⁻¹) * ((D + k * h) ^ 4)⁻¹ := by ring
  exact Zeta23.Tail.summable_and_norm_tsum_le_inv_pow_four_grid
    (mul_nonneg hC (inv_nonneg.mpr (pow_nonneg hD.le 4))) hD hh hmajor

/-- Fourth-derivative Sobolev mass of the distinguished window. -/
def distinguishedWindowSobolevMassFour
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  (∫ u, ‖(F.window T (F.distinguished T) u : ℂ)‖) +
    ∫ u, ‖derivFour
      (fun x => (F.window T (F.distinguished T) x : ℂ)) u‖

/-- Uniform eighth-order Fourier majorant for a pair of window factors. -/
def distinguishedWindowFourierMajorantEight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  (Real.exp ((1 / 2 : ℝ) *
      (F.period T (F.distinguished T) / 2)) *
    distinguishedWindowSobolevMassFour F T) ^ 2

/-- Eighth-order norm scale of either canonical remote half-lattice. -/
def distinguishedRemoteTailScaleEight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  distinguishedWindowFourierMajorantEight F T *
    ((Zeta23.D0 T ^ 4)⁻¹ *
      ((Zeta23.D0 T ^ 4)⁻¹ +
        (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)))

theorem distinguishedLatticeTerm_le_eightMajorant_on_ZI
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hwindow : ContDiff ℝ 4
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupport : ∀ u,
      (F.window T (F.distinguished T) u : ℂ) ≠ 0 →
        |u| ≤ F.period T (F.distinguished T) / 2)
    (ρ ρ' : ↥(Zeta23.ZeroSide.ZI Z T)) (k : ℤ) :
    ‖PoissonKernelBridge.distinguishedLatticeTerm F T
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) k‖ *
        ((1 + ((gammaOf (ρ : ℂ)).re -
          (T + (k : ℝ) *
            PoissonKernelBridge.distinguishedGridStep F T)) ^ 4) *
         (1 + ((gammaOf (ρ' : ℂ)).re -
          (T + (k : ℝ) *
            PoissonKernelBridge.distinguishedGridStep F T)) ^ 4)) ≤
      distinguishedWindowFourierMajorantEight F T := by
  have hstrip : 0 ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ 1 :=
    Z.strip (ρ : ℂ)
      (Zeta23.ZeroSide.mem_carrier_of_mem_ZI Z T ρ.property)
  have hstrip' : 0 ≤ (ρ' : ℂ).re ∧ (ρ' : ℂ).re ≤ 1 :=
    Z.strip (ρ' : ℂ)
      (Zeta23.ZeroSide.mem_carrier_of_mem_ZI Z T ρ'.property)
  have him : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := by
    have hgamma : (gammaOf (ρ : ℂ)).im = 1 / 2 - (ρ : ℂ).re := by
      simp [gammaOf, Complex.div_I]
    rw [hgamma, abs_le]
    constructor <;> linarith
  have him' : |(gammaOf (ρ' : ℂ)).im| ≤ 1 / 2 := by
    have hgamma : (gammaOf (ρ' : ℂ)).im = 1 / 2 - (ρ' : ℂ).re := by
      simp [gammaOf, Complex.div_I]
    rw [hgamma, abs_le]
    constructor <;> linarith
  have hbound := paperFT_mul_horizontal_decay_four_uniform
    hwindow hsupport (by linarith) (by norm_num)
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) him him'
      (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)
  simpa only [PoissonKernelBridge.distinguishedLatticeTerm,
    PoissonKernelBridge.distinguishedGridStep,
    distinguishedWindowFourierMajorantEight,
    distinguishedWindowSobolevMassFour] using hbound

private theorem norm_le_mul_inv_pow_eight_of_weighted_decay
    {r a b x C : ℝ} (hr : 0 ≤ r) (hx : 0 < x)
    (hdecay : r * ((1 + a ^ 4) * (1 + b ^ 4)) ≤ C)
    (ha : x ≤ |a|) (hb : x ≤ |b|) :
    r ≤ C * (x ^ 8)⁻¹ := by
  have hxa : x ^ 4 ≤ a ^ 4 := by
    calc
      x ^ 4 ≤ |a| ^ 4 := pow_le_pow_left₀ hx.le ha 4
      _ = a ^ 4 := by
        calc
          |a| ^ 4 = (|a| ^ 2) ^ 2 := by ring
          _ = (a ^ 2) ^ 2 := by rw [sq_abs]
          _ = a ^ 4 := by ring
  have hxb : x ^ 4 ≤ b ^ 4 := by
    calc
      x ^ 4 ≤ |b| ^ 4 := pow_le_pow_left₀ hx.le hb 4
      _ = b ^ 4 := by
        calc
          |b| ^ 4 = (|b| ^ 2) ^ 2 := by ring
          _ = (b ^ 2) ^ 2 := by rw [sq_abs]
          _ = b ^ 4 := by ring
  have hweight : x ^ 8 ≤ (1 + a ^ 4) * (1 + b ^ 4) := by
    calc
      x ^ 8 = x ^ 4 * x ^ 4 := by ring
      _ ≤ x ^ 4 * (1 + b ^ 4) :=
        mul_le_mul_of_nonneg_left
          (hxb.trans (le_add_of_nonneg_left (by norm_num))) (pow_nonneg hx.le _)
      _ ≤ (1 + a ^ 4) * (1 + b ^ 4) :=
        mul_le_mul_of_nonneg_right
          (hxa.trans (le_add_of_nonneg_left (by norm_num))) (by positivity)
  have hrx : r * x ^ 8 ≤ C :=
    (mul_le_mul_of_nonneg_left hweight hr).trans hdecay
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hx 8)).2 hrx

theorem lowerLatticeTailFrom_bound_of_weightedDecayEight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T D C : ℝ) (r : ℕ)
    (hL : 0 < F.period T (F.distinguished T))
    (hD : 0 < D) (hC0 : 0 ≤ C)
    (z z' : ℂ)
    (hdecay : ∀ k : ℤ,
      ‖PoissonKernelBridge.distinguishedLatticeTerm F T z z' k‖ *
          ((1 + (z.re -
            (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)) ^ 4) *
           (1 + (z'.re -
            (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)) ^ 4)) ≤ C)
    (hz : T - (r + 1) *
      (2 * Real.pi / F.period T (F.distinguished T)) + D ≤ z.re)
    (hz' : T - (r + 1) *
      (2 * Real.pi / F.period T (F.distinguished T)) + D ≤ z'.re) :
    Summable (fun m : ℕ =>
        PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          (-(((r + m : ℕ) : ℤ) + 1))) ∧
      ‖∑' m : ℕ,
        PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          (-(((r + m : ℕ) : ℤ) + 1))‖ ≤
        (C * (D ^ 4)⁻¹) *
          ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ /
            (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
  let h : ℝ := 2 * Real.pi / F.period T (F.distinguished T)
  have hh : 0 < h := by
    dsimp only [h]
    positivity
  have hz_h : T - (r + 1) * h + D ≤ z.re := by
    simpa only [h] using hz
  have hz'_h : T - (r + 1) * h + D ≤ z'.re := by
    simpa only [h] using hz'
  have hmajor : ∀ m : ℕ,
      ‖PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          (-(((r + m : ℕ) : ℤ) + 1))‖ ≤
        C * ((D + m * h) ^ 8)⁻¹ := by
    intro m
    have hx : 0 < D + m * h := by positivity
    have hfreq :
        T + ((-(((r + m : ℕ) : ℤ) + 1) : ℤ) : ℝ) * h =
          T - (r + 1) * h - m * h := by
      push_cast
      ring
    have ha : D + m * h ≤
        |z.re - (T +
          ((-(((r + m : ℕ) : ℤ) + 1) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonneg]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    have hb : D + m * h ≤
        |z'.re - (T +
          ((-(((r + m : ℕ) : ℤ) + 1) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonneg]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    apply norm_le_mul_inv_pow_eight_of_weighted_decay
      (norm_nonneg _) hx _ ha hb
    simpa only [h, PoissonKernelBridge.distinguishedGridStep] using
      hdecay (-(((r + m : ℕ) : ℤ) + 1))
  obtain ⟨hsum, hnorm⟩ :=
    summable_and_norm_tsum_le_inv_pow_eight_grid hC0 hD hh hmajor
  refine ⟨hsum, ?_⟩
  simpa only [h] using hnorm

theorem upperLatticeTail_bound_of_weightedDecayEight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T D C : ℝ) (n : ℕ)
    (hL : 0 < F.period T (F.distinguished T))
    (hD : 0 < D) (hC0 : 0 ≤ C)
    (z z' : ℂ)
    (hdecay : ∀ k : ℤ,
      ‖PoissonKernelBridge.distinguishedLatticeTerm F T z z' k‖ *
          ((1 + (z.re -
            (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)) ^ 4) *
           (1 + (z'.re -
            (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)) ^ 4)) ≤ C)
    (hz : z.re + D ≤ T + n *
      (2 * Real.pi / F.period T (F.distinguished T)))
    (hz' : z'.re + D ≤ T + n *
      (2 * Real.pi / F.period T (F.distinguished T))) :
    Summable (fun m : ℕ =>
        PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          ((n + m : ℕ) : ℤ)) ∧
      ‖∑' m : ℕ,
        PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          ((n + m : ℕ) : ℤ)‖ ≤
        (C * (D ^ 4)⁻¹) *
          ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ /
            (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
  let h : ℝ := 2 * Real.pi / F.period T (F.distinguished T)
  have hh : 0 < h := by
    dsimp only [h]
    positivity
  have hz_h : z.re + D ≤ T + n * h := by simpa only [h] using hz
  have hz'_h : z'.re + D ≤ T + n * h := by simpa only [h] using hz'
  have hmajor : ∀ m : ℕ,
      ‖PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          ((n + m : ℕ) : ℤ)‖ ≤ C * ((D + m * h) ^ 8)⁻¹ := by
    intro m
    have hx : 0 < D + m * h := by positivity
    have hfreq :
        T + (((n + m : ℕ) : ℤ) : ℝ) * h = T + n * h + m * h := by
      push_cast
      ring
    have ha : D + m * h ≤
        |z.re - (T + (((n + m : ℕ) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonpos]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    have hb : D + m * h ≤
        |z'.re - (T + (((n + m : ℕ) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonpos]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    apply norm_le_mul_inv_pow_eight_of_weighted_decay
      (norm_nonneg _) hx _ ha hb
    simpa only [h, PoissonKernelBridge.distinguishedGridStep] using
      hdecay ((n + m : ℕ) : ℤ)
  obtain ⟨hsum, hnorm⟩ :=
    summable_and_norm_tsum_le_inv_pow_eight_grid hC0 hD hh hmajor
  refine ⟨hsum, ?_⟩
  simpa only [h] using hnorm

/-- The balanced pair scale obtained from four integrations by parts in
each Fourier factor. -/
def remoteLatticePairScaleEight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  ‖PoissonKernelBridge.distinguishedLatticeScale F T‖ *
    (distinguishedRemoteTailScaleEight F T +
      distinguishedRemoteTailScaleEight F T)

theorem remoteLatticePairKernel_norm_le_eight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hT : 0 < T)
    (hL : 0 < F.period T (F.distinguished T))
    (hcount : F.channelDim T (F.distinguished T) =
      ⌊F.period T (F.distinguished T) * T / (2 * Real.pi)⌋₊)
    (hwindow : ContDiff ℝ 4
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupport : ∀ u,
      (F.window T (F.distinguished T) u : ℂ) ≠ 0 →
        |u| ≤ F.period T (F.distinguished T) / 2)
    (ρ ρ' : ↥(Zeta23.ZeroSide.ZI Z T)) :
    ‖remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ)‖ ≤
      remoteLatticePairScaleEight F T := by
  let n := F.channelDim T (F.distinguished T)
  let r := PoissonKernelBridge.distinguishedEndpointGuardWidth F T
  let C := distinguishedWindowFourierMajorantEight F T
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
  have hdecay := distinguishedLatticeTerm_le_eightMajorant_on_ZI
    F T hL hwindow hsupport ρ ρ'
  have hC0 : 0 ≤ C := by
    dsimp only [C, distinguishedWindowFourierMajorantEight]
    positivity
  have hlower := lowerLatticeTailFrom_bound_of_weightedDecayEight
    F T (Zeta23.D0 T) C r hL hD hC0
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) hdecay
      (by simpa only [PoissonKernelBridge.distinguishedGridStep] using hdist.1)
      (by simpa only [PoissonKernelBridge.distinguishedGridStep] using hdist'.1)
  have hupper := upperLatticeTail_bound_of_weightedDecayEight
    F T (Zeta23.D0 T) C (n + r) hL hD hC0
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) hdecay
      (by simpa only [n, r, Nat.cast_add,
        PoissonKernelBridge.distinguishedGridStep] using hdist.2)
      (by simpa only [n, r, Nat.cast_add,
        PoissonKernelBridge.distinguishedGridStep] using hdist'.2)
  have hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)) :=
    hasCompactSupport_of_support_subset_abs hsupport
  have hwindow2 : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)) :=
    hwindow.of_le (by norm_num)
  have hsum : Summable (PoissonKernelBridge.distinguishedLatticeTerm F T
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))) :=
    (PoissonKernelBridge.hasSum_distinguishedLatticeTerm_alias_of_hasCompactSupport
      F T hL hwindow2 hcompact
        (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))).2.summable
  rw [remoteLatticePairKernel_eq_scaled_remoteTails F T ρ ρ' hsum,
    norm_mul]
  unfold remoteLatticePairScaleEight
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
      _ ≤ distinguishedRemoteTailScaleEight F T +
          distinguishedRemoteTailScaleEight F T := by
        gcongr
        · simpa only [C, r, distinguishedRemoteTailScaleEight,
            PoissonKernelBridge.distinguishedGridStep, mul_assoc] using hlower.2
        · simpa only [C, n, r, distinguishedRemoteTailScaleEight,
            PoissonKernelBridge.distinguishedGridStep, Nat.add_assoc,
            mul_assoc] using hupper.2
  · exact norm_nonneg _

theorem remoteLatticePairScaleEight_nonneg
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hT : 0 < T)
    (hL : 0 < F.period T (F.distinguished T)) :
    0 ≤ remoteLatticePairScaleEight F T := by
  unfold remoteLatticePairScaleEight distinguishedRemoteTailScaleEight
    PoissonKernelBridge.distinguishedGridStep
    distinguishedWindowFourierMajorantEight
  have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT
  have hgrid : 0 < 2 * Real.pi / F.period T (F.distinguished T) := by
    positivity
  positivity

theorem eventually_remotePair_le_scale_eight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : PoissonKernelBridge.DistinguishedGuardedPoissonKernelData F) :
    ∀ᶠ T in atTop, ∀ ρ ρ' : ↥(ZeroSide.ZI Z T),
      ‖remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ)‖ ≤
        remoteLatticePairScaleEight F T := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hguard.periods_pos,
    hguard.windows_smooth, hguard.distinguished_grid_count,
    htail.distinguished_support_half]
      with T hT hperiod hsmooth hcount hsupport
  intro ρ ρ'
  have hL : 0 < F.period T (F.distinguished T) :=
    hperiod (F.distinguished T)
  have hwindow : ContDiff ℝ 4
      (fun u => (F.window T (F.distinguished T) u : ℂ)) := by
    change ContDiff ℝ 4
      (Complex.ofRealCLM ∘ F.window T (F.distinguished T))
    exact (Complex.ofRealCLM.contDiff.comp
      (hsmooth (F.distinguished T))).of_le (by
        exact (WithTop.coe_le_coe).2
          (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hsupp : ∀ u,
      (F.window T (F.distinguished T) u : ℂ) ≠ 0 →
        |u| ≤ F.period T (F.distinguished T) / 2 := by
    intro u hu
    apply hsupport u
    simpa only [Complex.ofReal_ne_zero] using hu
  exact remoteLatticePairKernel_norm_le_eight
    F T hT hL hcount hwindow hsupp ρ ρ'

/-- Eventual balanced Frobenius control using the eighth-order pair scale. -/
theorem eventually_balancedRemote_norm_le_eight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : PoissonKernelBridge.DistinguishedGuardedPoissonKernelData F)
    (hhat : ∀ᶠ T in atTop, 0 < F.hatDenominator T) :
    ∀ᶠ T in atTop,
      ‖balancedRemoteLatticeZeroMatrix F T‖ ≤
        remoteLatticePairScaleEight F T *
          ((Z.NIprime T : ℝ) / F.hatDenominator T) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hguard.periods_pos,
    eventually_remotePair_le_scale_eight htail hguard, hhat]
      with T hT hperiod hpair hhatT
  have h := norm_balancedKernelMatrix_le
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (remoteLatticePairScaleEight_nonneg F T hT
      (hperiod (F.distinguished T))) hpair
  change ‖balancedKernelMatrix
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ))‖ ≤ _
  rw [sum_zeroVertexWeight_norm_sq F T hhatT] at h
  exact h

/-- Any fixed logarithmic power is absorbed by the power saving left by
`μ < 1`; this is the six-log version needed by the quartic perturbation. -/
theorem tendsto_rpow_sub_half_mul_log_pow_six
    {μ : ℝ} (hμ : μ < 1) :
    Tendsto (fun T : ℝ =>
      T ^ (μ / 2 - 1 / 2 : ℝ) * Real.log T ^ 6) atTop (nhds 0) := by
  let δ : ℝ := (1 - μ) / 2
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
  have hexp : μ / 2 - 1 / 2 = -δ := by
    dsimp only [δ]
    ring
  rw [hexp, Real.rpow_neg hT0.le]
  simp only [div_eq_mul_inv]
  ring

theorem distinguishedWindowFourierMajorantEight_le
    {Z : ZeroConfig} {σ μ p c T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 ≤ μ) (hT : 1 < T)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hmass : distinguishedWindowSobolevMassFour F T ≤ c * Zeta23.l T) :
    distinguishedWindowFourierMajorantEight F T ≤
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
  have hmass0 : 0 ≤ distinguishedWindowSobolevMassFour F T := by
    unfold distinguishedWindowSobolevMassFour
    positivity
  have hcl0 : 0 ≤ c * Zeta23.l T := hmass0.trans hmass
  unfold distinguishedWindowFourierMajorantEight
  calc
    (Real.exp ((1 / 2 : ℝ) *
          (F.period T (F.distinguished T) / 2)) *
        distinguishedWindowSobolevMassFour F T) ^ 2 =
        (Real.exp ((1 / 2 : ℝ) *
          (F.period T (F.distinguished T) / 2))) ^ 2 *
          distinguishedWindowSobolevMassFour F T ^ 2 := by ring
    _ ≤ T ^ (μ / 2 : ℝ) * (c * Zeta23.l T) ^ 2 :=
      mul_le_mul hexp ((sq_le_sq₀ hmass0 hcl0).2 hmass)
        (sq_nonneg _) (by positivity)
    _ = c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2 := by ring

theorem distinguishedRemoteTailGridFactorEight_le
    {Z : ZeroConfig} {σ μ p T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 < μ) (hT : 1 ≤ T) (hl : 1 ≤ Zeta23.l T)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T) :
    (Zeta23.D0 T ^ 4)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 7)⁻¹ := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT0
  have hold := PoissonKernelBridge.distinguishedRemoteTailGridFactor_le
    F hμ hT hl hperiod
  calc
    (Zeta23.D0 T ^ 4)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (Zeta23.D0 T ^ 4)⁻¹ *
        ((1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 3)⁻¹) := by
          gcongr
    _ = (1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 7)⁻¹ := by
      field_simp [hD.ne']

/-- Three zero-count factors still leave the full power saving supplied by
the eighth-order pair tail. -/
theorem N_cube_mul_distinguishedRemoteTailScaleEight_le
    {Z : ZeroConfig} {σ μ p c T : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 < μ) (hT : 1 < T) (hl : 1 ≤ Zeta23.l T)
    (hperiod : F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hN : (Z.N T (2 * T) : ℝ) ≤ T * Zeta23.l T)
    (hMaj : distinguishedWindowFourierMajorantEight F T ≤
      c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2)
    (hTail : (Zeta23.D0 T ^ 4)⁻¹ *
        ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)) ≤
      (1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 7)⁻¹) :
    (Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleEight F T ≤
      c ^ 2 * (1 + μ) * T ^ (μ / 2 - 1 / 2 : ℝ) *
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
  have htail0 : 0 ≤ (Zeta23.D0 T ^ 4)⁻¹ *
      ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
        (3 * PoissonKernelBridge.distinguishedGridStep F T)) := by
    positivity
  have hmaj0 : 0 ≤ distinguishedWindowFourierMajorantEight F T := by
    unfold distinguishedWindowFourierMajorantEight
    positivity
  have hrightMaj0 :
      0 ≤ c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2 := by
    positivity
  have hNpow : (Z.N T (2 * T) : ℝ) ^ 3 ≤
      (T * Zeta23.l T) ^ 3 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hN 3
  have hraw :
      (Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleEight F T ≤
        (T * Zeta23.l T) ^ 3 *
          ((c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2) *
            ((1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 7)⁻¹)) := by
    unfold distinguishedRemoteTailScaleEight
    calc
      (Z.N T (2 * T) : ℝ) ^ 3 *
          (distinguishedWindowFourierMajorantEight F T *
            ((Zeta23.D0 T ^ 4)⁻¹ *
              ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
                (3 * PoissonKernelBridge.distinguishedGridStep F T)))) ≤
          (T * Zeta23.l T) ^ 3 *
            (distinguishedWindowFourierMajorantEight F T *
              ((Zeta23.D0 T ^ 4)⁻¹ *
                ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
                  (3 * PoissonKernelBridge.distinguishedGridStep F T)))) :=
        mul_le_mul_of_nonneg_right hNpow (mul_nonneg hmaj0 htail0)
      _ ≤ (T * Zeta23.l T) ^ 3 *
          ((c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2) *
            ((Zeta23.D0 T ^ 4)⁻¹ *
              ((Zeta23.D0 T ^ 4)⁻¹ + (Zeta23.D0 T ^ 3)⁻¹ /
                (3 * PoissonKernelBridge.distinguishedGridStep F T)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hMaj htail0) (by positivity)
      _ ≤ (T * Zeta23.l T) ^ 3 *
          ((c ^ 2 * T ^ (μ / 2 : ℝ) * Zeta23.l T ^ 2) *
            ((1 + μ) * Zeta23.l T * (Zeta23.D0 T ^ 7)⁻¹)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hTail hrightMaj0) (by positivity)
  have hDsquare : Zeta23.D0 T ^ 2 = T := Real.sq_sqrt hT0.le
  have hD7 : Zeta23.D0 T ^ 7 = Zeta23.D0 T * T ^ 3 := by
    calc
      Zeta23.D0 T ^ 7 = Zeta23.D0 T * (Zeta23.D0 T ^ 2) ^ 3 := by ring
      _ = Zeta23.D0 T * T ^ 3 := by rw [hDsquare]
  have hpower :
      T ^ 3 * T ^ (μ / 2 : ℝ) * (Zeta23.D0 T ^ 7)⁻¹ =
        T ^ (μ / 2 - 1 / 2 : ℝ) := by
    rw [hD7]
    have hcancel :
        T ^ 3 * T ^ (μ / 2 : ℝ) * (Zeta23.D0 T * T ^ 3)⁻¹ =
          T ^ (μ / 2 : ℝ) / Zeta23.D0 T := by
      field_simp
    rw [hcancel, Zeta23.D0, Real.sqrt_eq_rpow,
      ← Real.rpow_sub hT0]
  calc
    (Z.N T (2 * T) : ℝ) ^ 3 * distinguishedRemoteTailScaleEight F T ≤ _ := hraw
    _ = c ^ 2 * (1 + μ) *
          (T ^ 3 * T ^ (μ / 2 : ℝ) * (Zeta23.D0 T ^ 7)⁻¹) *
            Zeta23.l T ^ 6 := by ring
    _ = c ^ 2 * (1 + μ) * T ^ (μ / 2 - 1 / 2 : ℝ) *
          Zeta23.l T ^ 6 := by rw [hpower]
    _ ≤ c ^ 2 * (1 + μ) * T ^ (μ / 2 - 1 / 2 : ℝ) *
          Real.log T ^ 6 := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ hl0 hlLog 6
      · positivity

theorem tendsto_N_cube_mul_distinguishedRemoteTailScaleEight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 < μ) (hμ1 : μ < 1) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hmass : (fun T => distinguishedWindowSobolevMassFour F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T => (Z.N T (2 * T) : ℝ) ^ 3 *
      distinguishedRemoteTailScaleEight F T) atTop (nhds 0) := by
  obtain ⟨c, hc⟩ := hmass.bound
  have hlim : Tendsto (fun T =>
      c ^ 2 * (1 + μ) *
        (T ^ (μ / 2 - 1 / 2 : ℝ) * Real.log T ^ 6))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => c ^ 2 * (1 + μ)) atTop
        (nhds (c ^ 2 * (1 + μ))) := tendsto_const_nhds
    simpa only [mul_zero] using
      hconst.mul (tendsto_rpow_sub_half_mul_log_pow_six hμ1)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hperiod, Zeta23.Assembly.eventually_one_le_l,
      eventually_gt_atTop (1 : ℝ)] with T hperiodT hl hT
    have hgrid : 0 < PoissonKernelBridge.distinguishedGridStep F T := by
      unfold PoissonKernelBridge.distinguishedGridStep
      rw [hperiodT]
      positivity
    unfold distinguishedRemoteTailScaleEight
    apply mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3)
    apply mul_nonneg
    · unfold distinguishedWindowFourierMajorantEight
      positivity
    · apply mul_nonneg
      · exact inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg T) 4)
      · apply add_nonneg
        · exact inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg T) 4)
        · exact div_nonneg
            (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg T) 3))
            (mul_nonneg (by norm_num) hgrid.le)
  · filter_upwards [hc, hperiod, Zeta23.Assembly.eventually_one_le_l,
      Zeta23.Assembly.eventually_N_le Z hRvM,
      eventually_gt_atTop (1 : ℝ)] with T hmassT hperiodT hl hN hT
    have hmass0 : 0 ≤ distinguishedWindowSobolevMassFour F T := by
      unfold distinguishedWindowSobolevMassFour
      positivity
    have hl0 : 0 ≤ Zeta23.l T := le_trans zero_le_one hl
    have hmassPoint :
        distinguishedWindowSobolevMassFour F T ≤ c * Zeta23.l T := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hmass0,
        abs_of_nonneg hl0] using hmassT
    have hMaj := distinguishedWindowFourierMajorantEight_le
      F hμ.le hT hperiodT hmassPoint
    have hTail := distinguishedRemoteTailGridFactorEight_le
      F hμ hT.le hl hperiodT
    simpa only [mul_assoc] using
      N_cube_mul_distinguishedRemoteTailScaleEight_le
        F hμ hT hl hperiodT hN hMaj hTail

/-- The complete eighth-order pair scale remains negligible after three
dyadic zero-count factors. -/
theorem remoteLatticePairScaleEight_cube_negligible
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hσ : 0 ≤ σ)
    (hμ : 0 < μ) (hμ1 : μ < 1) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = μ * Zeta23.l T)
    (hmass : (fun T => distinguishedWindowSobolevMassFour F T) =O[atTop]
      Zeta23.l) :
    Tendsto (fun T => (Z.N T (2 * T) : ℝ) ^ 3 *
      remoteLatticePairScaleEight F T) atTop (nhds 0) := by
  have htail := tendsto_N_cube_mul_distinguishedRemoteTailScaleEight
    F hμ hμ1 hRvM hperiod hmass
  have hconst : Tendsto (fun _ : ℝ => 2 * (σ / μ)) atTop
      (nhds (2 * (σ / μ))) := tendsto_const_nhds
  have hlim := hconst.mul htail
  simpa only [mul_zero] using hlim.congr' (by
    filter_upwards [hperiod, Zeta23.Assembly.eventually_one_le_l]
      with T hperiodT hl
    have hlpos : 0 < Zeta23.l T := lt_of_lt_of_le zero_lt_one hl
    rw [remoteLatticePairScaleEight,
      norm_distinguishedLatticeScale_eq_ratio F T hσ hμ hlpos hperiodT]
    ring)

/-! ## Completed-kernel growth -/

theorem norm_paperFT_localProfile_le_exp
    {r : ℝ → ℝ} (hint : Integrable r)
    (hnonneg : ∀ x, 0 ≤ r x)
    (hsupp : tsupport r ⊆ Icc (-(1 : ℝ) / 2) (1 / 2))
    (hmean : ∫ x, r x = 1) (z : ℂ) :
    ‖paperFT (fun x => (r x : ℂ)) z‖ ≤ Real.exp (|z.im| / 2) := by
  have hintC : Integrable (fun x => (r x : ℂ)) := hint.ofReal
  have hsuppC : ∀ u, (r u : ℂ) ≠ 0 → |u| ≤ (1 : ℝ) / 2 := by
    intro u hu
    have hur : r u ≠ 0 := by simpa only [Complex.ofReal_ne_zero] using hu
    have hucl : u ∈ tsupport r := subset_closure (Function.mem_support.mpr hur)
    have huIcc := hsupp hucl
    rw [abs_le]
    constructor <;> linarith [huIcc.1, huIcc.2]
  have h := Zeta23.norm_paperFT_le hintC hsuppC z
  have hintnorm : (∫ x, ‖(r x : ℂ)‖) = 1 := by
    calc
      (∫ x, ‖(r x : ℂ)‖) = ∫ x, r x := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hnonneg x)]
      _ = 1 := hmean
  rw [hintnorm, mul_one] at h
  simpa only [div_eq_mul_inv, one_mul] using h

/-- Uniform completed-pair growth over the enlarged zero window. -/
theorem fullLatticePairKernel_norm_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T)
    (hE : 0 < F.channelEnergy T (F.distinguished T))
    (hprofileInt : Integrable (F.localProfile T))
    (hprofileNonneg : ∀ x, 0 ≤ F.localProfile T x)
    (hprofileSupport : tsupport (F.localProfile T) ⊆
      Icc (-(1 : ℝ) / 2) (1 / 2))
    (hprofileMean : ∫ x, F.localProfile T x = 1)
    (ρ ρ' : ↥(Zeta23.ZeroSide.ZI Z T)) :
    ‖fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ)‖ ≤
      QuarticGramFamily.fullLength (σ := σ) T *
        F.channelEnergy T (F.distinguished T) *
          Real.exp (F.period T (F.distinguished T) / 2) := by
  have hstrip : 0 ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ 1 :=
    Z.strip (ρ : ℂ)
      (Zeta23.ZeroSide.mem_carrier_of_mem_ZI Z T ρ.property)
  have hstrip' : 0 ≤ (ρ' : ℂ).re ∧ (ρ' : ℂ).re ≤ 1 :=
    Z.strip (ρ' : ℂ)
      (Zeta23.ZeroSide.mem_carrier_of_mem_ZI Z T ρ'.property)
  let z : ℂ := (F.period T (F.distinguished T) : ℂ) *
    (gammaOf (ρ : ℂ) - gammaOf (ρ' : ℂ))
  have himdiff :
      (gammaOf (ρ : ℂ) - gammaOf (ρ' : ℂ)).im =
        (ρ' : ℂ).re - (ρ : ℂ).re := by
    simp [gammaOf, Complex.div_I]
  have him : |z.im| ≤ F.period T (F.distinguished T) := by
    have hdiff : |(ρ' : ℂ).re - (ρ : ℂ).re| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    dsimp only [z]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, himdiff, abs_mul, abs_of_pos hadm.L_pos]
    nlinarith [mul_le_mul_of_nonneg_left hdiff hadm.L_pos.le]
  have hft := norm_paperFT_localProfile_le_exp
    hprofileInt hprofileNonneg hprofileSupport hprofileMean z
  have hexp : Real.exp (|z.im| / 2) ≤
      Real.exp (F.period T (F.distinguished T) / 2) := by
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right him (by norm_num))
  rw [fullLatticePairKernel_eq_localProfile F T w c hadm hfull hE.ne']
  change ‖((QuarticGramFamily.fullLength (σ := σ) T *
      F.channelEnergy T (F.distinguished T) : ℝ) : ℂ) *
    paperFT (fun x => (F.localProfile T x : ℂ)) z‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos hfull hE)]
  calc
    (QuarticGramFamily.fullLength (σ := σ) T *
        F.channelEnergy T (F.distinguished T)) *
        ‖paperFT (fun x => (F.localProfile T x : ℂ)) z‖ ≤
      (QuarticGramFamily.fullLength (σ := σ) T *
        F.channelEnergy T (F.distinguished T)) *
        Real.exp (|z.im| / 2) :=
      mul_le_mul_of_nonneg_left hft (mul_pos hfull hE).le
    _ ≤ (QuarticGramFamily.fullLength (σ := σ) T *
        F.channelEnergy T (F.distinguished T)) *
        Real.exp (F.period T (F.distinguished T) / 2) :=
      mul_le_mul_of_nonneg_left hexp (mul_pos hfull hE).le
    _ = _ := by ring

/-- Square-root balancing cancels the physical length and total-energy
normalization from the completed kernel. -/
theorem norm_balancedFullLatticeZeroMatrix_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T)
    (hE : 0 < F.channelEnergy T (F.distinguished T))
    (htotal : 0 < ∫ u : ℝ, F.windowEnergy T u)
    (hprofileInt : Integrable (F.localProfile T))
    (hprofileNonneg : ∀ x, 0 ≤ F.localProfile T x)
    (hprofileSupport : tsupport (F.localProfile T) ⊆
      Icc (-(1 : ℝ) / 2) (1 / 2))
    (hprofileMean : ∫ x, F.localProfile T x = 1) :
    ‖balancedFullLatticeZeroMatrix F T‖ ≤
      distinguishedEnergyFraction F T *
        Real.exp (F.period T (F.distinguished T) / 2) *
          (Z.NIprime T : ℝ) := by
  let C : ℝ := QuarticGramFamily.fullLength (σ := σ) T *
    F.channelEnergy T (F.distinguished T) *
      Real.exp (F.period T (F.distinguished T) / 2)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hpair : ∀ ρ ρ' : ↥(ZeroSide.ZI Z T),
      ‖fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ)‖ ≤ C := by
    intro ρ ρ'
    exact fullLatticePairKernel_norm_le F T w c hadm hfull hE
      hprofileInt hprofileNonneg hprofileSupport hprofileMean ρ ρ'
  have hhat : 0 < F.hatDenominator T := by
    unfold QuarticGramFamily.hatDenominator
    positivity
  have h := norm_balancedKernelMatrix_le
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ)) hC hpair
  change ‖balancedKernelMatrix
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ : ↥(ZeroSide.ZI Z T) =>
      (zeroVertexWeight F T (ρ : ℂ) : ℂ))‖ ≤ _
  rw [sum_zeroVertexWeight_norm_sq F T hhat] at h
  calc
    ‖balancedKernelMatrix
      (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
        fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
      (fun ρ : ↥(ZeroSide.ZI Z T) =>
        (zeroVertexWeight F T (ρ : ℂ) : ℂ))‖ ≤
        C * ((Z.NIprime T : ℝ) / F.hatDenominator T) := h
    _ = distinguishedEnergyFraction F T *
        Real.exp (F.period T (F.distinguished T) / 2) *
          (Z.NIprime T : ℝ) := by
      unfold C distinguishedEnergyFraction QuarticGramFamily.hatDenominator
      field_simp [hfull.ne', htotal.ne']

theorem fullLatticeZeroCycle4_eq_rsGaugeTest_atScale
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c q s : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := σ) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hq : 0 < q)
    (hperiod : F.period T (F.distinguished T) = q * s)
    (ρ₁ ρ₂ ρ₃ ρ₄ : ℂ) :
    (q : ℂ) ^ 4 * fullLatticeZeroCycle4 F T ρ₁ ρ₂ ρ₃ ρ₄ =
      (distinguishedEnergyFraction F T : ℂ) ^ 4 *
        ((Z.mult ρ₁ : ℂ) * (Z.mult ρ₂ : ℂ) *
          (Z.mult ρ₃ : ℂ) * (Z.mult ρ₄ : ℂ)) *
        rsGaugeTest (n := 3)
          (RSReduction.weightedCyclicSymbol (k := 4) q (F.localProfile T))
          ![scaledZeroOrdinateAtScale s ρ₁,
            scaledZeroOrdinateAtScale s ρ₄,
            scaledZeroOrdinateAtScale s ρ₃,
            scaledZeroOrdinateAtScale s ρ₂] := by
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
    hq (F.localProfile T)
      (localProfile_continuous F T w c hadm)
      (localProfile_hasCompactSupport F T w c hadm)
      ![scaledZeroOrdinateAtScale s ρ₁,
        scaledZeroOrdinateAtScale s ρ₄,
        scaledZeroOrdinateAtScale s ρ₃,
        scaledZeroOrdinateAtScale s ρ₂]
  rw [cyclicFrequencyFour_scaled_reversed_atScale hperiod
    ρ₁ ρ₂ ρ₃ ρ₄, Fin.prod_univ_four] at hrs
  simp at hrs
  rw [hfactor, h12, h23, h34, h41, hrs]
  ring_nf

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
