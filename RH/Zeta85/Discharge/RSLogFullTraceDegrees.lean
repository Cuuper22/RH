import RH.Zeta85.Discharge.RSLogRemoteCorrection

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

/-- One vector-indexed finite gauge sum.  Its tuple index has exactly the
same shape as `rsZeroTupleTerm`; only the restriction to `ZI` remains. -/
def finiteRSGaugeTupleSumAtScale
    (Z : ZeroConfig) (n : ℕ) (T s : ℝ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ) : ℂ :=
  ∑ rho : Fin (n + 1) → ↥(ZeroSide.ZI Z T),
    (∏ j : Fin (n + 1), (Z.mult (rho j : ℂ) : ℂ)) *
      rsGaugeTest Phi (fun j => scaledZeroOrdinateAtScale s (rho j : ℂ))

def finiteRSLogGaugeTupleSum
    (Z : ZeroConfig) (n : ℕ) (T : ℝ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ) : ℂ :=
  finiteRSGaugeTupleSumAtScale Z n T (Real.log T) Phi

/-- Embed a tuple from the finite enlarged dyadic window into the carrier
tuple type used by RS 3.1. -/
def ziTupleToCarrier
    (Z : ZeroConfig) (n : ℕ) (T : ℝ)
    (rho : Fin (n + 1) → ↥(ZeroSide.ZI Z T)) :
    Fin (n + 1) → Z.carrier :=
  fun j => ⟨(rho j : ℂ),
    ZeroSide.mem_carrier_of_mem_ZI Z T (rho j).property⟩

/-- If a height transform is one on the finite dyadic window, the RS tuple
summand is literally the logarithmic finite-gauge summand. -/
theorem rsZeroTupleTerm_ziTupleToCarrier_of_height_one
    {Z : ZeroConfig} {n : ℕ} {T : ℝ}
    (g : Fin (n + 1) → ℝ → ℂ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ)
    (hheight : ∀ j (rho : ↥(ZeroSide.ZI Z T)),
      paperFT (g j) (gammaOf (rho : ℂ) / T) = 1)
    (rho : Fin (n + 1) → ↥(ZeroSide.ZI Z T)) :
    rsZeroTupleTerm Z g Phi T (ziTupleToCarrier Z n T rho) =
      (∏ j : Fin (n + 1), (Z.mult (rho j : ℂ) : ℂ)) *
        rsGaugeTest Phi
          (fun j => scaledZeroOrdinateAtScale (Real.log T) (rho j : ℂ)) := by
  unfold rsZeroTupleTerm ziTupleToCarrier scaledZeroOrdinateAtScale
  simp_rw [hheight]
  simp

/-- Exact finite RS tuple sums are a special case of the smoothed RS sum
whenever the chosen fixed height transforms equal one on the enlarged
dyadic window and vanish on every carrier zero outside it. -/
theorem tsum_rsZeroTupleTerm_eq_finiteRSLogGaugeTupleSum
    {Z : ZeroConfig} {n : ℕ} {T : ℝ}
    (g : Fin (n + 1) → ℝ → ℂ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ)
    (hheight : ∀ j (rho : Z.carrier),
      paperFT (g j) (gammaOf (rho : ℂ) / T) =
        if (rho : ℂ) ∈ ZeroSide.ZI Z T then 1 else 0) :
    ∑' rho, rsZeroTupleTerm Z g Phi T rho =
      finiteRSLogGaugeTupleSum Z n T Phi := by
  classical
  let S : Set (Fin (n + 1) → Z.carrier) :=
    {rho | ∀ j, ((rho j : Z.carrier) : ℂ) ∈ ZeroSide.ZI Z T}
  let e : (Fin (n + 1) → ↥(ZeroSide.ZI Z T)) ≃ Subtype S := {
    toFun := fun rho => ⟨ziTupleToCarrier Z n T rho,
      fun j => (rho j).property⟩
    invFun := fun rho j => ⟨((rho.1 j : Z.carrier) : ℂ), rho.2 j⟩
    left_inv := fun rho => by
      funext j
      apply Subtype.ext
      rfl
    right_inv := fun rho => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      rfl
  }
  have hfinite : S.Finite := by
    have hrange : S ⊆ Set.range (fun rho : Fin (n + 1) →
        ↥(ZeroSide.ZI Z T) => ziTupleToCarrier Z n T rho) := by
      intro rho hrho
      use fun j => ⟨((rho j : Z.carrier) : ℂ), hrho j⟩
      funext j
      apply Subtype.ext
      rfl
    exact Set.Finite.subset (Set.finite_range _) hrange
  letI : Fintype (Subtype S) := hfinite.fintype
  have hout : ∀ rho ∉ hfinite.toFinset,
      rsZeroTupleTerm Z g Phi T rho = 0 := by
    intro rho hrho
    have hrhoS : rho ∉ S := by
      simpa only [Set.Finite.mem_toFinset] using hrho
    have hout : ∃ j, ((rho j : Z.carrier) : ℂ) ∉ ZeroSide.ZI Z T := by
      simpa only [S, Set.mem_ofPred_eq, not_forall] using hrhoS
    obtain ⟨j, hj⟩ := hout
    unfold rsZeroTupleTerm
    have hz : paperFT (g j) (gammaOf (rho j) / T) = 0 := by
      rw [hheight]
      simp [hj]
    have hprod : (∏ a : Fin (n + 1),
        (Z.mult (rho a) : ℂ) *
          paperFT (g a) (gammaOf (rho a) / T)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hz, mul_zero]
    rw [hprod, zero_mul]
  rw [tsum_eq_sum hout]
  rw [Finset.sum_subtype hfinite.toFinset
    (fun rho => hfinite.mem_toFinset)]
  unfold finiteRSLogGaugeTupleSum finiteRSGaugeTupleSumAtScale
  apply (Fintype.sum_equiv e _ _ ?_).symm
  intro rho
  have hpoint := rsZeroTupleTerm_ziTupleToCarrier_of_height_one
    (Z := Z) (n := n) (T := T) g Phi (fun j z => by
      have hz := hheight j
        (⟨(z : ℂ), ZeroSide.mem_carrier_of_mem_ZI Z T z.property⟩ : Z.carrier)
      simpa [z.property] using hz) rho
  change _ = rsZeroTupleTerm Z g Phi T (ziTupleToCarrier Z n T rho)
  exact hpoint.symm

def fullLatticeZeroCycle1
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T : ℝ) (rho : ℂ) : ℂ :=
  fullLatticePairKernel F T rho rho *
    QuarticTransfer.zeroEdgeWeight F T rho

def fullLatticeZeroCycle2
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T : ℝ)
    (rho1 rho2 : ℂ) : ℂ :=
  fullLatticePairKernel F T rho1 rho2 *
    (fullLatticePairKernel F T rho1 rho2 *
      (QuarticTransfer.zeroEdgeWeight F T rho1 *
        QuarticTransfer.zeroEdgeWeight F T rho2))

def fullLatticeZeroCycle3
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T : ℝ)
    (rho1 rho2 rho3 : ℂ) : ℂ :=
  fullLatticePairKernel F T rho1 rho2 *
    (fullLatticePairKernel F T rho2 rho3 *
      (fullLatticePairKernel F T rho1 rho3 *
        (QuarticTransfer.zeroEdgeWeight F T rho1 *
          (QuarticTransfer.zeroEdgeWeight F T rho2 *
            QuarticTransfer.zeroEdgeWeight F T rho3))))

theorem fullLatticeZeroCycle1_eq_rsGaugeTest_atScale
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T w c q s : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (rho : ℂ) :
    (q : ℂ) * fullLatticeZeroCycle1 F T rho =
      (distinguishedEnergyFraction F T : ℂ) * (Z.mult rho : ℂ) *
        rsGaugeTest (n := 0)
          (RSReduction.weightedCyclicSymbol (k := 1) q (F.localProfile T))
          ![scaledZeroOrdinateAtScale s rho] := by
  have h11 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal rho rho
  have hrs := RSReduction.rsGaugeTest_weightedCyclicSymbol_one
    (mu := q) (F.localProfile T) ![scaledZeroOrdinateAtScale s rho]
  unfold fullLatticeZeroCycle1
  rw [h11]
  rw [hrs]
  simp
  ring

theorem cyclicFrequencyTwo_scaled_atScale
    {q s L : ℝ} (hperiod : L = q * s) (rho1 rho2 : ℂ) :
    (q : ℂ) * (2 * Real.pi : ℂ) *
        (scaledZeroOrdinateAtScale s rho2 -
          scaledZeroOrdinateAtScale s rho1) =
      (L : ℂ) * (gammaOf rho2 - gammaOf rho1) := by
  simp [scaledZeroOrdinateAtScale, hperiod]
  field_simp [Real.pi_ne_zero]

theorem fullLatticeZeroCycle2_eq_rsGaugeTest_atScale
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T w c q s : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hq : 0 < q)
    (hperiod : F.period T (F.distinguished T) = q * s)
    (rho1 rho2 : ℂ) :
    (q : ℂ) ^ 2 * fullLatticeZeroCycle2 F T rho1 rho2 =
      (distinguishedEnergyFraction F T : ℂ) ^ 2 *
        ((Z.mult rho1 : ℂ) * (Z.mult rho2 : ℂ)) *
        rsGaugeTest (n := 1)
          (RSReduction.weightedCyclicSymbol (k := 2) q (F.localProfile T))
          ![scaledZeroOrdinateAtScale s rho1,
            scaledZeroOrdinateAtScale s rho2] := by
  have hfactor : fullLatticeZeroCycle2 F T rho1 rho2 =
      (fullLatticePairKernel F T rho1 rho2 *
        QuarticTransfer.zeroEdgeWeight F T rho1) *
      (fullLatticePairKernel F T rho2 rho1 *
        QuarticTransfer.zeroEdgeWeight F T rho2) := by
    unfold fullLatticeZeroCycle2
    rw [fullLatticePairKernel_comm F T rho2 rho1]
    ring
  have h12 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal rho1 rho2
  have h21 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal rho2 rho1
  have heven := localProfile_even F T w c hadm
  have hrs := RSReduction.rsGaugeTest_weightedCyclicSymbol_two
    hq (F.localProfile T) heven
      (localProfile_continuous F T w c hadm)
      (localProfile_hasCompactSupport F T w c hadm)
      ![scaledZeroOrdinateAtScale s rho1,
        scaledZeroOrdinateAtScale s rho2]
  simp at hrs
  rw [cyclicFrequencyTwo_scaled_atScale hperiod rho1 rho2] at hrs
  have hneg : (F.period T (F.distinguished T) : ℂ) *
      (gammaOf rho2 - gammaOf rho1) =
        -((F.period T (F.distinguished T) : ℂ) *
          (gammaOf rho1 - gammaOf rho2)) := by ring
  rw [hneg, Zeta23.Taper.paperFT_neg_of_even heven] at hrs h21
  rw [hfactor, h12, h21, hrs]
  ring

theorem cyclicFrequencyThree_scaled_reversed_atScale
    {q s L : ℝ} (hperiod : L = q * s)
    (rho1 rho2 rho3 : ℂ) :
    RSReduction.cyclicFrequencyThree q
      ![scaledZeroOrdinateAtScale s rho1,
        scaledZeroOrdinateAtScale s rho3,
        scaledZeroOrdinateAtScale s rho2] =
      ![(L : ℂ) * (gammaOf rho1 - gammaOf rho2),
        (L : ℂ) * (gammaOf rho3 - gammaOf rho1),
        (L : ℂ) * (gammaOf rho2 - gammaOf rho3)] := by
  funext j
  fin_cases j <;>
    simp [RSReduction.cyclicFrequencyThree, scaledZeroOrdinateAtScale,
      hperiod] <;>
    field_simp [Real.pi_ne_zero]

theorem fullLatticeZeroCycle3_eq_rsGaugeTest_atScale
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T w c q s : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hq : 0 < q)
    (hperiod : F.period T (F.distinguished T) = q * s)
    (rho1 rho2 rho3 : ℂ) :
    (q : ℂ) ^ 3 * fullLatticeZeroCycle3 F T rho1 rho2 rho3 =
      (distinguishedEnergyFraction F T : ℂ) ^ 3 *
        ((Z.mult rho1 : ℂ) * (Z.mult rho2 : ℂ) *
          (Z.mult rho3 : ℂ)) *
        rsGaugeTest (n := 2)
          (RSReduction.weightedCyclicSymbol (k := 3) q (F.localProfile T))
          ![scaledZeroOrdinateAtScale s rho1,
            scaledZeroOrdinateAtScale s rho3,
            scaledZeroOrdinateAtScale s rho2] := by
  have hfactor : fullLatticeZeroCycle3 F T rho1 rho2 rho3 =
      (fullLatticePairKernel F T rho1 rho2 *
        QuarticTransfer.zeroEdgeWeight F T rho1) *
      (fullLatticePairKernel F T rho2 rho3 *
        QuarticTransfer.zeroEdgeWeight F T rho2) *
      (fullLatticePairKernel F T rho3 rho1 *
        QuarticTransfer.zeroEdgeWeight F T rho3) := by
    unfold fullLatticeZeroCycle3
    rw [fullLatticePairKernel_comm F T rho3 rho1]
    ring
  have h12 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal rho1 rho2
  have h23 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal rho2 rho3
  have h31 := fullLatticePairKernel_mul_zeroEdgeWeight_eq_localProfile
    F T w c hadm hfull hE htotal rho3 rho1
  have hrs := RSReduction.rsGaugeTest_weightedCyclicSymbol_three
    hq (F.localProfile T)
      (localProfile_continuous F T w c hadm)
      (localProfile_hasCompactSupport F T w c hadm)
      ![scaledZeroOrdinateAtScale s rho1,
        scaledZeroOrdinateAtScale s rho3,
        scaledZeroOrdinateAtScale s rho2]
  rw [cyclicFrequencyThree_scaled_reversed_atScale hperiod
    rho1 rho2 rho3, Fin.prod_univ_three] at hrs
  simp at hrs
  rw [hfactor, h12, h23, h31, hrs]
  ring_nf

def fullLatticeZeroKernelCyclicTrace1
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T : ℝ) : ℝ :=
  Complex.re (∑ rho ∈ ZeroSide.ZI Z T,
    fullLatticeZeroCycle1 F T rho)

def fullLatticeZeroKernelCyclicTrace2
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T : ℝ) : ℝ :=
  Complex.re (∑ rho1 ∈ ZeroSide.ZI Z T, ∑ rho2 ∈ ZeroSide.ZI Z T,
    fullLatticeZeroCycle2 F T rho1 rho2)

def fullLatticeZeroKernelCyclicTrace3
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T : ℝ) : ℝ :=
  Complex.re (∑ rho1 ∈ ZeroSide.ZI Z T, ∑ rho2 ∈ ZeroSide.ZI Z T,
    ∑ rho3 ∈ ZeroSide.ZI Z T,
      fullLatticeZeroCycle3 F T rho1 rho2 rho3)

def finiteRSGaugeTrace1AtScale
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T q s : ℝ) : ℝ :=
  Complex.re (∑ rho ∈ ZeroSide.ZI Z T,
    (Z.mult rho : ℂ) *
      rsGaugeTest (n := 0)
        (RSReduction.weightedCyclicSymbol (k := 1) q (F.localProfile T))
        ![scaledZeroOrdinateAtScale s rho])

def finiteRSGaugeTrace2AtScale
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T q s : ℝ) : ℝ :=
  Complex.re (∑ rho1 ∈ ZeroSide.ZI Z T, ∑ rho2 ∈ ZeroSide.ZI Z T,
    ((Z.mult rho1 : ℂ) * (Z.mult rho2 : ℂ)) *
      rsGaugeTest (n := 1)
        (RSReduction.weightedCyclicSymbol (k := 2) q (F.localProfile T))
        ![scaledZeroOrdinateAtScale s rho1,
          scaledZeroOrdinateAtScale s rho2])

def finiteRSGaugeTrace3AtScale
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T q s : ℝ) : ℝ :=
  Complex.re (∑ rho1 ∈ ZeroSide.ZI Z T, ∑ rho2 ∈ ZeroSide.ZI Z T,
    ∑ rho3 ∈ ZeroSide.ZI Z T,
      ((Z.mult rho1 : ℂ) * (Z.mult rho2 : ℂ) * (Z.mult rho3 : ℂ)) *
        rsGaugeTest (n := 2)
          (RSReduction.weightedCyclicSymbol (k := 3) q (F.localProfile T))
          ![scaledZeroOrdinateAtScale s rho1,
            scaledZeroOrdinateAtScale s rho3,
            scaledZeroOrdinateAtScale s rho2])

theorem fullLatticeTrace1_eq_finiteRSGauge_atScale
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T w c q s : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0) :
    q * fullLatticeZeroKernelCyclicTrace1 F T =
      distinguishedEnergyFraction F T *
        finiteRSGaugeTrace1AtScale F T q s := by
  have hsum :
      (q : ℂ) * (∑ rho ∈ ZeroSide.ZI Z T,
        fullLatticeZeroCycle1 F T rho) =
      (distinguishedEnergyFraction F T : ℂ) *
        (∑ rho ∈ ZeroSide.ZI Z T,
          (Z.mult rho : ℂ) *
            rsGaugeTest (n := 0)
              (RSReduction.weightedCyclicSymbol (k := 1) q
                (F.localProfile T))
              ![scaledZeroOrdinateAtScale s rho]) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hrho
    simpa only [mul_assoc] using
      fullLatticeZeroCycle1_eq_rsGaugeTest_atScale
        F T w c q s hadm hfull hE htotal rho
  have hre := congrArg Complex.re hsum
  unfold fullLatticeZeroKernelCyclicTrace1 finiteRSGaugeTrace1AtScale
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hre

theorem fullLatticeTrace2_eq_finiteRSGauge_atScale
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T w c q s : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hq : 0 < q)
    (hperiod : F.period T (F.distinguished T) = q * s) :
    q ^ 2 * fullLatticeZeroKernelCyclicTrace2 F T =
      distinguishedEnergyFraction F T ^ 2 *
        finiteRSGaugeTrace2AtScale F T q s := by
  have hsum :
      (q : ℂ) ^ 2 *
          (∑ rho1 ∈ ZeroSide.ZI Z T, ∑ rho2 ∈ ZeroSide.ZI Z T,
            fullLatticeZeroCycle2 F T rho1 rho2) =
      (distinguishedEnergyFraction F T : ℂ) ^ 2 *
        (∑ rho1 ∈ ZeroSide.ZI Z T, ∑ rho2 ∈ ZeroSide.ZI Z T,
          ((Z.mult rho1 : ℂ) * (Z.mult rho2 : ℂ)) *
            rsGaugeTest (n := 1)
              (RSReduction.weightedCyclicSymbol (k := 2) q
                (F.localProfile T))
              ![scaledZeroOrdinateAtScale s rho1,
                scaledZeroOrdinateAtScale s rho2]) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho1 hrho1
    apply Finset.sum_congr rfl
    intro rho2 hrho2
    simpa only [mul_assoc] using
      fullLatticeZeroCycle2_eq_rsGaugeTest_atScale
        F T w c q s hadm hfull hE htotal hq hperiod rho1 rho2
  have hqcast : (q : ℂ) ^ 2 = ((q ^ 2 : ℝ) : ℂ) := by norm_num
  have hecast : (distinguishedEnergyFraction F T : ℂ) ^ 2 =
      ((distinguishedEnergyFraction F T ^ 2 : ℝ) : ℂ) := by norm_num
  rw [hqcast, hecast] at hsum
  have hre := congrArg Complex.re hsum
  unfold fullLatticeZeroKernelCyclicTrace2 finiteRSGaugeTrace2AtScale
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hre

theorem fullLatticeTrace3_eq_finiteRSGauge_atScale
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T w c q s : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hq : 0 < q)
    (hperiod : F.period T (F.distinguished T) = q * s) :
    q ^ 3 * fullLatticeZeroKernelCyclicTrace3 F T =
      distinguishedEnergyFraction F T ^ 3 *
        finiteRSGaugeTrace3AtScale F T q s := by
  have hsum :
      (q : ℂ) ^ 3 *
          (∑ rho1 ∈ ZeroSide.ZI Z T, ∑ rho2 ∈ ZeroSide.ZI Z T,
            ∑ rho3 ∈ ZeroSide.ZI Z T,
              fullLatticeZeroCycle3 F T rho1 rho2 rho3) =
      (distinguishedEnergyFraction F T : ℂ) ^ 3 *
        (∑ rho1 ∈ ZeroSide.ZI Z T, ∑ rho2 ∈ ZeroSide.ZI Z T,
          ∑ rho3 ∈ ZeroSide.ZI Z T,
            ((Z.mult rho1 : ℂ) * (Z.mult rho2 : ℂ) *
              (Z.mult rho3 : ℂ)) *
              rsGaugeTest (n := 2)
                (RSReduction.weightedCyclicSymbol (k := 3) q
                  (F.localProfile T))
                ![scaledZeroOrdinateAtScale s rho1,
                  scaledZeroOrdinateAtScale s rho3,
                  scaledZeroOrdinateAtScale s rho2]) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho1 hrho1
    apply Finset.sum_congr rfl
    intro rho2 hrho2
    apply Finset.sum_congr rfl
    intro rho3 hrho3
    simpa only [mul_assoc] using
      fullLatticeZeroCycle3_eq_rsGaugeTest_atScale
        F T w c q s hadm hfull hE htotal hq hperiod rho1 rho2 rho3
  have hqcast : (q : ℂ) ^ 3 = ((q ^ 3 : ℝ) : ℂ) := by norm_num
  have hecast : (distinguishedEnergyFraction F T : ℂ) ^ 3 =
      ((distinguishedEnergyFraction F T ^ 3 : ℝ) : ℂ) := by norm_num
  rw [hqcast, hecast] at hsum
  have hre := congrArg Complex.re hsum
  unfold fullLatticeZeroKernelCyclicTrace3 finiteRSGaugeTrace3AtScale
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hre

def finiteRSLogGaugeTrace1
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T : ℝ) : ℝ :=
  finiteRSGaugeTrace1AtScale F T mu (Real.log T)

def finiteRSLogGaugeTrace2
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T : ℝ) : ℝ :=
  finiteRSGaugeTrace2AtScale F T mu (Real.log T)

def finiteRSLogGaugeTrace3
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T : ℝ) : ℝ :=
  finiteRSGaugeTrace3AtScale F T mu (Real.log T)

theorem fullLatticeTrace1_eq_finiteRSLogGauge
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0) :
    mu * fullLatticeZeroKernelCyclicTrace1 F T =
      distinguishedEnergyFraction F T * finiteRSLogGaugeTrace1 F T :=
  fullLatticeTrace1_eq_finiteRSGauge_atScale
    F T w c mu (Real.log T) hadm hfull hE htotal

theorem fullLatticeTrace2_eq_finiteRSLogGauge
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hmu : 0 < mu)
    (hperiod : F.period T (F.distinguished T) = mu * Real.log T) :
    mu ^ 2 * fullLatticeZeroKernelCyclicTrace2 F T =
      distinguishedEnergyFraction F T ^ 2 * finiteRSLogGaugeTrace2 F T :=
  fullLatticeTrace2_eq_finiteRSGauge_atScale
    F T w c mu (Real.log T) hadm hfull hE htotal hmu hperiod

theorem fullLatticeTrace3_eq_finiteRSLogGauge
    {Z : ZeroConfig} {sigma mu p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z sigma mu p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hfull : 0 < QuarticGramFamily.fullLength (σ := sigma) T)
    (hE : F.channelEnergy T (F.distinguished T) ≠ 0)
    (htotal : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hmu : 0 < mu)
    (hperiod : F.period T (F.distinguished T) = mu * Real.log T) :
    mu ^ 3 * fullLatticeZeroKernelCyclicTrace3 F T =
      distinguishedEnergyFraction F T ^ 3 * finiteRSLogGaugeTrace3 F T :=
  fullLatticeTrace3_eq_finiteRSGauge_atScale
    F T w c mu (Real.log T) hadm hfull hE htotal hmu hperiod

end RH.Zeta85.RSPoissonCyclicBridge
