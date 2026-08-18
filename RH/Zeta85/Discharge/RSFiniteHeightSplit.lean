import RH.Zeta85.Discharge.RSSlowDiagonal
import RH.Zeta85.Discharge.RSLogFullTraceDegrees

/-!
# Exact finite/remote split for RS height weights

The compact physical height tests in RS have Fourier tails, so their all-zero
sum is not literally the enlarged-window sum.  This module makes the needed
split exact: the inside term is a finite tuple sum over `ZI`, and the only
remaining term is the complementary remote-zero `tsum`.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def finiteHeightWeightedRSGaugeTupleSum
    (Z : ZeroConfig) (n : ℕ) (T : ℝ)
    (g : Fin (n + 1) → ℝ → ℂ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ) : ℂ :=
  ∑' rho : Fin (n + 1) → ↥(ZeroSide.ZI Z T),
    (∏ j : Fin (n + 1),
      (Z.mult (rho j : ℂ) : ℂ) *
        paperFT (g j) (gammaOf (rho j : ℂ) / T)) *
      rsGaugeTest Phi
        (fun j => scaledZeroOrdinateAtScale (Real.log T) (rho j : ℂ))

def rsInsideTupleSet
    (Z : ZeroConfig) (n : ℕ) (T : ℝ) :
    Set (Fin (n + 1) → Z.carrier) :=
  {rho | ∀ j, ((rho j : Z.carrier) : ℂ) ∈ ZeroSide.ZI Z T}

def remoteHeightWeightedRSTupleTail
    (Z : ZeroConfig) (n : ℕ) (T : ℝ)
    (g : Fin (n + 1) → ℝ → ℂ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ) : ℂ :=
  ∑' rho : ↥((rsInsideTupleSet Z n T)ᶜ),
    rsZeroTupleTerm Z g Phi T rho

def normalizedFiniteHeightSplit
    (Z : ZeroConfig) (n : ℕ) (T : ℝ)
    (g : Fin (n + 1) → ℝ → ℂ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ) : ℂ :=
  ((2 * Real.pi / (T * Real.log T) : ℝ) : ℂ) *
    (finiteHeightWeightedRSGaugeTupleSum Z n T g Phi +
      remoteHeightWeightedRSTupleTail Z n T g Phi)

def ziTupleInsideEquiv
    (Z : ZeroConfig) (n : ℕ) (T : ℝ) :
    (Fin (n + 1) → ↥(ZeroSide.ZI Z T)) ≃
      rsInsideTupleSet Z n T where
  toFun rho := ⟨ziTupleToCarrier Z n T rho,
    fun j => (rho j).property⟩
  invFun rho j := ⟨((rho.1 j : Z.carrier) : ℂ), rho.2 j⟩
  left_inv rho := by
    funext j
    apply Subtype.ext
    rfl
  right_inv rho := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    rfl

theorem rsZeroTupleTerm_ziTupleToCarrier
    {Z : ZeroConfig} {n : ℕ} {T : ℝ}
    (g : Fin (n + 1) → ℝ → ℂ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ)
    (rho : Fin (n + 1) → ↥(ZeroSide.ZI Z T)) :
    rsZeroTupleTerm Z g Phi T (ziTupleToCarrier Z n T rho) =
      (∏ j : Fin (n + 1),
        (Z.mult (rho j : ℂ) : ℂ) *
          paperFT (g j) (gammaOf (rho j : ℂ) / T)) *
        rsGaugeTest Phi
          (fun j => scaledZeroOrdinateAtScale (Real.log T) (rho j : ℂ)) := by
  unfold rsZeroTupleTerm ziTupleToCarrier scaledZeroOrdinateAtScale
  simp

theorem tsum_rsZeroTupleTerm_eq_finiteHeightWeighted_add_remote
    {Z : ZeroConfig} {n : ℕ} {T : ℝ}
    (g : Fin (n + 1) → ℝ → ℂ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ)
    (hsum : Summable (rsZeroTupleTerm Z g Phi T)) :
    (∑' rho, rsZeroTupleTerm Z g Phi T rho) =
      finiteHeightWeightedRSGaugeTupleSum Z n T g Phi +
        remoteHeightWeightedRSTupleTail Z n T g Phi := by
  let S := rsInsideTupleSet Z n T
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl S
  have hinside :
      (∑' rho : S, rsZeroTupleTerm Z g Phi T rho) =
        finiteHeightWeightedRSGaugeTupleSum Z n T g Phi := by
    rw [← (ziTupleInsideEquiv Z n T).tsum_eq]
    unfold finiteHeightWeightedRSGaugeTupleSum
    apply tsum_congr
    intro rho
    exact rsZeroTupleTerm_ziTupleToCarrier g Phi rho
  rw [← hinside]
  unfold remoteHeightWeightedRSTupleTail
  simpa only [S] using hsplit.symm

theorem normalizedRSZeroTupleSum_eq_normalizedFiniteHeightSplit
    {Z : ZeroConfig} {n : ℕ} {T : ℝ}
    (g : Fin (n + 1) → ℝ → ℂ)
    (Phi : (Fin (n + 1) → ℝ) → ℂ)
    (hsum : Summable (rsZeroTupleTerm Z g Phi T)) :
    RSReduction.normalizedRSZeroTupleSum Z g Phi T =
      normalizedFiniteHeightSplit Z n T g Phi := by
  unfold RSReduction.normalizedRSZeroTupleSum normalizedFiniteHeightSplit
  rw [tsum_rsZeroTupleTerm_eq_finiteHeightWeighted_add_remote g Phi hsum]

theorem RSReduction.RS1996ZetaInputs.exists_normalizedFiniteHeightSplit_diagonal
    {Z : ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3)
    {p delta mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    ∃ R : ℕ → ℝ, ∃ m : ℕ → ℕ, ∃ T : ℕ → ℝ,
      (∀ q, 0 < R q) ∧ Tendsto R atTop atTop ∧
      Tendsto m atTop atTop ∧ Tendsto T atTop atTop ∧
      (∀ q, Summable (rsZeroTupleTerm Z
        (windowAveragedHeightFamily (n := n) (R q)
          (RSReduction.topHatSmoothingWidth 1 q))
        (RSReduction.weightedCyclicSymbol (k := n + 1) mu
          (RSReduction.smoothTopHat p
            (RSReduction.topHatSmoothingWidth p (m q)))) (T q))) ∧
      Tendsto
        (fun q : ℕ => normalizedFiniteHeightSplit Z n (T q)
          (windowAveragedHeightFamily (n := n) (R q)
            (RSReduction.topHatSmoothingWidth 1 q))
          (RSReduction.weightedCyclicSymbol (k := n + 1) mu
            (RSReduction.smoothTopHat p
              (RSReduction.topHatSmoothingWidth p (m q)))))
        atTop (𝓝 (RSReduction.evaluatedTopHatCyclicMain n p mu)) := by
  obtain ⟨R, m, T, hRpos, hRtop, hmtop, hTtop, hsum, hlim⟩ :=
    RH.Zeta85.RSReduction.RS1996ZetaInputs.exists_normalized_windowAveragedHeight_diagonal
      hRS n hn hp hp1 hdelta hmu hbudget
  refine ⟨R, m, T, hRpos, hRtop, hmtop, hTtop, hsum, ?_⟩
  apply hlim.congr'
  filter_upwards [] with q
  exact normalizedRSZeroTupleSum_eq_normalizedFiniteHeightSplit _ _ (hsum q)

end RH.Zeta85.RSPoissonCyclicBridge
