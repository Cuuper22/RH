import RH.Zeta85.Discharge.RSRealHeightFourStage
import RH.Zeta85.Discharge.RSFiniteHeightSplit

/-!
# Exact finite/remote split at genuine real height

The full real-height Rudnick--Sarnak limit is rewritten, eventually at every
large physical height, as the exact finite-height contribution plus its remote
tail.  This is the decomposition consumed by the logarithmic trace and remote
correction machinery.
-/

open Filter Topology

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open RSReduction

/-- The real-height four-stage RS selector carries summability, so the exact
finite/remote decomposition holds eventually and has the same limiting main
term. -/
theorem RSReduction.RS1996ZetaInputs.exists_normalizedFiniteHeightSplit_realHeight
    {Z : ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3)
    {p delta mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    ∃ R : ℕ → ℝ, ∃ m : ℕ → ℕ, ∃ s : ℝ → ℕ,
      (∀ q, 0 < R q) ∧ Tendsto R atTop atTop ∧
      Tendsto m atTop atTop ∧ Tendsto s atTop atTop ∧
      (∀ᶠ T in atTop, Summable (rsZeroTupleTerm Z
        (windowAveragedHeightFamily (n := n) (R (s T))
          (RSReduction.topHatSmoothingWidth 1 (s T)))
        (RSReduction.weightedCyclicSymbol (k := n + 1) mu
          (RSReduction.smoothTopHat p
            (RSReduction.topHatSmoothingWidth p (m (s T))))) T)) ∧
      Tendsto
        (fun T : ℝ => normalizedFiniteHeightSplit Z n T
          (windowAveragedHeightFamily (n := n) (R (s T))
            (RSReduction.topHatSmoothingWidth 1 (s T)))
          (RSReduction.weightedCyclicSymbol (k := n + 1) mu
            (RSReduction.smoothTopHat p
              (RSReduction.topHatSmoothingWidth p (m (s T))))))
        atTop (𝓝 (RSReduction.evaluatedTopHatCyclicMain n p mu)) := by
  obtain ⟨R, m, s, hRpos, hRtop, hmtop, hstop, hsum, hlim⟩ :=
    RH.Zeta85.RSReduction.RS1996ZetaInputs.exists_normalized_windowAveragedHeight_realHeight
      hRS n hn hp hp1 hdelta hmu hbudget
  refine ⟨R, m, s, hRpos, hRtop, hmtop, hstop, hsum, ?_⟩
  apply hlim.congr'
  filter_upwards [hsum] with T hsumT
  exact normalizedRSZeroTupleSum_eq_normalizedFiniteHeightSplit _ _ hsumT

end RH.Zeta85.RSPoissonCyclicBridge

end
