import RH.Zeta85.Discharge.RSHeightFactorLimit

/-!
# Rudnick--Sarnak with the concentrating dyadic height family

This module inserts the averaged height selector into the fixed-test
Rudnick--Sarnak theorem.  The limits occur in their required order: height
first for every fixed smooth test, then the cyclic-symbol smoothing, then
concentration of the physical height selector, and finally sharpening of its
dyadic window.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators ContDiff

noncomputable section

namespace RH.Zeta85.RSReduction

open TopHatMoments
open RSPoissonCyclicBridge

def evaluatedTopHatCyclicMain (n : ℕ) (p mu : ℝ) : ℂ :=
  (mu : ℂ) *
    (uncenteredContractionMoment (topHatR3Terms p) mu (n + 1) : ℝ)

theorem windowAveragedHeightFamily_admissible
    {n : ℕ} {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1) :
    ∀ j, ContDiff ℝ ∞ (windowAveragedHeightFamily (n := n) R w j) ∧
      HasCompactSupport (windowAveragedHeightFamily (n := n) R w j) := by
  intro j
  exact ⟨windowAveragedHeightTest_contDiff hR hw hw1,
    windowAveragedHeightTest_hasCompactSupport hR⟩

theorem RS1996ZetaInputs.normalized_windowAveragedHeightFamily_evaluated
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3)
    {p delta mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    (∀ q : ℕ, ∀ R : ℝ, 0 < R →
      (∀ m : ℕ, Tendsto
        (normalizedRSZeroTupleSum Z
          (windowAveragedHeightFamily (n := n) R
            (topHatSmoothingWidth 1 q))
          (weightedCyclicSymbol (k := n + 1) mu
            (smoothTopHat p (topHatSmoothingWidth p m))))
        atTop
        (𝓝 (rsHeightFactor
          (windowAveragedHeightFamily (n := n) R
            (topHatSmoothingWidth 1 q)) *
          rsMainTerm (weightedCyclicSymbol (k := n + 1) mu
            (smoothTopHat p (topHatSmoothingWidth p m)))))) ∧
      Tendsto
        (fun m : ℕ => rsHeightFactor
          (windowAveragedHeightFamily (n := n) R
            (topHatSmoothingWidth 1 q)) *
          rsMainTerm (weightedCyclicSymbol (k := n + 1) mu
            (smoothTopHat p (topHatSmoothingWidth p m))))
        atTop
        (𝓝 (rsHeightFactor
          (windowAveragedHeightFamily (n := n) R
            (topHatSmoothingWidth 1 q)) *
          evaluatedTopHatCyclicMain n p mu))) ∧
    (∀ q : ℕ, Tendsto
      (fun R : ℝ => rsHeightFactor
        (windowAveragedHeightFamily (n := n) R
          (topHatSmoothingWidth 1 q)) *
        evaluatedTopHatCyclicMain n p mu)
      atTop
      (𝓝 (Complex.ofReal (∫ x, smoothHeightWindow
        (topHatSmoothingWidth 1 q) x ^ (n + 1)) *
        evaluatedTopHatCyclicMain n p mu))) ∧
    Tendsto
      (fun q : ℕ => Complex.ofReal (∫ x, smoothHeightWindow
        (topHatSmoothingWidth 1 q) x ^ (n + 1)) *
        evaluatedTopHatCyclicMain n p mu)
      atTop
      (𝓝 (evaluatedTopHatCyclicMain n p mu)) := by
  constructor
  · intro q R hR
    exact RH.Zeta85.RSReduction.RS1996ZetaInputs.normalized_fixedSmoothTopHatFamily_evaluated
      hRS n hn
      (windowAveragedHeightFamily (n := n) R
        (topHatSmoothingWidth 1 q))
      (windowAveragedHeightFamily_admissible hR
        (topHatSmoothingWidth_pos (show (0 : ℝ) < 1 by norm_num) q)
        (two_mul_topHatSmoothingWidth_le
          (show (0 : ℝ) < 1 by norm_num) q))
      hp hp1 hdelta hmu hbudget
  constructor
  · intro q
    exact (rsHeightFactor_windowAveragedHeightFamily_tendsto
      (n := n)
      (topHatSmoothingWidth_pos (show (0 : ℝ) < 1 by norm_num) q)
      (two_mul_topHatSmoothingWidth_le
        (show (0 : ℝ) < 1 by norm_num) q)).mul_const
          (evaluatedTopHatCyclicMain n p mu)
  · simpa only [one_mul] using
      (rsHeightFactor_windowAveragedHeightFamily_iterated_tendsto_one n).2.mul_const
        (evaluatedTopHatCyclicMain n p mu)

end RH.Zeta85.RSReduction
