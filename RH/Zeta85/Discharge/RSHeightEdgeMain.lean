import RH.Zeta85.Discharge.RSHeightEdgeProfiles
import RH.Zeta85.Discharge.RSHeightSmoothedMain

/-!
# Vanishing Rudnick--Sarnak edge families

The coordinate-localized profiles are inserted into the actual normalized
Rudnick--Sarnak zero-tuple theorem.  After the zero-height limit and the
cyclic sharping limit, their main terms vanish as the edge width shrinks.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators ContDiff

noncomputable section

namespace RH.Zeta85.RSReduction

open TopHatMoments
open RSPoissonCyclicBridge

theorem mixedEdgeAveragedHeightFamily_admissible
    {n : ℕ} {i : Fin (n + 1)} {d c w R : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (hR : 0 < R) :
    ∀ j, ContDiff ℝ ∞
        (averagedHeightFamilyOf (mixedEdgeHeightProfiles i d c w) R j) ∧
      HasCompactSupport
        (averagedHeightFamilyOf (mixedEdgeHeightProfiles i d c w) R j) := by
  intro j
  exact ⟨averagedHeightTestOf_contDiff
      (mixedEdgeHeightProfiles_continuous hd hw hw1 j)
      (mixedEdgeHeightProfiles_hasCompactSupport hd hw j) hR,
    averagedHeightTestOf_hasCompactSupport _ hR⟩

theorem RS1996ZetaInputs.normalized_mixedEdgeHeightFamily_evaluated
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3) (i : Fin (n + 1))
    {d c w R p delta mu : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (hR : 0 < R)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    (∀ m : ℕ, Tendsto
      (normalizedRSZeroTupleSum Z
        (averagedHeightFamilyOf (mixedEdgeHeightProfiles i d c w) R)
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m))))
      atTop
      (𝓝 (rsHeightFactor
        (averagedHeightFamilyOf (mixedEdgeHeightProfiles i d c w) R) *
        rsMainTerm (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m)))))) ∧
    Tendsto
      (fun m : ℕ => rsHeightFactor
        (averagedHeightFamilyOf (mixedEdgeHeightProfiles i d c w) R) *
        rsMainTerm (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m))))
      atTop
      (𝓝 (rsHeightFactor
        (averagedHeightFamilyOf (mixedEdgeHeightProfiles i d c w) R) *
        evaluatedTopHatCyclicMain n p mu)) ∧
    ‖rsHeightFactor
        (averagedHeightFamilyOf (mixedEdgeHeightProfiles i d c w) R) *
        evaluatedTopHatCyclicMain n p mu‖ ≤
      4 * d * ‖evaluatedTopHatCyclicMain n p mu‖ := by
  have hstages :=
    RH.Zeta85.RSReduction.RS1996ZetaInputs.normalized_fixedSmoothTopHatFamily_evaluated
    hRS n hn
    (averagedHeightFamilyOf (mixedEdgeHeightProfiles i d c w) R)
    (mixedEdgeAveragedHeightFamily_admissible hd hw hw1 hR)
    hp hp1 hdelta hmu hbudget
  refine ⟨hstages.1, ?_, ?_⟩
  · simpa only [evaluatedTopHatCyclicMain] using hstages.2
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_rsHeightFactor_mixedEdgeHeightProfiles_le hd hw hw1 hR)
      (norm_nonneg _)

def canonicalEdgeWidth (q : ℕ) : ℝ :=
  1 / ((q : ℝ) + 1)

theorem canonicalEdgeWidth_pos (q : ℕ) : 0 < canonicalEdgeWidth q := by
  unfold canonicalEdgeWidth
  positivity

theorem canonicalEdgeWidth_tendsto_zero :
    Tendsto canonicalEdgeWidth atTop (𝓝 0) := by
  change Tendsto (fun q : ℕ => 1 / ((q : ℝ) + 1)) atTop (𝓝 0)
  have hden : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop hden

theorem rsHeightFactor_mixedEdgeHeightProfiles_mul_const_tendsto_zero
    {n : ℕ} (i : Fin (n + 1)) {c w : ℝ}
    (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (R : ℕ → ℝ) (hR : ∀ q, 0 < R q) (A : ℂ) :
    Tendsto
      (fun q : ℕ => rsHeightFactor
        (averagedHeightFamilyOf
          (mixedEdgeHeightProfiles i (canonicalEdgeWidth q) c w) (R q)) * A)
      atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
    (g := fun q : ℕ => 4 * canonicalEdgeWidth q * ‖A‖)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [] with q
    simp only [sub_zero, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_rsHeightFactor_mixedEdgeHeightProfiles_le
        (canonicalEdgeWidth_pos q) hw hw1 (hR q)) (norm_nonneg _)
  · have hfour := (show Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)
        from tendsto_const_nhds).mul canonicalEdgeWidth_tendsto_zero
    have h := hfour.mul
      (show Tendsto (fun _ : ℕ => ‖A‖) atTop (𝓝 ‖A‖) from tendsto_const_nhds)
    simpa only [mul_zero, zero_mul] using h

theorem RS1996ZetaInputs.exists_normalized_mixedEdge_diagonal_tendsto_zero
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3) (i : Fin (n + 1))
    {c w p delta mu : ℝ} (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    ∃ m : ℕ → ℕ, ∃ T : ℕ → ℝ,
      Tendsto m atTop atTop ∧ Tendsto T atTop atTop ∧
      (∀ q, Summable (rsZeroTupleTerm Z
        (averagedHeightFamilyOf
          (mixedEdgeHeightProfiles i (canonicalEdgeWidth q) c w)
          ((q : ℝ) + 1))
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p (m q)))) (T q))) ∧
      Tendsto
        (fun q : ℕ => normalizedRSZeroTupleSum Z
          (averagedHeightFamilyOf
            (mixedEdgeHeightProfiles i (canonicalEdgeWidth q) c w)
            ((q : ℝ) + 1))
          (weightedCyclicSymbol (k := n + 1) mu
            (smoothTopHat p (topHatSmoothingWidth p (m q)))) (T q))
        atTop (𝓝 0) := by
  let g : ℕ → Fin (n + 1) → ℝ → ℂ := fun q =>
    averagedHeightFamilyOf
      (mixedEdgeHeightProfiles i (canonicalEdgeWidth q) c w) ((q : ℝ) + 1)
  let Phi : ℕ → (Fin (n + 1) → ℝ) → ℂ := fun m =>
    weightedCyclicSymbol (k := n + 1) mu
      (smoothTopHat p (topHatSmoothingWidth p m))
  have hgadm (q : ℕ) : ∀ j, ContDiff ℝ ∞ (g q j) ∧
      HasCompactSupport (g q j) := by
    exact mixedEdgeAveragedHeightFamily_admissible
      (canonicalEdgeWidth_pos q) hw hw1 (by positivity)
  have hstages (q : ℕ) :=
    RH.Zeta85.RSReduction.RS1996ZetaInputs.normalized_fixedSmoothTopHatFamily_evaluated
      hRS n hn (g q) (hgadm q) hp hp1 hdelta hmu hbudget
  obtain ⟨_R, m, T, _hRpos, _hRtop, hmtop, hTtop, hsum, hlim⟩ :=
    exists_slow_diagonal_four_stage
      (f := fun q (_ : ℝ) m T => normalizedRSZeroTupleSum Z (g q) (Phi m) T)
      (a := fun q (_ : ℝ) m => rsHeightFactor (g q) * rsMainTerm (Phi m))
      (b := fun q (_ : ℝ) => rsHeightFactor (g q) *
        evaluatedTopHatCyclicMain n p mu)
      (c := fun q => rsHeightFactor (g q) * evaluatedTopHatCyclicMain n p mu)
      (d := (0 : ℂ))
      (good := fun q (_ : ℝ) m T => Summable (rsZeroTupleTerm Z (g q) (Phi m) T))
      (fun q _ _ m => by simpa only [Phi] using (hstages q).1 m)
      (fun q _ _ => by
        simpa only [Phi, evaluatedTopHatCyclicMain] using (hstages q).2)
      (fun q => tendsto_const_nhds)
      (by
        simpa only [g] using
          rsHeightFactor_mixedEdgeHeightProfiles_mul_const_tendsto_zero
            i hw hw1 (fun q => (q : ℝ) + 1) (fun q => by positivity)
            (evaluatedTopHatCyclicMain n p mu))
      (fun q _ _ m => by
        obtain ⟨hfixed, _⟩ :=
          RH.Zeta85.RSReduction.RS1996ZetaInputs.theorem31_fixedSmoothTopHatFamily_evaluated
            hRS n hn (g q) (hgadm q) hp hp1 hdelta hmu hbudget
        obtain ⟨C, T0, hC, hT0, hbound⟩ := hfixed m
        filter_upwards [eventually_ge_atTop T0] with T hT
        simpa only [Phi] using (hbound T hT).1)
  exact ⟨m, T, hmtop, hTtop, hsum, by simpa only [g, Phi] using hlim⟩

end RH.Zeta85.RSReduction
