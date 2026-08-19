import Mathlib.Data.Nat.Find
import RH.Zeta85.Discharge.RSSlowDiagonal

/-!
# Real-height slow diagonal

A diagonal indexed only by natural stages is not yet an `atTop` statement in
the physical height.  This module chooses, at every real height, the largest
stage whose uniform threshold has already been crossed.  The chosen stage
tends to infinity and the resulting height-dependent family has a genuine
real-height limit.
-/

open Filter Topology

noncomputable section

namespace RH.Zeta85.RSReduction

/-- Promote a countable family of real-height limits followed by a sharp
parameter limit to one genuine real-height limit.  The selector changes only
when the next uniform threshold has been crossed, so no monotonicity of `f`
is required. -/
theorem exists_realHeight_slow_selector
    {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → ℝ → X) (a : ℕ → X) (d : X)
    (hf : ∀ q, Tendsto (f q) atTop (𝓝 (a q)))
    (ha : Tendsto a atTop (𝓝 d)) :
    ∃ s : ℝ → ℕ,
      Tendsto s atTop atTop ∧
      Tendsto (fun T => f (s T) T) atTop (𝓝 d) := by
  let eps : ℕ → ℝ := fun q => 1 / ((q : ℝ) + 1)
  have heps_pos (q : ℕ) : 0 < eps q := by
    dsimp [eps]
    positivity
  have hcutoff_exists : ∀ q : ℕ, ∃ C : ℝ,
      (q : ℝ) ≤ C ∧
      ∀ T, C ≤ T → dist (f q T) (a q) < eps q := by
    intro q
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
      (Metric.tendsto_nhds.1 (hf q) (eps q) (heps_pos q))
    refine ⟨max (q : ℝ) B, le_max_left _ _, ?_⟩
    intro T hT
    exact hB T ((le_max_right _ _).trans hT)
  choose C hC_large hC_close using hcutoff_exists
  let s : ℝ → ℕ := fun T =>
    Nat.findGreatest (fun q => C q ≤ T) (Nat.floor T)
  have hs : Tendsto s atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro q
    filter_upwards [eventually_ge_atTop (C q)] with T hT
    have hq_floor : q ≤ Nat.floor T :=
      Nat.le_floor ((hC_large q).trans hT)
    simpa only [s] using
      (Nat.le_findGreatest (P := fun r => C r ≤ T) hq_floor hT)
  have hselected : ∀ᶠ T : ℝ in atTop, C (s T) ≤ T := by
    filter_upwards [eventually_ge_atTop (C 0)] with T hT
    have hspec := Nat.findGreatest_spec
      (P := fun q => C q ≤ T) (m := 0)
      (Nat.zero_le (Nat.floor T)) hT
    simpa only [s] using hspec
  have hclose : ∀ᶠ T : ℝ in atTop,
      dist (f (s T) T) (a (s T)) < eps (s T) := by
    filter_upwards [hselected] with T hT
    exact hC_close (s T) T hT
  have heps_zero : Tendsto eps atTop (𝓝 0) := by
    have hden : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa only [eps] using tendsto_const_nhds.div_atTop hden
  have heps_selected : Tendsto (fun T => eps (s T)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using heps_zero.comp hs
  have hdist_le : ∀ᶠ T : ℝ in atTop,
      dist (a (s T)) (f (s T) T) ≤ eps (s T) := by
    filter_upwards [hclose] with T hT
    simpa only [dist_comm] using hT.le
  have hdist : Tendsto
      (fun T => dist (a (s T)) (f (s T) T)) atTop (𝓝 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun _ => dist_nonneg)
      hdist_le heps_selected
  refine ⟨s, hs, ?_⟩
  exact (ha.comp hs).congr_dist hdist

end RH.Zeta85.RSReduction

end
