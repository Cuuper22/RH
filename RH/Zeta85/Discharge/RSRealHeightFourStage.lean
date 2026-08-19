import RH.Zeta85.Discharge.RSRealHeightDiagonal

/-!
# Four-stage Rudnick--Sarnak limit at genuine real height

The fixed-test height limit, cyclic-symbol smoothing, physical-height
concentration, and sharp dyadic limit are assembled without collapsing the
height variable to a subsequence.  At each real height the selector uses the
largest stage whose permanent accuracy and side conditions are already
available.
-/

open Filter Topology

noncomputable section

namespace RH.Zeta85.RSReduction

open RSPoissonCyclicBridge

/-- Real-height slow selection with an eventual side condition carried along
with the approximation. -/
theorem exists_realHeight_slow_selector_with_good
    {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → ℝ → X) (a : ℕ → X) (d : X)
    (good : ℕ → ℝ → Prop)
    (hf : ∀ q, Tendsto (f q) atTop (𝓝 (a q)))
    (ha : Tendsto a atTop (𝓝 d))
    (hgood : ∀ q, ∀ᶠ T in atTop, good q T) :
    ∃ s : ℝ → ℕ,
      Tendsto s atTop atTop ∧
      (∀ᶠ T in atTop, good (s T) T) ∧
      Tendsto (fun T => f (s T) T) atTop (𝓝 d) := by
  let eps : ℕ → ℝ := fun q => 1 / ((q : ℝ) + 1)
  have heps_pos (q : ℕ) : 0 < eps q := by
    dsimp [eps]
    positivity
  have hcutoff_exists : ∀ q : ℕ, ∃ C : ℝ,
      (q : ℝ) ≤ C ∧
      ∀ T, C ≤ T → good q T ∧ dist (f q T) (a q) < eps q := by
    intro q
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
      ((hgood q).and
        (Metric.tendsto_nhds.1 (hf q) (eps q) (heps_pos q)))
    refine ⟨max (q : ℝ) B, le_max_left _ _, ?_⟩
    intro T hT
    exact hB T ((le_max_right _ _).trans hT)
  choose C hC_large hC_data using hcutoff_exists
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
  have hdata : ∀ᶠ T : ℝ in atTop,
      good (s T) T ∧ dist (f (s T) T) (a (s T)) < eps (s T) := by
    filter_upwards [hselected] with T hT
    exact hC_data (s T) T hT
  have hgood_selected : ∀ᶠ T : ℝ in atTop, good (s T) T :=
    hdata.mono fun _ hT => hT.1
  have hclose : ∀ᶠ T : ℝ in atTop,
      dist (f (s T) T) (a (s T)) < eps (s T) :=
    hdata.mono fun _ hT => hT.2
  have heps_zero : Tendsto eps atTop (𝓝 0) := by
    have hden : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa only [eps] using tendsto_const_nhds.div_atTop hden
  have heps_selected : Tendsto (fun T => eps (s T)) atTop (𝓝 0) := by
    change Tendsto (eps ∘ s) atTop (𝓝 0)
    exact heps_zero.comp hs
  have hdist_le : ∀ᶠ T : ℝ in atTop,
      dist (a (s T)) (f (s T) T) ≤ eps (s T) := by
    filter_upwards [hclose] with T hT
    simpa only [dist_comm] using hT.le
  have hdist : Tendsto
      (fun T => dist (a (s T)) (f (s T) T)) atTop (𝓝 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun _ => dist_nonneg)
      hdist_le heps_selected
  refine ⟨s, hs, hgood_selected, ?_⟩
  exact (ha.comp hs).congr_dist hdist

/-- Assemble four nested limits into one genuine real-height limit while
preserving the eventual fixed-test side condition. -/
theorem exists_realHeight_slow_diagonal_four_stage
    {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → ℝ → ℕ → ℝ → X)
    (a : ℕ → ℝ → ℕ → X)
    (b : ℕ → ℝ → X) (c : ℕ → X) (d : X)
    (good : ℕ → ℝ → ℕ → ℝ → Prop)
    (hf : ∀ q R, 0 < R → ∀ m,
      Tendsto (f q R m) atTop (𝓝 (a q R m)))
    (ha : ∀ q R, 0 < R → Tendsto (a q R) atTop (𝓝 (b q R)))
    (hb : ∀ q, Tendsto (b q) atTop (𝓝 (c q)))
    (hc : Tendsto c atTop (𝓝 d))
    (hgood : ∀ q R, 0 < R → ∀ m, ∀ᶠ T in atTop, good q R m T) :
    ∃ R : ℕ → ℝ, ∃ m : ℕ → ℕ, ∃ s : ℝ → ℕ,
      (∀ q, 0 < R q) ∧ Tendsto R atTop atTop ∧
      Tendsto m atTop atTop ∧ Tendsto s atTop atTop ∧
      (∀ᶠ T in atTop, good (s T) (R (s T)) (m (s T)) T) ∧
      Tendsto
        (fun T => f (s T) (R (s T)) (m (s T)) T)
        atTop (𝓝 d) := by
  let eps : ℕ → ℝ := fun q => 1 / ((q : ℝ) + 1)
  have heps_pos (q : ℕ) : 0 < eps q := by
    dsimp [eps]
    positivity
  have hRexists : ∀ q : ℕ, ∃ R : ℝ,
      0 < R ∧ (q : ℝ) ≤ R ∧ dist (b q R) (c q) < eps q := by
    intro q
    exact ((eventually_gt_atTop (0 : ℝ)).and
      ((eventually_ge_atTop (q : ℝ)).and
        (Metric.tendsto_nhds.1 (hb q) (eps q) (heps_pos q)))).exists
  choose R hRpos hRlarge hRclose using hRexists
  have hmexists : ∀ q : ℕ, ∃ m : ℕ,
      q ≤ m ∧ dist (a q (R q) m) (b q (R q)) < eps q := by
    intro q
    exact ((eventually_ge_atTop q).and
      (Metric.tendsto_nhds.1 (ha q (R q) (hRpos q))
        (eps q) (heps_pos q))).exists
  choose m hmlarge hmclose using hmexists
  have hRtop : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRlarge tendsto_natCast_atTop_atTop
  have hmtop : Tendsto m atTop atTop :=
    tendsto_atTop_mono hmlarge tendsto_id
  have heps_two_zero : Tendsto (fun q : ℕ => 2 * eps q) atTop (𝓝 0) := by
    have hden : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun q : ℕ => 1 / ((q : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    simpa only [mul_zero, eps] using
      (show Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)
        from tendsto_const_nhds).mul hinv
  have hdiag_dist : ∀ q : ℕ,
      dist (a q (R q) (m q)) (c q) < 2 * eps q := by
    intro q
    calc
      dist (a q (R q) (m q)) (c q) ≤
          dist (a q (R q) (m q)) (b q (R q)) +
            dist (b q (R q)) (c q) := dist_triangle _ _ _
      _ < eps q + eps q := add_lt_add (hmclose q) (hRclose q)
      _ = 2 * eps q := by ring
  have hdiag_dist_zero : Tendsto
      (fun q => dist (c q) (a q (R q) (m q))) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun _ => dist_nonneg)
      (Eventually.of_forall fun q => by
        simpa only [dist_comm] using (hdiag_dist q).le)
      heps_two_zero
  have hadiag : Tendsto (fun q => a q (R q) (m q)) atTop (𝓝 d) :=
    hc.congr_dist hdiag_dist_zero
  obtain ⟨s, hs, hgood_selected, hlimit⟩ :=
    exists_realHeight_slow_selector_with_good
      (f := fun q T => f q (R q) (m q) T)
      (a := fun q => a q (R q) (m q))
      (d := d)
      (good := fun q T => good q (R q) (m q) T)
      (fun q => hf q (R q) (hRpos q) (m q))
      hadiag
      (fun q => hgood q (R q) (hRpos q) (m q))
  exact ⟨R, m, s, hRpos, hRtop, hmtop, hs, hgood_selected, hlimit⟩

/-- The four-stage Rudnick--Sarnak evaluation now holds along the full real
height filter, with stage parameters changing only after their fixed-test
thresholds have been crossed. -/
theorem RS1996ZetaInputs.exists_normalized_windowAveragedHeight_realHeight
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3)
    {p delta mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    ∃ R : ℕ → ℝ, ∃ m : ℕ → ℕ, ∃ s : ℝ → ℕ,
      (∀ q, 0 < R q) ∧ Tendsto R atTop atTop ∧
      Tendsto m atTop atTop ∧ Tendsto s atTop atTop ∧
      (∀ᶠ T in atTop, Summable (rsZeroTupleTerm Z
        (windowAveragedHeightFamily (n := n) (R (s T))
          (topHatSmoothingWidth 1 (s T)))
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p (m (s T))))) T)) ∧
      Tendsto
        (fun T : ℝ => normalizedRSZeroTupleSum Z
          (windowAveragedHeightFamily (n := n) (R (s T))
            (topHatSmoothingWidth 1 (s T)))
          (weightedCyclicSymbol (k := n + 1) mu
            (smoothTopHat p (topHatSmoothingWidth p (m (s T))))) T)
        atTop (𝓝 (evaluatedTopHatCyclicMain n p mu)) := by
  have hstages :=
    RH.Zeta85.RSReduction.RS1996ZetaInputs.normalized_windowAveragedHeightFamily_evaluated
      hRS n hn hp hp1 hdelta hmu hbudget
  exact exists_realHeight_slow_diagonal_four_stage
    (f := fun q R m T => normalizedRSZeroTupleSum Z
      (windowAveragedHeightFamily (n := n) R
        (topHatSmoothingWidth 1 q))
      (weightedCyclicSymbol (k := n + 1) mu
        (smoothTopHat p (topHatSmoothingWidth p m))) T)
    (a := fun q R m => rsHeightFactor
      (windowAveragedHeightFamily (n := n) R
        (topHatSmoothingWidth 1 q)) *
      rsMainTerm (weightedCyclicSymbol (k := n + 1) mu
        (smoothTopHat p (topHatSmoothingWidth p m))))
    (b := fun q R => rsHeightFactor
      (windowAveragedHeightFamily (n := n) R
        (topHatSmoothingWidth 1 q)) *
      evaluatedTopHatCyclicMain n p mu)
    (c := fun q => Complex.ofReal (∫ x, smoothHeightWindow
      (topHatSmoothingWidth 1 q) x ^ (n + 1)) *
      evaluatedTopHatCyclicMain n p mu)
    (d := evaluatedTopHatCyclicMain n p mu)
    (good := fun q R m T => Summable (rsZeroTupleTerm Z
      (windowAveragedHeightFamily (n := n) R
        (topHatSmoothingWidth 1 q))
      (weightedCyclicSymbol (k := n + 1) mu
        (smoothTopHat p (topHatSmoothingWidth p m))) T))
    (fun q R hR m => (hstages.1 q R hR).1 m)
    (fun q R hR => (hstages.1 q R hR).2)
    hstages.2.1 hstages.2.2
    (fun q R hR m => by
      obtain ⟨hfixed, _hsharp⟩ :=
        RH.Zeta85.RSReduction.RS1996ZetaInputs.theorem31_fixedSmoothTopHatFamily_evaluated
          hRS n hn
          (windowAveragedHeightFamily (n := n) R
            (topHatSmoothingWidth 1 q))
          (windowAveragedHeightFamily_admissible hR
            (topHatSmoothingWidth_pos (show (0 : ℝ) < 1 by norm_num) q)
            (two_mul_topHatSmoothingWidth_le
              (show (0 : ℝ) < 1 by norm_num) q))
          hp hp1 hdelta hmu hbudget
      obtain ⟨C, T0, hC, hT0, hbound⟩ := hfixed m
      filter_upwards [eventually_ge_atTop T0] with T hT
      exact (hbound T hT).1)

end RH.Zeta85.RSReduction

end
