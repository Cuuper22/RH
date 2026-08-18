import RH.Zeta85.Discharge.RSHeightSmoothedMain

open Filter Topology

namespace RH.Zeta85.RSReduction

open RSPoissonCyclicBridge

theorem exists_slow_diagonal_four_stage
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
    ∃ R : ℕ → ℝ, ∃ m : ℕ → ℕ, ∃ T : ℕ → ℝ,
      (∀ q, 0 < R q) ∧ Tendsto R atTop atTop ∧ Tendsto m atTop atTop ∧
      Tendsto T atTop atTop ∧ (∀ q, good q (R q) (m q) (T q)) ∧
      Tendsto (fun q => f q (R q) (m q) (T q)) atTop (𝓝 d) := by
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
  have hTexists : ∀ q : ℕ, ∃ T : ℝ,
      (q : ℝ) ≤ T ∧
        good q (R q) (m q) T ∧
        dist (f q (R q) (m q) T) (a q (R q) (m q)) < eps q := by
    intro q
    exact ((eventually_ge_atTop (q : ℝ)).and
      ((hgood q (R q) (hRpos q) (m q)).and
        (Metric.tendsto_nhds.1 (hf q (R q) (hRpos q) (m q)) (eps q)
          (heps_pos q)))).exists
  choose T hTlarge hTgood hTclose using hTexists
  refine ⟨R, m, T, hRpos,
    tendsto_atTop_mono hRlarge tendsto_natCast_atTop_atTop,
    tendsto_atTop_mono hmlarge tendsto_id,
    tendsto_atTop_mono hTlarge tendsto_natCast_atTop_atTop, hTgood, ?_⟩
  have heps_zero : Tendsto (fun q : ℕ => 3 * eps q) atTop (𝓝 0) := by
    have hden : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun q : ℕ => 1 / ((q : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    simpa only [mul_zero, eps] using
      (show Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (𝓝 3)
        from tendsto_const_nhds).mul hinv
  have hdist : ∀ q : ℕ,
      dist (f q (R q) (m q) (T q)) (c q) < 3 * eps q := by
    intro q
    calc
      dist (f q (R q) (m q) (T q)) (c q) ≤
          dist (f q (R q) (m q) (T q)) (a q (R q) (m q)) +
            dist (a q (R q) (m q)) (c q) := dist_triangle _ _ _
      _ ≤ dist (f q (R q) (m q) (T q)) (a q (R q) (m q)) +
          (dist (a q (R q) (m q)) (b q (R q)) +
            dist (b q (R q)) (c q)) := by
              gcongr
              exact dist_triangle _ _ _
      _ < eps q + (eps q + eps q) :=
        add_lt_add (hTclose q) (add_lt_add (hmclose q) (hRclose q))
      _ = 3 * eps q := by ring
  have hdist_zero : Tendsto
      (fun q => dist (c q) (f q (R q) (m q) (T q))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
      (Eventually.of_forall fun q => ?_) heps_zero
    simpa only [dist_comm] using (hdist q).le
  exact hc.congr_dist hdist_zero

/-- A single cofinal sequence realizes all four nested RS limits.  The
physical selector, cyclic smoothing width, and zero height grow only as fast
as the preceding fixed-test limit permits. -/
theorem RS1996ZetaInputs.exists_normalized_windowAveragedHeight_diagonal
    {Z : Zeta23.ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3)
    {p delta mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    ∃ R : ℕ → ℝ, ∃ m : ℕ → ℕ, ∃ T : ℕ → ℝ,
      (∀ q, 0 < R q) ∧ Tendsto R atTop atTop ∧
      Tendsto m atTop atTop ∧ Tendsto T atTop atTop ∧
      (∀ q, Summable (rsZeroTupleTerm Z
        (windowAveragedHeightFamily (n := n) (R q)
          (topHatSmoothingWidth 1 q))
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p (m q)))) (T q))) ∧
      Tendsto
        (fun q : ℕ => normalizedRSZeroTupleSum Z
          (windowAveragedHeightFamily (n := n) (R q)
            (topHatSmoothingWidth 1 q))
          (weightedCyclicSymbol (k := n + 1) mu
            (smoothTopHat p (topHatSmoothingWidth p (m q)))) (T q))
        atTop (𝓝 (evaluatedTopHatCyclicMain n p mu)) := by
  have hstages :=
    RH.Zeta85.RSReduction.RS1996ZetaInputs.normalized_windowAveragedHeightFamily_evaluated
      hRS n hn hp hp1 hdelta hmu hbudget
  exact exists_slow_diagonal_four_stage
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
