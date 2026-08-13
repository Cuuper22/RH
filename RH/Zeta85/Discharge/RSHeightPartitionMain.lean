import RH.Zeta85.Discharge.RSHeightPartition
import RH.Zeta85.Discharge.RSHeightEdgeMain

/-!
# Full dyadic height-boundary removal

The exact one-coordinate partition is telescoped across all coordinates.
The resulting difference between the outer selector (one on the whole
closed dyadic interval) and the inner selector has height factor bounded by
the number of coordinates times the shrinking edge mass.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ContDiff Convolution BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def constantHeightProfiles {n : ℕ} (H : ℝ → ℝ) : Fin (n + 1) → ℝ → ℝ :=
  fun _ => H

def outerAveragedHeightFamily {n : ℕ} (d R : ℝ) :
    Fin (n + 1) → ℝ → ℂ :=
  averagedHeightFamilyOf (constantHeightProfiles (n := n) (outerHeightProfile d)) R

def coreAveragedHeightFamily {n : ℕ} (w R : ℝ) :
    Fin (n + 1) → ℝ → ℂ :=
  averagedHeightFamilyOf (constantHeightProfiles (n := n) (smoothHeightWindow w)) R

theorem averagedHeightWeightOf_outer_eq_core_add_edge
    {d w R : ℝ} (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hR : 0 < R) (x : ℝ) :
    averagedHeightWeightOf (outerHeightProfile d) R x =
      averagedHeightWeightOf (smoothHeightWindow w) R x +
        averagedHeightWeightOf (dyadicEdgeRemainder d w) R x := by
  unfold averagedHeightWeightOf
  rw [paperFT_averagedHeightTestOf_outer_eq_core_add_edge hd hw hw1 hR]
  simp

theorem averagedHeightWeightOf_edge_nonneg
    {d w R : ℝ} (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hR : 0 < R) (x : ℝ) :
    0 ≤ averagedHeightWeightOf (dyadicEdgeRemainder d w) R x := by
  simpa only [averagedHeightWeightOf] using
    (paperFT_averagedHeightTestOf_real_mem_Icc
      (dyadicEdgeRemainder_continuous hd hw hw1)
      (dyadicEdgeRemainder_hasCompactSupport hd hw)
      (fun x => dyadicEdgeRemainder_nonneg hd hw)
      (fun x => dyadicEdgeRemainder_le_one hd) hR x).1

theorem integral_abs_outerWeight_sub_coreWeight_le
    {d w R : ℝ} (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hR : 0 < R) :
    (∫ x, |averagedHeightWeightOf (outerHeightProfile d) R x -
      averagedHeightWeightOf (smoothHeightWindow w) R x|) ≤
      4 * d + 2 * w := by
  have hfun : (fun x => |averagedHeightWeightOf (outerHeightProfile d) R x -
      averagedHeightWeightOf (smoothHeightWindow w) R x|) =
      averagedHeightWeightOf (dyadicEdgeRemainder d w) R := by
    funext x
    rw [averagedHeightWeightOf_outer_eq_core_add_edge hd hw hw1 hR]
    simp only [add_sub_cancel_left]
    exact abs_of_nonneg (averagedHeightWeightOf_edge_nonneg hd hw hw1 hR x)
  rw [hfun, integral_averagedHeightWeightOf
    (dyadicEdgeRemainder_continuous hd hw hw1)
    (dyadicEdgeRemainder_hasCompactSupport hd hw) hR]
  exact integral_dyadicEdgeRemainder_le hd hw hw1

theorem norm_rsHeightFactor_outer_sub_core_le
    {n : ℕ} {d w R : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (hR : 0 < R) :
    ‖RH.Zeta85.rsHeightFactor (outerAveragedHeightFamily (n := n) d R) -
      RH.Zeta85.rsHeightFactor (coreAveragedHeightFamily (n := n) w R)‖ ≤
      (n + 1 : ℝ) * (4 * d + 2 * w) := by
  let Wo : Fin (n + 1) → ℝ → ℝ := fun _ x =>
    averagedHeightWeightOf (outerHeightProfile d) R x
  let Wc : Fin (n + 1) → ℝ → ℝ := fun _ x =>
    averagedHeightWeightOf (smoothHeightWindow w) R x
  have houterC := (outerHeightProfile_contDiff hd).continuous
  have houterK := outerHeightProfile_hasCompactSupport hd
  have hcoreC := (smoothHeightWindow_contDiff hw hw1).continuous
  have hcoreK := smoothHeightWindow_hasCompactSupport hw
  have hWoIcc : ∀ j x, Wo j x ∈ Set.Icc (0 : ℝ) 1 := by
    intro j x
    simpa only [Wo, averagedHeightWeightOf] using
      paperFT_averagedHeightTestOf_real_mem_Icc houterC houterK
        (fun x => outerHeightProfile_nonneg hd)
        (fun x => outerHeightProfile_le_one hd) hR x
  have hWcIcc : ∀ j x, Wc j x ∈ Set.Icc (0 : ℝ) 1 := by
    intro j x
    simpa only [Wc, averagedHeightWeightOf] using
      paperFT_averagedHeightTestOf_real_mem_Icc hcoreC hcoreK
        (fun x => smoothHeightWindow_nonneg)
        (fun x => smoothHeightWindow_le_one) hR x
  have hWoProd : Integrable (fun x => ∏ j, Wo j x) := by
    have hpow := averagedHeightWeightOf_integrable houterC houterK hR
    have hcont := averagedHeightWeightOf_continuous houterC houterK hR
    have hprod : Integrable (fun x => Wo (0 : Fin (n + 1)) x *
        Wo (0 : Fin (n + 1)) x ^ n) := by
      refine hpow.mul_bdd (c := 1) (hcont.pow n).aestronglyMeasurable ?_
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (hWoIcc 0 x).1]
      exact pow_le_one₀ (hWoIcc 0 x).1 (hWoIcc 0 x).2
    convert hprod using 1
    funext x
    rw [show (∏ j, Wo j x) = Wo 0 x ^ (n + 1) by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    rw [pow_succ']
  have hWcProd : Integrable (fun x => ∏ j, Wc j x) := by
    have hpow := averagedHeightWeightOf_integrable hcoreC hcoreK hR
    have hcont := averagedHeightWeightOf_continuous hcoreC hcoreK hR
    have hprod : Integrable (fun x => Wc (0 : Fin (n + 1)) x *
        Wc (0 : Fin (n + 1)) x ^ n) := by
      refine hpow.mul_bdd (c := 1) (hcont.pow n).aestronglyMeasurable ?_
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (hWcIcc 0 x).1]
      exact pow_le_one₀ (hWcIcc 0 x).1 (hWcIcc 0 x).2
    convert hprod using 1
    funext x
    rw [show (∏ j, Wc j x) = Wc 0 x ^ (n + 1) by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    rw [pow_succ']
  unfold outerAveragedHeightFamily coreAveragedHeightFamily
  rw [rsHeightFactor_averagedHeightFamilyOf
      (H := constantHeightProfiles (n := n) (outerHeightProfile d))
      (fun _ => houterC) (fun _ => houterK) hR,
    rsHeightFactor_averagedHeightFamilyOf
      (H := constantHeightProfiles (n := n) (smoothHeightWindow w))
      (fun _ => hcoreC) (fun _ => hcoreK) hR]
  change ‖((∫ x, ∏ j, Wo j x : ℝ) : ℂ) -
    ((∫ x, ∏ j, Wc j x : ℝ) : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    ← integral_sub hWoProd hWcProd]
  have hcomponent : ∀ j ∈ Finset.univ,
      Integrable (fun x => |Wo j x - Wc j x|) := by
    intro j hj
    exact ((averagedHeightWeightOf_integrable houterC houterK hR).sub
      (averagedHeightWeightOf_integrable hcoreC hcoreK hR)).abs
  have hmajor : Integrable (fun x => ∑ j, |Wo j x - Wc j x|) :=
    integrable_finsetSum Finset.univ hcomponent
  have hle := norm_integral_le_of_norm_le hmajor
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_finset_prod_sub_prod_le_sum_abs_of_Icc Finset.univ
        (fun j => Wo j x) (fun j => Wc j x)
        (fun j _ => (hWoIcc j x).1) (fun j _ => (hWoIcc j x).2)
        (fun j _ => (hWcIcc j x).1) (fun j _ => (hWcIcc j x).2))
  calc
    |∫ x, (∏ j, Wo j x) - ∏ j, Wc j x| ≤
        ∫ x, ∑ j, |Wo j x - Wc j x| := hle
    _ = ∑ j, ∫ x, |Wo j x - Wc j x| :=
      integral_finsetSum Finset.univ hcomponent
    _ ≤ ∑ _j : Fin (n + 1), (4 * d + 2 * w) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Wo, Wc] using
        integral_abs_outerWeight_sub_coreWeight_le hd hw hw1 hR
    _ = (n + 1 : ℝ) * (4 * d + 2 * w) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_cast

theorem averagedHeightFamilyOf_admissible
    {n : ℕ} {H : Fin (n + 1) → ℝ → ℝ} {R : ℝ}
    (hH : ∀ j, Continuous (H j)) (hHc : ∀ j, HasCompactSupport (H j))
    (hR : 0 < R) :
    ∀ j, ContDiff ℝ ∞ (averagedHeightFamilyOf H R j) ∧
      HasCompactSupport (averagedHeightFamilyOf H R j) := by
  intro j
  exact ⟨averagedHeightTestOf_contDiff (hH j) (hHc j) hR,
    averagedHeightTestOf_hasCompactSupport _ hR⟩

theorem RSReduction.RS1996ZetaInputs.normalized_outer_sub_core_tendsto
    {Z : ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3) {d w R p delta mu : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hw1 : 2 * w ≤ 1) (hR : 0 < R)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) (m : ℕ) :
    Tendsto
      (fun T => RSReduction.normalizedRSZeroTupleSum Z
          (outerAveragedHeightFamily (n := n) d R)
          (RSReduction.weightedCyclicSymbol (k := n + 1) mu
            (RSReduction.smoothTopHat p
              (RSReduction.topHatSmoothingWidth p m))) T -
        RSReduction.normalizedRSZeroTupleSum Z
          (coreAveragedHeightFamily (n := n) w R)
          (RSReduction.weightedCyclicSymbol (k := n + 1) mu
            (RSReduction.smoothTopHat p
              (RSReduction.topHatSmoothingWidth p m))) T)
      atTop
      (𝓝 ((rsHeightFactor (outerAveragedHeightFamily (n := n) d R) -
          rsHeightFactor (coreAveragedHeightFamily (n := n) w R)) *
        rsMainTerm (RSReduction.weightedCyclicSymbol (k := n + 1) mu
          (RSReduction.smoothTopHat p
            (RSReduction.topHatSmoothingWidth p m))))) := by
  have houtAdm : ∀ j, ContDiff ℝ ∞
      (outerAveragedHeightFamily (n := n) d R j) ∧
      HasCompactSupport (outerAveragedHeightFamily (n := n) d R j) := by
    exact averagedHeightFamilyOf_admissible
      (fun _ => (outerHeightProfile_contDiff hd).continuous)
      (fun _ => outerHeightProfile_hasCompactSupport hd) hR
  have hcoreAdm : ∀ j, ContDiff ℝ ∞
      (coreAveragedHeightFamily (n := n) w R j) ∧
      HasCompactSupport (coreAveragedHeightFamily (n := n) w R j) := by
    exact averagedHeightFamilyOf_admissible
      (fun _ => (smoothHeightWindow_contDiff hw hw1).continuous)
      (fun _ => smoothHeightWindow_hasCompactSupport hw) hR
  have hout :=
    RH.Zeta85.RSReduction.RS1996ZetaInputs.normalized_fixedSmoothTopHatFamily_evaluated
      hRS n hn (outerAveragedHeightFamily (n := n) d R) houtAdm
        hp hp1 hdelta hmu hbudget
  have hcore :=
    RH.Zeta85.RSReduction.RS1996ZetaInputs.normalized_fixedSmoothTopHatFamily_evaluated
      hRS n hn (coreAveragedHeightFamily (n := n) w R) hcoreAdm
        hp hp1 hdelta hmu hbudget
  have hsub := (hout.1 m).sub (hcore.1 m)
  convert hsub using 1 <;> ring_nf

theorem rsOuterCoreMainDifference_tendsto_zero
    {n : ℕ} {p mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hmu : 0 < mu) :
    Tendsto
      (fun q : ℕ =>
        (rsHeightFactor (outerAveragedHeightFamily (n := n)
            (RSReduction.topHatSmoothingWidth 1 q) ((q : ℝ) + 1)) -
          rsHeightFactor (coreAveragedHeightFamily (n := n)
            (RSReduction.topHatSmoothingWidth 1 q) ((q : ℝ) + 1))) *
          rsMainTerm (RSReduction.weightedCyclicSymbol (k := n + 1) mu
            (RSReduction.smoothTopHat p
              (RSReduction.topHatSmoothingWidth p q))))
      atTop (𝓝 0) := by
  let wq : ℕ → ℝ := fun q => RSReduction.topHatSmoothingWidth 1 q
  let D : ℕ → ℂ := fun q =>
    rsHeightFactor (outerAveragedHeightFamily (n := n) (wq q) ((q : ℝ) + 1)) -
      rsHeightFactor (coreAveragedHeightFamily (n := n) (wq q) ((q : ℝ) + 1))
  let M : ℕ → ℂ := fun q =>
    rsMainTerm (RSReduction.weightedCyclicSymbol (k := n + 1) mu
      (RSReduction.smoothTopHat p (RSReduction.topHatSmoothingWidth p q)))
  have hwlim : Tendsto wq atTop (𝓝 0) := by
    simpa only [wq] using RSReduction.topHatSmoothingWidth_tendsto_zero 1
  have hboundlim : Tendsto (fun q : ℕ => (n + 1 : ℝ) * (6 * wq q))
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (n + 1 : ℝ) * 6) atTop
        (𝓝 ((n + 1 : ℝ) * 6)) := tendsto_const_nhds
    simpa only [mul_zero, mul_assoc] using hconst.mul hwlim
  have hDnorm : Tendsto (fun q => ‖D q‖) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun q => norm_nonneg (D q))
      (Eventually.of_forall fun q => ?_) hboundlim
    have hwpos := RSReduction.topHatSmoothingWidth_pos
      (show (0 : ℝ) < 1 by norm_num) q
    have hw1 := RSReduction.two_mul_topHatSmoothingWidth_le
      (show (0 : ℝ) < 1 by norm_num) q
    have h := norm_rsHeightFactor_outer_sub_core_le (n := n)
      hwpos hwpos hw1 (by positivity : 0 < (q : ℝ) + 1)
    simpa only [D, wq] using h.trans_eq (by ring)
  have hD : Tendsto D atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hDnorm
  have hM : Tendsto M atTop
      (𝓝 (rsMainTerm (RSReduction.weightedCyclicSymbol (k := n + 1) mu
        (RH.Zeta85.TopHatMoments.topHat p)))) := by
    simpa only [M] using
      RSReduction.rsMainTerm_smoothTopHat_tendsto_topHat
        (n := n) hp hp1 hmu
  simpa only [D, M, zero_mul] using hD.mul hM

theorem RSReduction.RS1996ZetaInputs.exists_outer_core_diagonal_tendsto_zero
    {Z : ZeroConfig} (hRS : RS1996ZetaInputs Z)
    (n : ℕ) (hn : n ≤ 3) {p delta mu : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hbudget : (n + 1 : ℝ) * mu + delta < 2) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      (∀ q, Summable (rsZeroTupleTerm Z
          (outerAveragedHeightFamily (n := n)
            (RSReduction.topHatSmoothingWidth 1 q) ((q : ℝ) + 1))
          (RSReduction.weightedCyclicSymbol (k := n + 1) mu
            (RSReduction.smoothTopHat p
              (RSReduction.topHatSmoothingWidth p q))) (T q)) ∧
        Summable (rsZeroTupleTerm Z
          (coreAveragedHeightFamily (n := n)
            (RSReduction.topHatSmoothingWidth 1 q) ((q : ℝ) + 1))
          (RSReduction.weightedCyclicSymbol (k := n + 1) mu
            (RSReduction.smoothTopHat p
              (RSReduction.topHatSmoothingWidth p q))) (T q))) ∧
      Tendsto
        (fun q : ℕ =>
          RSReduction.normalizedRSZeroTupleSum Z
              (outerAveragedHeightFamily (n := n)
                (RSReduction.topHatSmoothingWidth 1 q) ((q : ℝ) + 1))
              (RSReduction.weightedCyclicSymbol (k := n + 1) mu
                (RSReduction.smoothTopHat p
                  (RSReduction.topHatSmoothingWidth p q))) (T q) -
            RSReduction.normalizedRSZeroTupleSum Z
              (coreAveragedHeightFamily (n := n)
                (RSReduction.topHatSmoothingWidth 1 q) ((q : ℝ) + 1))
              (RSReduction.weightedCyclicSymbol (k := n + 1) mu
                (RSReduction.smoothTopHat p
                  (RSReduction.topHatSmoothingWidth p q))) (T q))
        atTop (𝓝 0) := by
  let wq : ℕ → ℝ := fun q => RSReduction.topHatSmoothingWidth 1 q
  let go : ℕ → Fin (n + 1) → ℝ → ℂ := fun q =>
    outerAveragedHeightFamily (n := n) (wq q) ((q : ℝ) + 1)
  let gc : ℕ → Fin (n + 1) → ℝ → ℂ := fun q =>
    coreAveragedHeightFamily (n := n) (wq q) ((q : ℝ) + 1)
  let Phi : ℕ → (Fin (n + 1) → ℝ) → ℂ := fun q =>
    RSReduction.weightedCyclicSymbol (k := n + 1) mu
      (RSReduction.smoothTopHat p (RSReduction.topHatSmoothingWidth p q))
  let f : ℕ → ℝ → ℂ := fun q T =>
    RSReduction.normalizedRSZeroTupleSum Z (go q) (Phi q) T -
      RSReduction.normalizedRSZeroTupleSum Z (gc q) (Phi q) T
  let a : ℕ → ℂ := fun q =>
    (rsHeightFactor (go q) - rsHeightFactor (gc q)) * rsMainTerm (Phi q)
  have hf (q : ℕ) : Tendsto (f q) atTop (𝓝 (a q)) := by
    simpa only [f, a, go, gc, Phi, wq] using
      RH.Zeta85.RSPoissonCyclicBridge.RSReduction.RS1996ZetaInputs.normalized_outer_sub_core_tendsto
        hRS n hn
        (RSReduction.topHatSmoothingWidth_pos (by norm_num) q)
        (RSReduction.topHatSmoothingWidth_pos (by norm_num) q)
        (RSReduction.two_mul_topHatSmoothingWidth_le (by norm_num) q)
        (by positivity : 0 < (q : ℝ) + 1)
        hp hp1 hdelta hmu hbudget q
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, go, gc, Phi, wq] using
      rsOuterCoreMainDifference_tendsto_zero (n := n) hp hp1 hmu
  have hgood (q : ℕ) : ∀ᶠ T : ℝ in atTop,
      Summable (rsZeroTupleTerm Z (go q) (Phi q) T) ∧
        Summable (rsZeroTupleTerm Z (gc q) (Phi q) T) := by
    have hwpos : 0 < wq q := RSReduction.topHatSmoothingWidth_pos
      (show (0 : ℝ) < 1 by norm_num) q
    have hw1 : 2 * wq q ≤ 1 := RSReduction.two_mul_topHatSmoothingWidth_le
      (show (0 : ℝ) < 1 by norm_num) q
    have hoAdm : ∀ j, ContDiff ℝ ∞ (go q j) ∧ HasCompactSupport (go q j) := by
      exact averagedHeightFamilyOf_admissible
        (fun _ => (outerHeightProfile_contDiff hwpos).continuous)
        (fun _ => outerHeightProfile_hasCompactSupport hwpos) (by positivity)
    have hcAdm : ∀ j, ContDiff ℝ ∞ (gc q j) ∧ HasCompactSupport (gc q j) := by
      exact averagedHeightFamilyOf_admissible
        (fun _ => (smoothHeightWindow_contDiff hwpos hw1).continuous)
        (fun _ => smoothHeightWindow_hasCompactSupport hwpos) (by positivity)
    obtain ⟨hoFixed, _⟩ :=
      RH.Zeta85.RSReduction.RS1996ZetaInputs.theorem31_fixedSmoothTopHatFamily_evaluated
        hRS n hn (go q) hoAdm hp hp1 hdelta hmu hbudget
    obtain ⟨hcFixed, _⟩ :=
      RH.Zeta85.RSReduction.RS1996ZetaInputs.theorem31_fixedSmoothTopHatFamily_evaluated
        hRS n hn (gc q) hcAdm hp hp1 hdelta hmu hbudget
    obtain ⟨Co, To, hCo, hTo, hobound⟩ := hoFixed q
    obtain ⟨Cc, Tc, hCc, hTc, hcbound⟩ := hcFixed q
    filter_upwards [eventually_ge_atTop To, eventually_ge_atTop Tc] with T hToT hTcT
    exact ⟨(hobound T hToT).1, (hcbound T hTcT).1⟩
  let eps : ℕ → ℝ := fun q => 1 / ((q : ℝ) + 1)
  have heps : ∀ q, 0 < eps q := fun q => by dsimp [eps]; positivity
  have hTexists : ∀ q : ℕ, ∃ T : ℝ, (q : ℝ) ≤ T ∧
      (Summable (rsZeroTupleTerm Z (go q) (Phi q) T) ∧
        Summable (rsZeroTupleTerm Z (gc q) (Phi q) T)) ∧
      dist (f q T) (a q) < eps q := by
    intro q
    exact ((eventually_ge_atTop (q : ℝ)).and
      ((hgood q).and (Metric.tendsto_nhds.1 (hf q) (eps q) (heps q)))).exists
  choose T hTlarge hTgood hTclose using hTexists
  refine ⟨T, tendsto_atTop_mono hTlarge tendsto_natCast_atTop_atTop,
    hTgood, ?_⟩
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    have hden : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa only [eps] using tendsto_const_nhds.div_atTop hden
  have hdist : Tendsto (fun q => dist (a q) (f q (T q))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
      (Eventually.of_forall fun q => ?_) heps0
    simpa only [dist_comm] using (hTclose q).le
  have hdiag : Tendsto (fun q => f q (T q)) atTop (𝓝 0) := ha.congr_dist hdist
  simpa only [f, go, gc, Phi, wq] using hdiag

end RH.Zeta85.RSPoissonCyclicBridge
