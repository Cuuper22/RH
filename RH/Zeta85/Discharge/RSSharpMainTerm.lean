/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.RSPairIntegrals

/-!
# Sharp evaluation and fixed-test smoothing of the Rudnick--Sarnak main term

This module constructs a canonical smooth approximation to the sharp top hat
and proves that every disjoint-pair contraction, hence the complete
Rudnick--Sarnak main term, converges to its sharp counterpart.  The estimate
is quantitative and linear in the taper width.  Crucially, Rudnick--Sarnak is
therefore applied only to fixed smooth test data; the taper width is sent to
zero afterwards.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators Matrix ContDiff Convolution

noncomputable section

namespace RH.Zeta85.RSReduction

open TopHatMoments

theorem topHat_stronglyMeasurable (p : ℝ) :
    StronglyMeasurable (topHat p) := by
  unfold topHat topHatSupport
  exact stronglyMeasurable_const.indicator measurableSet_Icc

theorem weightedCyclicSymbol_stronglyMeasurable {k : ℕ}
    (mu : ℝ) (r : ℝ → ℝ) (hr : StronglyMeasurable r) :
    StronglyMeasurable (weightedCyclicSymbol (k := k) mu r) := by
  have hjoint : StronglyMeasurable
      (fun z : (Fin k → ℝ) × ℝ =>
        ∏ a : Fin k, r (z.2 + cyclicPartialSum z.1 a / mu)) := by
    apply Finset.stronglyMeasurable_fun_prod Finset.univ
    intro a ha
    apply hr.comp_measurable
    have hpartial : Continuous
        (fun xi : Fin k → ℝ => cyclicPartialSum xi a) := by
      unfold cyclicPartialSum
      fun_prop
    exact (continuous_snd.add
      ((hpartial.comp continuous_fst).div_const mu)).measurable
  unfold weightedCyclicSymbol
  exact Complex.continuous_ofReal.comp_stronglyMeasurable
    ((hjoint.integral_prod_right').const_mul mu)

theorem topHatSupport_subset_baseWindow {p : ℝ} (hp1 : p ≤ 1) :
    topHatSupport p ⊆ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  intro x hx
  unfold topHatSupport at hx
  constructor <;> linarith [hx.1, hx.2]

theorem topHat_support_subset_baseWindow {p : ℝ} (hp1 : p ≤ 1) :
    Function.support (topHat p) ⊆ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  intro x hx
  by_contra hout
  apply hx
  simp [topHat, Set.indicator_of_notMem
    (fun h => hout (topHatSupport_subset_baseWindow hp1 h))]

theorem weightedCyclicSymbol_topHat_norm_le {n : ℕ}
    {p mu : ℝ} (hp : 0 < p) (hmu : 0 < mu)
    (xi : Fin (n + 1) → ℝ) :
    ‖weightedCyclicSymbol mu (topHat p) xi‖ ≤
      mu * (max 1 (1 / p)) ^ (n + 1) * p := by
  let C : ℝ := max 1 (1 / p)
  have hC : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
  have hfactor (z : ℝ) : |topHat p z| ≤ C := by
    by_cases hz : z ∈ topHatSupport p
    · simp [topHat, hz, abs_of_pos hp, C]
    · simp [topHat, hz, C, hC]
  have ha0 : cyclicPartialSum xi (0 : Fin (n + 1)) = 0 := by
    simp [cyclicPartialSum]
  have hpoint (x : ℝ) :
      |∏ a : Fin (n + 1),
          topHat p (x + cyclicPartialSum xi a / mu)| ≤
        (topHatSupport p).indicator (fun _ => C ^ (n + 1)) x := by
    by_cases hx : x ∈ topHatSupport p
    · rw [Set.indicator_of_mem hx, Finset.abs_prod]
      calc
        (∏ a : Fin (n + 1),
            |topHat p (x + cyclicPartialSum xi a / mu)|) ≤
            ∏ _a : Fin (n + 1), C :=
          Finset.prod_le_prod (s := Finset.univ)
            (fun a _ => abs_nonneg _)
            (fun a _ => hfactor _)
        _ = C ^ (n + 1) := by simp
    · rw [Set.indicator_of_notMem hx]
      have hzero : (∏ a : Fin (n + 1),
          topHat p (x + cyclicPartialSum xi a / mu)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n + 1)))
        rw [ha0, zero_div, add_zero, topHat,
          Set.indicator_of_notMem hx]
      simp [hzero]
  have hupper : Integrable
      ((topHatSupport p).indicator (fun _ => C ^ (n + 1))) := by
    unfold topHatSupport
    exact (integrableOn_const (s := Set.Icc (-p / 2) (p / 2))
      (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  unfold weightedCyclicSymbol
  change ‖((mu * ∫ x : ℝ, ∏ a : Fin (n + 1),
    topHat p (x + cyclicPartialSum xi a / mu) : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hmu]
  calc
    mu * |∫ x : ℝ, ∏ a : Fin (n + 1),
        topHat p (x + cyclicPartialSum xi a / mu)| ≤
        mu * ∫ x : ℝ, |∏ a : Fin (n + 1),
          topHat p (x + cyclicPartialSum xi a / mu)| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hmu.le
    _ ≤ mu * ∫ x : ℝ,
        (topHatSupport p).indicator (fun _ => C ^ (n + 1)) x := by
      exact mul_le_mul_of_nonneg_left
        (integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) hupper
          (Eventually.of_forall hpoint)) hmu.le
    _ = mu * C ^ (n + 1) * p := by
      rw [integral_indicator_const _ (by simp [topHatSupport])]
      unfold topHatSupport
      rw [Real.volume_real_Icc_of_le (by linarith)]
      simp only [smul_eq_mul]
      ring
    _ = mu * (max 1 (1 / p)) ^ (n + 1) * p := by rfl

theorem rsPairVector_fst_of_mem_rsPairings {n q : ℕ}
    {pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))}
    (hpair : pairing ∈ rsPairings n q) (w : Fin q → ℝ) (a : Fin q) :
    rsPairVector pairing w (pairing.1 a) = w a := by
  have hp := (Finset.mem_filter.mp hpair).2
  rcases hp with ⟨hmono, hinj, hlt, hcross⟩
  unfold rsPairVector
  rw [Finset.sum_eq_single a]
  · simp [ne_of_gt (hlt a)]
  · intro b hb hba
    have hfst : pairing.1 b ≠ pairing.1 a := by
      intro heq
      exact hba (hmono.injective heq)
    have hsnd : pairing.2 b ≠ pairing.1 a := (hcross a b).symm
    simp [hfst, hsnd]
  · simp

theorem abs_rsPairVector_fst_le_sum {n q : ℕ}
    (pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1)))
    (w : Fin q → ℝ) (a : Fin q) :
    |rsPairVector pairing w (pairing.1 a)| ≤
      ∑ i : Fin (n + 1), |rsPairVector pairing w i| := by
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun i : Fin (n + 1) => |rsPairVector pairing w i|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ (pairing.1 a))

theorem weightedCyclicSymbol_rsPairVector_coordinate_bound
    {n q : ℕ} {mu : ℝ} (hmu : 0 < mu) (r : ℝ → ℝ)
    (hrsupp : Function.support r ⊆
      Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    {pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))}
    (hpair : pairing ∈ rsPairings n q) (w : Fin q → ℝ)
    (hPhi : weightedCyclicSymbol (k := n + 1) mu r
      (rsPairVector pairing w) ≠ 0) (a : Fin q) :
    |w a| ≤ (n + 1 : ℝ) * mu + 1 := by
  have hgauge : gaugeFixedCyclicSymbol (k := n + 1) 1 mu r
      (rsPairVector pairing w) ≠ 0 := by
    rw [gaugeFixedCyclicSymbol_rsPairVector one_pos mu r pairing w]
    exact hPhi
  have htotal := gaugeFixedCyclicSymbol_support_subset
    one_pos hmu r hrsupp hgauge
  rw [← rsPairVector_fst_of_mem_rsPairings hpair w a]
  exact (abs_rsPairVector_fst_le_sum pairing w a).trans htotal

theorem weightedCyclicSymbol_rsPairVector_eq_zero_outside_box
    {n q : ℕ} {mu : ℝ} (hmu : 0 < mu) (r : ℝ → ℝ)
    (hrsupp : Function.support r ⊆
      Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    {pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))}
    (hpair : pairing ∈ rsPairings n q) (w : Fin q → ℝ)
    (hout : w ∉ Set.Icc
      (fun _ : Fin q => -((n + 1 : ℝ) * mu + 1))
      (fun _ : Fin q => (n + 1 : ℝ) * mu + 1)) :
    weightedCyclicSymbol (k := n + 1) mu r
      (rsPairVector pairing w) = 0 := by
  let B : ℝ := (n + 1 : ℝ) * mu + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ha : ∃ a : Fin q, B < |w a| := by
    by_contra h
    push_neg at h
    apply hout
    constructor
    · intro a
      exact (abs_le.mp (h a)).1
    · intro a
      exact (abs_le.mp (h a)).2
  obtain ⟨a, ha⟩ := ha
  by_contra hPhi
  have hbound := weightedCyclicSymbol_rsPairVector_coordinate_bound
    hmu r hrsupp hpair w hPhi a
  exact (not_lt_of_ge hbound) ha

theorem rsPairVector_continuous {n q : ℕ}
    (pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))) :
    Continuous (fun w : Fin q → ℝ => rsPairVector pairing w) := by
  apply continuous_pi
  intro i
  unfold rsPairVector
  apply continuous_finset_sum
  intro a ha
  by_cases hfst : pairing.1 a = i <;>
    by_cases hsnd : pairing.2 a = i <;>
      simp [hfst, hsnd] <;> fun_prop

theorem rsPairIntegrand_stronglyMeasurable {n q : ℕ}
    (Phi : (Fin (n + 1) → ℝ) → ℂ) (hPhi : StronglyMeasurable Phi)
    (pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))) :
    StronglyMeasurable (fun w : Fin q → ℝ =>
      (∏ a : Fin q, |w a| : ℝ) * Phi (rsPairVector pairing w)) := by
  have hweight : StronglyMeasurable
      (fun w : Fin q → ℝ => ∏ a : Fin q, |w a|) := by fun_prop
  have hcomp : StronglyMeasurable
      (fun w : Fin q → ℝ => Phi (rsPairVector pairing w)) :=
    hPhi.comp_measurable (rsPairVector_continuous pairing).measurable
  exact (Complex.continuous_ofReal.comp_stronglyMeasurable hweight).mul hcomp

theorem rsPairIntegrand_integrable_of_box_bound {n q : ℕ}
    (Phi : (Fin (n + 1) → ℝ) → ℂ) (hPhi : StronglyMeasurable Phi)
    (pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1)))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hzero : ∀ w : Fin q → ℝ,
      w ∉ Set.Icc (fun _ : Fin q => -B) (fun _ : Fin q => B) →
        Phi (rsPairVector pairing w) = 0)
    (hbound : ∀ w : Fin q → ℝ,
      w ∈ Set.Icc (fun _ : Fin q => -B) (fun _ : Fin q => B) →
        ‖Phi (rsPairVector pairing w)‖ ≤ M) :
    Integrable (fun w : Fin q → ℝ =>
      (∏ a : Fin q, |w a| : ℝ) * Phi (rsPairVector pairing w)) := by
  let box : Set (Fin q → ℝ) :=
    Set.Icc (fun _ : Fin q => -B) (fun _ : Fin q => B)
  let K : ℝ := B ^ q * M
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hB _) hM
  have hconst : Integrable
      (box.indicator (fun _ => (K : ℂ))) := by
    apply IntegrableOn.integrable_indicator
      (integrableOn_const (s := box) (by simp [box, Real.volume_Icc_pi]))
      (by simp [box])
  apply hconst.mono
    (rsPairIntegrand_stronglyMeasurable Phi hPhi pairing).aestronglyMeasurable
  filter_upwards [] with w
  by_cases hw : w ∈ box
  · have hcoord (a : Fin q) : |w a| ≤ B := by
      have hlo : -B ≤ w a := hw.1 a
      have hhi : w a ≤ B := hw.2 a
      exact abs_le.mpr ⟨hlo, hhi⟩
    have hprod : (∏ a : Fin q, |w a|) ≤ B ^ q := by
      calc
        (∏ a : Fin q, |w a|) ≤ ∏ _a : Fin q, B :=
          Finset.prod_le_prod (s := Finset.univ)
          (fun a _ => abs_nonneg (w a))
          (fun a _ => hcoord a)
        _ = B ^ q := by simp
    rw [Set.indicator_of_mem hw]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun a _ => abs_nonneg (w a)),
      abs_of_nonneg hK]
    exact mul_le_mul hprod (hbound w hw) (norm_nonneg _) (pow_nonneg hB _)
  · rw [hzero w hw, mul_zero, norm_zero, Set.indicator_of_notMem hw,
      norm_zero]

theorem rsPairIntegrand_topHat_integrable {n q : ℕ}
    {p mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hmu : 0 < mu)
    {pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))}
    (hpair : pairing ∈ rsPairings n q) :
    Integrable (fun v : Fin q → ℝ =>
      (∏ a : Fin q, |v a| : ℝ) *
        weightedCyclicSymbol (k := n + 1) mu (topHat p)
          (rsPairVector pairing v)) := by
  let B : ℝ := (n + 1 : ℝ) * mu + 1
  let M : ℝ := mu * (max 1 (1 / p)) ^ (n + 1) * p
  apply rsPairIntegrand_integrable_of_box_bound
    (weightedCyclicSymbol (k := n + 1) mu (topHat p))
    (weightedCyclicSymbol_stronglyMeasurable mu (topHat p)
      (topHat_stronglyMeasurable p)) pairing
    (B := B) (M := M)
  · dsimp [B]
    positivity
  · dsimp [M]
    positivity
  · intro v hv
    exact weightedCyclicSymbol_rsPairVector_eq_zero_outside_box
      hmu (topHat p) (topHat_support_subset_baseWindow hp1)
      hpair v hv
  · intro v hv
    exact weightedCyclicSymbol_topHat_norm_le hp hmu _

theorem rsPairIntegrand_smoothSub_integrable {n q : ℕ}
    {p w mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hw : 0 < w) (hwp : 2 * w ≤ p) (hmu : 0 < mu)
    {pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))}
    (hpair : pairing ∈ rsPairings n q) :
    Integrable (fun v : Fin q → ℝ =>
      (∏ a : Fin q, |v a| : ℝ) *
        (weightedCyclicSymbol (k := n + 1) mu (smoothTopHat p w)
            (rsPairVector pairing v) -
          weightedCyclicSymbol (k := n + 1) mu (topHat p)
            (rsPairVector pairing v))) := by
  let B : ℝ := (n + 1 : ℝ) * mu + 1
  let E : ℝ := mu * (max 1 (1 / p)) ^ (n + 1) *
    (n + 1) * (2 * w / p)
  have hsmoothSupport : Function.support (smoothTopHat p w) ⊆
      Set.Icc (-(1 : ℝ) / 2) (1 / 2) :=
    (smoothTopHat_support hw).trans (topHatSupport_subset_baseWindow hp1)
  have hsharpSupport : Function.support (topHat p) ⊆
      Set.Icc (-(1 : ℝ) / 2) (1 / 2) :=
    topHat_support_subset_baseWindow hp1
  apply rsPairIntegrand_integrable_of_box_bound
    (fun xi =>
      weightedCyclicSymbol (k := n + 1) mu (smoothTopHat p w) xi -
        weightedCyclicSymbol (k := n + 1) mu (topHat p) xi)
    ((weightedCyclicSymbol_stronglyMeasurable mu (smoothTopHat p w)
        (smoothTopHat_contDiff hw hwp).continuous.stronglyMeasurable).sub
      (weightedCyclicSymbol_stronglyMeasurable mu (topHat p)
        (topHat_stronglyMeasurable p))) pairing
    (B := B) (M := E)
  · dsimp [B]
    positivity
  · dsimp [E]
    positivity
  · intro v hv
    rw [weightedCyclicSymbol_rsPairVector_eq_zero_outside_box
        hmu (smoothTopHat p w) hsmoothSupport hpair v hv,
      weightedCyclicSymbol_rsPairVector_eq_zero_outside_box
        hmu (topHat p) hsharpSupport hpair v hv,
      sub_zero]
  · intro v hv
    dsimp [E]
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      (weightedCyclicSymbol_smoothTopHat_sub_topHat_le
        hp hw hwp hmu (Nat.succ_le_succ (Nat.zero_le n))
        (rsPairVector pairing v))

theorem norm_rsPairIntegral_smoothTopHat_sub_topHat_le {n q : ℕ}
    {p w mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hw : 0 < w) (hwp : 2 * w ≤ p) (hmu : 0 < mu)
    {pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))}
    (hpair : pairing ∈ rsPairings n q) :
    ‖rsPairIntegral
          (weightedCyclicSymbol (k := n + 1) mu (smoothTopHat p w)) pairing -
        rsPairIntegral
          (weightedCyclicSymbol (k := n + 1) mu (topHat p)) pairing‖ ≤
      (((n + 1 : ℝ) * mu + 1) ^ q *
        (mu * (max 1 (1 / p)) ^ (n + 1) *
          (n + 1) * (2 * w / p))) *
        (2 * ((n + 1 : ℝ) * mu + 1)) ^ q := by
  let B : ℝ := (n + 1 : ℝ) * mu + 1
  let E : ℝ := mu * (max 1 (1 / p)) ^ (n + 1) *
    (n + 1) * (2 * w / p)
  let PhiS : (Fin (n + 1) → ℝ) → ℂ :=
    weightedCyclicSymbol (k := n + 1) mu (smoothTopHat p w)
  let PhiT : (Fin (n + 1) → ℝ) → ℂ :=
    weightedCyclicSymbol (k := n + 1) mu (topHat p)
  let fS : (Fin q → ℝ) → ℂ := fun v =>
    (∏ a : Fin q, |v a| : ℝ) * PhiS (rsPairVector pairing v)
  let fT : (Fin q → ℝ) → ℂ := fun v =>
    (∏ a : Fin q, |v a| : ℝ) * PhiT (rsPairVector pairing v)
  let fDiff : (Fin q → ℝ) → ℂ := fun v =>
    (∏ a : Fin q, |v a| : ℝ) *
      (PhiS (rsPairVector pairing v) - PhiT (rsPairVector pairing v))
  let box : Set (Fin q → ℝ) :=
    Set.Icc (fun _ : Fin q => -B) (fun _ : Fin q => B)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hsmoothSupport : Function.support (smoothTopHat p w) ⊆
      Set.Icc (-(1 : ℝ) / 2) (1 / 2) :=
    (smoothTopHat_support hw).trans (topHatSupport_subset_baseWindow hp1)
  have hsharpSupport : Function.support (topHat p) ⊆
      Set.Icc (-(1 : ℝ) / 2) (1 / 2) :=
    topHat_support_subset_baseWindow hp1
  have hsharpInt : Integrable fT := by
    simpa only [fT, PhiT] using
      (rsPairIntegrand_topHat_integrable hp hp1 hmu hpair)
  have hdiffInt : Integrable fDiff := by
    simpa only [fDiff, PhiS, PhiT] using
      (rsPairIntegrand_smoothSub_integrable hp hp1 hw hwp hmu hpair)
  have hsmoothInt : Integrable fS := by
    apply (hdiffInt.add hsharpInt).congr
    filter_upwards [] with v
    dsimp [fS, fDiff, fT, PhiS, PhiT]
    ring
  unfold rsPairIntegral
  change ‖(∫ v, fS v) - ∫ v, fT v‖ ≤ _
  rw [← integral_sub hsmoothInt hsharpInt]
  have hsub : (fun v => fS v - fT v) = fDiff := by
    funext v
    dsimp [fS, fDiff, fT]
    ring
  rw [hsub]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := box) (f := fDiff) (fun v hv => by
      dsimp [fDiff, PhiS, PhiT]
      rw [weightedCyclicSymbol_rsPairVector_eq_zero_outside_box
          hmu (smoothTopHat p w) hsmoothSupport hpair v hv,
        weightedCyclicSymbol_rsPairVector_eq_zero_outside_box
          hmu (topHat p) hsharpSupport hpair v hv,
        sub_zero, mul_zero])]
  calc
    ‖∫ v in box, fDiff v‖ ≤ (B ^ q * E) * volume.real box := by
      apply norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
      intro v hv
      have hcoord (a : Fin q) : |v a| ≤ B := by
        exact abs_le.mpr ⟨hv.1 a, hv.2 a⟩
      have hprod : (∏ a : Fin q, |v a|) ≤ B ^ q := by
        calc
          (∏ a : Fin q, |v a|) ≤ ∏ _a : Fin q, B :=
            Finset.prod_le_prod (s := Finset.univ)
              (fun a _ => abs_nonneg (v a))
              (fun a _ => hcoord a)
          _ = B ^ q := by simp
      have hsymbol :
          ‖PhiS (rsPairVector pairing v) -
              PhiT (rsPairVector pairing v)‖ ≤ E := by
        dsimp [PhiS, PhiT, E]
        simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
          (weightedCyclicSymbol_smoothTopHat_sub_topHat_le
            hp hw hwp hmu (Nat.succ_le_succ (Nat.zero_le n))
            (rsPairVector pairing v))
      dsimp [fDiff]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg fun a _ => abs_nonneg (v a))]
      exact mul_le_mul hprod hsymbol (norm_nonneg _) (pow_nonneg hB _)
    _ = (B ^ q * E) * (2 * B) ^ q := by
      dsimp [box]
      rw [measureReal_def, Real.volume_Icc_pi_toReal]
      · simp only [Fin.prod_const]
        congr 2
        ring
      · intro a
        dsimp
        linarith
    _ = (((n + 1 : ℝ) * mu + 1) ^ q *
        (mu * (max 1 (1 / p)) ^ (n + 1) *
          (n + 1) * (2 * w / p))) *
        (2 * ((n + 1 : ℝ) * mu + 1)) ^ q := by
      rfl

theorem norm_rsMainTerm_smoothTopHat_sub_topHat_le {n : ℕ}
    {p w mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hw : 0 < w) (hwp : 2 * w ≤ p) (hmu : 0 < mu) :
    ‖rsMainTerm
          (weightedCyclicSymbol (k := n + 1) mu (smoothTopHat p w)) -
        rsMainTerm
          (weightedCyclicSymbol (k := n + 1) mu (topHat p))‖ ≤
      (let B : ℝ := (n + 1 : ℝ) * mu + 1
       let A : ℝ := mu * (max 1 (1 / p)) ^ (n + 1) *
         (n + 1) * (2 / p)
       (A + ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          ∑ _pairing ∈ rsPairings n q,
            B ^ q * A * (2 * B) ^ q) * w) := by
  let B : ℝ := (n + 1 : ℝ) * mu + 1
  let A : ℝ := mu * (max 1 (1 / p)) ^ (n + 1) *
    (n + 1) * (2 / p)
  let PhiS : (Fin (n + 1) → ℝ) → ℂ :=
    weightedCyclicSymbol (k := n + 1) mu (smoothTopHat p w)
  let PhiT : (Fin (n + 1) → ℝ) → ℂ :=
    weightedCyclicSymbol (k := n + 1) mu (topHat p)
  have hzero : ‖PhiS 0 - PhiT 0‖ ≤ A * w := by
    have h := weightedCyclicSymbol_smoothTopHat_sub_topHat_le
      hp hw hwp hmu (Nat.succ_le_succ (Nat.zero_le n))
      (0 : Fin (n + 1) → ℝ)
    dsimp [PhiS, PhiT, A]
    convert h using 1 <;>
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] <;>
      ring
  have hpair {q : ℕ}
      (pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1)))
      (hpairing : pairing ∈ rsPairings n q) :
      ‖rsPairIntegral PhiS pairing - rsPairIntegral PhiT pairing‖ ≤
        (B ^ q * A * (2 * B) ^ q) * w := by
    have h := norm_rsPairIntegral_smoothTopHat_sub_topHat_le
      hp hp1 hw hwp hmu hpairing
    dsimp [PhiS, PhiT, B, A]
    calc
      ‖rsPairIntegral
            (weightedCyclicSymbol (k := n + 1) mu (smoothTopHat p w)) pairing -
          rsPairIntegral
            (weightedCyclicSymbol (k := n + 1) mu (topHat p)) pairing‖ ≤
          (((n + 1 : ℝ) * mu + 1) ^ q *
            (mu * max 1 (1 / p) ^ (n + 1) *
              (n + 1) * (2 * w / p))) *
            (2 * ((n + 1 : ℝ) * mu + 1)) ^ q := h
      _ = ((((n + 1 : ℝ) * mu + 1) ^ q *
            (mu * max 1 (1 / p) ^ (n + 1) *
              (n + 1) * (2 / p)) *
            (2 * ((n + 1 : ℝ) * mu + 1)) ^ q) * w) := by ring
  have hmain : rsMainTerm PhiS - rsMainTerm PhiT =
      (PhiS 0 - PhiT 0) +
        ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          ∑ pairing ∈ rsPairings n q,
            (rsPairIntegral PhiS pairing - rsPairIntegral PhiT pairing) := by
    unfold rsMainTerm
    calc
      PhiS 0 +
            (∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
              ∑ pairing ∈ rsPairings n q, rsPairIntegral PhiS pairing) -
          (PhiT 0 +
            ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
              ∑ pairing ∈ rsPairings n q, rsPairIntegral PhiT pairing) =
          (PhiS 0 - PhiT 0) +
            ((∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
                ∑ pairing ∈ rsPairings n q, rsPairIntegral PhiS pairing) -
              ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
                ∑ pairing ∈ rsPairings n q,
                  rsPairIntegral PhiT pairing) := by ring
      _ = (PhiS 0 - PhiT 0) +
            ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
              ((∑ pairing ∈ rsPairings n q,
                  rsPairIntegral PhiS pairing) -
                ∑ pairing ∈ rsPairings n q,
                  rsPairIntegral PhiT pairing) := by
        rw [Finset.sum_sub_distrib]
      _ = (PhiS 0 - PhiT 0) +
            ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
              ∑ pairing ∈ rsPairings n q,
                (rsPairIntegral PhiS pairing -
                  rsPairIntegral PhiT pairing) := by
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_sub_distrib]
  rw [hmain]
  calc
    ‖(PhiS 0 - PhiT 0) +
        ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          ∑ pairing ∈ rsPairings n q,
            (rsPairIntegral PhiS pairing - rsPairIntegral PhiT pairing)‖ ≤
        ‖PhiS 0 - PhiT 0‖ +
          ‖∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
            ∑ pairing ∈ rsPairings n q,
              (rsPairIntegral PhiS pairing - rsPairIntegral PhiT pairing)‖ :=
      norm_add_le _ _
    _ ≤ ‖PhiS 0 - PhiT 0‖ +
        ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          ‖∑ pairing ∈ rsPairings n q,
            (rsPairIntegral PhiS pairing - rsPairIntegral PhiT pairing)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ‖PhiS 0 - PhiT 0‖ +
        ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          ∑ pairing ∈ rsPairings n q,
            ‖rsPairIntegral PhiS pairing -
              rsPairIntegral PhiT pairing‖ := by
      gcongr with q hq
      exact norm_sum_le _ _
    _ ≤ A * w +
        ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          ∑ _pairing ∈ rsPairings n q,
            (B ^ q * A * (2 * B) ^ q) * w := by
      gcongr with q hq pairing hpairing
      exact hpair pairing hpairing
    _ = (A + ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          ∑ _pairing ∈ rsPairings n q,
            B ^ q * A * (2 * B) ^ q) * w := by
      simp_rw [← Finset.sum_mul]
      ring

def topHatSmoothingWidth (p : ℝ) (m : ℕ) : ℝ :=
  (p / 2) * (1 / ((m : ℝ) + 1))

theorem topHatSmoothingWidth_pos {p : ℝ} (hp : 0 < p) (m : ℕ) :
    0 < topHatSmoothingWidth p m := by
  unfold topHatSmoothingWidth
  positivity

theorem two_mul_topHatSmoothingWidth_le {p : ℝ} (hp : 0 < p) (m : ℕ) :
    2 * topHatSmoothingWidth p m ≤ p := by
  unfold topHatSmoothingWidth
  rw [show 2 * (p / 2 * (1 / ((m : ℝ) + 1))) =
      p / ((m : ℝ) + 1) by ring]
  exact div_le_self hp.le (by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith)

theorem topHatSmoothingWidth_tendsto_zero (p : ℝ) :
    Tendsto (topHatSmoothingWidth p) atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => p / 2) atTop (𝓝 (p / 2)) :=
    tendsto_const_nhds
  have hone : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h := hconst.mul hone
  change Tendsto (fun m : ℕ =>
    (p / 2) * (1 / ((m : ℝ) + 1))) atTop (𝓝 0)
  simpa only [mul_zero] using h

theorem rsMainTerm_smoothTopHat_tendsto_topHat {n : ℕ}
    {p mu : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hmu : 0 < mu) :
    Tendsto
      (fun m : ℕ => rsMainTerm
        (weightedCyclicSymbol (k := n + 1) mu
          (smoothTopHat p (topHatSmoothingWidth p m))))
      atTop
      (𝓝 (rsMainTerm
        (weightedCyclicSymbol (k := n + 1) mu (topHat p)))) := by
  let B : ℝ := (n + 1 : ℝ) * mu + 1
  let A : ℝ := mu * (max 1 (1 / p)) ^ (n + 1) *
    (n + 1) * (2 / p)
  let K : ℝ := A + ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
    ∑ _pairing ∈ rsPairings n q, B ^ q * A * (2 * B) ^ q
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero
    (g := fun m : ℕ => K * topHatSmoothingWidth p m)
    (fun _ => norm_nonneg _) (fun m => ?_) ?_
  · simpa only [K, B, A] using
      (norm_rsMainTerm_smoothTopHat_sub_topHat_le
        hp hp1 (topHatSmoothingWidth_pos hp m)
        (two_mul_topHatSmoothingWidth_le hp m) hmu)
  · simpa using
      ((show Tendsto (fun _ : ℕ => K) atTop (𝓝 K) from tendsto_const_nhds).mul
        (topHatSmoothingWidth_tendsto_zero p) :
        Tendsto (fun m : ℕ => K * topHatSmoothingWidth p m)
          atTop (𝓝 (K * 0)))

end RH.Zeta85.RSReduction
