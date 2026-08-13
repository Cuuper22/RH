import RH.Zeta85.Discharge.RSHeightRemoteDecay
import Zeta23.Tail

/-!
# Gap-parametrized fourth-order zero tails

The standard tail count fixes the physical gap at `sqrt T`.  The dyadic
height selector instead supplies a freely chosen normalized gap.  Keeping
that gap through the unit-window count gives the fourth-order summability
needed by the remote height argument.
-/

open Filter Topology Finset Real
open scoped BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def remoteTailCubicWindowBound (T D : ℝ) : ℝ :=
  (2 * (D ^ 3)⁻¹ + (D ^ 2)⁻¹ / 2) * Real.log (2 * T + 4) +
    (2 * (D ^ 2)⁻¹ + D⁻¹) / (2 * T + 4)

theorem remoteTailCubicWindowBound_le
    {T D : ℝ} (hT : 6 ≤ T) (hD : 2 ≤ D) (hDT : D ≤ T) :
    remoteTailCubicWindowBound T D ≤
      5 * (D ^ 2)⁻¹ * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hDpos : 0 < D := by linarith
  have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogTone : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    nlinarith [Real.exp_one_lt_d9]
  have hlogB : Real.log (2 * T + 4) ≤ 2 * Real.log T := by
    have hB4 : 2 * T + 4 ≤ 4 * T := by linarith
    have hmono := Real.log_le_log (by linarith : 0 < 2 * T + 4) hB4
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hTpos.ne'] at hmono
    have hlog4 : Real.log 4 ≤ Real.log T :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hcoef :
      2 * (D ^ 3)⁻¹ + (D ^ 2)⁻¹ / 2 ≤ 2 * (D ^ 2)⁻¹ := by
    field_simp [hDpos.ne']
    nlinarith
  have hfirst :
      (2 * (D ^ 3)⁻¹ + (D ^ 2)⁻¹ / 2) * Real.log (2 * T + 4) ≤
        4 * (D ^ 2)⁻¹ * Real.log T := by
    calc
      (2 * (D ^ 3)⁻¹ + (D ^ 2)⁻¹ / 2) * Real.log (2 * T + 4) ≤
          (2 * (D ^ 2)⁻¹) * (2 * Real.log T) := by
        exact mul_le_mul hcoef hlogB
          (Real.log_nonneg (by linarith)) (by positivity)
      _ = 4 * (D ^ 2)⁻¹ * Real.log T := by ring
  have hnum : 2 * (D ^ 2)⁻¹ + D⁻¹ ≤ 2 * D⁻¹ := by
    field_simp [hDpos.ne']
    nlinarith
  have hquot :
      (2 * (D ^ 2)⁻¹ + D⁻¹) / (2 * T + 4) ≤ D⁻¹ / T := by
    calc
      (2 * (D ^ 2)⁻¹ + D⁻¹) / (2 * T + 4) ≤
          (2 * D⁻¹) / (2 * T) := by
        exact div_le_div₀ (by positivity) hnum (by positivity) (by linarith)
      _ = D⁻¹ / T := by ring
  have hDlog : D ≤ T * Real.log T := by
    calc
      D ≤ T := hDT
      _ ≤ T * Real.log T := by nlinarith
  have hsecond : D⁻¹ / T ≤ (D ^ 2)⁻¹ * Real.log T := by
    field_simp [hDpos.ne', hTpos.ne']
    nlinarith
  unfold remoteTailCubicWindowBound
  calc
    (2 * (D ^ 3)⁻¹ + (D ^ 2)⁻¹ / 2) * Real.log (2 * T + 4) +
          (2 * (D ^ 2)⁻¹ + D⁻¹) / (2 * T + 4) ≤
        4 * (D ^ 2)⁻¹ * Real.log T +
          (D ^ 2)⁻¹ * Real.log T :=
      add_le_add hfirst (hquot.trans hsecond)
    _ = 5 * (D ^ 2)⁻¹ * Real.log T := by ring

theorem remote_tail_cubic_sum_le
    {ι : Type*} {gamma : ι → ℝ} {mult : ι → ℕ} {A0 T D : ℝ}
    (hcount : Tail.LocalCount gamma mult A0) (hT : 0 ≤ T) (hD : 2 ≤ D)
    (s : Finset ι)
    (hs : ∀ rho ∈ s,
      gamma rho ≤ T - D ∨ 2 * T + D ≤ gamma rho) :
    ∑ rho ∈ s, (mult rho : ℝ) *
        ((Tail.distI T (gamma rho)) ^ 3)⁻¹ ≤
      2 * A0 * remoteTailCubicWindowBound T D := by
  classical
  have hA0 : 0 ≤ A0 := hcount.A₀_pos.le
  have hDpos : 0 < D := by linarith
  let B : ℝ := 2 * T + 4
  have hB : 1 ≤ B := by dsimp [B]; linarith
  let slo : Finset ι := s.filter fun rho => gamma rho ≤ T - D
  let shi : Finset ι := s.filter fun rho => ¬gamma rho ≤ T - D
  have hhiMem : ∀ rho ∈ shi, 2 * T + D ≤ gamma rho := by
    intro rho hrho
    simp only [shi, Finset.mem_filter] at hrho
    rcases hs rho hrho.1 with hlo | hhi
    · exact absurd hlo hrho.2
    · exact hhi
  have hlogmono : ∀ (t : ℝ) (j : ℕ), |t| + 3 ≤ B + j →
      A0 * Real.log (|t| + 3) ≤ A0 * Real.log (B + j) := by
    intro t j ht
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) ht) hA0
  have hlo :
      ∑ rho ∈ slo, (mult rho : ℝ) *
          ((Tail.distI T (gamma rho)) ^ 3)⁻¹ ≤
        A0 * remoteTailCubicWindowBound T D := by
    have hmem : ∀ rho ∈ slo, gamma rho ≤ T - D := by
      intro rho hrho
      exact (Finset.mem_filter.mp hrho).2
    have heq : ∀ rho ∈ slo,
        (mult rho : ℝ) * ((Tail.distI T (gamma rho)) ^ 3)⁻¹ =
          (mult rho : ℝ) * ((T - gamma rho) ^ 3)⁻¹ := by
      intro rho hrho
      rw [Tail.distI_of_le hT (by linarith [hmem rho hrho])]
    rw [Finset.sum_congr rfl heq]
    unfold remoteTailCubicWindowBound
    apply Tail.one_side_sum_le slo (fun rho => T - gamma rho) mult
      (fun rho => ⌊T - gamma rho⌋₊) hA0 hB hD
    · intro rho hrho
      linarith [hmem rho hrho]
    · intro rho hrho
      exact Nat.floor_le (by linarith [hmem rho hrho])
    · intro rho hrho
      exact (Nat.lt_floor_add_one _).le
    · intro j
      refine (hcount.window (T - j - 1) _ ?_).trans
        (hlogmono (T - j - 1) j ?_)
      · intro rho hrho
        rw [Finset.mem_filter] at hrho
        obtain ⟨hrhos, hrhoj⟩ := hrho
        have hnonneg : 0 ≤ T - gamma rho := by
          linarith [hmem rho hrhos]
        have hj := (Nat.floor_eq_iff hnonneg).mp hrhoj
        constructor <;> linarith [hj.1, hj.2]
      · have habs : |T - j - 1| ≤ T + j + 1 := by
          rw [abs_le]
          constructor <;> nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        dsimp [B]
        linarith
  have hhi :
      ∑ rho ∈ shi, (mult rho : ℝ) *
          ((Tail.distI T (gamma rho)) ^ 3)⁻¹ ≤
        A0 * remoteTailCubicWindowBound T D := by
    have heq : ∀ rho ∈ shi,
        (mult rho : ℝ) * ((Tail.distI T (gamma rho)) ^ 3)⁻¹ =
          (mult rho : ℝ) * ((gamma rho - 2 * T) ^ 3)⁻¹ := by
      intro rho hrho
      rw [Tail.distI_of_ge hT (by linarith [hhiMem rho hrho])]
    rw [Finset.sum_congr rfl heq]
    have hceil1 : ∀ rho ∈ shi, 1 ≤ ⌈gamma rho - 2 * T⌉₊ := by
      intro rho hrho
      exact Nat.one_le_ceil_iff.mpr (by linarith [hhiMem rho hrho])
    have hcast : ∀ rho ∈ shi,
        (((⌈gamma rho - 2 * T⌉₊ - 1 : ℕ) : ℝ)) =
          ⌈gamma rho - 2 * T⌉₊ - 1 := by
      intro rho hrho
      rw [Nat.cast_sub (hceil1 rho hrho)]
      simp
    unfold remoteTailCubicWindowBound
    apply Tail.one_side_sum_le shi (fun rho => gamma rho - 2 * T) mult
      (fun rho => ⌈gamma rho - 2 * T⌉₊ - 1) hA0 hB hD
    · intro rho hrho
      linarith [hhiMem rho hrho]
    · intro rho hrho
      rw [hcast rho hrho]
      have hc := Nat.ceil_lt_add_one
        (show 0 ≤ gamma rho - 2 * T by linarith [hhiMem rho hrho])
      linarith
    · intro rho hrho
      rw [hcast rho hrho]
      have hc := Nat.le_ceil (gamma rho - 2 * T)
      linarith
    · intro j
      refine (hcount.window (2 * T + j) _ ?_).trans
        (hlogmono (2 * T + j) j ?_)
      · intro rho hrho
        rw [Finset.mem_filter] at hrho
        obtain ⟨hrhos, hrhoj⟩ := hrho
        have hc : ⌈gamma rho - 2 * T⌉₊ = j + 1 := by
          have hone := hceil1 rho hrhos
          omega
        have hj := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
        push_cast at hj
        constructor <;> linarith [hj.1, hj.2]
      · rw [abs_of_nonneg (by positivity)]
        dsimp [B]
        linarith
  rw [← Finset.sum_filter_add_sum_filter_not s
    (fun rho => gamma rho ≤ T - D)]
  simpa only [slo, shi] using
    (add_le_add hlo hhi).trans_eq (by ring)

theorem remote_tail_fourth_sum_le
    {ι : Type*} {gamma : ι → ℝ} {mult : ι → ℕ} {A0 T D : ℝ}
    (hcount : Tail.LocalCount gamma mult A0) (hT : 0 ≤ T) (hD : 2 ≤ D)
    (s : Finset ι)
    (hs : ∀ rho ∈ s,
      gamma rho ≤ T - D ∨ 2 * T + D ≤ gamma rho) :
    ∑ rho ∈ s, (mult rho : ℝ) *
        ((Tail.distI T (gamma rho)) ^ 4)⁻¹ ≤
      2 * A0 * D⁻¹ * remoteTailCubicWindowBound T D := by
  have hDpos : 0 < D := by linarith
  have hdist : ∀ rho ∈ s, D ≤ Tail.distI T (gamma rho) := by
    intro rho hrho
    rcases hs rho hrho with hlo | hhi
    · rw [Tail.distI_of_le hT (by linarith)]
      linarith
    · rw [Tail.distI_of_ge hT (by linarith)]
      linarith
  calc
    ∑ rho ∈ s, (mult rho : ℝ) *
          ((Tail.distI T (gamma rho)) ^ 4)⁻¹ ≤
        ∑ rho ∈ s, (mult rho : ℝ) *
          (D⁻¹ * ((Tail.distI T (gamma rho)) ^ 3)⁻¹) := by
      apply Finset.sum_le_sum
      intro rho hrho
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [← mul_inv]
      apply inv_anti₀
      · exact mul_pos hDpos
          (pow_pos (lt_of_lt_of_le hDpos (hdist rho hrho)) 3)
      · calc
          D * Tail.distI T (gamma rho) ^ 3 ≤
              Tail.distI T (gamma rho) * Tail.distI T (gamma rho) ^ 3 :=
            mul_le_mul_of_nonneg_right (hdist rho hrho)
              (pow_nonneg (Tail.distI_nonneg _ _) 3)
          _ = Tail.distI T (gamma rho) ^ 4 := by ring
    _ = D⁻¹ * (∑ rho ∈ s, (mult rho : ℝ) *
          ((Tail.distI T (gamma rho)) ^ 3)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      ring
    _ ≤ D⁻¹ * (2 * A0 * remoteTailCubicWindowBound T D) := by
      exact mul_le_mul_of_nonneg_left
        (remote_tail_cubic_sum_le hcount hT hD s hs)
        (inv_nonneg.mpr hDpos.le)
    _ = 2 * A0 * D⁻¹ * remoteTailCubicWindowBound T D := by ring

theorem distI_one_div_eq_distI_div
    {T gamma : ℝ} (hT : 0 < T)
    (hout : gamma ≤ T ∨ 2 * T ≤ gamma) :
    Tail.distI 1 (gamma / T) = Tail.distI T gamma / T := by
  rcases hout with hlo | hhi
  · have hlo' : gamma / T ≤ 1 := (div_le_one hT).2 hlo
    rw [Tail.distI_of_le (by norm_num) hlo', Tail.distI_of_le hT.le hlo]
    field_simp [hT.ne']
  · have hhi' : 2 * (1 : ℝ) ≤ gamma / T := by
      rw [le_div_iff₀ hT]
      nlinarith
    rw [Tail.distI_of_ge (by norm_num) hhi', Tail.distI_of_ge hT.le hhi]
    field_simp [hT.ne']

theorem norm_paperFT_windowAveraged_le_dist_four
    {Z : ZeroConfig} {R w T D : ℝ}
    (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hT : 0 < T) (hRT : R ≤ 2 * T) (hD : 0 < D)
    (rho : Z.carrier)
    (hout : (rho : ℂ).im ≤ T - D ∨
      2 * T + D ≤ (rho : ℂ).im) :
    ‖paperFT (windowAveragedHeightTest R w)
        (gammaOf (rho : ℂ) / T)‖ ≤
      (T ^ 4 / (baseHeightKernelMass * R ^ 3)) *
        baseHeightRemoteDecayConstant *
          ((Tail.distI T (rho : ℂ).im) ^ 4)⁻¹ := by
  have houter : (rho : ℂ).im ≤ T ∨ 2 * T ≤ (rho : ℂ).im := by
    rcases hout with hlo | hhi
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hdist : D ≤ Tail.distI T (rho : ℂ).im := by
    rcases hout with hlo | hhi
    · rw [Tail.distI_of_le hT.le (by linarith)]
      linarith
    · rw [Tail.distI_of_ge hT.le (by linarith)]
      linarith
  have hd1 : Tail.distI 1 ((rho : ℂ).im / T) =
      Tail.distI T (rho : ℂ).im / T :=
    distI_one_div_eq_distI_div hT houter
  have hscale : 0 < R * Tail.distI 1 ((rho : ℂ).im / T) := by
    rw [hd1]
    exact mul_pos hR (div_pos (lt_of_lt_of_le hD hdist) hT)
  have hpacket := norm_paperFT_windowAveraged_mul_dist_four_le
    hR hw hw1 hT hRT rho
  calc
    ‖paperFT (windowAveragedHeightTest R w)
          (gammaOf (rho : ℂ) / T)‖ ≤
        ((R / baseHeightKernelMass) * baseHeightRemoteDecayConstant) /
          (R * Tail.distI 1 ((rho : ℂ).im / T)) ^ 4 :=
      (le_div_iff₀ (pow_pos hscale 4)).2 hpacket
    _ = (T ^ 4 / (baseHeightKernelMass * R ^ 3)) *
          baseHeightRemoteDecayConstant *
            ((Tail.distI T (rho : ℂ).im) ^ 4)⁻¹ := by
      rw [hd1]
      field_simp [hR.ne', hT.ne', baseHeightKernelMass_pos.ne',
        (lt_of_lt_of_le hD hdist).ne']

theorem remote_height_sum_le_of_local_count
    {Z : ZeroConfig} {A0 R w T D : ℝ}
    (hcount : Tail.LocalCount
      (fun rho : Z.carrier => (rho : ℂ).im)
        (fun rho : Z.carrier => Z.mult (rho : ℂ)) A0)
    (hR : 0 < R) (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hT : 0 < T) (hRT : R ≤ 2 * T) (hD : 2 ≤ D)
    (s : Finset Z.carrier)
    (hs : ∀ rho ∈ s,
      (rho : ℂ).im ≤ T - D ∨ 2 * T + D ≤ (rho : ℂ).im) :
    ∑ rho ∈ s, (Z.mult rho : ℝ) *
        ‖paperFT (windowAveragedHeightTest R w)
          (gammaOf (rho : ℂ) / T)‖ ≤
      (T ^ 4 / (baseHeightKernelMass * R ^ 3)) *
        baseHeightRemoteDecayConstant *
          (2 * A0 * D⁻¹ * remoteTailCubicWindowBound T D) := by
  have hK0 : 0 ≤
      (T ^ 4 / (baseHeightKernelMass * R ^ 3)) *
        baseHeightRemoteDecayConstant := by
    exact mul_nonneg
      (div_nonneg (pow_nonneg hT.le 4)
        (mul_nonneg baseHeightKernelMass_pos.le (pow_nonneg hR.le 3)))
      baseHeightRemoteDecayConstant_nonneg
  calc
    ∑ rho ∈ s, (Z.mult rho : ℝ) *
          ‖paperFT (windowAveragedHeightTest R w)
            (gammaOf (rho : ℂ) / T)‖ ≤
        ∑ rho ∈ s, (Z.mult rho : ℝ) *
          ((T ^ 4 / (baseHeightKernelMass * R ^ 3)) *
            baseHeightRemoteDecayConstant *
              ((Tail.distI T (rho : ℂ).im) ^ 4)⁻¹) := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact mul_le_mul_of_nonneg_left
        (norm_paperFT_windowAveraged_le_dist_four
          hR hw hw1 hT hRT (by linarith) rho (hs rho hrho))
        (Nat.cast_nonneg _)
    _ = ((T ^ 4 / (baseHeightKernelMass * R ^ 3)) *
          baseHeightRemoteDecayConstant) *
        (∑ rho ∈ s, (Z.mult rho : ℝ) *
          ((Tail.distI T (rho : ℂ).im) ^ 4)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      ring
    _ ≤ ((T ^ 4 / (baseHeightKernelMass * R ^ 3)) *
          baseHeightRemoteDecayConstant) *
        (2 * A0 * D⁻¹ * remoteTailCubicWindowBound T D) := by
      exact mul_le_mul_of_nonneg_left
        (remote_tail_fourth_sum_le hcount hT.le hD s hs) hK0
    _ = (T ^ 4 / (baseHeightKernelMass * R ^ 3)) *
          baseHeightRemoteDecayConstant *
            (2 * A0 * D⁻¹ * remoteTailCubicWindowBound T D) := by ring

theorem dyadic_remote_height_sum_normalized_le_of_local_count
    {Z : ZeroConfig} {A0 w T : ℝ} (q : ℕ) (hq : 1 ≤ q)
    (hcount : Tail.LocalCount
      (fun rho : Z.carrier => (rho : ℂ).im)
        (fun rho : Z.carrier => Z.mult (rho : ℂ)) A0)
    (hw : 0 < w) (hw1 : 2 * w ≤ 1)
    (hTpower : ((q : ℝ) + 1) ^ 4 ≤ T)
    (s : Finset Z.carrier)
    (hs : ∀ rho ∈ s,
      (rho : ℂ).im / T ≤ 1 - dyadicRemoteHeightGap q ∨
        2 + dyadicRemoteHeightGap q ≤ (rho : ℂ).im / T) :
    (∑ rho ∈ s, (Z.mult rho : ℝ) *
        ‖paperFT (windowAveragedHeightTest ((q : ℝ) + 1) w)
          (gammaOf (rho : ℂ) / T)‖) /
          (T * Real.log T) ≤
      (10 * A0 *
        (baseHeightRemoteDecayConstant / baseHeightKernelMass)) *
          (((q : ℝ) + 1) * Real.sqrt ((q : ℝ) + 1))⁻¹ := by
  let X : ℝ := (q : ℝ) + 1
  let D : ℝ := T / Real.sqrt X
  have hX2 : 2 ≤ X := by
    dsimp only [X]
    exact_mod_cast Nat.add_le_add_right hq 1
  have hX : 0 < X := by linarith
  have hXpow : X ≤ X ^ 4 := by
    nlinarith [sq_nonneg (X - 1),
      mul_nonneg (sq_nonneg X) (sq_nonneg (X - 1))]
  have hX4six : 6 ≤ X ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hX2 4
    norm_num at hp ⊢
    linarith
  have hTpos : 0 < T := lt_of_lt_of_le (pow_pos hX 4) hTpower
  have hT6 : 6 ≤ T := hX4six.trans hTpower
  have hRT : X ≤ 2 * T := by linarith [hXpow.trans hTpower]
  have hsqrtpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hsqrt1 : 1 ≤ Real.sqrt X := by
    rw [Real.le_sqrt (by norm_num) hX.le]
    nlinarith
  have hsqrtle : Real.sqrt X ≤ X := by
    nlinarith [Real.sq_sqrt hX.le, Real.sqrt_nonneg X]
  have hX3 : (8 : ℝ) ≤ X ^ 3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hX2 3
    norm_num at hp ⊢
    exact hp
  have h2X : 2 * X ≤ X ^ 4 := by
    have hm := mul_le_mul_of_nonneg_left hX3 hX.le
    nlinarith
  have hD2 : 2 ≤ D := by
    dsimp only [D]
    rw [le_div_iff₀ hsqrtpos]
    exact (by nlinarith [hsqrtle, h2X, hTpower] :
      2 * Real.sqrt X ≤ T)
  have hDT : D ≤ T := by
    dsimp only [D]
    rw [div_le_iff₀ hsqrtpos]
    nlinarith
  have hactual : ∀ rho ∈ s,
      (rho : ℂ).im ≤ T - D ∨ 2 * T + D ≤ (rho : ℂ).im := by
    intro rho hrho
    rcases hs rho hrho with hlo | hhi
    · left
      have hm := (div_le_iff₀ hTpos).mp hlo
      unfold dyadicRemoteHeightGap at hm
      dsimp only [X, D] at hm ⊢
      field_simp [hsqrtpos.ne'] at hm ⊢
      nlinarith
    · right
      have hm := (le_div_iff₀ hTpos).mp hhi
      unfold dyadicRemoteHeightGap at hm
      dsimp only [X, D] at hm ⊢
      field_simp [hsqrtpos.ne'] at hm ⊢
      nlinarith
  have hW := remoteTailCubicWindowBound_le hT6 hD2 hDT
  have hA0 : 0 ≤ A0 := hcount.A₀_pos.le
  have htail :
      2 * A0 * D⁻¹ * remoteTailCubicWindowBound T D ≤
        10 * A0 * (D ^ 3)⁻¹ * Real.log T := by
    calc
      2 * A0 * D⁻¹ * remoteTailCubicWindowBound T D ≤
          2 * A0 * D⁻¹ * (5 * (D ^ 2)⁻¹ * Real.log T) := by
        exact mul_le_mul_of_nonneg_left hW
          (mul_nonneg (mul_nonneg (by positivity) hA0)
            (inv_nonneg.mpr (by linarith)))
      _ = 10 * A0 * (D ^ 3)⁻¹ * Real.log T := by
        field_simp [(by linarith : D ≠ 0)]
        ring
  have hK0 : 0 ≤
      (T ^ 4 / (baseHeightKernelMass * X ^ 3)) *
        baseHeightRemoteDecayConstant := by
    exact mul_nonneg
      (div_nonneg (pow_nonneg hTpos.le 4)
        (mul_nonneg baseHeightKernelMass_pos.le (pow_nonneg hX.le 3)))
      baseHeightRemoteDecayConstant_nonneg
  have hraw := remote_height_sum_le_of_local_count
    hcount hX hw hw1 hTpos hRT hD2 s hactual
  have hsum :
      ∑ rho ∈ s, (Z.mult rho : ℝ) *
          ‖paperFT (windowAveragedHeightTest X w)
            (gammaOf (rho : ℂ) / T)‖ ≤
        ((T ^ 4 / (baseHeightKernelMass * X ^ 3)) *
          baseHeightRemoteDecayConstant) *
            (10 * A0 * (D ^ 3)⁻¹ * Real.log T) := by
    exact hraw.trans (mul_le_mul_of_nonneg_left htail hK0)
  have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
  rw [div_le_iff₀ (mul_pos hTpos hlogTpos)]
  dsimp only [X] at hsum ⊢
  calc
    ∑ rho ∈ s, (Z.mult rho : ℝ) *
          ‖paperFT (windowAveragedHeightTest ((q : ℝ) + 1) w)
            (gammaOf (rho : ℂ) / T)‖ ≤
        ((T ^ 4 /
            (baseHeightKernelMass * ((q : ℝ) + 1) ^ 3)) *
          baseHeightRemoteDecayConstant) *
            (10 * A0 * (D ^ 3)⁻¹ * Real.log T) := hsum
    _ = ((10 * A0 *
          (baseHeightRemoteDecayConstant / baseHeightKernelMass)) *
            (((q : ℝ) + 1) * Real.sqrt ((q : ℝ) + 1))⁻¹) *
          (T * Real.log T) := by
      dsimp only [D, X]
      have hsquare : Real.sqrt ((q : ℝ) + 1) ^ 2 = (q : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      field_simp [hTpos.ne', baseHeightKernelMass_pos.ne',
        (by positivity : (q : ℝ) + 1 ≠ 0),
        (by positivity : Real.sqrt ((q : ℝ) + 1) ≠ 0)]
      nlinarith

theorem rvm_dyadic_far_height_sum_tendsto_zero
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z)
    (T : ℕ → ℝ) (hTpower : ∀ q, ((q : ℝ) + 1) ^ 4 ≤ T q)
    (w : ℕ → ℝ) (hw : ∀ q, 0 < w q) (hw1 : ∀ q, 2 * w q ≤ 1)
    (s : ℕ → Finset Z.carrier)
    (hs : ∀ q rho, rho ∈ s q →
      (rho : ℂ).im / T q ≤ 1 - dyadicRemoteHeightGap q ∨
        2 + dyadicRemoteHeightGap q ≤ (rho : ℂ).im / T q) :
    Tendsto
      (fun q : ℕ =>
        (∑ rho ∈ s q, (Z.mult rho : ℝ) *
          ‖paperFT (windowAveragedHeightTest ((q : ℝ) + 1) (w q))
            (gammaOf (rho : ℂ) / T q)‖) /
          (T q * Real.log (T q)))
      atTop (nhds 0) := by
  obtain ⟨A0, hA0, hlocal⟩ := hRvM.local_count
  have hcount := Tail.LocalCount.ofWindowCount Z hA0 hlocal
  let C : ℝ := 10 * A0 *
    (baseHeightRemoteDecayConstant / baseHeightKernelMass)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hbase : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun q : ℕ => (((q : ℝ) + 1))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hbase
  have hupper : Tendsto (fun q : ℕ => C * (((q : ℝ) + 1))⁻¹)
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (show Tendsto (fun _ : ℕ => C) atTop (nhds C) from
        tendsto_const_nhds).mul hinv
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 1] with q hq
    let X : ℝ := (q : ℝ) + 1
    have hX2 : 2 ≤ X := by
      dsimp only [X]
      exact_mod_cast Nat.add_le_add_right hq 1
    have hX : 0 < X := by linarith
    have hTpos : 0 < T q :=
      lt_of_lt_of_le (pow_pos hX 4) (by simpa only [X] using hTpower q)
    have hlog : 0 < Real.log (T q) := by
      apply Real.log_pos
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hX2 4
      norm_num at hp ⊢
      linarith [hp, hTpower q]
    exact div_nonneg
      (Finset.sum_nonneg fun _ _ =>
        mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      (mul_nonneg hTpos.le hlog.le)
  · filter_upwards [eventually_ge_atTop 1] with q hq
    have hraw := dyadic_remote_height_sum_normalized_le_of_local_count
      q hq hcount (hw q) (hw1 q) (hTpower q) (s q) (hs q)
    let X : ℝ := (q : ℝ) + 1
    have hX2 : 2 ≤ X := by
      dsimp only [X]
      exact_mod_cast Nat.add_le_add_right hq 1
    have hX : 0 < X := by linarith
    have hsqrt1 : 1 ≤ Real.sqrt X := by
      rw [Real.le_sqrt (by norm_num) hX.le]
      nlinarith
    have hden : X ≤ X * Real.sqrt X := by nlinarith
    have hinvle : (X * Real.sqrt X)⁻¹ ≤ X⁻¹ :=
      inv_anti₀ hX hden
    have hbound : C * (X * Real.sqrt X)⁻¹ ≤ C * X⁻¹ :=
      mul_le_mul_of_nonneg_left hinvle hC0
    exact hraw.trans (by simpa only [C, X] using hbound)

end RH.Zeta85.RSPoissonCyclicBridge
