import RH.Zeta85.Discharge.RSHeightRemoteSum
import RH.Zeta85.Discharge.RSCyclicFourierBridge

/-!
# Lifting one remote vertex through a cyclic kernel

The remote height estimate must be summed before the remaining zero
coordinates.  A weighted row bound for the cyclic Fourier kernel does this
without replacing the other coordinates by independent zero counts.
-/

open Filter Topology Finset Real
open scoped BigOperators

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def cyclicFourWeight {ι : Type*}
    (a : ι → ℝ) (b : ι → ι → ℝ) (i j k l : ι) : ℝ :=
  a i * b i j * (a j * b j k * (a k * b k l * (a l * b l i)))

def anchoredCyclicFourSum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (remote : ι → Prop) [DecidablePred remote]
    (a : ι → ℝ) (b : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s.filter remote, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
    cyclicFourWeight a b i j k l

def remoteCyclicFourSum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (remote : ι → Prop) [DecidablePred remote]
    (a : ι → ℝ) (b : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
    if remote i ∨ remote j ∨ remote k ∨ remote l then
      cyclicFourWeight a b i j k l else 0

theorem anchoredCyclicFourSum_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (remote : ι → Prop) [DecidablePred remote]
    (a : ι → ℝ) (b : ι → ι → ℝ) {B C : ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ b i j)
    (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hentry : ∀ i ∈ s, ∀ j ∈ s, b i j ≤ B)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, a j * b i j ≤ C) :
    anchoredCyclicFourSum s remote a b ≤
      B * C ^ 3 * ∑ i ∈ s.filter remote, a i := by
  have hlast : ∀ k ∈ s, ∀ i ∈ s,
      (∑ l ∈ s, a l * b k l * b l i) ≤ B * C := by
    intro k hk i hi
    calc
      (∑ l ∈ s, a l * b k l * b l i) ≤
          ∑ l ∈ s, a l * b k l * B := by
        apply Finset.sum_le_sum
        intro l hl
        exact mul_le_mul_of_nonneg_left (hentry l hl i hi)
          (mul_nonneg (ha l hl) (hb k hk l hl))
      _ = B * (∑ l ∈ s, a l * b k l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ ≤ B * C := mul_le_mul_of_nonneg_left (hrow k hk) hB0
  have htwo : ∀ j ∈ s, ∀ i ∈ s,
      (∑ k ∈ s, a k * b j k *
        (∑ l ∈ s, a l * b k l * b l i)) ≤ B * C ^ 2 := by
    intro j hj i hi
    calc
      (∑ k ∈ s, a k * b j k *
          (∑ l ∈ s, a l * b k l * b l i)) ≤
          ∑ k ∈ s, a k * b j k * (B * C) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (hlast k hk i hi)
          (mul_nonneg (ha k hk) (hb j hj k hk))
      _ = (B * C) * (∑ k ∈ s, a k * b j k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ (B * C) * C :=
        mul_le_mul_of_nonneg_left (hrow j hj) (mul_nonneg hB0 hC0)
      _ = B * C ^ 2 := by ring
  have hthree : ∀ i ∈ s,
      (∑ j ∈ s, a j * b i j *
        (∑ k ∈ s, a k * b j k *
          (∑ l ∈ s, a l * b k l * b l i))) ≤ B * C ^ 3 := by
    intro i hi
    calc
      (∑ j ∈ s, a j * b i j *
          (∑ k ∈ s, a k * b j k *
            (∑ l ∈ s, a l * b k l * b l i))) ≤
          ∑ j ∈ s, a j * b i j * (B * C ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (htwo j hj i hi)
          (mul_nonneg (ha j hj) (hb i hi j hj))
      _ = (B * C ^ 2) * (∑ j ∈ s, a j * b i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ (B * C ^ 2) * C :=
        mul_le_mul_of_nonneg_left (hrow i hi)
          (mul_nonneg hB0 (pow_nonneg hC0 2))
      _ = B * C ^ 3 := by ring
  unfold anchoredCyclicFourSum
  unfold cyclicFourWeight
  calc
    (∑ i ∈ s.filter remote, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
        a i * b i j *
          (a j * b j k * (a k * b k l * (a l * b l i)))) ≤
        ∑ i ∈ s.filter remote, a i * (B * C ^ 3) := by
      apply Finset.sum_le_sum
      intro i hi
      have his : i ∈ s := (Finset.mem_filter.mp hi).1
      calc
        (∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
            a i * b i j *
              (a j * b j k * (a k * b k l * (a l * b l i)))) =
            a i * (∑ j ∈ s, a j * b i j *
              (∑ k ∈ s, a k * b j k *
                (∑ l ∈ s, a l * b k l * b l i))) := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          ring
        _ ≤ a i * (B * C ^ 3) :=
          mul_le_mul_of_nonneg_left (hthree i his) (ha i his)
    _ = B * C ^ 3 * ∑ i ∈ s.filter remote, a i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem remoteCyclicFourSum_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (remote : ι → Prop) [DecidablePred remote]
    (a : ι → ℝ) (b : ι → ι → ℝ) {B C : ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ b i j)
    (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hentry : ∀ i ∈ s, ∀ j ∈ s, b i j ≤ B)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, a j * b i j ≤ C) :
    remoteCyclicFourSum s remote a b ≤
      4 * B * C ^ 3 * ∑ i ∈ s.filter remote, a i := by
  classical
  let S0 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
    if remote i then cyclicFourWeight a b i j k l else 0
  let S1 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
    if remote j then cyclicFourWeight a b i j k l else 0
  let S2 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
    if remote k then cyclicFourWeight a b i j k l else 0
  let S3 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
    if remote l then cyclicFourWeight a b i j k l else 0
  have hweight0 : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, ∀ l ∈ s,
      0 ≤ cyclicFourWeight a b i j k l := by
    intro i hi j hj k hk l hl
    have hai := ha i hi
    have haj := ha j hj
    have hak := ha k hk
    have hal := ha l hl
    have hij := hb i hi j hj
    have hjk := hb j hj k hk
    have hkl := hb k hk l hl
    have hli := hb l hl i hi
    unfold cyclicFourWeight
    positivity
  have hunion : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, ∀ l ∈ s,
      (if remote i ∨ remote j ∨ remote k ∨ remote l then
          cyclicFourWeight a b i j k l else 0) ≤
        (if remote i then cyclicFourWeight a b i j k l else 0) +
        (if remote j then cyclicFourWeight a b i j k l else 0) +
        (if remote k then cyclicFourWeight a b i j k l else 0) +
        (if remote l then cyclicFourWeight a b i j k l else 0) := by
    intro i hi j hj k hk l hl
    have ht := hweight0 i hi j hj k hk l hl
    by_cases h0 : remote i <;> by_cases h1 : remote j <;>
      by_cases h2 : remote k <;> by_cases h3 : remote l <;>
      simp [h0, h1, h2, h3] <;> nlinarith
  have hrot (i j k l : ι) :
      cyclicFourWeight a b i j k l = cyclicFourWeight a b j k l i := by
    unfold cyclicFourWeight
    ring
  have hS0 : S0 = anchoredCyclicFourSum s remote a b := by
    dsimp only [S0]
    unfold anchoredCyclicFourSum
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hir : remote i
    · simp [hir]
    · simp [hir]
  have hS1 : S1 = S0 := by
    dsimp only [S1, S0]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrot]
  have hS2 : S2 = S1 := by
    dsimp only [S2, S1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrot]
  have hS3 : S3 = S2 := by
    dsimp only [S3, S2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrot]
  have hanch := anchoredCyclicFourSum_le
    s remote a b ha hb hB0 hC0 hentry hrow
  unfold remoteCyclicFourSum
  calc
    (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
        if remote i ∨ remote j ∨ remote k ∨ remote l then
          cyclicFourWeight a b i j k l else 0) ≤
        ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
          ((if remote i then cyclicFourWeight a b i j k l else 0) +
          (if remote j then cyclicFourWeight a b i j k l else 0) +
          (if remote k then cyclicFourWeight a b i j k l else 0) +
          (if remote l then cyclicFourWeight a b i j k l else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact hunion i hi j hj k hk l hl
    _ = S0 + S1 + S2 + S3 := by
      dsimp only [S0, S1, S2, S3]
      simp_rw [Finset.sum_add_distrib]
    _ = 4 * anchoredCyclicFourSum s remote a b := by
      rw [hS3, hS2, hS1, hS0]
      ring
    _ ≤ 4 * (B * C ^ 3 * ∑ i ∈ s.filter remote, a i) :=
      mul_le_mul_of_nonneg_left hanch (by norm_num)
    _ = 4 * B * C ^ 3 * ∑ i ∈ s.filter remote, a i := by ring

def rsCyclicFourKernel (mu T : ℝ) (r : ℝ → ℝ)
    (rho rho' : ℂ) : ℝ :=
  ‖paperFT (fun y => (r y : ℂ))
    (((mu * Real.log T : ℝ) : ℂ) * (gammaOf rho' - gammaOf rho))‖

theorem cyclicFrequencyFour_logScaled
    (mu T : ℝ) (rho0 rho1 rho2 rho3 : ℂ) :
    RSReduction.cyclicFrequencyFour mu
      ![((Real.log T / (2 * Real.pi) : ℝ) : ℂ) * gammaOf rho0,
        ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) * gammaOf rho1,
        ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) * gammaOf rho2,
        ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) * gammaOf rho3] =
      ![(((mu * Real.log T : ℝ) : ℂ) * (gammaOf rho0 - gammaOf rho3)),
        (((mu * Real.log T : ℝ) : ℂ) * (gammaOf rho1 - gammaOf rho0)),
        (((mu * Real.log T : ℝ) : ℂ) * (gammaOf rho2 - gammaOf rho1)),
        (((mu * Real.log T : ℝ) : ℂ) * (gammaOf rho3 - gammaOf rho2))] := by
  funext i
  fin_cases i <;>
    simp [RSReduction.cyclicFrequencyFour] <;>
    field_simp [Real.pi_ne_zero] <;> ring

def rsHeightVertexWeight (Z : ZeroConfig) (R w T : ℝ)
    (rho : Z.carrier) : ℝ :=
  (Z.mult rho : ℝ) *
    ‖paperFT (windowAveragedHeightTest R w) (gammaOf (rho : ℂ) / T)‖

theorem norm_rsZeroTupleTerm_cyclic_four_eq
    {Z : ZeroConfig} {mu R w T : ℝ} (r : ℝ → ℝ)
    (hmu : 0 < mu) (hrcont : Continuous r)
    (hrcompact : HasCompactSupport r)
    (rho0 rho1 rho2 rho3 : Z.carrier) :
    ‖rsZeroTupleTerm Z
        (windowAveragedHeightFamily (n := 3) R w)
        (RSReduction.weightedCyclicSymbol (k := 4) mu r) T
        ![rho0, rho1, rho2, rho3]‖ =
        mu ^ 4 * cyclicFourWeight
          (rsHeightVertexWeight Z R w T)
          (fun rho rho' : Z.carrier =>
            rsCyclicFourKernel mu T r (rho : ℂ) (rho' : ℂ))
          rho0 rho1 rho2 rho3 := by
  let x : Fin 4 → ℂ := fun j =>
    ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) *
      gammaOf ((![rho0, rho1, rho2, rho3] : Fin 4 → Z.carrier) j : ℂ)
  have hx : x =
      ![((Real.log T / (2 * Real.pi) : ℝ) : ℂ) * gammaOf (rho0 : ℂ),
        ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) * gammaOf (rho1 : ℂ),
        ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) * gammaOf (rho2 : ℂ),
        ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) * gammaOf (rho3 : ℂ)] := by
    funext j
    fin_cases j <;> rfl
  have hxarg :
      (fun j : Fin 4 =>
        (Real.log T / (2 * Real.pi) : ℂ) *
          gammaOf ((![rho0, rho1, rho2, rho3] : Fin 4 → Z.carrier) j : ℂ)) = x := by
    funext j
    dsimp [x]
    push_cast
    rfl
  have hrs := RSReduction.rsGaugeTest_weightedCyclicSymbol_four
    hmu r hrcont hrcompact x
  rw [hx, cyclicFrequencyFour_logScaled] at hrs
  rw [← hx] at hrs
  unfold rsZeroTupleTerm
  simp only [windowAveragedHeightFamily]
  rw [hxarg]
  rw [hrs]
  simp only [norm_mul, norm_pow, norm_prod, Fin.prod_univ_four]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmu,
    Complex.norm_natCast]
  rw [Fin.prod_univ_four]
  unfold rsHeightVertexWeight rsCyclicFourKernel cyclicFourWeight
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  ring_nf

def remoteRSCyclicFourNormSum
    (Z : ZeroConfig) (s : Finset Z.carrier)
    (remote : Z.carrier → Prop) [DecidablePred remote]
    (mu R w T : ℝ) (r : ℝ → ℝ) : ℝ :=
  ∑ rho0 ∈ s, ∑ rho1 ∈ s, ∑ rho2 ∈ s, ∑ rho3 ∈ s,
    if remote rho0 ∨ remote rho1 ∨ remote rho2 ∨ remote rho3 then
      ‖rsZeroTupleTerm Z
        (windowAveragedHeightFamily (n := 3) R w)
        (RSReduction.weightedCyclicSymbol (k := 4) mu r) T
        ![rho0, rho1, rho2, rho3]‖
    else 0

theorem remoteRSCyclicFourNormSum_eq
    {Z : ZeroConfig} (s : Finset Z.carrier)
    (remote : Z.carrier → Prop) [DecidablePred remote]
    {mu R w T : ℝ} (r : ℝ → ℝ)
    (hmu : 0 < mu) (hrcont : Continuous r)
    (hrcompact : HasCompactSupport r) :
    remoteRSCyclicFourNormSum Z s remote mu R w T r =
      mu ^ 4 * remoteCyclicFourSum s remote
        (rsHeightVertexWeight Z R w T)
        (fun rho rho' : Z.carrier =>
          rsCyclicFourKernel mu T r (rho : ℂ) (rho' : ℂ)) := by
  unfold remoteRSCyclicFourNormSum remoteCyclicFourSum
  simp_rw [norm_rsZeroTupleTerm_cyclic_four_eq r hmu hrcont hrcompact]
  calc
    (∑ rho0 ∈ s, ∑ rho1 ∈ s, ∑ rho2 ∈ s, ∑ rho3 ∈ s,
        if remote rho0 ∨ remote rho1 ∨ remote rho2 ∨ remote rho3 then
          mu ^ 4 * cyclicFourWeight
            (rsHeightVertexWeight Z R w T)
            (fun rho rho' : Z.carrier =>
              rsCyclicFourKernel mu T r (rho : ℂ) (rho' : ℂ))
            rho0 rho1 rho2 rho3
        else 0) =
        ∑ rho0 ∈ s, ∑ rho1 ∈ s, ∑ rho2 ∈ s, ∑ rho3 ∈ s,
          mu ^ 4 *
            (if remote rho0 ∨ remote rho1 ∨ remote rho2 ∨ remote rho3 then
              cyclicFourWeight
                (rsHeightVertexWeight Z R w T)
                (fun rho rho' : Z.carrier =>
                  rsCyclicFourKernel mu T r (rho : ℂ) (rho' : ℂ))
                rho0 rho1 rho2 rho3
            else 0) := by
      apply Finset.sum_congr rfl
      intro rho0 hrho0
      apply Finset.sum_congr rfl
      intro rho1 hrho1
      apply Finset.sum_congr rfl
      intro rho2 hrho2
      apply Finset.sum_congr rfl
      intro rho3 hrho3
      by_cases hremote :
          remote rho0 ∨ remote rho1 ∨ remote rho2 ∨ remote rho3
      · simp [hremote]
      · simp [hremote]
    _ = mu ^ 4 *
        (∑ rho0 ∈ s, ∑ rho1 ∈ s, ∑ rho2 ∈ s, ∑ rho3 ∈ s,
          if remote rho0 ∨ remote rho1 ∨ remote rho2 ∨ remote rho3 then
            cyclicFourWeight
              (rsHeightVertexWeight Z R w T)
              (fun rho rho' : Z.carrier =>
                rsCyclicFourKernel mu T r (rho : ℂ) (rho' : ℂ))
              rho0 rho1 rho2 rho3
          else 0) := by
      simp_rw [← Finset.mul_sum]

theorem remoteRSCyclicFourNormSum_le
    {Z : ZeroConfig} (s : Finset Z.carrier)
    (remote : Z.carrier → Prop) [DecidablePred remote]
    {mu R w T B C : ℝ} (r : ℝ → ℝ)
    (hmu : 0 < mu) (hrcont : Continuous r)
    (hrcompact : HasCompactSupport r)
    (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hentry : ∀ rho ∈ s, ∀ rho' ∈ s,
      rsCyclicFourKernel mu T r (rho : ℂ) (rho' : ℂ) ≤ B)
    (hrow : ∀ rho ∈ s,
      ∑ rho' ∈ s, rsHeightVertexWeight Z R w T rho' *
        rsCyclicFourKernel mu T r (rho : ℂ) (rho' : ℂ) ≤ C) :
    remoteRSCyclicFourNormSum Z s remote mu R w T r ≤
      mu ^ 4 *
        (4 * B * C ^ 3 *
          ∑ rho ∈ s.filter remote, rsHeightVertexWeight Z R w T rho) := by
  have hcycle := remoteCyclicFourSum_le s remote
    (rsHeightVertexWeight Z R w T)
    (fun rho rho' : Z.carrier =>
      rsCyclicFourKernel mu T r (rho : ℂ) (rho' : ℂ))
    (B := B) (C := C)
    (by
      intro rho hrho
      unfold rsHeightVertexWeight
      positivity)
    (by
      intro rho hrho rho' hrho'
      exact norm_nonneg _)
    hB0 hC0 hentry hrow
  rw [remoteRSCyclicFourNormSum_eq s remote r hmu hrcont hrcompact]
  exact mul_le_mul_of_nonneg_left hcycle (pow_nonneg hmu.le 4)

end RH.Zeta85.RSPoissonCyclicBridge
