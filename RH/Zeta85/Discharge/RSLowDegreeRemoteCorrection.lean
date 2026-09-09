import RH.Zeta85.Discharge.RSLogFullTraceDegrees

/-!
# Lower-degree completed/guarded trace correction

The quartic completed-to-guarded correction already has a balanced matrix
form and a Frobenius perturbation bound.  This module supplies the exact
analogues in degrees one, two, and three.  No asymptotic input is introduced
here: every statement is finite-dimensional algebra on the canonical zero
matrices.
-/

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

private theorem rtrace_pow_one_eq_cyclic_generic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) :
    RHLinalg.rtrace (B ^ 1) =
      Complex.re (∑ i : ι, B i i) := by
  simp [RHLinalg.rtrace, Matrix.trace]

private theorem rtrace_pow_two_eq_cyclic_generic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) :
    RHLinalg.rtrace (B ^ 2) =
      Complex.re (∑ i : ι, ∑ j : ι, B i j * B j i) := by
  rw [show B ^ 2 = B * B by noncomm_ring]
  simp [RHLinalg.rtrace, Matrix.trace, Matrix.mul_apply]

private theorem rtrace_pow_three_eq_cyclic_generic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) :
    RHLinalg.rtrace (B ^ 3) =
      Complex.re (∑ i : ι, ∑ j : ι, ∑ k : ι,
        B i k * B k j * B j i) := by
  rw [show B ^ 3 = (B * B) * B by noncomm_ring]
  simp [RHLinalg.rtrace, Matrix.trace, Matrix.mul_apply, Finset.sum_mul]

private theorem sum_finsetSubtype_eq_finset
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) :
    (∑ x : ↥s, f (x : α)) = ∑ x ∈ s, f x := by
  exact (Finset.sum_subtype s (fun _ => Iff.rfl) f).symm

private theorem sum_finsetSubtype2_eq_finset2
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → α → M) :
    (∑ x : ↥s, ∑ y : ↥s, f (x : α) (y : α)) =
      ∑ x ∈ s, ∑ y ∈ s, f x y := by
  calc
    (∑ x : ↥s, ∑ y : ↥s, f (x : α) (y : α)) =
        ∑ x : ↥s, ∑ y ∈ s, f (x : α) y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_finsetSubtype_eq_finset s (f (x : α))
    _ = ∑ x ∈ s, ∑ y ∈ s, f x y :=
      sum_finsetSubtype_eq_finset s (fun x => ∑ y ∈ s, f x y)

private theorem sum_finsetSubtype3_eq_finset3
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → α → α → M) :
    (∑ x : ↥s, ∑ y : ↥s, ∑ z : ↥s,
      f (x : α) (y : α) (z : α)) =
      ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, f x y z := by
  calc
    (∑ x : ↥s, ∑ y : ↥s, ∑ z : ↥s,
        f (x : α) (y : α) (z : α)) =
        ∑ x : ↥s, ∑ y ∈ s, ∑ z ∈ s, f (x : α) y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_finsetSubtype2_eq_finset2 s (f (x : α))
    _ = ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, f x y z :=
      sum_finsetSubtype_eq_finset s
        (fun x => ∑ y ∈ s, ∑ z ∈ s, f x y z)

/-! ## Exact completed and guarded trace identities -/

theorem rtrace_fullLatticeZeroMatrix_pow_one_eq_fullTrace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 1) =
      fullLatticeZeroKernelCyclicTrace1 F T := by
  rw [rtrace_pow_one_eq_cyclic_generic]
  unfold fullLatticeZeroKernelCyclicTrace1
  apply congrArg Complex.re
  calc
    (∑ ρ : ↥(ZeroSide.ZI Z T), fullLatticeZeroMatrix F T ρ ρ) =
        ∑ ρ : ↥(ZeroSide.ZI Z T),
          fullLatticeZeroCycle1 F T (ρ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rfl
    _ = ∑ ρ ∈ ZeroSide.ZI Z T,
        fullLatticeZeroCycle1 F T ρ :=
      sum_finsetSubtype_eq_finset (ZeroSide.ZI Z T)
        (fullLatticeZeroCycle1 F T)

theorem rtrace_fullLatticeZeroMatrix_pow_two_eq_fullTrace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 2) =
      fullLatticeZeroKernelCyclicTrace2 F T := by
  rw [rtrace_pow_two_eq_cyclic_generic]
  unfold fullLatticeZeroKernelCyclicTrace2
  apply congrArg Complex.re
  calc
    (∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        fullLatticeZeroMatrix F T ρ₁ ρ₂ *
          fullLatticeZeroMatrix F T ρ₂ ρ₁) =
        ∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
          fullLatticeZeroCycle2 F T (ρ₁ : ℂ) (ρ₂ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ₁ hρ₁
      apply Finset.sum_congr rfl
      intro ρ₂ hρ₂
      unfold fullLatticeZeroMatrix fullLatticeZeroCycle2
      rw [fullLatticePairKernel_comm F T (ρ₂ : ℂ) (ρ₁ : ℂ)]
      ring
    _ = ∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
        fullLatticeZeroCycle2 F T ρ₁ ρ₂ :=
      sum_finsetSubtype2_eq_finset2 (ZeroSide.ZI Z T)
        (fullLatticeZeroCycle2 F T)

theorem rtrace_fullLatticeZeroMatrix_pow_three_eq_fullTrace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 3) =
      fullLatticeZeroKernelCyclicTrace3 F T := by
  rw [rtrace_pow_three_eq_cyclic_generic]
  unfold fullLatticeZeroKernelCyclicTrace3
  apply congrArg Complex.re
  calc
    (∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
      ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
        fullLatticeZeroMatrix F T ρ₁ ρ₃ *
          fullLatticeZeroMatrix F T ρ₃ ρ₂ *
            fullLatticeZeroMatrix F T ρ₂ ρ₁) =
        ∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
          ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
            fullLatticeZeroCycle3 F T
              (ρ₁ : ℂ) (ρ₃ : ℂ) (ρ₂ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ₁ hρ₁
      apply Finset.sum_congr rfl
      intro ρ₂ hρ₂
      apply Finset.sum_congr rfl
      intro ρ₃ hρ₃
      unfold fullLatticeZeroMatrix fullLatticeZeroCycle3
      rw [fullLatticePairKernel_comm F T (ρ₂ : ℂ) (ρ₁ : ℂ)]
      ring
    _ = ∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
          fullLatticeZeroCycle3 F T
            (ρ₁ : ℂ) (ρ₂ : ℂ) (ρ₃ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ₁ hρ₁
      rw [Finset.sum_comm]
    _ = ∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
        ∑ ρ₃ ∈ ZeroSide.ZI Z T,
          fullLatticeZeroCycle3 F T ρ₁ ρ₂ ρ₃ :=
      sum_finsetSubtype3_eq_finset3 (ZeroSide.ZI Z T)
        (fullLatticeZeroCycle3 F T)

theorem rtrace_guardedLatticeZeroMatrix_pow_one_eq_guardedTrace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 1) =
      QuarticTransfer.guardedZeroKernelCyclicTrace1 F T := by
  rw [rtrace_pow_one_eq_cyclic_generic]
  unfold QuarticTransfer.guardedZeroKernelCyclicTrace1
  apply congrArg Complex.re
  calc
    (∑ ρ : ↥(ZeroSide.ZI Z T), guardedLatticeZeroMatrix F T ρ ρ) =
        ∑ ρ : ↥(ZeroSide.ZI Z T),
          QuarticTransfer.guardedZeroCycle1 F T (ρ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rfl
    _ = ∑ ρ ∈ ZeroSide.ZI Z T,
        QuarticTransfer.guardedZeroCycle1 F T ρ :=
      sum_finsetSubtype_eq_finset (ZeroSide.ZI Z T)
        (QuarticTransfer.guardedZeroCycle1 F T)

theorem rtrace_guardedLatticeZeroMatrix_pow_two_eq_guardedTrace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 2) =
      QuarticTransfer.guardedZeroKernelCyclicTrace2 F T := by
  rw [rtrace_pow_two_eq_cyclic_generic]
  unfold QuarticTransfer.guardedZeroKernelCyclicTrace2
  apply congrArg Complex.re
  calc
    (∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        guardedLatticeZeroMatrix F T ρ₁ ρ₂ *
          guardedLatticeZeroMatrix F T ρ₂ ρ₁) =
        ∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
          QuarticTransfer.guardedZeroCycle2 F T
            (ρ₁ : ℂ) (ρ₂ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ₁ hρ₁
      apply Finset.sum_congr rfl
      intro ρ₂ hρ₂
      unfold guardedLatticeZeroMatrix QuarticTransfer.guardedZeroCycle2
      rw [guardedLatticePairKernel_comm F T (ρ₂ : ℂ) (ρ₁ : ℂ)]
      ring
    _ = ∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
        QuarticTransfer.guardedZeroCycle2 F T ρ₁ ρ₂ :=
      sum_finsetSubtype2_eq_finset2 (ZeroSide.ZI Z T)
        (QuarticTransfer.guardedZeroCycle2 F T)

theorem rtrace_guardedLatticeZeroMatrix_pow_three_eq_guardedTrace
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 3) =
      QuarticTransfer.guardedZeroKernelCyclicTrace3 F T := by
  rw [rtrace_pow_three_eq_cyclic_generic]
  unfold QuarticTransfer.guardedZeroKernelCyclicTrace3
  apply congrArg Complex.re
  calc
    (∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
      ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
        guardedLatticeZeroMatrix F T ρ₁ ρ₃ *
          guardedLatticeZeroMatrix F T ρ₃ ρ₂ *
            guardedLatticeZeroMatrix F T ρ₂ ρ₁) =
        ∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
          ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
            QuarticTransfer.guardedZeroCycle3 F T
              (ρ₁ : ℂ) (ρ₃ : ℂ) (ρ₂ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ₁ hρ₁
      apply Finset.sum_congr rfl
      intro ρ₂ hρ₂
      apply Finset.sum_congr rfl
      intro ρ₃ hρ₃
      unfold guardedLatticeZeroMatrix QuarticTransfer.guardedZeroCycle3
      rw [guardedLatticePairKernel_comm F T (ρ₂ : ℂ) (ρ₁ : ℂ)]
      ring
    _ = ∑ ρ₁ : ↥(ZeroSide.ZI Z T), ∑ ρ₂ : ↥(ZeroSide.ZI Z T),
        ∑ ρ₃ : ↥(ZeroSide.ZI Z T),
          QuarticTransfer.guardedZeroCycle3 F T
            (ρ₁ : ℂ) (ρ₂ : ℂ) (ρ₃ : ℂ) := by
      apply Finset.sum_congr rfl
      intro ρ₁ hρ₁
      rw [Finset.sum_comm]
    _ = ∑ ρ₁ ∈ ZeroSide.ZI Z T, ∑ ρ₂ ∈ ZeroSide.ZI Z T,
        ∑ ρ₃ ∈ ZeroSide.ZI Z T,
          QuarticTransfer.guardedZeroCycle3 F T ρ₁ ρ₂ ρ₃ :=
      sum_finsetSubtype3_eq_finset3 (ZeroSide.ZI Z T)
        (QuarticTransfer.guardedZeroCycle3 F T)

/-! ## Exact square-root balancing in degrees one through three -/

theorem rtrace_balancedKernelMatrix_pow_one_eq_rightWeighted
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (s w : ι → ℂ)
    (hs : ∀ i, s i ^ 2 = w i) :
    RHLinalg.rtrace ((balancedKernelMatrix K s) ^ 1) =
      RHLinalg.rtrace ((rightWeightedKernelMatrix K w) ^ 1) := by
  rw [rtrace_pow_one_eq_cyclic_generic,
    rtrace_pow_one_eq_cyclic_generic]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i hi
  unfold balancedKernelMatrix rightWeightedKernelMatrix
  rw [← hs i]
  ring

theorem rtrace_balancedKernelMatrix_pow_two_eq_rightWeighted
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (s w : ι → ℂ)
    (hs : ∀ i, s i ^ 2 = w i) :
    RHLinalg.rtrace ((balancedKernelMatrix K s) ^ 2) =
      RHLinalg.rtrace ((rightWeightedKernelMatrix K w) ^ 2) := by
  rw [rtrace_pow_two_eq_cyclic_generic,
    rtrace_pow_two_eq_cyclic_generic]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold balancedKernelMatrix rightWeightedKernelMatrix
  rw [← hs i, ← hs j]
  ring

theorem rtrace_balancedKernelMatrix_pow_three_eq_rightWeighted
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (s w : ι → ℂ)
    (hs : ∀ i, s i ^ 2 = w i) :
    RHLinalg.rtrace ((balancedKernelMatrix K s) ^ 3) =
      RHLinalg.rtrace ((rightWeightedKernelMatrix K w) ^ 3) := by
  rw [rtrace_pow_three_eq_cyclic_generic,
    rtrace_pow_three_eq_cyclic_generic]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  unfold balancedKernelMatrix rightWeightedKernelMatrix
  rw [← hs i, ← hs j, ← hs k]
  ring

theorem rtrace_balancedFull_pow_one_eq_full
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    RHLinalg.rtrace ((balancedFullLatticeZeroMatrix F T) ^ 1) =
      RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 1) := by
  exact rtrace_balancedKernelMatrix_pow_one_eq_rightWeighted
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ => (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (fun ρ => QuarticTransfer.zeroEdgeWeight F T (ρ : ℂ))
    (fun ρ => zeroVertexWeight_sq F T hhat (ρ : ℂ))

theorem rtrace_balancedFull_pow_two_eq_full
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    RHLinalg.rtrace ((balancedFullLatticeZeroMatrix F T) ^ 2) =
      RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 2) := by
  exact rtrace_balancedKernelMatrix_pow_two_eq_rightWeighted
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ => (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (fun ρ => QuarticTransfer.zeroEdgeWeight F T (ρ : ℂ))
    (fun ρ => zeroVertexWeight_sq F T hhat (ρ : ℂ))

theorem rtrace_balancedFull_pow_three_eq_full
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    RHLinalg.rtrace ((balancedFullLatticeZeroMatrix F T) ^ 3) =
      RHLinalg.rtrace ((fullLatticeZeroMatrix F T) ^ 3) := by
  exact rtrace_balancedKernelMatrix_pow_three_eq_rightWeighted
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      fullLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ))
    (fun ρ => (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (fun ρ => QuarticTransfer.zeroEdgeWeight F T (ρ : ℂ))
    (fun ρ => zeroVertexWeight_sq F T hhat (ρ : ℂ))

theorem rtrace_balancedGuarded_pow_one_eq_guarded
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    RHLinalg.rtrace ((balancedGuardedLatticeZeroMatrix F T) ^ 1) =
      RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 1) := by
  exact rtrace_balancedKernelMatrix_pow_one_eq_rightWeighted
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      PoissonKernelBridge.canonicalGuardedPairKernel F T
        (ρ : ℂ) (ρ' : ℂ))
    (fun ρ => (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (fun ρ => QuarticTransfer.zeroEdgeWeight F T (ρ : ℂ))
    (fun ρ => zeroVertexWeight_sq F T hhat (ρ : ℂ))

theorem rtrace_balancedGuarded_pow_two_eq_guarded
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    RHLinalg.rtrace ((balancedGuardedLatticeZeroMatrix F T) ^ 2) =
      RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 2) := by
  exact rtrace_balancedKernelMatrix_pow_two_eq_rightWeighted
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      PoissonKernelBridge.canonicalGuardedPairKernel F T
        (ρ : ℂ) (ρ' : ℂ))
    (fun ρ => (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (fun ρ => QuarticTransfer.zeroEdgeWeight F T (ρ : ℂ))
    (fun ρ => zeroVertexWeight_sq F T hhat (ρ : ℂ))

theorem rtrace_balancedGuarded_pow_three_eq_guarded
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    RHLinalg.rtrace ((balancedGuardedLatticeZeroMatrix F T) ^ 3) =
      RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ 3) := by
  exact rtrace_balancedKernelMatrix_pow_three_eq_rightWeighted
    (fun ρ ρ' : ↥(ZeroSide.ZI Z T) =>
      PoissonKernelBridge.canonicalGuardedPairKernel F T
        (ρ : ℂ) (ρ' : ℂ))
    (fun ρ => (zeroVertexWeight F T (ρ : ℂ) : ℂ))
    (fun ρ => QuarticTransfer.zeroEdgeWeight F T (ρ : ℂ))
    (fun ρ => zeroVertexWeight_sq F T hhat (ρ : ℂ))

/-! ## Noncommutative low-degree perturbation bounds -/

theorem rtrace_pow_two_add_sub_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G R : Matrix ι ι ℂ) :
    |RHLinalg.rtrace ((G + R) ^ 2) - RHLinalg.rtrace (G ^ 2)| ≤
      ‖R‖ * ‖G + R‖ + ‖G‖ * ‖R‖ := by
  have hid :
      (G + R) ^ 2 - G ^ 2 = R * (G + R) + G * R := by
    noncomm_ring
  have h1 : |RHLinalg.rtrace (R * (G + R))| ≤
      ‖R‖ * ‖G + R‖ :=
    abs_rtrace_mul_le_frobenius R (G + R)
  have h2 : |RHLinalg.rtrace (G * R)| ≤ ‖G‖ * ‖R‖ :=
    abs_rtrace_mul_le_frobenius G R
  rw [← RHLinalg.rtrace_sub, hid, RHLinalg.rtrace_add]
  calc
    |RHLinalg.rtrace (R * (G + R)) + RHLinalg.rtrace (G * R)| ≤
        |RHLinalg.rtrace (R * (G + R))| +
          |RHLinalg.rtrace (G * R)| := abs_add_le _ _
    _ ≤ ‖R‖ * ‖G + R‖ + ‖G‖ * ‖R‖ := by linarith

theorem rtrace_pow_three_add_sub_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G R : Matrix ι ι ℂ) :
    |RHLinalg.rtrace ((G + R) ^ 3) - RHLinalg.rtrace (G ^ 3)| ≤
      ‖R‖ * ‖G + R‖ ^ 2 +
        (‖G‖ * ‖R‖) * ‖G + R‖ +
        ‖G‖ ^ 2 * ‖R‖ := by
  have hpow2 (X : Matrix ι ι ℂ) : ‖X ^ 2‖ ≤ ‖X‖ ^ 2 := by
    rw [pow_two, pow_two]
    exact Matrix.frobenius_norm_mul X X
  have hid :
      (G + R) ^ 3 - G ^ 3 =
        R * (G + R) ^ 2 + (G * R) * (G + R) + G ^ 2 * R := by
    noncomm_ring
  have h1 : |RHLinalg.rtrace (R * (G + R) ^ 2)| ≤
      ‖R‖ * ‖G + R‖ ^ 2 := by
    calc
      |RHLinalg.rtrace (R * (G + R) ^ 2)| ≤
          ‖R‖ * ‖(G + R) ^ 2‖ :=
        abs_rtrace_mul_le_frobenius R ((G + R) ^ 2)
      _ ≤ ‖R‖ * ‖G + R‖ ^ 2 := by
        gcongr
        exact hpow2 (G + R)
  have h2 : |RHLinalg.rtrace ((G * R) * (G + R))| ≤
      (‖G‖ * ‖R‖) * ‖G + R‖ := by
    calc
      |RHLinalg.rtrace ((G * R) * (G + R))| ≤
          ‖G * R‖ * ‖G + R‖ :=
        abs_rtrace_mul_le_frobenius (G * R) (G + R)
      _ ≤ (‖G‖ * ‖R‖) * ‖G + R‖ := by
        gcongr
        exact Matrix.frobenius_norm_mul G R
  have h3 : |RHLinalg.rtrace (G ^ 2 * R)| ≤
      ‖G‖ ^ 2 * ‖R‖ := by
    calc
      |RHLinalg.rtrace (G ^ 2 * R)| ≤ ‖G ^ 2‖ * ‖R‖ :=
        abs_rtrace_mul_le_frobenius (G ^ 2) R
      _ ≤ ‖G‖ ^ 2 * ‖R‖ := by
        gcongr
        exact hpow2 G
  rw [← RHLinalg.rtrace_sub, hid, RHLinalg.rtrace_add,
    RHLinalg.rtrace_add]
  calc
    |RHLinalg.rtrace (R * (G + R) ^ 2) +
        RHLinalg.rtrace ((G * R) * (G + R)) +
        RHLinalg.rtrace (G ^ 2 * R)| ≤
      |RHLinalg.rtrace (R * (G + R) ^ 2)| +
        |RHLinalg.rtrace ((G * R) * (G + R))| +
        |RHLinalg.rtrace (G ^ 2 * R)| := by
      let a := RHLinalg.rtrace (R * (G + R) ^ 2)
      let b := RHLinalg.rtrace ((G * R) * (G + R))
      let c := RHLinalg.rtrace (G ^ 2 * R)
      change |a + b + c| ≤ |a| + |b| + |c|
      calc
        |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
        _ ≤ (|a| + |b|) + |c| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ ‖R‖ * ‖G + R‖ ^ 2 +
        (‖G‖ * ‖R‖) * ‖G + R‖ +
        ‖G‖ ^ 2 * ‖R‖ := by linarith

/-! ## Balanced completed/guarded correction bounds -/

theorem full_sub_guarded_trace_two_abs_le_balanced_frobenius
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    |fullLatticeZeroKernelCyclicTrace2 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace2 F T| ≤
      ‖balancedRemoteLatticeZeroMatrix F T‖ *
          ‖balancedFullLatticeZeroMatrix F T‖ +
        ‖balancedGuardedLatticeZeroMatrix F T‖ *
          ‖balancedRemoteLatticeZeroMatrix F T‖ := by
  have h := rtrace_pow_two_add_sub_bound
    (balancedGuardedLatticeZeroMatrix F T)
    (balancedRemoteLatticeZeroMatrix F T)
  rw [balancedGuarded_add_remote_eq_full,
    rtrace_balancedFull_pow_two_eq_full F T hhat,
    rtrace_balancedGuarded_pow_two_eq_guarded F T hhat,
    rtrace_fullLatticeZeroMatrix_pow_two_eq_fullTrace,
    rtrace_guardedLatticeZeroMatrix_pow_two_eq_guardedTrace] at h
  exact h

theorem full_sub_guarded_trace_three_abs_le_balanced_frobenius
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hhat : 0 < F.hatDenominator T) :
    |fullLatticeZeroKernelCyclicTrace3 F T -
        QuarticTransfer.guardedZeroKernelCyclicTrace3 F T| ≤
      ‖balancedRemoteLatticeZeroMatrix F T‖ *
          ‖balancedFullLatticeZeroMatrix F T‖ ^ 2 +
        (‖balancedGuardedLatticeZeroMatrix F T‖ *
          ‖balancedRemoteLatticeZeroMatrix F T‖) *
          ‖balancedFullLatticeZeroMatrix F T‖ +
        ‖balancedGuardedLatticeZeroMatrix F T‖ ^ 2 *
          ‖balancedRemoteLatticeZeroMatrix F T‖ := by
  have h := rtrace_pow_three_add_sub_bound
    (balancedGuardedLatticeZeroMatrix F T)
    (balancedRemoteLatticeZeroMatrix F T)
  rw [balancedGuarded_add_remote_eq_full,
    rtrace_balancedFull_pow_three_eq_full F T hhat,
    rtrace_balancedGuarded_pow_three_eq_guarded F T hhat,
    rtrace_fullLatticeZeroMatrix_pow_three_eq_fullTrace,
    rtrace_guardedLatticeZeroMatrix_pow_three_eq_guardedTrace] at h
  exact h

end RH.Zeta85.RSPoissonCyclicBridge
