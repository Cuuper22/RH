import RH.Zeta85.Discharge.RSGuardedZeroBlock

open MeasureTheory Set Filter Matrix Finset RHLinalg
open scoped BigOperators Matrix.Norms.Frobenius ComplexOrder

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

/-- The inner product of two guarded-grid feature vectors is the canonical
contiguous guarded pair kernel. -/
theorem sum_guardedGridVector_mul_eq_canonicalGuardedPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (ρ ρ' : Zeta23.ZeroSide.ZI Z T) :
    (∑ i : Fin (guardedGridDim F T),
      guardedGridVector F T ρ i * guardedGridVector F T ρ' i) =
      PoissonKernelBridge.canonicalGuardedPairKernel F T (ρ : ℂ) (ρ' : ℂ) := by
  unfold guardedGridVector guardedGridDim guardedGridLabel
  unfold PoissonKernelBridge.canonicalGuardedPairKernel
    PoissonKernelBridge.distinguishedLatticeScale
    PoissonKernelBridge.canonicalGuardedLatticeSegment
    PoissonKernelBridge.distinguishedLatticeTerm
    PoissonKernelBridge.distinguishedLatticeFeature
    PoissonKernelBridge.distinguishedGridStep
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Weighted zero-to-grid factor. -/
def guardedGridLeft
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    Matrix (Fin (guardedGridDim F T))
      (Zeta23.ZeroSide.ZI Z T) ℂ :=
  fun i ρ => QuarticTransfer.zeroEdgeWeight F T (ρ : ℂ) *
    guardedGridVector F T ρ i

/-- Unweighted grid-to-zero factor. -/
def guardedGridRight
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    Matrix (Zeta23.ZeroSide.ZI Z T)
      (Fin (guardedGridDim F T)) ℂ :=
  fun ρ i => guardedGridVector F T ρ i

/-- The enlarged zero-side block is the grid-space product L R. -/
theorem guardedGridBlock_eq_left_mul_right
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    guardedGridBlock F T w c hadm =
      guardedGridLeft F T * guardedGridRight F T := by
  ext i j
  rw [guardedGridBlock, Matrix.smul_apply,
    Zeta23.ZeroSide.ZeroBlockData.blockA_apply, Matrix.mul_apply]
  simp only [guardedGridData, Zeta23.ZeroSide.mkData_m,
    Zeta23.ZeroSide.mkData_v, guardedGridLeft, guardedGridRight,
    QuarticTransfer.zeroEdgeWeight, smul_eq_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

/-- The guarded zero-space matrix is the reverse product R L. -/
theorem guardedLatticeZeroMatrix_eq_right_mul_left
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) :
    guardedLatticeZeroMatrix F T =
      guardedGridRight F T * guardedGridLeft F T := by
  ext ρ ρ'
  rw [Matrix.mul_apply]
  unfold guardedGridRight guardedGridLeft guardedLatticeZeroMatrix
  calc
    ∑ i, guardedGridVector F T ρ i *
        (QuarticTransfer.zeroEdgeWeight F T (ρ' : ℂ) *
          guardedGridVector F T ρ' i) =
      (∑ i, guardedGridVector F T ρ i *
        guardedGridVector F T ρ' i) *
          QuarticTransfer.zeroEdgeWeight F T (ρ' : ℂ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = PoissonKernelBridge.canonicalGuardedPairKernel F T
          (ρ : ℂ) (ρ' : ℂ) *
        QuarticTransfer.zeroEdgeWeight F T (ρ' : ℂ) := by
      rw [sum_guardedGridVector_mul_eq_canonicalGuardedPairKernel]

/-- Rectangular cyclicity in every positive degree. -/
private theorem trace_pow_succ_rect_comm
    {d ι : Type*} [Fintype d] [DecidableEq d]
    [Fintype ι] [DecidableEq ι]
    (L : Matrix d ι ℂ) (R : Matrix ι d ℂ) (k : ℕ) :
    Matrix.trace ((L * R) ^ (k + 1)) =
      Matrix.trace ((R * L) ^ (k + 1)) := by
  have key : ∀ k : ℕ, (L * R) ^ (k + 1) =
      L * (R * L) ^ k * R := by
    intro k
    induction k with
    | zero => simp [Matrix.mul_assoc]
    | succ k ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]
  rw [key, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, ← pow_succ]

/-- Every positive power has the same real trace on the enlarged grid block
and on the guarded zero-space matrix. -/
theorem rtrace_guardedGridBlock_pow_succ_eq_guardedLattice
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) (k : ℕ) :
    RHLinalg.rtrace ((guardedGridBlock F T w c hadm) ^ (k + 1)) =
      RHLinalg.rtrace ((guardedLatticeZeroMatrix F T) ^ (k + 1)) := by
  unfold RHLinalg.rtrace
  rw [guardedGridBlock_eq_left_mul_right hadm,
    guardedLatticeZeroMatrix_eq_right_mul_left]
  exact congrArg Complex.re
    (trace_pow_succ_rect_comm (guardedGridLeft F T)
      (guardedGridRight F T) k)

end RH.Zeta85.RSPoissonCyclicBridge