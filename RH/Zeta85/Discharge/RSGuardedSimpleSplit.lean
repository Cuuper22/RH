import RH.Zeta85.Discharge.RSGuardedBlockFactorization

open MeasureTheory Set Filter Matrix Finset RHLinalg
open scoped BigOperators Matrix.Norms.Frobenius ComplexOrder

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23 Zeta23.ZeroSide

namespace SimpleSplit

variable {ι d : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype d] [DecidableEq d]

/-- The contribution of simple on-line atoms only. -/
def simplePart (D : Zeta23.ZeroSide.ZeroBlockData ι d) : Matrix d d ℂ :=
  ∑ z ∈ D.S₁, (D.m z : ℂ) • Matrix.vecMulVec (D.v z) (D.v z)

/-- The contribution of multiple on-line atoms only. -/
def multiplePart (D : Zeta23.ZeroSide.ZeroBlockData ι d) : Matrix d d ℂ :=
  ∑ z ∈ D.S₂, (D.m z : ℂ) • Matrix.vecMulVec (D.v z) (D.v z)

lemma simplePart_posSemidef (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    (simplePart D).PosSemidef := by
  unfold simplePart
  refine posSemidef_sum _ fun z hz => ?_
  simp only [Zeta23.ZeroSide.ZeroBlockData.S₁, Finset.mem_filter,
    Finset.mem_univ, true_and] at hz
  exact Zeta23.ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec
    (D.star_v_of_onLine hz.1) (Nat.cast_nonneg (D.m z))

lemma multiplePart_posSemidef (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    (multiplePart D).PosSemidef := by
  unfold multiplePart
  refine posSemidef_sum _ fun z hz => ?_
  simp only [Zeta23.ZeroSide.ZeroBlockData.S₂, Finset.mem_filter,
    Finset.mem_univ, true_and] at hz
  exact Zeta23.ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec
    (D.star_v_of_onLine hz.1) (Nat.cast_nonneg (D.m z))

lemma rank_simplePart_le (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    (simplePart D).rank ≤ D.s₁ := by
  unfold simplePart Zeta23.ZeroSide.ZeroBlockData.s₁
  refine (rank_sum_le _ _ (fun _ => 1)
    fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

lemma rank_multiplePart_le (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    (multiplePart D).rank ≤ D.s₂ := by
  unfold multiplePart Zeta23.ZeroSide.ZeroBlockData.s₂
  refine (rank_sum_le _ _ (fun _ => 1)
    fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

lemma onPart_eq_simple_add_multiple
    (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    D.onPart = simplePart D + multiplePart D := by
  unfold Zeta23.ZeroSide.ZeroBlockData.onPart simplePart multiplePart
  rw [D.onLine_eq_S₁_union_S₂,
    Finset.sum_union D.disjoint_S₁_S₂]

variable (D : Zeta23.ZeroSide.ZeroBlockData ι d)
  (P : D.PairReps)

lemma blockA_sub_simple_eq :
    D.blockA - simplePart D =
      multiplePart D + (D.rePart P - D.imPart P) := by
  rw [D.blockA_decomp P, onPart_eq_simple_add_multiple]
  abel

end SimpleSplit

/-- Positive block containing only simple on-line zeros. -/
def guardedGridSimpleP
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    Matrix (Fin (guardedGridDim F T)) (Fin (guardedGridDim F T)) ℂ :=
  (((F.hatDenominator T)⁻¹ : ℝ) : ℂ) •
    SimpleSplit.simplePart (guardedGridData F T w c hadm)

/-- Everything except the simple on-line block. -/
def guardedGridBadQ
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    Matrix (Fin (guardedGridDim F T)) (Fin (guardedGridDim F T)) ℂ :=
  (((F.hatDenominator T)⁻¹ : ℝ) : ℂ) •
    ((guardedGridData F T w c hadm).blockA -
      SimpleSplit.simplePart (guardedGridData F T w c hadm))

/-- Exact simple/bad decomposition of the enlarged guarded block. -/
theorem guardedGridBlock_eq_simpleP_add_badQ
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    guardedGridBlock F T w c hadm =
      guardedGridSimpleP F T w c hadm +
        guardedGridBadQ F T w c hadm := by
  unfold guardedGridBlock guardedGridSimpleP guardedGridBadQ
  rw [← smul_add]
  congr 1
  abel

/-- The simple block is positive semidefinite. -/
theorem guardedGridSimpleP_posSemidef
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hhat : 0 < F.hatDenominator T) :
    (guardedGridSimpleP F T w c hadm).PosSemidef := by
  unfold guardedGridSimpleP
  exact (SimpleSplit.simplePart_posSemidef
    (guardedGridData F T w c hadm)).smul
      (Complex.zero_le_real.mpr (inv_nonneg.mpr hhat.le))

/-- The simple block rank is bounded by the number of simple critical-line
zeros, exactly matching the frozen transfer. -/
theorem rank_guardedGridSimpleP_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hhat : 0 < F.hatDenominator T) :
    (guardedGridSimpleP F T w c hadm).rank ≤ Z.s1 T := by
  unfold guardedGridSimpleP
  rw [Zeta23.ZeroSide.rank_smul_of_ne_zero _ (by
    exact_mod_cast (inv_ne_zero hhat.ne'))]
  rw [Zeta23.ZeroSide.s1_eq_mk Z T (guardedGridVector F T)
      (guardedGridVector_reflect hadm)]
  exact SimpleSplit.rank_simplePart_le
    (guardedGridData F T w c hadm)

/-- The bad block is Hermitian. -/
theorem guardedGridBadQ_isHermitian
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    (guardedGridBadQ F T w c hadm).IsHermitian := by
  unfold guardedGridBadQ
  exact Zeta23.ZeroSide.ZeroBlockData.isHermitian_real_smul
    ((guardedGridData F T w c hadm).blockA_isHermitian.sub
      (SimpleSplit.simplePart_posSemidef
        (guardedGridData F T w c hadm)).isHermitian) _

/-- The positive inertia of the bad block is bounded by multiple on-line
zeros plus off-line reflected pairs. -/
theorem posIndex_guardedGridBadQ_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hhat : 0 < F.hatDenominator T) :
    posIndex (guardedGridBadQ_isHermitian hadm) ≤ Z.s2 T + Z.p T := by
  let D := guardedGridData F T w c hadm
  let P := guardedGridPairReps F T w c hadm
  have hM := SimpleSplit.multiplePart_posSemidef D
  have hRe := D.rePart_posSemidef P
  have hIm := D.imPart_posSemidef P
  have hbase :
      (SimpleSplit.multiplePart D + (D.rePart P - D.imPart P)).IsHermitian :=
    hM.isHermitian.add (hRe.isHermitian.sub hIm.isHermitian)
  have hqeq : guardedGridBadQ F T w c hadm =
      ((((F.hatDenominator T)⁻¹ : ℝ) : ℂ) •
        (SimpleSplit.multiplePart D + (D.rePart P - D.imPart P))) := by
    unfold guardedGridBadQ
    rw [SimpleSplit.blockA_sub_simple_eq]
  have hindex : posIndex (guardedGridBadQ_isHermitian hadm) =
      posIndex hbase := by
    rw [Zeta23.ZeroSide.ZeroBlockData.posIndex_congr
      (guardedGridBadQ_isHermitian hadm)
      (Zeta23.ZeroSide.ZeroBlockData.isHermitian_real_smul hbase
        (F.hatDenominator T)⁻¹) hqeq]
    exact RHLinalg.posIndex_smul_pos hbase (inv_pos.mpr hhat) _
  rw [hindex]
  have h1 := RHLinalg.posIndex_add_le hM.isHermitian
    (hRe.isHermitian.sub hIm.isHermitian)
  rw [RHLinalg.posIndex_eq_rank_of_posSemidef hM] at h1
  have h2 := RHLinalg.posIndex_sub_le_rank hRe hIm
  have hbound : posIndex hbase ≤ D.s₂ + P.p :=
    h1.trans (Nat.add_le_add
      (SimpleSplit.rank_multiplePart_le D)
      (h2.trans (D.rank_rePart_le P)))
  rw [Zeta23.ZeroSide.s2_eq_mk Z T (guardedGridVector F T)
      (guardedGridVector_reflect hadm),
    Zeta23.ZeroSide.p_eq_mk Z T (guardedGridVector F T)
      (guardedGridVector_reflect hadm)]
  exact hbound

end RH.Zeta85.RSPoissonCyclicBridge