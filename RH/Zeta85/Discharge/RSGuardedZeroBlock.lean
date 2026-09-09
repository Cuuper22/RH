import RH.Zeta85.Discharge.RSLowDegreeRemoteCorrectionThree

/-!
# The guarded modulation grid as the zero-side block

Instead of treating the two endpoint strips as an error, this file makes the
entire contiguous guarded lattice the finite feature family.  The abstract
zero-side decomposition then applies to that enlarged block exactly.
-/

open MeasureTheory Set Filter Matrix RHLinalg
open scoped BigOperators Matrix.Norms.Frobenius ComplexOrder

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

/-- Number of columns in the contiguous guarded modulation grid. -/
def guardedGridDim
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℕ :=
  let r := PoissonKernelBridge.distinguishedEndpointGuardWidth F T
  r + F.channelDim T (F.distinguished T) + r

/-- Integer lattice label of a guarded-grid column. -/
def guardedGridLabel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (i : Fin (guardedGridDim F T)) : ℤ :=
  (i.val : ℤ) -
    (PoissonKernelBridge.distinguishedEndpointGuardWidth F T : ℤ)

/-- The raw normalized Fourier feature on one enlarged-window zero. -/
def guardedGridVector
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (ρ : Zeta23.ZeroSide.ZI Z T) : Fin (guardedGridDim F T) → ℂ :=
  fun i =>
    (Real.sqrt (QuarticGramFamily.fullLength (σ := σ) T /
      F.period T (F.distinguished T)) : ℂ) *
      PoissonKernelBridge.distinguishedLatticeFeature F T
        (guardedGridLabel F T i) ρ

/-- A real even window has a Fourier transform commuting with conjugation. -/
private theorem paperFT_star_of_even
    (w : ℝ → ℝ) (heven : ∀ u, w (-u) = w u) (z : ℂ) :
    paperFT (fun u => (w u : ℂ)) ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (paperFT (fun u => (w u : ℂ)) z) := by
  calc
    paperFT (fun u => (w u : ℂ)) ((starRingEnd ℂ) z) =
        paperFT (fun u => (w u : ℂ)) (-((starRingEnd ℂ) z)) :=
      (Zeta23.Taper.paperFT_neg_of_even heven ((starRingEnd ℂ) z)).symm
    _ = (starRingEnd ℂ) (paperFT (fun u => (w u : ℂ)) z) :=
      (Zeta23.Taper.conj_paperFT_ofReal w z).symm

/-- Each guarded-grid feature respects reflection of the zero. -/
theorem distinguishedLatticeFeature_reflect
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (k : ℤ) (ρ : Zeta23.ZeroSide.ZI Z T) :
    PoissonKernelBridge.distinguishedLatticeFeature F T k
        ⟨reflect (ρ : ℂ),
          Zeta23.ZeroSide.reflect_mem_ZI Z T ρ.2⟩ =
      (starRingEnd ℂ)
        (PoissonKernelBridge.distinguishedLatticeFeature F T k ρ) := by
  unfold PoissonKernelBridge.distinguishedLatticeFeature
  rw [Zeta23.ZeroSide.gammaOf_reflect]
  have harg :
      (starRingEnd ℂ) (gammaOf (ρ : ℂ)) -
          (T + (k : ℝ) *
            PoissonKernelBridge.distinguishedGridStep F T : ℝ) =
        (starRingEnd ℂ)
          (gammaOf (ρ : ℂ) -
            (T + (k : ℝ) *
              PoissonKernelBridge.distinguishedGridStep F T : ℝ)) := by
    simp
  rw [harg, paperFT_star_of_even _ hadm.even]

/-- The full guarded vector is equivariant under zero reflection. -/
theorem guardedGridVector_reflect
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    ∀ ρ : Zeta23.ZeroSide.ZI Z T,
      guardedGridVector F T
          ⟨reflect (ρ : ℂ),
            Zeta23.ZeroSide.reflect_mem_ZI Z T ρ.2⟩ =
        star (guardedGridVector F T ρ) := by
  intro ρ
  funext i
  simp only [guardedGridVector, Pi.star_apply, map_mul,
    RCLike.star_def, Complex.conj_ofReal]
  rw [distinguishedLatticeFeature_reflect hadm]

/-- Abstract zero-side data for the entire contiguous guarded grid. -/
def guardedGridData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    Zeta23.ZeroSide.ZeroBlockData (Zeta23.ZeroSide.ZI Z T)
      (Fin (guardedGridDim F T)) :=
  Zeta23.ZeroSide.mkData Z T (guardedGridVector F T)
    (guardedGridVector_reflect hadm)

/-- Canonical representatives of the off-line reflected pairs. -/
def guardedGridPairReps
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    (guardedGridData F T w c hadm).PairReps :=
  Zeta23.ZeroSide.mkPairReps Z T (guardedGridVector F T)
    (guardedGridVector_reflect hadm)

/-- The normalized column-space block of the guarded grid. -/
def guardedGridBlock
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    Matrix (Fin (guardedGridDim F T)) (Fin (guardedGridDim F T)) ℂ :=
  (((F.hatDenominator T)⁻¹ : ℝ) : ℂ) •
    (guardedGridData F T w c hadm).blockA

/-- The on-line positive part of the guarded block. -/
def guardedGridP
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    Matrix (Fin (guardedGridDim F T)) (Fin (guardedGridDim F T)) ℂ :=
  (guardedGridData F T w c hadm).blockP (F.hatDenominator T)

/-- The reflected-pair Hermitian part of the guarded block. -/
def guardedGridQ
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T w c : ℝ)
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    Matrix (Fin (guardedGridDim F T)) (Fin (guardedGridDim F T)) ℂ :=
  (guardedGridData F T w c hadm).blockQ (F.hatDenominator T)

/-- The zero-side decomposition is exact on the enlarged guarded grid. -/
theorem guardedGridBlock_eq_P_add_Q
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    guardedGridBlock F T w c hadm =
      guardedGridP F T w c hadm + guardedGridQ F T w c hadm := by
  symm
  exact (guardedGridData F T w c hadm).blockP_add_blockQ
    (F.hatDenominator T)

/-- The on-line part is positive semidefinite. -/
theorem guardedGridP_posSemidef
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hhat : 0 < F.hatDenominator T) :
    (guardedGridP F T w c hadm).PosSemidef := by
  exact (guardedGridData F T w c hadm).blockP_posSemidef hhat

/-- Rank of the positive part is bounded by the simple and multiple on-line
zero counts, exactly as in the original block. -/
theorem rank_guardedGridP_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hhat : 0 < F.hatDenominator T) :
    (guardedGridP F T w c hadm).rank ≤ Z.s1 T + Z.s2 T := by
  change ((guardedGridData F T w c hadm).blockP
    (F.hatDenominator T)).rank ≤ Z.s1 T + Z.s2 T
  rw [Zeta23.ZeroSide.s1_eq_mk Z T (guardedGridVector F T)
      (guardedGridVector_reflect hadm),
    Zeta23.ZeroSide.s2_eq_mk Z T (guardedGridVector F T)
      (guardedGridVector_reflect hadm)]
  exact (guardedGridData F T w c hadm).rank_blockP_le hhat

/-- The pair part is Hermitian. -/
theorem guardedGridQ_isHermitian
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c) :
    (guardedGridQ F T w c hadm).IsHermitian := by
  exact (guardedGridData F T w c hadm).blockQ_isHermitian
    (F.hatDenominator T)

/-- The positive inertia of the pair part is bounded by the number of
reflected off-line pairs. -/
theorem posIndex_guardedGridQ_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} {T w c : ℝ}
    (hadm : AdmWindow (F.window T (F.distinguished T))
      (F.period T (F.distinguished T)) w c)
    (hhat : 0 < F.hatDenominator T) :
    posIndex (guardedGridQ_isHermitian hadm) ≤ Z.p T := by
  change posIndex ((guardedGridData F T w c hadm).blockQ_isHermitian
    (F.hatDenominator T)) ≤ Z.p T
  rw [Zeta23.ZeroSide.p_eq_mk Z T (guardedGridVector F T)
      (guardedGridVector_reflect hadm)]
  exact (guardedGridData F T w c hadm).posIndex_blockQ_le
    (guardedGridPairReps F T w c hadm) hhat

end RH.Zeta85.RSPoissonCyclicBridge