import RH.Zeta85.Inputs95
import Zeta23.Poisson.ComplexAlias

open Filter Matrix MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace RH.Zeta85.PoissonKernelBridge

open Zeta23 RHLinalg

def distinguishedBlockLabel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (i : Fin (F.blockDim T)) :
    Fin (F.channelDim T (F.distinguished T)) :=
  Fin.cast
    (congrArg (F.channelDim T) (hcolumns i))
    (F.columnAddress T (F.blockEmbedding T i)).2

private theorem distinguishedBlockLabel_injective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (haddress : Function.Injective (F.columnAddress T))
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T) :
    Function.Injective (distinguishedBlockLabel F T hcolumns) := by
  intro i i' hii'
  apply (F.blockEmbedding T).injective
  apply haddress
  apply Sigma.ext
    ((hcolumns i).trans (hcolumns i').symm)
  apply (Fin.heq_ext_iff
    (congrArg (F.channelDim T)
      ((hcolumns i).trans (hcolumns i').symm))).2
  have hval := congrArg Fin.val hii'
  change
    (F.columnAddress T (F.blockEmbedding T i)).2.val =
      (F.columnAddress T (F.blockEmbedding T i')).2.val at hval
  exact hval

private theorem distinguishedBlockLabel_surjective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (haddress : Function.Surjective (F.columnAddress T))
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (hexhaustive : ∀ i,
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i) :
    Function.Surjective (distinguishedBlockLabel F T hcolumns) := by
  intro k
  obtain ⟨i, hi⟩ := haddress ⟨F.distinguished T, k⟩
  have hfirst : (F.columnAddress T i).1 = F.distinguished T := by
    exact congrArg Sigma.fst hi
  obtain ⟨b, hb⟩ := hexhaustive i hfirst
  refine ⟨b, ?_⟩
  apply Fin.ext
  have hfull :
      F.columnAddress T (F.blockEmbedding T b) =
        ⟨F.distinguished T, k⟩ := by
    rw [hb, hi]
  have hval := congrArg (fun a => a.2.val) hfull
  change (F.columnAddress T (F.blockEmbedding T b)).2.val = k.val
  exact hval

def distinguishedBlockLabelEquiv
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (haddress : Function.Bijective (F.columnAddress T))
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (hexhaustive : ∀ i,
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i) :
    Fin (F.blockDim T) ≃ Fin (F.channelDim T (F.distinguished T)) :=
  Equiv.ofBijective (distinguishedBlockLabel F T hcolumns)
    ⟨distinguishedBlockLabel_injective F T haddress.1 hcolumns,
      distinguishedBlockLabel_surjective F T haddress.2 hcolumns hexhaustive⟩

def distinguishedAtom
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (k : Fin (F.channelDim T (F.distinguished T))) (ρ : ℂ) : ℂ :=
  let j := F.distinguished T
  let L := F.period T j
  (Real.sqrt (QuarticGramFamily.fullLength (σ := σ) T / L) : ℂ) *
    paperFT (fun u => (F.window T j u : ℂ))
      (gammaOf ρ - (T + 2 * Real.pi * (k : ℕ) / L : ℝ))

theorem atom_blockEmbedding_eq_distinguishedAtom
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (i : Fin (F.blockDim T)) (ρ : ℂ) :
    F.atom T (F.blockEmbedding T i) ρ =
      distinguishedAtom F T (distinguishedBlockLabel F T hcolumns i) ρ := by
  cases haddress : F.columnAddress T (F.blockEmbedding T i) with
  | mk j k =>
      have hj : j = F.distinguished T := by
        simpa only [haddress] using hcolumns i
      subst j
      simp only [QuarticGramFamily.atom, distinguishedAtom,
        distinguishedBlockLabel, haddress, Fin.val_cast]

def blockPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑ i : Fin (F.blockDim T),
    F.atom T (F.blockEmbedding T i) ρ *
      F.atom T (F.blockEmbedding T i) ρ'

theorem zeroPairKernel_eq_distinguishedLabelSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (haddress : Function.Bijective (F.columnAddress T))
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (hexhaustive : ∀ i,
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (ρ ρ' : ℂ) :
    blockPairKernel F T ρ ρ' =
      ∑ k : Fin (F.channelDim T (F.distinguished T)),
        distinguishedAtom F T k ρ * distinguishedAtom F T k ρ' := by
  unfold blockPairKernel
  apply Fintype.sum_equiv
    (distinguishedBlockLabelEquiv F T haddress hcolumns hexhaustive)
  intro i
  rw [atom_blockEmbedding_eq_distinguishedAtom F T hcolumns,
    atom_blockEmbedding_eq_distinguishedAtom F T hcolumns]
  rfl

/-- The full integer frequency lattice attached to the distinguished
channel, in exactly the convention used by complex Poisson summation. -/
def distinguishedLatticeTerm
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (k : ℤ) : ℂ :=
  let j := F.distinguished T
  let L := F.period T j
  paperFT (fun u => (F.window T j u : ℂ))
      (z - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)) *
    paperFT (fun u => (F.window T j u : ℂ))
      (z' - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ))

/-- A product of two actual block atoms is the corresponding distinguished
lattice term times the construction's squared normalization. -/
theorem distinguishedAtom_mul_eq_latticeTerm
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (k : Fin (F.channelDim T (F.distinguished T))) (ρ ρ' : ℂ) :
    distinguishedAtom F T k ρ * distinguishedAtom F T k ρ' =
      ((Real.sqrt
        (QuarticGramFamily.fullLength (σ := σ) T /
          F.period T (F.distinguished T)) : ℂ) ^ 2) *
        distinguishedLatticeTerm F T (gammaOf ρ) (gammaOf ρ') (k : ℕ) := by
  unfold distinguishedAtom distinguishedLatticeTerm
  dsimp only
  have hfrequency :
      T + 2 * Real.pi * (k : ℕ) / F.period T (F.distinguished T) =
        T + ((k : ℕ) : ℝ) *
          (2 * Real.pi / F.period T (F.distinguished T)) := by
    ring
  rw [hfrequency]
  push_cast
  ring

/-- The live scalar block contraction is therefore an exact initial segment
of the full complex Poisson lattice. -/
theorem blockPairKernel_eq_latticeSegment
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (haddress : Function.Bijective (F.columnAddress T))
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (hexhaustive : ∀ i,
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (ρ ρ' : ℂ) :
    blockPairKernel F T ρ ρ' =
      ((Real.sqrt
        (QuarticGramFamily.fullLength (σ := σ) T /
          F.period T (F.distinguished T)) : ℂ) ^ 2) *
        ∑ k : Fin (F.channelDim T (F.distinguished T)),
          distinguishedLatticeTerm F T (gammaOf ρ) (gammaOf ρ') (k : ℕ) := by
  rw [zeroPairKernel_eq_distinguishedLabelSum
    F T haddress hcolumns hexhaustive]
  simp_rw [distinguishedAtom_mul_eq_latticeTerm]
  rw [← Finset.mul_sum]

/-- Complex Poisson summation specialized to the literal distinguished
window.  Its spectral side is definitionally the full lattice extending the
finite segment in `blockPairKernel_eq_latticeSegment`. -/
theorem hasSum_distinguishedLatticeTerm_alias
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupport : ∀ u, Λ < |u| →
      (F.window T (F.distinguished T) u : ℂ) = 0)
    (z z' : ℂ) :
    Summable (Zeta23.Poisson.complexPoissonAliasTerm
      (fun u => (F.window T (F.distinguished T) u : ℂ))
      (F.period T (F.distinguished T)) T z z') ∧
      HasSum (distinguishedLatticeTerm F T z z')
        (∑' m : ℤ, Zeta23.Poisson.complexPoissonAliasTerm
          (fun u => (F.window T (F.distinguished T) u : ℂ))
          (F.period T (F.distinguished T)) T z z' m) := by
  obtain ⟨hsummable, hsum⟩ :=
    Zeta23.Poisson.hasSum_paperFT_mul_paperFT_alias
      hL hΛ hwindow hsupport z z'
  refine ⟨hsummable, hsum.congr ?_⟩
  intro k
  rfl

/-- The canonical embedding of the first `n` nonnegative labels into the
integer Poisson lattice. -/
def finiteLabelEmbedding (n : ℕ) : Fin n ↪ ℤ where
  toFun k := (k : ℕ)
  inj' := by
    intro k l hkl
    apply Fin.ext
    exact Int.ofNat_inj.mp hkl

/-- Extend the actual finite label segment by zero to the full integer
lattice. -/
def distinguishedLatticeSegmentExtension
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) : ℤ → ℂ :=
  Function.extend (finiteLabelEmbedding n)
    (fun k : Fin n => distinguishedLatticeTerm F T z z' (k : ℕ)) 0

/-- What the actual finite block omits from the full Poisson lattice.  This
single signed family contains both the negative-frequency side and the
upper tail beyond the last retained channel label. -/
def distinguishedLatticeRemainder
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  distinguishedLatticeTerm F T z z' k -
    distinguishedLatticeSegmentExtension F T z z' n k

theorem hasSum_distinguishedLatticeSegmentExtension
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) :
    HasSum (distinguishedLatticeSegmentExtension F T z z' n)
      (∑ k : Fin n, distinguishedLatticeTerm F T z z' (k : ℕ)) := by
  unfold distinguishedLatticeSegmentExtension
  exact (hasSum_extend_zero (finiteLabelEmbedding n).injective).2
    (hasSum_fintype _)

/-- Exact Poisson remainder identity: after the actual finite segment is
removed, the remaining lattice has sum equal to the full spatial-alias sum
minus that segment. -/
theorem hasSum_distinguishedLatticeRemainder
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupport : ∀ u, Λ < |u| →
      (F.window T (F.distinguished T) u : ℂ) = 0)
    (z z' : ℂ) (n : ℕ) :
    HasSum (distinguishedLatticeRemainder F T z z' n)
      ((∑' m : ℤ, Zeta23.Poisson.complexPoissonAliasTerm
          (fun u => (F.window T (F.distinguished T) u : ℂ))
          (F.period T (F.distinguished T)) T z z' m) -
        ∑ k : Fin n, distinguishedLatticeTerm F T z z' (k : ℕ)) := by
  obtain ⟨_, hfull⟩ := hasSum_distinguishedLatticeTerm_alias
    F T Λ hL hΛ hwindow hsupport z z'
  exact hfull.sub
    (hasSum_distinguishedLatticeSegmentExtension F T z z' n)

/-- The scalar kernel entering every factored quartic cycle is now expressed
as one full spatial-alias sum minus one explicit finite-grid remainder. -/
theorem blockPairKernel_eq_aliasSum_sub_remainder
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T Λ : ℝ)
    (haddress : Function.Bijective (F.columnAddress T))
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (hexhaustive : ∀ i,
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupport : ∀ u, Λ < |u| →
      (F.window T (F.distinguished T) u : ℂ) = 0)
    (ρ ρ' : ℂ) :
    blockPairKernel F T ρ ρ' =
      ((Real.sqrt
        (QuarticGramFamily.fullLength (σ := σ) T /
          F.period T (F.distinguished T)) : ℂ) ^ 2) *
        ((∑' m : ℤ, Zeta23.Poisson.complexPoissonAliasTerm
            (fun u => (F.window T (F.distinguished T) u : ℂ))
            (F.period T (F.distinguished T)) T
            (gammaOf ρ) (gammaOf ρ') m) -
          ∑' k : ℤ, distinguishedLatticeRemainder F T
            (gammaOf ρ) (gammaOf ρ')
            (F.channelDim T (F.distinguished T)) k) := by
  rw [blockPairKernel_eq_latticeSegment
    F T haddress hcolumns hexhaustive]
  have hrem := hasSum_distinguishedLatticeRemainder
    F T Λ hL hΛ hwindow hsupport (gammaOf ρ) (gammaOf ρ')
      (F.channelDim T (F.distinguished T))
  rw [hrem.tsum_eq]
  ring

/-- The Poisson-completed value of one pair kernel: all spatial aliases,
with precisely the integer frequencies absent from the finite block removed. -/
def poissonAliasCompletedPair
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((Real.sqrt
    (QuarticGramFamily.fullLength (σ := σ) T /
      F.period T (F.distinguished T)) : ℂ) ^ 2) *
    ((∑' m : ℤ, Zeta23.Poisson.complexPoissonAliasTerm
        (fun u => (F.window T (F.distinguished T) u : ℂ))
        (F.period T (F.distinguished T)) T
        (gammaOf ρ) (gammaOf ρ') m) -
      ∑' k : ℤ, distinguishedLatticeRemainder F T
        (gammaOf ρ) (gammaOf ρ')
        (F.channelDim T (F.distinguished T)) k)

theorem blockPairKernel_eq_poissonAliasCompletedPair
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T Λ : ℝ)
    (haddress : Function.Bijective (F.columnAddress T))
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (hexhaustive : ∀ i,
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupport : ∀ u, Λ < |u| →
      (F.window T (F.distinguished T) u : ℂ) = 0)
    (ρ ρ' : ℂ) :
    blockPairKernel F T ρ ρ' = poissonAliasCompletedPair F T ρ ρ' := by
  unfold poissonAliasCompletedPair
  exact blockPairKernel_eq_aliasSum_sub_remainder
    F T Λ haddress hcolumns hexhaustive hL hΛ hwindow hsupport ρ ρ'

end RH.Zeta85.PoissonKernelBridge

end
