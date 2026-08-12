import RH.Zeta85.Inputs95
import Zeta23.Poisson.ComplexAlias

open Filter Matrix MeasureTheory
open scoped BigOperators Topology ContDiff

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

/-- The same distinguished-lattice identity with compact support supplied
directly, so downstream constructions need no arbitrary support radius. -/
theorem hasSum_distinguishedLatticeTerm_alias_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (z z' : ℂ) :
    Summable (Zeta23.Poisson.complexPoissonAliasTerm
      (fun u => (F.window T (F.distinguished T) u : ℂ))
      (F.period T (F.distinguished T)) T z z') ∧
      HasSum (distinguishedLatticeTerm F T z z')
        (∑' m : ℤ, Zeta23.Poisson.complexPoissonAliasTerm
          (fun u => (F.window T (F.distinguished T) u : ℂ))
          (F.period T (F.distinguished T)) T z z' m) := by
  obtain ⟨hsummable, hsum⟩ :=
    Zeta23.Poisson.hasSum_paperFT_mul_paperFT_alias_of_hasCompactSupport
      hL hwindow hcompact z z'
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

/-- The embedded finite labels are exactly the nonnegative integers below
`n`. -/
theorem exists_finiteLabelEmbedding_iff (n : ℕ) (k : ℤ) :
    (∃ i : Fin n, finiteLabelEmbedding n i = k) ↔
      0 ≤ k ∧ k < (n : ℤ) := by
  constructor
  · rintro ⟨i, rfl⟩
    change 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < (n : ℤ)
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr i.isLt⟩
  · rintro ⟨hk0, hkn⟩
    have hnat : k.toNat < n := by omega
    refine ⟨⟨k.toNat, hnat⟩, ?_⟩
    simp only [finiteLabelEmbedding]
    exact Int.toNat_of_nonneg hk0

theorem distinguishedLatticeSegmentExtension_apply
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) (i : Fin n) :
    distinguishedLatticeSegmentExtension F T z z' n
        (finiteLabelEmbedding n i) =
      distinguishedLatticeTerm F T z z' (i : ℕ) := by
  unfold distinguishedLatticeSegmentExtension
  exact (finiteLabelEmbedding n).injective.extend_apply _ _ i

/-- What the actual finite block omits from the full Poisson lattice.  This
single signed family contains both the negative-frequency side and the
upper tail beyond the last retained channel label. -/
def distinguishedLatticeRemainder
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  distinguishedLatticeTerm F T z z' k -
    distinguishedLatticeSegmentExtension F T z z' n k

/-- Every retained finite frequency cancels identically from the omitted
lattice remainder. -/
theorem distinguishedLatticeRemainder_inside
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) (i : Fin n) :
    distinguishedLatticeRemainder F T z z' n
        (finiteLabelEmbedding n i) = 0 := by
  rw [distinguishedLatticeRemainder,
    distinguishedLatticeSegmentExtension_apply]
  change distinguishedLatticeTerm F T z z' (i.val : ℤ) -
      distinguishedLatticeTerm F T z z' (i.val : ℤ) = 0
  ring

/-- Outside the retained interval, the remainder is literally the original
lattice term.  Thus it consists of exactly the negative side and the upper
tail. -/
theorem distinguishedLatticeRemainder_outside
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) (k : ℤ)
    (hk : k < 0 ∨ (n : ℤ) ≤ k) :
    distinguishedLatticeRemainder F T z z' n k =
      distinguishedLatticeTerm F T z z' k := by
  have hout : ¬ ∃ i : Fin n, finiteLabelEmbedding n i = k := by
    rw [exists_finiteLabelEmbedding_iff]
    omega
  rw [distinguishedLatticeRemainder]
  unfold distinguishedLatticeSegmentExtension
  rw [Function.extend_apply' _ _ _ hout]
  simp

/-- The exact index set omitted by the finite modulation grid. -/
def omittedLatticeSet (n : ℕ) : Set ℤ :=
  {k | k < 0 ∨ (n : ℤ) ≤ k}

/-- Pointwise, the remainder is the lattice family restricted to the two
omitted sides. -/
theorem distinguishedLatticeRemainder_eq_indicator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) :
    distinguishedLatticeRemainder F T z z' n =
      (omittedLatticeSet n).indicator
        (distinguishedLatticeTerm F T z z') := by
  funext k
  by_cases hk : k < 0 ∨ (n : ℤ) ≤ k
  · have hmem : k ∈ omittedLatticeSet n := hk
    rw [Set.indicator_of_mem hmem,
      distinguishedLatticeRemainder_outside F T z z' n k hk]
  · have hnot : k ∉ omittedLatticeSet n := hk
    rw [Set.indicator_of_notMem hnot]
    have hin : 0 ≤ k ∧ k < (n : ℤ) := by omega
    obtain ⟨i, hi⟩ := (exists_finiteLabelEmbedding_iff n k).2 hin
    rw [← hi, distinguishedLatticeRemainder_inside]

/-- The opaque full-integer remainder sum is exactly a sum over the negative
and upper-tail indices, with no retained frequency left inside it. -/
theorem tsum_distinguishedLatticeRemainder_eq_omitted
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) :
    (∑' k : ℤ, distinguishedLatticeRemainder F T z z' n k) =
      ∑' k : omittedLatticeSet n,
        distinguishedLatticeTerm F T z z' k := by
  rw [distinguishedLatticeRemainder_eq_indicator]
  exact
    (tsum_subtype (omittedLatticeSet n)
      (distinguishedLatticeTerm F T z z')).symm

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

theorem hasSum_distinguishedLatticeRemainder_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (z z' : ℂ) (n : ℕ) :
    HasSum (distinguishedLatticeRemainder F T z z' n)
      ((∑' m : ℤ, Zeta23.Poisson.complexPoissonAliasTerm
          (fun u => (F.window T (F.distinguished T) u : ℂ))
          (F.period T (F.distinguished T)) T z z' m) -
        ∑ k : Fin n, distinguishedLatticeTerm F T z z' (k : ℕ)) := by
  obtain ⟨_, hfull⟩ :=
    hasSum_distinguishedLatticeTerm_alias_of_hasCompactSupport
      F T hL hwindow hcompact z z'
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

/-- Compact-support form of the scalar kernel identity. -/
theorem blockPairKernel_eq_aliasSum_sub_remainder_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (haddress : Function.Bijective (F.columnAddress T))
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (hexhaustive : ∀ i,
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (hL : 0 < F.period T (F.distinguished T))
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
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
  have hrem :=
    hasSum_distinguishedLatticeRemainder_of_hasCompactSupport
      F T hL hwindow hcompact (gammaOf ρ) (gammaOf ρ')
        (F.channelDim T (F.distinguished T))
  rw [hrem.tsum_eq]
  ring

/-- The Poisson-completed value of one pair kernel: all spatial aliases,
with precisely the negative and upper-tail integer frequencies absent from
the finite block removed. -/
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
      ∑' k : omittedLatticeSet
          (F.channelDim T (F.distinguished T)),
        distinguishedLatticeTerm F T (gammaOf ρ) (gammaOf ρ') k)

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
  rw [← tsum_distinguishedLatticeRemainder_eq_omitted]
  exact blockPairKernel_eq_aliasSum_sub_remainder
    F T Λ haddress hcolumns hexhaustive hL hΛ hwindow hsupport ρ ρ'

theorem blockPairKernel_eq_poissonAliasCompletedPair_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (haddress : Function.Bijective (F.columnAddress T))
    (hcolumns : ∀ i,
      (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T)
    (hexhaustive : ∀ i,
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (hL : 0 < F.period T (F.distinguished T))
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (ρ ρ' : ℂ) :
    blockPairKernel F T ρ ρ' = poissonAliasCompletedPair F T ρ ρ' := by
  unfold poissonAliasCompletedPair
  rw [← tsum_distinguishedLatticeRemainder_eq_omitted]
  exact blockPairKernel_eq_aliasSum_sub_remainder_of_hasCompactSupport
    F T haddress hcolumns hexhaustive hL hwindow hcompact ρ ρ'

/-! ## Eventual construction interface -/

/-- The minimal physical data needed to evaluate every distinguished pair
kernel by complex Poisson summation.  Unlike `PrincipalCyclicBlock`, this
interface contains no channel-allocation or energy-ratio clauses. -/
structure DistinguishedPoissonKernelData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  periods_pos : ∀ᶠ T in atTop, ∀ j, 0 < F.period T j
  column_address_bijective : ∀ᶠ T in atTop,
    Function.Bijective (F.columnAddress T)
  windows_smooth : ∀ᶠ T in atTop, ∀ j, ContDiff ℝ ∞ (F.window T j)
  windows_compact : ∀ᶠ T in atTop, ∀ j, HasCompactSupport (F.window T j)
  distinguished_columns : ∀ᶠ T in atTop, ∀ i,
    (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T
  distinguished_exhaustive : ∀ᶠ T in atTop, ∀ i,
    (F.columnAddress T i).1 = F.distinguished T →
      ∃ b, F.blockEmbedding T b = i

/-- The older physical-window bundle contains the minimal Poisson-kernel
data as a literal sub-interface. -/
theorem PrincipalCyclicBlock.toDistinguishedPoissonKernelData
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : PrincipalCyclicBlock F) : DistinguishedPoissonKernelData F where
  periods_pos := h.periods_pos
  column_address_bijective := h.column_address_bijective
  windows_smooth := h.windows_smooth
  windows_compact := h.windows_compact
  distinguished_columns := h.distinguished_columns
  distinguished_exhaustive := h.distinguished_exhaustive

private theorem complexWindow_contDiff_two
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (h : ContDiff ℝ ∞ (F.window T (F.distinguished T))) :
    ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)) := by
  change ContDiff ℝ 2
    (Complex.ofRealCLM ∘ F.window T (F.distinguished T))
  exact (Complex.ofRealCLM.contDiff.comp h).of_le (by
    exact (WithTop.coe_le_coe).2 (show (2 : ℕ∞) ≤ ⊤ from le_top))

private theorem complexWindow_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (h : HasCompactSupport (F.window T (F.distinguished T))) :
    HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)) := by
  apply h.mono
  intro u hu
  simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hu

/-- The minimal construction data simultaneously evaluates every complex
zero pair for all sufficiently large heights. -/
theorem DistinguishedPoissonKernelData.eventually_blockPairKernel_eq
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : DistinguishedPoissonKernelData F) :
    ∀ᶠ T in atTop, ∀ ρ ρ' : ℂ,
      blockPairKernel F T ρ ρ' = poissonAliasCompletedPair F T ρ ρ' := by
  filter_upwards [h.periods_pos, h.column_address_bijective,
    h.windows_smooth, h.windows_compact, h.distinguished_columns,
    h.distinguished_exhaustive] with T hperiod haddress hsmooth hcompact
      hcolumns hexhaustive
  intro ρ ρ'
  exact blockPairKernel_eq_poissonAliasCompletedPair_of_hasCompactSupport
    F T haddress hcolumns hexhaustive (hperiod (F.distinguished T))
      (complexWindow_contDiff_two F T (hsmooth (F.distinguished T)))
      (complexWindow_hasCompactSupport F T (hcompact (F.distinguished T)))
      ρ ρ'

end RH.Zeta85.PoissonKernelBridge

end
