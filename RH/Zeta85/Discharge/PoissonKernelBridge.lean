import RH.Zeta85.Inputs95
import Zeta23.Poisson.ComplexAlias
import Zeta23.Tail.Grid

open Filter Matrix MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff

noncomputable section

namespace RH.Zeta85.PoissonKernelBridge

open Zeta23 RHLinalg

/-- Spacing of the distinguished modulation lattice. -/
def distinguishedGridStep
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  2 * Real.pi / F.period T (F.distinguished T)

/-- Canonical strip width covering both the `sqrt T` overhang of `ZIprime`
and a further `sqrt T` decay buffer, with two extra grid points for the
floor/ceiling endpoints. -/
def distinguishedEndpointGuardWidth
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℕ :=
  Zeta23.Tail.endpointGuardWidth (2 * Zeta23.D0 T)
    (distinguishedGridStep F T)

/-- Every zero in the actual enlarged window lies between the two guarded
remote tails, each at least `sqrt T` away.  All closer labels are precisely
the two finite boundary strips. -/
theorem mem_ZIprime_guarded_distances
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (n : ℕ)
    (hL : 0 < F.period T (F.distinguished T))
    (hn : n = ⌊T / distinguishedGridStep F T⌋₊)
    {ρ : ℂ} (hρ : ρ ∈ Z.ZIprime T) :
    T - (distinguishedEndpointGuardWidth F T + 1) *
        distinguishedGridStep F T + Zeta23.D0 T ≤
          (gammaOf ρ).re ∧
      (gammaOf ρ).re + Zeta23.D0 T ≤
        T + (n + distinguishedEndpointGuardWidth F T) *
          distinguishedGridStep F T := by
  have hh : 0 < distinguishedGridStep F T := by
    unfold distinguishedGridStep
    positivity
  have hmem := (Zeta23.ZeroSide.mem_ZIprime_iff Z T).1 hρ
  have hgamma : (gammaOf ρ).re = ρ.im := by
    simp [gammaOf, Complex.div_I]
  have hlower := Zeta23.Tail.lower_endpointGuard_distance
    (T := T) (D := 2 * Zeta23.D0 T)
    (h := distinguishedGridStep F T) hh
  have hupper := Zeta23.Tail.upper_endpointGuard_distance
    (T := T) (D := 2 * Zeta23.D0 T)
    (h := distinguishedGridStep F T) hh
  change
    T - (Zeta23.Tail.endpointGuardWidth (2 * Zeta23.D0 T)
        (distinguishedGridStep F T) + 1) * distinguishedGridStep F T +
          Zeta23.D0 T ≤ (gammaOf ρ).re ∧
      (gammaOf ρ).re + Zeta23.D0 T ≤
        T + (n + Zeta23.Tail.endpointGuardWidth (2 * Zeta23.D0 T)
          (distinguishedGridStep F T)) * distinguishedGridStep F T
  constructor
  · rw [hgamma]
    have hD0 : 0 ≤ Zeta23.D0 T := Real.sqrt_nonneg T
    nlinarith [hmem.2.1]
  · rw [hgamma, hn]
    push_cast
    calc
      ρ.im + Zeta23.D0 T ≤
          2 * T + 2 * Zeta23.D0 T := by linarith [hmem.2.2]
      _ ≤ 2 * T + 2 * Zeta23.D0 T + distinguishedGridStep F T := by
        linarith
      _ ≤ T +
          ((⌊T / distinguishedGridStep F T⌋₊ : ℝ) +
            (Zeta23.Tail.endpointGuardWidth (2 * Zeta23.D0 T)
              (distinguishedGridStep F T) : ℝ)) *
            distinguishedGridStep F T := by
        simpa only [add_assoc] using hupper

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

/-- The full distinguished lattice carries a uniform fourth-order
horizontal majorant: both Fourier factors retain their quadratic decay. -/
theorem distinguishedLatticeTerm_horizontal_decay_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (z z' : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ,
      ‖distinguishedLatticeTerm F T z z' k‖ *
          ((1 + (z.re -
            (T + (k : ℝ) *
              (2 * Real.pi / F.period T (F.distinguished T)))) ^ 2) *
           (1 + (z'.re -
            (T + (k : ℝ) *
              (2 * Real.pi / F.period T (F.distinguished T)))) ^ 2)) ≤ C := by
  obtain ⟨C, hC0, hC⟩ :=
    Zeta23.Poisson.paperFT_mul_horizontal_decay_of_hasCompactSupport
      hwindow hcompact z z'
  refine ⟨C, hC0, ?_⟩
  intro k
  simpa only [distinguishedLatticeTerm] using
    hC (T + (k : ℝ) *
      (2 * Real.pi / F.period T (F.distinguished T)))

private theorem norm_le_mul_inv_pow_four_of_weighted_decay
    {r a b x C : ℝ} (hr : 0 ≤ r) (hx : 0 < x)
    (hdecay : r * ((1 + a ^ 2) * (1 + b ^ 2)) ≤ C)
    (ha : x ≤ |a|) (hb : x ≤ |b|) :
    r ≤ C * (x ^ 4)⁻¹ := by
  have hxa : x ^ 2 ≤ a ^ 2 := (sq_le_sq).2 (by
    simpa [abs_of_pos hx] using ha)
  have hxb : x ^ 2 ≤ b ^ 2 := (sq_le_sq).2 (by
    simpa [abs_of_pos hx] using hb)
  have hweight : x ^ 4 ≤ (1 + a ^ 2) * (1 + b ^ 2) := by
    calc
      x ^ 4 = x ^ 2 * x ^ 2 := by ring
      _ ≤ (1 + a ^ 2) * (1 + b ^ 2) :=
        mul_le_mul (hxa.trans (le_add_of_nonneg_left (by norm_num)))
          (hxb.trans (le_add_of_nonneg_left (by norm_num)))
          (sq_nonneg _) (by positivity)
  have hrx : r * x ^ 4 ≤ C :=
    (mul_le_mul_of_nonneg_left hweight hr).trans hdecay
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hx 4)).2 hrx

/-- If a pair of complex frequencies lies a positive distance to the right
of the last negative lattice frequency, the entire negative half-lattice
has an explicit fourth-power norm bound. -/
theorem exists_negativeLatticeTail_bound_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T D : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hD : 0 < D)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (z z' : ℂ)
    (hz : T - 2 * Real.pi / F.period T (F.distinguished T) + D ≤ z.re)
    (hz' : T - 2 * Real.pi / F.period T (F.distinguished T) + D ≤ z'.re) :
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun m : ℕ =>
        distinguishedLatticeTerm F T z z' (-((m : ℤ) + 1))) ∧
      ‖∑' m : ℕ,
        distinguishedLatticeTerm F T z z' (-((m : ℤ) + 1))‖ ≤
        C * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ /
          (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
  obtain ⟨C, hC0, hdecay⟩ :=
    distinguishedLatticeTerm_horizontal_decay_of_hasCompactSupport
      F T hwindow hcompact z z'
  let h : ℝ := 2 * Real.pi / F.period T (F.distinguished T)
  have hh : 0 < h := by
    dsimp only [h]
    positivity
  have hz_h : T - h + D ≤ z.re := by simpa only [h] using hz
  have hz'_h : T - h + D ≤ z'.re := by simpa only [h] using hz'
  have hmajor : ∀ m : ℕ,
      ‖distinguishedLatticeTerm F T z z' (-((m : ℤ) + 1))‖ ≤
        C * ((D + m * h) ^ 4)⁻¹ := by
    intro m
    have hx : 0 < D + m * h := by positivity
    have hfreq :
        T + ((-((m : ℤ) + 1) : ℤ) : ℝ) * h = T - h - m * h := by
      push_cast
      ring
    have ha : D + m * h ≤
        |z.re - (T + ((-((m : ℤ) + 1) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonneg]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    have hb : D + m * h ≤
        |z'.re - (T + ((-((m : ℤ) + 1) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonneg]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    apply norm_le_mul_inv_pow_four_of_weighted_decay
      (norm_nonneg _) hx _ ha hb
    simpa only [h] using hdecay (-((m : ℤ) + 1))
  obtain ⟨hsum, hnorm⟩ :=
    Zeta23.Tail.summable_and_norm_tsum_le_inv_pow_four_grid
      hC0 hD hh hmajor
  refine ⟨C, hC0, hsum, ?_⟩
  simpa only [h] using hnorm

/-- Lower-tail estimate after peeling `r` endpoint labels.  This is the
form needed for the enlarged zero window, whose lower edge extends below
the first retained frequency. -/
theorem exists_lowerLatticeTailFrom_bound_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T D : ℝ) (r : ℕ)
    (hL : 0 < F.period T (F.distinguished T))
    (hD : 0 < D)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (z z' : ℂ)
    (hz : T - (r + 1) *
      (2 * Real.pi / F.period T (F.distinguished T)) + D ≤ z.re)
    (hz' : T - (r + 1) *
      (2 * Real.pi / F.period T (F.distinguished T)) + D ≤ z'.re) :
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun m : ℕ =>
        distinguishedLatticeTerm F T z z'
          (-(((r + m : ℕ) : ℤ) + 1))) ∧
      ‖∑' m : ℕ,
        distinguishedLatticeTerm F T z z'
          (-(((r + m : ℕ) : ℤ) + 1))‖ ≤
        C * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ /
          (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
  obtain ⟨C, hC0, hdecay⟩ :=
    distinguishedLatticeTerm_horizontal_decay_of_hasCompactSupport
      F T hwindow hcompact z z'
  let h : ℝ := 2 * Real.pi / F.period T (F.distinguished T)
  have hh : 0 < h := by
    dsimp only [h]
    positivity
  have hz_h : T - (r + 1) * h + D ≤ z.re := by
    simpa only [h] using hz
  have hz'_h : T - (r + 1) * h + D ≤ z'.re := by
    simpa only [h] using hz'
  have hmajor : ∀ m : ℕ,
      ‖distinguishedLatticeTerm F T z z'
          (-(((r + m : ℕ) : ℤ) + 1))‖ ≤
        C * ((D + m * h) ^ 4)⁻¹ := by
    intro m
    have hx : 0 < D + m * h := by positivity
    have hfreq :
        T + ((-(((r + m : ℕ) : ℤ) + 1) : ℤ) : ℝ) * h =
          T - (r + 1) * h - m * h := by
      push_cast
      ring
    have ha : D + m * h ≤
        |z.re - (T +
          ((-(((r + m : ℕ) : ℤ) + 1) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonneg]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    have hb : D + m * h ≤
        |z'.re - (T +
          ((-(((r + m : ℕ) : ℤ) + 1) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonneg]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    apply norm_le_mul_inv_pow_four_of_weighted_decay
      (norm_nonneg _) hx _ ha hb
    simpa only [h] using hdecay (-(((r + m : ℕ) : ℤ) + 1))
  obtain ⟨hsum, hnorm⟩ :=
    Zeta23.Tail.summable_and_norm_tsum_le_inv_pow_four_grid
      hC0 hD hh hmajor
  refine ⟨C, hC0, hsum, ?_⟩
  simpa only [h] using hnorm

/-- The matching estimate on any upper half-lattice.  The starting label is
explicit, allowing finitely many endpoint labels to be peeled off before
the fourth-order estimate is applied. -/
theorem exists_upperLatticeTail_bound_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T D : ℝ) (n : ℕ)
    (hL : 0 < F.period T (F.distinguished T))
    (hD : 0 < D)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (z z' : ℂ)
    (hz : z.re + D ≤ T + n *
      (2 * Real.pi / F.period T (F.distinguished T)))
    (hz' : z'.re + D ≤ T + n *
      (2 * Real.pi / F.period T (F.distinguished T))) :
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun m : ℕ =>
        distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ)) ∧
      ‖∑' m : ℕ,
        distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ)‖ ≤
        C * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ /
          (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
  obtain ⟨C, hC0, hdecay⟩ :=
    distinguishedLatticeTerm_horizontal_decay_of_hasCompactSupport
      F T hwindow hcompact z z'
  let h : ℝ := 2 * Real.pi / F.period T (F.distinguished T)
  have hh : 0 < h := by
    dsimp only [h]
    positivity
  have hz_h : z.re + D ≤ T + n * h := by simpa only [h] using hz
  have hz'_h : z'.re + D ≤ T + n * h := by simpa only [h] using hz'
  have hmajor : ∀ m : ℕ,
      ‖distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ)‖ ≤
        C * ((D + m * h) ^ 4)⁻¹ := by
    intro m
    have hx : 0 < D + m * h := by positivity
    have hfreq :
        T + (((n + m : ℕ) : ℤ) : ℝ) * h = T + n * h + m * h := by
      push_cast
      ring
    have ha : D + m * h ≤
        |z.re - (T + (((n + m : ℕ) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonpos]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    have hb : D + m * h ≤
        |z'.re - (T + (((n + m : ℕ) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonpos]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    apply norm_le_mul_inv_pow_four_of_weighted_decay
      (norm_nonneg _) hx _ ha hb
    simpa only [h] using hdecay ((n + m : ℕ) : ℤ)
  obtain ⟨hsum, hnorm⟩ :=
    Zeta23.Tail.summable_and_norm_tsum_le_inv_pow_four_grid
      hC0 hD hh hmajor
  refine ⟨C, hC0, hsum, ?_⟩
  simpa only [h] using hnorm

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

/-- The first `r` omitted labels below the retained grid. -/
def lowerLatticeBoundaryStrip
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (r : ℕ) : ℂ :=
  ∑ m ∈ Finset.range r,
    distinguishedLatticeTerm F T z z' (-((m : ℤ) + 1))

/-- The first `r` omitted labels at and above the upper endpoint `n`. -/
def upperLatticeBoundaryStrip
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n r : ℕ) : ℂ :=
  ∑ m ∈ Finset.range r,
    distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ)

/-- The two endpoint strips selected canonically for the enlarged zero
window.  They are combined before any absolute-value estimate. -/
def canonicalLatticeBoundaryStrip
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ) : ℂ :=
  let r := distinguishedEndpointGuardWidth F T
  lowerLatticeBoundaryStrip F T z z' r +
    upperLatticeBoundaryStrip F T z z' n r

/-- One distinguished-lattice Fourier feature on an actual enlarged-window
zero. -/
def distinguishedLatticeFeature
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (k : ℤ)
    (ρ : ↥(Zeta23.ZeroSide.ZI Z T)) : ℂ :=
  paperFT (fun u => (F.window T (F.distinguished T) u : ℂ))
    (gammaOf (ρ : ℂ) -
      (T + (k : ℝ) * distinguishedGridStep F T : ℝ))

/-- Lower finite boundary strip as a matrix on the actual finite zero set. -/
def lowerLatticeBoundaryKernelMatrix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (r : ℕ) :
    Matrix (↥(Zeta23.ZeroSide.ZI Z T))
      (↥(Zeta23.ZeroSide.ZI Z T)) ℂ :=
  ∑ m ∈ Finset.range r,
    vecMulVec
      (distinguishedLatticeFeature F T (-((m : ℤ) + 1)))
      (distinguishedLatticeFeature F T (-((m : ℤ) + 1)))

/-- Upper finite boundary strip as a matrix on the actual finite zero set. -/
def upperLatticeBoundaryKernelMatrix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (n r : ℕ) :
    Matrix (↥(Zeta23.ZeroSide.ZI Z T))
      (↥(Zeta23.ZeroSide.ZI Z T)) ℂ :=
  ∑ m ∈ Finset.range r,
    vecMulVec
      (distinguishedLatticeFeature F T ((n + m : ℕ) : ℤ))
      (distinguishedLatticeFeature F T ((n + m : ℕ) : ℤ))

/-- Combined canonical endpoint strip matrix. -/
def canonicalLatticeBoundaryKernelMatrix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (n : ℕ) :
    Matrix (↥(Zeta23.ZeroSide.ZI Z T))
      (↥(Zeta23.ZeroSide.ZI Z T)) ℂ :=
  let r := distinguishedEndpointGuardWidth F T
  lowerLatticeBoundaryKernelMatrix F T r +
    upperLatticeBoundaryKernelMatrix F T n r

/-- The zero-space boundary matrix has the canonical boundary strip as its
literal `(ρ,ρ')` entry. -/
theorem canonicalLatticeBoundaryKernelMatrix_apply
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (n : ℕ)
    (ρ ρ' : ↥(Zeta23.ZeroSide.ZI Z T)) :
    canonicalLatticeBoundaryKernelMatrix F T n ρ ρ' =
      canonicalLatticeBoundaryStrip F T
        (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) n := by
  simp only [canonicalLatticeBoundaryKernelMatrix,
    canonicalLatticeBoundaryStrip, lowerLatticeBoundaryKernelMatrix,
    upperLatticeBoundaryKernelMatrix, lowerLatticeBoundaryStrip,
    upperLatticeBoundaryStrip, Matrix.sum_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply,
    distinguishedLatticeFeature, distinguishedLatticeTerm,
    distinguishedGridStep]

/-- The lower endpoint strip has rank at most its number of labels. -/
theorem lowerLatticeBoundaryKernelMatrix_rank_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (r : ℕ) :
    (lowerLatticeBoundaryKernelMatrix F T r).rank ≤ r := by
  unfold lowerLatticeBoundaryKernelMatrix
  refine (Zeta23.ZeroSide.rank_sum_le (Finset.range r) _ (fun _ => 1) ?_).trans ?_
  · intro m hm
    exact rank_vecMulVec_le _ _
  · simp

/-- The upper endpoint strip has rank at most its number of labels. -/
theorem upperLatticeBoundaryKernelMatrix_rank_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (n r : ℕ) :
    (upperLatticeBoundaryKernelMatrix F T n r).rank ≤ r := by
  unfold upperLatticeBoundaryKernelMatrix
  refine (Zeta23.ZeroSide.rank_sum_le (Finset.range r) _ (fun _ => 1) ?_).trans ?_
  · intro m hm
    exact rank_vecMulVec_le _ _
  · simp

/-- The entire non-decaying Poisson boundary is a rank-`2r` object.  This is
the algebraic reason it can be charged as a vanishing-density endpoint
strip instead of estimated pair by pair. -/
theorem canonicalLatticeBoundaryKernelMatrix_rank_le
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (n : ℕ) :
    (canonicalLatticeBoundaryKernelMatrix F T n).rank ≤
      2 * distinguishedEndpointGuardWidth F T := by
  unfold canonicalLatticeBoundaryKernelMatrix
  exact (Zeta23.ZeroSide.rank_add_le _ _).trans (by
    have hlo := lowerLatticeBoundaryKernelMatrix_rank_le F T
      (distinguishedEndpointGuardWidth F T)
    have hup := upperLatticeBoundaryKernelMatrix_rank_le F T n
      (distinguishedEndpointGuardWidth F T)
    omega)

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

/-- The omitted remainder is exactly two one-sided natural-number tails:
the negative lattice and the lattice beginning at the first excluded
nonnegative label.  This is the form consumed by one-sided grid bounds. -/
theorem tsum_distinguishedLatticeRemainder_eq_two_tails
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n : ℕ)
    (hsum : Summable (distinguishedLatticeTerm F T z z')) :
    (∑' k : ℤ, distinguishedLatticeRemainder F T z z' n k) =
      (∑' m : ℕ, distinguishedLatticeTerm F T z z'
        (-((m : ℤ) + 1))) +
      ∑' m : ℕ, distinguishedLatticeTerm F T z z'
        ((n + m : ℕ) : ℤ) := by
  have hsegment :=
    (hasSum_distinguishedLatticeSegmentExtension F T z z' n).summable
  have hrem : Summable (distinguishedLatticeRemainder F T z z' n) := by
    exact hsum.sub hsegment
  have hnat : Summable (fun m : ℕ =>
      distinguishedLatticeRemainder F T z z' n (m : ℤ)) :=
    hrem.comp_injective Int.ofNat_injective
  have hneg : Summable (fun m : ℕ =>
      distinguishedLatticeRemainder F T z z' n (-((m : ℤ) + 1))) :=
    hrem.comp_injective (by
      intro a b hab
      have : Int.negSucc a = Int.negSucc b := by simpa using hab
      exact Int.negSucc.inj this)
  have hprefix :
      (∑ m ∈ Finset.range n,
        distinguishedLatticeRemainder F T z z' n (m : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hm_lt : m < n := Finset.mem_range.mp hm
    let i : Fin n := ⟨m, hm_lt⟩
    change distinguishedLatticeRemainder F T z z' n
      (finiteLabelEmbedding n i) = 0
    exact distinguishedLatticeRemainder_inside F T z z' n i
  have hshift := hnat.sum_add_tsum_nat_add n
  rw [hprefix, zero_add] at hshift
  have hneg_eq : (fun m : ℕ =>
      distinguishedLatticeRemainder F T z z' n (-((m : ℤ) + 1))) =
      fun m : ℕ => distinguishedLatticeTerm F T z z' (-((m : ℤ) + 1)) := by
    funext m
    exact distinguishedLatticeRemainder_outside F T z z' n _ (Or.inl (by omega))
  have hupper :
      (∑' m : ℕ, distinguishedLatticeRemainder F T z z' n (m : ℤ)) =
        ∑' m : ℕ, distinguishedLatticeTerm F T z z'
          ((n + m : ℕ) : ℤ) := by
    calc
      (∑' m : ℕ, distinguishedLatticeRemainder F T z z' n (m : ℤ)) =
          ∑' m : ℕ, distinguishedLatticeRemainder F T z z' n
            ((m + n : ℕ) : ℤ) := hshift.symm
      _ = ∑' m : ℕ, distinguishedLatticeTerm F T z z'
            ((n + m : ℕ) : ℤ) := by
        apply tsum_congr
        intro m
        rw [distinguishedLatticeRemainder_outside F T z z' n]
        · congr 2
          omega
        · right
          push_cast
          omega
  calc
    (∑' k : ℤ, distinguishedLatticeRemainder F T z z' n k) =
        (∑' m : ℕ, distinguishedLatticeRemainder F T z z' n (m : ℤ)) +
          ∑' m : ℕ, distinguishedLatticeRemainder F T z z' n
            (-((m : ℤ) + 1)) := tsum_of_nat_of_neg_add_one hnat hneg
    _ = (∑' m : ℕ, distinguishedLatticeTerm F T z z'
          ((n + m : ℕ) : ℤ)) +
        ∑' m : ℕ, distinguishedLatticeTerm F T z z'
          (-((m : ℤ) + 1)) := by rw [hupper, hneg_eq]
    _ = _ := add_comm _ _

/-- Peel an arbitrary finite endpoint strip from the upper omitted tail.
Everything beyond that strip is again a clean one-sided lattice, while the
strip stays as a literal finite sum ready to be combined across zero
variables before estimation. -/
theorem tsum_distinguishedLatticeRemainder_eq_guarded_tails
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n r : ℕ)
    (hsum : Summable (distinguishedLatticeTerm F T z z')) :
    (∑' k : ℤ, distinguishedLatticeRemainder F T z z' n k) =
      (∑' m : ℕ, distinguishedLatticeTerm F T z z'
        (-((m : ℤ) + 1))) +
      (∑ m ∈ Finset.range r,
        distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ)) +
      ∑' m : ℕ, distinguishedLatticeTerm F T z z'
        ((n + r + m : ℕ) : ℤ) := by
  rw [tsum_distinguishedLatticeRemainder_eq_two_tails F T z z' n hsum]
  have hupper : Summable (fun m : ℕ =>
      distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ)) :=
    hsum.comp_injective (by
      intro a b hab
      exact Nat.add_left_cancel (Int.ofNat_inj.mp hab))
  have hsplit := hupper.sum_add_tsum_nat_add r
  calc
    (∑' m : ℕ, distinguishedLatticeTerm F T z z'
          (-((m : ℤ) + 1))) +
        ∑' m : ℕ, distinguishedLatticeTerm F T z z'
          ((n + m : ℕ) : ℤ) =
      (∑' m : ℕ, distinguishedLatticeTerm F T z z'
          (-((m : ℤ) + 1))) +
        ((∑ m ∈ Finset.range r,
          distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ)) +
        ∑' m : ℕ, distinguishedLatticeTerm F T z z'
          ((n + r + m : ℕ) : ℤ)) := by
        congr 1
        rw [← hsplit]
        congr 1
        apply tsum_congr
        intro m
        congr 2
        omega
    _ = _ := by ring

/-- Peel finite strips from both endpoints of the omitted lattice.  The two
finite strips are grouped together before either remote infinite tail,
which is the sum-first arrangement used by the enlarged-window argument. -/
theorem tsum_distinguishedLatticeRemainder_eq_two_guarded_tails
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (z z' : ℂ) (n rneg rpos : ℕ)
    (hsum : Summable (distinguishedLatticeTerm F T z z')) :
    (∑' k : ℤ, distinguishedLatticeRemainder F T z z' n k) =
      ((∑ m ∈ Finset.range rneg,
          distinguishedLatticeTerm F T z z' (-((m : ℤ) + 1))) +
        ∑ m ∈ Finset.range rpos,
          distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ)) +
      (∑' m : ℕ, distinguishedLatticeTerm F T z z'
        (-(((rneg + m : ℕ) : ℤ) + 1))) +
      ∑' m : ℕ, distinguishedLatticeTerm F T z z'
        ((n + rpos + m : ℕ) : ℤ) := by
  rw [tsum_distinguishedLatticeRemainder_eq_guarded_tails
    F T z z' n rpos hsum]
  have hneg : Summable (fun m : ℕ =>
      distinguishedLatticeTerm F T z z' (-((m : ℤ) + 1))) :=
    hsum.comp_injective (by
      intro a b hab
      have : Int.negSucc a = Int.negSucc b := by simpa using hab
      exact Int.negSucc.inj this)
  have hsplit := hneg.sum_add_tsum_nat_add rneg
  have hremote :
      (∑' m : ℕ, distinguishedLatticeTerm F T z z'
        (-(((m + rneg : ℕ) : ℤ) + 1))) =
      ∑' m : ℕ, distinguishedLatticeTerm F T z z'
        (-(((rneg + m : ℕ) : ℤ) + 1)) := by
    apply tsum_congr
    intro m
    congr 3
    omega
  rw [hremote] at hsplit
  rw [← hsplit]
  ring

/-- Quantitative guarded-remainder theorem.  After a finite upper endpoint
strip is left untouched, both infinite pieces are absolutely summable and
bounded by explicit fourth-power grid tails.  The remaining finite strip is
the sole object that must be summed with the zero variables before applying
the analytic input. -/
theorem exists_guardedLatticeRemainder_bound_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T Dneg Dpos : ℝ) (n r : ℕ)
    (hL : 0 < F.period T (F.distinguished T))
    (hDneg : 0 < Dneg) (hDpos : 0 < Dpos)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (z z' : ℂ)
    (hzneg : T - 2 * Real.pi / F.period T (F.distinguished T) + Dneg ≤ z.re)
    (hz'neg : T - 2 * Real.pi / F.period T (F.distinguished T) + Dneg ≤ z'.re)
    (hzpos : z.re + Dpos ≤ T + (n + r) *
      (2 * Real.pi / F.period T (F.distinguished T)))
    (hz'pos : z'.re + Dpos ≤ T + (n + r) *
      (2 * Real.pi / F.period T (F.distinguished T))) :
    ∃ Cneg Cpos : ℝ, 0 ≤ Cneg ∧ 0 ≤ Cpos ∧
      ‖∑' k : ℤ, distinguishedLatticeRemainder F T z z' n k‖ ≤
        ‖∑ m ∈ Finset.range r,
          distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ)‖ +
        Cneg * ((Dneg ^ 4)⁻¹ + (Dneg ^ 3)⁻¹ /
          (3 * (2 * Real.pi / F.period T (F.distinguished T)))) +
        Cpos * ((Dpos ^ 4)⁻¹ + (Dpos ^ 3)⁻¹ /
          (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
  obtain ⟨Cneg, hCneg, hnegsum, hnegbound⟩ :=
    exists_negativeLatticeTail_bound_of_hasCompactSupport
      F T Dneg hL hDneg hwindow hcompact z z' hzneg hz'neg
  have hzpos_cast : z.re + Dpos ≤ T + ((n + r : ℕ) : ℝ) *
      (2 * Real.pi / F.period T (F.distinguished T)) := by
    simpa only [Nat.cast_add] using hzpos
  have hz'pos_cast : z'.re + Dpos ≤ T + ((n + r : ℕ) : ℝ) *
      (2 * Real.pi / F.period T (F.distinguished T)) := by
    simpa only [Nat.cast_add] using hz'pos
  obtain ⟨Cpos, hCpos, hpossum, hposbound⟩ :=
    exists_upperLatticeTail_bound_of_hasCompactSupport
      F T Dpos (n + r) hL hDpos hwindow hcompact z z'
        hzpos_cast hz'pos_cast
  have hfull : Summable (distinguishedLatticeTerm F T z z') :=
    (hasSum_distinguishedLatticeTerm_alias_of_hasCompactSupport
      F T hL hwindow hcompact z z').2.summable
  refine ⟨Cneg, Cpos, hCneg, hCpos, ?_⟩
  rw [tsum_distinguishedLatticeRemainder_eq_guarded_tails
    F T z z' n r hfull]
  have htri := norm_add_le
    ((∑' m : ℕ, distinguishedLatticeTerm F T z z'
        (-((m : ℤ) + 1))) +
      ∑ m ∈ Finset.range r,
        distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ))
    (∑' m : ℕ, distinguishedLatticeTerm F T z z'
      ((n + r + m : ℕ) : ℤ))
  have htri' := norm_add_le
    (∑' m : ℕ, distinguishedLatticeTerm F T z z'
      (-((m : ℤ) + 1)))
    (∑ m ∈ Finset.range r,
      distinguishedLatticeTerm F T z z' ((n + m : ℕ) : ℤ))
  nlinarith

/-- Fully guarded quantitative remainder bound.  For an enlarged zero
window, choose the two strip widths to cover its lower and upper overhangs;
then only their combined finite sum remains, while both remote tails carry
explicit fourth-power bounds. -/
theorem exists_twoGuardedLatticeRemainder_bound_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T Dneg Dpos : ℝ)
    (n rneg rpos : ℕ)
    (hL : 0 < F.period T (F.distinguished T))
    (hDneg : 0 < Dneg) (hDpos : 0 < Dpos)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (z z' : ℂ)
    (hzneg : T - (rneg + 1) *
      (2 * Real.pi / F.period T (F.distinguished T)) + Dneg ≤ z.re)
    (hz'neg : T - (rneg + 1) *
      (2 * Real.pi / F.period T (F.distinguished T)) + Dneg ≤ z'.re)
    (hzpos : z.re + Dpos ≤ T + (n + rpos) *
      (2 * Real.pi / F.period T (F.distinguished T)))
    (hz'pos : z'.re + Dpos ≤ T + (n + rpos) *
      (2 * Real.pi / F.period T (F.distinguished T))) :
    ∃ Cneg Cpos : ℝ, 0 ≤ Cneg ∧ 0 ≤ Cpos ∧
      ‖∑' k : ℤ, distinguishedLatticeRemainder F T z z' n k‖ ≤
        ‖lowerLatticeBoundaryStrip F T z z' rneg +
          upperLatticeBoundaryStrip F T z z' n rpos‖ +
        Cneg * ((Dneg ^ 4)⁻¹ + (Dneg ^ 3)⁻¹ /
          (3 * (2 * Real.pi / F.period T (F.distinguished T)))) +
        Cpos * ((Dpos ^ 4)⁻¹ + (Dpos ^ 3)⁻¹ /
          (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
  obtain ⟨Cneg, hCneg, hnegsum, hnegbound⟩ :=
    exists_lowerLatticeTailFrom_bound_of_hasCompactSupport
      F T Dneg rneg hL hDneg hwindow hcompact z z' hzneg hz'neg
  have hzpos_cast : z.re + Dpos ≤ T + ((n + rpos : ℕ) : ℝ) *
      (2 * Real.pi / F.period T (F.distinguished T)) := by
    simpa only [Nat.cast_add] using hzpos
  have hz'pos_cast : z'.re + Dpos ≤ T + ((n + rpos : ℕ) : ℝ) *
      (2 * Real.pi / F.period T (F.distinguished T)) := by
    simpa only [Nat.cast_add] using hz'pos
  obtain ⟨Cpos, hCpos, hpossum, hposbound⟩ :=
    exists_upperLatticeTail_bound_of_hasCompactSupport
      F T Dpos (n + rpos) hL hDpos hwindow hcompact z z'
        hzpos_cast hz'pos_cast
  have hfull : Summable (distinguishedLatticeTerm F T z z') :=
    (hasSum_distinguishedLatticeTerm_alias_of_hasCompactSupport
      F T hL hwindow hcompact z z').2.summable
  refine ⟨Cneg, Cpos, hCneg, hCpos, ?_⟩
  rw [tsum_distinguishedLatticeRemainder_eq_two_guarded_tails
    F T z z' n rneg rpos hfull]
  let edge : ℂ :=
    lowerLatticeBoundaryStrip F T z z' rneg +
      upperLatticeBoundaryStrip F T z z' n rpos
  let low : ℂ := ∑' m : ℕ, distinguishedLatticeTerm F T z z'
    (-(((rneg + m : ℕ) : ℤ) + 1))
  let high : ℂ := ∑' m : ℕ, distinguishedLatticeTerm F T z z'
    ((n + rpos + m : ℕ) : ℤ)
  change ‖edge + low + high‖ ≤
    ‖edge‖ +
      Cneg * ((Dneg ^ 4)⁻¹ + (Dneg ^ 3)⁻¹ /
        (3 * (2 * Real.pi / F.period T (F.distinguished T)))) +
      Cpos * ((Dpos ^ 4)⁻¹ + (Dpos ^ 3)⁻¹ /
        (3 * (2 * Real.pi / F.period T (F.distinguished T))))
  have htri := norm_add_le (edge + low) high
  have htri' := norm_add_le edge low
  nlinarith

/-- Canonical enlarged-window specialization.  For every pair of actual
`ZIprime` zeros, both remote Poisson tails start at distance `sqrt T`; the
only non-decaying contribution is the combined finite boundary strip. -/
theorem exists_ZIprime_canonicalRemainder_bound_of_hasCompactSupport
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) (n : ℕ)
    (hT : 0 < T)
    (hL : 0 < F.period T (F.distinguished T))
    (hn : n = ⌊T / distinguishedGridStep F T⌋₊)
    (hwindow : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (ρ ρ' : ℂ) (hρ : ρ ∈ Z.ZIprime T) (hρ' : ρ' ∈ Z.ZIprime T) :
    ∃ Cneg Cpos : ℝ, 0 ≤ Cneg ∧ 0 ≤ Cpos ∧
      ‖∑' k : ℤ, distinguishedLatticeRemainder F T
        (gammaOf ρ) (gammaOf ρ') n k‖ ≤
        ‖canonicalLatticeBoundaryStrip F T
          (gammaOf ρ) (gammaOf ρ') n‖ +
        Cneg * (((Zeta23.D0 T) ^ 4)⁻¹ +
          ((Zeta23.D0 T) ^ 3)⁻¹ / (3 * distinguishedGridStep F T)) +
        Cpos * (((Zeta23.D0 T) ^ 4)⁻¹ +
          ((Zeta23.D0 T) ^ 3)⁻¹ / (3 * distinguishedGridStep F T)) := by
  have hD0 : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT
  have hdist := mem_ZIprime_guarded_distances F T n hL hn hρ
  have hdist' := mem_ZIprime_guarded_distances F T n hL hn hρ'
  have hbound :=
    exists_twoGuardedLatticeRemainder_bound_of_hasCompactSupport
      F T (Zeta23.D0 T) (Zeta23.D0 T) n
        (distinguishedEndpointGuardWidth F T)
        (distinguishedEndpointGuardWidth F T)
        hL hD0 hD0 hwindow hcompact (gammaOf ρ) (gammaOf ρ')
        (by simpa only [distinguishedGridStep] using hdist.1)
        (by simpa only [distinguishedGridStep] using hdist'.1)
        (by simpa only [distinguishedGridStep] using hdist.2)
        (by simpa only [distinguishedGridStep] using hdist'.2)
  simpa only [canonicalLatticeBoundaryStrip, distinguishedGridStep] using hbound

/-- Under the distinguished-period law, the canonical endpoint-strip width
is `O(sqrt T * log(T/2π))`. -/
theorem distinguishedEndpointGuardWidth_isBigO
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 < μ)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = μ * Zeta23.l T) :
    (fun T => (distinguishedEndpointGuardWidth F T : ℝ)) =O[atTop]
      fun T => Real.sqrt T * Zeta23.l T := by
  refine IsBigO.of_bound (μ + 3) ?_
  filter_upwards [hperiod, Zeta23.Assembly.eventually_one_le_l,
    eventually_ge_atTop (1 : ℝ)] with T hperiodT hl hT
  have hT0 : 0 ≤ T := by linarith
  have hsqrt : 1 ≤ Real.sqrt T := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT
  have hbase : 1 ≤ Real.sqrt T * Zeta23.l T :=
    one_le_mul_of_one_le_of_one_le hsqrt hl
  have hden : 0 < μ * Zeta23.l T := mul_pos hμ (lt_of_lt_of_le zero_lt_one hl)
  let a : ℝ :=
    2 * Zeta23.D0 T /
      (2 * Real.pi / (μ * Zeta23.l T))
  have ha0 : 0 ≤ a := by
    dsimp only [a, Zeta23.D0]
    positivity
  have hceil := Nat.ceil_lt_add_one ha0
  have haeq : a = μ * Real.sqrt T * Zeta23.l T / Real.pi := by
    dsimp only [a, Zeta23.D0]
    field_simp
  have hnum : 0 ≤ μ * Real.sqrt T * Zeta23.l T := by positivity
  have hale : a ≤ μ * Real.sqrt T * Zeta23.l T := by
    rw [haeq, div_le_iff₀ Real.pi_pos]
    have hmul := mul_le_mul_of_nonneg_left Real.two_le_pi hnum
    nlinarith
  have hguard :
      (distinguishedEndpointGuardWidth F T : ℝ) ≤ a + 3 := by
    unfold distinguishedEndpointGuardWidth distinguishedGridStep
    rw [hperiodT]
    unfold Zeta23.Tail.endpointGuardWidth
    push_cast
    change (⌈a⌉₊ : ℝ) + 2 ≤ a + 3
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  calc
    (distinguishedEndpointGuardWidth F T : ℝ) ≤ a + 3 := hguard
    _ ≤ μ * (Real.sqrt T * Zeta23.l T) + 3 := by
      nlinarith [hale]
    _ ≤ (μ + 3) * (Real.sqrt T * Zeta23.l T) := by
      nlinarith

/-- Hence the rank budget of the combined endpoint matrix is negligible on
the dyadic zero-count scale. -/
theorem canonicalLatticeBoundaryKernelRank_isLittleO
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (hμ : 0 < μ) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = μ * Zeta23.l T) :
    (fun T => ((2 * distinguishedEndpointGuardWidth F T : ℕ) : ℝ)) =o[atTop]
      fun T => (Z.N T (2 * T) : ℝ) := by
  have hO :
      (fun T => ((2 * distinguishedEndpointGuardWidth F T : ℕ) : ℝ)) =O[atTop]
        fun T => Real.sqrt T * Zeta23.l T := by
    have hg := distinguishedEndpointGuardWidth_isBigO F hμ hperiod
    obtain ⟨c, hc⟩ := hg.bound
    refine IsBigO.of_bound (2 * c) ?_
    filter_upwards [hc] with T hT
    change ‖((2 * distinguishedEndpointGuardWidth F T : ℕ) : ℝ)‖ ≤
      (2 * c) * ‖Real.sqrt T * Zeta23.l T‖
    rw [Nat.cast_mul, Nat.cast_ofNat, norm_mul]
    have hnormTwo : ‖(2 : ℝ)‖ = 2 := by norm_num
    rw [hnormTwo]
    calc
      2 * ‖(distinguishedEndpointGuardWidth F T : ℝ)‖ ≤
          2 * (c * ‖Real.sqrt T * Zeta23.l T‖) :=
        mul_le_mul_of_nonneg_left hT (by norm_num)
      _ = (2 * c) * ‖Real.sqrt T * Zeta23.l T‖ := by ring
  exact hO.trans_isLittleO
    (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM
      Zeta23.Assembly.isLittleO_sqrt_mul_l_Tl)

/-- The rank of the actual zero-indexed endpoint matrix, for any choice of
the retained lattice length, has density tending to zero among the dyadic
zeros. -/
theorem canonicalLatticeBoundaryKernelMatrix_rank_isLittleO
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (n : ℝ → ℕ)
    (hμ : 0 < μ) (hRvM : RiemannVonMangoldt Z)
    (hperiod : ∀ᶠ T in atTop,
      F.period T (F.distinguished T) = μ * Zeta23.l T) :
    (fun T => ((canonicalLatticeBoundaryKernelMatrix F T (n T)).rank : ℝ))
        =o[atTop] fun T => (Z.N T (2 * T) : ℝ) := by
  have hO :
      (fun T => ((canonicalLatticeBoundaryKernelMatrix F T (n T)).rank : ℝ))
          =O[atTop]
        fun T => ((2 * distinguishedEndpointGuardWidth F T : ℕ) : ℝ) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun T => ?_)
    have hr := canonicalLatticeBoundaryKernelMatrix_rank_le F T (n T)
    have hr' :
        ((canonicalLatticeBoundaryKernelMatrix F T (n T)).rank : ℝ) ≤
          ((2 * distinguishedEndpointGuardWidth F T : ℕ) : ℝ) := by
      exact_mod_cast hr
    have hleft :
        0 ≤ ((canonicalLatticeBoundaryKernelMatrix F T (n T)).rank : ℝ) :=
      Nat.cast_nonneg _
    have hright :
        0 ≤ ((2 * distinguishedEndpointGuardWidth F T : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft,
      abs_of_nonneg hright, one_mul] using hr'
  exact hO.trans_isLittleO
    (canonicalLatticeBoundaryKernelRank_isLittleO F hμ hRvM hperiod)

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
