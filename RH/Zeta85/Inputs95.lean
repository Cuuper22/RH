/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
# Explicit analytic inputs for the quartic rungs

This module declares no Lean axioms and constructs no instance of `Inputs95`.
Its structures are only an explicit hypothesis boundary.  The same displayed
windows, atoms, truncated matrix, and principal block occur in every layer.

There are three deliberate separations.

* `PairTraceGrade95` does not imply `FullTraceLimits` here: the arithmetic
  trace evaluation is a separate bridge which still has to be proved.
* `RS1996ZetaInputs` does not imply `BlockMomentLimits` here: the off-RH
  complex Poisson passage, finite-grid estimates, and sharp-height removal
  are separate obligations.
* finite robust stability is a theorem, not a field.  It is applied to the
  enlarged-window truncation `A = P + Q`; the full matrix is `G = A + E`.

The two full profiles are type parameters.  Thus `Inputs95Data` contains the
literal proved B3 witnesses `v8686` and `v9506`, rather than an unrelated
function plus a proposition asserting equality later.
-/
import RH.Zeta85.Arith
import RH.Zeta85.Discharge.QuarticWindowWitnesses
import RH.Zeta85.Discharge.RobustStability
import RH.Zeta85.Discharge.TopHatMoments
import Zeta23.Assembly
import Zeta23.Hypotheses
import Zeta23.LinAlg
import Zeta23.ZeroSide

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder ContDiff Topology

noncomputable section

namespace RH
namespace Zeta85

open Zeta23 RHLinalg

/-! ## Smooth signed prime-pair input -/

/-- A real smooth compactly supported weight in the fixed dyadic interval
`[1,2]`.  This is intentionally stronger and more precise than the legacy
`SignedPairTraceGrade`, whose test class did not record these conditions. -/
def DyadicSmoothWeight (w : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ w ∧ tsupport w ⊆ Icc 1 2

/-- Smooth signed pair trace at support `σ`, with every logarithmic exponent
shown explicitly.  The singular series `S` is shared between both supports.
No implication from this predicate to a matrix trace limit is asserted in
this module. -/
def PairTraceGrade95 (S : ℕ → ℝ) (σ : ℝ) : Prop :=
  ∀ (w V : ℝ → ℝ), DyadicSmoothWeight w → DyadicSmoothWeight V →
    ∀ A : ℝ, 0 < A → ∃ K T₀ : ℝ, 0 < K ∧
      ∀ T ≥ T₀,
        |signedPairAggregate w V S (∫ x : ℝ, V x)
            (T ^ σ) (T ^ (σ - 1))|
          ≤ K * T ^ σ * (Real.log T) ^ (-A)

/-! ## Actual channel families and matrices -/

/-- The saturated full-matrix cost for a literal normalized profile. -/
def profileSaturatedCost (σ : ℝ) (v : ℝ → ℝ) : ℝ :=
  ((∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2) + σ * satJ σ v) /
    (σ * (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s) ^ 2)

/-- The support-`14999/10000` cost is definitionally tied to the proved
degree-18 B3 profile and rewrites to its proved exact cost. -/
theorem profileSaturatedCost_v8686 :
    profileSaturatedCost (14999 / 10000)
        QuarticWindowWitnesses.v8686 = QuarticWindowWitnesses.D8686 := by
  rw [profileSaturatedCost, QuarticWindowWitnesses.integral_v8686,
    QuarticWindowWitnesses.integral_v8686_sq,
    QuarticWindowWitnesses.satJ_8686]
  rfl

/-- The support-`19999/10000` cost is definitionally tied to the proved
degree-10 B3 profile and rewrites to its proved exact cost. -/
theorem profileSaturatedCost_v9506 :
    profileSaturatedCost (19999 / 10000)
        QuarticWindowWitnesses.v9506 = QuarticWindowWitnesses.D9506 := by
  rw [profileSaturatedCost, QuarticWindowWitnesses.integral_v9506,
    QuarticWindowWitnesses.integral_v9506_sq,
    QuarticWindowWitnesses.satJ_9506]
  rfl

/-- Data for one channelized Gram family.  Its support `σ`, distinguished
bandwidth `μ`, target fill `p`, and full profile `v` are type parameters, so
they cannot drift after construction.  All error functions are data, not
analytic assertions. -/
structure QuarticGramFamily (Z : ZeroConfig)
    (σ μ p : ℝ) (v : ℝ → ℝ) where
  /-- Number of physical window channels at height `T`. -/
  channelCount : ℝ → ℕ
  /-- Physical modulation period of each channel. -/
  period : ∀ T, Fin (channelCount T) → ℝ
  /-- Physical window of each channel. -/
  window : ∀ T, Fin (channelCount T) → ℝ → ℝ
  /-- Distinguished channel used by the nested block. -/
  distinguished : ∀ T, Fin (channelCount T)
  /-- Number of finite modulation columns. -/
  dim : ℝ → ℕ
  /-- Number of retained labels in each channel. -/
  channelDim : ∀ T, Fin (channelCount T) → ℕ
  /-- Channel and finite modulation label of each actual column. -/
  columnAddress : ∀ T, Fin (dim T) →
    (j : Fin (channelCount T)) × Fin (channelDim T j)
  /-- PSD simple-on-line part of the truncated zero matrix. -/
  P : ∀ T, Matrix (Fin (dim T)) (Fin (dim T)) ℂ
  /-- Hermitian nonsimple/off-line part of the truncated zero matrix. -/
  Q : ∀ T, Matrix (Fin (dim T)) (Fin (dim T)) ℂ
  /-- Error in the finite trace cap for `P`. -/
  pTraceError : ℝ → ℝ
  /-- Trace error of the truncated matrix at the dyadic zero scale. -/
  traceError : ℝ → ℝ
  /-- Frobenius error of the truncated matrix at the dyadic zero scale. -/
  frobError : ℝ → ℝ
  /-- Dimension of the distinguished block. -/
  blockDim : ℝ → ℕ
  /-- Literal coordinate embedding of that block. -/
  blockEmbedding : ∀ T, Fin (blockDim T) ↪ Fin (dim T)

namespace QuarticGramFamily

variable {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)

include F

/-- Full physical support length `σ log(T/2π)`. -/
def fullLength (T : ℝ) : ℝ := σ * Zeta23.l T

/-- The type-level full profile, cut off to its normalized support. -/
def supportedFullProfile (x : ℝ) : ℝ :=
  (Icc (-(1 : ℝ) / 2) (1 / 2)).indicator v x

/-- Total physical window energy at a point. -/
def windowEnergy (T u : ℝ) : ℝ :=
  ∑ j : Fin (F.channelCount T), F.window T j u ^ 2

/-- Energy of one physical channel. -/
def channelEnergy (T : ℝ) (j : Fin (F.channelCount T)) : ℝ :=
  ∫ u : ℝ, F.window T j u ^ 2

/-- Correct hat-unit denominator `L * ∫ Σ_j |φ_j|²`. -/
def hatDenominator (T : ℝ) : ℝ :=
  fullLength (σ := σ) T * ∫ u : ℝ, F.windowEnergy T u

/-- Fourier atom for a literal column and a complex zero argument. -/
def atom (T : ℝ) (i : Fin (F.dim T)) (ρ : ℂ) : ℂ :=
  let address := F.columnAddress T i
  let j := address.1
  let Lj := F.period T j
  let τ : ℝ := T + 2 * Real.pi * (address.2 : ℕ) / Lj
  (Real.sqrt (fullLength (σ := σ) T / Lj) : ℂ) *
    paperFT (fun u => (F.window T j u : ℂ)) (gammaOf ρ - τ)

/-- Full all-zero Gram sum, before hat normalization. -/
def rawFullGram (T : ℝ) : Matrix (Fin (F.dim T)) (Fin (F.dim T)) ℂ :=
  fun i j => ∑' ρ : Z.carrier,
    (Z.mult ρ : ℂ) * F.atom T i ρ * F.atom T j ρ

/-- Enlarged-window finite Gram sum over the actual set `ZIprime`. -/
def rawTruncatedGram (T : ℝ) : Matrix (Fin (F.dim T)) (Fin (F.dim T)) ℂ :=
  fun i j => ∑ᶠ ρ ∈ Z.ZIprime T,
    (Z.mult ρ : ℂ) * F.atom T i ρ * F.atom T j ρ

/-- The actual normalized full matrix `G`. -/
def G (T : ℝ) : Matrix (Fin (F.dim T)) (Fin (F.dim T)) ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) • F.rawFullGram T

/-- The actual normalized enlarged-window truncation `A`. -/
def A (T : ℝ) : Matrix (Fin (F.dim T)) (Fin (F.dim T)) ℂ :=
  ((F.hatDenominator T)⁻¹ : ℂ) • F.rawTruncatedGram T

/-- The actual tail matrix `E = G - A`. -/
def E (T : ℝ) : Matrix (Fin (F.dim T)) (Fin (F.dim T)) ℂ :=
  F.G T - F.A T

/-- The full/enlarged/tail identity is definitional, not a hypothesis. -/
theorem G_eq_A_add_E (T : ℝ) : F.G T = F.A T + F.E T := by
  simp only [E]
  abel

/-- The distinguished block is definitionally a principal compression of
the enlarged-window matrix `A`, not an unrelated matrix witness. -/
def block (T : ℝ) : Matrix (Fin (F.blockDim T)) (Fin (F.blockDim T)) ℂ :=
  (F.A T).submatrix (F.blockEmbedding T) (F.blockEmbedding T)

/-- Normalized energy profile of the literal distinguished physical window,
in coordinates `x ∈ [-1/2,1/2]`. -/
def localProfile (T x : ℝ) : ℝ :=
  let j := F.distinguished T
  let Lj := F.period T j
  Lj * F.window T j (Lj * x) ^ 2 / F.channelEnergy T j

/-- The exact saturated profile cost; the profile is a type parameter. -/
def saturatedCost : ℝ := profileSaturatedCost σ v

/-- A real-frequency Poisson alias term.  This construction-level object
does not by itself provide the off-RH complex/local-uniform passage used in
R1b. -/
def realAliasTerm (T τ τ' : ℝ) (j : Fin (F.channelCount T)) (m : ℤ) : ℂ :=
  let Lj := F.period T j
  Complex.exp (Complex.I * (τ' - T) * (m : ℝ) * Lj) *
    ∫ u : ℝ,
      (F.window T j u : ℂ) * F.window T j (u - (m : ℝ) * Lj) *
        Complex.exp (Complex.I * (τ - τ') * u)

/-- The corresponding off-RH complex-frequency alias term. -/
def complexAliasTerm (T : ℝ) (z z' : ℂ)
    (j : Fin (F.channelCount T)) (m : ℤ) : ℂ :=
  let Lj := F.period T j
  Complex.exp (Complex.I * (z' - T) * (m : ℝ) * Lj) *
    ∫ u : ℝ,
      (F.window T j u : ℂ) * F.window T j (u - (m : ℝ) * Lj) *
        Complex.exp (Complex.I * (z - z') * u)

/-- All nonzero aliases of all channels. -/
abbrev AliasIndex (T : ℝ) :=
  Fin (F.channelCount T) × {m : ℤ // m ≠ 0}

def realAliasFamily (T τ τ' : ℝ) : F.AliasIndex T → ℂ :=
  fun jm => F.realAliasTerm T τ τ' jm.1 jm.2

def complexAliasFamily (T : ℝ) (z z' : ℂ) : F.AliasIndex T → ℂ :=
  fun jm => F.complexAliasTerm T z z' jm.1 jm.2

/-- Centered empirical `k`th moment of the literal principal block. -/
def centeredBlockMoment (k : ℕ) (T : ℝ) : ℝ :=
  rtrace ((F.block T - 1) ^ k) / (F.blockDim T : ℝ)

end QuarticGramFamily

/-! ## Published Rudnick--Sarnak input, gauge fixed -/

/-- Insert the last coordinate which makes a vector sum to zero. -/
def rsZeroSumLift {n : ℕ} (ξ : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases (-∑ i, ξ i) (fun i => ξ i)

/-- The zero-sum Fourier test, with the Dirac delta eliminated by fixing its
last coordinate. -/
def rsGaugeTest {n : ℕ} (Φ : (Fin (n + 1) → ℝ) → ℂ)
    (x : Fin (n + 1) → ℂ) : ℂ :=
  ∫ ξ : Fin n → ℝ,
    Φ (rsZeroSumLift ξ) *
      Complex.exp (-2 * Real.pi * Complex.I *
        ∑ j : Fin (n + 1), x j * rsZeroSumLift ξ j)

/-- Canonically ordered collections of `q` disjoint unordered pairs. -/
def rsPairings (n q : ℕ) :
    Finset ((Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))) :=
  Finset.univ.filter fun pairing =>
    StrictMono pairing.1 ∧ Function.Injective pairing.2 ∧
      (∀ a, pairing.1 a < pairing.2 a) ∧
      (∀ a b, pairing.1 a ≠ pairing.2 b)

/-- The vector `Σ_a v_a(e_{i_a}-e_{j_a})` of RS Theorem 3.1. -/
def rsPairVector {n q : ℕ}
    (pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1)))
    (w : Fin q → ℝ) : Fin (n + 1) → ℝ :=
  fun i => ∑ a : Fin q,
    ((if pairing.1 a = i then w a else 0) -
      (if pairing.2 a = i then w a else 0))

/-- One disjoint-pair contraction integral. -/
def rsPairIntegral {n q : ℕ} (Φ : (Fin (n + 1) → ℝ) → ℂ)
    (pairing : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1))) : ℂ :=
  ∫ w : Fin q → ℝ,
    (∏ a : Fin q, |w a| : ℝ) * Φ (rsPairVector pairing w)

/-- The bracketed main term of RS equations (3.8)--(3.9). -/
def rsMainTerm {n : ℕ} (Φ : (Fin (n + 1) → ℝ) → ℂ) : ℂ :=
  Φ 0 + ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
    ∑ pairing ∈ rsPairings n q, rsPairIntegral Φ pairing

/-- `κ(h)=∫h₁(r)⋯h_n(r)dr`, with `h_j` the paper Fourier transform of
the compactly supported height weight `g_j`. -/
def rsHeightFactor {n : ℕ} (g : Fin (n + 1) → ℝ → ℂ) : ℂ :=
  ∫ r : ℝ, ∏ j : Fin (n + 1), paperFT (g j) r

/-- One multiplicity-weighted ordered zero tuple. -/
def rsZeroTupleTerm (Z : ZeroConfig) {n : ℕ}
    (g : Fin (n + 1) → ℝ → ℂ)
    (Φ : (Fin (n + 1) → ℝ) → ℂ) (T : ℝ)
    (ρ : Fin (n + 1) → Z.carrier) : ℂ :=
  (∏ j : Fin (n + 1), (Z.mult (ρ j) : ℂ) *
      paperFT (g j) (gammaOf (ρ j) / T)) *
    rsGaugeTest Φ (fun j =>
      (Real.log T / (2 * Real.pi) : ℂ) * gammaOf (ρ j))

/-- **Rudnick--Sarnak 1996, Theorem 3.1, `m=1`.**

This is the smoothed all-tuples statement with multiplicities, strict total
Fourier support below `2`, height factor `κ(h)`, and error `O(T)`.  The full
Fourier-space delta is rendered by `rsZeroSumLift`; it is not treated as an
ordinary Bochner integral.  The `Summable` clause prevents Lean's total
`tsum` from assigning a misleading value to a divergent tuple sum.

Source: Rudnick--Sarnak, Duke Math. J. 81 (1996), Theorem 3.1 and equations
(3.8)--(3.9), specialized to zeta (`m=1`); Proposition 2.4 makes Hypothesis H
automatic in this specialization.  The RH-dependent sharp-height Theorem
3.2 is not included. -/
structure RS1996ZetaInputs (Z : ZeroConfig) : Prop where
  theorem31 : ∀ (n : ℕ) (g : Fin (n + 1) → ℝ → ℂ)
      (Φ : (Fin (n + 1) → ℝ) → ℂ),
    (∀ j, ContDiff ℝ ∞ (g j) ∧ HasCompactSupport (g j)) →
    ContDiff ℝ 1 Φ →
    tsupport Φ ⊆ {ξ | ∑ j : Fin (n + 1), |ξ j| < 2} →
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 ≤ T₀ ∧ ∀ T ≥ T₀,
      Summable (rsZeroTupleTerm Z g Φ T) ∧
      ‖(∑' ρ, rsZeroTupleTerm Z g Φ T ρ) -
          rsHeightFactor g * (T * Real.log T / (2 * Real.pi)) *
            rsMainTerm Φ‖ ≤ C * T

/-! ## Exact analytic obligations on one literal family -/

/-- Full trace limits for the actual enlarged-window matrix `A`.  These are
not inferred from `PairTraceGrade95` in this file.  The cost is the literal
functional of the type-level B3 profile, never a free numeric field. -/
structure FullTraceLimits {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  trace_bound : ∀ᶠ T in atTop,
    |rtrace (F.A T) - (Z.N T (2 * T) : ℝ)| ≤ F.traceError T
  frob_bound : ∀ᶠ T in atTop,
    frobSq (F.A T) ≤
      profileSaturatedCost σ v * (Z.N T (2 * T) : ℝ) + F.frobError T
  trace_small : F.traceError =o[atTop] fun T => (Z.N T (2 * T) : ℝ)
  frob_small : F.frobError =o[atTop] fun T => (Z.N T (2 * T) : ℝ)

/-- Stable zero-side input for the genuine enlarged-window mechanism.

`A=P+Q` is the truncated finite zero sum, while the separately defined full
matrix satisfies the theorem `G_eq_A_add_E`.  The budgets are the actual
enlarged-window populations `s₁` and `s₂+p`; the edge count is `NII`, not an
exact identification with the dyadic count.  No full-matrix `G=P+Q` premise
is made.  Trace and moment limits are stated directly for `A`; consequently
no unused quantitative tail-error fields are included here.

Provenance: the zero-side block construction and enlarged-window tail
passage.  For a new multi-window system these clauses, especially the split
putting only simple on-line atoms in `P`, are exact named blockers. -/
structure StableZeroSide {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  truncated_decomposition : ∀ T, F.A T = F.P T + F.Q T
  p_psd : ∀ T, (F.P T).PosSemidef
  q_hermitian : ∀ T, (F.Q T).IsHermitian
  simple_rank_bound : ∀ᶠ T in atTop,
    (F.P T).rank ≤ Z.s1 T
  simple_trace_cap : ∀ᶠ T in atTop,
    rtrace (F.P T) ≤
      (Z.s1 T : ℝ) + F.pTraceError T
  bad_index_bound : ∀ᶠ T in atTop,
    posIndex (q_hermitian T) ≤ Z.s2 T + Z.p T
  p_trace_small : F.pTraceError =o[atTop]
    fun T => (Z.N T (2 * T) : ℝ)

/-- The only construction data consumed by the quartic transfer: positive
block density and convergence of the literal block dimension.  This interface
is separated from `PrincipalCyclicBlock`, whose physical-window allocation
fields are not used by the transfer and are inconsistent for the frozen
families. -/
structure BlockDimensionLimit {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  bandwidth_pos : 0 < μ
  block_dimension : Tendsto
    (fun T => (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ))
      atTop (nhds μ)

/-- The literal principal block is Hermitian by the actual `A=P+Q`
decomposition.  This is derived data, not a field of either input structure. -/
theorem StableZeroSide.block_isHermitian
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} (hzero : StableZeroSide F) (T : ℝ) :
    (F.block T).IsHermitian := by
  rw [QuarticGramFamily.block, hzero.truncated_decomposition T]
  exact ((hzero.p_psd T).isHermitian.add
    (hzero.q_hermitian T)).submatrix (F.blockEmbedding T)

/-- Exact finite core-plus-edge count comparison.  This is proved from the
base zero populations; it is not an analytic field of `Inputs95`. -/
theorem core_count_le_dyadic_add_edge (Z : ZeroConfig) {T : ℝ} (hT : 0 ≤ T) :
    (Z.s1 T : ℝ) + 2 * (Z.s2 T + Z.p T : ℕ) ≤
      (Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
  have hcore : Z.s1 T + 2 * (Z.s2 T + Z.p T) ≤ Z.NIprime T := by
    have h := ZeroSide.s1_add_two_s2_add_two_p_le_NIprime Z T
    omega
  rw [Assembly.NIprime_eq Z hT] at hcore
  exact_mod_cast hcore

/-- The proved robust stability inequality applied to the literal principal
compression of `A`.  The edge-count loss enters with the proved coefficient
`2`; no matrix dimension is identified with the zero scale. -/
theorem robustBlockTailBound_eventually
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F) :
    ∀ᶠ T in atTop,
      tailExcessSq (hzero.block_isHermitian T) (Z.s2 T + Z.p T) ≤
        (Z.s1 T : ℝ) -
          (2 - profileSaturatedCost σ v) * (Z.N T (2 * T) : ℝ) +
          2 * F.pTraceError T + 4 * F.traceError T + F.frobError T +
          2 * (Assembly.NII Z T : ℝ) := by
  filter_upwards [hzero.simple_rank_bound, hzero.simple_trace_cap,
    hzero.bad_index_bound, hfull.trace_bound, hfull.frob_bound,
    eventually_ge_atTop (0 : ℝ)] with T hrank htraceP hposQ htraceA hfrobA hT
  have htraceA' :
      |rtrace (F.P T + F.Q T) - (Z.N T (2 * T) : ℝ)| ≤
        F.traceError T := by
    simpa only [← hzero.truncated_decomposition T] using htraceA
  have hfrobA' :
      frobSq (F.P T + F.Q T) ≤
        profileSaturatedCost σ v * (Z.N T (2 * T) : ℝ) + F.frobError T := by
    simpa only [← hzero.truncated_decomposition T] using hfrobA
  have hrob :=
    RobustStability.robust_stability_inequality_principalCompression_withCountError
      (hzero.p_psd T) (hzero.q_hermitian T) (F.blockEmbedding T)
      hrank htraceP hposQ (core_count_le_dyadic_add_edge Z hT)
      htraceA' hfrobA'
  have hblock : F.block T =
      (F.P T + F.Q T).submatrix (F.blockEmbedding T) (F.blockEmbedding T) := by
    rw [QuarticGramFamily.block, hzero.truncated_decomposition T]
  rw [tailExcessSq_congr hblock (hzero.block_isHermitian T)
    (((hzero.p_psd T).isHermitian.add
      (hzero.q_hermitian T)).submatrix (F.blockEmbedding T))]
  exact hrob

/-! ## Actual principal construction and the R1b bridge -/

/-- R1a construction of one literal normalized principal block.

The real-frequency alias clauses are construction checks only.  They are not
described as formula (23), do not identify any cyclic moment, and do not
supply the off-RH complex Poisson identity at the actual `ZIprime` zeros.
That identity remains in `BlockMomentLimits`.  The literal local profile and
its translated-product convergence tie the construction to `p`, but do not
assert a matrix moment.  The block itself is already definitionally a
principal compression of the finite `ZIprime` sum. -/
structure PrincipalCyclicBlock {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  support_pos : 0 < σ
  bandwidth_pos : 0 < μ
  strict_fourier_support : 4 * μ < 2
  fill_pos : 0 < p
  fill_le_one : p ≤ 1
  periods_pos : ∀ᶠ T in atTop, ∀ j, 0 < F.period T j
  critical_count : ∀ᶠ T in atTop,
    ∑ j : Fin (F.channelCount T), F.period T j =
      @QuarticGramFamily.fullLength σ T
  channel_grid_count : ∀ᶠ T in atTop, ∀ j,
    F.channelDim T j = ⌊F.period T j * T / (2 * Real.pi)⌋₊
  column_address_bijective : ∀ᶠ T in atTop,
    Function.Bijective (F.columnAddress T)
  windows_smooth : ∀ᶠ T in atTop, ∀ j, ContDiff ℝ ∞ (F.window T j)
  windows_compact : ∀ᶠ T in atTop, ∀ j, HasCompactSupport (F.window T j)
  zero_alias_reconstruction : ∀ᶠ T in atTop,
    ∀ᵐ u : ℝ ∂volume,
      F.windowEnergy T u =
        @QuarticGramFamily.supportedFullProfile v
          (u / @QuarticGramFamily.fullLength σ T)
  real_aliases_summable : ∀ᶠ T in atTop, ∀ τ τ',
    Summable (F.realAliasFamily T τ τ')
  real_aliases_cancel : ∀ᶠ T in atTop, ∀ τ τ',
    ∑' a, F.realAliasFamily T τ τ' a = 0
  full_gram_summable : ∀ᶠ T in atTop, ∀ i j,
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℂ) * F.atom T i ρ * F.atom T j ρ)
  distinguished_period : ∀ᶠ T in atTop,
    F.period T (F.distinguished T) = μ * Zeta23.l T
  /-- Mean-one hat allocation requires energy fraction `μ`, not `μ/σ`. -/
  distinguished_energy_ratio : Tendsto
    (fun T => F.channelEnergy T (F.distinguished T) /
      (∫ u : ℝ, F.windowEnergy T u)) atTop (nhds μ)
  distinguished_channel_energy_pos : ∀ᶠ T in atTop,
    0 < F.channelEnergy T (F.distinguished T)
  local_profile_integrable : ∀ᶠ T in atTop,
    Integrable (F.localProfile T)
  local_profile_nonneg : ∀ᶠ T in atTop, ∀ x,
    0 ≤ F.localProfile T x
  local_profile_support : ∀ᶠ T in atTop,
    tsupport (F.localProfile T) ⊆ Icc (-(1 : ℝ) / 2) (1 / 2)
  local_profile_mean_one : ∀ᶠ T in atTop,
    ∫ x : ℝ, F.localProfile T x = 1
  /-- The fill parameter is tied to the literal window by locally uniform
  `L¹` convergence of every translated product through degree four.  This
  is stronger than scalar `L¹` convergence and is the construction datum
  needed before the cyclic Fourier tests can be formed. -/
  translated_products_locally_uniform :
    ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∀ᶠ T in atTop, ∀ shift : Fin k → ℝ,
        (∀ a, |shift a| ≤ R) →
          Integrable (fun x : ℝ =>
            |(∏ a : Fin k, F.localProfile T (x + shift a)) -
              ∏ a : Fin k, TopHatMoments.topHat p (x + shift a)|) ∧
          (∫ x : ℝ,
            |(∏ a : Fin k, F.localProfile T (x + shift a)) -
              ∏ a : Fin k, TopHatMoments.topHat p (x + shift a)|) ≤ ε
  distinguished_columns : ∀ᶠ T in atTop, ∀ i,
    (F.columnAddress T (F.blockEmbedding T i)).1 = F.distinguished T
  distinguished_exhaustive : ∀ᶠ T in atTop, ∀ i,
    (F.columnAddress T i).1 = F.distinguished T →
      ∃ b, F.blockEmbedding T b = i
  block_dimension : Tendsto
    (fun T => (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ))
      atTop (nhds μ)

/-- The full physical construction implies the minimal dimension interface
used by the transfer. -/
theorem PrincipalCyclicBlock.toBlockDimensionLimit
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} (h : PrincipalCyclicBlock F) :
    BlockDimensionLimit F :=
  ⟨h.bandwidth_pos, h.block_dimension⟩

/-- Formula-(21) target for a centered block moment. -/
def formula21Moment (k : ℕ) (μ p : ℝ) : ℝ :=
  match k with
  | 0 => 1
  | 1 => 0
  | 2 => TopHatMoments.formula21M2Integral μ p
  | 3 => TopHatMoments.formula21M3Integral μ p
  | 4 => TopHatMoments.formula21M4Integral μ p
  | _ => 0

/-- The only moment data consumed by the quartic transfer.  The complex
Poisson and alias fields of `BlockMomentLimits` belong to one proposed
construction route, not to the transfer theorem itself. -/
structure BlockMomentConvergence {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  moments : ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
    Tendsto (F.centeredBlockMoment k) atTop
      (nhds (formula21Moment k μ p))

/-- **R1b, the sole actual-block-to-formula-(21) linkage.**

The `moments` field is the complete final limit statement for the literal
principal compression of `A`; no scalar `L¹` profile convergence is used to
infer translated quartic products.  The preceding complex clauses expose
the off-RH complex Poisson identity at the actual enlarged-window zeros;
real alias cancellation does not prove it.  RS 1996 itself remains a
separate input, so no implication from the published theorem to this
finite-grid/sharp-height statement is asserted without a derivation.

Provenance: specialization of RS Theorem 3.1 plus complex Poisson expansion,
finite/infinite-grid estimates, common height smoothing, and sharp-height
removal as mapped in `docs/audit/rs_reduction.md`. -/
structure BlockMomentLimits {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) : Prop where
  complex_aliases_summable_at_zeros : ∀ᶠ T in atTop,
    ∀ ρ ∈ Z.ZIprime T, ∀ ρ' ∈ Z.ZIprime T,
      Summable (F.complexAliasFamily T (gammaOf ρ) (gammaOf ρ'))
  offRH_complex_poisson_at_zeros : ∀ᶠ T in atTop,
    ∀ ρ ∈ Z.ZIprime T, ∀ ρ' ∈ Z.ZIprime T,
      ∑' a, F.complexAliasFamily T (gammaOf ρ) (gammaOf ρ') a = 0
  moments : ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
    Tendsto (F.centeredBlockMoment k) atTop
      (nhds (formula21Moment k μ p))

/-- The full R1b route implies the minimal moment interface used by the
transfer. -/
theorem BlockMomentLimits.toBlockMomentConvergence
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v} (h : BlockMomentLimits F) :
    BlockMomentConvergence F :=
  ⟨h.moments⟩

/-! ## Explicit bundle -/

abbrev Family14999 (Z : ZeroConfig) :=
  QuarticGramFamily Z (14999 / 10000) (4999 / 10000) (89 / 100)
    QuarticWindowWitnesses.v8686

abbrev Family19999 (Z : ZeroConfig) :=
  QuarticGramFamily Z (19999 / 10000) (4999 / 10000) (83 / 100)
    QuarticWindowWitnesses.v9506

/-- Shared data for both quartic supports.  Exact B3 profiles occur in the
types of the two families, and the singular series is literally shared. -/
structure Inputs95Data (Z : ZeroConfig) where
  singularSeries : ℕ → ℝ
  family14999 : Family14999 Z
  family19999 : Family19999 Z

/-- The current analytic boundary.  There is no constructor theorem and no
asserted instance.  Finite stability, exact witness arithmetic, dual
polynomials, and the proved crossing identity are absent from the fields. -/
structure Inputs95 (Z : ZeroConfig) (X : Inputs95Data Z) : Prop where
  /-- A1 at strict support `1.4999`. -/
  pair14999 : PairTraceGrade95 X.singularSeries (14999 / 10000)
  /-- A1 at strict support `1.9999`. -/
  pair19999 : PairTraceGrade95 X.singularSeries (19999 / 10000)
  /-- Separate prime-side trace bridge for the actual `A` at `1.4999`. -/
  trace14999 : FullTraceLimits X.family14999
  /-- Separate prime-side trace bridge for the actual `A` at `1.9999`. -/
  trace19999 : FullTraceLimits X.family19999
  /-- Enlarged-window zero-side decomposition at `1.4999`. -/
  zeroSide14999 : StableZeroSide X.family14999
  /-- Enlarged-window zero-side decomposition at `1.9999`. -/
  zeroSide19999 : StableZeroSide X.family19999
  /-- Published smoothed all-tuples theorem, shared by both blocks. -/
  rs1996 : RS1996ZetaInputs Z
  /-- Literal R1a window/grid construction at `1.4999`. -/
  r1a14999 : PrincipalCyclicBlock X.family14999
  /-- Literal R1a window/grid construction at `1.9999`. -/
  r1a19999 : PrincipalCyclicBlock X.family19999
  /-- Complete R1b actual-block moment passage at `1.4999`. -/
  r1b14999 : BlockMomentLimits X.family14999
  /-- Complete R1b actual-block moment passage at `1.9999`. -/
  r1b19999 : BlockMomentLimits X.family19999

end Zeta85
end RH

end
