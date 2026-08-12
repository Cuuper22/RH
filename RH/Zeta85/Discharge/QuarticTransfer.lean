/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Inputs95
import RH.Zeta85.Discharge.TrimmedMoment
import Zeta23.Final
import Zeta23.Tail

/-!
# Finite-to-asymptotic transfer for the quartic rungs

This file consumes only the explicit per-support analytic structures in
`Inputs95`.  It does not use the signed-pair or Rudnick--Sarnak fields: those
are upstream routes for proving the trace and moment structures, not logical
substitutes for them.

The finite bridge is evaluated at the actual first four spectral moments.
Its asymptotic boundary is only the single scalar quartic score selected by
the terminal certificate; no finite matrix is asserted to have its limiting
top-hat moments exactly.
-/

open Filter Matrix Finset Unitary
open scoped BigOperators ComplexOrder Topology

noncomputable section

namespace RH
namespace Zeta85
namespace QuarticTransfer

open Zeta23 RHLinalg
open RobustStability TrimmedMoment

/-! ## 1. Centered spectral moments -/

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem specMap_const_one {d : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian) :
    specMap hG (fun _ => (1 : ℝ)) = 1 := by
  unfold specMap
  rw [conjStarAlgAut_apply]
  simp

private theorem specMap_pow_nat {d : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian)
    (f : ℝ → ℝ) (k : ℕ) :
    (specMap hG f) ^ k = specMap hG (fun x => f x ^ k) := by
  induction k with
  | zero =>
      simpa only [pow_zero] using (specMap_const_one hG).symm
  | succ k ih =>
      rw [pow_succ, ih, ← specMap_mul]
      congr 1

/-- The normalized centered eigenvalue moment is exactly the normalized
real trace of the corresponding centered matrix power. -/
theorem spectralMoment_eq_centered_rtrace {d : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian) (k : ℕ) :
    spectralMoment hG k = rtrace ((G - 1) ^ k) / (d : ℝ) := by
  have hcenter : G - 1 = specMap hG (fun x => x - 1) := by
    calc
      G - 1 = specMap hG id - specMap hG (fun _ => (1 : ℝ)) := by
        rw [specMap_id, specMap_const_one]
      _ = specMap hG (id - fun _ => (1 : ℝ)) := (specMap_sub hG _ _).symm
      _ = specMap hG (fun x => x - 1) := by rfl
  have htrace :
      rtrace ((G - 1) ^ k) =
        ∑ i : SpectralIndex d, (hG.eigenvalues₀ i - 1) ^ k := by
    rw [hcenter, specMap_pow_nat, rtrace_specMap]
    exact sum_eigenvalues_reindex hG (fun x => (x - 1) ^ k)
  rw [htrace]
  simp only [spectralMoment, normalizedMoment, uniformWeight, centeredSpectrum,
    SpectralIndex, Fintype.card_fin, div_eq_mul_inv]
  simp only [one_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## 2. The finite affine bridge -/

/-- The quartic evaluated at the actual first four centered moments of the
distinguished finite block. -/
def quarticScore {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  q.p0 + q.p1 * F.centeredBlockMoment 1 T +
    q.p2 * F.centeredBlockMoment 2 T +
    q.p3 * F.centeredBlockMoment 3 T +
    q.p4 * F.centeredBlockMoment 4 T

/-- The same quartic evaluated at the formula-(21) limiting moments. -/
def limitQuarticScore (q : Quartic) (μ p : ℝ) : ℝ :=
  q.p0 + q.p1 * formula21Moment 1 μ p +
    q.p2 * formula21Moment 2 μ p +
    q.p3 * formula21Moment 3 μ p +
    q.p4 * formula21Moment 4 μ p

/-- The target-specific analytic datum actually consumed by a quartic
certificate: convergence of its one scalar score.  Separate convergence of
all four moments is a sufficient construction route, not a logical
requirement of the transfer. -/
def QuarticScoreConvergence
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop :=
  Tendsto (quarticScore q F) atTop
    (nhds (limitQuarticScore q μ p))

/-- The combined asymptotic datum actually consumed after the finite
inequality is normalized.  Taking this product before the limit permits
cancellation between the block density and normalized block moments. -/
structure WeightedQuarticLimit
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos : ∀ᶠ T in atTop, 0 < F.blockDim T
  weighted_score : Tendsto
    (fun T => (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
      quarticScore q F T)
    atTop (nhds (μ * limitQuarticScore q μ p))

/-- All finite errors in the affine bridge.  The coefficient `3` on the
enlarged-window edge count is exact: `2` comes from robust stability and
`1` from the two count comparisons. -/
def transferError {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  2 * F.pTraceError T + 4 * F.traceError T + F.frobError T +
    3 * (Assembly.NII Z T : ℝ)

/-- Sorted-head weak duality for the actual principal block, with all
normalizations cleared. -/
private theorem scaled_block_quartic_le_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hzero : StableZeroSide F) (q : Quartic) (cap : ℝ)
    (hdual : DualFeasible q cap) (T : ℝ) (hm : 0 < F.blockDim T) :
    (F.blockDim T : ℝ) * quarticScore q F T -
        (Z.s2 T + Z.p T : ℕ) * cap ≤
      tailExcessSq (hzero.block_isHermitian T) (Z.s2 T + Z.p T) := by
  let hB := hzero.block_isHermitian T
  have hmR : (0 : ℝ) < F.blockDim T := by exact_mod_cast hm
  have hinputs := spectral_headTrimmedMomentInputs
    (b := Z.s2 T + Z.p T) hB hm
  have hdualFinite := finite_trimmed_quartic_dual q cap
    (centeredSpectrum hB) (uniformWeight (SpectralIndex (F.blockDim T)))
    (uniformRemoved
      (spectralHeadSet (Fintype.card (Fin (F.blockDim T))) (Z.s2 T + Z.p T)))
    (spectralMoment hB 1) (spectralMoment hB 2)
    (spectralMoment hB 3) (spectralMoment hB 4)
    (((Z.s2 T + Z.p T : ℕ) : ℝ) / F.blockDim T) hdual hinputs
  have hscaled := mul_le_mul_of_nonneg_left hdualFinite hmR.le
  rw [spectral_residualTail_eq_tailExcessSq_div] at hscaled
  have hscore :
      q.p0 + q.p1 * spectralMoment hB 1 + q.p2 * spectralMoment hB 2 +
          q.p3 * spectralMoment hB 3 + q.p4 * spectralMoment hB 4 =
        quarticScore q F T := by
    simp only [quarticScore, QuarticGramFamily.centeredBlockMoment,
      spectralMoment_eq_centered_rtrace]
  rw [hscore] at hscaled
  calc
    (F.blockDim T : ℝ) * quarticScore q F T -
          (Z.s2 T + Z.p T : ℕ) * cap =
        (F.blockDim T : ℝ) *
          (quarticScore q F T -
            ((Z.s2 T + Z.p T : ℕ) : ℝ) / F.blockDim T * cap) := by
              field_simp [hmR.ne']
    _ ≤ (F.blockDim T : ℝ) *
        (tailExcessSq hB (Z.s2 T + Z.p T) / F.blockDim T) := hscaled
    _ = tailExcessSq (hzero.block_isHermitian T) (Z.s2 T + Z.p T) := by
      field_simp [hmR.ne']

/-- The exact finite affine bridge.  It uses the actual finite moments,
never their limits. -/
theorem finite_affine_bridge_at
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hzero : StableZeroSide F) (q : Quartic) (cap Dbar : ℝ)
    (hdual : DualFeasible q cap) (hcap : cap / 2 ≤ 1)
    (hcost : profileSaturatedCost σ v ≤ Dbar)
    (T : ℝ) (hT : 0 ≤ T) (hm : 0 < F.blockDim T)
    (htail :
      tailExcessSq (hzero.block_isHermitian T) (Z.s2 T + Z.p T) ≤
        (Z.s1 T : ℝ) -
          (2 - profileSaturatedCost σ v) * (Z.N T (2 * T) : ℝ) +
          2 * F.pTraceError T + 4 * F.traceError T + F.frobError T +
          2 * (Assembly.NII Z T : ℝ)) :
    (F.blockDim T : ℝ) * quarticScore q F T +
        (2 - Dbar - cap / 2) * (Z.N T (2 * T) : ℝ) ≤
      (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) + transferError F T := by
  have hweak := scaled_block_quartic_le_tail hzero q cap hdual T hm
  have hcore := core_count_le_dyadic_add_edge Z hT
  have hs1Nat := Assembly.s1_le Z hT
  have hs1 : (Z.s1 T : ℝ) ≤
      (Z.N0s T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast hs1Nat
  have hcap0 : 0 ≤ cap / 2 := div_nonneg hdual.cap_nonneg (by norm_num)
  have hremain : 0 ≤ 1 - cap / 2 := sub_nonneg.mpr hcap
  have hcoreScaled := mul_le_mul_of_nonneg_left hcore hcap0
  have hs1Scaled := mul_le_mul_of_nonneg_left hs1 hremain
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := by positivity
  have hcostScaled := mul_le_mul_of_nonneg_right hcost hN
  unfold transferError
  nlinarith

private theorem blockDim_pos_eventually
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hr1a : BlockDimensionLimit F) :
    ∀ᶠ T in atTop, 0 < F.blockDim T := by
  have hratio : ∀ᶠ T in atTop,
      0 < (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) :=
    hr1a.block_dimension.eventually (Ioi_mem_nhds hr1a.bandwidth_pos)
  filter_upwards [hratio] with T hratioT
  apply Nat.pos_of_ne_zero
  intro hm0
  simp [hm0] at hratioT

/-- Separate block-density and scalar-score limits imply the combined
weighted limit.  This compatibility theorem keeps the earlier construction
interfaces usable while exposing the weaker object the transfer needs. -/
theorem weightedQuarticLimit_of_separate
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hr1a : BlockDimensionLimit F)
    (hscore : QuarticScoreConvergence q F) :
    WeightedQuarticLimit q F :=
  ⟨blockDim_pos_eventually hr1a, hr1a.block_dimension.mul hscore⟩

/-- Eventual form of the finite affine bridge, obtained directly from the
proved robust stability inequality. -/
theorem finite_affine_bridge
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hblock : ∀ᶠ T in atTop, 0 < F.blockDim T)
    (q : Quartic) (cap Dbar : ℝ) (hdual : DualFeasible q cap)
    (hcap : cap / 2 ≤ 1) (hcost : profileSaturatedCost σ v ≤ Dbar) :
    ∀ᶠ T in atTop,
      (F.blockDim T : ℝ) * quarticScore q F T +
          (2 - Dbar - cap / 2) * (Z.N T (2 * T) : ℝ) ≤
        (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) + transferError F T := by
  filter_upwards [robustBlockTailBound_eventually hfull hzero,
    hblock, eventually_ge_atTop (0 : ℝ)]
      with T htail hm hT
  exact finite_affine_bridge_at hzero q cap Dbar hdual hcap hcost T hT hm htail

/-! ## 3. Passage to the limit -/

theorem quarticScore_tendsto
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hmom : BlockMomentConvergence F) (q : Quartic) :
    Tendsto (quarticScore q F) atTop (nhds (limitQuarticScore q μ p)) := by
  change Tendsto
    (fun T => q.p0 + q.p1 * F.centeredBlockMoment 1 T +
      q.p2 * F.centeredBlockMoment 2 T +
      q.p3 * F.centeredBlockMoment 3 T +
      q.p4 * F.centeredBlockMoment 4 T) atTop
    (nhds (q.p0 + q.p1 * formula21Moment 1 μ p +
      q.p2 * formula21Moment 2 μ p + q.p3 * formula21Moment 3 μ p +
      q.p4 * formula21Moment 4 μ p))
  have h1 := hmom.moments 1 (by omega) (by omega)
  have h2 := hmom.moments 2 (by omega) (by omega)
  have h3 := hmom.moments 3 (by omega) (by omega)
  have h4 := hmom.moments 4 (by omega) (by omega)
  exact
    ((((tendsto_const_nhds.add (tendsto_const_nhds.mul h1)).add
      (tendsto_const_nhds.mul h2)).add
      (tendsto_const_nhds.mul h3)).add
      (tendsto_const_nhds.mul h4))

/-- Four separate moment limits imply the one target-specific scalar limit.
This keeps the stronger formula-(21) route available without forcing every
future construction to prove unused coordinates. -/
theorem quarticScoreConvergence_of_moments
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hmom : BlockMomentConvergence F) (q : Quartic) :
    QuarticScoreConvergence q F :=
  quarticScore_tendsto hmom q

private theorem edgeCount_small
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) :
    (fun T => (Assembly.NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hRvM.local_count
  obtain ⟨C, hC⟩ := Tail.eventually_NII_le Z hA₀ hloc
  have hO : (fun T => (Assembly.NII Z T : ℝ)) =O[atTop]
      (fun T => Real.sqrt T * Zeta23.l T) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hC, Assembly.eventually_l_pos] with T hCT hlT
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    simpa [mul_assoc] using hCT
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM
      Assembly.isLittleO_sqrt_mul_l_Tl)

theorem transferError_small
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hRvM : RiemannVonMangoldt Z) (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F) :
    transferError F =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  change (fun T => 2 * F.pTraceError T + 4 * F.traceError T + F.frobError T +
    3 * (Assembly.NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ))
  have hp := hzero.p_trace_small.const_mul_left 2
  have ht := hfull.trace_small.const_mul_left 4
  have he := (edgeCount_small hRvM).const_mul_left 3
  exact (((hp.add ht).add hfull.frob_small).add he)

/-- The finite affine lower-bound expression after division by the dyadic
zero count and by the positive affine denominator. -/
def normalizedTransfer {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : Quartic) (cap Dbar : ℝ) (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) : ℝ :=
  (((F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ)) * quarticScore q F T +
      (2 - Dbar - cap / 2) -
      transferError F T / (Z.N T (2 * T) : ℝ)) /
    (1 - cap / 2)

theorem normalizedTransfer_tendsto
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hRvM : RiemannVonMangoldt Z) (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (q : Quartic) (hweighted : WeightedQuarticLimit q F)
    (cap Dbar : ℝ) :
    Tendsto (normalizedTransfer q cap Dbar F) atTop
      (nhds ((μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2) /
        (1 - cap / 2))) := by
  have hproduct := hweighted.weighted_score
  have herror := (transferError_small hRvM hfull hzero).tendsto_div_nhds_zero
  have hconstant : Tendsto (fun _ : ℝ => 2 - Dbar - cap / 2) atTop
      (nhds (2 - Dbar - cap / 2)) := tendsto_const_nhds
  have hnumerator :=
    (hproduct.add hconstant).sub herror
  have hquotient := hnumerator.div_const (1 - cap / 2)
  change Tendsto
    (fun T =>
      (((F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ)) * quarticScore q F T +
          (2 - Dbar - cap / 2) -
          transferError F T / (Z.N T (2 * T) : ℝ)) /
        (1 - cap / 2)) atTop
    (nhds ((μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2) /
      (1 - cap / 2)))
  have hlimit :
      (μ * limitQuarticScore q μ p + (2 - Dbar - cap / 2) - 0) /
          (1 - cap / 2) =
        (μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2) /
          (1 - cap / 2) := by ring
  rw [← hlimit]
  exact hquotient

/-- Generic finite-to-asymptotic transfer.  The strict numerical comparison
is separated as a premise so each terminal specialization must prove it by
exact arithmetic; it does not assume any zero-density conclusion. -/
theorem asymptotic_eps_transfer
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hRvM : RiemannVonMangoldt Z) (hfull : FullTraceLimits F)
    (hzero : StableZeroSide F)
    (q : Quartic) (hweighted : WeightedQuarticLimit q F)
    (cap Dbar target : ℝ) (hdual : DualFeasible q cap)
    (hcap : cap / 2 < 1) (hcost : profileSaturatedCost σ v ≤ Dbar)
    (hstrict : target <
      (μ * limitQuarticScore q μ p + 2 - Dbar - cap / 2) /
        (1 - cap / 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (target - ε) * (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  have hden : 0 < 1 - cap / 2 := sub_pos.mpr hcap
  have hlower : ∀ᶠ T in atTop, target < normalizedTransfer q cap Dbar F T :=
    (normalizedTransfer_tendsto hRvM hfull hzero q hweighted cap Dbar).eventually
      (Ioi_mem_nhds hstrict)
  have hfinite := finite_affine_bridge hfull hzero
    hweighted.block_dimension_pos q cap Dbar hdual
    hcap.le hcost
  have hNpos := (Assembly.tendsto_N_atTop Z hRvM).eventually_gt_atTop 0
  have htarget : ∀ᶠ T in atTop,
      target * (Z.N T (2 * T) : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hlower, hfinite, hNpos] with T hlowerT hfiniteT hNT
    rw [normalizedTransfer] at hlowerT
    have hlowerDen := (lt_div_iff₀ hden).mp hlowerT
    have hrewrite :
        (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) * quarticScore q F T +
              (2 - Dbar - cap / 2) -
              transferError F T / (Z.N T (2 * T) : ℝ) =
          ((F.blockDim T : ℝ) * quarticScore q F T +
              (2 - Dbar - cap / 2) * (Z.N T (2 * T) : ℝ) -
              transferError F T) /
            (Z.N T (2 * T) : ℝ) := by
      field_simp [hNT.ne']
    rw [hrewrite] at hlowerDen
    have hlowerN := (lt_div_iff₀ hNT).mp hlowerDen
    have hmul :
        target * (1 - cap / 2) * (Z.N T (2 * T) : ℝ) <
          (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) := by
      linarith
    have hmul' :
        (1 - cap / 2) * (target * (Z.N T (2 * T) : ℝ)) <
          (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) := by
      calc
        (1 - cap / 2) * (target * (Z.N T (2 * T) : ℝ)) =
            target * (1 - cap / 2) * (Z.N T (2 * T) : ℝ) := by ring
        _ < (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) := hmul
    exact (lt_of_mul_lt_mul_left hmul' hden.le).le
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp htarget
  refine ⟨T₀, ?_⟩
  intro T hT
  have hmain := hT₀ T hT
  have hNnonneg : 0 ≤ (Z.N T (2 * T) : ℝ) := by positivity
  nlinarith

/-! ## 4. Exact terminal specializations -/

private theorem formula21_moments_8686 :
    formula21Moment 2 Terminal8686.mu Terminal8686.width = Terminal8686.m2 ∧
    formula21Moment 3 Terminal8686.mu Terminal8686.width = Terminal8686.m3 ∧
    formula21Moment 4 Terminal8686.mu Terminal8686.width = Terminal8686.m4 := by
  constructor
  · simp only [formula21Moment, Terminal8686.m2, topHatM2]
    rw [TopHatMoments.formula21M2Integral_eq
      (by norm_num [Terminal8686.width]) (by norm_num [Terminal8686.width])]
  · constructor
    · simp only [formula21Moment, Terminal8686.m3, topHatM3]
      rw [TopHatMoments.formula21M3Integral_eq
        (by norm_num [Terminal8686.width]) (by norm_num [Terminal8686.width])]
    · simp only [formula21Moment, Terminal8686.m4, topHatM4]
      rw [TopHatMoments.formula21M4Integral_eq
        (by norm_num [Terminal8686.width]) (by norm_num [Terminal8686.width])]

private theorem formula21_moments_9506 :
    formula21Moment 2 Terminal9506.mu Terminal9506.width = Terminal9506.m2 ∧
    formula21Moment 3 Terminal9506.mu Terminal9506.width = Terminal9506.m3 ∧
    formula21Moment 4 Terminal9506.mu Terminal9506.width = Terminal9506.m4 := by
  constructor
  · simp only [formula21Moment, Terminal9506.m2, topHatM2]
    rw [TopHatMoments.formula21M2Integral_eq
      (by norm_num [Terminal9506.width]) (by norm_num [Terminal9506.width])]
  · constructor
    · simp only [formula21Moment, Terminal9506.m3, topHatM3]
      rw [TopHatMoments.formula21M3Integral_eq
        (by norm_num [Terminal9506.width]) (by norm_num [Terminal9506.width])]
    · simp only [formula21Moment, Terminal9506.m4, topHatM4]
      rw [TopHatMoments.formula21M4Integral_eq
        (by norm_num [Terminal9506.width]) (by norm_num [Terminal9506.width])]

theorem limitQuarticScore_8686 :
    limitQuarticScore Terminal8686.dual Terminal8686.mu Terminal8686.width =
      Terminal8686.AP := by
  obtain ⟨hm2, hm3, hm4⟩ := formula21_moments_8686
  rw [limitQuarticScore, show formula21Moment 1 Terminal8686.mu
    Terminal8686.width = 0 by rfl, hm2, hm3, hm4]
  simp only [mul_zero, add_zero, Terminal8686.AP]

theorem limitQuarticScore_9506 :
    limitQuarticScore Terminal9506.dual Terminal9506.mu Terminal9506.width =
      Terminal9506.AP := by
  obtain ⟨hm2, hm3, hm4⟩ := formula21_moments_9506
  rw [limitQuarticScore, show formula21Moment 1 Terminal9506.mu
    Terminal9506.width = 0 by rfl, hm2, hm3, hm4]
  simp only [mul_zero, add_zero, Terminal9506.AP]

theorem strict_transfer_8686 :
    (86855250 / 100000000 : ℝ) <
      ((4999 / 10000 : ℝ) *
          limitQuarticScore Terminal8686.dual (4999 / 10000) (89 / 100) +
          2 - Terminal8686.costUpper - Terminal8686.cap / 2) /
        (1 - Terminal8686.cap / 2) := by
  rw [show limitQuarticScore Terminal8686.dual (4999 / 10000) (89 / 100) =
    Terminal8686.AP by simpa only [Terminal8686.mu, Terminal8686.width] using
      limitQuarticScore_8686]
  have hden : 0 < 1 - Terminal8686.cap / 2 :=
    sub_pos.mpr Terminal8686.cap_slope
  have hden2 : 2 - Terminal8686.cap ≠ 0 := by linarith
  have hid :
      ((4999 / 10000 : ℝ) * Terminal8686.AP + 2 -
          Terminal8686.costUpper - Terminal8686.cap / 2) /
          (1 - Terminal8686.cap / 2) =
        2 - Terminal8686.costUpper + Terminal8686.fixedPoint := by
    rw [Terminal8686.fixedPoint, Terminal8686.mu]
    field_simp [hden.ne', hden2]
    ring
  rw [hid]
  exact Terminal8686.density_gt_frozen

theorem strict_transfer_9506 :
    (95063832187565 / 100000000000000 : ℝ) <
      ((4999 / 10000 : ℝ) *
          limitQuarticScore Terminal9506.dual (4999 / 10000) (83 / 100) +
          2 - Terminal9506.costUpper - Terminal9506.cap / 2) /
        (1 - Terminal9506.cap / 2) := by
  rw [show limitQuarticScore Terminal9506.dual (4999 / 10000) (83 / 100) =
    Terminal9506.AP by simpa only [Terminal9506.mu, Terminal9506.width] using
      limitQuarticScore_9506]
  have hden : 0 < 1 - Terminal9506.cap / 2 :=
    sub_pos.mpr Terminal9506.cap_slope
  have hden2 : 2 - Terminal9506.cap ≠ 0 := by linarith
  have hid :
      ((4999 / 10000 : ℝ) * Terminal9506.AP + 2 -
          Terminal9506.costUpper - Terminal9506.cap / 2) /
          (1 - Terminal9506.cap / 2) =
        2 - Terminal9506.costUpper + Terminal9506.fixedPoint := by
    rw [Terminal9506.fixedPoint, Terminal9506.mu]
    field_simp [hden.ne', hden2]
    ring
  rw [hid]
  exact Terminal9506.density_gt_frozen

/-- Support `14999/10000`: the three explicit analytic structures imply the
frozen R-8686 epsilon form. -/
theorem eps_transfer_8686
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family14999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : WeightedQuarticLimit Terminal8686.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((86855250 / 100000000 : ℝ) - ε) * (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  have hcost :
      profileSaturatedCost (14999 / 10000) QuarticWindowWitnesses.v8686 ≤
        Terminal8686.costUpper := by
    rw [profileSaturatedCost_v8686]
    exact QuarticWindowWitnesses.D8686_lt.le
  exact asymptotic_eps_transfer hRvM hfull hzero
    Terminal8686.dual hweighted Terminal8686.cap Terminal8686.costUpper
    (86855250 / 100000000) Terminal8686.dual_feasible
    Terminal8686.cap_slope hcost strict_transfer_8686

/-- Support `19999/10000`: the three explicit analytic structures imply the
frozen R-9506 epsilon form. -/
theorem eps_transfer_9506
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family19999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : WeightedQuarticLimit Terminal9506.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((95063832187565 / 100000000000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  have hcost :
      profileSaturatedCost (19999 / 10000) QuarticWindowWitnesses.v9506 ≤
        Terminal9506.costUpper := by
    rw [profileSaturatedCost_v9506]
    exact QuarticWindowWitnesses.D9506_lt.le
  exact asymptotic_eps_transfer hRvM hfull hzero
    Terminal9506.dual hweighted Terminal9506.cap Terminal9506.costUpper
    (95063832187565 / 100000000000000) Terminal9506.dual_feasible
    Terminal9506.cap_slope hcost strict_transfer_9506

theorem frozen_8657_lt_8686 :
    (865674254456636 / 1000000000000000 : ℝ) <
      86855250 / 100000000 := by
  norm_num

theorem frozen_9383_lt_9506 :
    (938313327050949 / 1000000000000000 : ℝ) <
      95063832187565 / 100000000000000 := by
  norm_num

/-- R-8657 follows monotonically from the stronger support-`14999/10000`
frozen transfer, with no additional analytic input. -/
theorem eps_transfer_8657
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family14999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : WeightedQuarticLimit Terminal8686.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((865674254456636 / 1000000000000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eps_transfer_8686 hRvM hfull hzero hweighted ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  have hstrong := hT₀ T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := by positivity
  nlinarith [frozen_8657_lt_8686]

/-- R-9383 follows monotonically from the stronger support-`19999/10000`
frozen transfer, with no additional analytic input. -/
theorem eps_transfer_9383
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z) {F : Family19999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : WeightedQuarticLimit Terminal9506.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((938313327050949 / 1000000000000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eps_transfer_9506 hRvM hfull hzero hweighted ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  have hstrong := hT₀ T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := by positivity
  nlinarith [frozen_9383_lt_9506]

/-! ## 5. Concrete zeta wrappers -/

private theorem zeta_N (T₁ T₂ : ℝ) :
    zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ :=
  zetaZeros_N zetaSeam T₁ T₂

private theorem zeta_N0s (T₁ T₂ : ℝ) :
    zetaZeroConfig.N0s T₁ T₂ = N0simple T₁ T₂ :=
  zetaZeros_N0s zetaSeam T₁ T₂

/-- Concrete-zeta R-8686 epsilon form.  Riemann--von Mangoldt and its local
count are discharged by the base repository; exactly the four per-support
structures remain explicit. -/
theorem zeta_eps_transfer_8686
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : WeightedQuarticLimit Terminal8686.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((86855250 / 100000000 : ℝ) - ε) * (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_8686 paperInputs_zeta.RvM hfull hzero hweighted)

/-- Concrete-zeta R-9506 epsilon form, conditional only on the three explicit
per-support structures. -/
theorem zeta_eps_transfer_9506
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : WeightedQuarticLimit Terminal9506.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((95063832187565 / 100000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_9506 paperInputs_zeta.RvM hfull hzero hweighted)

/-- Concrete-zeta R-8657, obtained monotonically from R-8686. -/
theorem zeta_eps_transfer_8657
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : WeightedQuarticLimit Terminal8686.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((865674254456636 / 1000000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_8657 paperInputs_zeta.RvM hfull hzero hweighted)

/-- Concrete-zeta R-9383, obtained monotonically from R-9506. -/
theorem zeta_eps_transfer_9383
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hweighted : WeightedQuarticLimit Terminal9506.dual F) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((938313327050949 / 1000000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_9383 paperInputs_zeta.RvM hfull hzero hweighted)

end QuarticTransfer
end Zeta85
end RH

end
