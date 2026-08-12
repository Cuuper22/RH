/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.QuarticTransfer

/-!
# Isometric block architecture

The frozen coordinate-block interface is allocation-inconsistent.  The finite
stability theorem, however, already works for every isometric compression.
This file exposes that strictly more flexible block object and proves that it
inherits the identical robust tail bound.
-/

open Filter Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace RH
namespace Zeta85
namespace IsometricBlock

open Zeta23 RHLinalg RobustStability

/-- A height-dependent isometry from a smaller block space into the complete
physical channel-column space.  Its columns may mix channels. -/
structure Data
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) where
  compression :
    ∀ T : ℝ, Matrix (Fin (F.dim T)) (Fin (F.blockDim T)) ℂ
  isometry :
    ∀ T : ℝ, (compression T)ᴴ * compression T = 1

/-- Compression of the literal enlarged-window matrix by the chosen
isometry. -/
def block
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F) (T : ℝ) :
    Matrix (Fin (F.blockDim T)) (Fin (F.blockDim T)) ℂ :=
  (C.compression T)ᴴ * F.A T * C.compression T

/-- The isometrically compressed block is Hermitian under the same literal
zero-side decomposition used by the coordinate block. -/
theorem block_isHermitian
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F) (hzero : StableZeroSide F) (T : ℝ) :
    (block C T).IsHermitian := by
  rw [block, hzero.truncated_decomposition T]
  exact isHermitian_conjTranspose_mul_mul
    (C.compression T)
    ((hzero.p_psd T).isHermitian.add (hzero.q_hermitian T))

/-- Centered spectral moment of the mixed-channel block. -/
def centeredMoment
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F) (k : ℕ) (T : ℝ) : ℝ :=
  rtrace ((block C T - 1) ^ k) / (F.blockDim T : ℝ)

/-- The exact robust stability inequality survives the mixed-channel block,
with precisely the same finite error budget as the coordinate block. -/
theorem robustTailBound_eventually
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F)
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F) :
    ∀ᶠ T in Filter.atTop,
      tailExcessSq (block_isHermitian C hzero T)
          (Z.s2 T + Z.p T) ≤
        (Z.s1 T : ℝ) -
          (2 - profileSaturatedCost σ v) *
            (Z.N T (2 * T) : ℝ) +
          2 * F.pTraceError T + 4 * F.traceError T +
            F.frobError T + 2 * (Assembly.NII Z T : ℝ) := by
  filter_upwards [hzero.simple_rank_bound, hzero.simple_trace_cap,
    hzero.bad_index_bound, hfull.trace_bound, hfull.frob_bound,
    eventually_ge_atTop (0 : ℝ)] with
      T hrank htraceP hposQ htraceA hfrobA hT
  have htraceA' :
      |rtrace (F.P T + F.Q T) -
          (Z.N T (2 * T) : ℝ)| ≤ F.traceError T := by
    simpa only [← hzero.truncated_decomposition T] using htraceA
  have hfrobA' :
      frobSq (F.P T + F.Q T) ≤
        profileSaturatedCost σ v *
          (Z.N T (2 * T) : ℝ) + F.frobError T := by
    simpa only [← hzero.truncated_decomposition T] using hfrobA
  have hrob :=
    RobustStability.robust_stability_inequality_isometricCompression_withCountError
      (hzero.p_psd T) (hzero.q_hermitian T)
      (C.compression T) (C.isometry T)
      hrank htraceP hposQ
      (core_count_le_dyadic_add_edge Z hT)
      htraceA' hfrobA'
  have hblock :
      block C T =
        (C.compression T)ᴴ * (F.P T + F.Q T) *
          C.compression T := by
    rw [block, hzero.truncated_decomposition T]
  rw [tailExcessSq_congr hblock
    (block_isHermitian C hzero T)
    (isHermitian_conjTranspose_mul_mul
      (C.compression T)
      ((hzero.p_psd T).isHermitian.add
        (hzero.q_hermitian T)))]
  exact hrob


/-- The terminal quartic evaluated on the first four centered moments of the
mixed-channel block. -/
def quarticScore
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (q : TrimmedMoment.Quartic) (C : Data F) (T : ℝ) : ℝ :=
  q.p0 + q.p1 * centeredMoment C 1 T +
    q.p2 * centeredMoment C 2 T +
    q.p3 * centeredMoment C 3 T +
    q.p4 * centeredMoment C 4 T

/-- Weak quartic duality applied directly to an isometrically compressed
block. -/
theorem scaled_quarticScore_le_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F) (hzero : StableZeroSide F)
    (q : TrimmedMoment.Quartic) (cap : ℝ)
    (hdual : TrimmedMoment.DualFeasible q cap)
    (T : ℝ) (hm : 0 < F.blockDim T) :
    (F.blockDim T : ℝ) * quarticScore q C T -
        (Z.s2 T + Z.p T : ℕ) * cap ≤
      tailExcessSq (block_isHermitian C hzero T)
        (Z.s2 T + Z.p T) := by
  let hB := block_isHermitian C hzero T
  have hmR : (0 : ℝ) < F.blockDim T := by
    exact_mod_cast hm
  have hinputs := spectral_headTrimmedMomentInputs
    (b := Z.s2 T + Z.p T) hB hm
  have hdualFinite := TrimmedMoment.finite_trimmed_quartic_dual q cap
    (centeredSpectrum hB)
    (uniformWeight (SpectralIndex (F.blockDim T)))
    (uniformRemoved
      (spectralHeadSet
        (Fintype.card (Fin (F.blockDim T)))
        (Z.s2 T + Z.p T)))
    (spectralMoment hB 1) (spectralMoment hB 2)
    (spectralMoment hB 3) (spectralMoment hB 4)
    (((Z.s2 T + Z.p T : ℕ) : ℝ) / F.blockDim T)
    hdual hinputs
  have hscaled :=
    mul_le_mul_of_nonneg_left hdualFinite hmR.le
  rw [spectral_residualTail_eq_tailExcessSq_div] at hscaled
  have hscore :
      q.p0 + q.p1 * spectralMoment hB 1 +
          q.p2 * spectralMoment hB 2 +
          q.p3 * spectralMoment hB 3 +
          q.p4 * spectralMoment hB 4 =
        quarticScore q C T := by
    simp only [quarticScore, centeredMoment,
      QuarticTransfer.spectralMoment_eq_centered_rtrace]
  rw [hscore] at hscaled
  calc
    (F.blockDim T : ℝ) * quarticScore q C T -
          (Z.s2 T + Z.p T : ℕ) * cap =
        (F.blockDim T : ℝ) *
          (quarticScore q C T -
            ((Z.s2 T + Z.p T : ℕ) : ℝ) /
              F.blockDim T * cap) := by
      field_simp [hmR.ne']
    _ ≤ (F.blockDim T : ℝ) *
        (tailExcessSq hB (Z.s2 T + Z.p T) /
          F.blockDim T) := hscaled
    _ = tailExcessSq (block_isHermitian C hzero T)
        (Z.s2 T + Z.p T) := by
      field_simp [hmR.ne']

/-- The exact finite affine bridge for an isometric mixed-channel block. -/
theorem finite_affine_bridge_at
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F) (hzero : StableZeroSide F)
    (q : TrimmedMoment.Quartic) (cap Dbar : ℝ)
    (hdual : TrimmedMoment.DualFeasible q cap)
    (hcap : cap / 2 ≤ 1)
    (hcost : profileSaturatedCost σ v ≤ Dbar)
    (T : ℝ) (hT : 0 ≤ T) (hm : 0 < F.blockDim T)
    (htail :
      tailExcessSq (block_isHermitian C hzero T)
          (Z.s2 T + Z.p T) ≤
        (Z.s1 T : ℝ) -
          (2 - profileSaturatedCost σ v) *
            (Z.N T (2 * T) : ℝ) +
          2 * F.pTraceError T + 4 * F.traceError T +
            F.frobError T + 2 * (Assembly.NII Z T : ℝ)) :
    (F.blockDim T : ℝ) * quarticScore q C T +
        (2 - Dbar - cap / 2) *
          (Z.N T (2 * T) : ℝ) ≤
      (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) +
        QuarticTransfer.transferError F T := by
  have hweak :=
    scaled_quarticScore_le_tail C hzero q cap hdual T hm
  have hcore := core_count_le_dyadic_add_edge Z hT
  have hs1Nat := Assembly.s1_le Z hT
  have hs1 : (Z.s1 T : ℝ) ≤
      (Z.N0s T (2 * T) : ℝ) +
        (Assembly.NII Z T : ℝ) := by
    exact_mod_cast hs1Nat
  have hcap0 : 0 ≤ cap / 2 :=
    div_nonneg hdual.cap_nonneg (by norm_num)
  have hremain : 0 ≤ 1 - cap / 2 :=
    sub_nonneg.mpr hcap
  have hcoreScaled :=
    mul_le_mul_of_nonneg_left hcore hcap0
  have hs1Scaled :=
    mul_le_mul_of_nonneg_left hs1 hremain
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := by
    positivity
  have hcostScaled :=
    mul_le_mul_of_nonneg_right hcost hN
  unfold QuarticTransfer.transferError
  nlinarith


/-- The one-sided asymptotic datum for the complete mixed-channel block.
Only the weighted terminal polynomial is retained; no separate convergence
of four moments and no coordinate allocation are required. -/
structure WeightedQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (q : TrimmedMoment.Quartic) (C : Data F) : Prop where
  block_dimension_pos :
    ∀ᶠ T in Filter.atTop, 0 < F.blockDim T
  eventually_gt :
    ∀ x : ℝ, x < μ * QuarticTransfer.limitQuarticScore q μ p →
      ∀ᶠ T in Filter.atTop,
        x < (F.blockDim T : ℝ) /
              (Z.N T (2 * T) : ℝ) * quarticScore q C T

/-- Eventual form of the finite affine bridge for an isometric block. -/
theorem finite_affine_bridge
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (C : Data F)
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (hblock : ∀ᶠ T in Filter.atTop, 0 < F.blockDim T)
    (q : TrimmedMoment.Quartic) (cap Dbar : ℝ)
    (hdual : TrimmedMoment.DualFeasible q cap)
    (hcap : cap / 2 ≤ 1)
    (hcost : profileSaturatedCost σ v ≤ Dbar) :
    ∀ᶠ T in Filter.atTop,
      (F.blockDim T : ℝ) * quarticScore q C T +
          (2 - Dbar - cap / 2) *
            (Z.N T (2 * T) : ℝ) ≤
        (1 - cap / 2) * (Z.N0s T (2 * T) : ℝ) +
          QuarticTransfer.transferError F T := by
  filter_upwards [robustTailBound_eventually C hfull hzero,
    hblock, eventually_ge_atTop (0 : ℝ)]
      with T htail hm hT
  exact finite_affine_bridge_at C hzero q cap Dbar hdual hcap
    hcost T hT hm htail

/-- The mixed-channel finite expression after division by the dyadic count
and the positive affine denominator. -/
def normalizedTransfer
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (q : TrimmedMoment.Quartic) (cap Dbar : ℝ)
    (C : Data F) (T : ℝ) : ℝ :=
  (((F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ)) *
        quarticScore q C T +
      (2 - Dbar - cap / 2) -
      QuarticTransfer.transferError F T /
        (Z.N T (2 * T) : ℝ)) /
    (1 - cap / 2)

/-- Generic finite-to-asymptotic transfer for a channel-mixing isometry.
This is the same exact density argument as the coordinate route, with the
impossible principal-block premise replaced throughout by the actual
isometrically compressed matrix. -/
theorem asymptotic_eps_transfer
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hRvM : RiemannVonMangoldt Z)
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : Data F)
    (q : TrimmedMoment.Quartic)
    (hweighted : WeightedQuarticLowerBound q C)
    (cap Dbar target : ℝ)
    (hdual : TrimmedMoment.DualFeasible q cap)
    (hcap : cap / 2 < 1)
    (hcost : profileSaturatedCost σ v ≤ Dbar)
    (hstrict : target <
      (μ * QuarticTransfer.limitQuarticScore q μ p +
          2 - Dbar - cap / 2) /
        (1 - cap / 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (target - ε) * (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  have hden : 0 < 1 - cap / 2 := sub_pos.mpr hcap
  have hstrict' :
      target * (1 - cap / 2) <
        μ * QuarticTransfer.limitQuarticScore q μ p +
          2 - Dbar - cap / 2 :=
    (lt_div_iff₀ hden).mp hstrict
  let δ : ℝ :=
    (μ * QuarticTransfer.limitQuarticScore q μ p +
        2 - Dbar - cap / 2 -
        target * (1 - cap / 2)) / 3
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  have hscore : ∀ᶠ T in Filter.atTop,
      μ * QuarticTransfer.limitQuarticScore q μ p - δ <
        (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
          quarticScore q C T :=
    hweighted.eventually_gt _ (by linarith)
  have herror0 :=
    (QuarticTransfer.transferError_small hRvM hfull hzero).
      tendsto_div_nhds_zero
  have herror : ∀ᶠ T in Filter.atTop,
      QuarticTransfer.transferError F T /
          (Z.N T (2 * T) : ℝ) < δ :=
    herror0.eventually (Iio_mem_nhds hδ)
  have hlower : ∀ᶠ T in Filter.atTop,
      target < normalizedTransfer q cap Dbar C T := by
    filter_upwards [hscore, herror] with T hscoreT herrorT
    rw [normalizedTransfer]
    apply (lt_div_iff₀ hden).2
    dsimp only [δ] at hscoreT herrorT
    linarith
  have hfinite := finite_affine_bridge C hfull hzero
    hweighted.block_dimension_pos q cap Dbar hdual
    hcap.le hcost
  have hNpos :=
    (Assembly.tendsto_N_atTop Z hRvM).eventually_gt_atTop 0
  have htarget : ∀ᶠ T in Filter.atTop,
      target * (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hlower, hfinite, hNpos]
      with T hlowerT hfiniteT hNT
    rw [normalizedTransfer] at hlowerT
    have hlowerDen := (lt_div_iff₀ hden).mp hlowerT
    have hrewrite :
        (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
              quarticScore q C T +
              (2 - Dbar - cap / 2) -
              QuarticTransfer.transferError F T /
                (Z.N T (2 * T) : ℝ) =
          ((F.blockDim T : ℝ) * quarticScore q C T +
              (2 - Dbar - cap / 2) *
                (Z.N T (2 * T) : ℝ) -
              QuarticTransfer.transferError F T) /
            (Z.N T (2 * T) : ℝ) := by
      field_simp [hNT.ne']
    rw [hrewrite] at hlowerDen
    have hlowerN := (lt_div_iff₀ hNT).mp hlowerDen
    have hmul :
        target * (1 - cap / 2) *
              (Z.N T (2 * T) : ℝ) <
          (1 - cap / 2) *
              (Z.N0s T (2 * T) : ℝ) := by
      linarith
    have hmul' :
        (1 - cap / 2) *
              (target * (Z.N T (2 * T) : ℝ)) <
          (1 - cap / 2) *
              (Z.N0s T (2 * T) : ℝ) := by
      calc
        (1 - cap / 2) *
              (target * (Z.N T (2 * T) : ℝ)) =
            target * (1 - cap / 2) *
              (Z.N T (2 * T) : ℝ) := by ring
        _ < (1 - cap / 2) *
              (Z.N0s T (2 * T) : ℝ) := hmul
    exact (lt_of_mul_lt_mul_left hmul' hden.le).le
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp htarget
  refine ⟨T₀, ?_⟩
  intro T hT
  have hmain := hT₀ T hT
  have hNnonneg : 0 ≤ (Z.N T (2 * T) : ℝ) := by
    positivity
  nlinarith

end IsometricBlock
end Zeta85
end RH

end
