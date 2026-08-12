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


/-! ## Exact terminal specializations -/

/-- Support 14999/10000: the isometric weighted statistic implies the
frozen R-8686 epsilon statement. -/
theorem eps_transfer_8686
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z)
    {F : Family14999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : Data F)
    (hweighted :
      WeightedQuarticLowerBound
        TrimmedMoment.Terminal8686.dual C) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((86855250 / 100000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  have hcost :
      profileSaturatedCost (14999 / 10000)
          QuarticWindowWitnesses.v8686 ≤
        TrimmedMoment.Terminal8686.costUpper := by
    rw [profileSaturatedCost_v8686]
    exact QuarticWindowWitnesses.D8686_lt.le
  exact asymptotic_eps_transfer hRvM hfull hzero C
    TrimmedMoment.Terminal8686.dual hweighted
    TrimmedMoment.Terminal8686.cap
    TrimmedMoment.Terminal8686.costUpper
    (86855250 / 100000000)
    TrimmedMoment.Terminal8686.dual_feasible
    TrimmedMoment.Terminal8686.cap_slope hcost
    QuarticTransfer.strict_transfer_8686

/-- Support 19999/10000: the isometric weighted statistic implies the
frozen R-9506 epsilon statement. -/
theorem eps_transfer_9506
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z)
    {F : Family19999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : Data F)
    (hweighted :
      WeightedQuarticLowerBound
        TrimmedMoment.Terminal9506.dual C) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((95063832187565 / 100000000000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  have hcost :
      profileSaturatedCost (19999 / 10000)
          QuarticWindowWitnesses.v9506 ≤
        TrimmedMoment.Terminal9506.costUpper := by
    rw [profileSaturatedCost_v9506]
    exact QuarticWindowWitnesses.D9506_lt.le
  exact asymptotic_eps_transfer hRvM hfull hzero C
    TrimmedMoment.Terminal9506.dual hweighted
    TrimmedMoment.Terminal9506.cap
    TrimmedMoment.Terminal9506.costUpper
    (95063832187565 / 100000000000000)
    TrimmedMoment.Terminal9506.dual_feasible
    TrimmedMoment.Terminal9506.cap_slope hcost
    QuarticTransfer.strict_transfer_9506

/-- R-8657 follows monotonically from the stronger mixed-channel
support-14999 transfer. -/
theorem eps_transfer_8657
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z)
    {F : Family14999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : Data F)
    (hweighted :
      WeightedQuarticLowerBound
        TrimmedMoment.Terminal8686.dual C) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((865674254456636 / 1000000000000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    eps_transfer_8686 hRvM hfull hzero C hweighted ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  have hstrong := hT₀ T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := by
    positivity
  nlinarith [QuarticTransfer.frozen_8657_lt_8686]

/-- R-9383 follows monotonically from the stronger mixed-channel
support-19999 transfer. -/
theorem eps_transfer_9383
    {Z : ZeroConfig} (hRvM : RiemannVonMangoldt Z)
    {F : Family19999 Z}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : Data F)
    (hweighted :
      WeightedQuarticLowerBound
        TrimmedMoment.Terminal9506.dual C) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((938313327050949 / 1000000000000000 : ℝ) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    eps_transfer_9506 hRvM hfull hzero C hweighted ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  have hstrong := hT₀ T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := by
    positivity
  nlinarith [QuarticTransfer.frozen_9383_lt_9506]

private theorem zeta_N (T₁ T₂ : ℝ) :
    zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ :=
  zetaZeros_N zetaSeam T₁ T₂

private theorem zeta_N0s (T₁ T₂ : ℝ) :
    zetaZeroConfig.N0s T₁ T₂ = N0simple T₁ T₂ :=
  zetaZeros_N0s zetaSeam T₁ T₂

theorem zeta_eps_transfer_8686
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : Data F)
    (hweighted :
      WeightedQuarticLowerBound
        TrimmedMoment.Terminal8686.dual C) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((86855250 / 100000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_8686 paperInputs_zeta.RvM hfull hzero C hweighted)

theorem zeta_eps_transfer_9506
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : Data F)
    (hweighted :
      WeightedQuarticLowerBound
        TrimmedMoment.Terminal9506.dual C) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((95063832187565 / 100000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_9506 paperInputs_zeta.RvM hfull hzero C hweighted)

theorem zeta_eps_transfer_8657
    {F : Family14999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : Data F)
    (hweighted :
      WeightedQuarticLowerBound
        TrimmedMoment.Terminal8686.dual C) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((865674254456636 / 1000000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_8657 paperInputs_zeta.RvM hfull hzero C hweighted)

theorem zeta_eps_transfer_9383
    {F : Family19999 zetaZeroConfig}
    (hfull : FullTraceLimits F) (hzero : StableZeroSide F)
    (C : Data F)
    (hweighted :
      WeightedQuarticLowerBound
        TrimmedMoment.Terminal9506.dual C) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((938313327050949 / 1000000000000000 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  simpa only [zeta_N, zeta_N0s] using
    (eps_transfer_9383 paperInputs_zeta.RvM hfull hzero C hweighted)


/-! ## Sum-first coordinates for mixed blocks -/

/-- Combine the block-size term and four raw centered traces before the
single dyadic normalization. -/
def quarticTraceNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (q : TrimmedMoment.Quartic) (C : Data F) (T : ℝ) : ℝ :=
  q.p0 * (F.blockDim T : ℝ) +
    q.p1 * rtrace ((block C T - 1) ^ 1) +
    q.p2 * rtrace ((block C T - 1) ^ 2) +
    q.p3 * rtrace ((block C T - 1) ^ 3) +
    q.p4 * rtrace ((block C T - 1) ^ 4)

/-- The same numerator after shifting the certificate from centered to raw
eigenvalue coordinates. -/
def uncenteredQuarticTraceNumerator
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (q : TrimmedMoment.Quartic) (C : Data F) (T : ℝ) : ℝ :=
  let u := QuarticTransfer.uncenteredQuartic q
  u.p0 * (F.blockDim T : ℝ) +
    u.p1 * rtrace ((block C T) ^ 1) +
    u.p2 * rtrace ((block C T) ^ 2) +
    u.p3 * rtrace ((block C T) ^ 3) +
    u.p4 * rtrace ((block C T) ^ 4)

theorem blockDim_mul_quarticScore
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic} {C : Data F} {T : ℝ}
    (hm : 0 < F.blockDim T) :
    (F.blockDim T : ℝ) * quarticScore q C T =
      quarticTraceNumerator q C T := by
  have hm0 : (F.blockDim T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  simp only [quarticScore, quarticTraceNumerator, centeredMoment]
  field_simp [hm0]
  <;> ring

/-- Centering the mixed block and shifting the terminal polynomial are the
same finite operation. -/
theorem quarticTraceNumerator_eq_uncentered
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic} {C : Data F} {T : ℝ} :
    quarticTraceNumerator q C T =
      uncenteredQuarticTraceNumerator q C T := by
  have hone :
      rtrace
          (1 : Matrix (Fin (F.blockDim T))
            (Fin (F.blockDim T)) ℂ) =
        (F.blockDim T : ℝ) := by
    simp [rtrace, Matrix.trace]
  rw [quarticTraceNumerator, uncenteredQuarticTraceNumerator,
    QuarticTransfer.uncenteredQuartic]
  rw [show (block C T - 1) ^ 1 =
      block C T ^ 1 - 1 by noncomm_ring]
  rw [show (block C T - 1) ^ 2 =
      block C T ^ 2 - (block C T + block C T) + 1 by
        noncomm_ring]
  rw [show (block C T - 1) ^ 3 =
      block C T ^ 3 -
        (block C T ^ 2 + block C T ^ 2 + block C T ^ 2) +
        (block C T + block C T + block C T) - 1 by
          noncomm_ring]
  rw [show (block C T - 1) ^ 4 =
      block C T ^ 4 -
        (block C T ^ 3 + block C T ^ 3 +
          block C T ^ 3 + block C T ^ 3) +
        (block C T ^ 2 + block C T ^ 2 +
          block C T ^ 2 + block C T ^ 2 +
          block C T ^ 2 + block C T ^ 2) -
        (block C T + block C T + block C T + block C T) +
        1 by
          noncomm_ring]
  simp only [rtrace_add, rtrace_sub, hone]
  ring

/-- The raw mixed-block numerator is the generic explicit cyclic trace
functional already used by the zero-kernel route. -/
theorem uncenteredQuarticTraceNumerator_eq_cyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic} {C : Data F} {T : ℝ} :
    uncenteredQuarticTraceNumerator q C T =
      QuarticTransfer.cyclicQuarticTraceNumerator q
        (block C T) := by
  simp only [uncenteredQuarticTraceNumerator,
    QuarticTransfer.cyclicQuarticTraceNumerator,
    QuarticTransfer.rtrace_pow_one_eq_cyclic,
    QuarticTransfer.rtrace_pow_two_eq_cyclic,
    QuarticTransfer.rtrace_pow_three_eq_cyclic,
    QuarticTransfer.rtrace_pow_four_eq_cyclic]

theorem weightedQuarticScore_eq_cyclic
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    {q : TrimmedMoment.Quartic} {C : Data F} {T : ℝ}
    (hm : 0 < F.blockDim T) :
    (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
        quarticScore q C T =
      QuarticTransfer.cyclicQuarticTraceNumerator q
          (block C T) /
        (Z.N T (2 * T) : ℝ) := by
  calc
    (F.blockDim T : ℝ) / (Z.N T (2 * T) : ℝ) *
          quarticScore q C T =
        ((F.blockDim T : ℝ) * quarticScore q C T) /
          (Z.N T (2 * T) : ℝ) := by
      ring
    _ = quarticTraceNumerator q C T /
          (Z.N T (2 * T) : ℝ) := by
      rw [blockDim_mul_quarticScore hm]
    _ = uncenteredQuarticTraceNumerator q C T /
          (Z.N T (2 * T) : ℝ) := by
      rw [quarticTraceNumerator_eq_uncentered]
    _ = QuarticTransfer.cyclicQuarticTraceNumerator q
          (block C T) /
          (Z.N T (2 * T) : ℝ) := by
      rw [uncenteredQuarticTraceNumerator_eq_cyclic]

end IsometricBlock
end Zeta85
end RH

end
