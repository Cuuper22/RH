/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.ComplexAliasBridge
import RH.Zeta85.Discharge.VirtualChannelMixer

/-!
# Aggregate cancellation of complex Poisson aliases

Individual physical or virtual windows need not kill their nonzero Poisson
translations.  This module changes the order of summation: channel aliases
are added first, and only their aggregate is required to cancel.
-/

open Complex MeasureTheory Real Set
open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace AggregateComplexAlias

open Zeta23

/-- Complete frequency lattices added across a finite channel family. -/
def aggregateVirtualFrequencyPairSum
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (f : ι → ℝ → ℝ) (z z' : ℂ) : ℂ :=
  ∑ r : ι,
    ComplexAliasBridge.virtualFrequencyPairSum T L (f r) z z'

/-- Spatial alias lattices added across the channels before cancellation. -/
def aggregateVirtualAliasSum
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (f : ι → ℝ → ℝ) (z z' : ℂ) : ℂ :=
  ∑ r : ι,
    ComplexAliasBridge.virtualAliasSum T L (f r) z z'

/-- Aggregate of the zero spatial translations. -/
def aggregateVirtualZeroTranslation
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (f : ι → ℝ → ℝ) (z z' : ℂ) : ℂ :=
  ∑ r : ι,
    ComplexAliasBridge.virtualComplexAliasTerm T L (f r) z z' 0

/-- The summed channel energy transform. -/
def aggregateVirtualEnergyIntegral
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (z z' : ℂ) : ℂ :=
  ∑ r : ι,
    ∫ u : ℝ,
      (f r u : ℂ) * f r u *
        Complex.exp (Complex.I * (z - z') * (u : ℂ))

/-- The exact remaining condition after the channel sum is formed: nonzero
aliases may be nonzero channel by channel, but their total must vanish. -/
structure AggregateAliasCancellation
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (f : ι → ℝ → ℝ) : Prop where
  nonzero_sum_eq_zero :
    ∀ z z' : ℂ,
      (∑ r : ι,
        ∑' m : {m : ℤ // m ≠ 0},
          ComplexAliasBridge.virtualComplexAliasTerm
            T L (f r) z z' m) = 0

/-- Without any support-gap assumption, one channel's alias lattice splits
into its zero translation and the sum of all nonzero translations. -/
theorem virtualAliasSum_eq_zero_add_nonzero
    (T L Λ : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (heven : ∀ u, f (-u) = f u)
    (z z' : ℂ) :
    ComplexAliasBridge.virtualAliasSum T L f z z' =
      ComplexAliasBridge.virtualComplexAliasTerm T L f z z' 0 +
        ∑' m : {m : ℤ // m ≠ 0},
          ComplexAliasBridge.virtualComplexAliasTerm T L f z z' m := by
  have hL0 : (L : ℂ) ≠ 0 := by
    exact_mod_cast hL.ne'
  have hscaled :=
    (ComplexAliasBridge.hasSum_virtualComplexAlias
      T L Λ f hL hΛ hsmooth hsupp heven z z').1
  have hsum :
      Summable (fun m : ℤ =>
        ComplexAliasBridge.virtualComplexAliasTerm T L f z z' m) :=
    (summable_mul_left_iff hL0).1 hscaled
  unfold ComplexAliasBridge.virtualAliasSum
  simpa only [Finset.sum_singleton, Finset.mem_singleton] using
    (hsum.sum_add_tsum_subtype_compl ({0} : Finset ℤ)).symm

/-- Poisson summation is linear across the finite channel family. -/
theorem aggregateVirtualFrequencyPairSum_eq_period_mul_aliasSum
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (Λ : ι → ℝ) (f : ι → ℝ → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ r, 0 ≤ Λ r)
    (hsmooth : ∀ r, ContDiff ℝ 2 (fun u => (f r u : ℂ)))
    (hsupp : ∀ r u, Λ r < |u| → f r u = 0)
    (heven : ∀ r u, f r (-u) = f r u)
    (z z' : ℂ) :
    aggregateVirtualFrequencyPairSum T L f z z' =
      (L : ℂ) * aggregateVirtualAliasSum T L f z z' := by
  unfold aggregateVirtualFrequencyPairSum aggregateVirtualAliasSum
  calc
    (∑ r : ι,
      ComplexAliasBridge.virtualFrequencyPairSum
        T L (f r) z z') =
        ∑ r : ι, (L : ℂ) *
          ComplexAliasBridge.virtualAliasSum T L (f r) z z' := by
      apply Finset.sum_congr rfl
      intro r _
      exact ComplexAliasBridge.virtualFrequencyPairSum_eq_period_mul_aliasSum
        T L (Λ r) (f r) hL (hΛ r) (hsmooth r)
        (hsupp r) (heven r) z z'
    _ = (L : ℂ) *
        ∑ r : ι,
          ComplexAliasBridge.virtualAliasSum T L (f r) z z' := by
      rw [Finset.mul_sum]

/-- Aggregate nonzero-alias cancellation leaves exactly the summed zero
translations, even when no channel cancels separately. -/
theorem aggregateVirtualAliasSum_eq_zeroTranslation
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (Λ : ι → ℝ) (f : ι → ℝ → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ r, 0 ≤ Λ r)
    (hsmooth : ∀ r, ContDiff ℝ 2 (fun u => (f r u : ℂ)))
    (hsupp : ∀ r u, Λ r < |u| → f r u = 0)
    (heven : ∀ r u, f r (-u) = f r u)
    (hcancel : AggregateAliasCancellation T L f)
    (z z' : ℂ) :
    aggregateVirtualAliasSum T L f z z' =
      aggregateVirtualZeroTranslation T L f z z' := by
  unfold aggregateVirtualAliasSum aggregateVirtualZeroTranslation
  calc
    (∑ r : ι,
      ComplexAliasBridge.virtualAliasSum T L (f r) z z') =
        ∑ r : ι,
          (ComplexAliasBridge.virtualComplexAliasTerm
              T L (f r) z z' 0 +
            ∑' m : {m : ℤ // m ≠ 0},
              ComplexAliasBridge.virtualComplexAliasTerm
                T L (f r) z z' m) := by
      apply Finset.sum_congr rfl
      intro r _
      exact virtualAliasSum_eq_zero_add_nonzero
        T L (Λ r) (f r) hL (hΛ r) (hsmooth r)
        (hsupp r) (heven r) z z'
    _ = (∑ r : ι,
          ComplexAliasBridge.virtualComplexAliasTerm
            T L (f r) z z' 0) +
        ∑ r : ι,
          ∑' m : {m : ℤ // m ≠ 0},
            ComplexAliasBridge.virtualComplexAliasTerm
              T L (f r) z z' m := by
      rw [Finset.sum_add_distrib]
    _ = ∑ r : ι,
        ComplexAliasBridge.virtualComplexAliasTerm
          T L (f r) z z' 0 := by
      rw [hcancel.nonzero_sum_eq_zero z z', add_zero]

/-- The aggregate zero translation is the sum of the channel energy
transforms. -/
theorem aggregateVirtualZeroTranslation_eq_energyIntegral
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (f : ι → ℝ → ℝ) (z z' : ℂ) :
    aggregateVirtualZeroTranslation T L f z z' =
      aggregateVirtualEnergyIntegral f z z' := by
  unfold aggregateVirtualZeroTranslation aggregateVirtualEnergyIntegral
  apply Finset.sum_congr rfl
  intro r _
  exact ComplexAliasBridge.virtualComplexAliasTerm_zero
    T L (f r) z z'

/-- Main multichannel Poisson identity: summing channels first permits exact
collective alias cancellation. -/
theorem aggregateVirtualFrequencyPairSum_eq_energyIntegral
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (Λ : ι → ℝ) (f : ι → ℝ → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ r, 0 ≤ Λ r)
    (hsmooth : ∀ r, ContDiff ℝ 2 (fun u => (f r u : ℂ)))
    (hsupp : ∀ r u, Λ r < |u| → f r u = 0)
    (heven : ∀ r u, f r (-u) = f r u)
    (hcancel : AggregateAliasCancellation T L f)
    (z z' : ℂ) :
    aggregateVirtualFrequencyPairSum T L f z z' =
      (L : ℂ) * aggregateVirtualEnergyIntegral f z z' := by
  rw [aggregateVirtualFrequencyPairSum_eq_period_mul_aliasSum
    T L Λ f hL hΛ hsmooth hsupp heven z z']
  rw [aggregateVirtualAliasSum_eq_zeroTranslation
    T L Λ f hL hΛ hsmooth hsupp heven hcancel z z']
  rw [aggregateVirtualZeroTranslation_eq_energyIntegral]

/-- Reciprocal-period normalization again cancels the common channel period,
now after collective rather than channelwise alias cancellation. -/
theorem aggregateVirtualNormalizedFrequencyPairSum_eq_energyIntegral
    {ι : Type*} [Fintype ι]
    (fullLength T L : ℝ) (Λ : ι → ℝ) (f : ι → ℝ → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ r, 0 ≤ Λ r)
    (hsmooth : ∀ r, ContDiff ℝ 2 (fun u => (f r u : ℂ)))
    (hsupp : ∀ r u, Λ r < |u| → f r u = 0)
    (heven : ∀ r u, f r (-u) = f r u)
    (hcancel : AggregateAliasCancellation T L f)
    (z z' : ℂ) :
    (fullLength : ℂ) / (L : ℂ) *
        aggregateVirtualFrequencyPairSum T L f z z' =
      (fullLength : ℂ) *
        aggregateVirtualEnergyIntegral f z z' := by
  have hL0 : (L : ℂ) ≠ 0 := by
    exact_mod_cast hL.ne'
  rw [aggregateVirtualFrequencyPairSum_eq_energyIntegral
    T L Λ f hL hΛ hsmooth hsupp heven hcancel z z']
  field_simp [hL0]

/-! ## Constructors for collective cancellation -/

/-- Termwise collective cancellation implies the summed-tsum cancellation
interface.  Absolute summability is supplied by the same compact-smooth
Poisson theorem used for the individual channels. -/
theorem aggregateAliasCancellation_of_termwise
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (Λ : ι → ℝ) (f : ι → ℝ → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ r, 0 ≤ Λ r)
    (hsmooth : ∀ r, ContDiff ℝ 2 (fun u => (f r u : ℂ)))
    (hsupp : ∀ r u, Λ r < |u| → f r u = 0)
    (heven : ∀ r u, f r (-u) = f r u)
    (hterm : ∀ (z z' : ℂ) (m : {m : ℤ // m ≠ 0}),
      (∑ r : ι,
        ComplexAliasBridge.virtualComplexAliasTerm
          T L (f r) z z' m) = 0) :
    AggregateAliasCancellation T L f := by
  refine ⟨?_⟩
  intro z z'
  have hL0 : (L : ℂ) ≠ 0 := by
    exact_mod_cast hL.ne'
  have hsummable (r : ι) :
      Summable (fun m : {m : ℤ // m ≠ 0} =>
        ComplexAliasBridge.virtualComplexAliasTerm
          T L (f r) z z' m) := by
    have hscaled :=
      (ComplexAliasBridge.hasSum_virtualComplexAlias
        T L (Λ r) (f r) hL (hΛ r) (hsmooth r)
        (hsupp r) (heven r) z z').1
    have hfull :
        Summable (fun m : ℤ =>
          ComplexAliasBridge.virtualComplexAliasTerm
            T L (f r) z z' m) :=
      (summable_mul_left_iff hL0).1 hscaled
    exact hfull.comp_injective Subtype.val_injective
  have hHas :
      HasSum
        (fun m : {m : ℤ // m ≠ 0} =>
          ∑ r : ι,
            ComplexAliasBridge.virtualComplexAliasTerm
              T L (f r) z z' m)
        (∑ r : ι,
          ∑' m : {m : ℤ // m ≠ 0},
            ComplexAliasBridge.virtualComplexAliasTerm
              T L (f r) z z' m) := by
    simpa using
      (hasSum_sum (s := (Finset.univ : Finset ι))
        (fun r _ => (hsummable r).hasSum))
  calc
    (∑ r : ι,
      ∑' m : {m : ℤ // m ≠ 0},
        ComplexAliasBridge.virtualComplexAliasTerm
          T L (f r) z z' m) =
        ∑' m : {m : ℤ // m ≠ 0},
          ∑ r : ι,
            ComplexAliasBridge.virtualComplexAliasTerm
              T L (f r) z z' m :=
      hHas.tsum_eq.symm
    _ = 0 := by
      have hzero :
          (fun m : {m : ℤ // m ≠ 0} =>
            ∑ r : ι,
              ComplexAliasBridge.virtualComplexAliasTerm
                T L (f r) z z' m) = 0 := by
        funext m
        exact hterm z z' m
      rw [hzero]
      exact tsum_zero

/-- It is enough to cancel the summed shifted overlap integrals.  The
translation-dependent exponential is common to every channel and factors
out after the channel sum is taken. -/
theorem aggregateAliasCancellation_of_shiftIntegrals
    {ι : Type*} [Fintype ι]
    (T L : ℝ) (Λ : ι → ℝ) (f : ι → ℝ → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ r, 0 ≤ Λ r)
    (hsmooth : ∀ r, ContDiff ℝ 2 (fun u => (f r u : ℂ)))
    (hsupp : ∀ r u, Λ r < |u| → f r u = 0)
    (heven : ∀ r u, f r (-u) = f r u)
    (hshift : ∀ (z z' : ℂ) (m : ℤ), m ≠ 0 →
      (∑ r : ι,
        ∫ u : ℝ,
          (f r u : ℂ) * f r (u - (m : ℝ) * L) *
            Complex.exp
              (Complex.I * (z - z') * (u : ℂ))) = 0) :
    AggregateAliasCancellation T L f := by
  apply aggregateAliasCancellation_of_termwise
    T L Λ f hL hΛ hsmooth hsupp heven
  intro z z' m
  unfold ComplexAliasBridge.virtualComplexAliasTerm
  calc
    (∑ r : ι,
      Complex.exp
          (Complex.I * (z' - T) * (m : ℝ) * L) *
        ∫ u : ℝ,
          (f r u : ℂ) * f r (u - (m : ℝ) * L) *
            Complex.exp
              (Complex.I * (z - z') * (u : ℂ))) =
        Complex.exp
            (Complex.I * (z' - T) * (m : ℝ) * L) *
          ∑ r : ι,
            ∫ u : ℝ,
              (f r u : ℂ) * f r (u - (m : ℝ) * L) *
                Complex.exp
                  (Complex.I * (z - z') * (u : ℂ)) := by
      rw [Finset.mul_sum]
    _ = 0 := by
      rw [hshift z z' m m.property, mul_zero]

/-! ## Orthogonal synthesis produces collective cancellation -/

/-- If the complete channel overlap vanishes pointwise after channels are
summed, then every nonzero aggregate complex alias vanishes. -/
theorem aggregateAliasCancellation_of_pointwiseOverlap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T L : ℝ) (Λ : ι → ℝ) (f : ι → ℝ → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ r, 0 ≤ Λ r)
    (hsmooth : ∀ r, ContDiff ℝ 2 (fun u => (f r u : ℂ)))
    (hsupp : ∀ r u, Λ r < |u| → f r u = 0)
    (heven : ∀ r u, f r (-u) = f r u)
    (hInt : ∀ (r : ι) (z z' : ℂ) (m : ℤ), m ≠ 0 →
      Integrable
        (fun u : ℝ =>
          (f r u : ℂ) * f r (u - (m : ℝ) * L) *
            Complex.exp
              (Complex.I * (z - z') * (u : ℂ))))
    (hpoint : ∀ (m : ℤ), m ≠ 0 → ∀ u : ℝ,
      (∑ r : ι, f r u * f r (u - (m : ℝ) * L)) = 0) :
    AggregateAliasCancellation T L f := by
  apply aggregateAliasCancellation_of_shiftIntegrals
    T L Λ f hL hΛ hsmooth hsupp heven
  intro z z' m hm
  calc
    (∑ r : ι,
      ∫ u : ℝ,
        (f r u : ℂ) * f r (u - (m : ℝ) * L) *
          Complex.exp
            (Complex.I * (z - z') * (u : ℂ))) =
        ∫ u : ℝ,
          ∑ r : ι,
            (f r u : ℂ) * f r (u - (m : ℝ) * L) *
              Complex.exp
                (Complex.I * (z - z') * (u : ℂ)) := by
      rw [integral_finsetSum]
      intro r _
      exact hInt r z z' m hm
    _ = 0 := by
      have hfun :
          (fun u : ℝ =>
            ∑ r : ι,
              (f r u : ℂ) * f r (u - (m : ℝ) * L) *
                Complex.exp
                  (Complex.I * (z - z') * (u : ℂ))) = 0 := by
        funext u
        rw [← Finset.sum_mul]
        have hp := congrArg (fun x : ℝ => (x : ℂ))
          (hpoint m hm u)
        push_cast at hp
        simpa [hp]
      rw [hfun]
      simp

/-- Orthogonal synthesis is the concrete mechanism for collective
cancellation.  No physical channel is required to have zero aliases:
Parseval is applied to the whole physical-channel sum first. -/
theorem aggregateAliasCancellation_orthogonalSynthesis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : VirtualChannelMixer.Data ι)
    (T L : ℝ) (Λ : ι → ℝ) (virtual : ι → ℝ → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ j, 0 ≤ Λ j)
    (hsmooth : ∀ j,
      ContDiff ℝ 2
        (fun u =>
          (VirtualChannelMixer.synthesize C virtual j u : ℂ)))
    (hsupp : ∀ j u, Λ j < |u| →
      VirtualChannelMixer.synthesize C virtual j u = 0)
    (heven : ∀ j u,
      VirtualChannelMixer.synthesize C virtual j (-u) =
        VirtualChannelMixer.synthesize C virtual j u)
    (hInt : ∀ (j : ι) (z z' : ℂ) (m : ℤ), m ≠ 0 →
      Integrable
        (fun u : ℝ =>
          (VirtualChannelMixer.synthesize C virtual j u : ℂ) *
            VirtualChannelMixer.synthesize C virtual j
              (u - (m : ℝ) * L) *
            Complex.exp
              (Complex.I * (z - z') * (u : ℂ))))
    (hvirtual : ∀ (r : ι) (m : ℤ), m ≠ 0 → ∀ u : ℝ,
      virtual r u * virtual r (u - (m : ℝ) * L) = 0) :
    AggregateAliasCancellation T L
      (VirtualChannelMixer.synthesize C virtual) := by
  apply aggregateAliasCancellation_of_pointwiseOverlap
    T L Λ (VirtualChannelMixer.synthesize C virtual)
    hL hΛ hsmooth hsupp heven hInt
  intro m hm u
  exact VirtualChannelMixer.aggregate_shift_overlap_eq_zero
    C virtual u ((m : ℝ) * L) (fun r => hvirtual r m hm u)

/-- A strict sub-period support interval for each virtual channel provides the
translated-overlap hypothesis automatically for every nonzero integer shift. -/
theorem aggregateAliasCancellation_orthogonalSynthesis_of_intervalSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : VirtualChannelMixer.Data ι)
    (T L : ℝ) (Λ : ι → ℝ) (virtual : ι → ℝ → ℝ)
    (a b : ι → ℝ)
    (hL : 0 < L)
    (hΛ : ∀ j, 0 ≤ Λ j)
    (hsmooth : ∀ j,
      ContDiff ℝ 2
        (fun u =>
          (VirtualChannelMixer.synthesize C virtual j u : ℂ)))
    (hsuppPhysical : ∀ j u, Λ j < |u| →
      VirtualChannelMixer.synthesize C virtual j u = 0)
    (heven : ∀ j u,
      VirtualChannelMixer.synthesize C virtual j (-u) =
        VirtualChannelMixer.synthesize C virtual j u)
    (hInt : ∀ (j : ι) (z z' : ℂ) (m : ℤ), m ≠ 0 →
      Integrable
        (fun u : ℝ =>
          (VirtualChannelMixer.synthesize C virtual j u : ℂ) *
            VirtualChannelMixer.synthesize C virtual j
              (u - (m : ℝ) * L) *
            Complex.exp
              (Complex.I * (z - z') * (u : ℂ))))
    (hsuppVirtual : ∀ r : ι, ∀ x : ℝ,
      virtual r x ≠ 0 → a r ≤ x ∧ x ≤ b r)
    (hwidth : ∀ r : ι, b r - a r < L) :
    AggregateAliasCancellation T L
      (VirtualChannelMixer.synthesize C virtual) := by
  apply aggregateAliasCancellation_orthogonalSynthesis
    C T L Λ virtual hL hΛ hsmooth hsuppPhysical heven hInt
  intro r m hm u
  apply VirtualChannelMixer.self_shift_overlap_eq_zero
    (virtual r) (a r) (b r) u ((m : ℝ) * L)
    (hsuppVirtual r)
  have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  calc
    b r - a r < L := hwidth r
    _ = 1 * L := by ring
    _ ≤ |(m : ℝ)| * L :=
      mul_le_mul_of_nonneg_right hmabs hL.le
    _ = |(m : ℝ) * L| := by
      rw [abs_mul, abs_of_pos hL]

/-! ## Virtual regularity generates every physical analytic clause -/

/-- A smooth compactly supported real window has an integrable complex
shift-overlap against every exponential phase. -/
theorem integrable_complexShiftOverlap
    (f : ℝ → ℝ) (Λ h : ℝ)
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (phase : ℂ) :
    Integrable
      (fun u : ℝ =>
        (f u : ℂ) * f (u - h) *
          Complex.exp (phase * (u : ℂ))) := by
  have hcontinuous :
      Continuous
        (fun u : ℝ =>
          (f u : ℂ) * f (u - h) *
            Complex.exp (phase * (u : ℂ))) :=
    (hsmooth.continuous.mul
      (hsmooth.continuous.comp
        (continuous_id.sub continuous_const))).mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))
  have hcompactWindow :
      HasCompactSupport (fun u : ℝ => (f u : ℂ)) := by
    refine HasCompactSupport.intro
      (K := Icc (-Λ) Λ) isCompact_Icc ?_
    intro u hu
    have habs : Λ < |u| := by
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu
      · rw [abs_of_neg
          (lt_of_lt_of_le hu (neg_nonpos.mpr hΛ))]
        linarith
      · rw [abs_of_pos (lt_of_le_of_lt hΛ hu)]
        exact hu
    simp [hsupp u habs]
  have hcompact :
      HasCompactSupport
        (fun u : ℝ =>
          (f u : ℂ) * f (u - h) *
            Complex.exp (phase * (u : ℂ))) := by
    apply hcompactWindow.mono
    intro u hu
    change
      (f u : ℂ) * f (u - h) *
          Complex.exp (phase * (u : ℂ)) ≠ 0 at hu
    change (f u : ℂ) ≠ 0
    intro hzero
    apply hu
    simp [hzero]
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

/-- Smooth, even, compact virtual channels with strict sub-period interval
support synthesize physical channels whose complex aliases cancel
collectively.  All physical smoothness, support, evenness, and integrability
premises are derived inside the theorem. -/
theorem aggregateAliasCancellation_of_virtualWindowSystem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : VirtualChannelMixer.Data ι)
    (T L Λ : ℝ) (virtual : ι → ℝ → ℝ)
    (a b : ι → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmoothVirtual : ∀ r,
      ContDiff ℝ 2 (fun u => (virtual r u : ℂ)))
    (hsuppVirtualCommon : ∀ r u,
      Λ < |u| → virtual r u = 0)
    (hevenVirtual : ∀ r u,
      virtual r (-u) = virtual r u)
    (hsuppVirtualInterval : ∀ r : ι, ∀ x : ℝ,
      virtual r x ≠ 0 → a r ≤ x ∧ x ≤ b r)
    (hwidth : ∀ r : ι, b r - a r < L) :
    AggregateAliasCancellation T L
      (VirtualChannelMixer.synthesize C virtual) := by
  apply aggregateAliasCancellation_orthogonalSynthesis_of_intervalSupport
    C T L (fun _ => Λ) virtual a b hL
  · intro j
    exact hΛ
  · intro j
    simp only [VirtualChannelMixer.synthesize]
    push_cast
    apply ContDiff.sum
    intro r _
    exact contDiff_const.mul (hsmoothVirtual r)
  · intro j u hu
    exact VirtualChannelMixer.synthesize_eq_zero
      C virtual j u (fun r => hsuppVirtualCommon r u hu)
  · intro j u
    unfold VirtualChannelMixer.synthesize
    apply Finset.sum_congr rfl
    intro r _
    rw [hevenVirtual r u]
  · intro j z z' m hm
    exact integrable_complexShiftOverlap
      (VirtualChannelMixer.synthesize C virtual j)
      Λ ((m : ℝ) * L) hΛ
      (by
        simp only [VirtualChannelMixer.synthesize]
        push_cast
        apply ContDiff.sum
        intro r _
        exact contDiff_const.mul (hsmoothVirtual r))
      (fun u hu =>
        VirtualChannelMixer.synthesize_eq_zero
          C virtual j u (fun r => hsuppVirtualCommon r u hu))
      (Complex.I * (z - z'))
  · exact hsuppVirtualInterval
  · exact hwidth

end AggregateComplexAlias
end Zeta85
end RH

end
