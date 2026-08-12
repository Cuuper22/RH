/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.MeasureTheory.Integral.CompactlySupported
import RH.Zeta85.Inputs95
import RH.Zeta85.Discharge.QuarticTransfer
import Zeta23.Poisson.ComplexAlias

/-!
# Complex Poisson aliases for a quartic physical channel

This file identifies the general compact-window complex Poisson formula with
the exact alias term already defined on QuarticGramFamily.
-/

open Complex MeasureTheory Real Set
open scoped BigOperators

noncomputable section

namespace RH
namespace Zeta85
namespace ComplexAliasBridge

open Zeta23

/-- One shifted Poisson term is exactly the channel period times the
repository's existing complex alias term. -/
theorem shiftAlias_eq_period_mul_complexAlias
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T))
    (z z' : ℂ) (m : ℤ) :
    Poisson.complexPoissonShiftAliasTerm
        (fun u => (F.window T j u : ℂ))
        (F.period T j) T z z' m =
      (F.period T j : ℂ) * F.complexAliasTerm T z z' j m := by
  simp only [Poisson.complexPoissonShiftAliasTerm,
    QuarticGramFamily.complexAliasTerm]
  ring

/-- The full complex-frequency lattice sum for one even compact physical
channel, stated directly using the family complex alias term. -/
theorem hasSum_channel_complexAlias
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (Λ : ℝ)
    (hL : 0 < F.period T j) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → F.window T j u = 0)
    (heven : ∀ u, F.window T j (-u) = F.window T j u)
    (z z' : ℂ) :
    Summable
        (fun m : ℤ =>
          (F.period T j : ℂ) * F.complexAliasTerm T z z' j m) ∧
      HasSum
        (fun k : ℤ =>
          paperFT (fun u => (F.window T j u : ℂ))
              (z - (T + (k : ℝ) *
                (2 * Real.pi / F.period T j) : ℝ)) *
            paperFT (fun u => (F.window T j u : ℂ))
              (z' - (T + (k : ℝ) *
                (2 * Real.pi / F.period T j) : ℝ)))
        (∑' m : ℤ,
          (F.period T j : ℂ) * F.complexAliasTerm T z z' j m) := by
  have hsupp' : ∀ u, Λ < |u| →
      (F.window T j u : ℂ) = 0 := by
    intro u hu
    rw [hsupp u hu]
    norm_num
  have heven' : ∀ u,
      (F.window T j (-u) : ℂ) = F.window T j u := by
    intro u
    rw [heven u]
  simpa only [shiftAlias_eq_period_mul_complexAlias] using
    (Poisson.hasSum_paperFT_mul_paperFT_shift_alias
      hL hΛ hsmooth hsupp' heven' z z')

/-- Infinite frequency-pair lattice for one physical channel. -/
def channelFrequencyPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (z z' : ℂ) : ℂ :=
  ∑' k : ℤ,
    paperFT (fun u => (F.window T j u : ℂ))
        (z - (T + (k : ℝ) *
          (2 * Real.pi / F.period T j) : ℝ)) *
      paperFT (fun u => (F.window T j u : ℂ))
        (z' - (T + (k : ℝ) *
          (2 * Real.pi / F.period T j) : ℝ))

/-- Total spatial alias sum of one physical channel. -/
def channelAliasSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (z z' : ℂ) : ℂ :=
  ∑' m : ℤ, F.complexAliasTerm T z z' j m

/-- The one-channel frequency lattice is its period times the unweighted
alias sum.  This is the normalization used by the Gram atom. -/
theorem channelFrequencyPairSum_eq_period_mul_aliasSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (Λ : ℝ)
    (hL : 0 < F.period T j) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → F.window T j u = 0)
    (heven : ∀ u, F.window T j (-u) = F.window T j u)
    (z z' : ℂ) :
    channelFrequencyPairSum F T j z z' =
      (F.period T j : ℂ) * channelAliasSum F T j z z' := by
  obtain ⟨_, hhas⟩ :=
    hasSum_channel_complexAlias F T j Λ hL hΛ
      hsmooth hsupp heven z z'
  unfold channelFrequencyPairSum channelAliasSum
  calc
    (∑' k : ℤ,
      paperFT (fun u => (F.window T j u : ℂ))
          (z - (T + (k : ℝ) *
            (2 * Real.pi / F.period T j) : ℝ)) *
        paperFT (fun u => (F.window T j u : ℂ))
          (z' - (T + (k : ℝ) *
            (2 * Real.pi / F.period T j) : ℝ))) =
        ∑' m : ℤ,
          (F.period T j : ℂ) *
            F.complexAliasTerm T z z' j m :=
      hhas.tsum_eq
    _ = (F.period T j : ℂ) *
          ∑' m : ℤ, F.complexAliasTerm T z z' j m := by
      rw [tsum_mul_left]

/-- The zero spatial alias is the literal squared-window Fourier integral. -/
theorem complexAliasTerm_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (z z' : ℂ) :
    F.complexAliasTerm T z z' j 0 =
      ∫ u : ℝ,
        (F.window T j u : ℂ) * F.window T j u *
          cexp (I * (z - z') * (u : ℂ)) := by
  simp [QuarticGramFamily.complexAliasTerm]


/-- A channel alias sum is its zero translation plus the sum over all
nonzero translations. -/
theorem channelAliasSum_eq_zero_add_nonzero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (z z' : ℂ)
    (hsum : Summable
      (fun m : ℤ => F.complexAliasTerm T z z' j m)) :
    channelAliasSum F T j z z' =
      F.complexAliasTerm T z z' j 0 +
        ∑' m : {m : ℤ // m ≠ 0},
          F.complexAliasTerm T z z' j m := by
  classical
  unfold channelAliasSum
  simpa using
    (hsum.sum_add_tsum_subtype_compl ({0} : Finset ℤ)).symm

/-- Once the frozen off-RH alias family cancels, summing the full alias
lattices over channels leaves exactly the zero translations. -/
theorem sum_channelAliasSum_eq_sum_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (z z' : ℂ)
    (hsum : ∀ j : Fin (F.channelCount T),
      Summable (fun m : ℤ => F.complexAliasTerm T z z' j m))
    (hfamily : Summable (F.complexAliasFamily T z z'))
    (hoff : (∑' a : F.AliasIndex T,
      F.complexAliasFamily T z z' a) = 0) :
    (∑ j : Fin (F.channelCount T),
        channelAliasSum F T j z z') =
      ∑ j : Fin (F.channelCount T),
        F.complexAliasTerm T z z' j 0 := by
  classical
  have hprod :
      (∑' a : F.AliasIndex T,
          F.complexAliasFamily T z z' a) =
        ∑' j : Fin (F.channelCount T),
          ∑' m : {m : ℤ // m ≠ 0},
            F.complexAliasTerm T z z' j m := by
    simpa only [QuarticGramFamily.complexAliasFamily] using
      hfamily.tsum_prod
  have hnonzero :
      (∑ j : Fin (F.channelCount T),
          ∑' m : {m : ℤ // m ≠ 0},
            F.complexAliasTerm T z z' j m) = 0 := by
    calc
      (∑ j : Fin (F.channelCount T),
          ∑' m : {m : ℤ // m ≠ 0},
            F.complexAliasTerm T z z' j m) =
          ∑' j : Fin (F.channelCount T),
            ∑' m : {m : ℤ // m ≠ 0},
              F.complexAliasTerm T z z' j m := by simp
      _ = ∑' a : F.AliasIndex T,
          F.complexAliasFamily T z z' a := hprod.symm
      _ = 0 := hoff
  calc
    (∑ j : Fin (F.channelCount T),
        channelAliasSum F T j z z') =
      ∑ j : Fin (F.channelCount T),
        (F.complexAliasTerm T z z' j 0 +
          ∑' m : {m : ℤ // m ≠ 0},
            F.complexAliasTerm T z z' j m) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact channelAliasSum_eq_zero_add_nonzero
        F T j z z' (hsum j)
    _ = (∑ j : Fin (F.channelCount T),
          F.complexAliasTerm T z z' j 0) +
        ∑ j : Fin (F.channelCount T),
          ∑' m : {m : ℤ // m ≠ 0},
            F.complexAliasTerm T z z' j m := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j : Fin (F.channelCount T),
        F.complexAliasTerm T z z' j 0 := by
      rw [hnonzero, add_zero]


/-- The channel frequency-pair lattice with the reciprocal-period factor
coming from the square of the Gram atom. -/
def channelNormalizedFrequencyPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (z z' : ℂ) : ℂ :=
  (F.fullLength T : ℂ) / (F.period T j : ℂ) *
    channelFrequencyPairSum F T j z z'

/-- Complex Poisson cancels the channel period against the atom's
reciprocal-period normalization. -/
theorem channelNormalizedFrequencyPairSum_eq_fullLength_mul_aliasSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (Λ : ℝ)
    (hL : 0 < F.period T j) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → F.window T j u = 0)
    (heven : ∀ u, F.window T j (-u) = F.window T j u)
    (z z' : ℂ) :
    channelNormalizedFrequencyPairSum F T j z z' =
      (F.fullLength T : ℂ) * channelAliasSum F T j z z' := by
  have hL0 : (F.period T j : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hL)
  unfold channelNormalizedFrequencyPairSum
  rw [channelFrequencyPairSum_eq_period_mul_aliasSum
    F T j Λ hL hΛ hsmooth hsupp heven z z']
  rw [mul_assoc, div_mul_cancel₀ _ hL0]

/-- Smooth compact channels have summable unscaled spatial alias lattices. -/
theorem summable_channelAlias
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (Λ : ℝ)
    (hL : 0 < F.period T j) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → F.window T j u = 0)
    (heven : ∀ u, F.window T j (-u) = F.window T j u)
    (z z' : ℂ) :
    Summable (fun m : ℤ => F.complexAliasTerm T z z' j m) := by
  have hL0 : (F.period T j : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hL)
  have hscaled :=
    (hasSum_channel_complexAlias F T j Λ hL hΛ
      hsmooth hsupp heven z z').1
  exact (summable_mul_left_iff hL0).1 hscaled

/-- After summing normalized physical channels, the frozen off-RH
cancellation removes every nonzero spatial translation. -/
theorem sum_channelNormalizedFrequencyPairSum_eq_fullLength_mul_sum_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hL : ∀ j : Fin (F.channelCount T), 0 < F.period T j)
    (hsmooth : ∀ j : Fin (F.channelCount T),
      ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ j : Fin (F.channelCount T), ∀ u,
      Λ < |u| → F.window T j u = 0)
    (heven : ∀ j : Fin (F.channelCount T), ∀ u,
      F.window T j (-u) = F.window T j u)
    (z z' : ℂ)
    (hfamily : Summable (F.complexAliasFamily T z z'))
    (hoff : (∑' a : F.AliasIndex T,
      F.complexAliasFamily T z z' a) = 0) :
    (∑ j : Fin (F.channelCount T),
        channelNormalizedFrequencyPairSum F T j z z') =
      (F.fullLength T : ℂ) *
        ∑ j : Fin (F.channelCount T),
          F.complexAliasTerm T z z' j 0 := by
  have hsum : ∀ j : Fin (F.channelCount T),
      Summable (fun m : ℤ => F.complexAliasTerm T z z' j m) :=
    fun j => summable_channelAlias F T j Λ
      (hL j) hΛ (hsmooth j) (hsupp j) (heven j) z z'
  calc
    (∑ j : Fin (F.channelCount T),
        channelNormalizedFrequencyPairSum F T j z z') =
      ∑ j : Fin (F.channelCount T),
        (F.fullLength T : ℂ) * channelAliasSum F T j z z' := by
      apply Finset.sum_congr rfl
      intro j hj
      exact channelNormalizedFrequencyPairSum_eq_fullLength_mul_aliasSum
        F T j Λ (hL j) hΛ (hsmooth j) (hsupp j) (heven j) z z'
    _ = (F.fullLength T : ℂ) *
        ∑ j : Fin (F.channelCount T),
          channelAliasSum F T j z z' := by
      rw [Finset.mul_sum]
    _ = (F.fullLength T : ℂ) *
        ∑ j : Fin (F.channelCount T),
          F.complexAliasTerm T z z' j 0 := by
      rw [sum_channelAliasSum_eq_sum_zero
        F T z z' hsum hfamily hoff]


/-- The cancellation field of BlockMomentLimits, specialized to the actual
zero pairs and combined with the channel Poisson identity. -/
theorem BlockMomentLimits.eventually_normalizedFrequencyPairSum_eq_zeroAliases
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : BlockMomentLimits F)
    (Λ : ℝ → ℝ)
    (hΛ : ∀ᶠ T in Filter.atTop, 0 ≤ Λ T)
    (hL : ∀ᶠ T in Filter.atTop,
      ∀ j : Fin (F.channelCount T), 0 < F.period T j)
    (hsmooth : ∀ᶠ T in Filter.atTop,
      ∀ j : Fin (F.channelCount T),
        ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ᶠ T in Filter.atTop,
      ∀ j : Fin (F.channelCount T), ∀ u,
        Λ T < |u| → F.window T j u = 0)
    (heven : ∀ᶠ T in Filter.atTop,
      ∀ j : Fin (F.channelCount T), ∀ u,
        F.window T j (-u) = F.window T j u) :
    ∀ᶠ T in Filter.atTop,
      ∀ ρ ∈ Z.ZIprime T, ∀ ρ' ∈ Z.ZIprime T,
        (∑ j : Fin (F.channelCount T),
            channelNormalizedFrequencyPairSum F T j
              (gammaOf ρ) (gammaOf ρ')) =
          (F.fullLength T : ℂ) *
            ∑ j : Fin (F.channelCount T),
              F.complexAliasTerm T (gammaOf ρ) (gammaOf ρ') j 0 := by
  filter_upwards [
    h.complex_aliases_summable_at_zeros,
    h.offRH_complex_poisson_at_zeros,
    hΛ, hL, hsmooth, hsupp, heven
  ] with T hfamily hoff hΛT hLT hsmoothT hsuppT hevenT
  intro ρ hρ ρ' hρ'
  exact
    sum_channelNormalizedFrequencyPairSum_eq_fullLength_mul_sum_zero
      F T (Λ T) hΛT hLT hsmoothT hsuppT hevenT
      (gammaOf ρ) (gammaOf ρ')
      (hfamily ρ hρ ρ' hρ') (hoff ρ hρ ρ' hρ')


/-- The sum of all zero translations is the Fourier integral of the total
physical window energy. -/
theorem sum_complexAliasTerm_zero_eq_integral_windowEnergy
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (z z' : ℂ)
    (hintegrable : ∀ j : Fin (F.channelCount T),
      Integrable (fun u : ℝ =>
        (F.window T j u : ℂ) * F.window T j u *
          cexp (I * (z - z') * (u : ℂ)))) :
    (∑ j : Fin (F.channelCount T),
        F.complexAliasTerm T z z' j 0) =
      ∫ u : ℝ,
        (F.windowEnergy T u : ℂ) *
          cexp (I * (z - z') * (u : ℂ)) := by
  calc
    (∑ j : Fin (F.channelCount T),
        F.complexAliasTerm T z z' j 0) =
      ∑ j : Fin (F.channelCount T),
        ∫ u : ℝ,
          (F.window T j u : ℂ) * F.window T j u *
            cexp (I * (z - z') * (u : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact complexAliasTerm_zero F T j z z'
    _ = ∫ u : ℝ,
        ∑ j : Fin (F.channelCount T),
          (F.window T j u : ℂ) * F.window T j u *
            cexp (I * (z - z') * (u : ℂ)) := by
      simpa using
        (integral_finsetSum Finset.univ
          (fun j hj => hintegrable j)).symm
    _ = ∫ u : ℝ,
        (F.windowEnergy T u : ℂ) *
          cexp (I * (z - z') * (u : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp [QuarticGramFamily.windowEnergy, Finset.sum_mul, pow_two]

/-- The normalized cross-channel Poisson identity expressed directly in the
physical total-energy profile. -/
theorem sum_channelNormalizedFrequencyPairSum_eq_energyIntegral
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hL : ∀ j : Fin (F.channelCount T), 0 < F.period T j)
    (hsmooth : ∀ j : Fin (F.channelCount T),
      ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ j : Fin (F.channelCount T), ∀ u,
      Λ < |u| → F.window T j u = 0)
    (heven : ∀ j : Fin (F.channelCount T), ∀ u,
      F.window T j (-u) = F.window T j u)
    (z z' : ℂ)
    (hfamily : Summable (F.complexAliasFamily T z z'))
    (hoff : (∑' a : F.AliasIndex T,
      F.complexAliasFamily T z z' a) = 0)
    (hintegrable : ∀ j : Fin (F.channelCount T),
      Integrable (fun u : ℝ =>
        (F.window T j u : ℂ) * F.window T j u *
          cexp (I * (z - z') * (u : ℂ)))) :
    (∑ j : Fin (F.channelCount T),
        channelNormalizedFrequencyPairSum F T j z z') =
      (F.fullLength T : ℂ) *
        ∫ u : ℝ,
          (F.windowEnergy T u : ℂ) *
            cexp (I * (z - z') * (u : ℂ)) := by
  rw [sum_channelNormalizedFrequencyPairSum_eq_fullLength_mul_sum_zero
    F T Λ hΛ hL hsmooth hsupp heven z z' hfamily hoff]
  rw [sum_complexAliasTerm_zero_eq_integral_windowEnergy
    F T z z' hintegrable]


/-- Smoothness and the channel support bound imply the integrability needed
to commute the zero-alias channel sum with the Fourier integral. -/
theorem integrable_zeroAliasIntegrand
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (Λ : ℝ)
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → F.window T j u = 0)
    (z z' : ℂ) :
    Integrable (fun u : ℝ =>
      (F.window T j u : ℂ) * F.window T j u *
        cexp (I * (z - z') * (u : ℂ))) := by
  have hcontinuous :
      Continuous (fun u : ℝ =>
        (F.window T j u : ℂ) * F.window T j u *
          cexp (I * (z - z') * (u : ℂ))) :=
    (hsmooth.continuous.mul hsmooth.continuous).mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))
  have hcompactWindow :
      HasCompactSupport (fun u : ℝ => (F.window T j u : ℂ)) := by
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
      HasCompactSupport (fun u : ℝ =>
        (F.window T j u : ℂ) * F.window T j u *
          cexp (I * (z - z') * (u : ℂ))) := by
    apply hcompactWindow.mono
    intro u hu
    change
      (F.window T j u : ℂ) * F.window T j u *
        cexp (I * (z - z') * (u : ℂ)) ≠ 0 at hu
    change (F.window T j u : ℂ) ≠ 0
    intro hzero
    apply hu
    simp [hzero]
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

/-- The energy-integral form of normalized alias cancellation has no
separate integrability premise: it follows from the Poisson hypotheses. -/
theorem sum_channelNormalizedFrequencyPairSum_eq_energyIntegral_of_compact
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hL : ∀ j : Fin (F.channelCount T), 0 < F.period T j)
    (hsmooth : ∀ j : Fin (F.channelCount T),
      ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ j : Fin (F.channelCount T), ∀ u,
      Λ < |u| → F.window T j u = 0)
    (heven : ∀ j : Fin (F.channelCount T), ∀ u,
      F.window T j (-u) = F.window T j u)
    (z z' : ℂ)
    (hfamily : Summable (F.complexAliasFamily T z z'))
    (hoff : (∑' a : F.AliasIndex T,
      F.complexAliasFamily T z z' a) = 0) :
    (∑ j : Fin (F.channelCount T),
        channelNormalizedFrequencyPairSum F T j z z') =
      (F.fullLength T : ℂ) *
        ∫ u : ℝ,
          (F.windowEnergy T u : ℂ) *
            cexp (I * (z - z') * (u : ℂ)) := by
  apply sum_channelNormalizedFrequencyPairSum_eq_energyIntegral
    F T Λ hΛ hL hsmooth hsupp heven z z' hfamily hoff
  intro j
  exact integrable_zeroAliasIntegrand
    F T j Λ hΛ (hsmooth j) (hsupp j) z z'


/-- The BlockMomentLimits complex-alias fields now yield, for every actual
zero pair at large height, the physical energy form of Poisson summation. -/
theorem BlockMomentLimits.eventually_normalizedFrequencyPairSum_eq_energyIntegral
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : BlockMomentLimits F)
    (Λ : ℝ → ℝ)
    (hΛ : ∀ᶠ T in Filter.atTop, 0 ≤ Λ T)
    (hL : ∀ᶠ T in Filter.atTop,
      ∀ j : Fin (F.channelCount T), 0 < F.period T j)
    (hsmooth : ∀ᶠ T in Filter.atTop,
      ∀ j : Fin (F.channelCount T),
        ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ᶠ T in Filter.atTop,
      ∀ j : Fin (F.channelCount T), ∀ u,
        Λ T < |u| → F.window T j u = 0)
    (heven : ∀ᶠ T in Filter.atTop,
      ∀ j : Fin (F.channelCount T), ∀ u,
        F.window T j (-u) = F.window T j u) :
    ∀ᶠ T in Filter.atTop,
      ∀ ρ ∈ Z.ZIprime T, ∀ ρ' ∈ Z.ZIprime T,
        (∑ j : Fin (F.channelCount T),
            channelNormalizedFrequencyPairSum F T j
              (gammaOf ρ) (gammaOf ρ')) =
          (F.fullLength T : ℂ) *
            ∫ u : ℝ,
              (F.windowEnergy T u : ℂ) *
                cexp (I * (gammaOf ρ - gammaOf ρ') *
                  (u : ℂ)) := by
  filter_upwards [
    h.complex_aliases_summable_at_zeros,
    h.offRH_complex_poisson_at_zeros,
    hΛ, hL, hsmooth, hsupp, heven
  ] with T hfamily hoff hΛT hLT hsmoothT hsuppT hevenT
  intro ρ hρ ρ' hρ'
  exact
    sum_channelNormalizedFrequencyPairSum_eq_energyIntegral_of_compact
      F T (Λ T) hΛT hLT hsmoothT hsuppT hevenT
      (gammaOf ρ) (gammaOf ρ')
      (hfamily ρ hρ ρ' hρ') (hoff ρ hρ ρ' hρ')


/-- The literal finite frequency-pair sum carried by the distinguished
principal block.  The column label is read from the actual embedding; no
contiguous-grid enumeration is assumed. -/
def distinguishedBlockFrequencyPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑ i : Fin (F.blockDim T),
    let address := F.columnAddress T (F.blockEmbedding T i)
    let L := F.period T (F.distinguished T)
    let τ : ℝ := T + 2 * Real.pi * (address.2 : ℕ) / L
    paperFT (fun u => (F.window T (F.distinguished T) u : ℂ))
        (gammaOf ρ - τ) *
      paperFT (fun u => (F.window T (F.distinguished T) u : ℂ))
        (gammaOf ρ' - τ)

/-- Once the block columns are known to belong to the distinguished channel,
the scalar zero-pair kernel is exactly its finite physical-frequency sum,
with the two Fourier normalizations factored outside the summation. -/
theorem zeroPairKernel_eq_distinguishedBlockFrequencyPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T) :
    QuarticTransfer.zeroPairKernel F T ρ ρ' =
      (Real.sqrt
          (F.fullLength T / F.period T (F.distinguished T)) : ℂ) ^ 2 *
        distinguishedBlockFrequencyPairSum F T ρ ρ' := by
  classical
  simp only [QuarticTransfer.zeroPairKernel,
    distinguishedBlockFrequencyPairSum, Finset.mul_sum, pow_two]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [QuarticGramFamily.atom]
  rw [hdist i]
  ring

/-- The preceding identity holds eventually for every zero pair in any
literal principal construction. -/
theorem PrincipalCyclicBlock.eventually_zeroPairKernel_eq_distinguishedBlockFrequencyPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : PrincipalCyclicBlock F) :
    ∀ᶠ T in Filter.atTop, ∀ ρ ρ' : ℂ,
      QuarticTransfer.zeroPairKernel F T ρ ρ' =
        (Real.sqrt
            (F.fullLength T / F.period T (F.distinguished T)) : ℂ) ^ 2 *
          distinguishedBlockFrequencyPairSum F T ρ ρ' := by
  filter_upwards [h.distinguished_columns] with T hdist
  intro ρ ρ'
  exact zeroPairKernel_eq_distinguishedBlockFrequencyPairSum
    F T ρ ρ' hdist


/-- Under the natural nonnegativity of the Fourier normalization, the square
of the real square root is the exact reciprocal-period factor used by the
Poisson lattice. -/
theorem zeroPairKernel_eq_normalizedDistinguishedBlockFrequencyPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (hratio : 0 ≤
      F.fullLength T / F.period T (F.distinguished T)) :
    QuarticTransfer.zeroPairKernel F T ρ ρ' =
      ((F.fullLength T / F.period T (F.distinguished T) : ℝ) : ℂ) *
        distinguishedBlockFrequencyPairSum F T ρ ρ' := by
  rw [zeroPairKernel_eq_distinguishedBlockFrequencyPairSum
    F T ρ ρ' hdist]
  have hsqrt :
      (Real.sqrt
          (F.fullLength T / F.period T (F.distinguished T)) : ℂ) ^ 2 =
        ((F.fullLength T /
          F.period T (F.distinguished T) : ℝ) : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hratio
  rw [hsqrt]

/-- Every literal principal construction eventually has the normalized exact
finite-frequency representation, simultaneously for all zero pairs. -/
theorem PrincipalCyclicBlock.eventually_zeroPairKernel_eq_normalizedDistinguishedBlockFrequencyPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : PrincipalCyclicBlock F) :
    ∀ᶠ T in Filter.atTop, ∀ ρ ρ' : ℂ,
      QuarticTransfer.zeroPairKernel F T ρ ρ' =
        ((F.fullLength T /
          F.period T (F.distinguished T) : ℝ) : ℂ) *
          distinguishedBlockFrequencyPairSum F T ρ ρ' := by
  filter_upwards [
    h.distinguished_columns,
    h.periods_pos,
    Zeta23.Assembly.eventually_l_pos
  ] with T hdist hperiod hl
  have hfull : 0 ≤ F.fullLength T := by
    simp only [QuarticGramFamily.fullLength]
    exact mul_nonneg h.support_pos.le hl.le
  have hratio : 0 ≤
      F.fullLength T / F.period T (F.distinguished T) :=
    div_nonneg hfull (hperiod (F.distinguished T)).le
  intro ρ ρ'
  exact
    zeroPairKernel_eq_normalizedDistinguishedBlockFrequencyPairSum
      F T ρ ρ' hdist hratio


/-- The exact finite/infinite frequency discrepancy for the distinguished
channel, before its reciprocal-period normalization. -/
def distinguishedFrequencyPairTail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  channelFrequencyPairSum F T (F.distinguished T)
      (gammaOf ρ) (gammaOf ρ') -
    distinguishedBlockFrequencyPairSum F T ρ ρ'

/-- The actual zero-pair kernel is exactly the normalized infinite Poisson
lattice minus one explicit finite-grid tail. -/
theorem zeroPairKernel_eq_normalizedFrequencyPairSum_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (hratio : 0 ≤
      F.fullLength T / F.period T (F.distinguished T)) :
    QuarticTransfer.zeroPairKernel F T ρ ρ' =
      channelNormalizedFrequencyPairSum F T (F.distinguished T)
          (gammaOf ρ) (gammaOf ρ') -
        ((F.fullLength T /
          F.period T (F.distinguished T) : ℝ) : ℂ) *
          distinguishedFrequencyPairTail F T ρ ρ' := by
  rw [zeroPairKernel_eq_normalizedDistinguishedBlockFrequencyPairSum
    F T ρ ρ' hdist hratio]
  have hcast :
      ((F.fullLength T /
        F.period T (F.distinguished T) : ℝ) : ℂ) =
        (F.fullLength T : ℂ) /
          (F.period T (F.distinguished T) : ℂ) := by
    norm_cast
  rw [hcast]
  simp only [channelNormalizedFrequencyPairSum,
    distinguishedFrequencyPairTail]
  ring

/-- In a literal principal construction, the main-minus-tail decomposition
holds eventually and simultaneously for all zero pairs. -/
theorem PrincipalCyclicBlock.eventually_zeroPairKernel_eq_normalizedFrequencyPairSum_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : PrincipalCyclicBlock F) :
    ∀ᶠ T in Filter.atTop, ∀ ρ ρ' : ℂ,
      QuarticTransfer.zeroPairKernel F T ρ ρ' =
        channelNormalizedFrequencyPairSum F T (F.distinguished T)
            (gammaOf ρ) (gammaOf ρ') -
          ((F.fullLength T /
            F.period T (F.distinguished T) : ℝ) : ℂ) *
            distinguishedFrequencyPairTail F T ρ ρ' := by
  filter_upwards [
    h.distinguished_columns,
    h.periods_pos,
    Zeta23.Assembly.eventually_l_pos
  ] with T hdist hperiod hl
  have hfull : 0 ≤ F.fullLength T := by
    simp only [QuarticGramFamily.fullLength]
    exact mul_nonneg h.support_pos.le hl.le
  have hratio : 0 ≤
      F.fullLength T / F.period T (F.distinguished T) :=
    div_nonneg hfull (hperiod (F.distinguished T)).le
  intro ρ ρ'
  exact zeroPairKernel_eq_normalizedFrequencyPairSum_sub_tail
    F T ρ ρ' hdist hratio


/-- A single channel with a strict support gap needs no cross-channel alias
cancellation: its normalized infinite frequency lattice is exactly the
Fourier integral of that channel's physical energy. -/
theorem channelNormalizedFrequencyPairSum_eq_channelEnergyIntegral_of_support_gap
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (j : Fin (F.channelCount T)) (Λ : ℝ)
    (hL : 0 < F.period T j) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (F.window T j u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → F.window T j u = 0)
    (heven : ∀ u, F.window T j (-u) = F.window T j u)
    (hgap : 2 * Λ < F.period T j)
    (z z' : ℂ) :
    channelNormalizedFrequencyPairSum F T j z z' =
      (F.fullLength T : ℂ) *
        ∫ u : ℝ,
          (F.window T j u : ℂ) * F.window T j u *
            cexp (I * (z - z') * (u : ℂ)) := by
  have hsupp' : ∀ u, Λ < |u| →
      (F.window T j u : ℂ) = 0 := by
    intro u hu
    rw [hsupp u hu]
    norm_num
  have heven' : ∀ u,
      (F.window T j (-u) : ℂ) = F.window T j u := by
    intro u
    rw [heven u]
  have hhas :=
    Poisson.hasSum_paperFT_mul_paperFT_shift_alias_zero_only
      hL hΛ hsmooth hsupp' heven' hgap z z'
  have hfreq :
      channelFrequencyPairSum F T j z z' =
        Poisson.complexPoissonShiftAliasTerm
          (fun u => (F.window T j u : ℂ))
          (F.period T j) T z z' 0 := by
    unfold channelFrequencyPairSum
    exact hhas.tsum_eq
  rw [shiftAlias_eq_period_mul_complexAlias] at hfreq
  have hL0 : (F.period T j : ℂ) ≠ 0 := by
    exact_mod_cast hL.ne'
  unfold channelNormalizedFrequencyPairSum
  rw [hfreq, mul_assoc, div_mul_cancel₀ _ hL0]
  rw [complexAliasTerm_zero]

/-- The actual distinguished zero-pair kernel is therefore its one-channel
physical-energy integral minus only the finite/infinite grid tail. -/
theorem zeroPairKernel_eq_distinguishedEnergyIntegral_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (hratio : 0 ≤
      F.fullLength T / F.period T (F.distinguished T))
    (Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ u, Λ < |u| →
      F.window T (F.distinguished T) u = 0)
    (heven : ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u)
    (hgap : 2 * Λ < F.period T (F.distinguished T)) :
    QuarticTransfer.zeroPairKernel F T ρ ρ' =
      (F.fullLength T : ℂ) *
          ∫ u : ℝ,
            (F.window T (F.distinguished T) u : ℂ) *
              F.window T (F.distinguished T) u *
              cexp (I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) -
        ((F.fullLength T /
          F.period T (F.distinguished T) : ℝ) : ℂ) *
          distinguishedFrequencyPairTail F T ρ ρ' := by
  rw [zeroPairKernel_eq_normalizedFrequencyPairSum_sub_tail
    F T ρ ρ' hdist hratio]
  rw [channelNormalizedFrequencyPairSum_eq_channelEnergyIntegral_of_support_gap
    F T (F.distinguished T) Λ hL hΛ hsmooth hsupp heven hgap]

/-- The one-channel energy-minus-tail representation holds eventually for a
principal construction as soon as its distinguished window has a strict
support gap.  No complex-alias summability or cancellation premise appears. -/
theorem PrincipalCyclicBlock.eventually_zeroPairKernel_eq_distinguishedEnergyIntegral_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hblock : PrincipalCyclicBlock F)
    (Λ : ℝ → ℝ)
    (hΛ : ∀ᶠ T in Filter.atTop, 0 ≤ Λ T)
    (hsmooth : ∀ᶠ T in Filter.atTop,
      ContDiff ℝ 2
        (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ᶠ T in Filter.atTop, ∀ u,
      Λ T < |u| → F.window T (F.distinguished T) u = 0)
    (heven : ∀ᶠ T in Filter.atTop, ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u)
    (hgap : ∀ᶠ T in Filter.atTop,
      2 * Λ T < F.period T (F.distinguished T)) :
    ∀ᶠ T in Filter.atTop, ∀ ρ ρ' : ℂ,
      QuarticTransfer.zeroPairKernel F T ρ ρ' =
        (F.fullLength T : ℂ) *
            ∫ u : ℝ,
              (F.window T (F.distinguished T) u : ℂ) *
                F.window T (F.distinguished T) u *
                cexp (I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) -
          ((F.fullLength T /
            F.period T (F.distinguished T) : ℝ) : ℂ) *
            distinguishedFrequencyPairTail F T ρ ρ' := by
  filter_upwards [
    hblock.eventually_zeroPairKernel_eq_normalizedFrequencyPairSum_sub_tail,
    hblock.periods_pos,
    hΛ, hsmooth, hsupp, heven, hgap
  ] with T hkernel hperiod hΛT hsmoothT hsuppT hevenT hgapT
  intro ρ ρ'
  rw [hkernel ρ ρ']
  rw [channelNormalizedFrequencyPairSum_eq_channelEnergyIntegral_of_support_gap
    F T (F.distinguished T) (Λ T)
    (hperiod (F.distinguished T)) hΛT hsmoothT hsuppT hevenT hgapT]


/-- After the hat normalization is moved inside the pair contraction, its
full-length factor cancels exactly.  The main term becomes the distinguished
energy transform divided by total channel energy, and the finite-grid tail
gets its exact reciprocal period-energy scale. -/
theorem normalizedZeroPairKernel_eq_energyRatioIntegral_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (hratio : 0 ≤
      F.fullLength T / F.period T (F.distinguished T))
    (Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ u, Λ < |u| →
      F.window T (F.distinguished T) u = 0)
    (heven : ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u)
    (hgap : 2 * Λ < F.period T (F.distinguished T))
    (hfull0 : F.fullLength T ≠ 0)
    (henergy0 : (∫ u : ℝ, F.windowEnergy T u) ≠ 0) :
    QuarticTransfer.normalizedZeroPairKernel F T ρ ρ' =
      (∫ u : ℝ,
          (F.window T (F.distinguished T) u : ℂ) *
            F.window T (F.distinguished T) u *
            cexp (I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))) /
        ((∫ u : ℝ, F.windowEnergy T u : ℝ) : ℂ) -
      (((F.period T (F.distinguished T) *
        ∫ u : ℝ, F.windowEnergy T u)⁻¹ : ℝ) : ℂ) *
        distinguishedFrequencyPairTail F T ρ ρ' := by
  unfold QuarticTransfer.normalizedZeroPairKernel
  rw [zeroPairKernel_eq_distinguishedEnergyIntegral_sub_tail
    F T ρ ρ' hdist hratio Λ hL hΛ hsmooth hsupp heven hgap]
  simp only [QuarticGramFamily.hatDenominator]
  push_cast
  field_simp [hfull0, hL.ne', henergy0]
  <;> ring


/-- Fourier transform of the literal distinguished local profile at the
physical zero-difference scale. -/
def localProfileFourierIntegral
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (z z' : ℂ) : ℂ :=
  ∫ x : ℝ,
    (F.localProfile T x : ℂ) *
      cexp (I * (z - z') *
        ((F.period T (F.distinguished T) * x : ℝ) : ℂ))

/-- Exact change of variables from the distinguished physical-window energy
integral to the normalized local-profile Fourier integral. -/
theorem channelEnergy_mul_localProfileFourierIntegral
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (z z' : ℂ)
    (hL : 0 < F.period T (F.distinguished T))
    (henergy0 : F.channelEnergy T (F.distinguished T) ≠ 0) :
    (F.channelEnergy T (F.distinguished T) : ℂ) *
        localProfileFourierIntegral F T z z' =
      ∫ u : ℝ,
        (F.window T (F.distinguished T) u : ℂ) *
          F.window T (F.distinguished T) u *
          cexp (I * (z - z') * (u : ℂ)) := by
  let L : ℝ := F.period T (F.distinguished T)
  let E : ℝ := F.channelEnergy T (F.distinguished T)
  let w : ℝ → ℝ := F.window T (F.distinguished T)
  unfold localProfileFourierIntegral
  rw [← integral_const_mul_C]
  calc
    (∫ x : ℝ,
        (E : ℂ) *
          ((F.localProfile T x : ℂ) *
            cexp (I * (z - z') * ((L * x : ℝ) : ℂ)))) =
      ∫ x : ℝ,
        (L : ℂ) *
          ((w (L * x) : ℂ) * w (L * x) *
            cexp (I * (z - z') * ((L * x : ℝ) : ℂ))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [QuarticGramFamily.localProfile]
      dsimp only [L, E, w]
      push_cast
      field_simp [henergy0]
      <;> ring
    _ = (L : ℂ) *
        ∫ x : ℝ,
          (w (L * x) : ℂ) * w (L * x) *
            cexp (I * (z - z') * ((L * x : ℝ) : ℂ)) :=
      integral_const_mul_C _ _
    _ = ∫ u : ℝ,
        (w u : ℂ) * w u *
          cexp (I * (z - z') * (u : ℂ)) := by
      let J : ℝ → ℂ := fun u =>
        (w u : ℂ) * w u *
          cexp (I * (z - z') * (u : ℂ))
      change (L : ℂ) * (∫ x : ℝ, J (L * x)) =
        ∫ u : ℝ, J u
      rw [Measure.integral_comp_mul_left J L,
        abs_of_pos (inv_pos.mpr hL)]
      rw [← Complex.coe_smul, smul_eq_mul, ← mul_assoc, ofReal_inv,
        mul_inv_cancel₀ (ofReal_ne_zero.mpr hL.ne'), one_mul]

/-- Dividing by total channel energy after the change of variables produces
the exact distinguished-channel energy ratio times the local-profile
Fourier transform. -/
theorem channelEnergyIntegral_div_total_eq_ratio_mul_localProfile
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (z z' : ℂ)
    (hL : 0 < F.period T (F.distinguished T))
    (henergy0 : F.channelEnergy T (F.distinguished T) ≠ 0) :
    (∫ u : ℝ,
        (F.window T (F.distinguished T) u : ℂ) *
          F.window T (F.distinguished T) u *
          cexp (I * (z - z') * (u : ℂ))) /
        ((∫ u : ℝ, F.windowEnergy T u : ℝ) : ℂ) =
      ((F.channelEnergy T (F.distinguished T) /
        (∫ u : ℝ, F.windowEnergy T u) : ℝ) : ℂ) *
        localProfileFourierIntegral F T z z' := by
  rw [← channelEnergy_mul_localProfileFourierIntegral
    F T z z' hL henergy0]
  push_cast
  ring


/-- Final exact pair-level coordinate: the normalized actual zero-pair kernel
is the literal local-profile Fourier transform weighted by the distinguished
energy ratio, minus one explicitly scaled finite-grid tail. -/
theorem normalizedZeroPairKernel_eq_localProfile_sub_tail
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (hratio : 0 ≤
      F.fullLength T / F.period T (F.distinguished T))
    (Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ u, Λ < |u| →
      F.window T (F.distinguished T) u = 0)
    (heven : ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u)
    (hgap : 2 * Λ < F.period T (F.distinguished T))
    (hfull0 : F.fullLength T ≠ 0)
    (htotal0 : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hchannel0 : F.channelEnergy T (F.distinguished T) ≠ 0) :
    QuarticTransfer.normalizedZeroPairKernel F T ρ ρ' =
      ((F.channelEnergy T (F.distinguished T) /
        (∫ u : ℝ, F.windowEnergy T u) : ℝ) : ℂ) *
          localProfileFourierIntegral F T (gammaOf ρ) (gammaOf ρ') -
      (((F.period T (F.distinguished T) *
        ∫ u : ℝ, F.windowEnergy T u)⁻¹ : ℝ) : ℂ) *
        distinguishedFrequencyPairTail F T ρ ρ' := by
  rw [normalizedZeroPairKernel_eq_energyRatioIntegral_sub_tail
    F T ρ ρ' hdist hratio Λ hL hΛ hsmooth hsupp heven hgap
      hfull0 htotal0]
  rw [channelEnergyIntegral_div_total_eq_ratio_mul_localProfile
    F T (gammaOf ρ) (gammaOf ρ') hL hchannel0]


/-- The scalar pair kernel after all exact Poisson, support-gap, hat, and
physical-to-local rearrangements: a local-profile main term minus the
normalized finite-grid tail. -/
def localProfileTailPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((F.channelEnergy T (F.distinguished T) /
    (∫ u : ℝ, F.windowEnergy T u) : ℝ) : ℂ) *
      localProfileFourierIntegral F T (gammaOf ρ) (gammaOf ρ') -
    (((F.period T (F.distinguished T) *
      ∫ u : ℝ, F.windowEnergy T u)⁻¹ : ℝ) : ℂ) *
      distinguishedFrequencyPairTail F T ρ ρ'

theorem normalizedZeroPairKernel_eq_localProfileTailPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (hratio : 0 ≤
      F.fullLength T / F.period T (F.distinguished T))
    (Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ u, Λ < |u| →
      F.window T (F.distinguished T) u = 0)
    (heven : ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u)
    (hgap : 2 * Λ < F.period T (F.distinguished T))
    (hfull0 : F.fullLength T ≠ 0)
    (htotal0 : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hchannel0 : F.channelEnergy T (F.distinguished T) ≠ 0) :
    QuarticTransfer.normalizedZeroPairKernel F T ρ ρ' =
      localProfileTailPairKernel F T ρ ρ' := by
  exact normalizedZeroPairKernel_eq_localProfile_sub_tail
    F T ρ ρ' hdist hratio Λ hL hΛ hsmooth hsupp heven hgap
      hfull0 htotal0 hchannel0

/-- The complete actual target-specific quartic numerator is exactly the
generic zero-tuple polynomial generated by the local-profile-minus-tail pair
kernel.  The substitution is made before every higher product and finite
zero sum. -/
theorem factoredZeroKernelQuarticNumerator_eq_localProfileTailPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : RHLinalg.Quartic)
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (hratio : 0 ≤
      F.fullLength T / F.period T (F.distinguished T))
    (Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ u, Λ < |u| →
      F.window T (F.distinguished T) u = 0)
    (heven : ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u)
    (hgap : 2 * Λ < F.period T (F.distinguished T))
    (hfull0 : F.fullLength T ≠ 0)
    (htotal0 : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hchannel0 : F.channelEnergy T (F.distinguished T) ≠ 0) :
    QuarticTransfer.factoredZeroKernelQuarticNumerator q F T =
      QuarticTransfer.pairKernelQuarticNumerator q F T
        (localProfileTailPairKernel F T) := by
  rw [QuarticTransfer.factoredZeroKernelQuarticNumerator_eq_normalized,
    QuarticTransfer.normalizedFactoredZeroKernelQuarticNumerator_eq_pairKernel]
  apply QuarticTransfer.pairKernelQuarticNumerator_congr
  intro ρ hρ ρ' hρ'
  exact normalizedZeroPairKernel_eq_localProfileTailPairKernel
    F T ρ ρ' hdist hratio Λ hL hΛ hsmooth hsupp heven hgap
      hfull0 htotal0 hchannel0


/-- The exact analytic boundary after the order of operations has been
changed: normalize each zero-pair kernel first, replace it by the
distinguished local profile minus its finite-grid tail, and only then form
the cyclic products and zero sums. -/
structure LocalProfileTailQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : RHLinalg.Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos :
    ∀ᶠ T in Filter.atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ,
    x < μ * QuarticTransfer.limitQuarticScore q μ p →
      ∀ᶠ T in Filter.atTop,
        x <
          QuarticTransfer.pairKernelQuarticNumerator q F T
              (localProfileTailPairKernel F T) /
            (Z.N T (2 * T) : ℝ)

/-- The local-profile-minus-tail lower bound implies the literal factored
zero-kernel lower bound using only the concrete, pointwise hypotheses of the
one-channel Poisson reduction.  No principal-block structure is assumed. -/
theorem LocalProfileTailQuarticLowerBound.toFactored
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : RHLinalg.Quartic} {F : QuarticGramFamily Z σ μ p v}
    (h : LocalProfileTailQuarticLowerBound q F)
    (Λ : ℝ → ℝ)
    (hdist : ∀ᶠ T in Filter.atTop,
      ∀ i : Fin (F.blockDim T),
        (F.columnAddress T (F.blockEmbedding T i)).1 =
          F.distinguished T)
    (hratio : ∀ᶠ T in Filter.atTop,
      0 ≤ F.fullLength T / F.period T (F.distinguished T))
    (hL : ∀ᶠ T in Filter.atTop,
      0 < F.period T (F.distinguished T))
    (hΛ : ∀ᶠ T in Filter.atTop, 0 ≤ Λ T)
    (hsmooth : ∀ᶠ T in Filter.atTop,
      ContDiff ℝ 2
        (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ᶠ T in Filter.atTop, ∀ u,
      Λ T < |u| →
        F.window T (F.distinguished T) u = 0)
    (heven : ∀ᶠ T in Filter.atTop, ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u)
    (hgap : ∀ᶠ T in Filter.atTop,
      2 * Λ T < F.period T (F.distinguished T))
    (hfull0 : ∀ᶠ T in Filter.atTop, F.fullLength T ≠ 0)
    (htotal0 : ∀ᶠ T in Filter.atTop,
      (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hchannel0 : ∀ᶠ T in Filter.atTop,
      F.channelEnergy T (F.distinguished T) ≠ 0) :
    QuarticTransfer.FactoredZeroKernelQuarticLowerBound q F := by
  refine ⟨h.block_dimension_pos, ?_⟩
  intro x hx
  filter_upwards [
    h.eventually_gt x hx, hdist, hratio, hL, hΛ, hsmooth,
    hsupp, heven, hgap, hfull0, htotal0, hchannel0
  ] with T hT hdistT hratioT hLT hΛT hsmoothT
      hsuppT hevenT hgapT hfull0T htotal0T hchannel0T
  rw [factoredZeroKernelQuarticNumerator_eq_localProfileTailPairKernel
    q F T hdistT hratioT (Λ T) hLT hΛT hsmoothT hsuppT hevenT
      hgapT hfull0T htotal0T hchannel0T]
  exact hT


/-- The distinguished local-profile main term before the finite frequency
tail is subtracted. -/
def localProfileMainPairKernel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((F.channelEnergy T (F.distinguished T) /
    (∫ u : ℝ, F.windowEnergy T u) : ℝ) : ℂ) *
      localProfileFourierIntegral F T (gammaOf ρ) (gammaOf ρ')

/-- The normalized error made by replacing the complete
local-profile-minus-tail quartic numerator by its local-profile main
numerator.  The subtraction is deliberately taken after all cyclic products
and finite zero sums have been formed. -/
def localProfileTailQuarticErrorDensity
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : RHLinalg.Quartic) (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) : ℝ :=
  QuarticTransfer.pairKernelQuarticNumerator q F T
        (localProfileTailPairKernel F T) /
      (Z.N T (2 * T) : ℝ) -
    QuarticTransfer.pairKernelQuarticNumerator q F T
        (localProfileMainPairKernel F T) /
      (Z.N T (2 * T) : ℝ)

/-- One-sided asymptotics for the local-profile main numerator. -/
structure LocalProfileMainQuarticLowerBound
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : RHLinalg.Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  block_dimension_pos :
    ∀ᶠ T in Filter.atTop, 0 < F.blockDim T
  eventually_gt : ∀ x : ℝ,
    x < μ * QuarticTransfer.limitQuarticScore q μ p →
      ∀ᶠ T in Filter.atTop,
        x <
          QuarticTransfer.pairKernelQuarticNumerator q F T
              (localProfileMainPairKernel F T) /
            (Z.N T (2 * T) : ℝ)

/-- The sum-first tail error vanishes after normalization.  This asks for
no pointwise tail bound on individual zero pairs. -/
structure LocalProfileTailQuarticErrorVanishing
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (q : RHLinalg.Quartic) (F : QuarticGramFamily Z σ μ p v) : Prop where
  vanishes : Tendsto
    (localProfileTailQuarticErrorDensity q F)
    Filter.atTop (nhds 0)

/-- A strict lower bound survives any perturbation that tends to zero.
Applied here, it transfers the local-profile main estimate to the exact
local-profile-minus-finite-tail numerator. -/
theorem localProfileTailQuarticLowerBound_of_main_of_error
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {q : RHLinalg.Quartic} {F : QuarticGramFamily Z σ μ p v}
    (hmain : LocalProfileMainQuarticLowerBound q F)
    (herror : LocalProfileTailQuarticErrorVanishing q F) :
    LocalProfileTailQuarticLowerBound q F := by
  refine ⟨hmain.block_dimension_pos, ?_⟩
  intro x hx
  let L : ℝ := μ * QuarticTransfer.limitQuarticScore q μ p
  let y : ℝ := (x + L) / 2
  have hxy : x < y := by
    dsimp [y, L]
    linarith
  have hyL : y < L := by
    dsimp [y]
    linarith
  have herrorLower : ∀ᶠ T in Filter.atTop,
      x - y < localProfileTailQuarticErrorDensity q F T :=
    herror.vanishes.eventually (Ioi_mem_nhds (sub_neg.mpr hxy))
  filter_upwards [hmain.eventually_gt y hyL, herrorLower]
      with T hmainT herrorT
  unfold localProfileTailQuarticErrorDensity at herrorT
  linarith


/-- The finite modulation label carried by an actual block column, transported
to the distinguished channel using the proved channel identity. -/
def distinguishedBlockLabel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (i : Fin (F.blockDim T)) :
    Fin (F.channelDim T (F.distinguished T)) := by
  let address := F.columnAddress T (F.blockEmbedding T i)
  have hfirst : address.1 = F.distinguished T := by
    simpa only [address] using hdist i
  refine ⟨address.2.val, ?_⟩
  rw [← hfirst]
  exact address.2.isLt

/-- Bijectivity of the global column address together with exhaustion of the
distinguished channel makes the actual block labels a bijection onto the
entire distinguished finite grid. -/
theorem distinguishedBlockLabel_bijective
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (haddr : Function.Bijective (F.columnAddress T))
    (hexhaustive : ∀ i : Fin (F.dim T),
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i) :
    Function.Bijective (distinguishedBlockLabel F T hdist) := by
  constructor
  · intro i i' hii
    apply (F.blockEmbedding T).injective
    apply haddr.1
    apply Sigma.subtype_ext
    · exact (hdist i).trans (hdist i').symm
    · have hval := congrArg Fin.val hii
      simpa only [distinguishedBlockLabel] using hval
  · intro k
    obtain ⟨c, hc⟩ :=
      haddr.2 ⟨F.distinguished T, k⟩
    have hcfirst :
        (F.columnAddress T c).1 = F.distinguished T := by
      rw [hc]
    obtain ⟨i, hi⟩ := hexhaustive c hcfirst
    refine ⟨i, ?_⟩
    apply Fin.ext
    simp [distinguishedBlockLabel, hi, hc]

/-- The canonical equivalence between actual block columns and the complete
distinguished finite grid. -/
def distinguishedBlockLabelEquiv
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (haddr : Function.Bijective (F.columnAddress T))
    (hexhaustive : ∀ i : Fin (F.dim T),
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i) :
    Fin (F.blockDim T) ≃
      Fin (F.channelDim T (F.distinguished T)) :=
  Equiv.ofBijective (distinguishedBlockLabel F T hdist)
    (distinguishedBlockLabel_bijective F T hdist haddr hexhaustive)

/-- Consequently the actual block dimension is exactly the distinguished
channel's finite-grid count. -/
theorem blockDim_eq_distinguished_channelDim
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (haddr : Function.Bijective (F.columnAddress T))
    (hexhaustive : ∀ i : Fin (F.dim T),
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i) :
    F.blockDim T = F.channelDim T (F.distinguished T) := by
  simpa using Fintype.card_congr
    (distinguishedBlockLabelEquiv F T hdist haddr hexhaustive)

/-- Every finite sum over actual block columns can now be rewritten as a
sum over the complete distinguished finite grid. -/
theorem sum_distinguishedBlockLabel
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {M : Type*} [AddCommMonoid M]
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (haddr : Function.Bijective (F.columnAddress T))
    (hexhaustive : ∀ i : Fin (F.dim T),
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (g : Fin (F.channelDim T (F.distinguished T)) → M) :
    (∑ i : Fin (F.blockDim T),
      g (distinguishedBlockLabel F T hdist i)) =
      ∑ k : Fin (F.channelDim T (F.distinguished T)), g k :=
  Equiv.sum_comp
    (distinguishedBlockLabelEquiv F T hdist haddr hexhaustive) g


/-- One distinguished-channel Fourier-pair summand at a nonnegative
modulation label. -/
def distinguishedNatFrequencyPairTerm
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) (k : ℕ) : ℂ :=
  let L := F.period T (F.distinguished T)
  let τ : ℝ := T + 2 * Real.pi * k / L
  paperFT (fun u => (F.window T (F.distinguished T) u : ℂ))
      (gammaOf ρ - τ) *
    paperFT (fun u => (F.window T (F.distinguished T) u : ℂ))
      (gammaOf ρ' - τ)

/-- The literal complete distinguished finite grid, independent of the
particular block embedding used to enumerate it. -/
def distinguishedFiniteGridPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑ k : Fin (F.channelDim T (F.distinguished T)),
    distinguishedNatFrequencyPairTerm F T ρ ρ' k

/-- Reindex the actual block frequency sum by the complete distinguished
finite grid. -/
theorem distinguishedBlockFrequencyPairSum_eq_finiteGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (haddr : Function.Bijective (F.columnAddress T))
    (hexhaustive : ∀ i : Fin (F.dim T),
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i) :
    distinguishedBlockFrequencyPairSum F T ρ ρ' =
      distinguishedFiniteGridPairSum F T ρ ρ' := by
  simpa only [distinguishedBlockFrequencyPairSum,
    distinguishedFiniteGridPairSum, distinguishedNatFrequencyPairTerm,
    distinguishedBlockLabel] using
      (sum_distinguishedBlockLabel F T hdist haddr hexhaustive
        (fun k =>
          distinguishedNatFrequencyPairTerm F T ρ ρ' k))

/-- The formerly opaque finite/infinite discrepancy is exactly the full
integer lattice minus the complete distinguished nonnegative cutoff grid. -/
theorem distinguishedFrequencyPairTail_eq_full_sub_finiteGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (haddr : Function.Bijective (F.columnAddress T))
    (hexhaustive : ∀ i : Fin (F.dim T),
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i) :
    distinguishedFrequencyPairTail F T ρ ρ' =
      channelFrequencyPairSum F T (F.distinguished T)
          (gammaOf ρ) (gammaOf ρ') -
        distinguishedFiniteGridPairSum F T ρ ρ' := by
  unfold distinguishedFrequencyPairTail
  rw [distinguishedBlockFrequencyPairSum_eq_finiteGrid
    F T ρ ρ' hdist haddr hexhaustive]

/-- If the construction supplies its exact floor cutoff, the finite part of
the tail is literally indexed by that floor. -/
theorem distinguishedFrequencyPairTail_eq_full_sub_floorGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (haddr : Function.Bijective (F.columnAddress T))
    (hexhaustive : ∀ i : Fin (F.dim T),
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (hgrid :
      F.channelDim T (F.distinguished T) =
        ⌊F.period T (F.distinguished T) * T /
          (2 * Real.pi)⌋₊) :
    distinguishedFrequencyPairTail F T ρ ρ' =
      channelFrequencyPairSum F T (F.distinguished T)
          (gammaOf ρ) (gammaOf ρ') -
        ∑ k : Fin
            ⌊F.period T (F.distinguished T) * T /
              (2 * Real.pi)⌋₊,
          distinguishedNatFrequencyPairTerm F T ρ ρ' k := by
  rw [distinguishedFrequencyPairTail_eq_full_sub_finiteGrid
    F T ρ ρ' hdist haddr hexhaustive]
  unfold distinguishedFiniteGridPairSum
  rw [hgrid]


/-- One distinguished-channel Fourier-pair summand on the full integer
frequency lattice. -/
def distinguishedIntegerFrequencyPairTerm
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) (k : ℤ) : ℂ :=
  let L := F.period T (F.distinguished T)
  paperFT (fun u => (F.window T (F.distinguished T) u : ℂ))
      (gammaOf ρ -
        (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)) *
    paperFT (fun u => (F.window T (F.distinguished T) u : ℂ))
      (gammaOf ρ' -
        (T + (k : ℝ) * (2 * Real.pi / L) : ℝ))

/-- Casting a nonnegative label into the integer lattice gives exactly the
same frequency-pair summand. -/
theorem distinguishedIntegerFrequencyPairTerm_natCast
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) (k : ℕ) :
    distinguishedIntegerFrequencyPairTerm F T ρ ρ' (k : ℤ) =
      distinguishedNatFrequencyPairTerm F T ρ ρ' k := by
  have hshift :
      T + (((k : ℤ) : ℝ) *
          (2 * Real.pi /
            F.period T (F.distinguished T))) =
        T + 2 * Real.pi * (k : ℝ) /
          F.period T (F.distinguished T) := by
    push_cast
    ring
  simp only [distinguishedIntegerFrequencyPairTerm,
    distinguishedNatFrequencyPairTerm]
  rw [hshift]

/-- The embedding of natural cutoff labels into the integer frequency
lattice. -/
def natFrequencyEmbedding : ℕ ↪ ℤ where
  toFun k := k
  inj' := by
    intro k k' h
    exact_mod_cast h

/-- Integer frequencies retained by the finite nonnegative cutoff. -/
def nonnegativeFrequencyRange (n : ℕ) : Finset ℤ :=
  (Finset.range n).map natFrequencyEmbedding

/-- The complete integer lattice is definitionally the channel frequency
sum. -/
theorem channelFrequencyPairSum_eq_integerLattice
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) :
    channelFrequencyPairSum F T (F.distinguished T)
        (gammaOf ρ) (gammaOf ρ') =
      ∑' k : ℤ,
        distinguishedIntegerFrequencyPairTerm F T ρ ρ' k := by
  rfl

/-- The complete distinguished finite grid is the finite sum over its image
inside the integer lattice. -/
theorem distinguishedFiniteGridPairSum_eq_integerRange
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) :
    distinguishedFiniteGridPairSum F T ρ ρ' =
      ∑ k ∈ nonnegativeFrequencyRange
          (F.channelDim T (F.distinguished T)),
        distinguishedIntegerFrequencyPairTerm F T ρ ρ' k := by
  unfold distinguishedFiniteGridPairSum nonnegativeFrequencyRange
  rw [Fin.sum_univ_eq_sum_range]
  simp only [Finset.sum_map, distinguishedIntegerFrequencyPairTerm_natCast]

/-- The exact tail is the summable lattice restricted to the complement of
the retained nonnegative cutoff. -/
def distinguishedOutsideGridPairSum
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑' k : {k : ℤ // k ∉
      nonnegativeFrequencyRange
        (F.channelDim T (F.distinguished T))},
    distinguishedIntegerFrequencyPairTerm F T ρ ρ' k

/-- After the actual block has been reindexed, its finite/infinite
discrepancy is exactly the outside-cutoff integer sum. -/
theorem distinguishedFrequencyPairTail_eq_outsideGrid
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (haddr : Function.Bijective (F.columnAddress T))
    (hexhaustive : ∀ i : Fin (F.dim T),
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (hsum : Summable
      (distinguishedIntegerFrequencyPairTerm F T ρ ρ')) :
    distinguishedFrequencyPairTail F T ρ ρ' =
      distinguishedOutsideGridPairSum F T ρ ρ' := by
  rw [distinguishedFrequencyPairTail_eq_full_sub_finiteGrid
    F T ρ ρ' hdist haddr hexhaustive]
  rw [channelFrequencyPairSum_eq_integerLattice,
    distinguishedFiniteGridPairSum_eq_integerRange]
  unfold distinguishedOutsideGridPairSum
  have hsplit := hsum.sum_add_tsum_subtype_compl
    (nonnegativeFrequencyRange
      (F.channelDim T (F.distinguished T)))
  rw [← hsplit]
  ring


/-- The retained integer range is exactly the half-open interval from zero
through the cutoff. -/
theorem mem_nonnegativeFrequencyRange_iff
    (n : ℕ) (k : ℤ) :
    k ∈ nonnegativeFrequencyRange n ↔
      0 ≤ k ∧ k < n := by
  classical
  simp only [nonnegativeFrequencyRange, Finset.mem_map,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ha, hcast⟩
    subst k
    constructor <;> omega
  · intro hk
    refine ⟨k.toNat, ?_, ?_⟩
    · omega
    · simp only [natFrequencyEmbedding]
      omega

/-- Every omitted integer frequency lies either below zero or at/above the
finite cutoff. -/
theorem not_mem_nonnegativeFrequencyRange_iff
    (n : ℕ) (k : ℤ) :
    k ∉ nonnegativeFrequencyRange n ↔
      k < 0 ∨ (n : ℤ) ≤ k := by
  rw [mem_nonnegativeFrequencyRange_iff]
  omega

/-- Smooth compact support gives summability of the distinguished integer
frequency-pair lattice directly from complex Poisson summation. -/
theorem summable_distinguishedIntegerFrequencyPairTerm
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ u, Λ < |u| →
      F.window T (F.distinguished T) u = 0)
    (heven : ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u)
    (ρ ρ' : ℂ) :
    Summable
      (distinguishedIntegerFrequencyPairTerm F T ρ ρ') := by
  have hhas :=
    (hasSum_channel_complexAlias F T (F.distinguished T) Λ
      hL hΛ hsmooth hsupp heven (gammaOf ρ) (gammaOf ρ')).2
  exact hhas.summable

/-- The tail equals the outside-cutoff lattice with summability discharged
by the same smooth compact one-channel hypotheses used for Poisson. -/
theorem distinguishedFrequencyPairTail_eq_outsideGrid_of_compact
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T : ℝ) (ρ ρ' : ℂ)
    (hdist : ∀ i : Fin (F.blockDim T),
      (F.columnAddress T (F.blockEmbedding T i)).1 =
        F.distinguished T)
    (haddr : Function.Bijective (F.columnAddress T))
    (hexhaustive : ∀ i : Fin (F.dim T),
      (F.columnAddress T i).1 = F.distinguished T →
        ∃ b, F.blockEmbedding T b = i)
    (Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ u, Λ < |u| →
      F.window T (F.distinguished T) u = 0)
    (heven : ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u) :
    distinguishedFrequencyPairTail F T ρ ρ' =
      distinguishedOutsideGridPairSum F T ρ ρ' :=
  distinguishedFrequencyPairTail_eq_outsideGrid
    F T ρ ρ' hdist haddr hexhaustive
      (summable_distinguishedIntegerFrequencyPairTerm
        F T Λ hL hΛ hsmooth hsupp heven ρ ρ')


/-! ## Distinguished-channel aliases vanish from support alone -/


/-- Half-period support of the distinguished local profile kills every
nonzero spatial alias, for arbitrary complex frequencies.  Two translates
can overlap only at the single endpoint u = m L / 2, hence the integral
vanishes without an RH or real-frequency restriction. -/
theorem distinguished_complexAliasTerm_eq_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (henergy : 0 < F.channelEnergy T (F.distinguished T))
    (hsupport :
      tsupport (F.localProfile T) ⊆ Icc (-(1 : ℝ) / 2) (1 / 2))
    (z z' : ℂ) (m : ℤ) (hm : m ≠ 0) :
    F.complexAliasTerm T z z' (F.distinguished T) m = 0 := by
  let L : ℝ := F.period T (F.distinguished T)
  have hL' : 0 < L := by simpa only [L] using hL
  have hwindow_mem (u : ℝ)
      (hu : F.window T (F.distinguished T) u ≠ 0) :
      u / L ∈ Icc (-(1 : ℝ) / 2) (1 / 2) := by
    have hlocal :
        F.localProfile T (u / L) ≠ 0 := by
      have harg : L * (u / L) = u := by
        field_simp [hL'.ne']
      unfold QuarticGramFamily.localProfile
      dsimp only
      rw [show F.period T (F.distinguished T) = L by rfl, harg]
      exact div_ne_zero
        (mul_ne_zero hL'.ne' (pow_ne_zero 2 hu))
        henergy.ne'
    exact hsupport (subset_tsupport _ hlocal)
  unfold QuarticGramFamily.complexAliasTerm
  dsimp only
  rw [show F.period T (F.distinguished T) = L by rfl]
  have hint :
      (∫ u : ℝ,
        (F.window T (F.distinguished T) u : ℂ) *
          F.window T (F.distinguished T) (u - (m : ℝ) * L) *
          cexp (I * (z - z') * (u : ℂ))) = 0 := by
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [ae_neq ((m : ℝ) * L / 2)] with u hu
    by_cases hwu : F.window T (F.distinguished T) u = 0
    · simp [hwu]
    by_cases hwshift :
        F.window T (F.distinguished T) (u - (m : ℝ) * L) = 0
    · simp [hwshift]
    have hx := hwindow_mem u hwu
    have hy := hwindow_mem (u - (m : ℝ) * L) hwshift
    have hxy :
        u / L - (u - (m : ℝ) * L) / L = (m : ℝ) := by
      field_simp [hL'.ne']
      ring
    have hmloR : (-1 : ℝ) ≤ (m : ℝ) := by
      rw [← hxy]
      linarith [hx.1, hy.2]
    have hmhiR : (m : ℝ) ≤ 1 := by
      rw [← hxy]
      linarith [hx.2, hy.1]
    have hmlo : (-1 : ℤ) ≤ m := by
      exact_mod_cast hmloR
    have hmhi : m ≤ (1 : ℤ) := by
      exact_mod_cast hmhiR
    have hmcase : m = -1 ∨ m = 1 := by
      omega
    apply False.elim
    apply hu
    rcases hmcase with rfl | rfl
    · have hxval : u / L = -(1 : ℝ) / 2 := by
        norm_num at hxy
        linarith [hx.1, hy.2]
      have huval : u = (-(1 : ℝ) / 2) * L :=
        (div_eq_iff hL'.ne').mp hxval
      calc
        u = (-(1 : ℝ) / 2) * L := huval
        _ = ((-1 : ℤ) : ℝ) * L / 2 := by norm_num; ring
    · have hxval : u / L = (1 : ℝ) / 2 := by
        norm_num at hxy
        linarith [hx.2, hy.1]
      have huval : u = ((1 : ℝ) / 2) * L :=
        (div_eq_iff hL'.ne').mp hxval
      calc
        u = ((1 : ℝ) / 2) * L := huval
        _ = ((1 : ℤ) : ℝ) * L / 2 := by norm_num; ring
  rw [hint, mul_zero]


/-- The distinguished infinite frequency lattice equals its zero-translation
energy integral under closed half-period support.  Unlike the earlier support
gap lemma, no strict inequality between support width and period is needed. -/
theorem distinguishedNormalizedFrequencyPairSum_eq_energyIntegral
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T Λ : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupp : ∀ u, Λ < |u| ->
      F.window T (F.distinguished T) u = 0)
    (heven : ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u)
    (henergy : 0 < F.channelEnergy T (F.distinguished T))
    (hlocalSupport :
      tsupport (F.localProfile T) ⊆ Icc (-(1 : ℝ) / 2) (1 / 2))
    (z z' : ℂ) :
    channelNormalizedFrequencyPairSum F T (F.distinguished T) z z' =
      (F.fullLength T : ℂ) *
        ∫ u : ℝ,
          (F.window T (F.distinguished T) u : ℂ) *
            F.window T (F.distinguished T) u *
            cexp (I * (z - z') * (u : ℂ)) := by
  let j : Fin (F.channelCount T) := F.distinguished T
  have hsum :
      Summable (fun m : ℤ => F.complexAliasTerm T z z' j m) :=
    summable_channelAlias F T j Λ hL hΛ hsmooth hsupp heven z z'
  have hnonzero :
      (∑' m : {m : ℤ // m ≠ 0},
        F.complexAliasTerm T z z' j m) = 0 := by
    have hfun :
        (fun m : {m : ℤ // m ≠ 0} =>
          F.complexAliasTerm T z z' j m) = 0 := by
      funext m
      exact distinguished_complexAliasTerm_eq_zero F T
        hL henergy hlocalSupport z z' m m.property
    rw [hfun]
    simp
  have halias :
      channelAliasSum F T j z z' =
        F.complexAliasTerm T z z' j 0 := by
    rw [channelAliasSum_eq_zero_add_nonzero F T j z z' hsum,
      hnonzero, add_zero]
  have hL0 : (F.period T j : ℂ) ≠ 0 := by
    exact_mod_cast hL.ne'
  unfold channelNormalizedFrequencyPairSum
  rw [channelFrequencyPairSum_eq_period_mul_aliasSum
    F T j Λ hL hΛ hsmooth hsupp heven z z']
  rw [halias, mul_assoc, div_mul_cancel₀ _ hL0]
  exact congrArg (fun w : ℂ => (F.fullLength T : ℂ) * w)
    (complexAliasTerm_zero F T j z z')

/-- The physical principal-block construction therefore supplies literal
nonzero-alias cancellation on its distinguished channel eventually. -/
theorem PrincipalCyclicBlock.eventually_distinguished_complexAlias_zero
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : PrincipalCyclicBlock F) :
    ∀ᶠ T in Filter.atTop,
      ∀ z z' : ℂ, ∀ m : ℤ, m ≠ 0 ->
        F.complexAliasTerm T z z' (F.distinguished T) m = 0 := by
  filter_upwards [
    h.periods_pos,
    h.distinguished_channel_energy_pos,
    h.local_profile_support
  ] with T hperiod henergy hsupport
  intro z z' m hm
  exact distinguished_complexAliasTerm_eq_zero F T
    (hperiod (F.distinguished T)) henergy hsupport z z' m hm


/-- In particular, the entire nonzero distinguished-channel alias family is
summable and has zero sum at every complex frequency pair. -/
theorem PrincipalCyclicBlock.eventually_distinguished_nonzeroAliases
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (h : PrincipalCyclicBlock F) :
    ∀ᶠ T in Filter.atTop, ∀ z z' : ℂ,
      Summable (fun m : {m : ℤ // m ≠ 0} =>
        F.complexAliasTerm T z z' (F.distinguished T) m) ∧
      (∑' m : {m : ℤ // m ≠ 0},
        F.complexAliasTerm T z z' (F.distinguished T) m) = 0 := by
  filter_upwards [
    eventually_distinguished_complexAlias_zero h
  ] with T hzero
  intro z z'
  have hfun :
      (fun m : {m : ℤ // m ≠ 0} =>
        F.complexAliasTerm T z z' (F.distinguished T) m) = 0 := by
    funext m
    exact hzero z z' m m.property
  rw [hfun]
  simp


/-- Closed half-period support upgrades the actual block pair kernel to the
energy-integral-minus-grid-tail formula with no strict support-gap premise.
This removes the endpoint obstruction in the previous Poisson wrapper. -/
theorem PrincipalCyclicBlock.eventually_zeroPairKernel_eq_distinguishedEnergyIntegral_sub_tail_closed
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (hblock : PrincipalCyclicBlock F)
    (Λ : ℝ -> ℝ)
    (hΛ : ∀ᶠ T in Filter.atTop, 0 ≤ Λ T)
    (hsupp : ∀ᶠ T in Filter.atTop, ∀ u,
      Λ T < |u| ->
        F.window T (F.distinguished T) u = 0)
    (heven : ∀ᶠ T in Filter.atTop, ∀ u,
      F.window T (F.distinguished T) (-u) =
        F.window T (F.distinguished T) u) :
    ∀ᶠ T in Filter.atTop, ∀ ρ ρ' : ℂ,
      QuarticTransfer.zeroPairKernel F T ρ ρ' =
        (F.fullLength T : ℂ) *
            ∫ u : ℝ,
              (F.window T (F.distinguished T) u : ℂ) *
                F.window T (F.distinguished T) u *
                cexp (I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) -
          ((F.fullLength T /
            F.period T (F.distinguished T) : ℝ) : ℂ) *
            distinguishedFrequencyPairTail F T ρ ρ' := by
  filter_upwards [
    eventually_zeroPairKernel_eq_normalizedFrequencyPairSum_sub_tail hblock,
    hblock.periods_pos,
    hblock.windows_smooth,
    hblock.distinguished_channel_energy_pos,
    hblock.local_profile_support,
    hΛ, hsupp, heven
  ] with T hkernel hperiod hsmooth henergy hlocal hΛT hsuppT hevenT
  have hsmoothC :
      ContDiff ℝ 2
        (fun u => (F.window T (F.distinguished T) u : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp
      (hsmooth (F.distinguished T))).of_le (by norm_num)
  intro ρ ρ'
  rw [hkernel ρ ρ']
  rw [distinguishedNormalizedFrequencyPairSum_eq_energyIntegral
    F T (Λ T) (hperiod (F.distinguished T)) hΛT
    hsmoothC hsuppT hevenT henergy hlocal
    (gammaOf ρ) (gammaOf ρ')]


/-! ## Virtual-window half-period cancellation -/

/-- A real window supported in one closed half-period has zero overlap,
almost everywhere, with every nonzero integral period translate.  The only
possible overlap for shifts `m = ±1` is a single endpoint, which is null. -/
theorem halfPeriod_shift_product_ae_zero
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hsupport : tsupport f ⊆ Icc (-L / 2) (L / 2))
    (m : ℤ) (hm : m ≠ 0) :
    ∀ᵐ u : ℝ, f u * f (u - (m : ℝ) * L) = 0 := by
  have hmem (x : ℝ) (hx : f x ≠ 0) :
      x / L ∈ Icc (-(1 : ℝ) / 2) (1 / 2) := by
    have hx' := hsupport (subset_tsupport _ hx)
    rw [Set.mem_Icc] at hx' ⊢
    constructor
    · apply (le_div_iff₀ hL).2
      nlinarith
    · apply (div_le_iff₀ hL).2
      nlinarith
  filter_upwards [ae_neq ((m : ℝ) * L / 2)] with u hu
  by_cases hfu : f u = 0
  · simp [hfu]
  by_cases hfshift : f (u - (m : ℝ) * L) = 0
  · simp [hfshift]
  have hx := hmem u hfu
  have hy := hmem (u - (m : ℝ) * L) hfshift
  have hxy :
      u / L - (u - (m : ℝ) * L) / L = (m : ℝ) := by
    field_simp [hL.ne']
    ring
  have hmloR : (-1 : ℝ) ≤ (m : ℝ) := by
    rw [← hxy]
    linarith [hx.1, hy.2]
  have hmhiR : (m : ℝ) ≤ 1 := by
    rw [← hxy]
    linarith [hx.2, hy.1]
  have hmlo : (-1 : ℤ) ≤ m := by
    exact_mod_cast hmloR
  have hmhi : m ≤ (1 : ℤ) := by
    exact_mod_cast hmhiR
  have hmcase : m = -1 ∨ m = 1 := by
    omega
  apply False.elim
  apply hu
  rcases hmcase with rfl | rfl
  · have hxval : u / L = -(1 : ℝ) / 2 := by
      norm_num at hxy
      linarith [hx.1, hy.2]
    have huval : u = (-(1 : ℝ) / 2) * L :=
      (div_eq_iff hL.ne').mp hxval
    calc
      u = (-(1 : ℝ) / 2) * L := huval
      _ = ((-1 : ℤ) : ℝ) * L / 2 := by norm_num; ring
  · have hxval : u / L = (1 : ℝ) / 2 := by
      norm_num at hxy
      linarith [hx.2, hy.1]
    have huval : u = ((1 : ℝ) / 2) * L :=
      (div_eq_iff hL.ne').mp hxval
    calc
      u = ((1 : ℝ) / 2) * L := huval
      _ = ((1 : ℤ) : ℝ) * L / 2 := by norm_num; ring

/-- Multiplying the translated overlap by an arbitrary complex exponential
still gives a zero integral. -/
theorem halfPeriod_complexShiftIntegral_eq_zero
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hsupport : tsupport f ⊆ Icc (-L / 2) (L / 2))
    (m : ℤ) (hm : m ≠ 0) (phase : ℂ) :
    (∫ u : ℝ,
      (f u : ℂ) * f (u - (m : ℝ) * L) *
        Complex.exp (phase * (u : ℂ))) = 0 := by
  rw [← integral_zero]
  apply integral_congr_ae
  filter_upwards [
    halfPeriod_shift_product_ae_zero f L hL hsupport m hm
  ] with u hu
  rcases mul_eq_zero.mp hu with hzero | hzero
  · simp [hzero]
  · simp [hzero]

/-- The complex Poisson alias of a standalone virtual window. -/
def virtualComplexAliasTerm
    (T L : ℝ) (f : ℝ → ℝ) (z z' : ℂ) (m : ℤ) : ℂ :=
  Complex.exp
      (Complex.I * (z' - T) * (m : ℝ) * L) *
    ∫ u : ℝ,
      (f u : ℂ) * f (u - (m : ℝ) * L) *
        Complex.exp (Complex.I * (z - z') * (u : ℂ))

/-- Every nonzero complex alias of a closed-half-period virtual window
vanishes exactly.  This statement is independent of
`PrincipalCyclicBlock` and is therefore usable by the routed isometry. -/
theorem virtualComplexAliasTerm_eq_zero
    (T L : ℝ) (f : ℝ → ℝ) (hL : 0 < L)
    (hsupport : tsupport f ⊆ Icc (-L / 2) (L / 2))
    (z z' : ℂ) (m : ℤ) (hm : m ≠ 0) :
    virtualComplexAliasTerm T L f z z' m = 0 := by
  unfold virtualComplexAliasTerm
  rw [halfPeriod_complexShiftIntegral_eq_zero
    f L hL hsupport m hm (Complex.I * (z - z')), mul_zero]


/-! ## Exact virtual frequency lattice -/

/-- Infinite frequency-pair lattice of one standalone virtual window. -/
def virtualFrequencyPairSum
    (T L : ℝ) (f : ℝ → ℝ) (z z' : ℂ) : ℂ :=
  ∑' k : ℤ,
    paperFT (fun u => (f u : ℂ))
        (z - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)) *
      paperFT (fun u => (f u : ℂ))
        (z' - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ))

/-- Spatial alias lattice of one standalone virtual window. -/
def virtualAliasSum
    (T L : ℝ) (f : ℝ → ℝ) (z z' : ℂ) : ℂ :=
  ∑' m : ℤ, virtualComplexAliasTerm T L f z z' m

/-- The generic Poisson shift term is the period times the virtual alias. -/
theorem virtualShiftAlias_eq_period_mul
    (T L : ℝ) (f : ℝ → ℝ) (z z' : ℂ) (m : ℤ) :
    Poisson.complexPoissonShiftAliasTerm
        (fun u => (f u : ℂ)) L T z z' m =
      (L : ℂ) * virtualComplexAliasTerm T L f z z' m := by
  simp only [Poisson.complexPoissonShiftAliasTerm,
    virtualComplexAliasTerm]
  ring

/-- Complex Poisson summation stated entirely in virtual-window
coordinates. -/
theorem hasSum_virtualComplexAlias
    (T L Λ : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (heven : ∀ u, f (-u) = f u)
    (z z' : ℂ) :
    Summable
        (fun m : ℤ =>
          (L : ℂ) * virtualComplexAliasTerm T L f z z' m) ∧
      HasSum
        (fun k : ℤ =>
          paperFT (fun u => (f u : ℂ))
              (z - (T + (k : ℝ) *
                (2 * Real.pi / L) : ℝ)) *
            paperFT (fun u => (f u : ℂ))
              (z' - (T + (k : ℝ) *
                (2 * Real.pi / L) : ℝ)))
        (∑' m : ℤ,
          (L : ℂ) * virtualComplexAliasTerm T L f z z' m) := by
  have hsupp' : ∀ u, Λ < |u| → (f u : ℂ) = 0 := by
    intro u hu
    rw [hsupp u hu]
    norm_num
  have heven' : ∀ u, (f (-u) : ℂ) = f u := by
    intro u
    rw [heven u]
  simpa only [virtualShiftAlias_eq_period_mul] using
    (Poisson.hasSum_paperFT_mul_paperFT_shift_alias
      hL hΛ hsmooth hsupp' heven' z z')

/-- The virtual frequency lattice is its period times its alias lattice. -/
theorem virtualFrequencyPairSum_eq_period_mul_aliasSum
    (T L Λ : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (heven : ∀ u, f (-u) = f u)
    (z z' : ℂ) :
    virtualFrequencyPairSum T L f z z' =
      (L : ℂ) * virtualAliasSum T L f z z' := by
  obtain ⟨_, hhas⟩ :=
    hasSum_virtualComplexAlias T L Λ f
      hL hΛ hsmooth hsupp heven z z'
  unfold virtualFrequencyPairSum virtualAliasSum
  calc
    (∑' k : ℤ,
      paperFT (fun u => (f u : ℂ))
          (z - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)) *
        paperFT (fun u => (f u : ℂ))
          (z' - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ))) =
        ∑' m : ℤ,
          (L : ℂ) * virtualComplexAliasTerm T L f z z' m :=
      hhas.tsum_eq
    _ = (L : ℂ) *
          ∑' m : ℤ, virtualComplexAliasTerm T L f z z' m := by
      rw [tsum_mul_left]

/-- The zero virtual alias is the squared-window Fourier integral. -/
theorem virtualComplexAliasTerm_zero
    (T L : ℝ) (f : ℝ → ℝ) (z z' : ℂ) :
    virtualComplexAliasTerm T L f z z' 0 =
      ∫ u : ℝ,
        (f u : ℂ) * f u *
          Complex.exp (Complex.I * (z - z') * (u : ℂ)) := by
  simp [virtualComplexAliasTerm]

/-- Under closed half-period support the complete virtual alias lattice is
exactly its zero translation. -/
theorem virtualAliasSum_eq_zeroTranslation
    (T L Λ : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (heven : ∀ u, f (-u) = f u)
    (hhalf : tsupport f ⊆ Icc (-L / 2) (L / 2))
    (z z' : ℂ) :
    virtualAliasSum T L f z z' =
      virtualComplexAliasTerm T L f z z' 0 := by
  have hL0 : (L : ℂ) ≠ 0 := by
    exact_mod_cast hL.ne'
  have hscaled :=
    (hasSum_virtualComplexAlias T L Λ f
      hL hΛ hsmooth hsupp heven z z').1
  have hsum :
      Summable (fun m : ℤ =>
        virtualComplexAliasTerm T L f z z' m) :=
    (summable_mul_left_iff hL0).1 hscaled
  have hnonzero :
      (∑' m : {m : ℤ // m ≠ 0},
        virtualComplexAliasTerm T L f z z' m) = 0 := by
    have hfun :
        (fun m : {m : ℤ // m ≠ 0} =>
          virtualComplexAliasTerm T L f z z' m) = 0 := by
      funext m
      exact virtualComplexAliasTerm_eq_zero
        T L f hL hhalf z z' m m.property
    rw [hfun]
    simp
  unfold virtualAliasSum
  calc
    (∑' m : ℤ, virtualComplexAliasTerm T L f z z' m) =
        virtualComplexAliasTerm T L f z z' 0 +
          ∑' m : {m : ℤ // m ≠ 0},
            virtualComplexAliasTerm T L f z z' m := by
      simpa using
        (hsum.sum_add_tsum_subtype_compl ({0} : Finset ℤ)).symm
    _ = virtualComplexAliasTerm T L f z z' 0 := by
      rw [hnonzero, add_zero]

/-- Closed half-period support evaluates the complete virtual frequency
lattice exactly, with no strict support gap. -/
theorem virtualFrequencyPairSum_eq_energyIntegral
    (T L Λ : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (heven : ∀ u, f (-u) = f u)
    (hhalf : tsupport f ⊆ Icc (-L / 2) (L / 2))
    (z z' : ℂ) :
    virtualFrequencyPairSum T L f z z' =
      (L : ℂ) *
        ∫ u : ℝ,
          (f u : ℂ) * f u *
            Complex.exp (Complex.I * (z - z') * (u : ℂ)) := by
  rw [virtualFrequencyPairSum_eq_period_mul_aliasSum
    T L Λ f hL hΛ hsmooth hsupp heven z z']
  rw [virtualAliasSum_eq_zeroTranslation
    T L Λ f hL hΛ hsmooth hsupp heven hhalf z z']
  rw [virtualComplexAliasTerm_zero]

/-- The reciprocal-period Gram normalization cancels the virtual period,
leaving the requested full-length energy transform. -/
theorem virtualNormalizedFrequencyPairSum_eq_energyIntegral
    (fullLength T L Λ : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (heven : ∀ u, f (-u) = f u)
    (hhalf : tsupport f ⊆ Icc (-L / 2) (L / 2))
    (z z' : ℂ) :
    (fullLength : ℂ) / (L : ℂ) *
        virtualFrequencyPairSum T L f z z' =
      (fullLength : ℂ) *
        ∫ u : ℝ,
          (f u : ℂ) * f u *
            Complex.exp (Complex.I * (z - z') * (u : ℂ)) := by
  have hL0 : (L : ℂ) ≠ 0 := by
    exact_mod_cast hL.ne'
  rw [virtualFrequencyPairSum_eq_energyIntegral
    T L Λ f hL hΛ hsmooth hsupp heven hhalf z z']
  rw [mul_assoc, div_mul_cancel₀ _ hL0]


/-! ## Canonical finite exhaustion of the virtual frequency lattice -/

/-- One integer-frequency product in the standalone virtual lattice. -/
def virtualFrequencyPairTerm
    (T L : ℝ) (f : ℝ → ℝ) (z z' : ℂ) (k : ℤ) : ℂ :=
  paperFT (fun u => (f u : ℂ))
      (z - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ)) *
    paperFT (fun u => (f u : ℂ))
      (z' - (T + (k : ℝ) * (2 * Real.pi / L) : ℝ))

/-- The first n nonnegative frequencies paired with the first n negative
frequencies.  This enumerates every integer exactly once as n tends to
infinity. -/
def virtualSymmetricFrequencyPartialSum
    (T L : ℝ) (f : ℝ → ℝ) (z z' : ℂ) (n : ℕ) : ℂ :=
  ∑ k in Finset.range n,
    virtualFrequencyPairTerm T L f z z' (k : ℤ) +
      virtualFrequencyPairTerm T L f z z' (-(k : ℤ) - 1)

/-- The canonical finite symmetric grids converge to the complete virtual
Poisson lattice. -/
theorem tendsto_virtualSymmetricFrequencyPartialSum
    (T L Λ : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (heven : ∀ u, f (-u) = f u)
    (z z' : ℂ) :
    Tendsto
      (virtualSymmetricFrequencyPartialSum T L f z z')
      Filter.atTop
      (nhds (virtualFrequencyPairSum T L f z z')) := by
  have hsum :
      Summable (virtualFrequencyPairTerm T L f z z') := by
    simpa only [virtualFrequencyPairTerm] using
      (hasSum_virtualComplexAlias T L Λ f
        hL hΛ hsmooth hsupp heven z z').2.summable
  have hpair :
      HasSum
        (fun n : ℕ =>
          virtualFrequencyPairTerm T L f z z' (n : ℤ) +
            virtualFrequencyPairTerm T L f z z' (-(n : ℤ) - 1))
        (∑' k : ℤ, virtualFrequencyPairTerm T L f z z' k) := by
    have hbase := hsum.hasSum.nat_add_neg_add_one
    convert hbase using 1
    funext n
    congr 1
    push_cast
    ring
  simpa only [virtualSymmetricFrequencyPartialSum,
    virtualFrequencyPairSum, virtualFrequencyPairTerm] using
      hpair.tendsto_sum_nat


/-- With closed half-period support, the canonical finite grids converge
directly to the evaluated energy transform. -/
theorem tendsto_virtualSymmetricFrequencyPartialSum_energy
    (T L Λ : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (heven : ∀ u, f (-u) = f u)
    (hhalf : tsupport f ⊆ Icc (-L / 2) (L / 2))
    (z z' : ℂ) :
    Tendsto
      (virtualSymmetricFrequencyPartialSum T L f z z')
      Filter.atTop
      (nhds
        ((L : ℂ) *
          ∫ u : ℝ,
            (f u : ℂ) * f u *
              Complex.exp (Complex.I * (z - z') * (u : ℂ)))) := by
  rw [← virtualFrequencyPairSum_eq_energyIntegral
    T L Λ f hL hΛ hsmooth hsupp heven hhalf z z']
  exact tendsto_virtualSymmetricFrequencyPartialSum
    T L Λ f hL hΛ hsmooth hsupp heven z z'

/-- After reciprocal-period Gram normalization, the canonical finite grids
converge to the full-length energy transform. -/
theorem tendsto_virtualNormalizedSymmetricFrequencyPartialSum_energy
    (fullLength T L Λ : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ)
    (hsmooth : ContDiff ℝ 2 (fun u => (f u : ℂ)))
    (hsupp : ∀ u, Λ < |u| → f u = 0)
    (heven : ∀ u, f (-u) = f u)
    (hhalf : tsupport f ⊆ Icc (-L / 2) (L / 2))
    (z z' : ℂ) :
    Tendsto
      (fun n =>
        (fullLength : ℂ) / (L : ℂ) *
          virtualSymmetricFrequencyPartialSum T L f z z' n)
      Filter.atTop
      (nhds
        ((fullLength : ℂ) *
          ∫ u : ℝ,
            (f u : ℂ) * f u *
              Complex.exp (Complex.I * (z - z') * (u : ℂ)))) := by
  have hL0 : (L : ℂ) ≠ 0 := by
    exact_mod_cast hL.ne'
  have ht :=
    tendsto_const_nhds.mul
      (tendsto_virtualSymmetricFrequencyPartialSum_energy
        T L Λ f hL hΛ hsmooth hsupp heven hhalf z z')
      ((fullLength : ℂ) / (L : ℂ))
  convert ht using 1
  rw [mul_assoc, div_mul_cancel₀ _ hL0]

end ComplexAliasBridge
end Zeta85
end RH

end
