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

end ComplexAliasBridge
end Zeta85
end RH

end
