/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Inputs95
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

end ComplexAliasBridge
end Zeta85
end RH

end
