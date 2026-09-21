/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.SmoothRadialShell
import RH.Zeta85.Discharge.AlignedIsometricLayout

/-!
# Exact annular-energy handoff

The physical channels are summed before normalization.  When their total
energy is a nonzero scalar multiple of one shrinking annular shell, that
scalar cancels exactly.  The routed quartic numerator is therefore literally
the complete annular quartic numerator selected after the zero contraction.
-/

open MeasureTheory Filter Matrix Finset Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RH
namespace Zeta85
namespace AnnularEnergyBridge

open Zeta23
open SmoothRadialShell AlignedIsometricLayout

/-- A nonzero common scalar disappears from the normalized Fourier transform
of total physical window energy. -/
theorem normalizedPhysicalWindowEnergyPairKernel_eq_of_windowEnergy_eq_const_mul
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v)
    (T c : ℝ) (W : ℝ → ℝ)
    (henergy : ∀ u : ℝ, F.windowEnergy T u = c * W u)
    (hc : c ≠ 0)
    (hmass : (∫ u : ℝ, (W u : ℂ)) ≠ 0)
    (ρ ρ' : ℂ) :
    normalizedPhysicalWindowEnergyPairKernel F T ρ ρ' =
      ((∫ u : ℝ, (W u : ℂ))⁻¹) *
        ∫ u : ℝ,
          (W u : ℂ) *
            Complex.exp
              (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) := by
  unfold normalizedPhysicalWindowEnergyPairKernel
  have hmassF :
      (∫ u : ℝ, (F.windowEnergy T u : ℂ)) =
        (c : ℂ) * ∫ u : ℝ, (W u : ℂ) := by
    calc
      (∫ u : ℝ, (F.windowEnergy T u : ℂ)) =
          ∫ u : ℝ, (c : ℂ) * (W u : ℂ) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with u
        rw [henergy u]
        push_cast
      _ = (c : ℂ) * ∫ u : ℝ, (W u : ℂ) :=
        Zeta23.integral_const_mul_C _ _
  have hfourierF :
      (∫ u : ℝ,
        (F.windowEnergy T u : ℂ) *
          Complex.exp
            (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))) =
        (c : ℂ) *
          ∫ u : ℝ,
            (W u : ℂ) *
              Complex.exp
                (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) := by
    calc
      (∫ u : ℝ,
        (F.windowEnergy T u : ℂ) *
          Complex.exp
            (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))) =
          ∫ u : ℝ,
            (c : ℂ) *
              ((W u : ℂ) *
                Complex.exp
                  (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with u
        rw [henergy u]
        push_cast
        ring
      _ = (c : ℂ) *
          ∫ u : ℝ,
            (W u : ℂ) *
              Complex.exp
                (Complex.I * (gammaOf ρ - gammaOf ρ') * (u : ℂ)) :=
        Zeta23.integral_const_mul_C _ _
  rw [hmassF, hfourierF]
  have hcC : (c : ℂ) ≠ 0 := by
    exact_mod_cast hc
  field_simp [hcC, hmass]

/-- If every physical channel is the same annular window at one fixed height,
the normalized total-energy kernel is exactly the one-shell normalized
kernel.  Channel multiplicity cancels after the sum is formed. -/
theorem normalizedPhysicalWindowEnergyPairKernel_eq_shrinkingProfileShell
    {Z : ZeroConfig} {σ μ p : ℝ} {w : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p w)
    (T : ℝ) (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    (hchannels : 0 < F.channelCount T)
    (hwindow : ∀ (j : Fin (F.channelCount T)) (u : ℝ),
      F.window T j u = shrinkingProfileShellWindow v L n hL u)
    (hmass :
      (∫ u : ℝ,
        (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ)) ≠ 0)
    (ρ ρ' : ℂ) :
    normalizedPhysicalWindowEnergyPairKernel F T ρ ρ' =
      shrinkingProfileShellNormalizedPairKernel v L n hL ρ ρ' := by
  have henergy : ∀ u : ℝ,
      F.windowEnergy T u =
        (F.channelCount T : ℝ) *
          shrinkingProfileShellWindow v L n hL u ^ 2 := by
    intro u
    unfold QuarticGramFamily.windowEnergy
    simp [hwindow, nsmul_eq_mul]
  have hcount : (F.channelCount T : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hchannels
  simpa only [shrinkingProfileShellNormalizedPairKernel] using
    normalizedPhysicalWindowEnergyPairKernel_eq_of_windowEnergy_eq_const_mul
      F T (F.channelCount T : ℝ)
        (fun u => shrinkingProfileShellWindow v L n hL u ^ 2)
        henergy hcount hmass ρ ρ'

/-- Routed energy reaches the same annular pair kernel once the routed frame
has been summed, the literal hat factors cancel, and the physical channels
share one annular stage. -/
theorem routedEnergyPairKernel_eq_shrinkingProfileShell
    {Z : ZeroConfig} {σ μ p : ℝ} {w : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p w}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L₀ : Layout F ι} {G : RoutedGrid L₀}
    (H : RoutedFourierGrid G (canonicalAtomFactorization L₀))
    (hreg : RoutedWindowRegularity H)
    (henergy : RoutedEnergyNormalization H)
    (T : ℝ) (v : ℝ → ℝ) (L : ℝ) (n : ℕ) (hL : 0 < L)
    (hfull : @QuarticGramFamily.fullLength σ T ≠ 0)
    (hphysicalMass : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hchannels : 0 < F.channelCount T)
    (hwindow : ∀ (j : Fin (F.channelCount T)) (u : ℝ),
      F.window T j u = shrinkingProfileShellWindow v L n hL u)
    (hshellMass :
      (∫ u : ℝ,
        (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ)) ≠ 0)
    (ρ ρ' : ℂ) :
    routedEnergyPairKernel H T ρ ρ' =
      shrinkingProfileShellNormalizedPairKernel v L n hL ρ ρ' := by
  rw [routedEnergyPairKernel_eq_physicalWindowEnergyPairKernel
      H hreg henergy T ρ ρ',
    physicalWindowEnergyPairKernel_eq_normalized
      F T hfull hphysicalMass ρ ρ',
    normalizedPhysicalWindowEnergyPairKernel_eq_shrinkingProfileShell
      F T v L n hL hchannels hwindow hshellMass ρ ρ']

/-- After both channel summation and hat normalization, the complete routed
quartic contraction is literally the complete annular quartic contraction. -/
theorem routedEnergyQuarticNumerator_eq_shrinkingAnnular
    {Z : ZeroConfig} {σ μ p : ℝ} {w : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p w}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L₀ : Layout F ι} {G : RoutedGrid L₀}
    (q : TrimmedMoment.Quartic)
    (H : RoutedFourierGrid G (canonicalAtomFactorization L₀))
    (hreg : RoutedWindowRegularity H)
    (henergy : RoutedEnergyNormalization H)
    (T : ℝ) (v : ℝ → ℝ) (L : ℝ → ℝ) (n : ℕ)
    (hL : ∀ T, 0 < L T)
    (hfull : @QuarticGramFamily.fullLength σ T ≠ 0)
    (hphysicalMass : (∫ u : ℝ, F.windowEnergy T u) ≠ 0)
    (hchannels : 0 < F.channelCount T)
    (hwindow : ∀ (j : Fin (F.channelCount T)) (u : ℝ),
      F.window T j u =
        shrinkingProfileShellWindow v (L T) n (hL T) u)
    (hshellMass :
      (∫ u : ℝ,
        (shrinkingProfileShellWindow v (L T) n (hL T) u ^ 2 : ℂ)) ≠ 0) :
    routedEnergyQuarticNumerator q H T =
      shrinkingAnnularNormalizedQuarticNumerator
        q F v L hL T n := by
  unfold routedEnergyQuarticNumerator
    shrinkingAnnularNormalizedQuarticNumerator
  apply QuarticTransfer.pairKernelQuarticNumerator_congr
  intro ρ hρ ρ' hρ'
  exact routedEnergyPairKernel_eq_shrinkingProfileShell
    H hreg henergy T v (L T) n (hL T)
      hfull hphysicalMass hchannels hwindow hshellMass ρ ρ'

end AnnularEnergyBridge
end Zeta85
end RH

end
