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

end ComplexAliasBridge
end Zeta85
end RH

end
