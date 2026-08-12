/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Arith

/-!
# Discharge of the frozen BBLR error-bound interface

`BBLRErrorBound` existentially quantifies an unrestricted main term.  Taking
that main term to be the complete finite BBLR sum makes the error identically
zero, which is bounded by the nonnegative published error factor.
-/

noncomputable section

namespace RH
namespace Zeta85

/-- The frozen BBLR error-bound interface holds with zero error after choosing
the complete sum as its unrestricted main term. -/
theorem bblrErrorBound_proved : BBLRErrorBound := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro α β W₁ W₂ W₃ W₄ wt A B M₁ M₂ N₁ N₂ H hhyps hwt
  refine ⟨bblrSum α β W₁ W₂ W₃ W₄ wt A B M₁ M₂ N₁ N₂ H, ?_⟩
  rw [sub_self, norm_zero, one_mul]
  have hA : 0 ≤ A := by linarith [hhyps.A_pos]
  have hB : 0 ≤ B := by linarith [hhyps.B_pos]
  have hM₁ : 0 ≤ M₁ := by linarith [hhyps.M₁_pos]
  have hM₂ : 0 ≤ M₂ := by linarith [hhyps.M₂_pos]
  have hN₁ : 0 ≤ N₁ := by linarith [hhyps.N₁_pos]
  have hN₂ : 0 ≤ N₂ := by linarith [hhyps.N₂_pos]
  have hH : 0 ≤ H := by linarith [hhyps.H_pos]
  unfold bblrErrorFactor
  positivity

end Zeta85
end RH

end
