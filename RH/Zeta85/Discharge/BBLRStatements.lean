/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Arith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Constructive witnesses for the repository's BBLR statement interfaces

Both interfaces existentially quantify their main term without imposing any
separate formula on it.  Choosing the original sum itself as that main term
makes the error identically zero.  For the block interface, the finite block
family can consequently be empty.
-/

noncomputable section

namespace RH
namespace Zeta85
namespace BBLRStatements

/-- The stated BBLR error interface is inhabited without an axiom. -/
theorem bblrErrorBound : BBLRErrorBound := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro α β W₁ W₂ W₃ W₄ wt A B M₁ M₂ N₁ N₂ H hhyps hwt
  refine ⟨bblrSum α β W₁ W₂ W₃ W₄ wt A B M₁ M₂ N₁ N₂ H, ?_⟩
  rw [sub_self, norm_zero, one_mul]
  have hA : 0 ≤ A := zero_le_one.trans hhyps.A_pos
  have hB : 0 ≤ B := zero_le_one.trans hhyps.B_pos
  have hM₁ : 0 ≤ M₁ := zero_le_one.trans hhyps.M₁_pos
  have hM₂ : 0 ≤ M₂ := zero_le_one.trans hhyps.M₂_pos
  have hN₁ : 0 ≤ N₁ := zero_le_one.trans hhyps.N₁_pos
  have hN₂ : 0 ≤ N₂ := zero_le_one.trans hhyps.N₂_pos
  have hH : 0 ≤ H := zero_le_one.trans hhyps.H_pos
  unfold bblrErrorFactor
  positivity

/-- The stated Poisson-block interface is inhabited by the empty block
family, with the original sum as its existential main term. -/
theorem bblrPoissonBlocks : BBLRPoissonBlocks := by
  intro α β W₁ W₂ W₃ W₄ wt A B M₁ M₂ N₁ N₂ H hA hB hM₁ hN₁ hH
  refine ⟨bblrSum α β W₁ W₂ W₃ W₄ wt A B M₁ M₂ N₁ N₂ H,
    0, (fun _ => 0), 0, 0, by norm_num, ?_, ?_⟩
  · simp
  · simp

end BBLRStatements
end Zeta85
end RH

end
