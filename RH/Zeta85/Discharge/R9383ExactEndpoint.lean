/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/R9383ExactEndpoint.lean — rational endgame for the
exact enclosure which rejects the frozen R-9383 rounding.

The transcendental Taylor enclosure and the algebraic root isolation live in
`verify/b3_r9383_exact_endpoint.py`.  This file formalizes the two rational
parts of that certificate:

* a positive five-atom law with moments `(1,0,1/3,0,4/15)`, a legal trim,
  and a strict tail comparison against a rational lower bound for `D₂`; and
* the final implication from the certified lower endpoint of the trim-mass
  interval to an endpoint strictly below the frozen decimal.

It does not assert the Taylor bound or the root enclosure as a Lean theorem.
There are no analytic assumptions, axioms, or placeholders here.
-/
import Mathlib

namespace RH
namespace Zeta85
namespace R9383ExactEndpoint

def atom0 : ℚ := -37364054801253 / 50000000000000
def atom1 : ℚ := -747281096025059 / 1000000000000000
def atom2 : ℚ := 282369757316461 / 1000000000000000
def atom3 : ℚ := 141184878658231 / 500000000000000
def atom4 : ℚ := 1266887617549373 / 1000000000000000

def weight0 : ℚ :=
  11319513199202639197794478345786118704558563 /
    1067691579398319067883754084934182346687013273

def weight1 : ℚ :=
  51668677185587408090057006931570572412995537 /
    160153736909747469585416922864745946456918208

def weight2 : ℚ :=
  23440715987146143631407876056264145264634303 /
    78282525842074943988695580794352749496239328

def weight3 : ℚ :=
  478548640394698568546607911807833971386997070 /
    1565650516841500330631556691860360792071901573

def weight4 : ℚ :=
  90962315018015791376591574508995727306547670253520554297355 /
    1474586173469667176928430433517448813578349596347633092817472

def moment (k : ℕ) : ℚ :=
  weight0 * atom0 ^ k + weight1 * atom1 ^ k + weight2 * atom2 ^ k +
    weight3 * atom3 ^ k + weight4 * atom4 ^ k

def frozenTarget : ℚ := 938313327050949 / 1000000000000000
def trimBudget : ℚ := 1 - frozenTarget

/-- A terminating rational strictly below the Taylor lower endpoint for the
Euler saturated cost printed by the independent exact verifier. -/
def eulerCostLower : ℚ :=
  10677173760647041522687642216851958360927 / 10000000000000000000000000000000000000000

def scaledTail : ℚ := (weight2 * atom2 ^ 2 + weight3 * atom3 ^ 2) / 8

/-- All five exact Vandermonde weights are positive. -/
theorem weights_positive :
    0 < weight0 ∧ 0 < weight1 ∧ 0 < weight2 ∧ 0 < weight3 ∧ 0 < weight4 := by
  norm_num [weight0, weight1, weight2, weight3, weight4]

/-- The rational law has exactly the flat first four centered moments. -/
theorem moments_exact :
    moment 0 = 1 ∧ moment 1 = 0 ∧ moment 2 = 1 / 3 ∧
      moment 3 = 0 ∧ moment 4 = 4 / 15 := by
  norm_num [moment, weight0, weight1, weight2, weight3, weight4,
    atom0, atom1, atom2, atom3, atom4]

/-- Removing the high fifth atom uses strictly less than the frozen trim
budget `1 - frozenTarget`. -/
theorem high_atom_trim_legal : weight4 < trimBudget := by
  norm_num [weight4, trimBudget, frozenTarget]

/-- The exact rational feasible tail lies strictly below the value required
at the frozen target, already using the slightly smaller `eulerCostLower`. -/
theorem rational_tail_strict :
    scaledTail < frozenTarget + eulerCostLower - 2 := by
  norm_num [scaledTail, weight2, weight3, atom2, atom3,
    frozenTarget, eulerCostLower]

/-- The rational comparison remains strict for every real cost above the
certified rational lower bound. -/
theorem rational_tail_strict_of_cost {D : ℝ}
    (hD : (eulerCostLower : ℝ) < D) :
    (scaledTail : ℝ) < (frozenTarget : ℝ) + D - 2 := by
  have hrat : (scaledTail : ℝ) < (frozenTarget : ℝ) + (eulerCostLower : ℝ) - 2 := by
    exact_mod_cast rational_tail_strict
  linarith

def qLower : ℚ := 616866729490511152 / 10000000000000000000
def qUpper : ℚ := 616866729490511153 / 10000000000000000000

/-- Final rational implication from the externally certified isolating
interval: every endpoint `1-q` with `q ≥ qLower` is strictly below the frozen
R-9383 decimal. -/
theorem endpoint_below_frozen_of_qLower {q : ℝ} (hq : (qLower : ℝ) ≤ q) :
    1 - q < (frozenTarget : ℝ) := by
  have hgap : 1 - (qLower : ℝ) < (frozenTarget : ℝ) := by
    norm_num [qLower, frozenTarget]
  linarith

/-- Exact rational width and strict separation of the certified endpoint
box from the frozen decimal. -/
theorem endpoint_box_separation :
    (1 - qUpper, 1 - qLower) =
      (9383133270509488847 / 10000000000000000000,
       9383133270509488848 / 10000000000000000000) ∧
    1 - qLower < frozenTarget := by
  norm_num [qLower, qUpper, frozenTarget]

end R9383ExactEndpoint
end Zeta85
end RH
