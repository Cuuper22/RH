/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/HBToBBLRSmoothGrouping.lean

An exact method-class audit of the fixed asymmetric grouping claimed in
docs/run/12.  BBLR Proposition 3.1 has one arbitrary coefficient variable
and two literal smooth variables on each side.  This module considers the
literal-slot class in which each of those smooth variables is one original
unrestricted Heath--Brown slot; multiplying several slots into a smooth
variable is excluded because it introduces a divisor coefficient.

At eta = 43/100, the legal K=4, j=1 dyadic exponent block

  mu, mu, zeta, log = 43/200, 43/200, 2/5, 3/5

has total exponent 143/100.  Its two irregular atoms give the requested
outer exponent 43/100 exactly, every irregular atom lies below the K=4 cap,
and neither unrestricted atom crosses the Type-I threshold 1.  Nevertheless
its only literal smooth scales are 2/5 and 3/5.  They stay a fixed exponent
distance from both run-12 target pairs (1/2,1/2) and (7/100,93/100), so an
o(1) support cushion cannot repair the grouping.

This kills only the fixed-scale literal-slot method class.  It does not rule
out a higher-dimensional quadratic-divisor theorem retaining all factor
variables, or a new coefficient identity that constructs the requested
smooth variables with proved derivative bounds and exact recombination.
-/
import RH.Zeta85.Discharge.HBDepthFour
import RH.Zeta85.Discharge.BBLRGCDAllocation

open scoped BigOperators ArithmeticFunction

noncomputable section

namespace RH.Zeta85.HBToBBLRSmoothGrouping

open RH.Zeta85.HBDepthFour

/-! ## Exact endpoint and source inventory -/

/-- The cycle-5 endpoint eta. -/
def eta : ℝ := 43 / 100

/-- The exponent of X = T^(1+eta). -/
def traceExponent : ℝ := 1 + eta

/-- The largest exponent of a K=4 truncated irregular atom. -/
def irregularCap : ℝ := traceExponent / 4

/-- A smooth atom reaching this exponent is the cycle-4 Type-I alternative. -/
def typeIThreshold : ℝ := traceExponent - eta

/-- Exponent of each of the two truncated Moebius slots in the counterexample. -/
def terminalMuExponent : ℝ := 43 / 200

/-- The two unrestricted slots of the K=4, j=1 counterexample: zeta and log. -/
def terminalSmoothExponent : Fin 2 → ℝ := ![2 / 5, 3 / 5]

/-- The formal eight-slot inventory really contains, in component j=1,
two truncated Moebius slots, one zeta slot, one log slot, and four identities. -/
theorem hb_component_one_inventory (Z : ℕ) :
    hbAtom Z (1 : Fin 4) 0 = muCut Z ∧
      hbAtom Z (1 : Fin 4) 1 = muCut Z ∧
      hbAtom Z (1 : Fin 4) 2 = 1 ∧
      hbAtom Z (1 : Fin 4) 3 = 1 ∧
      hbAtom Z (1 : Fin 4) 4 = (ArithmeticFunction.zeta : AF) ∧
      hbAtom Z (1 : Fin 4) 5 = 1 ∧
      hbAtom Z (1 : Fin 4) 6 = 1 ∧
      hbAtom Z (1 : Fin 4) 7 = ArithmeticFunction.log := by
  simp [hbAtom]

/-- The zero-based component `j = 1` is the signed two-Möbius summand. -/
theorem hb_component_one_scalar :
    hbScalar (1 : Fin 4) = -(6 : AF) := by
  rfl

/-- Once the truncation contains `2`, a Möbius slot is not a
coefficient-one unrestricted slot: it differs from zeta already at `2`.
This is why the two Möbius atoms in the literal-slot class must remain in
the arbitrary outer coefficient. -/
theorem muCut_ne_coefficientOne {Z : ℕ} (hZ : 2 ≤ Z) :
    muCut Z ≠ (ArithmeticFunction.zeta : AF) := by
  intro h
  have h2 := DFunLike.congr_fun h 2
  norm_num [muCut, hZ] at h2
  have hm : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  rw [hm] at h2
  norm_num at h2

/-- The proved BBLR gcd allocation only reindexes the outer/smooth pair it
is given.  In particular, its output still contains the supplied `smooth`
function; it does not construct a new smooth Heath--Brown factor. -/
theorem bblr_allocation_preserves_supplied_smooth
    (alpha smooth : ℕ → ℂ) {d p : ℕ} (hd : 0 < d) (hp : 0 < p) :
    RH.Zeta85.BBLRGCDAllocation.collapsedCoeff alpha smooth d p =
      ∑ AM ∈ (d * p).divisorsAntidiagonal, alpha AM.1 * smooth AM.2 :=
  RH.Zeta85.BBLRGCDAllocation.collapsedCoeff_eq_divisorSum
    alpha smooth hd hp

/-- Exact legality of the counterexample exponent block.  In order:
the truncated slots are positive and below the K=4 cap; the unrestricted
slots are positive and below the Type-I threshold; all four slots have
product exponent 143/100; and the two truncated slots already have outer
exponent eta. -/
theorem terminal_component_one_legal :
    0 < terminalMuExponent ∧
      terminalMuExponent ≤ irregularCap ∧
      (∀ i : Fin 2, 0 < terminalSmoothExponent i) ∧
      (∀ i : Fin 2, terminalSmoothExponent i < typeIThreshold) ∧
      2 * terminalMuExponent +
          terminalSmoothExponent 0 + terminalSmoothExponent 1 = traceExponent ∧
      2 * terminalMuExponent = eta := by
  simp only [terminalMuExponent, irregularCap, traceExponent, eta,
    typeIThreshold]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · intro i
    fin_cases i <;> norm_num [terminalSmoothExponent]
  constructor
  · intro i
    fin_cases i <;> norm_num [terminalSmoothExponent]
  constructor <;> norm_num [terminalSmoothExponent]

/-! ## Literal-slot method class -/

/-- A one-side fixed-scale BBLR assignment in the literal-slot class.
The indices range only over the two unrestricted component-j=1 slots.  The
other two nontrivial slots are Moebius coefficients and therefore must stay
in the outer arbitrary coefficient.  `eps` records exponent slack. -/
def LiteralSideGrouping (M1 M2 eps : ℝ) : Prop :=
  ∃ first second : Fin 2,
    first ≠ second ∧
      |terminalSmoothExponent first - M1| ≤ eps ∧
      |terminalSmoothExponent second - M2| ≤ eps

/-- The two-sided asymmetric assignment asserted in run 12. -/
def AsymmetricLiteralGrouping (eps : ℝ) : Prop :=
  LiteralSideGrouping (1 / 2) (1 / 2) eps ∧
    LiteralSideGrouping (1 / 2 - eta) (1 / 2 + eta) eps

/-- Both available left smooth slots are exactly 1/10 away from exponent 1/2. -/
theorem left_literal_gap (i : Fin 2) :
    |terminalSmoothExponent i - 1 / 2| = 1 / 10 := by
  fin_cases i <;> norm_num [terminalSmoothExponent]

/-- Either available smooth slot is at least 33/100 away from the requested
short right exponent 1/2-eta = 7/100. -/
theorem right_short_literal_gap (i : Fin 2) :
    33 / 100 ≤ |terminalSmoothExponent i - (1 / 2 - eta)| := by
  fin_cases i <;> norm_num [terminalSmoothExponent, eta]

/-- Either available smooth slot is at least 33/100 away from the requested
long right exponent 1/2+eta = 93/100. -/
theorem right_long_literal_gap (i : Fin 2) :
    33 / 100 ≤ |terminalSmoothExponent i - (1 / 2 + eta)| := by
  fin_cases i <;> norm_num [terminalSmoothExponent, eta]

/-- The counterexample cannot have the fixed left split M1=M2=T^(1/2),
even with any exponent cushion strictly smaller than 1/10. -/
theorem no_left_literal_grouping {eps : ℝ} (heps : eps < 1 / 10) :
    ¬LiteralSideGrouping (1 / 2) (1 / 2) eps := by
  rintro ⟨first, _second, _hne, hclose, _⟩
  have hgap := left_literal_gap first
  rw [hgap] at hclose
  linarith

/-- The same counterexample cannot have the fixed right split
(N1,N2)=(T^(7/100),T^(93/100)); already the short target has a fixed
33/100 gap. -/
theorem no_right_literal_grouping {eps : ℝ} (heps : eps < 33 / 100) :
    ¬LiteralSideGrouping (1 / 2 - eta) (1 / 2 + eta) eps := by
  rintro ⟨first, _second, _hne, hclose, _⟩
  have hgap := right_short_literal_gap first
  linarith

/-- Therefore not every legal K=4 terminal dyadic block admits the full
run-12 asymmetric literal-slot assignment.  A 1/10 exponent cushion is
already too small, so a T^o(1) grouping slack cannot change the verdict. -/
theorem no_asymmetric_literal_grouping {eps : ℝ} (heps : eps < 1 / 10) :
    ¬AsymmetricLiteralGrouping eps := by
  rintro ⟨left, _right⟩
  exact no_left_literal_grouping heps left

/-! ## Why multiplying smooth slots is outside the literal class -/

/-- The coefficient introduced when two coefficient-one variables are
collapsed to their product: one term for every ordered factor pair. -/
def twoUnitSlotMultiplicity (n : ℕ) : ℕ := n.divisorsAntidiagonal.card

theorem twoUnitSlotMultiplicity_two : twoUnitSlotMultiplicity 2 = 2 := by decide

theorem twoUnitSlotMultiplicity_four : twoUnitSlotMultiplicity 4 = 3 := by decide

/-- Collapsing two coefficient-one HB slots produces a genuinely
coefficient-bearing arithmetic function, rather than another literal
coefficient-one smooth slot. -/
theorem two_unit_slot_collapse_not_constant :
    twoUnitSlotMultiplicity 2 ≠ twoUnitSlotMultiplicity 4 := by
  norm_num [twoUnitSlotMultiplicity_two, twoUnitSlotMultiplicity_four]

/-- The same multiplicity is exactly the Dirichlet convolution zeta*zeta. -/
theorem zeta_sq_eq_twoUnitSlotMultiplicity (n : ℕ) :
    (((ArithmeticFunction.zeta : AF) * (ArithmeticFunction.zeta : AF)) n) =
      twoUnitSlotMultiplicity n := by
  rw [ArithmeticFunction.mul_apply]
  calc
    (∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.zeta : AF) x.1 *
          (ArithmeticFunction.zeta : AF) x.2) =
        ∑ _x ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨hprod, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have hxne : x.1 ≠ 0 ∧ x.2 ≠ 0 := by
        rwa [← Nat.mul_ne_zero_iff, hprod]
      simp [hxne.1, hxne.2]
    _ = twoUnitSlotMultiplicity n := by
      simp [twoUnitSlotMultiplicity]

end RH.Zeta85.HBToBBLRSmoothGrouping

end
