/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/HBDepthFour.lean

An exact, assumption-free coefficient layer for the depth-four Heath--Brown route.

This module constructs the sharp-cutoff identity

  Λ = 4 μ_Z*log - 6 μ_Z^2*ζ*log + 4 μ_Z^3*ζ^2*log - μ_Z^4*ζ^3*log

coefficientwise on n ≤ Z^4.  It retains all eight factor slots, permits an
explicit grouping at every common dyadic scale, expands a candidate
d₁d₂=d divisor allocation at fixed d into finite coefficients, and supplies
exact support and absolute majorants.  Generic residue cells are centered by
their constructed mean; they are not identified with the planned block.

Honesty boundary: docs/run/12 never supplies the sharp/smooth cutoff
identification, its scale-dependent grouping plan, the Fourier factor
F_{d,ell}, or the pointwise equality between its zero frequency and the
prime-pair singular series.  Accordingly no definition below is claimed to
be that source's c_{d,p} or e_{d,q}, and no cross-Y, EDB, WG-HB, or trace-grade
estimate is asserted.  SingularSeriesCentering names the exact remaining
pointwise equality without assuming it.
-/
import RH.Zeta85.Arith

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
open Finset

noncomputable section

namespace RH.Zeta85.HBDepthFour

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

abbrev AF := ArithmeticFunction ℝ

def muCut (Z : ℕ) : AF :=
  ⟨fun n => if n ≤ Z then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

def hb4 (Z : ℕ) : AF :=
  (4 : AF) * (muCut Z * ArithmeticFunction.log)
    - (6 : AF) * ((muCut Z) ^ 2 * (ArithmeticFunction.zeta : AF) * ArithmeticFunction.log)
    + (4 : AF) * ((muCut Z) ^ 3 * (ArithmeticFunction.zeta : AF) ^ 2 *
        ArithmeticFunction.log)
    - ((muCut Z) ^ 4 * (ArithmeticFunction.zeta : AF) ^ 3 *
        ArithmeticFunction.log)

/-- One explicitly retained short Möbius factor in every depth-four summand. -/
def hbRetained (Z : ℕ) (_ : Fin 4) : AF := muCut Z

/-- The complementary factor after retaining one short Möbius factor. -/
def hbComplement (Z : ℕ) : Fin 4 → AF :=
  ![(4 : AF) * ArithmeticFunction.log,
    -(6 : AF) * (muCut Z * (ArithmeticFunction.zeta : AF) * ArithmeticFunction.log),
    (4 : AF) * ((muCut Z) ^ 2 * (ArithmeticFunction.zeta : AF) ^ 2 *
      ArithmeticFunction.log),
    -((muCut Z) ^ 3 * (ArithmeticFunction.zeta : AF) ^ 3 *
      ArithmeticFunction.log)]

def hbComponent (Z : ℕ) (j : Fin 4) : AF :=
  hbRetained Z j * hbComplement Z j

lemma hbComponent_factorization (Z : ℕ) (j : Fin 4) :
    hbComponent Z j = hbRetained Z j * hbComplement Z j := rfl

lemma sum_hbComponent (Z : ℕ) :
    ∑ j : Fin 4, hbComponent Z j = hb4 Z := by
  simp [hbComponent, hbRetained, hbComplement, hb4, Fin.sum_univ_four]
  ring

def hbAtom (Z : ℕ) : Fin 4 → Fin 8 → AF :=
  ![![(muCut Z), 1, 1, 1, 1, 1, 1, ArithmeticFunction.log],
    ![(muCut Z), (muCut Z), 1, 1, (ArithmeticFunction.zeta : AF), 1, 1,
      ArithmeticFunction.log],
    ![(muCut Z), (muCut Z), (muCut Z), 1, (ArithmeticFunction.zeta : AF),
      (ArithmeticFunction.zeta : AF), 1, ArithmeticFunction.log],
    ![(muCut Z), (muCut Z), (muCut Z), (muCut Z),
      (ArithmeticFunction.zeta : AF), (ArithmeticFunction.zeta : AF),
      (ArithmeticFunction.zeta : AF), ArithmeticFunction.log]]

def hbScalar : Fin 4 → AF := ![(4 : AF), -(6 : AF), (4 : AF), -(1 : AF)]

def hbGroupedLeft (Z : ℕ) (j : Fin 4) (S : Finset (Fin 8)) : AF :=
  ∏ s ∈ S, hbAtom Z j s

def hbGroupedRight (Z : ℕ) (j : Fin 4) (S : Finset (Fin 8)) : AF :=
  hbScalar j * ∏ s ∈ Sᶜ, hbAtom Z j s

lemma hbAtom_product (Z : ℕ) (j : Fin 4) :
    hbScalar j * ∏ s : Fin 8, hbAtom Z j s = hbComponent Z j := by
  fin_cases j <;>
    simp [hbScalar, hbAtom, hbComponent, hbRetained, hbComplement, Fin.prod_univ_eight] <;>
    ring

lemma hbGrouped_factorization (Z : ℕ) (j : Fin 4) (S : Finset (Fin 8)) :
    hbGroupedLeft Z j S * hbGroupedRight Z j S = hbComponent Z j := by
  rw [hbGroupedLeft, hbGroupedRight]
  rw [show (∏ s ∈ S, hbAtom Z j s) *
      (hbScalar j * ∏ s ∈ Sᶜ, hbAtom Z j s) =
      hbScalar j * ((∏ s ∈ S, hbAtom Z j s) *
        ∏ s ∈ Sᶜ, hbAtom Z j s) by ring]
  rw [Finset.prod_mul_prod_compl]
  exact hbAtom_product Z j

lemma empty_singleton_groupings_distinct :
    hbGroupedLeft 2 (0 : Fin 4) ∅ ≠ hbGroupedLeft 2 (0 : Fin 4) {0} := by
  intro h
  have h2 := congrArg (fun f : AF => f 2) h
  simp [hbGroupedLeft, hbAtom, muCut,
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2)] at h2

lemma abs_muCut_le_one (Z n : ℕ) : |muCut Z n| ≤ 1 := by
  by_cases hn : n ≤ Z
  · change |if n ≤ Z then (ArithmeticFunction.moebius n : ℝ) else 0| ≤ 1
    rw [if_pos hn]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp [muCut, hn]

lemma muCut_eq_zero_of_lt {Z n : ℕ} (h : Z < n) : muCut Z n = 0 := by
  simp [muCut, Nat.not_le.mpr h]

lemma mul_zero_below_mul (f g : AF) (A B : ℕ)
    (hf : ∀ n, n ≤ A → f n = 0) (hg : ∀ n, n ≤ B → g n = 0) :
    ∀ n, n ≤ A * B → (f * g) n = 0 := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro xy hxy
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hxy).1
  by_cases hx : xy.1 ≤ A
  · simp [hf _ hx]
  by_cases hy : xy.2 ≤ B
  · simp [hg _ hy]
  exfalso
  have hx' : A < xy.1 := Nat.lt_of_not_ge hx
  have hy' : B < xy.2 := Nat.lt_of_not_ge hy
  have hlt : A * B < xy.1 * xy.2 :=
    mul_lt_mul' hx'.le hy' (Nat.zero_le _) (Nat.zero_lt_of_lt hx')
  rw [hprod] at hlt
  exact (Nat.not_lt_of_ge hn) hlt

lemma mul_zero_below_left (f g : AF) (A : ℕ)
    (hf : ∀ n, n ≤ A → f n = 0) :
    ∀ n, n ≤ A → (f * g) n = 0 := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro xy hxy
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hxy
  have hxy0 : xy.1 ≠ 0 ∧ xy.2 ≠ 0 := by
    rwa [← Nat.mul_ne_zero_iff, hprod]
  have hxle : xy.1 ≤ n := by
    rw [← hprod]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hxy0.2)
  simp [hf _ (hxle.trans hn)]

lemma muCut_tail_zero (Z n : ℕ) (hn : n ≤ Z) :
    ((ArithmeticFunction.moebius : AF) - muCut Z) n = 0 := by
  change (ArithmeticFunction.moebius n : ℝ) -
      (if n ≤ Z then (ArithmeticFunction.moebius n : ℝ) else 0) = 0
  rw [if_pos hn]
  ring

lemma muCut_tail_four_zero (Z n : ℕ) (hn : n ≤ Z ^ 4) :
    (((ArithmeticFunction.moebius : AF) - muCut Z) ^ 4) n = 0 := by
  let t : AF := (ArithmeticFunction.moebius : AF) - muCut Z
  have ht : ∀ m, m ≤ Z → t m = 0 := by
    intro m hm
    exact muCut_tail_zero Z m hm
  have h2 : ∀ m, m ≤ Z * Z → (t ^ 2) m = 0 := by
    simpa [pow_two] using mul_zero_below_mul t t Z Z ht ht
  have h4 : ∀ m, m ≤ (Z * Z) * (Z * Z) → ((t ^ 2) * (t ^ 2)) m = 0 :=
    mul_zero_below_mul (t ^ 2) (t ^ 2) (Z * Z) (Z * Z) h2 h2
  have hpow : t ^ 4 = (t ^ 2) * (t ^ 2) := by ring
  change (t ^ 4) n = 0
  rw [hpow]
  apply h4 n
  simpa [pow_succ, mul_assoc] using hn

def inDyadicBlock (j n : ℕ) : Prop :=
  2 ^ j ≤ n ∧ n < 2 ^ (j + 1)

instance instDecidableInDyadicBlock (j n : ℕ) : Decidable (inDyadicBlock j n) := by
  unfold inDyadicBlock
  infer_instance

def dyadicPart (f : AF) (j : ℕ) : AF :=
  ⟨fun n => if inDyadicBlock j n then f n else 0, by
    simp [inDyadicBlock]⟩

@[simp]
lemma dyadicPart_apply (f : AF) (j n : ℕ) :
    dyadicPart f j n = if inDyadicBlock j n then f n else 0 := rfl

lemma dyadicPart_support {f : AF} {j n : ℕ} (h : dyadicPart f j n ≠ 0) :
    inDyadicBlock j n := by
  by_contra hn
  exact h (by simp [dyadicPart_apply, hn])

lemma abs_dyadicPart_le (f : AF) (j n : ℕ) :
    |dyadicPart f j n| ≤ |f n| := by
  by_cases h : inDyadicBlock j n <;> simp [dyadicPart_apply, h]

lemma inDyadicBlock_iff_log_eq {j n : ℕ} (hn : n ≠ 0) :
    inDyadicBlock j n ↔ Nat.log 2 n = j := by
  constructor
  · rintro ⟨hl, hu⟩
    exact Nat.log_eq_of_pow_le_of_lt_pow hl (by simpa [Nat.succ_eq_add_one] using hu)
  · intro h
    subst j
    exact ⟨Nat.pow_log_le_self 2 hn,
      by simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two n⟩

lemma sum_dyadicPart_apply (f : AF) {n : ℕ} (hn : n ≠ 0) :
    ∑ j ∈ Finset.range (Nat.log 2 n + 1), dyadicPart f j n = f n := by
  have hj : Nat.log 2 n ∈ Finset.range (Nat.log 2 n + 1) := by simp
  calc
    ∑ j ∈ Finset.range (Nat.log 2 n + 1), dyadicPart f j n =
        dyadicPart f (Nat.log 2 n) n := by
      apply Finset.sum_eq_single (Nat.log 2 n)
      · intro j hj' hne
        simp [dyadicPart_apply, inDyadicBlock_iff_log_eq hn, Ne.symm hne]
      · simp [hj]
    _ = f n := by
      simp [dyadicPart_apply, inDyadicBlock_iff_log_eq hn]

def dilateCoeff (f : AF) (d : ℕ) : AF :=
  ⟨fun n => f (d * n), by simp⟩

def reducedCoeff (α β : AF) (d₁ d₂ p : ℕ) : ℝ :=
  ∑ xy ∈ p.divisorsAntidiagonal, α (d₁ * xy.1) * β (d₂ * xy.2)

lemma reducedCoeff_eq_convolution (α β : AF) (d₁ d₂ p : ℕ) :
    reducedCoeff α β d₁ d₂ p =
      (dilateCoeff α d₁ * dilateCoeff β d₂) p := by
  rfl

/-- The literal d₁d₂=d divisor split.  This exposes the algebraic indices
used in run 12 but does not add its omitted smooth weights, allocation
restrictions, or cross-side gcd conditions. -/
def splitCoeff (α β : AF) (d p : ℕ) : ℝ :=
  ∑ dd ∈ d.divisorsAntidiagonal, reducedCoeff α β dd.1 dd.2 p

def reducedMajorant (α β : AF) (d₁ d₂ p : ℕ) : ℝ :=
  ∑ xy ∈ p.divisorsAntidiagonal, |α (d₁ * xy.1)| * |β (d₂ * xy.2)|

def splitMajorant (α β : AF) (d p : ℕ) : ℝ :=
  ∑ dd ∈ d.divisorsAntidiagonal, reducedMajorant α β dd.1 dd.2 p

lemma abs_reducedCoeff_le (α β : AF) (d₁ d₂ p : ℕ) :
    |reducedCoeff α β d₁ d₂ p| ≤ reducedMajorant α β d₁ d₂ p := by
  unfold reducedCoeff reducedMajorant
  calc
    |∑ xy ∈ p.divisorsAntidiagonal, α (d₁ * xy.1) * β (d₂ * xy.2)| ≤
        ∑ xy ∈ p.divisorsAntidiagonal,
          |α (d₁ * xy.1) * β (d₂ * xy.2)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ xy ∈ p.divisorsAntidiagonal,
        |α (d₁ * xy.1)| * |β (d₂ * xy.2)| := by simp [abs_mul]

lemma abs_splitCoeff_le (α β : AF) (d p : ℕ) :
    |splitCoeff α β d p| ≤ splitMajorant α β d p := by
  unfold splitCoeff splitMajorant
  calc
    |∑ dd ∈ d.divisorsAntidiagonal, reducedCoeff α β dd.1 dd.2 p| ≤
        ∑ dd ∈ d.divisorsAntidiagonal, |reducedCoeff α β dd.1 dd.2 p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ dd ∈ d.divisorsAntidiagonal, reducedMajorant α β dd.1 dd.2 p := by
      gcongr with dd hdd
      exact abs_reducedCoeff_le α β dd.1 dd.2 p

@[simp]
lemma splitCoeff_zero_d (α β : AF) (p : ℕ) : splitCoeff α β 0 p = 0 := by
  simp [splitCoeff]

@[simp]
lemma splitCoeff_zero_p (α β : AF) (d : ℕ) : splitCoeff α β d 0 = 0 := by
  simp [splitCoeff, reducedCoeff]

lemma reducedMajorant_nonneg (α β : AF) (d₁ d₂ p : ℕ) :
    0 ≤ reducedMajorant α β d₁ d₂ p := by
  exact Finset.sum_nonneg fun xy _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

lemma splitMajorant_nonneg (α β : AF) (d p : ℕ) :
    0 ≤ splitMajorant α β d p := by
  exact Finset.sum_nonneg fun dd _ => reducedMajorant_nonneg α β dd.1 dd.2 p

structure CommonScaleGeometry where
  baseH : ℕ
  Q : ℕ

namespace CommonScaleGeometry

def H (G : CommonScaleGeometry) (j : ℕ) : ℕ := G.baseH * 2 ^ j

def P (G : CommonScaleGeometry) (j : ℕ) : ℕ := G.H j * G.Q

def Y (G : CommonScaleGeometry) (j : ℕ) : ℕ := G.P j * G.Q

lemma P_eq_H_mul_Q (G : CommonScaleGeometry) (j : ℕ) :
    G.P j = G.H j * G.Q := rfl

lemma Y_eq_P_mul_Q (G : CommonScaleGeometry) (j : ℕ) :
    G.Y j = G.P j * G.Q := rfl

lemma Y_eq_H_mul_Q_sq (G : CommonScaleGeometry) (j : ℕ) :
    G.Y j = G.H j * G.Q ^ 2 := by
  simp [Y, P, pow_two, mul_assoc]

end CommonScaleGeometry

def sizeBlock (X : ℕ) : Finset ℕ := Finset.Icc X (2 * X)

structure HBBlockAddress where
  scale : ℕ
  d : ℕ
  ell : ℤ
  p : ℕ
  q : ℕ
  leftTerm : Fin 4
  rightTerm : Fin 4
deriving DecidableEq

/-- A literal grouping choice at every common dyadic scale for the two
depth-four von Mangoldt expansions.  This is data only: it has no estimate or
closure field. -/
structure HBGroupingPlan where
  left : ℕ → Fin 4 → Finset (Fin 8)
  right : ℕ → Fin 4 → Finset (Fin 8)

def canonicalGroupingPlan : HBGroupingPlan where
  left := fun _ _ => {0}
  right := fun _ _ => {0}

def localizedSplitCoeff (X : ℕ) (α β : AF) (d n : ℕ) : ℝ :=
  if n ∈ sizeBlock X then splitCoeff α β d n else 0

lemma localizedSplitCoeff_support {X : ℕ} {α β : AF} {d n : ℕ}
    (h : localizedSplitCoeff X α β d n ≠ 0) : n ∈ sizeBlock X := by
  by_contra hn
  exact h (by simp [localizedSplitCoeff, hn])

lemma abs_localizedSplitCoeff_le (X : ℕ) (α β : AF) (d n : ℕ) :
    |localizedSplitCoeff X α β d n| ≤ splitMajorant α β d n := by
  by_cases h : n ∈ sizeBlock X
  · simpa [localizedSplitCoeff, h] using abs_splitCoeff_le α β d n
  · simp [localizedSplitCoeff, h, splitMajorant_nonneg]

def plannedLeftBlockCoeff (G : CommonScaleGeometry) (plan : HBGroupingPlan)
    (Z : ℕ) (I : HBBlockAddress) : ℝ :=
  localizedSplitCoeff (G.P I.scale / I.d)
    (hbGroupedLeft Z I.leftTerm (plan.left I.scale I.leftTerm))
    (hbGroupedRight Z I.leftTerm (plan.left I.scale I.leftTerm)) I.d I.p

def plannedRightBlockCoeff (G : CommonScaleGeometry) (plan : HBGroupingPlan)
    (Z : ℕ) (I : HBBlockAddress) : ℝ :=
  localizedSplitCoeff (G.Q / I.d)
    (hbGroupedLeft Z I.rightTerm (plan.right I.scale I.rightTerm))
    (hbGroupedRight Z I.rightTerm (plan.right I.scale I.rightTerm)) I.d I.q

lemma plannedLeftBlockCoeff_support {G : CommonScaleGeometry} {plan : HBGroupingPlan}
    {Z : ℕ} {I : HBBlockAddress} (h : plannedLeftBlockCoeff G plan Z I ≠ 0) :
    I.p ∈ sizeBlock (G.P I.scale / I.d) :=
  localizedSplitCoeff_support h

lemma plannedRightBlockCoeff_support {G : CommonScaleGeometry} {plan : HBGroupingPlan}
    {Z : ℕ} {I : HBBlockAddress} (h : plannedRightBlockCoeff G plan Z I ≠ 0) :
    I.q ∈ sizeBlock (G.Q / I.d) :=
  localizedSplitCoeff_support h

lemma abs_plannedLeftBlockCoeff_le (G : CommonScaleGeometry) (plan : HBGroupingPlan)
    (Z : ℕ) (I : HBBlockAddress) :
    |plannedLeftBlockCoeff G plan Z I| ≤
      splitMajorant
        (hbGroupedLeft Z I.leftTerm (plan.left I.scale I.leftTerm))
        (hbGroupedRight Z I.leftTerm (plan.left I.scale I.leftTerm)) I.d I.p :=
  abs_localizedSplitCoeff_le _ _ _ _ _

lemma abs_plannedRightBlockCoeff_le (G : CommonScaleGeometry) (plan : HBGroupingPlan)
    (Z : ℕ) (I : HBBlockAddress) :
    |plannedRightBlockCoeff G plan Z I| ≤
      splitMajorant
        (hbGroupedLeft Z I.rightTerm (plan.right I.scale I.rightTerm))
        (hbGroupedRight Z I.rightTerm (plan.right I.scale I.rightTerm)) I.d I.q :=
  abs_localizedSplitCoeff_le _ _ _ _ _

/-- One weighted summand on the explicit shared address.  The supplied
kernel is where a future construction must place the exact separated
Fourier factor and signed h-shift transform.  The coprimality condition from
the Poisson block is imposed here rather than left to the kernel. -/
def plannedKernelTerm (G : CommonScaleGeometry) (plan : HBGroupingPlan)
    (Z : ℕ) (kernel : HBBlockAddress → ℂ) (I : HBBlockAddress) : ℂ :=
  if Nat.Coprime I.p I.q then
    (plannedLeftBlockCoeff G plan Z I : ℂ) *
      (plannedRightBlockCoeff G plan Z I : ℂ) * kernel I
  else 0

/-- The fixed-q inner family needed to formulate a coefficient-sensitive
WG-HB estimate.  No estimate is part of this definition. -/
def fixedQKernelSum (G : CommonScaleGeometry) (plan : HBGroupingPlan)
    (Z scale d q : ℕ) (ell : ℤ) (leftTerm rightTerm : Fin 4)
    (kernel : HBBlockAddress → ℂ) : ℂ :=
  ∑ p ∈ sizeBlock (G.P scale / d),
    plannedKernelTerm G plan Z kernel
      ⟨scale, d, ell, p, q, leftTerm, rightTerm⟩

/-- The outer q-L1 quantity appearing in the WG-HB route, now stated on
the constructed coefficients and a supplied exact kernel. -/
def fixedQKernelL1 (G : CommonScaleGeometry) (plan : HBGroupingPlan)
    (Z scale d : ℕ) (ell : ℤ) (leftTerm rightTerm : Fin 4)
    (kernel : HBBlockAddress → ℂ) : ℝ :=
  ∑ q ∈ sizeBlock (G.Q / d),
    ‖fixedQKernelSum G plan Z scale d q ell leftTerm rightTerm kernel‖

/-- One finite candidate for the common-scale leading family.  The scale
weight can contain the future T/Y_j normalization, and the supplied finite
frequency range is restricted to nonzero `ell`.  This makes a truncated
cross-Y signed sum a literal expression without asserting its bound or its
frequency-tail estimate. -/
def commonScaleLeadingSum (G : CommonScaleGeometry) (plan : HBGroupingPlan)
    (Z scaleCount dMax : ℕ) (scaleWeight : ℕ → ℂ)
    (ellRange : Finset ℤ) (kernel : HBBlockAddress → ℂ) : ℂ :=
  ∑ scale ∈ Finset.range scaleCount, scaleWeight scale *
    ∑ d ∈ Finset.Icc 1 dMax,
      ∑ ell ∈ ellRange.filter (· ≠ 0),
        ∑ leftTerm : Fin 4, ∑ rightTerm : Fin 4,
          ∑ p ∈ sizeBlock (G.P scale / d), ∑ q ∈ sizeBlock (G.Q / d),
            plannedKernelTerm G plan Z kernel
              ⟨scale, d, ell, p, q, leftTerm, rightTerm⟩

/-- A generic residue-class cell sum.  It is not connected to
`plannedKernelTerm` by any theorem in this module. -/
def progressionCell (c : ℕ → ℝ) (X q r : ℕ) : ℝ :=
  ∑ n ∈ (sizeBlock X).filter (fun n => n % q = r % q), c n

/-- The mean over all residue classes, not only reduced classes.  It is not
claimed to be the zero mode of the source's coprime Poisson block. -/
def progressionZeroMode (c : ℕ → ℝ) (X q : ℕ) : ℝ :=
  if q = 0 then 0
  else (q : ℝ)⁻¹ * ∑ r ∈ Finset.range q, progressionCell c X q r

def centeredProgressionCell (c : ℕ → ℝ) (X q r : ℕ) : ℝ :=
  progressionCell c X q r - progressionZeroMode c X q

lemma sum_centeredProgressionCell (c : ℕ → ℝ) (X q : ℕ) (hq : q ≠ 0) :
    ∑ r ∈ Finset.range q, centeredProgressionCell c X q r = 0 := by
  simp only [centeredProgressionCell, Finset.sum_sub_distrib]
  rw [progressionZeroMode, if_neg hq]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  field_simp
  ring

lemma centeredProgressionCell_eq_error (c : ℕ → ℝ) (X q r : ℕ) :
    centeredProgressionCell c X q r =
      progressionCell c X q r - progressionZeroMode c X q := rfl

/-- The exact equality still required to identify a supplied BBLR zero-mode
function with the singular-series subtraction in the signed pair aggregate.
This is a named predicate, not an assumed fact or a field of the coefficient data. -/
def SingularSeriesCentering (zeroMode S : ℕ → ℝ) (X IV : ℝ) : Prop :=
  ∀ h : ℕ, zeroMode h = S h * X * IV

def singularSeriesCenteringError (zeroMode S : ℕ → ℝ) (X IV : ℝ) (h : ℕ) : ℝ :=
  zeroMode h - S h * X * IV

lemma singularSeriesCentering_iff_error_zero (zeroMode S : ℕ → ℝ) (X IV : ℝ) :
    SingularSeriesCentering zeroMode S X IV ↔
      ∀ h : ℕ, singularSeriesCenteringError zeroMode S X IV h = 0 := by
  constructor <;> intro h
  · intro n
    simp [singularSeriesCenteringError, h n]
  · intro n
    have := h n
    simp only [singularSeriesCenteringError] at this
    linarith

lemma zeta_mul_injective :
    Function.Injective (fun f : AF => (ArithmeticFunction.zeta : AF) * f) := by
  intro f g h
  calc
    f = 1 * f := by rw [one_mul]
    _ = ((ArithmeticFunction.moebius : AF) * (ArithmeticFunction.zeta : AF)) * f := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = (ArithmeticFunction.moebius : AF) *
        ((ArithmeticFunction.zeta : AF) * f) := by rw [mul_assoc]
    _ = (ArithmeticFunction.moebius : AF) *
        ((ArithmeticFunction.zeta : AF) * g) :=
      congrArg (fun x : AF => (ArithmeticFunction.moebius : AF) * x) h
    _ = ((ArithmeticFunction.moebius : AF) * (ArithmeticFunction.zeta : AF)) * g := by
      rw [mul_assoc]
    _ = 1 * g := by rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = g := by rw [one_mul]

lemma hb4_remainder (Z : ℕ) :
    ArithmeticFunction.vonMangoldt - hb4 Z =
      ((ArithmeticFunction.moebius : AF) - muCut Z) ^ 4 *
        (ArithmeticFunction.zeta : AF) ^ 3 * ArithmeticFunction.log := by
  apply zeta_mul_injective
  change (ArithmeticFunction.zeta : AF) *
      (ArithmeticFunction.vonMangoldt - hb4 Z) =
    (ArithmeticFunction.zeta : AF) *
      (((ArithmeticFunction.moebius : AF) - muCut Z) ^ 4 *
        (ArithmeticFunction.zeta : AF) ^ 3 * ArithmeticFunction.log)
  have htail :
      (ArithmeticFunction.zeta : AF) *
          ((ArithmeticFunction.moebius : AF) - muCut Z) =
        1 - (ArithmeticFunction.zeta : AF) * muCut Z := by
    rw [mul_sub, ArithmeticFunction.coe_zeta_mul_coe_moebius]
  have hzhb :
      (ArithmeticFunction.zeta : AF) * hb4 Z =
        (4 : AF) * ((ArithmeticFunction.zeta : AF) * muCut Z *
          ArithmeticFunction.log)
          - (6 : AF) * (((ArithmeticFunction.zeta : AF) * muCut Z) ^ 2 *
            ArithmeticFunction.log)
          + (4 : AF) * (((ArithmeticFunction.zeta : AF) * muCut Z) ^ 3 *
            ArithmeticFunction.log)
          - (((ArithmeticFunction.zeta : AF) * muCut Z) ^ 4 *
            ArithmeticFunction.log) := by
    simp only [hb4]
    ring
  rw [mul_sub, ArithmeticFunction.zeta_mul_vonMangoldt, hzhb]
  rw [show (ArithmeticFunction.zeta : AF) *
      (((ArithmeticFunction.moebius : AF) - muCut Z) ^ 4 *
        (ArithmeticFunction.zeta : AF) ^ 3 * ArithmeticFunction.log) =
      ((ArithmeticFunction.zeta : AF) *
        ((ArithmeticFunction.moebius : AF) - muCut Z)) ^ 4 *
        ArithmeticFunction.log by ring]
  rw [htail]
  ring

theorem hb4_eq_vonMangoldt (Z n : ℕ) (hn : n ≤ Z ^ 4) :
    hb4 Z n = ArithmeticFunction.vonMangoldt n := by
  have htail :
      ((((ArithmeticFunction.moebius : AF) - muCut Z) ^ 4 *
        (ArithmeticFunction.zeta : AF) ^ 3 * ArithmeticFunction.log) n) = 0 := by
    have hzero := mul_zero_below_left
        (((ArithmeticFunction.moebius : AF) - muCut Z) ^ 4)
        ((ArithmeticFunction.zeta : AF) ^ 3 * ArithmeticFunction.log)
        (Z ^ 4)
        (fun m hm => muCut_tail_four_zero Z m hm) n hn
    simpa [mul_assoc] using hzero
  have h := congrArg (fun f : AF => f n) (hb4_remainder Z)
  change ArithmeticFunction.vonMangoldt n - hb4 Z n =
    (((ArithmeticFunction.moebius : AF) - muCut Z) ^ 4 *
      (ArithmeticFunction.zeta : AF) ^ 3 * ArithmeticFunction.log) n at h
  rw [htail] at h
  linarith

theorem sum_hbComponent_eq_vonMangoldt (Z n : ℕ) (hn : n ≤ Z ^ 4) :
    ∑ j : Fin 4, hbComponent Z j n = ArithmeticFunction.vonMangoldt n := by
  have h := congrArg (fun f : AF => f n) (sum_hbComponent Z)
  change (∑ j : Fin 4, hbComponent Z j n) = hb4 Z n at h
  rw [h, hb4_eq_vonMangoldt Z n hn]

end RH.Zeta85.HBDepthFour
