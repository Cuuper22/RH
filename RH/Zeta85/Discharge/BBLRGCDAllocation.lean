/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/BBLRGCDAllocation.lean

The exact gcd allocation used in the proof of Bettin--Bui--Li--Radziwill,
Proposition 3.1.  If d divides A*M, the source change of variables is

  dOuter = gcd A d,       dInner = d / dOuter,
  outer  = A / dOuter,    inner  = M / dInner.

The condition `Coprime outer dInner` is essential: it makes the allocation
unique.  Omitting it gives a non-injective raw divisor split.  This module is
finite arithmetic only.  It does not assert an analytic estimate or identify
any Heath--Brown grouping with the BBLR input sequences.
-/
import Mathlib

open scoped BigOperators
open Finset

noncomputable section

namespace RH.Zeta85.BBLRGCDAllocation

/-- An original ordered factor pair whose product is divisible by `d`. -/
@[ext] structure DivisiblePair (d : ℕ) where
  outer : ℕ
  inner : ℕ
  d_dvd_product : d ∣ outer * inner

/-- The source's canonical allocation of `d` between an outer coefficient
variable and an inner smooth variable. -/
@[ext] structure SplitPair (d : ℕ) where
  dOuter : ℕ
  dInner : ℕ
  outer : ℕ
  inner : ℕ
  split : dOuter * dInner = d
  coprime : Nat.Coprime outer dInner

/-- Merge a canonical split back to the original factor pair. -/
def merge {d : ℕ} (s : SplitPair d) : DivisiblePair d where
  outer := s.dOuter * s.outer
  inner := s.dInner * s.inner
  d_dvd_product := by
    refine ⟨s.outer * s.inner, ?_⟩
    calc
      (s.dOuter * s.outer) * (s.dInner * s.inner) =
          (s.dOuter * s.dInner) * (s.outer * s.inner) := by ac_rfl
      _ = d * (s.outer * s.inner) := by rw [s.split]

lemma quotient_gcd_dvd_inner {d : ℕ} (hd : 0 < d) (x : DivisiblePair d) :
    d / x.outer.gcd d ∣ x.inner := by
  let g := x.outer.gcd d
  have hg_dvd_outer : g ∣ x.outer := Nat.gcd_dvd_left _ _
  have hg_dvd_d : g ∣ d := Nat.gcd_dvd_right _ _
  have hg_dvd_product : g ∣ x.outer * x.inner :=
    dvd_mul_of_dvd_left hg_dvd_outer x.inner
  have hquotient : d / g ∣ (x.outer * x.inner) / g := by
    rw [Nat.dvd_div_iff_mul_dvd hg_dvd_product]
    simpa [Nat.mul_div_cancel' hg_dvd_d] using x.d_dvd_product
  have hrewrite : (x.outer * x.inner) / g = (x.outer / g) * x.inner := by
    calc
      (x.outer * x.inner) / g = (x.inner * x.outer) / g := by
        rw [Nat.mul_comm]
      _ = x.inner * (x.outer / g) := Nat.mul_div_assoc _ hg_dvd_outer
      _ = (x.outer / g) * x.inner := by rw [Nat.mul_comm]
  rw [hrewrite] at hquotient
  have hg_pos : 0 < x.outer.gcd d := Nat.gcd_pos_of_pos_right _ hd
  have hcoprime : Nat.Coprime (x.outer / g) (d / g) :=
    Nat.coprime_div_gcd_div_gcd hg_pos
  exact hcoprime.symm.dvd_of_dvd_mul_left hquotient

/-- Allocate `d` by first putting `gcd(A,d)` into the outer variable.
The remaining factor of `d` necessarily divides the inner variable. -/
def allocate {d : ℕ} (hd : 0 < d) (x : DivisiblePair d) : SplitPair d where
  dOuter := x.outer.gcd d
  dInner := d / x.outer.gcd d
  outer := x.outer / x.outer.gcd d
  inner := x.inner / (d / x.outer.gcd d)
  split := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  coprime := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hd)

@[simp]
lemma merge_allocate {d : ℕ} (hd : 0 < d) (x : DivisiblePair d) :
    merge (allocate hd x) = x := by
  apply DivisiblePair.ext
  · exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  · exact Nat.mul_div_cancel' (quotient_gcd_dvd_inner hd x)

lemma splitPair_dOuter_pos {d : ℕ} (hd : 0 < d) (s : SplitPair d) :
    0 < s.dOuter := by
  apply Nat.pos_of_mul_pos_right
  calc
    0 < s.dOuter * s.dInner := by rw [s.split]; exact hd

lemma splitPair_dInner_pos {d : ℕ} (hd : 0 < d) (s : SplitPair d) :
    0 < s.dInner := by
  apply Nat.pos_of_mul_pos_left
  calc
    0 < s.dOuter * s.dInner := by rw [s.split]; exact hd

/-- The coprimality side condition recovers the outer divisor allocation as
`gcd(originalOuter,d)`. -/
lemma gcd_merged_outer {d : ℕ} (s : SplitPair d) :
    (merge s).outer.gcd d = s.dOuter := by
  change (s.dOuter * s.outer).gcd d = s.dOuter
  calc
    (s.dOuter * s.outer).gcd d =
        (s.dOuter * s.outer).gcd (s.dOuter * s.dInner) :=
      congrArg ((s.dOuter * s.outer).gcd ·) s.split.symm
    _ = s.dOuter * s.outer.gcd s.dInner := Nat.gcd_mul_left _ _ _
    _ = s.dOuter := by rw [s.coprime.gcd_eq_one, mul_one]

@[simp]
lemma allocate_merge {d : ℕ} (hd : 0 < d) (s : SplitPair d) :
    allocate hd (merge s) = s := by
  have hdOuter : 0 < s.dOuter := splitPair_dOuter_pos hd s
  have hdInner : 0 < s.dInner := splitPair_dInner_pos hd s
  have hg : (s.dOuter * s.outer).gcd d = s.dOuter := gcd_merged_outer s
  apply SplitPair.ext
  · exact hg
  · change d / (s.dOuter * s.outer).gcd d = s.dInner
    rw [hg]
    calc
      d / s.dOuter = (s.dOuter * s.dInner) / s.dOuter :=
        congrArg (· / s.dOuter) s.split.symm
      _ = s.dInner := Nat.mul_div_right _ hdOuter
  · change (s.dOuter * s.outer) / (s.dOuter * s.outer).gcd d = s.outer
    rw [hg]
    exact Nat.mul_div_right _ hdOuter
  · change (s.dInner * s.inner) /
      (d / (s.dOuter * s.outer).gcd d) = s.inner
    rw [hg]
    have hquot : d / s.dOuter = s.dInner := by
      calc
        d / s.dOuter = (s.dOuter * s.dInner) / s.dOuter :=
          congrArg (· / s.dOuter) s.split.symm
        _ = s.dInner := Nat.mul_div_right _ hdOuter
    rw [hquot]
    exact Nat.mul_div_right _ hdInner

/-- For positive `d`, the BBLR allocation is a genuine bijection, so every
original factor pair occurs with multiplicity one. -/
def allocationEquiv (d : ℕ) (hd : 0 < d) : DivisiblePair d ≃ SplitPair d where
  toFun := allocate hd
  invFun := merge
  left_inv := merge_allocate hd
  right_inv := allocate_merge hd

/-- The merged product factors as `d` times the reduced product. -/
lemma merged_product_eq {d : ℕ} (s : SplitPair d) :
    (merge s).outer * (merge s).inner = d * (s.outer * s.inner) := by
  calc
    (merge s).outer * (merge s).inner =
        (s.dOuter * s.dInner) * (s.outer * s.inner) := by
      simp only [merge]
      ac_rfl
    _ = d * (s.outer * s.inner) := congrArg (· * (s.outer * s.inner)) s.split

/-- The reduced product in a canonical split is the original product divided
by `d`. -/
lemma reduced_product_eq_div {d : ℕ} (hd : 0 < d) (s : SplitPair d) :
    s.outer * s.inner = (merge s).outer * (merge s).inner / d := by
  rw [merged_product_eq]
  simpa [Nat.mul_comm] using (Nat.mul_div_left (s.outer * s.inner) hd).symm

lemma allocated_reduced_product_eq_div {d : ℕ} (hd : 0 < d)
    (x : DivisiblePair d) :
    (allocate hd x).outer * (allocate hd x).inner = x.outer * x.inner / d := by
  simpa using reduced_product_eq_div hd (allocate hd x)

/-- The two source-side allocations preserve the fact that, after dividing
the full gcd, the two reduced products are coprime. -/
lemma allocated_reduced_products_coprime
    (A M B N : ℕ)
    (hd : 0 < (A * M).gcd (B * N)) :
    let d := (A * M).gcd (B * N)
    let left : DivisiblePair d :=
      ⟨A, M, Nat.gcd_dvd_left _ _⟩
    let right : DivisiblePair d :=
      ⟨B, N, Nat.gcd_dvd_right _ _⟩
    Nat.Coprime
      ((allocate hd left).outer * (allocate hd left).inner)
      ((allocate hd right).outer * (allocate hd right).inner) := by
  dsimp only
  rw [allocated_reduced_product_eq_div, allocated_reduced_product_eq_div]
  exact Nat.coprime_div_gcd_div_gcd hd

/-- Conversely, equal divisor splits and coprime reduced products reconstruct
an original pair of products with gcd exactly `d`. -/
lemma gcd_merged_products {d : ℕ} (left right : SplitPair d)
    (hcoprime : Nat.Coprime (left.outer * left.inner) (right.outer * right.inner)) :
    ((merge left).outer * (merge left).inner).gcd
      ((merge right).outer * (merge right).inner) = d := by
  rw [merged_product_eq, merged_product_eq]
  rw [Nat.gcd_mul_left, hcoprime.gcd_eq_one, mul_one]

/-- The exact one-side coefficient after the source allocation and the
collapse `p = outer*inner`.  For BBLR's left side, instantiate
`alpha n = alpha_n` and `smooth n = W1(n/M1)`; the right side uses `beta`
and `W3`.  The coprimality filter is part of the source formula. -/
def collapsedCoeff (alpha smooth : ℕ → ℂ) (d p : ℕ) : ℂ :=
  ∑ dd ∈ d.divisorsAntidiagonal,
    ∑ am ∈ p.divisorsAntidiagonal,
      if Nat.Coprime am.1 dd.2 then
        alpha (dd.1 * am.1) * smooth (dd.2 * am.2)
      else 0

/-- The unfiltered nested divisor split used only to state the regression
against the earlier candidate in `HBDepthFour.splitCoeff`. -/
def rawCollapsedCoeff (alpha smooth : ℕ → ℂ) (d p : ℕ) : ℂ :=
  ∑ dd ∈ d.divisorsAntidiagonal,
    ∑ am ∈ p.divisorsAntidiagonal,
      alpha (dd.1 * am.1) * smooth (dd.2 * am.2)

def unitComplexCoeff : ℕ → ℂ := fun _ => 1

/-- The finite canonical index set behind `collapsedCoeff`. -/
def splitFiber (d p : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (d.divisorsAntidiagonal ×ˢ p.divisorsAntidiagonal).filter
    fun x => Nat.Coprime x.2.1 x.1.2

/-- Send `((dOuter,dInner),(outer,inner))` to the original pair
`(dOuter*outer,dInner*inner)`. -/
def splitMerge (x : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (x.1.1 * x.2.1, x.1.2 * x.2.2)

lemma splitMerge_mem_divisorsAntidiagonal {d p : ℕ} (hd : 0 < d) (hp : 0 < p)
    {x : (ℕ × ℕ) × (ℕ × ℕ)} (hx : x ∈ splitFiber d p) :
    splitMerge x ∈ (d * p).divisorsAntidiagonal := by
  obtain ⟨hprod, _⟩ := Finset.mem_filter.mp hx
  obtain ⟨hdd, ham⟩ := Finset.mem_product.mp hprod
  obtain ⟨hddprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hdd
  obtain ⟨hamprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp ham
  apply Nat.mem_divisorsAntidiagonal.mpr
  constructor
  · simp only [splitMerge]
    calc
      x.1.1 * x.2.1 * (x.1.2 * x.2.2) =
          (x.1.1 * x.1.2) * (x.2.1 * x.2.2) := by ac_rfl
      _ = d * p := by rw [hddprod, hamprod]
  · exact Nat.mul_ne_zero (Nat.ne_of_gt hd) (Nat.ne_of_gt hp)

/-- The canonical source allocation reindexes the fixed-product fiber with
multiplicity one. -/
lemma sum_splitFiber_eq_divisorsAntidiagonal {d p : ℕ} (hd : 0 < d) (hp : 0 < p)
    (f : ℕ × ℕ → ℂ) :
    ∑ x ∈ splitFiber d p, f (splitMerge x) =
      ∑ AM ∈ (d * p).divisorsAntidiagonal, f AM := by
  apply Finset.sum_bij (fun x _ => splitMerge x)
  · intro x hx
    exact splitMerge_mem_divisorsAntidiagonal hd hp hx
  · intro x hx y hy hxy
    obtain ⟨hxprod, hxcop⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxdd, hxam⟩ := Finset.mem_product.mp hxprod
    obtain ⟨hyprod, hycop⟩ := Finset.mem_filter.mp hy
    obtain ⟨hydd, hyam⟩ := Finset.mem_product.mp hyprod
    have hxddprod := (Nat.mem_divisorsAntidiagonal.mp hxdd).1
    have hxamprod := (Nat.mem_divisorsAntidiagonal.mp hxam).1
    have hyddprod := (Nat.mem_divisorsAntidiagonal.mp hydd).1
    have hyamprod := (Nat.mem_divisorsAntidiagonal.mp hyam).1
    let sx : SplitPair d :=
      ⟨x.1.1, x.1.2, x.2.1, x.2.2, hxddprod, hxcop⟩
    let sy : SplitPair d :=
      ⟨y.1.1, y.1.2, y.2.1, y.2.2, hyddprod, hycop⟩
    have hmerge : merge sx = merge sy := by
      apply DivisiblePair.ext
      · exact congrArg Prod.fst hxy
      · exact congrArg Prod.snd hxy
    have hs : sx = sy := by
      calc
        sx = allocate hd (merge sx) := (allocate_merge hd sx).symm
        _ = allocate hd (merge sy) := congrArg (allocate hd) hmerge
        _ = sy := allocate_merge hd sy
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg SplitPair.dOuter hs
      · exact congrArg SplitPair.dInner hs
    · apply Prod.ext
      · exact congrArg SplitPair.outer hs
      · exact congrArg SplitPair.inner hs
  · intro AM hAM
    obtain ⟨hAMprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hAM
    have hd_dvd : d ∣ AM.1 * AM.2 := by
      refine ⟨p, ?_⟩
      exact hAMprod
    let original : DivisiblePair d := ⟨AM.1, AM.2, hd_dvd⟩
    let s : SplitPair d := allocate hd original
    let x : (ℕ × ℕ) × (ℕ × ℕ) :=
      ((s.dOuter, s.dInner), (s.outer, s.inner))
    have hreduced : s.outer * s.inner = p := by
      calc
        s.outer * s.inner = AM.1 * AM.2 / d := by
          simpa [s, original] using allocated_reduced_product_eq_div hd original
        _ = (d * p) / d := congrArg (· / d) hAMprod
        _ = p := by simpa [Nat.mul_comm] using Nat.mul_div_left p hd
    refine ⟨x, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · exact Nat.mem_divisorsAntidiagonal.mpr
            ⟨s.split, Nat.ne_of_gt hd⟩
        · exact Nat.mem_divisorsAntidiagonal.mpr
            ⟨hreduced, Nat.ne_of_gt hp⟩
      · exact s.coprime
    · have hm : merge s = original := merge_allocate hd original
      apply Prod.ext
      · exact congrArg DivisiblePair.outer hm
      · exact congrArg DivisiblePair.inner hm
  · intro x hx
    rfl

/-- The exact BBLR coefficient collapse: the filtered `dOuter*dInner=d`,
`outer*inner=p` sum is exactly the original Dirichlet-convolution fiber at
`d*p`.  In particular, no artificial divisor-split multiplicity is present. -/
theorem collapsedCoeff_eq_divisorSum (alpha smooth : ℕ → ℂ)
    {d p : ℕ} (hd : 0 < d) (hp : 0 < p) :
    collapsedCoeff alpha smooth d p =
      ∑ AM ∈ (d * p).divisorsAntidiagonal, alpha AM.1 * smooth AM.2 := by
  calc
    collapsedCoeff alpha smooth d p =
        ∑ x ∈ splitFiber d p,
          alpha (splitMerge x).1 * smooth (splitMerge x).2 := by
      simp only [collapsedCoeff, splitFiber, splitMerge]
      rw [Finset.sum_filter]
      rw [Finset.sum_product]
    _ = ∑ AM ∈ (d * p).divisorsAntidiagonal,
        alpha AM.1 * smooth AM.2 :=
      sum_splitFiber_eq_divisorsAntidiagonal hd hp
        (fun AM => alpha AM.1 * smooth AM.2)

lemma divisorsAntidiagonal_two_card :
    (2 : ℕ).divisorsAntidiagonal.card = 2 := by decide

lemma divisorsAntidiagonal_four_card :
    (4 : ℕ).divisorsAntidiagonal.card = 3 := by decide

/-- At `d=p=2`, the canonical BBLR filter has exactly three terms. -/
theorem collapsedCoeff_two_two_unit :
    collapsedCoeff unitComplexCoeff unitComplexCoeff 2 2 = 3 := by
  rw [collapsedCoeff_eq_divisorSum unitComplexCoeff unitComplexCoeff
    (by norm_num) (by norm_num)]
  simp [unitComplexCoeff, divisorsAntidiagonal_four_card]

/-- Omitting `(outer,dInner)=1` duplicates `(A,M)=(2,2)` and gives four
terms at the same fiber. -/
theorem rawCollapsedCoeff_two_two_unit :
    rawCollapsedCoeff unitComplexCoeff unitComplexCoeff 2 2 = 4 := by
  simp [rawCollapsedCoeff, unitComplexCoeff, divisorsAntidiagonal_two_card]
  norm_num

lemma gcd_scaled_products_eq_iff_coprime {d p q : ℕ} (hd : 0 < d) :
    (d * p).gcd (d * q) = d ↔ Nat.Coprime p q := by
  rw [Nat.gcd_mul_left]
  constructor
  · intro h
    rw [Nat.Coprime]
    apply Nat.eq_of_mul_eq_mul_left hd
    simpa using h
  · intro h
    rw [Nat.Coprime] at h
    rw [h, mul_one]

/-- Exact two-sided finite-kernel reindexing.  The left side is the collapsed
`p,q` formula; the right side sums the original factor pairs and imposes the
literal gcd condition.  All ranges are explicit, and positivity excludes the
zero artifact of `Nat.divisorsAntidiagonal`.

For the BBLR Poisson block, after fixing `d,h,ell,x`, instantiate `kernel p q`
with

`W0(d*h/H) * e(negativeSign*ell*h*inverse(p)/q) *
 W2(q*x/M2) * W4(p*x/N2) * e(ell*x)`.

Thus this theorem covers exactly the source factors depending only on the
reduced products.  Constructing the smooth Heath--Brown grouping that supplies
`alpha`, `smoothLeft`, `beta`, and `smoothRight` is a separate step. -/
theorem collapsedKernelSum_eq_originalFibers
    (d : ℕ) (hd : 0 < d)
    (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q)
    (alpha smoothLeft beta smoothRight : ℕ → ℂ)
    (kernel : ℕ → ℕ → ℂ) :
    (∑ p ∈ P, ∑ q ∈ Q,
      if Nat.Coprime p q then
        collapsedCoeff alpha smoothLeft d p *
          collapsedCoeff beta smoothRight d q * kernel p q
      else 0) =
    ∑ p ∈ P, ∑ q ∈ Q,
      ∑ AM ∈ (d * p).divisorsAntidiagonal,
        ∑ BN ∈ (d * q).divisorsAntidiagonal,
          if (AM.1 * AM.2).gcd (BN.1 * BN.2) = d then
            alpha AM.1 * smoothLeft AM.2 *
              (beta BN.1 * smoothRight BN.2) * kernel p q
          else 0 := by
  apply Finset.sum_congr rfl
  intro p hpMem
  apply Finset.sum_congr rfl
  intro q hqMem
  have hp : 0 < p := hP p hpMem
  have hq : 0 < q := hQ q hqMem
  by_cases hcop : Nat.Coprime p q
  · rw [if_pos hcop]
    rw [collapsedCoeff_eq_divisorSum alpha smoothLeft hd hp]
    rw [collapsedCoeff_eq_divisorSum beta smoothRight hd hq]
    calc
      (∑ AM ∈ (d * p).divisorsAntidiagonal,
          alpha AM.1 * smoothLeft AM.2) *
          (∑ BN ∈ (d * q).divisorsAntidiagonal,
            beta BN.1 * smoothRight BN.2) * kernel p q =
          ∑ AM ∈ (d * p).divisorsAntidiagonal,
            ∑ BN ∈ (d * q).divisorsAntidiagonal,
              alpha AM.1 * smoothLeft AM.2 *
                (beta BN.1 * smoothRight BN.2) * kernel p q := by
        rw [Finset.sum_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro AM _
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
      _ = ∑ AM ∈ (d * p).divisorsAntidiagonal,
          ∑ BN ∈ (d * q).divisorsAntidiagonal,
            if (AM.1 * AM.2).gcd (BN.1 * BN.2) = d then
              alpha AM.1 * smoothLeft AM.2 *
                (beta BN.1 * smoothRight BN.2) * kernel p q
            else 0 := by
        apply Finset.sum_congr rfl
        intro AM hAM
        apply Finset.sum_congr rfl
        intro BN hBN
        have hAMprod := (Nat.mem_divisorsAntidiagonal.mp hAM).1
        have hBNprod := (Nat.mem_divisorsAntidiagonal.mp hBN).1
        rw [hAMprod, hBNprod]
        rw [if_pos ((gcd_scaled_products_eq_iff_coprime hd).mpr hcop)]
  · rw [if_neg hcop]
    symm
    apply Finset.sum_eq_zero
    intro AM hAM
    apply Finset.sum_eq_zero
    intro BN hBN
    have hAMprod := (Nat.mem_divisorsAntidiagonal.mp hAM).1
    have hBNprod := (Nat.mem_divisorsAntidiagonal.mp hBN).1
    rw [hAMprod, hBNprod]
    rw [if_neg (fun h => hcop ((gcd_scaled_products_eq_iff_coprime hd).mp h))]

/-- A raw divisor split, deliberately omitting the coprimality condition. -/
structure RawSplitPair (d : ℕ) where
  dOuter : ℕ
  dInner : ℕ
  outer : ℕ
  inner : ℕ
  split : dOuter * dInner = d

def rawMerge {d : ℕ} (s : RawSplitPair d) : ℕ × ℕ :=
  (s.dOuter * s.outer, s.dInner * s.inner)

/-- First raw representation of `(r,r)` at divisor `r`. -/
def rawFirst (r : ℕ) : RawSplitPair r where
  dOuter := 1
  dInner := r
  outer := r
  inner := 1
  split := one_mul r

/-- Second raw representation of `(r,r)` at divisor `r`. -/
def rawSecond (r : ℕ) : RawSplitPair r where
  dOuter := r
  dInner := 1
  outer := 1
  inner := r
  split := mul_one r

lemma raw_first_second_merge_equal (r : ℕ) :
    rawMerge (rawFirst r) = rawMerge (rawSecond r) := by
  simp [rawMerge, rawFirst, rawSecond]

lemma raw_first_second_distinct {r : ℕ} (hr : r ≠ 1) :
    rawFirst r ≠ rawSecond r := by
  intro h
  have := congrArg RawSplitPair.dOuter h
  have h1r : 1 = r := by simpa [rawFirst, rawSecond] using this
  exact hr h1r.symm

/-- The first raw representation is precisely the duplicate excluded by the
source condition when `r > 1`. -/
lemma rawFirst_not_canonical {r : ℕ} (hr : 1 < r) :
    ¬Nat.Coprime (rawFirst r).outer (rawFirst r).dInner := by
  simpa [rawFirst, Nat.coprime_self] using (Nat.ne_of_gt hr)

end RH.Zeta85.BBLRGCDAllocation
