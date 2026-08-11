/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/SQ4CRTConductor.lean

Exact CRT and conductor algebra for the generalized shifted Gauss products
in the surviving SQ4 family.  No analytic estimate is asserted.
-/
import RH.Zeta85.Discharge.SQ4GaussSquareTransform
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

noncomputable section

open scoped BigOperators

namespace RH.Zeta85.SQ4CRTConductor

open SQ4GaussSquareTransform

variable {R S : Type*} [CommRing R] [CommRing S] [Fintype Rˣ] [Fintype Sˣ]

local instance : Fintype (R × S)ˣ :=
  Fintype.ofEquiv (Rˣ × Sˣ) MulEquiv.prodUnits.symm.toEquiv

/-! ## Exact product-ring factorization -/

/-- Product of two additive characters, written multiplicatively in the
target. -/
def prodAddChar (psiR : AddChar R ℂ) (psiS : AddChar S ℂ) :
    AddChar (R × S) ℂ :=
  (psiR.compAddMonoidHom (AddMonoidHom.fst R S)) *
    (psiS.compAddMonoidHom (AddMonoidHom.snd R S))

/-- Product of two unit-group characters. -/
def prodUnitCharacter (chiR : UnitCharacter R) (chiS : UnitCharacter S) :
    UnitCharacter (R × S) :=
  (((chiR.comp (MonoidHom.fst Rˣ Sˣ)) *
      (chiS.comp (MonoidHom.snd Rˣ Sˣ))).comp
    MulEquiv.prodUnits.toMonoidHom)

/-- A generalized shifted Gauss sum factors exactly over a product ring.
No unit condition on either shift is used. -/
theorem unitGaussSum_prod
    (chiR : UnitCharacter R) (chiS : UnitCharacter S)
    (psiR : AddChar R ℂ) (psiS : AddChar S ℂ) (a : R) (b : S) :
    unitGaussSum (prodUnitCharacter chiR chiS) (prodAddChar psiR psiS) (a, b) =
      unitGaussSum chiR psiR a * unitGaussSum chiS psiS b := by
  rw [unitGaussSum, unitGaussSum, unitGaussSum, Fintype.sum_mul_sum,
    ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv MulEquiv.prodUnits.toEquiv _ _ fun z ↦ by
    simp [prodUnitCharacter, prodAddChar, MulEquiv.prodUnits]
    ring

/-! ## CRT transport for arbitrary global characters -/

/-- CRT on unit groups, including the canonical units-of-a-product
equivalence. -/
def crtUnits {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits

/-- Left local restriction of a global unit character under CRT. -/
def crtUnitCharacterLeft {m n : ℕ} (h : m.Coprime n)
    (chi : UnitCharacter (ZMod (m * n))) : UnitCharacter (ZMod m) :=
  chi.comp <| (crtUnits h).symm.toMonoidHom.comp
    (MonoidHom.inl (ZMod m)ˣ (ZMod n)ˣ)

/-- Right local restriction of a global unit character under CRT. -/
def crtUnitCharacterRight {m n : ℕ} (h : m.Coprime n)
    (chi : UnitCharacter (ZMod (m * n))) : UnitCharacter (ZMod n) :=
  chi.comp <| (crtUnits h).symm.toMonoidHom.comp
    (MonoidHom.inr (ZMod m)ˣ (ZMod n)ˣ)

/-- Left local restriction of a global additive character under CRT. -/
def crtAddCharLeft {m n : ℕ} (h : m.Coprime n)
    (psi : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod m) ℂ :=
  psi.compAddMonoidHom <| (ZMod.chineseRemainder h).symm.toAddMonoidHom.comp
    (AddMonoidHom.inl (ZMod m) (ZMod n))

/-- Right local restriction of a global additive character under CRT. -/
def crtAddCharRight {m n : ℕ} (h : m.Coprime n)
    (psi : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod n) ℂ :=
  psi.compAddMonoidHom <| (ZMod.chineseRemainder h).symm.toAddMonoidHom.comp
    (AddMonoidHom.inr (ZMod m) (ZMod n))

/-- Every global unit character is the product of its two CRT restrictions. -/
theorem crt_unitCharacter_factor {m n : ℕ} (h : m.Coprime n)
    (chi : UnitCharacter (ZMod (m * n))) (z : (ZMod (m * n))ˣ) :
    (chi z : ℂ) =
      (crtUnitCharacterLeft h chi ((crtUnits h z).1) : ℂ) *
        (crtUnitCharacterRight h chi ((crtUnits h z).2) : ℂ) := by
  change (chi z : ℂ) =
    (chi ((crtUnits h).symm ((crtUnits h z).1, 1)) : ℂ) *
      (chi ((crtUnits h).symm (1, (crtUnits h z).2)) : ℂ)
  change (chi z).val =
    (chi ((crtUnits h).symm ((crtUnits h z).1, 1)) *
      chi ((crtUnits h).symm (1, (crtUnits h z).2))).val
  congr 1
  rw [← map_mul]
  congr 1
  apply (crtUnits h).injective
  simp

/-- Every global additive character is the product of its two CRT
restrictions. -/
theorem crt_addChar_factor {m n : ℕ} (h : m.Coprime n)
    (psi : AddChar (ZMod (m * n)) ℂ) (z : ZMod (m * n)) :
    psi z =
      crtAddCharLeft h psi (ZMod.chineseRemainder h z).1 *
        crtAddCharRight h psi (ZMod.chineseRemainder h z).2 := by
  change psi z =
    psi ((ZMod.chineseRemainder h).symm ((ZMod.chineseRemainder h z).1, 0)) *
      psi ((ZMod.chineseRemainder h).symm (0, (ZMod.chineseRemainder h z).2))
  rw [← psi.map_add_eq_mul]
  congr 1
  apply (ZMod.chineseRemainder h).injective
  simp

/-- Source-faithful CRT factorization of a generalized shifted Gauss sum.
The local additive characters retain the complementary-modulus twists. -/
theorem unitGaussSum_crt {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (chi : UnitCharacter (ZMod (m * n)))
    (psi : AddChar (ZMod (m * n)) ℂ) (a : ZMod (m * n)) :
    unitGaussSum chi psi a =
      unitGaussSum (crtUnitCharacterLeft h chi) (crtAddCharLeft h psi)
          (ZMod.chineseRemainder h a).1 *
        unitGaussSum (crtUnitCharacterRight h chi) (crtAddCharRight h psi)
          (ZMod.chineseRemainder h a).2 := by
  rw [unitGaussSum, unitGaussSum, unitGaussSum, Fintype.sum_mul_sum,
    ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (crtUnits h).toEquiv _ _ fun z ↦ by
    rw [crt_unitCharacter_factor h chi z, crt_addChar_factor h psi (a * (z : ZMod (m * n)))]
    simp only [map_mul]
    change
      ((crtUnitCharacterLeft h chi ((crtUnits h z).1) : ℂ) *
          (crtUnitCharacterRight h chi ((crtUnits h z).2) : ℂ)) *
        (crtAddCharLeft h psi
            ((ZMod.chineseRemainder h a).1 * ((crtUnits h z).1 : ZMod m)) *
          crtAddCharRight h psi
            ((ZMod.chineseRemainder h a).2 * ((crtUnits h z).2 : ZMod n))) = _
    change _ =
      ((crtUnitCharacterLeft h chi ((crtUnits h z).1) : ℂ) *
          crtAddCharLeft h psi
            ((ZMod.chineseRemainder h a).1 * ((crtUnits h z).1 : ZMod m))) *
        ((crtUnitCharacterRight h chi ((crtUnits h z).2) : ℂ) *
          crtAddCharRight h psi
            ((ZMod.chineseRemainder h a).2 * ((crtUnits h z).2 : ZMod n)))
    ring

/-- The two-shift generalized Gauss product therefore becomes four local
shifted sums.  This is valid on nonunit strata as stated; no local sum is
replaced by a Gauss square. -/
theorem gauss_product_crt {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (chi : UnitCharacter (ZMod (m * n)))
    (psi : AddChar (ZMod (m * n)) ℂ) (k r : ZMod (m * n)) :
    unitGaussSum chi psi k * unitGaussSum chi psi r =
      (unitGaussSum (crtUnitCharacterLeft h chi) (crtAddCharLeft h psi)
          (ZMod.chineseRemainder h k).1 *
        unitGaussSum (crtUnitCharacterLeft h chi) (crtAddCharLeft h psi)
          (ZMod.chineseRemainder h r).1) *
      (unitGaussSum (crtUnitCharacterRight h chi) (crtAddCharRight h psi)
          (ZMod.chineseRemainder h k).2 *
        unitGaussSum (crtUnitCharacterRight h chi) (crtAddCharRight h psi)
          (ZMod.chineseRemainder h r).2) := by
  rw [unitGaussSum_crt h chi psi k, unitGaussSum_crt h chi psi r]
  ring

/-! ## Exact conductor support of nonunit shifts -/

/-- Units are equivalent to elements equipped with a proof of being a unit.
This is used only to compare the unit-supported sum with Mathlib's
zero-extended multiplicative character convention. -/
def isUnitEquivUnits {A : Type*} [Monoid A] : {x : A // IsUnit x} ≃ Aˣ where
  toFun x := x.prop.unit
  invFun u := ⟨(u : A), u.isUnit⟩
  left_inv x := by
    apply Subtype.ext
    exact x.prop.unit_spec
  right_inv u := by
    apply Units.ext
    exact u.isUnit.unit_spec

/-- The unit-supported shifted sum is exactly Mathlib's Gauss sum with the
multiplicative character extended by zero to nonunits. -/
theorem unitGaussSum_eq_gaussSum {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (psi : AddChar (ZMod N) ℂ) (a : ZMod N) :
    unitGaussSum chi.toUnitHom psi a = gaussSum chi (psi.mulShift a) := by
  rw [unitGaussSum, gaussSum]
  calc
    (∑ z : (ZMod N)ˣ, (chi.toUnitHom z : ℂ) * psi (a * (z : ZMod N))) =
        ∑ z : {x : ZMod N // IsUnit x}, chi z.1 * psi (a * z.1) := by
      exact Fintype.sum_equiv isUnitEquivUnits.symm _ _ fun z ↦ by
        simp [isUnitEquivUnits]
    _ = (∑ z : {x : ZMod N // IsUnit x},
          chi z.1 * (psi.mulShift a) z.1) +
        ∑ z : {x : ZMod N // ¬ IsUnit x},
          chi z.1 * (psi.mulShift a) z.1 := by
      simp only [AddChar.mulShift_apply]
      have hzero : (∑ z : {x : ZMod N // ¬ IsUnit x},
          chi z.1 * psi (a * z.1)) = 0 := by
        apply Finset.sum_eq_zero
        intro z _
        rw [MulChar.map_nonunit chi z.prop, zero_mul]
      rw [hzero, add_zero]
    _ = ∑ z : ZMod N, chi z * (psi.mulShift a) z :=
      Fintype.sum_subtype_add_sum_subtype
        (p := fun z : ZMod N ↦ IsUnit z)
        (fun z ↦ chi z * (psi.mulShift a) z)

/-- If a generalized shifted Gauss sum is nonzero and an additional shift
by `d | N` kills its additive character, then the multiplicative character
must factor through `d`. -/
theorem factorsThrough_of_unitGaussSum_ne_zero {N d : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (psi : AddChar (ZMod N) ℂ) (a : ZMod N)
    (hd : d ∣ N) (htriv : psi.mulShift (a * (d : ZMod N)) = 1)
    (hne : unitGaussSum chi.toUnitHom psi a ≠ 0) :
    chi.FactorsThrough d := by
  apply factorsThrough_of_gaussSum_ne_zero (e := psi.mulShift a) hd
  · simpa only [AddChar.mulShift_mulShift] using htriv
  · rwa [← unitGaussSum_eq_gaussSum]

/-- Conductor divisibility form of
`factorsThrough_of_unitGaussSum_ne_zero`. -/
theorem conductor_dvd_of_unitGaussSum_ne_zero {N d : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (psi : AddChar (ZMod N) ℂ) (a : ZMod N)
    (hd : d ∣ N) (htriv : psi.mulShift (a * (d : ZMod N)) = 1)
    (hne : unitGaussSum chi.toUnitHom psi a ≠ 0) :
    chi.conductor ∣ d := by
  apply (DirichletCharacter.mem_conductorSet_iff_conductor_dvd chi hd).mp
  exact factorsThrough_of_unitGaussSum_ne_zero chi psi a hd htriv hne

/-- For the standard character, a natural shift followed by `d` is trivial
whenever `N | t*d`. -/
theorem standard_shift_killed {N t d : ℕ} [NeZero N] (hkill : N ∣ t * d) :
    (ZMod.stdAddChar (N := N)).mulShift ((t : ZMod N) * (d : ZMod N)) = 1 := by
  have hz : (t : ZMod N) * (d : ZMod N) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact hkill
  rw [hz, AddChar.mulShift_zero]

/-- Exact gcd/conductor support for an arbitrary (possibly imprimitive)
Dirichlet character: nonvanishing at shift `t` forces its conductor to
divide `N / gcd(t,N)`. -/
theorem conductor_dvd_quotient_gcd_of_unitGaussSum_ne_zero {N t : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N)
    (hne : unitGaussSum chi.toUnitHom (ZMod.stdAddChar (N := N)) (t : ZMod N) ≠ 0) :
    chi.conductor ∣ N / t.gcd N := by
  let g := t.gcd N
  have hgdvdN : g ∣ N := Nat.gcd_dvd_right t N
  have hd : N / g ∣ N := Nat.div_dvd_of_dvd hgdvdN
  have hkill : N ∣ t * (N / g) := by
    refine ⟨t / g, ?_⟩
    calc
      t * (N / g) = (t / g * g) * (N / g) := by
        rw [Nat.div_mul_cancel (Nat.gcd_dvd_left t N)]
      _ = (N / g * g) * (t / g) := by ring
      _ = N * (t / g) := by rw [Nat.div_mul_cancel hgdvdN]
  apply conductor_dvd_of_unitGaussSum_ne_zero chi (ZMod.stdAddChar (N := N))
    (t : ZMod N) hd
  · exact standard_shift_killed hkill
  · exact hne

/-- For the generalized product at shifts `k,r`, simultaneous nonvanishing
forces the conductor into the intersection of the two gcd strata. -/
theorem conductor_dvd_gcd_of_gauss_product_ne_zero {N k r : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N)
    (hne : unitGaussSum chi.toUnitHom (ZMod.stdAddChar (N := N)) (k : ZMod N) *
      unitGaussSum chi.toUnitHom (ZMod.stdAddChar (N := N)) (r : ZMod N) ≠ 0) :
    chi.conductor ∣ (N / k.gcd N).gcd (N / r.gcd N) := by
  rw [mul_ne_zero_iff] at hne
  exact Nat.dvd_gcd
    (conductor_dvd_quotient_gcd_of_unitGaussSum_ne_zero chi hne.1)
    (conductor_dvd_quotient_gcd_of_unitGaussSum_ne_zero chi hne.2)

/-- Residue-class form of the one-shift conductor support statement. -/
theorem conductor_dvd_quotient_gcd_of_residue_gauss_ne_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (a : ZMod N)
    (hne : unitGaussSum chi.toUnitHom (ZMod.stdAddChar (N := N)) a ≠ 0) :
    chi.conductor ∣ N / a.val.gcd N := by
  apply conductor_dvd_quotient_gcd_of_unitGaussSum_ne_zero chi
  simpa only [ZMod.natCast_zmod_val] using hne

/-- Residue-class form of the exact two-shift conductor support statement,
covering signed source frequencies after reduction modulo `N`. -/
theorem conductor_dvd_gcd_of_residue_gauss_product_ne_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (a b : ZMod N)
    (hne : unitGaussSum chi.toUnitHom (ZMod.stdAddChar (N := N)) a *
      unitGaussSum chi.toUnitHom (ZMod.stdAddChar (N := N)) b ≠ 0) :
    chi.conductor ∣ (N / a.val.gcd N).gcd (N / b.val.gcd N) := by
  apply conductor_dvd_gcd_of_gauss_product_ne_zero chi
  simpa only [ZMod.natCast_zmod_val] using hne

/-- Primitive characters kill every nonunit shifted Gauss sum.  Imprimitive
characters require the conductor divisibility statements above instead. -/
theorem primitive_nonunit_shift_vanishes {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi.IsPrimitive)
    (psi : AddChar (ZMod N) ℂ) (a : ZMod N) (ha : ¬ IsUnit a) :
    unitGaussSum chi.toUnitHom psi a = 0 := by
  rw [unitGaussSum_eq_gaussSum, gaussSum_mulShift_of_isPrimitive psi hchi a,
    MulChar.map_nonunit _ ha, zero_mul]

/-! ## Exact formula for an explicitly induced primitive character -/

/-- Cancelling a right-hand modulus factor in the standard additive
character. -/
lemma stdAddChar_cancel_right {f s t a : ℕ} [NeZero f] [NeZero s] :
    ZMod.stdAddChar (N := f * s) ((s * t * a : ℕ) : ZMod (f * s)) =
      ZMod.stdAddChar (N := f) ((t * a : ℕ) : ZMod f) := by
  rw [show ((s * t * a : ℕ) : ZMod (f * s)) =
      ((s * t * a : ℤ) : ZMod (f * s)) by norm_num,
    show ((t * a : ℕ) : ZMod f) = ((t * a : ℤ) : ZMod f) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hf : (f : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne f
  have hs : (s : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne s
  field_simp

/-- Cancelling a left-hand modulus factor in the standard additive
character. -/
lemma stdAddChar_cancel_left {f s t a : ℕ} [NeZero f] [NeZero s] :
    ZMod.stdAddChar (N := f * s) ((f * t * a : ℕ) : ZMod (f * s)) =
      ZMod.stdAddChar (N := s) ((t * a : ℕ) : ZMod s) := by
  rw [show ((f * t * a : ℕ) : ZMod (f * s)) =
      ((f * t * a : ℤ) : ZMod (f * s)) by norm_num,
    show ((t * a : ℕ) : ZMod s) = ((t * a : ℤ) : ZMod s) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hf : (f : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne f
  have hs : (s : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne s
  field_simp

/-- Exact orthogonality for a shifted standard additive character. -/
lemma sum_stdAddChar_shift {s t : ℕ} [NeZero s] :
    (∑ x : ZMod s, ZMod.stdAddChar ((t : ZMod s) * x)) =
      if s ∣ t then (s : ℂ) else 0 := by
  by_cases h : s ∣ t
  · rw [if_pos h]
    have ht : (t : ZMod s) = 0 := (ZMod.natCast_eq_zero_iff t s).mpr h
    simp [ht]
  · rw [if_neg h]
    change (∑ x : ZMod s,
      ((ZMod.stdAddChar (N := s)).mulShift (t : ZMod s)) x) = 0
    apply AddChar.sum_eq_zero_of_ne_one
    intro heq
    have hone := DFunLike.congr_fun heq (1 : ZMod s)
    simp only [AddChar.mulShift_apply, mul_one] at hone
    have ht : (t : ZMod s) = 0 :=
      ZMod.injective_stdAddChar (by simpa using hone)
    exact h ((ZMod.natCast_eq_zero_iff t s).mp ht)

/-- Mixed-radix enumeration of the interval of length `f * s`. -/
def digitsEquiv (f s : ℕ) : Fin s × Fin f ≃ Fin (f * s) :=
  (finProdFinEquiv (m := s) (n := f)).trans (finCongr (Nat.mul_comm s f))

@[simp] lemma digitsEquiv_val (f s : ℕ) (x : Fin s × Fin f) :
    (digitsEquiv f s x).val = x.2.val + f * x.1.val := by
  rfl

/-- The standard enumeration of `ZMod n` agrees with the natural-number
representatives in `Fin n`. -/
lemma sum_fin_eq_zmod {n : ℕ} [NeZero n] (F : ZMod n → ℂ) :
    (∑ i : Fin n, F (i.val : ZMod n)) = ∑ x : ZMod n, F x := by
  apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
  intro i
  congr 1
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact ZMod.natCast_zmod_val ((ZMod.finEquiv (n + 1)) i)

/-- `gaussSum` enumerated over canonical natural representatives. -/
lemma gaussSum_eq_fin {n : ℕ} [NeZero n] (chi : DirichletCharacter ℂ n)
    (psi : AddChar (ZMod n) ℂ) :
    gaussSum chi psi =
      ∑ i : Fin n, chi (i.val : ZMod n) * psi (i.val : ZMod n) := by
  rw [gaussSum]
  exact (sum_fin_eq_zmod (fun x ↦ chi x * psi x)).symm

/-- A length-`f*s` sum in which the multiplicative character has period
`f`. -/
def periodicSum {f : ℕ} [NeZero f] (chi : DirichletCharacter ℂ f)
    (s t : ℕ) [NeZero s] : ℂ :=
  ∑ y : Fin (f * s), chi (y.val : ZMod f) *
    ZMod.stdAddChar (N := f * s) ((t * y.val : ℕ) : ZMod (f * s))

lemma chi_add_mul_modulus {f : ℕ} (chi : DirichletCharacter ℂ f)
    (a j : ℕ) :
    chi ((a + f * j : ℕ) : ZMod f) = chi (a : ZMod f) := by
  congr 1
  simp

lemma stdAddChar_split_digits {f s t : ℕ} [NeZero f] [NeZero s]
    (a j : ℕ) :
    ZMod.stdAddChar (N := f * s) ((t * (a + f * j) : ℕ) : ZMod (f * s)) =
      ZMod.stdAddChar (N := f * s) ((t * a : ℕ) : ZMod (f * s)) *
        ZMod.stdAddChar (N := s) ((t * j : ℕ) : ZMod s) := by
  rw [show t * (a + f * j) = t * a + f * (t * j) by ring]
  rw [Nat.cast_add, AddChar.map_add_eq_mul]
  congr 1
  simpa only [mul_assoc] using
    (stdAddChar_cancel_left (f := f) (s := s) (t := t) (a := j))

/-- Exact rectangular evaluation of `periodicSum`.  The outer residue
class sum vanishes unless `s ∣ t`; in the surviving case the remaining
sum is the shifted Gauss sum at modulus `f`. -/
lemma periodicSum_eq {f s t : ℕ} [NeZero f] [NeZero s]
    (chi : DirichletCharacter ℂ f) :
    periodicSum chi s t =
      if s ∣ t then (s : ℂ) *
        gaussSum chi
          ((ZMod.stdAddChar (N := f)).mulShift ((t / s : ℕ) : ZMod f))
      else 0 := by
  rw [periodicSum]
  conv_lhs => rw [← (digitsEquiv f s).sum_comp]
  simp only [digitsEquiv_val, chi_add_mul_modulus,
    stdAddChar_split_digits]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.mul_sum]
  have hinner : (∑ j : Fin s,
      ZMod.stdAddChar (N := s) ((t * j.val : ℕ) : ZMod s)) =
      if s ∣ t then (s : ℂ) else 0 := by
    calc
      _ = ∑ x : ZMod s, ZMod.stdAddChar ((t : ZMod s) * x) := by
        simpa only [Nat.cast_mul] using
          (sum_fin_eq_zmod
            (fun x : ZMod s ↦ ZMod.stdAddChar ((t : ZMod s) * x)))
      _ = _ := sum_stdAddChar_shift
  rw [hinner]
  by_cases hs : s ∣ t
  · rw [if_pos hs, if_pos hs]
    rw [gaussSum_eq_fin, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [AddChar.mulShift_apply]
    obtain ⟨u, rfl⟩ := hs
    rw [Nat.mul_div_cancel_left u (NeZero.pos s)]
    rw [show (u : ZMod f) * (a.val : ZMod f) =
      ((u * a.val : ℕ) : ZMod f) by norm_num]
    rw [stdAddChar_cancel_right (f := f) (s := s) (t := u) (a := a.val)]
    ring
  · rw [if_neg hs, if_neg hs]
    simp

/-- Evaluation of an explicitly changed-level character on a canonical
natural representative.  This makes the induction data and its additional
coprimality condition literal. -/
lemma induced_apply_eq_coprime_indicator {f l z : ℕ} [NeZero f] [NeZero l]
    (chi : DirichletCharacter ℂ f) :
    DirichletCharacter.changeLevel (f.dvd_mul_right l) chi
        ((z : ℕ) : ZMod (f * l)) =
      if z.Coprime l then chi ((z : ℕ) : ZMod f) else 0 := by
  by_cases hzl : z.Coprime l
  · rw [if_pos hzl]
    by_cases hzf : z.Coprime f
    · have hzq : z.Coprime (f * l) := hzf.mul_right hzl
      have hzq' : IsCoprime (z : ℤ) (f * l : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr hzq
      convert (DirichletCharacter.changeLevel_eq_cast_of_dvd' chi
        (f.dvd_mul_right l) hzq') using 1 <;> norm_num
    · have hnu_f : ¬ IsUnit ((z : ℕ) : ZMod f) := by
        simpa only [ZMod.isUnit_iff_coprime] using hzf
      have hnu_q : ¬ IsUnit ((z : ℕ) : ZMod (f * l)) := by
        rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
        exact fun h ↦ hzf h.1
      rw [MulChar.map_nonunit _ hnu_q, MulChar.map_nonunit _ hnu_f]
  · rw [if_neg hzl]
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
    exact fun h ↦ hzl h.2

/-- Möbius inversion of the coprimality indicator, cast into `ℂ`. -/
lemma coprime_indicator_eq_moebius_sum {z l : ℕ} [NeZero l] :
    (if z.Coprime l then (1 : ℂ) else 0) =
      ∑ d ∈ (z.gcd l).divisors,
        (ArithmeticFunction.moebius d : ℂ) := by
  have hg : z.gcd l ≠ 0 := Nat.gcd_ne_zero_right (NeZero.ne l)
  have hm := congrArg (fun F : ArithmeticFunction ℤ ↦ F (z.gcd l))
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.one_apply] at hm
  have hmC : (∑ d ∈ (z.gcd l).divisors,
      (ArithmeticFunction.moebius d : ℂ)) =
      if z.gcd l = 1 then 1 else 0 := by
    exact_mod_cast hm
  rw [hmC]

/-- Reindex a sum supported on the multiples of a divisor. -/
lemma sum_range_filter_dvd {Q d : ℕ} (hd0 : d ≠ 0) (hdQ : d ∣ Q)
    (F : ℕ → ℂ) :
    ∑ z ∈ (Finset.range Q).filter (d ∣ ·), F z =
      ∑ y ∈ Finset.range (Q / d), F (d * y) := by
  symm
  refine Finset.sum_bij (fun y _ ↦ d * y) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_filter]
    refine ⟨?_, dvd_mul_right d y⟩
    rw [Finset.mem_range] at hy ⊢
    have hQeq : d * (Q / d) = Q := Nat.mul_div_cancel' hdQ
    rw [← hQeq]
    exact (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hd0)).2 hy
  · intro y₁ hy₁ y₂ hy₂ heq
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) heq
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨z / d, ?_, ?_⟩
    · rw [Finset.mem_range]
      exact (Nat.div_lt_div_right hd0 hz.2 hdQ).2
        (Finset.mem_range.mp hz.1)
    · exact Nat.mul_div_cancel' hz.2
  · intro y hy
    rfl

/-- Möbius inversion moves a coprimality condition into exact divisor
sums.  No absolute value or analytic estimate enters. -/
lemma mobius_coprime_weighted_sum {Q l : ℕ} [NeZero l] (hlQ : l ∣ Q)
    (F : ℕ → ℂ) :
    (∑ z : Fin Q, if z.val.Coprime l then F z.val else 0) =
      ∑ d ∈ l.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ y : Fin (Q / d), F (d * y.val) := by
  calc
    (∑ z : Fin Q, if z.val.Coprime l then F z.val else 0) =
        ∑ z ∈ Finset.range Q, if z.Coprime l then F z else 0 :=
      Fin.sum_univ_eq_sum_range
        (fun z ↦ if z.Coprime l then F z else 0) Q
    _ = ∑ z ∈ Finset.range Q,
          (∑ d ∈ (z.gcd l).divisors,
            (ArithmeticFunction.moebius d : ℂ)) * F z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [← coprime_indicator_eq_moebius_sum]
      split <;> simp_all
    _ = ∑ z ∈ Finset.range Q,
        ∑ d ∈ l.divisors,
          if d ∣ z then (ArithmeticFunction.moebius d : ℂ) * F z else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_mul]
      have hg : z.gcd l ≠ 0 := Nat.gcd_ne_zero_right (NeZero.ne l)
      have hdiv : (z.gcd l).divisors =
          l.divisors.filter (fun d ↦ d ∣ z) := by
        ext d
        simp only [Nat.mem_divisors, Finset.mem_filter]
        rw [Nat.dvd_gcd_iff]
        constructor
        · rintro ⟨⟨hdz, hdl⟩, _⟩
          exact ⟨⟨hdl, NeZero.ne l⟩, hdz⟩
        · rintro ⟨⟨hdl, _⟩, hdz⟩
          exact ⟨⟨hdz, hdl⟩, hg⟩
      rw [hdiv, Finset.sum_filter]
    _ = ∑ d ∈ l.divisors,
        ∑ z ∈ Finset.range Q,
          if d ∣ z then (ArithmeticFunction.moebius d : ℂ) * F z else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ l.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ z ∈ (Finset.range Q).filter (d ∣ ·), F z := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum, Finset.sum_filter]
    _ = ∑ d ∈ l.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ y ∈ Finset.range (Q / d), F (d * y) := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      apply sum_range_filter_dvd
      · exact (Nat.pos_of_mem_divisors hd).ne'
      · exact (Nat.dvd_of_mem_divisors hd).trans hlQ
    _ = ∑ d ∈ l.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ y : Fin (Q / d), F (d * y.val) := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      exact (Fin.sum_univ_eq_sum_range
        (fun y ↦ F (d * y)) (Q / d)).symm

/-- Cancelling an arbitrary divisor of the standard additive character's
modulus. -/
lemma stdAddChar_cancel_divisor {Q d t a : ℕ} [NeZero Q] [NeZero (Q / d)]
    (hd0 : d ≠ 0) (hdQ : d ∣ Q) :
    ZMod.stdAddChar (N := Q) ((d * t * a : ℕ) : ZMod Q) =
      ZMod.stdAddChar (N := Q / d)
        ((t * a : ℕ) : ZMod (Q / d)) := by
  rw [show ((d * t * a : ℕ) : ZMod Q) =
      ((d * t * a : ℤ) : ZMod Q) by norm_num,
    show ((t * a : ℕ) : ZMod (Q / d)) =
      ((t * a : ℤ) : ZMod (Q / d)) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hQdC : ((Q / d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne (Q / d))
  have hQeq : d * (Q / d) = Q := Nat.mul_div_cancel' hdQ
  have hQeqC : (Q : ℂ) = (d : ℂ) * ((Q / d : ℕ) : ℂ) := by
    exact_mod_cast hQeq.symm
  rw [hQeqC]
  field_simp

/-- Divisor cancellation with the target modulus written as
`f * (l / d)`.  This spelling avoids any hidden coprimality assumption
between `f` and `l / d`. -/
lemma stdAddChar_cancel_divisor_of_dvd {f l d t a : ℕ}
    [NeZero f] [NeZero l] [NeZero (l / d)]
    (hd0 : d ≠ 0) (hd : d ∣ l) :
    ZMod.stdAddChar (N := f * l)
        ((d * t * a : ℕ) : ZMod (f * l)) =
      ZMod.stdAddChar (N := f * (l / d))
        ((t * a : ℕ) : ZMod (f * (l / d))) := by
  rw [show ((d * t * a : ℕ) : ZMod (f * l)) =
      ((d * t * a : ℤ) : ZMod (f * l)) by norm_num,
    show ((t * a : ℕ) : ZMod (f * (l / d))) =
      ((t * a : ℤ) : ZMod (f * (l / d))) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hfC : (f : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne f
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hcC : ((l / d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne (l / d)
  have hlC : (l : ℂ) = (d : ℂ) * ((l / d : ℕ) : ℂ) := by
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  rw [hlC]
  field_simp

/-- Complementary divisors give an exact involutive reindexing of a
divisor sum. -/
lemma sum_divisors_complement {M : Type*} [AddCommMonoid M]
    {l : ℕ} (hl : l ≠ 0) (F : ℕ → ℕ → M) :
    ∑ d ∈ l.divisors, F d (l / d) =
      ∑ s ∈ l.divisors, F (l / s) s := by
  refine Finset.sum_bij (fun d _ ↦ l / d) ?_ ?_ ?_ ?_
  · intro d hd
    exact Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hl⟩
  · intro d₁ hd₁ d₂ hd₂ heq
    have hinv : ∀ d, d ∈ l.divisors → l / (l / d) = d := by
      intro d hd
      have hddiv : d ∣ l := Nat.dvd_of_mem_divisors hd
      have hqpos : 0 < l / d := Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hl) hddiv)
        (Nat.pos_of_mem_divisors hd)
      apply (Nat.div_eq_iff_eq_mul_left hqpos
        (Nat.div_dvd_of_dvd hddiv)).2
      exact (Nat.mul_div_cancel' hddiv).symm
    calc
      d₁ = l / (l / d₁) := (hinv d₁ hd₁).symm
      _ = l / (l / d₂) := by rw [heq]
      _ = d₂ := hinv d₂ hd₂
  · intro s hs
    have hsdiv : s ∣ l := Nat.dvd_of_mem_divisors hs
    have hqmem : l / s ∈ l.divisors := Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd hsdiv, hl⟩
    refine ⟨l / s, hqmem, ?_⟩
    have hqpos : 0 < l / s := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hl) hsdiv)
      (Nat.pos_of_mem_divisors hs)
    apply (Nat.div_eq_iff_eq_mul_left hqpos
      (Nat.div_dvd_of_dvd hsdiv)).2
    exact (Nat.mul_div_cancel' hsdiv).symm
  · intro d hd
    congr 1
    have hddiv : d ∣ l := Nat.dvd_of_mem_divisors hd
    have hqpos : 0 < l / d := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hl) hddiv)
      (Nat.pos_of_mem_divisors hd)
    symm
    apply (Nat.div_eq_iff_eq_mul_left hqpos
      (Nat.div_dvd_of_dvd hddiv)).2
    exact (Nat.mul_div_cancel' hddiv).symm

/-- Exact imprimitive conductor formula in divisor-`d` coordinates.

The character at level `f * l` is explicitly `changeLevel` of the primitive
character `chi` at level `f`.  The formula is valid for arbitrary positive
`f,l`, including shared prime factors, arbitrary shift `t`, and arbitrary
complex-valued primitive Dirichlet characters.  No unit condition on `t`
is imposed. -/
theorem gaussSum_changeLevel_eq_conductor_formula
    {f l t : ℕ} [NeZero f] [NeZero l]
    (chi : DirichletCharacter ℂ f) (hchi : chi.IsPrimitive) :
    gaussSum (DirichletCharacter.changeLevel (f.dvd_mul_right l) chi)
        ((ZMod.stdAddChar (N := f * l)).mulShift (t : ZMod (f * l))) =
      gaussSum chi (ZMod.stdAddChar (N := f)) *
        ∑ d ∈ l.divisors,
          if (l / d) ∣ t then
            (ArithmeticFunction.moebius d : ℂ) *
              chi ((d : ℕ) : ZMod f) * ((l / d : ℕ) : ℂ) *
                chi⁻¹ ((t / (l / d) : ℕ) : ZMod f)
          else 0 := by
  rw [gaussSum_eq_fin]
  simp only [AddChar.mulShift_apply]
  simp_rw [induced_apply_eq_coprime_indicator]
  simp_rw [ite_mul, zero_mul]
  simp_rw [← Nat.cast_mul]
  change (∑ z : Fin (f * l), if z.val.Coprime l then
      chi ((z.val : ℕ) : ZMod f) *
        ZMod.stdAddChar (N := f * l)
          ((t * z.val : ℕ) : ZMod (f * l)) else 0) = _
  rw [mobius_coprime_weighted_sum (Q := f * l) (l := l)
    (l.dvd_mul_left f)
    (F := fun z ↦ chi ((z : ℕ) : ZMod f) *
      ZMod.stdAddChar (N := f * l) ((t * z : ℕ) : ZMod (f * l)))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hddiv : d ∣ l := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hspos : 0 < l / d :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos l) hddiv) hdpos
  let _ : NeZero (l / d) := NeZero.of_pos hspos
  let _ : NeZero ((f * l) / d) := by
    rw [Nat.mul_div_assoc f hddiv]
    exact NeZero.of_pos (Nat.mul_pos (NeZero.pos f) hspos)
  have hinner :
      (∑ y : Fin ((f * l) / d),
        chi (((d * y.val : ℕ) : ZMod f)) *
          ZMod.stdAddChar (N := f * l)
            ((t * (d * y.val) : ℕ) : ZMod (f * l))) =
        chi ((d : ℕ) : ZMod f) * periodicSum chi (l / d) t := by
    rw [Nat.mul_div_assoc f hddiv]
    rw [periodicSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [show ((d * y.val : ℕ) : ZMod f) =
      (d : ZMod f) * (y.val : ZMod f) by norm_num, map_mul]
    rw [show t * (d * y.val) = d * t * y.val by ring]
    rw [stdAddChar_cancel_divisor_of_dvd hdpos.ne' hddiv]
    ring
  change (ArithmeticFunction.moebius d : ℂ) *
      (∑ y : Fin ((f * l) / d),
        chi (((d * y.val : ℕ) : ZMod f)) *
          ZMod.stdAddChar (N := f * l)
            ((t * (d * y.val) : ℕ) : ZMod (f * l))) = _
  rw [hinner, periodicSum_eq chi]
  by_cases hs : l / d ∣ t
  · rw [if_pos hs, if_pos hs,
      gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := f)) hchi]
    ring
  · rw [if_neg hs, if_neg hs]
    simp

/-- Conjugate-value spelling of
`gaussSum_changeLevel_eq_conductor_formula`.  For complex multiplicative
characters, pointwise inversion is exactly complex conjugation. -/
theorem gaussSum_changeLevel_eq_conductor_formula_conj
    {f l t : ℕ} [NeZero f] [NeZero l]
    (chi : DirichletCharacter ℂ f) (hchi : chi.IsPrimitive) :
    gaussSum (DirichletCharacter.changeLevel (f.dvd_mul_right l) chi)
        ((ZMod.stdAddChar (N := f * l)).mulShift (t : ZMod (f * l))) =
      gaussSum chi (ZMod.stdAddChar (N := f)) *
        ∑ d ∈ l.divisors,
          if (l / d) ∣ t then
            (ArithmeticFunction.moebius d : ℂ) *
              chi ((d : ℕ) : ZMod f) * ((l / d : ℕ) : ℂ) *
                star (chi ((t / (l / d) : ℕ) : ZMod f))
          else 0 := by
  rw [gaussSum_changeLevel_eq_conductor_formula chi hchi]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hs : l / d ∣ t
  · rw [if_pos hs, if_pos hs, MulChar.star_apply']
  · rw [if_neg hs, if_neg hs]

/-- Complementary-divisor (`s`) spelling of the exact conductor formula.
The zero extension of `chi` automatically removes terms for which
`l / s` is not coprime to `f`. -/
theorem gaussSum_changeLevel_eq_conductor_formula_s
    {f l t : ℕ} [NeZero f] [NeZero l]
    (chi : DirichletCharacter ℂ f) (hchi : chi.IsPrimitive) :
    gaussSum (DirichletCharacter.changeLevel (f.dvd_mul_right l) chi)
        ((ZMod.stdAddChar (N := f * l)).mulShift (t : ZMod (f * l))) =
      gaussSum chi (ZMod.stdAddChar (N := f)) *
        ∑ s ∈ l.divisors,
          if s ∣ t then
            (ArithmeticFunction.moebius (l / s) : ℂ) *
              chi ((l / s : ℕ) : ZMod f) * (s : ℂ) *
                star (chi ((t / s : ℕ) : ZMod f))
          else 0 := by
  rw [gaussSum_changeLevel_eq_conductor_formula_conj chi hchi]
  congr 1
  simpa only using
    (sum_divisors_complement (M := ℂ) (NeZero.ne l)
      (fun d s ↦ if s ∣ t then
        (ArithmeticFunction.moebius d : ℂ) *
          chi ((d : ℕ) : ZMod f) * (s : ℂ) *
            star (chi ((t / s : ℕ) : ZMod f))
        else 0))

/-- The exact conductor formula in the unit-supported generalized Gauss-sum
notation used by the SQ4 transform. -/
theorem unitGaussSum_changeLevel_eq_conductor_formula_conj
    {f l t : ℕ} [NeZero f] [NeZero l]
    (chi : DirichletCharacter ℂ f) (hchi : chi.IsPrimitive) :
    unitGaussSum
        (DirichletCharacter.changeLevel (f.dvd_mul_right l) chi).toUnitHom
        (ZMod.stdAddChar (N := f * l)) (t : ZMod (f * l)) =
      gaussSum chi (ZMod.stdAddChar (N := f)) *
        ∑ d ∈ l.divisors,
          if (l / d) ∣ t then
            (ArithmeticFunction.moebius d : ℂ) *
              chi ((d : ℕ) : ZMod f) * ((l / d : ℕ) : ℂ) *
                star (chi ((t / (l / d) : ℕ) : ZMod f))
          else 0 := by
  rw [unitGaussSum_eq_gaussSum,
    gaussSum_changeLevel_eq_conductor_formula_conj chi hchi]

/-- Unit-supported version of the complementary-divisor formula. -/
theorem unitGaussSum_changeLevel_eq_conductor_formula_s
    {f l t : ℕ} [NeZero f] [NeZero l]
    (chi : DirichletCharacter ℂ f) (hchi : chi.IsPrimitive) :
    unitGaussSum
        (DirichletCharacter.changeLevel (f.dvd_mul_right l) chi).toUnitHom
        (ZMod.stdAddChar (N := f * l)) (t : ZMod (f * l)) =
      gaussSum chi (ZMod.stdAddChar (N := f)) *
        ∑ s ∈ l.divisors,
          if s ∣ t then
            (ArithmeticFunction.moebius (l / s) : ℂ) *
              chi ((l / s : ℕ) : ZMod f) * (s : ℂ) *
                star (chi ((t / s : ℕ) : ZMod f))
          else 0 := by
  rw [unitGaussSum_eq_gaussSum,
    gaussSum_changeLevel_eq_conductor_formula_s chi hchi]

/-! ## Shared squarefree slots and the CRT boundary -/

/-- Two nonzero Möbius slots may share primes.  For squarefree `u₁,u₂`,
the common part `g` and the two quotients are pairwise coprime, but the source
modulus contains `g²`. -/
theorem squarefree_gcd_decomposition {u₁ u₂ : ℕ}
    (hu₁ : Squarefree u₁) (hu₂ : Squarefree u₂) :
    let g := u₁.gcd u₂
    let a := u₁ / g
    let b := u₂ / g
    u₁ = g * a ∧ u₂ = g * b ∧
      g.Coprime a ∧ g.Coprime b ∧ a.Coprime b ∧
      u₁ * u₂ = g ^ 2 * a * b := by
  let g := u₁.gcd u₂
  let a := u₁ / g
  let b := u₂ / g
  change u₁ = g * a ∧ u₂ = g * b ∧
    g.Coprime a ∧ g.Coprime b ∧ a.Coprime b ∧
    u₁ * u₂ = g ^ 2 * a * b
  have hg₁ : g ∣ u₁ := Nat.gcd_dvd_left u₁ u₂
  have hg₂ : g ∣ u₂ := Nat.gcd_dvd_right u₁ u₂
  have ha₂ : a.Coprime u₂ :=
    Nat.coprime_div_gcd_of_squarefree hu₁ hu₂.ne_zero
  have hb₁ : b.Coprime u₁ := by
    simpa only [g, b, Nat.gcd_comm] using
      Nat.coprime_div_gcd_of_squarefree hu₂ hu₁.ne_zero
  have hga : g.Coprime a :=
    (Nat.Coprime.of_dvd_right hg₂ ha₂).symm
  have hgb : g.Coprime b :=
    (Nat.Coprime.of_dvd_right hg₁ hb₁).symm
  have hab : a.Coprime b :=
    Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd hg₂) ha₂
  have hu₁eq : u₁ = g * a := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel hg₁).symm
  have hu₂eq : u₂ = g * b := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel hg₂).symm
  refine ⟨hu₁eq, hu₂eq, hga, hgb, hab, ?_⟩
  rw [hu₁eq, hu₂eq]
  ring

/-- The common squarefree factor contributes its Möbius sign twice, so
that sign cancels exactly.  The common factor nevertheless remains squared
in the modulus, as `squarefree_gcd_decomposition` records. -/
theorem moebius_pair_shared_gcd_cancellation {u₁ u₂ : ℕ}
    (hu₁ : Squarefree u₁) (hu₂ : Squarefree u₂) :
    ArithmeticFunction.moebius u₁ * ArithmeticFunction.moebius u₂ =
      ArithmeticFunction.moebius (u₁ / u₁.gcd u₂) *
        ArithmeticFunction.moebius (u₂ / u₁.gcd u₂) := by
  let g := u₁.gcd u₂
  let a := u₁ / g
  let b := u₂ / g
  change ArithmeticFunction.moebius u₁ * ArithmeticFunction.moebius u₂ =
    ArithmeticFunction.moebius a * ArithmeticFunction.moebius b
  have h := squarefree_gcd_decomposition hu₁ hu₂
  change u₁ = g * a ∧ u₂ = g * b ∧
    g.Coprime a ∧ g.Coprime b ∧ a.Coprime b ∧
    u₁ * u₂ = g ^ 2 * a * b at h
  rcases h with ⟨hu₁eq, hu₂eq, hga, hgb, _, _⟩
  have hg : Squarefree g :=
    hu₁.squarefree_of_dvd (Nat.gcd_dvd_left u₁ u₂)
  rw [hu₁eq, hu₂eq,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hga.gcd_eq_one,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hgb.gcd_eq_one]
  calc
    (ArithmeticFunction.moebius g * ArithmeticFunction.moebius a) *
        (ArithmeticFunction.moebius g * ArithmeticFunction.moebius b) =
      ArithmeticFunction.moebius g ^ 2 *
        (ArithmeticFunction.moebius a * ArithmeticFunction.moebius b) := by ring
    _ = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b := by
      rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree hg, one_mul]

/-- Smallest source-shaped obstruction to treating the two outer Möbius
slots as coprime: both coefficients at `2` are nonzero, but the slots are
not coprime. -/
theorem shared_moebius_prime_counterexample :
    ArithmeticFunction.moebius 2 ≠ 0 ∧
      ArithmeticFunction.moebius 2 ≠ 0 ∧ ¬ Nat.Coprime 2 2 := by
  have hp : Nat.Prime 2 := by decide
  rw [ArithmeticFunction.moebius_apply_prime hp]
  norm_num

/-- The corresponding naive CRT is genuinely false: `ZMod 4` has a
nonzero square-zero element, while every element of `ZMod 2 × ZMod 2` is
idempotent. -/
theorem zmod_four_not_crt_two_two :
    ¬ Nonempty (ZMod 4 ≃+* (ZMod 2 × ZMod 2)) := by
  rintro ⟨e⟩
  have hx : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by decide
  have hidem : ∀ y : ZMod 2 × ZMod 2, y ^ 2 = y := by decide
  have hezero : e (2 : ZMod 4) = 0 := by
    rw [← hidem (e (2 : ZMod 4)), ← map_pow, hx.2, map_zero]
  apply hx.1
  apply e.injective
  simpa using hezero

end RH.Zeta85.SQ4CRTConductor

end
