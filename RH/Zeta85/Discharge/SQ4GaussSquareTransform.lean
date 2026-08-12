/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/SQ4GaussSquareTransform.lean

Exact finite algebra behind the multiplicative transform of the surviving
SQ4 Kloosterman kernel.  The ring may be composite.  No analytic estimate,
primitivity assertion, complete-sum bound, or source moment is asserted.
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

noncomputable section

open scoped BigOperators

namespace RH.Zeta85.SQ4GaussSquareTransform

variable {R : Type*} [CommRing R] [Fintype Rˣ]

/-- A multiplicative character on the unit group, with values represented by
complex units so that inversion is literal and never invokes a nonvanishing
assumption. -/
abbrev UnitCharacter (R : Type*) [CommRing R] := Rˣ →* ℂˣ

/-- The unit-supported shifted Gauss sum.  For `R = ZMod q`, this is
`∑_{z mod q}^* χ(z) ψ(a z)`. -/
def unitGaussSum (chi : UnitCharacter R) (psi : AddChar R ℂ) (a : R) : ℂ :=
  ∑ z : Rˣ, (chi z : ℂ) * psi (a * (z : R))

/-- The source Kloosterman kernel on the unit group.  For `R = ZMod q`,
`psi = e(·/q)`, this is `S(k v⁻¹, r; q)`. -/
def kloostermanKernel (psi : AddChar R ℂ) (k r : R) (v : Rˣ) : ℂ :=
  ∑ z : Rˣ, psi (k * ((v⁻¹ * z : Rˣ) : R) + r * ((z⁻¹ : Rˣ) : R))

/-- Multiplicative Fourier transform with the inverse-character convention:
`\hat F(chi) = ∑_v chi(v)⁻¹ F(v)`. -/
def unitFourierTransform (chi : UnitCharacter R) (F : Rˣ → ℂ) : ℂ :=
  ∑ v : Rˣ, ((chi v : ℂ)⁻¹) * F v

/-- The change of variables
`(v,z) ↦ (w,y) = (v⁻¹z,z⁻¹)` used in the transform. -/
def kernelChange : Rˣ × Rˣ ≃ Rˣ × Rˣ where
  toFun vz := (vz.1⁻¹ * vz.2, vz.2⁻¹)
  invFun wy := ((wy.1 * wy.2)⁻¹, wy.2⁻¹)
  left_inv vz := by
    ext <;> simp
  right_inv wy := by
    ext <;> simp

/-- Abstract correlation factorization.  This is the finite algebraic core;
it needs only the unit group and makes no assumption on the modulus. -/
theorem correlation_transform_factorization
    (chi : UnitCharacter R) (A B : Rˣ → ℂ) :
    (∑ v : Rˣ, ((chi v : ℂ)⁻¹) *
        ∑ z : Rˣ, A (v⁻¹ * z) * B z⁻¹) =
      (∑ w : Rˣ, (chi w : ℂ) * A w) *
        ∑ y : Rˣ, (chi y : ℂ) * B y := by
  rw [Fintype.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv kernelChange _ _ fun vz ↦ by
    change ((chi vz.1 : ℂ)⁻¹) * (A (vz.1⁻¹ * vz.2) * B vz.2⁻¹) =
      ((chi (vz.1⁻¹ * vz.2) : ℂ) * A (vz.1⁻¹ * vz.2)) *
        ((chi vz.2⁻¹ : ℂ) * B vz.2⁻¹)
    simp only [MonoidHom.map_mul, MonoidHom.map_inv, Units.val_mul,
      Units.val_inv_eq_inv_val]
    field_simp

/-- Exact transform of the Kloosterman kernel into two shifted Gauss sums.
This holds for every finite commutative ring, including `ZMod q` for
composite `q`, and for arbitrary residues `k,r`. -/
theorem kloosterman_transform_eq_gauss_product
    (chi : UnitCharacter R) (psi : AddChar R ℂ) (k r : R) :
    unitFourierTransform chi (kloostermanKernel psi k r) =
      unitGaussSum chi psi k * unitGaussSum chi psi r := by
  simp only [unitFourierTransform, kloostermanKernel]
  simp_rw [psi.map_add_eq_mul]
  simpa [unitGaussSum] using
    correlation_transform_factorization chi
      (fun w : Rˣ ↦ psi (k * (w : R)))
      (fun y : Rˣ ↦ psi (r * (y : R)))

/-- Scaling a shifted Gauss sum by a unit.  This is the precise algebraic
content behind `tau_q(chi;a) = chi(a)⁻¹ tau_q(chi;1)`; it does not require
the character to be primitive. -/
theorem unitGaussSum_unit_scale
    (chi : UnitCharacter R) (psi : AddChar R ℂ) (a : Rˣ) :
    unitGaussSum chi psi (a : R) =
      ((chi a : ℂ)⁻¹) * unitGaussSum chi psi 1 := by
  rw [unitGaussSum, unitGaussSum, Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun z ↦ by
    change (chi z : ℂ) * psi ((a : R) * (z : R)) =
      ((chi a : ℂ)⁻¹) *
        ((chi (a * z) : ℂ) * psi (1 * ((a * z : Rˣ) : R)))
    simp only [MonoidHom.map_mul, Units.val_mul, one_mul]
    field_simp

/-- On the coprime/unit stratum, the product is a square Gauss twist.
The hypotheses that `k,r` are units are essential for this simplification;
the preceding product identity remains valid without them. -/
theorem kloosterman_transform_eq_gauss_square
    (chi : UnitCharacter R) (psi : AddChar R ℂ) (k r : Rˣ) :
    unitFourierTransform chi
        (kloostermanKernel psi (k : R) (r : R)) =
      ((chi (k * r) : ℂ)⁻¹) * (unitGaussSum chi psi 1) ^ 2 := by
  rw [kloosterman_transform_eq_gauss_product,
    unitGaussSum_unit_scale, unitGaussSum_unit_scale]
  simp only [MonoidHom.map_mul, Units.val_mul, pow_two]
  field_simp

/-! ## Exact Dirichlet-character inversion on `ZMod q` -/

/-- The preceding inverse-character transform specialized to a Dirichlet
character modulo `q`. -/
def dirichletUnitFourierTransform {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (F : (ZMod q)ˣ → ℂ) : ℂ :=
  unitFourierTransform chi.toUnitHom F

/-- Exact finite Fourier inversion on the units modulo `q`. -/
theorem dirichlet_fourier_inversion {q : ℕ} [NeZero q]
    (F : (ZMod q)ˣ → ℂ) (v : (ZMod q)ˣ) :
    F v = ((q.totient : ℂ)⁻¹) *
      ∑ chi : DirichletCharacter ℂ q,
        chi (v : ZMod q) * dirichletUnitFourierTransform chi F := by
  simp only [dirichletUnitFourierTransform, unitFourierTransform]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  let _ : NeZero ((Monoid.exponent (ZMod q)ˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ)⟩
  have horth (y : (ZMod q)ˣ) :
      (∑ chi : DirichletCharacter ℂ q,
          ((chi.toUnitHom y : ℂ)⁻¹) * chi (v : ZMod q)) =
        if (y : ZMod q) = (v : ZMod q) then (q.totient : ℂ) else 0 := by
    simpa using
      (DirichletCharacter.sum_char_inv_mul_char_eq ℂ y.isUnit (v : ZMod q))
  have hphi : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  symm
  calc
    (∑ y : (ZMod q)ˣ, ∑ chi : DirichletCharacter ℂ q,
        ((q.totient : ℂ)⁻¹) *
          (chi (v : ZMod q) *
            (((chi.toUnitHom y : ℂ)⁻¹) * F y))) =
        ∑ y : (ZMod q)ˣ,
          (((q.totient : ℂ)⁻¹) *
            (∑ chi : DirichletCharacter ℂ q,
              ((chi.toUnitHom y : ℂ)⁻¹) * chi (v : ZMod q))) * F y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro chi _
      ring
    _ = ∑ y : (ZMod q)ˣ,
          (if (y : ZMod q) = (v : ZMod q) then 1 else 0) * F y := by
      simp_rw [horth]
      simp [hphi]
    _ = F v := by
      simp [Units.val_inj]

/-- Source-faithful inversion of the Kloosterman kernel.  It retains the two
shifted Gauss sums for arbitrary `k,r`; no coprimality or primitivity is used. -/
theorem kloosterman_kernel_character_inversion {q : ℕ} [NeZero q]
    (psi : AddChar (ZMod q) ℂ) (k r : ZMod q) (v : (ZMod q)ˣ) :
    kloostermanKernel psi k r v = ((q.totient : ℂ)⁻¹) *
      ∑ chi : DirichletCharacter ℂ q,
        chi (v : ZMod q) *
          (unitGaussSum chi.toUnitHom psi k *
            unitGaussSum chi.toUnitHom psi r) := by
  calc
    kloostermanKernel psi k r v = ((q.totient : ℂ)⁻¹) *
        ∑ chi : DirichletCharacter ℂ q,
          chi (v : ZMod q) *
            dirichletUnitFourierTransform chi
              (kloostermanKernel psi k r) :=
      dirichlet_fourier_inversion (kloostermanKernel psi k r) v
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro chi _
      congr 1
      simpa only [dirichletUnitFourierTransform] using
        kloosterman_transform_eq_gauss_product chi.toUnitHom psi k r

end RH.Zeta85.SQ4GaussSquareTransform

end
