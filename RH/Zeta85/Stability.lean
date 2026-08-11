/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Zeta23.LinAlg
import Mathlib.Order.Interval.Finset.Fin

/-!
# The quartic stability inequality

This file formalizes the finite-dimensional stability argument recorded in
`docs/audit/stability_inequality_proof.md`.  It is independent of every analytic
hypothesis in the conditional layer.

For a Hermitian matrix `G`, `tailExcessSq hG b` is

`sum_{i >= b} ((lambda_i(G) - 1)^+)^2`,

where the eigenvalues are in decreasing order.  The main theorem proves the
exact bound used by the quartic rungs.  The last section proves that the same
bound passes to isometric, hence principal, compressions.
-/

open Matrix Finset
open scoped BigOperators ComplexOrder

noncomputable section

namespace RH
namespace Zeta85

open RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Sorted tail energies -/

/-- The index `b + j` in a vector of length `N`, for `j < N - b`. -/
def tailIndex (N b : ℕ) (j : Fin (N - b)) : Fin N :=
  ⟨b + j, by omega⟩

/-- The index `j` in a vector of length `N`, for `j < N - b`. -/
def headIndex (N b : ℕ) (j : Fin (N - b)) : Fin N :=
  ⟨j, by omega⟩

@[simp] lemma tailIndex_val (N b : ℕ) (j : Fin (N - b)) :
    (tailIndex N b j).val = b + j := rfl

@[simp] lemma headIndex_val (N b : ℕ) (j : Fin (N - b)) :
    (headIndex N b j).val = j := rfl

/-- The squared positive excess after the largest `b` eigenvalues have been removed. -/
def tailExcessSq {N : ℕ} {G : Matrix (Fin N) (Fin N) 𝕜}
    (hG : G.IsHermitian) (b : ℕ) : ℝ :=
  ∑ j : Fin (Fintype.card (Fin N) - b),
    ((hG.eigenvalues₀ (tailIndex (Fintype.card (Fin N)) b j) - 1)⁺) ^ 2

/-- The squared positive excess over all eigenvalues. -/
def fullExcessSq {N : ℕ} {G : Matrix (Fin N) (Fin N) 𝕜}
    (hG : G.IsHermitian) : ℝ :=
  ∑ i : Fin (Fintype.card (Fin N)), ((hG.eigenvalues₀ i - 1)⁺) ^ 2

/-- `tailExcessSq` depends on the matrix, not on the chosen Hermitian proof. -/
lemma tailExcessSq_congr {N : ℕ} {G H : Matrix (Fin N) (Fin N) 𝕜}
    (hGH : G = H) (hG : G.IsHermitian) (hH : H.IsHermitian) (b : ℕ) :
    tailExcessSq hG b = tailExcessSq hH b := by
  subst H
  rfl

private lemma excessSq_mono {x y : ℝ} (hxy : x ≤ y) :
    ((x - 1)⁺) ^ 2 ≤ ((y - 1)⁺) ^ 2 := by
  exact pow_le_pow_left₀ (posPart_nonneg _) (posPart_mono (sub_le_sub_right hxy 1)) 2

private lemma excessSq_le_charge (x : ℝ) :
    ((x - 1)⁺) ^ 2 ≤ x ^ 2 - 2 * x + if 0 < x then 1 else 0 := by
  by_cases hx0 : 0 < x
  · rw [if_pos hx0]
    by_cases hx1 : 1 < x
    · rw [posPart_eq_self.mpr (sub_nonneg.mpr hx1.le)]
      ring_nf
      exact le_rfl
    · rw [posPart_eq_zero.mpr (sub_nonpos.mpr (not_lt.mp hx1))]
      nlinarith [sq_nonneg (x - 1)]
  · rw [if_neg hx0, posPart_eq_zero.mpr (sub_nonpos.mpr (by linarith))]
    nlinarith [sq_nonneg x]

/-- The scalar estimate (11), summed over the spectrum. -/
private lemma fullExcessSq_le {N s : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) (hpos : posIndex hA ≤ s) :
    fullExcessSq hA ≤ frobSq A - 2 * rtrace A + s := by
  have hsum :
      (∑ i : Fin (Fintype.card (Fin N)), ((hA.eigenvalues₀ i - 1)⁺) ^ 2)
        ≤ ∑ i : Fin (Fintype.card (Fin N)),
            ((hA.eigenvalues₀ i) ^ 2 - 2 * hA.eigenvalues₀ i
              + if 0 < hA.eigenvalues₀ i then 1 else 0) :=
    Finset.sum_le_sum fun i _ => excessSq_le_charge (hA.eigenvalues₀ i)
  have hsquares :
      (∑ i : Fin (Fintype.card (Fin N)), (hA.eigenvalues₀ i) ^ 2) = frobSq A := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hA,
      sum_eigenvalues_reindex hA (fun x => x ^ 2)]
  have htrace :
      (∑ i : Fin (Fintype.card (Fin N)), hA.eigenvalues₀ i) = rtrace A := by
    rw [rtrace_eq_sum_eigenvalues hA]
    simpa using (sum_eigenvalues_reindex hA (fun x => x)).symm
  have hindicator :
      (∑ i : Fin (Fintype.card (Fin N)),
          if 0 < hA.eigenvalues₀ i then (1 : ℝ) else 0)
        = posIndex hA := by
    rw [show (∑ i : Fin (Fintype.card (Fin N)),
          if 0 < hA.eigenvalues₀ i then (1 : ℝ) else 0)
        = (#{i : Fin (Fintype.card (Fin N)) | 0 < hA.eigenvalues₀ i} : ℕ) by simp]
    norm_cast
    rw [← card_eigenvalues_reindex hA (fun x => 0 < x)]
    rfl
  simp only [fullExcessSq, sum_add_distrib, sum_sub_distrib, ← mul_sum] at hsum ⊢
  rw [hsquares, htrace, hindicator] at hsum
  have hpos' : (posIndex hA : ℝ) ≤ s := by exact_mod_cast hpos
  linarith

/-! ## Rank perturbation in threshold-count form -/

/-- Rank is subadditive for square matrices. -/
private lemma matrix_rank_add_le {N : ℕ} (A B : Matrix (Fin N) (Fin N) 𝕜) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rintro _ ⟨x, rfl⟩
  simp only [mulVecLin_apply, add_mulVec]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

/-- If the quadratic form of the spectral truncation above `theta` vanishes on `x`,
then the original form on `x` is at most `theta * ||x||^2`. -/
private lemma hermForm_le_of_truncForm_eq_zero {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) (θ : ℝ)
    (x : Fin N → 𝕜)
    (hzero : hermForm (specMap hA (fun t => (t - θ)⁺)) x = 0) :
    hermForm A x ≤ θ * ∑ i, ‖x i‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => (t - θ)⁺
  let c : Fin N → 𝕜 :=
    star (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) 𝕜) *ᵥ x
  have hformS : hermForm (specMap hA f) x
      = ∑ i, f (hA.eigenvalues i) * ‖c i‖ ^ 2 := by
    simpa [hermForm, c] using hermForm_specMap hA f x
  have hsum0 : (∑ i, f (hA.eigenvalues i) * ‖c i‖ ^ 2) = 0 := by
    rw [← hformS]
    simpa [f] using hzero
  have hterm0 : ∀ i, f (hA.eigenvalues i) * ‖c i‖ ^ 2 = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun i => f (hA.eigenvalues i) * ‖c i‖ ^ 2)
      (fun i _ => mul_nonneg (posPart_nonneg _) (sq_nonneg _))).mp hsum0
    exact fun i => h i (Finset.mem_univ i)
  have hformA : hermForm A x = ∑ i, hA.eigenvalues i * ‖c i‖ ^ 2 := by
    have h := hermForm_specMap hA id x
    rw [specMap_id] at h
    simpa [hermForm, c] using h
  have hnorm : (∑ i, ‖c i‖ ^ 2) = ∑ i, ‖x i‖ ^ 2 := by
    simpa [c] using sum_normSq_unitary_mulVec hA x
  rw [hformA, ← hnorm, mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : hA.eigenvalues i ≤ θ
  · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  · have hfpos : 0 < f (hA.eigenvalues i) := by
      simp only [f]
      rw [posPart_eq_self.mpr (sub_nonneg.mpr (not_le.mp hi).le)]
      linarith
    have hci : ‖c i‖ ^ 2 = 0 :=
      (mul_eq_zero.mp (hterm0 i)).resolve_left hfpos.ne'
    rw [hci]
    simp

/-- Adding a positive-semidefinite matrix of rank `r` can create at most `r`
new eigenvalues above any threshold.  This is the rank form of Weyl interlacing
needed by the stability proof. -/
private theorem posIndexAbove_add_posSemidef_le_rank {N : ℕ}
    {A B : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) (hB : B.PosSemidef) (θ : ℝ) :
    posIndexAbove (hA.add hB.isHermitian) θ ≤ posIndexAbove hA θ + B.rank := by
  let hG : (A + B).IsHermitian := hA.add hB.isHermitian
  let S : Matrix (Fin N) (Fin N) 𝕜 := specMap hA (fun t => (t - θ)⁺)
  let T : Matrix (Fin N) (Fin N) 𝕜 := S + B
  let W : Submodule 𝕜 (Fin N → 𝕜) :=
    LinearMap.range (specMap hG (fun t => (t - θ)⁺)).mulVecLin
  have hSpsd : S.PosSemidef := by
    dsimp only [S]
    exact specMap_posSemidef hA fun _ => posPart_nonneg _
  have hdimW : Module.finrank 𝕜 W = posIndexAbove hG θ := by
    dsimp only [W]
    exact finrank_range_truncPos hG θ
  have hgt : ∀ x ∈ W, x ≠ 0 →
      θ * ∑ i, ‖x i‖ ^ 2 < hermForm (A + B) x := by
    dsimp only [W]
    exact hermForm_gt_on_range_truncPos hG θ
  let L : (Fin N → 𝕜) →ₗ[𝕜] (Fin N → 𝕜) := T.mulVecLin
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxT : T *ᵥ x = 0 := hxL
    simp only [Submodule.mem_bot]
    by_contra hne
    have hxne : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hformT : hermForm T x = 0 := by
      unfold hermForm
      rw [hxT]
      simp
    have hsplit : hermForm T x = hermForm S x + hermForm B x := by
      exact hermForm_add S B x
    have hSnonneg : 0 ≤ hermForm S x := hermForm_nonneg_of_posSemidef hSpsd x
    have hBnonneg : 0 ≤ hermForm B x := hermForm_nonneg_of_posSemidef hB x
    have hSzero : hermForm S x = 0 := by linarith
    have hBzero : hermForm B x = 0 := by linarith
    have hAle : hermForm A x ≤ θ * ∑ i, ‖x i‖ ^ 2 :=
      hermForm_le_of_truncForm_eq_zero hA θ x (by simpa [S] using hSzero)
    have hGform : hermForm (A + B) x = hermForm A x + hermForm B x :=
      hermForm_add A B x
    have := hgt x hxW hxne
    linarith
  have hrankS : S.rank = posIndexAbove hA θ := by
    dsimp only [S]
    change Module.finrank 𝕜
      (LinearMap.range (specMap hA (fun t => (t - θ)⁺)).mulVecLin) = _
    exact finrank_range_truncPos hA θ
  calc
    posIndexAbove (hA.add hB.isHermitian) θ
        = Module.finrank 𝕜 W := hdimW.symm
    _ = Module.finrank 𝕜 (LinearMap.range (L.domRestrict W)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank 𝕜 (LinearMap.range L) := by
        apply Submodule.finrank_mono
        rintro y ⟨⟨x, hxW⟩, rfl⟩
        exact ⟨x, rfl⟩
    _ = T.rank := rfl
    _ ≤ S.rank + B.rank := matrix_rank_add_le S B
    _ = posIndexAbove hA θ + B.rank := by rw [hrankS]

/-! ## From threshold counts to ordered eigenvalues -/

/-- Rank-`b` Weyl interlacing, derived from threshold counts. -/
private theorem eigenvalues₀_add_psd_rank_interlace {N b : ℕ}
    {A B : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) (hB : B.PosSemidef) (hrank : B.rank ≤ b)
    (j : Fin (Fintype.card (Fin N) - b)) :
    (hA.add hB.isHermitian).eigenvalues₀
        (tailIndex (Fintype.card (Fin N)) b j)
      ≤ hA.eigenvalues₀ (headIndex (Fintype.card (Fin N)) b j) := by
  let d := Fintype.card (Fin N)
  let hG : (A + B).IsHermitian := hA.add hB.isHermitian
  let ig : Fin d := tailIndex d b j
  let ir : Fin d := headIndex d b j
  let θ : ℝ := hA.eigenvalues₀ ir
  let sg : Finset (Fin d) := {i | θ < hG.eigenvalues₀ i}
  let sr : Finset (Fin d) := {i | θ < hA.eigenvalues₀ i}
  have hcount : #sg ≤ #sr + b := by
    have h := posIndexAbove_add_posSemidef_le_rank hA hB θ
    have h' : posIndexAbove hG θ ≤ posIndexAbove hA θ + b :=
      h.trans (Nat.add_le_add_left hrank _)
    simpa only [sg, sr, posIndexAbove, hG, θ,
      card_eigenvalues_reindex hG (fun x => θ < x),
      card_eigenvalues_reindex hA (fun x => θ < x)] using h'
  by_contra hnot
  have hlt : θ < hG.eigenvalues₀ ig := lt_of_not_ge hnot
  have hlow : Finset.Iic ig ⊆ sg := by
    intro i hi
    simp only [sg, mem_filter, mem_univ, true_and]
    exact lt_of_lt_of_le hlt (hG.eigenvalues₀_antitone (Finset.mem_Iic.mp hi))
  have hupp : sr ⊆ Finset.Iio ir := by
    intro i hi
    have hi' : θ < hA.eigenvalues₀ i := by
      simpa only [sr, mem_filter, mem_univ, true_and] using hi
    apply Finset.mem_Iio.mpr
    by_contra hni
    have hir : ir ≤ i := not_lt.mp hni
    have := hA.eigenvalues₀_antitone hir
    dsimp only [θ] at hi'
    linarith
  have hbad : b + j.val + 1 ≤ j.val + b := calc
    b + j.val + 1 = #(Finset.Iic ig) := by simp [ig, tailIndex]
    _ ≤ #sg := Finset.card_le_card hlow
    _ ≤ #sr + b := hcount
    _ ≤ #(Finset.Iio ir) + b := Nat.add_le_add_right (Finset.card_le_card hupp) b
    _ = j.val + b := by simp [ir, headIndex]
  omega

private def headEmbedding (N b : ℕ) : Fin (N - b) ↪ Fin N where
  toFun := headIndex N b
  inj' := by
    intro i j h
    refine Fin.ext ?_
    simpa [headIndex] using congrArg (fun x : Fin N => x.val) h

/-- Removing the `b` eigenvalue directions supplied by a PSD rank-`b`
perturbation leaves no more excess energy than the full unperturbed matrix. -/
private lemma tailExcessSq_add_psd_le_full {N b : ℕ}
    {A B : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) (hB : B.PosSemidef) (hrank : B.rank ≤ b) :
    tailExcessSq (hA.add hB.isHermitian) b ≤ fullExcessSq hA := by
  have hpoint : ∀ j : Fin (Fintype.card (Fin N) - b),
      (((hA.add hB.isHermitian).eigenvalues₀
          (tailIndex (Fintype.card (Fin N)) b j) - 1)⁺) ^ 2
        ≤ ((hA.eigenvalues₀
          (headIndex (Fintype.card (Fin N)) b j) - 1)⁺) ^ 2 :=
    fun j => excessSq_mono (eigenvalues₀_add_psd_rank_interlace hA hB hrank j)
  calc
    tailExcessSq (hA.add hB.isHermitian) b
        ≤ ∑ j : Fin (Fintype.card (Fin N) - b),
            ((hA.eigenvalues₀
              (headIndex (Fintype.card (Fin N)) b j) - 1)⁺) ^ 2 := by
          exact Finset.sum_le_sum fun j _ => hpoint j
    _ = ∑ i ∈ Finset.univ.map (headEmbedding (Fintype.card (Fin N)) b),
          ((hA.eigenvalues₀ i - 1)⁺) ^ 2 := by
          rw [Finset.sum_map]
          rfl
    _ ≤ ∑ i : Fin (Fintype.card (Fin N)), ((hA.eigenvalues₀ i - 1)⁺) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
    _ = fullExcessSq hA := rfl

/-! ## Positive index of `P - N` -/

private lemma posIndex_eq_zero_of_hermForm_nonpos {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (h : ∀ x, hermForm A x ≤ 0) : posIndex hA = 0 := by
  obtain ⟨W, hW, hdim⟩ := posIndex_eq_max_finrank_posDefOn hA
  rw [← hdim, Submodule.finrank_eq_zero]
  by_contra hne
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).mp hne
  exact absurd (hW x hxW hx0) (not_lt.mpr (h x))

private lemma posIndex_neg_eq_zero_of_posSemidef {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosSemidef) :
    posIndex hA.isHermitian.neg = 0 := by
  refine posIndex_eq_zero_of_hermForm_nonpos _ fun x => ?_
  have hneg : hermForm (-A) x = -hermForm A x := by
    unfold hermForm
    rw [neg_mulVec, dotProduct_neg, map_neg]
  rw [hneg, neg_nonpos]
  exact hermForm_nonneg_of_posSemidef hA x

private lemma posIndex_sub_le_rank {N : ℕ}
    {P A : Matrix (Fin N) (Fin N) 𝕜}
    (hP : P.PosSemidef) (hA : A.PosSemidef) :
    posIndex (hP.isHermitian.sub hA.isHermitian) ≤ P.rank := by
  have h := posIndex_add_le hP.isHermitian hA.isHermitian.neg
  rw [posIndex_eq_rank_of_posSemidef hP,
    posIndex_neg_eq_zero_of_posSemidef hA, add_zero] at h
  convert h using 2
  exact sub_eq_add_neg P A

/-! ## Exact slack and the stability theorem -/

/-- The exact nonnegative slack identity (13), used in inequality form. -/
private lemma exact_stability_slack {N s b : ℕ}
    {P Q : Matrix (Fin N) (Fin N) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (htraceP : rtrace P ≤ s) (hposQ : posIndex hQ ≤ b) :
    let Qm := hermNegPart hQ
    let R := P - Qm
    frobSq R - 2 * rtrace R + s
      ≤ frobSq (P + Q) - 4 * rtrace (P + Q) + 3 * s + 4 * b := by
  dsimp only
  let Qp := hermPosPart hQ
  let Qm := hermNegPart hQ
  let R := P - Qm
  have hQdec : Q = Qp - Qm := by
    exact (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQmQp : Qm * Qp = 0 := hermNegPart_mul_hermPosPart hQ
  have hR : R.IsHermitian := hP.isHermitian.sub hQm_psd.isHermitian
  have hGR : P + Q = R + Qp := by
    rw [hQdec]
    dsimp only [R]
    abel
  have hRQp : R * Qp = P * Qp := by
    dsimp only [R]
    rw [sub_mul, hQmQp]
    simp
  have hfrob : frobSq (P + Q)
      = frobSq R + 2 * RCLike.re (P * Qp).trace + frobSq Qp := by
    rw [hGR, frobSq_add_hermitian hR hQp_psd.isHermitian, hRQp]
  have htraceR : rtrace R = rtrace P - rtrace Qm := by
    dsimp only [R]
    exact rtrace_sub P Qm
  have htraceG : rtrace (P + Q) = rtrace P + rtrace Qp - rtrace Qm := by
    rw [hGR, rtrace_add, htraceR]
    ring
  have hcross : 0 ≤ RCLike.re (P * Qp).trace :=
    trace_mul_nonneg_of_posSemidef hP hQp_psd
  have htraceQm : 0 ≤ rtrace Qm := by
    dsimp only [Qm]
    rw [rtrace_hermNegPart]
    exact Finset.sum_nonneg fun _ _ => negPart_nonneg _
  have hposQp : posIndex hQp_psd.isHermitian ≤ b := by
    rw [posIndex_eq_rank_of_posSemidef hQp_psd]
    dsimp only [Qp]
    rw [rank_hermPosPart]
    exact hposQ
  have hQpcharge : 4 * rtrace Qp - 4 * (b : ℝ) ≤ frobSq Qp := by
    have h := rank_trace_ineq_two
      (P := (0 : Matrix (Fin N) (Fin N) 𝕜)) (Q := Qp)
      Matrix.PosSemidef.zero hQp_psd.isHermitian
      (r := 0) (b := b) (by simp) hposQp
    simpa [rtrace] using h
  linarith

/-- The same exact slack estimate with an arbitrary real upper bound for
`rtrace P`.  Keeping the rank budget `s` and the trace budget `traceCap`
separate is what makes finite normalization errors visible. -/
private lemma exact_stability_slack_traceCap {N s b : ℕ} {traceCap : ℝ}
    {P Q : Matrix (Fin N) (Fin N) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (htraceP : rtrace P ≤ traceCap) (hposQ : posIndex hQ ≤ b) :
    let Qm := hermNegPart hQ
    let R := P - Qm
    frobSq R - 2 * rtrace R + s
      ≤ frobSq (P + Q) - 4 * rtrace (P + Q) + s + 2 * traceCap + 4 * b := by
  dsimp only
  let Qp := hermPosPart hQ
  let Qm := hermNegPart hQ
  let R := P - Qm
  have hQdec : Q = Qp - Qm := by
    exact (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQmQp : Qm * Qp = 0 := hermNegPart_mul_hermPosPart hQ
  have hR : R.IsHermitian := hP.isHermitian.sub hQm_psd.isHermitian
  have hGR : P + Q = R + Qp := by
    rw [hQdec]
    dsimp only [R]
    abel
  have hRQp : R * Qp = P * Qp := by
    dsimp only [R]
    rw [sub_mul, hQmQp]
    simp
  have hfrob : frobSq (P + Q)
      = frobSq R + 2 * RCLike.re (P * Qp).trace + frobSq Qp := by
    rw [hGR, frobSq_add_hermitian hR hQp_psd.isHermitian, hRQp]
  have htraceR : rtrace R = rtrace P - rtrace Qm := by
    dsimp only [R]
    exact rtrace_sub P Qm
  have htraceG : rtrace (P + Q) = rtrace P + rtrace Qp - rtrace Qm := by
    rw [hGR, rtrace_add, htraceR]
    ring
  have hcross : 0 ≤ RCLike.re (P * Qp).trace :=
    trace_mul_nonneg_of_posSemidef hP hQp_psd
  have htraceQm : 0 ≤ rtrace Qm := by
    dsimp only [Qm]
    rw [rtrace_hermNegPart]
    exact Finset.sum_nonneg fun _ _ => negPart_nonneg _
  have hposQp : posIndex hQp_psd.isHermitian ≤ b := by
    rw [posIndex_eq_rank_of_posSemidef hQp_psd]
    dsimp only [Qp]
    rw [rank_hermPosPart]
    exact hposQ
  have hQpcharge : 4 * rtrace Qp - 4 * (b : ℝ) ≤ frobSq Qp := by
    have h := rank_trace_ineq_two
      (P := (0 : Matrix (Fin N) (Fin N) 𝕜)) (Q := Qp)
      Matrix.PosSemidef.zero hQp_psd.isHermitian
      (r := 0) (b := b) (by simp) hposQp
    simpa [rtrace] using h
  linarith

/-- The exact finite stability prebound before trace normalization, Frobenius
normalization, or the count inequality is applied.  This is the reusable form
of the stability argument when the matrix dimension and zero-count scale are
not definitionally equal. -/
theorem stability_prebound {N s b : ℕ} {traceCap : ℝ}
    {P Q : Matrix (Fin N) (Fin N) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hrank : P.rank ≤ s) (htraceP : rtrace P ≤ traceCap)
    (hposQ : posIndex hQ ≤ b) :
    tailExcessSq (hP.isHermitian.add hQ) b
      ≤ frobSq (P + Q) - 4 * rtrace (P + Q) + s + 2 * traceCap + 4 * b := by
  let Qp := hermPosPart hQ
  let Qm := hermNegPart hQ
  let R := P - Qm
  have hQdec : Q = Qp - Qm := by
    exact (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hR : R.IsHermitian := hP.isHermitian.sub hQm_psd.isHermitian
  have hGR : P + Q = R + Qp := by
    rw [hQdec]
    dsimp only [R]
    abel
  have hrankQp : Qp.rank ≤ b := by
    dsimp only [Qp]
    rw [rank_hermPosPart]
    exact hposQ
  have htail0 := tailExcessSq_add_psd_le_full hR hQp_psd hrankQp
  have htail : tailExcessSq (hP.isHermitian.add hQ) b ≤ fullExcessSq hR := by
    calc
      tailExcessSq (hP.isHermitian.add hQ) b
          = tailExcessSq (hR.add hQp_psd.isHermitian) b :=
            tailExcessSq_congr hGR (hP.isHermitian.add hQ)
              (hR.add hQp_psd.isHermitian) b
      _ ≤ fullExcessSq hR := htail0
  have hposR : posIndex hR ≤ s :=
    (posIndex_sub_le_rank hP hQm_psd).trans hrank
  have hfull := fullExcessSq_le hR hposR
  have hslack := exact_stability_slack_traceCap (s := s) hP hQ htraceP hposQ
  exact htail.trans (hfull.trans hslack)

/-- **Quartic stability inequality.**  Under the accepted zero-side decomposition
`G = P + Q`, the positive excess remaining after `b` free directions is bounded by
`s - (2-D)N`.  This is equation (4) of the audited proof. -/
theorem stability_inequality {N s b : ℕ} {D : ℝ}
    {P Q : Matrix (Fin N) (Fin N) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hrank : P.rank ≤ s) (htraceP : rtrace P ≤ s)
    (hposQ : posIndex hQ ≤ b) (hcount : s + 2 * b ≤ N)
    (htraceG : rtrace (P + Q) = N)
    (hfrobG : frobSq (P + Q) ≤ D * N) :
    tailExcessSq (hP.isHermitian.add hQ) b
      ≤ (s : ℝ) - (2 - D) * N := by
  let Qp := hermPosPart hQ
  let Qm := hermNegPart hQ
  let R := P - Qm
  have hQdec : Q = Qp - Qm := by
    exact (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hR : R.IsHermitian := hP.isHermitian.sub hQm_psd.isHermitian
  have hGR : P + Q = R + Qp := by
    rw [hQdec]
    dsimp only [R]
    abel
  have hrankQp : Qp.rank ≤ b := by
    dsimp only [Qp]
    rw [rank_hermPosPart]
    exact hposQ
  have htail0 := tailExcessSq_add_psd_le_full hR hQp_psd hrankQp
  have htail : tailExcessSq (hP.isHermitian.add hQ) b ≤ fullExcessSq hR := by
    calc
      tailExcessSq (hP.isHermitian.add hQ) b
          = tailExcessSq (hR.add hQp_psd.isHermitian) b :=
            tailExcessSq_congr hGR (hP.isHermitian.add hQ)
              (hR.add hQp_psd.isHermitian) b
      _ ≤ fullExcessSq hR := htail0
  have hposR : posIndex hR ≤ s :=
    (posIndex_sub_le_rank hP hQm_psd).trans hrank
  have hfull := fullExcessSq_le hR hposR
  have hslack := exact_stability_slack hP hQ htraceP hposQ
  have hpre : tailExcessSq (hP.isHermitian.add hQ) b
      ≤ frobSq (P + Q) - 4 * rtrace (P + Q) + 3 * s + 4 * b :=
    htail.trans (hfull.trans hslack)
  have hcount' : (s : ℝ) + 2 * b ≤ N := by exact_mod_cast hcount
  calc
    tailExcessSq (hP.isHermitian.add hQ) b
        ≤ frobSq (P + Q) - 4 * rtrace (P + Q) + 3 * s + 4 * b := hpre
    _ ≤ (s : ℝ) - (2 - D) * N := by
      rw [htraceG]
      nlinarith

/-! ## Isometric and principal compressions -/

/-- Thresholded hard Sylvester: a subspace on which the Hermitian form is
strictly larger than `theta * ||x||^2` has dimension at most the number of
eigenvalues above `theta`. -/
private theorem finrank_le_posIndexAbove_of_gtOn {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) (θ : ℝ)
    {W : Submodule 𝕜 (Fin N → 𝕜)}
    (hW : ∀ x ∈ W, x ≠ 0 → θ * ∑ i, ‖x i‖ ^ 2 < hermForm A x) :
    Module.finrank 𝕜 W ≤ posIndexAbove hA θ := by
  let S : Matrix (Fin N) (Fin N) 𝕜 := specMap hA (fun t => (t - θ)⁺)
  let L : (Fin N → 𝕜) →ₗ[𝕜] (Fin N → 𝕜) := S.mulVecLin
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxS : S *ᵥ x = 0 := hxL
    simp only [Submodule.mem_bot]
    by_contra hne
    have hxne : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hformS : hermForm S x = 0 := by
      unfold hermForm
      rw [hxS]
      simp
    have hle := hermForm_le_of_truncForm_eq_zero hA θ x (by simpa [S] using hformS)
    exact (not_lt_of_ge hle) (hW x hxW hxne)
  have hrankS : S.rank = posIndexAbove hA θ := by
    dsimp only [S]
    change Module.finrank 𝕜
      (LinearMap.range (specMap hA (fun t => (t - θ)⁺)).mulVecLin) = _
    exact finrank_range_truncPos hA θ
  calc
    Module.finrank 𝕜 W
        = Module.finrank 𝕜 (LinearMap.range (L.domRestrict W)) :=
          (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank 𝕜 (LinearMap.range L) := by
        apply Submodule.finrank_mono
        rintro y ⟨⟨x, hxW⟩, rfl⟩
        exact ⟨x, rfl⟩
    _ = S.rank := rfl
    _ = posIndexAbove hA θ := hrankS

/-- An isometric compression cannot increase the number of eigenvalues above
any fixed threshold. -/
private theorem posIndexAbove_isometricCompression_le {M N : ℕ}
    {G : Matrix (Fin N) (Fin N) 𝕜} (hG : G.IsHermitian)
    (B : Matrix (Fin N) (Fin M) 𝕜) (hB : Bᴴ * B = 1) (θ : ℝ) :
    posIndexAbove (isHermitian_conjTranspose_mul_mul B hG) θ ≤ posIndexAbove hG θ := by
  let C : Matrix (Fin M) (Fin M) 𝕜 := Bᴴ * G * B
  let hC : C.IsHermitian := isHermitian_conjTranspose_mul_mul B hG
  let W : Submodule 𝕜 (Fin M → 𝕜) :=
    LinearMap.range (specMap hC (fun t => (t - θ)⁺)).mulVecLin
  let LB : (Fin M → 𝕜) →ₗ[𝕜] (Fin N → 𝕜) := B.mulVecLin
  have hBinj : Function.Injective LB := by
    intro x y hxy
    change B *ᵥ x = B *ᵥ y at hxy
    have hxy' : (Bᴴ * B) *ᵥ x = (Bᴴ * B) *ᵥ y := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
    rwa [hB, one_mulVec, one_mulVec] at hxy'
  have hBinjW : Function.Injective (LB.domRestrict W) := by
    intro x y hxy
    apply Subtype.ext
    exact hBinj hxy
  let V : Submodule 𝕜 (Fin N → 𝕜) := LinearMap.range (LB.domRestrict W)
  have hdimW : Module.finrank 𝕜 W = posIndexAbove hC θ := by
    dsimp only [W]
    exact finrank_range_truncPos hC θ
  have hdimV : Module.finrank 𝕜 V = Module.finrank 𝕜 W := by
    dsimp only [V]
    exact LinearMap.finrank_range_of_inj hBinjW
  have hVgt : ∀ y ∈ V, y ≠ 0 →
      θ * ∑ i, ‖y i‖ ^ 2 < hermForm G y := by
    rintro _ ⟨⟨x, hxW⟩, rfl⟩ hyne
    have hxne : x ≠ 0 := by
      intro hx
      subst x
      simp at hyne
    have hgtC := hermForm_gt_on_range_truncPos hC θ x hxW hxne
    have hform : hermForm C x = hermForm G (B *ᵥ x) := by
      dsimp only [C]
      exact hermForm_conj G B x
    have hnorm : (∑ i, ‖(B *ᵥ x) i‖ ^ 2) = ∑ i, ‖x i‖ ^ 2 := by
      calc
        (∑ i, ‖(B *ᵥ x) i‖ ^ 2) =
            hermForm (1 : Matrix (Fin N) (Fin N) 𝕜) (B *ᵥ x) :=
          (hermForm_one (B *ᵥ x)).symm
        _ = hermForm (Bᴴ * (1 : Matrix (Fin N) (Fin N) 𝕜) * B) x :=
          (hermForm_conj (1 : Matrix (Fin N) (Fin N) 𝕜) B x).symm
        _ = hermForm (1 : Matrix (Fin M) (Fin M) 𝕜) x := by simp [hB]
        _ = ∑ i, ‖x i‖ ^ 2 := hermForm_one x
    rw [hform] at hgtC
    change θ * ∑ i, ‖(B *ᵥ x) i‖ ^ 2 < hermForm G (B *ᵥ x)
    rw [hnorm]
    exact hgtC
  calc
    posIndexAbove (isHermitian_conjTranspose_mul_mul B hG) θ
        = Module.finrank 𝕜 W := hdimW.symm
    _ = Module.finrank 𝕜 V := hdimV.symm
    _ ≤ posIndexAbove hG θ := finrank_le_posIndexAbove_of_gtOn hG θ hVgt

/-- Cast an index through an inequality of ambient dimensions. -/
private def castIndex {M N : ℕ} (hMN : M ≤ N) (i : Fin M) : Fin N :=
  ⟨i, lt_of_lt_of_le i.isLt hMN⟩

@[simp] private lemma castIndex_val {M N : ℕ} (hMN : M ≤ N) (i : Fin M) :
    (castIndex hMN i).val = i := rfl

/-- Cauchy interlacing for an isometric compression, derived from threshold counts. -/
private theorem eigenvalues₀_isometricCompression_le {M N : ℕ}
    {G : Matrix (Fin N) (Fin N) 𝕜} (hG : G.IsHermitian)
    (B : Matrix (Fin N) (Fin M) 𝕜) (hB : Bᴴ * B = 1)
    (hMN : Fintype.card (Fin M) ≤ Fintype.card (Fin N))
    (i : Fin (Fintype.card (Fin M))) :
    (isHermitian_conjTranspose_mul_mul B hG).eigenvalues₀ i
      ≤ hG.eigenvalues₀ (castIndex hMN i) := by
  let hC : (Bᴴ * G * B).IsHermitian := isHermitian_conjTranspose_mul_mul B hG
  let ig : Fin (Fintype.card (Fin N)) := castIndex hMN i
  let θ : ℝ := hG.eigenvalues₀ ig
  let sc : Finset (Fin (Fintype.card (Fin M))) := {j | θ < hC.eigenvalues₀ j}
  let sg : Finset (Fin (Fintype.card (Fin N))) := {j | θ < hG.eigenvalues₀ j}
  have hcount : #sc ≤ #sg := by
    have h := posIndexAbove_isometricCompression_le hG B hB θ
    simpa only [sc, sg, posIndexAbove, hC, θ,
      card_eigenvalues_reindex hC (fun x => θ < x),
      card_eigenvalues_reindex hG (fun x => θ < x)] using h
  by_contra hnot
  have hlt : θ < hC.eigenvalues₀ i := lt_of_not_ge hnot
  have hlow : Finset.Iic i ⊆ sc := by
    intro j hj
    simp only [sc, mem_filter, mem_univ, true_and]
    exact lt_of_lt_of_le hlt (hC.eigenvalues₀_antitone (Finset.mem_Iic.mp hj))
  have hupp : sg ⊆ Finset.Iio ig := by
    intro j hj
    have hj' : θ < hG.eigenvalues₀ j := by
      simpa only [sg, mem_filter, mem_univ, true_and] using hj
    apply Finset.mem_Iio.mpr
    by_contra hnj
    have hig : ig ≤ j := not_lt.mp hnj
    have := hG.eigenvalues₀_antitone hig
    dsimp only [θ] at hj'
    linarith
  have hbad : i.val + 1 ≤ i.val := calc
    i.val + 1 = #(Finset.Iic i) := by simp
    _ ≤ #sc := Finset.card_le_card hlow
    _ ≤ #sg := hcount
    _ ≤ #(Finset.Iio ig) := Finset.card_le_card hupp
    _ = i.val := by simp [ig, castIndex]
  omega

private def tailCastEmbedding {M N : ℕ} (hMN : M ≤ N) (b : ℕ) :
    Fin (M - b) ↪ Fin (N - b) where
  toFun j := ⟨j, lt_of_lt_of_le j.isLt (Nat.sub_le_sub_right hMN b)⟩
  inj' := by
    intro i j h
    refine Fin.ext ?_
    simpa using congrArg (fun x : Fin (N - b) => x.val) h

/-- The sorted tail energy is monotone under every isometric compression. -/
theorem tailExcessSq_isometricCompression_le {M N b : ℕ}
    {G : Matrix (Fin N) (Fin N) 𝕜} (hG : G.IsHermitian)
    (B : Matrix (Fin N) (Fin M) 𝕜) (hB : Bᴴ * B = 1) :
    tailExcessSq (isHermitian_conjTranspose_mul_mul B hG) b
      ≤ tailExcessSq hG b := by
  let LB : (Fin M → 𝕜) →ₗ[𝕜] (Fin N → 𝕜) := B.mulVecLin
  have hBinj : Function.Injective LB := by
    intro x y hxy
    change B *ᵥ x = B *ᵥ y at hxy
    have hxy' : (Bᴴ * B) *ᵥ x = (Bᴴ * B) *ᵥ y := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
    rwa [hB, one_mulVec, one_mulVec] at hxy'
  have hMN : Fintype.card (Fin M) ≤ Fintype.card (Fin N) := by
    have hdim := LinearMap.finrank_le_finrank_of_injective hBinj
    simpa using hdim
  let e : Fin (Fintype.card (Fin M) - b) ↪ Fin (Fintype.card (Fin N) - b) :=
    tailCastEmbedding hMN b
  have hpoint : ∀ j : Fin (Fintype.card (Fin M) - b),
      (((isHermitian_conjTranspose_mul_mul B hG).eigenvalues₀
          (tailIndex (Fintype.card (Fin M)) b j) - 1)⁺) ^ 2
        ≤ ((hG.eigenvalues₀
          (tailIndex (Fintype.card (Fin N)) b (e j)) - 1)⁺) ^ 2 := by
    intro j
    apply excessSq_mono
    have h := eigenvalues₀_isometricCompression_le hG B hB hMN
      (tailIndex (Fintype.card (Fin M)) b j)
    have hind :
        tailIndex (Fintype.card (Fin N)) b (e j) =
          castIndex hMN (tailIndex (Fintype.card (Fin M)) b j) := by
      apply Fin.ext
      rfl
    rw [hind]
    exact h
  calc
    tailExcessSq (isHermitian_conjTranspose_mul_mul B hG) b
        ≤ ∑ j : Fin (Fintype.card (Fin M) - b),
            ((hG.eigenvalues₀
              (tailIndex (Fintype.card (Fin N)) b (e j)) - 1)⁺) ^ 2 := by
          exact Finset.sum_le_sum fun j _ => hpoint j
    _ = ∑ j ∈ Finset.univ.map e,
          ((hG.eigenvalues₀
            (tailIndex (Fintype.card (Fin N)) b j) - 1)⁺) ^ 2 := by
          rw [Finset.sum_map]
    _ ≤ ∑ j : Fin (Fintype.card (Fin N) - b),
          ((hG.eigenvalues₀
            (tailIndex (Fintype.card (Fin N)) b j) - 1)⁺) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
    _ = tailExcessSq hG b := rfl

/-- The coordinate isometry associated with a principal submatrix. -/
private def principalEmbeddingMatrix {M N : ℕ} (e : Fin M ↪ Fin N) :
    Matrix (Fin N) (Fin M) 𝕜 :=
  (1 : Matrix (Fin N) (Fin N) 𝕜).submatrix id e

private lemma principalEmbeddingMatrix_star_mul_self {M N : ℕ}
    (e : Fin M ↪ Fin N) :
    (principalEmbeddingMatrix (𝕜 := 𝕜) e)ᴴ * principalEmbeddingMatrix (𝕜 := 𝕜) e = 1 := by
  ext i j
  simp [principalEmbeddingMatrix, Matrix.mul_apply, Matrix.one_apply]

private lemma principalEmbeddingMatrix_compression {M N : ℕ}
    (G : Matrix (Fin N) (Fin N) 𝕜) (e : Fin M ↪ Fin N) :
    (principalEmbeddingMatrix (𝕜 := 𝕜) e)ᴴ * G * principalEmbeddingMatrix (𝕜 := 𝕜) e
      = G.submatrix e e := by
  ext i j
  simp [principalEmbeddingMatrix, Matrix.mul_apply, Matrix.one_apply]

/-- Cauchy interlacing transfers the tail-energy bound to every principal compression. -/
theorem tailExcessSq_principalCompression_le {M N b : ℕ}
    {G : Matrix (Fin N) (Fin N) 𝕜} (hG : G.IsHermitian)
    (e : Fin M ↪ Fin N) :
    tailExcessSq (hG.submatrix e) b ≤ tailExcessSq hG b := by
  let B := principalEmbeddingMatrix (𝕜 := 𝕜) e
  have hB : Bᴴ * B = 1 := principalEmbeddingMatrix_star_mul_self e
  have hcomp : Bᴴ * G * B = G.submatrix e e :=
    principalEmbeddingMatrix_compression G e
  have h := tailExcessSq_isometricCompression_le hG B hB (b := b)
  calc
    tailExcessSq (hG.submatrix e) b
        = tailExcessSq (isHermitian_conjTranspose_mul_mul B hG) b :=
          (tailExcessSq_congr hcomp (isHermitian_conjTranspose_mul_mul B hG)
            (hG.submatrix e) b).symm
    _ ≤ tailExcessSq hG b := h

/-- Stability for an arbitrary isometric compression of `P + Q`. -/
theorem stability_inequality_isometricCompression {M N s b : ℕ} {D : ℝ}
    {P Q : Matrix (Fin N) (Fin N) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (B : Matrix (Fin N) (Fin M) 𝕜) (hB : Bᴴ * B = 1)
    (hrank : P.rank ≤ s) (htraceP : rtrace P ≤ s)
    (hposQ : posIndex hQ ≤ b) (hcount : s + 2 * b ≤ N)
    (htraceG : rtrace (P + Q) = N)
    (hfrobG : frobSq (P + Q) ≤ D * N) :
    tailExcessSq (isHermitian_conjTranspose_mul_mul B (hP.isHermitian.add hQ)) b
      ≤ (s : ℝ) - (2 - D) * N :=
  (tailExcessSq_isometricCompression_le (hP.isHermitian.add hQ) B hB).trans
    (stability_inequality hP hQ hrank htraceP hposQ hcount htraceG hfrobG)

/-- Stability for every principal compression of `P + Q`, equation (5) of the audit. -/
theorem stability_inequality_principalCompression {M N s b : ℕ} {D : ℝ}
    {P Q : Matrix (Fin N) (Fin N) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (e : Fin M ↪ Fin N)
    (hrank : P.rank ≤ s) (htraceP : rtrace P ≤ s)
    (hposQ : posIndex hQ ≤ b) (hcount : s + 2 * b ≤ N)
    (htraceG : rtrace (P + Q) = N)
    (hfrobG : frobSq (P + Q) ≤ D * N) :
    tailExcessSq ((hP.isHermitian.add hQ).submatrix e) b
      ≤ (s : ℝ) - (2 - D) * N :=
  (tailExcessSq_principalCompression_le (hP.isHermitian.add hQ) e).trans
    (stability_inequality hP hQ hrank htraceP hposQ hcount htraceG hfrobG)

end Zeta85
end RH

end
