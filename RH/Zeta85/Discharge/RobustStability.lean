/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Stability
import RH.Zeta85.Discharge.TrimmedMoment

/-!
# Finite robust stability and spectral-law normalization

This file keeps three quantities distinct:

* `d`, the ambient matrix dimension;
* `zeroScale`, the real zero-count normalization scale;
* `s` and `b`, the two finite rank budgets.

Starting from `stability_prebound`, trace, `P`-trace, and Frobenius errors
enter with exact coefficients `4`, `2`, and `1`, respectively.  The last
section constructs the uniform centered eigenvalue law and its finite trim.
It makes no limiting or moment-identification assertion.
-/

open Matrix Finset
open scoped BigOperators ComplexOrder

noncomputable section

namespace RH
namespace Zeta85
namespace RobustStability

open RHLinalg
open TrimmedMoment

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## 1. Exact error accounting -/

/-- The algebraic identity behind the robust coefficients.  The final term
is nonpositive under `s + 2b ≤ zeroScale`. -/
theorem error_accounting_identity (s b : ℕ)
    (zeroScale D pTraceErr traceErr frobErr : ℝ) :
    D * zeroScale + frobErr - 4 * (zeroScale - traceErr) + s +
        2 * ((s : ℝ) + pTraceErr) + 4 * b =
      (s : ℝ) - (2 - D) * zeroScale + 2 * pTraceErr +
        4 * traceErr + frobErr +
        2 * ((s : ℝ) + 2 * b - zeroScale) := by
  ring

/-- Robust finite stability with the one-sided trace estimate actually used
by the proof.  No sign assumptions on the three error variables are needed:
their defining upper/lower bounds are the complete hypotheses. -/
theorem robust_stability_inequality_oneSided {d s b : ℕ}
    {zeroScale D pTraceErr traceErr frobErr : ℝ}
    {P Q : Matrix (Fin d) (Fin d) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hrank : P.rank ≤ s)
    (htraceP : rtrace P ≤ (s : ℝ) + pTraceErr)
    (hposQ : posIndex hQ ≤ b)
    (hcount : (s : ℝ) + 2 * b ≤ zeroScale)
    (htraceG : zeroScale - traceErr ≤ rtrace (P + Q))
    (hfrobG : frobSq (P + Q) ≤ D * zeroScale + frobErr) :
    tailExcessSq (hP.isHermitian.add hQ) b ≤
      (s : ℝ) - (2 - D) * zeroScale + 2 * pTraceErr +
        4 * traceErr + frobErr := by
  have hpre := stability_prebound hP hQ hrank htraceP hposQ
  calc
    tailExcessSq (hP.isHermitian.add hQ) b
        ≤ frobSq (P + Q) - 4 * rtrace (P + Q) + s +
            2 * ((s : ℝ) + pTraceErr) + 4 * b := hpre
    _ ≤ (s : ℝ) - (2 - D) * zeroScale + 2 * pTraceErr +
          4 * traceErr + frobErr := by
      linarith

/-- Symmetric trace-error form of `robust_stability_inequality_oneSided`. -/
theorem robust_stability_inequality {d s b : ℕ}
    {zeroScale D pTraceErr traceErr frobErr : ℝ}
    {P Q : Matrix (Fin d) (Fin d) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hrank : P.rank ≤ s)
    (htraceP : rtrace P ≤ (s : ℝ) + pTraceErr)
    (hposQ : posIndex hQ ≤ b)
    (hcount : (s : ℝ) + 2 * b ≤ zeroScale)
    (htraceG : |rtrace (P + Q) - zeroScale| ≤ traceErr)
    (hfrobG : frobSq (P + Q) ≤ D * zeroScale + frobErr) :
    tailExcessSq (hP.isHermitian.add hQ) b ≤
      (s : ℝ) - (2 - D) * zeroScale + 2 * pTraceErr +
        4 * traceErr + frobErr := by
  have htraceLower : zeroScale - traceErr ≤ rtrace (P + Q) := by
    have hneg := (abs_le.mp htraceG).1
    linarith
  exact robust_stability_inequality_oneSided hP hQ hrank htraceP hposQ
    hcount htraceLower hfrobG

/-! ## 2. Isometric and principal compressions -/

/-- The robust bound survives every isometric compression. -/
theorem robust_stability_inequality_isometricCompression_oneSided
    {m d s b : ℕ} {zeroScale D pTraceErr traceErr frobErr : ℝ}
    {P Q : Matrix (Fin d) (Fin d) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (B : Matrix (Fin d) (Fin m) 𝕜) (hB : Bᴴ * B = 1)
    (hrank : P.rank ≤ s)
    (htraceP : rtrace P ≤ (s : ℝ) + pTraceErr)
    (hposQ : posIndex hQ ≤ b)
    (hcount : (s : ℝ) + 2 * b ≤ zeroScale)
    (htraceG : zeroScale - traceErr ≤ rtrace (P + Q))
    (hfrobG : frobSq (P + Q) ≤ D * zeroScale + frobErr) :
    tailExcessSq
        (isHermitian_conjTranspose_mul_mul B (hP.isHermitian.add hQ)) b ≤
      (s : ℝ) - (2 - D) * zeroScale + 2 * pTraceErr +
        4 * traceErr + frobErr :=
  (tailExcessSq_isometricCompression_le (hP.isHermitian.add hQ) B hB).trans
    (robust_stability_inequality_oneSided hP hQ hrank htraceP hposQ
      hcount htraceG hfrobG)

/-- Symmetric trace-error form for isometric compressions. -/
theorem robust_stability_inequality_isometricCompression
    {m d s b : ℕ} {zeroScale D pTraceErr traceErr frobErr : ℝ}
    {P Q : Matrix (Fin d) (Fin d) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (B : Matrix (Fin d) (Fin m) 𝕜) (hB : Bᴴ * B = 1)
    (hrank : P.rank ≤ s)
    (htraceP : rtrace P ≤ (s : ℝ) + pTraceErr)
    (hposQ : posIndex hQ ≤ b)
    (hcount : (s : ℝ) + 2 * b ≤ zeroScale)
    (htraceG : |rtrace (P + Q) - zeroScale| ≤ traceErr)
    (hfrobG : frobSq (P + Q) ≤ D * zeroScale + frobErr) :
    tailExcessSq
        (isHermitian_conjTranspose_mul_mul B (hP.isHermitian.add hQ)) b ≤
      (s : ℝ) - (2 - D) * zeroScale + 2 * pTraceErr +
        4 * traceErr + frobErr := by
  have htraceLower : zeroScale - traceErr ≤ rtrace (P + Q) := by
    have hneg := (abs_le.mp htraceG).1
    linarith
  exact robust_stability_inequality_isometricCompression_oneSided
    hP hQ B hB hrank htraceP hposQ hcount htraceLower hfrobG

/-- The robust bound survives every principal compression. -/
theorem robust_stability_inequality_principalCompression_oneSided
    {m d s b : ℕ} {zeroScale D pTraceErr traceErr frobErr : ℝ}
    {P Q : Matrix (Fin d) (Fin d) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (e : Fin m ↪ Fin d)
    (hrank : P.rank ≤ s)
    (htraceP : rtrace P ≤ (s : ℝ) + pTraceErr)
    (hposQ : posIndex hQ ≤ b)
    (hcount : (s : ℝ) + 2 * b ≤ zeroScale)
    (htraceG : zeroScale - traceErr ≤ rtrace (P + Q))
    (hfrobG : frobSq (P + Q) ≤ D * zeroScale + frobErr) :
    tailExcessSq ((hP.isHermitian.add hQ).submatrix e) b ≤
      (s : ℝ) - (2 - D) * zeroScale + 2 * pTraceErr +
        4 * traceErr + frobErr :=
  (tailExcessSq_principalCompression_le (hP.isHermitian.add hQ) e).trans
    (robust_stability_inequality_oneSided hP hQ hrank htraceP hposQ
      hcount htraceG hfrobG)

/-- Symmetric trace-error form for principal compressions. -/
theorem robust_stability_inequality_principalCompression
    {m d s b : ℕ} {zeroScale D pTraceErr traceErr frobErr : ℝ}
    {P Q : Matrix (Fin d) (Fin d) 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (e : Fin m ↪ Fin d)
    (hrank : P.rank ≤ s)
    (htraceP : rtrace P ≤ (s : ℝ) + pTraceErr)
    (hposQ : posIndex hQ ≤ b)
    (hcount : (s : ℝ) + 2 * b ≤ zeroScale)
    (htraceG : |rtrace (P + Q) - zeroScale| ≤ traceErr)
    (hfrobG : frobSq (P + Q) ≤ D * zeroScale + frobErr) :
    tailExcessSq ((hP.isHermitian.add hQ).submatrix e) b ≤
      (s : ℝ) - (2 - D) * zeroScale + 2 * pTraceErr +
        4 * traceErr + frobErr := by
  have htraceLower : zeroScale - traceErr ≤ rtrace (P + Q) := by
    have hneg := (abs_le.mp htraceG).1
    linarith
  exact robust_stability_inequality_principalCompression_oneSided
    hP hQ e hrank htraceP hposQ hcount htraceLower hfrobG

/-! ## 3. Uniform finite laws and exact trimming -/

/-- Uniform probability weight on a nonempty finite type. -/
def uniformWeight (ι : Type*) [Fintype ι] : ι → ℝ :=
  fun _ => 1 / Fintype.card ι

/-- The uniform submeasure removed on a finite set. -/
def uniformRemoved {ι : Type*} [Fintype ι] [DecidableEq ι]
    (removedSet : Finset ι) : ι → ℝ :=
  fun i => if i ∈ removedSet then uniformWeight ι i else 0

/-- Exact normalized moment of a finite scalar law. -/
def normalizedMoment {ι : Type*} [Fintype ι]
    (value : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i, uniformWeight ι i * value i ^ k

/-- Exact mass of a uniformly weighted removed set. -/
def uniformRemovedFraction {ι : Type*} [Fintype ι]
    (removedSet : Finset ι) : ℝ :=
  (#removedSet : ℝ) / Fintype.card ι

/-- A nonempty finite scalar law with a uniform finite trim supplies every
field of `TrimmedMomentInputs`, with no measure-theoretic limit hidden. -/
theorem uniform_trimmedMomentInputs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ) (removedSet : Finset ι)
    (hcard : 0 < Fintype.card ι) :
    TrimmedMomentInputs value (uniformWeight ι) (uniformRemoved removedSet)
      (normalizedMoment value 1) (normalizedMoment value 2)
      (normalizedMoment value 3) (normalizedMoment value 4)
      (uniformRemovedFraction removedSet) := by
  constructor
  · intro i
    simp only [uniformWeight]
    positivity
  · intro i
    by_cases hi : i ∈ removedSet <;>
      simp [uniformRemoved, hi, uniformWeight]
  · intro i
    by_cases hi : i ∈ removedSet <;>
      simp [uniformRemoved, hi, uniformWeight]
  · simp only [uniformRemoved, uniformRemovedFraction]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp [uniformWeight, div_eq_mul_inv]
  · simp [uniformWeight]
    field_simp
  · simp [normalizedMoment]
  · rfl
  · rfl
  · rfl

/-- Enlarging only the declared trim budget preserves the finite inputs. -/
theorem trimmedMomentInputs_mono_alpha {ι : Type*} [Fintype ι]
    {value weight removed : ι → ℝ} {m1 m2 m3 m4 alpha beta : ℝ}
    (h : TrimmedMomentInputs value weight removed m1 m2 m3 m4 alpha)
    (halpha : alpha ≤ beta) :
    TrimmedMomentInputs value weight removed m1 m2 m3 m4 beta where
  weight_nonneg := h.weight_nonneg
  removed_nonneg := h.removed_nonneg
  removed_le_weight := h.removed_le_weight
  removed_mass_le := h.removed_mass_le.trans halpha
  mass_one := h.mass_one
  moment_one := h.moment_one
  moment_two := h.moment_two
  moment_three := h.moment_three
  moment_four := h.moment_four

/-- For a uniform trim, the residual is exactly the normalized positive-square
sum over the unremoved finite set. -/
theorem residualTail_uniformRemoved {ι : Type*} [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ) (removedSet : Finset ι) :
    residualTail value (uniformWeight ι) (uniformRemoved removedSet) =
      (1 / Fintype.card ι : ℝ) *
        ∑ i ∈ Finset.univ \ removedSet, (max (value i) 0) ^ 2 := by
  classical
  unfold residualTail
  calc
    (∑ i, (uniformWeight ι i - uniformRemoved removedSet i) *
        (max (value i) 0) ^ 2) =
        ∑ i, if i ∉ removedSet then
          uniformWeight ι i * (max (value i) 0) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ removedSet <;>
        simp [uniformRemoved, hi]
    _ = ∑ i ∈ Finset.univ \ removedSet,
          uniformWeight ι i * (max (value i) 0) ^ 2 := by
      calc
        (∑ i, if i ∉ removedSet then
            uniformWeight ι i * (max (value i) 0) ^ 2 else 0) =
            ∑ i ∈ Finset.univ with i ∉ removedSet,
              uniformWeight ι i * (max (value i) 0) ^ 2 :=
          (Finset.sum_filter (s := Finset.univ) (fun i => i ∉ removedSet)
            (fun i => uniformWeight ι i * (max (value i) 0) ^ 2)).symm
        _ = ∑ i ∈ Finset.univ \ removedSet,
              uniformWeight ι i * (max (value i) 0) ^ 2 := by
          congr 1
          ext i
          simp
    _ = (1 / Fintype.card ι : ℝ) *
          ∑ i ∈ Finset.univ \ removedSet, (max (value i) 0) ^ 2 := by
      simp only [uniformWeight, Finset.mul_sum]

/-- Embedding of the eigenvalue indices retained after deleting the first
`b` decreasingly ordered eigenvalues. -/
def spectralTailEmbedding (d b : ℕ) : Fin (d - b) ↪ Fin d where
  toFun := tailIndex d b
  inj' := by
    intro i j hij
    apply Fin.ext
    simpa using congrArg Fin.val hij

/-- Indices retained by the sorted tail. -/
def spectralTailSet (d b : ℕ) : Finset (Fin d) :=
  Finset.univ.map (spectralTailEmbedding d b)

/-- Indices deleted by the sorted tail. -/
def spectralHeadSet (d b : ℕ) : Finset (Fin d) :=
  Finset.univ \ spectralTailSet d b

/-- The number of actually deleted indices is at most the declared budget
even when `b` exceeds the matrix dimension. -/
theorem card_spectralHeadSet_le (d b : ℕ) :
    #(spectralHeadSet d b) ≤ b := by
  simp only [spectralHeadSet, spectralTailSet, Finset.card_sdiff,
    Finset.inter_univ, Finset.card_univ, Fintype.card_fin, Finset.card_map]
  omega

/-- Hence the exact uniform deleted mass is at most `b / d`. -/
theorem uniformRemovedFraction_spectralHeadSet_le {d b : ℕ} (hd : 0 < d) :
    uniformRemovedFraction (spectralHeadSet d b) ≤ (b : ℝ) / d := by
  unfold uniformRemovedFraction
  have hcard : (#(spectralHeadSet d b) : ℝ) ≤ b := by
    exact_mod_cast card_spectralHeadSet_le d b
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simpa using (div_le_div_iff_of_pos_right hdR).mpr hcard

/-! ## 4. The centered eigenvalue law of a principal block -/

/-- The index type used by `IsHermitian.eigenvalues₀`. -/
abbrev SpectralIndex (d : ℕ) := Fin (Fintype.card (Fin d))

/-- Centered, decreasingly ordered eigenvalues of a Hermitian matrix. -/
def centeredSpectrum {d : ℕ} {G : Matrix (Fin d) (Fin d) 𝕜}
    (hG : G.IsHermitian) : SpectralIndex d → ℝ :=
  fun i => hG.eigenvalues₀ i - 1

/-- Exact normalized centered spectral moment. -/
def spectralMoment {d : ℕ} {G : Matrix (Fin d) (Fin d) 𝕜}
    (hG : G.IsHermitian) (k : ℕ) : ℝ :=
  normalizedMoment (centeredSpectrum hG) k

/-- The sorted-head trim of a finite Hermitian spectrum supplies the exact
moment inputs with declared trim budget `b / d`. -/
theorem spectral_headTrimmedMomentInputs {d b : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian) (hd : 0 < d) :
    TrimmedMomentInputs (centeredSpectrum hG) (uniformWeight (SpectralIndex d))
      (uniformRemoved (spectralHeadSet (Fintype.card (Fin d)) b))
      (spectralMoment hG 1) (spectralMoment hG 2)
      (spectralMoment hG 3) (spectralMoment hG 4) ((b : ℝ) / d) :=
  trimmedMomentInputs_mono_alpha
    (uniform_trimmedMomentInputs (centeredSpectrum hG)
      (spectralHeadSet (Fintype.card (Fin d)) b)
      (by simpa using hd))
    (by simpa using
      (uniformRemovedFraction_spectralHeadSet_le
        (b := b) (d := Fintype.card (Fin d)) (by simpa using hd)))

/-- For the sorted-head trim, the residual of the uniform centered spectral
law is exactly the matrix tail energy divided by the matrix dimension. -/
theorem spectral_residualTail_eq_tailExcessSq_div {d b : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian) :
    residualTail (centeredSpectrum hG) (uniformWeight (SpectralIndex d))
        (uniformRemoved (spectralHeadSet (Fintype.card (Fin d)) b)) =
      tailExcessSq hG b / d := by
  rw [residualTail_uniformRemoved]
  have hsets : Finset.univ \ spectralHeadSet (Fintype.card (Fin d)) b =
      spectralTailSet (Fintype.card (Fin d)) b := by
    simp [spectralHeadSet, spectralTailSet]
  rw [hsets]
  simp only [spectralTailSet, Finset.sum_map]
  unfold tailExcessSq centeredSpectrum
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  simp [SpectralIndex]

/-- A principal block and a finite set of its eigenvalue indices give an
explicit `TrimmedMomentInputs` object at their actual first four moments. -/
theorem principal_spectral_trimmedMomentInputs {m d : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian)
    (e : Fin m ↪ Fin d)
    (removedSet : Finset (SpectralIndex m)) (hm : 0 < m) :
    let hC := hG.submatrix e
    TrimmedMomentInputs (centeredSpectrum hC) (uniformWeight (SpectralIndex m))
      (uniformRemoved removedSet)
      (spectralMoment hC 1) (spectralMoment hC 2)
      (spectralMoment hC 3) (spectralMoment hC 4)
      (uniformRemovedFraction removedSet) := by
  dsimp only
  exact uniform_trimmedMomentInputs (centeredSpectrum (hG.submatrix e))
    removedSet (by simpa using hm)

/-- Specialization to deletion of the first `b` sorted eigenvalues of the
principal block.  Its declared removed mass is the explicit ratio `b / m`. -/
theorem principal_spectral_headTrimmedMomentInputs {m d b : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian)
    (e : Fin m ↪ Fin d) (hm : 0 < m) :
    let hC := hG.submatrix e
    TrimmedMomentInputs (centeredSpectrum hC) (uniformWeight (SpectralIndex m))
      (uniformRemoved (spectralHeadSet (Fintype.card (Fin m)) b))
      (spectralMoment hC 1) (spectralMoment hC 2)
      (spectralMoment hC 3) (spectralMoment hC 4) ((b : ℝ) / m) := by
  dsimp only
  exact spectral_headTrimmedMomentInputs (hG.submatrix e) hm

/-- The corresponding residual is exactly the principal block's sorted tail
energy divided by the block dimension. -/
theorem principal_spectral_residualTail_eq {m d b : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian)
    (e : Fin m ↪ Fin d) :
    residualTail (centeredSpectrum (hG.submatrix e))
        (uniformWeight (SpectralIndex m))
        (uniformRemoved (spectralHeadSet (Fintype.card (Fin m)) b)) =
      tailExcessSq (hG.submatrix e) b / m :=
  spectral_residualTail_eq_tailExcessSq_div (hG.submatrix e)

/-- The exact remaining interface for identifying a principal spectral law
with prescribed analytic moments: four finite equalities, and nothing else. -/
theorem principal_spectral_trimmedMomentInputs_of_moments {m d : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian)
    (e : Fin m ↪ Fin d)
    (removedSet : Finset (SpectralIndex m)) (hm : 0 < m)
    (m1 m2 m3 m4 : ℝ)
    (h1 : spectralMoment (hG.submatrix e) 1 = m1)
    (h2 : spectralMoment (hG.submatrix e) 2 = m2)
    (h3 : spectralMoment (hG.submatrix e) 3 = m3)
    (h4 : spectralMoment (hG.submatrix e) 4 = m4) :
    TrimmedMomentInputs
      (centeredSpectrum (hG.submatrix e)) (uniformWeight (SpectralIndex m))
      (uniformRemoved removedSet) m1 m2 m3 m4
      (uniformRemovedFraction removedSet) := by
  simpa only [h1, h2, h3, h4] using
    principal_spectral_trimmedMomentInputs hG e removedSet hm

/-- Precise finite signature still required to identify the sorted-head
principal spectral law with four prescribed analytic moments. -/
theorem principal_spectral_headTrimmedMomentInputs_of_moments {m d b : ℕ}
    {G : Matrix (Fin d) (Fin d) 𝕜} (hG : G.IsHermitian)
    (e : Fin m ↪ Fin d) (hm : 0 < m) (m1 m2 m3 m4 : ℝ)
    (h1 : spectralMoment (hG.submatrix e) 1 = m1)
    (h2 : spectralMoment (hG.submatrix e) 2 = m2)
    (h3 : spectralMoment (hG.submatrix e) 3 = m3)
    (h4 : spectralMoment (hG.submatrix e) 4 = m4) :
    TrimmedMomentInputs (centeredSpectrum (hG.submatrix e))
      (uniformWeight (SpectralIndex m))
      (uniformRemoved (spectralHeadSet (Fintype.card (Fin m)) b))
      m1 m2 m3 m4 ((b : ℝ) / m) := by
  simpa only [h1, h2, h3, h4] using
    principal_spectral_headTrimmedMomentInputs (b := b) hG e hm

end RobustStability
end Zeta85
end RH

end
