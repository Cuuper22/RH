/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Certificate.lean — **Phase A2/A3**: the exact rational certificate at support 143/100 and
the count lemma of the zero-side linear program.

A2, from `docs/run/01_certificate_cycle1.md` (10)–(12):

  c_pc      := λ·A²/(B + λ·J)   = 2227707598259143/2561811364469143  (= 0.8695829947…),
  c_pc      > 20/23,
  2 − 1/c_pc = 1893603832049143/2227707598259143  (= 0.8500235101…),
  (2 − 1/c_pc) − 17/20 = 1047470577429/44554151965182860 > 0.

`D_pc := 1/c_pc = 2561811364469143/2227707598259143 = 1.1499764899…` is the normalized Frobenius
cost that `RH/Zeta85/Hypotheses.lean` assumes on the prime side, and `2 − D_pc` is the certified
proportion.

A3, from `docs/run/01_hybrid_cycle1.md` §1, equations (1)–(3): for reals `s, d, p ≥ 0` and a real `C`,

  s + 2d + 2p ≤ N   and   3s + 4d + 4p ≥ (4 − C)·N   ⟹   s ≥ (2 − C)·N,

together with its specialization at `C = 23/20 − η`.

Everything in this file is PROVED (`norm_num` / `linarith`); no axioms and no `sorry`.
-/
import RH.Zeta85.Window

noncomputable section

namespace RH
namespace Zeta85

/-! ## 1. The certificate constant -/

/-- `c_pc = λ·A²/(B + λ·J)`  [01_certificate_cycle1.md (5), (10)], with `A`, `B`, `J` the three
moments proved in `Window.lean`. -/
def cPC : ℝ :=
  lam * (∫ s in (-(1:ℝ)/2)..(1/2), vProf s) ^ 2
    / ((∫ s in (-(1:ℝ)/2)..(1/2), vProf s ^ 2) + lam * jSat)

/-- **A2, first identity**: `c_pc = 2227707598259143/2561811364469143`
[01_certificate_cycle1.md (10)]. -/
theorem cPC_eq : cPC = 2227707598259143 / 2561811364469143 := by
  rw [cPC, integral_vProf, integral_vProf_sq, jSat_eq, lam]
  norm_num

/-- The normalized Frobenius cost `D_pc = 1/c_pc = 2561811364469143/2227707598259143`
(= 1.1499764899…)  [00_FINAL_RESULT_85_PERCENT_CROSSED.md, `D = c_pc^{-1}`]. -/
def DPC : ℝ := 2561811364469143 / 2227707598259143

theorem DPC_eq_inv_cPC : DPC = 1 / cPC := by
  rw [cPC_eq, DPC]; norm_num

theorem cPC_pos : 0 < cPC := by rw [cPC_eq]; norm_num

/-- **A2, second identity**: `c_pc > 20/23`, i.e. the 85 % threshold of
[01_certificate_cycle1.md (10)] is cleared. -/
theorem cPC_gt : (20 : ℝ) / 23 < cPC := by rw [cPC_eq]; norm_num

/-- **A2, third identity**: `2 − 1/c_pc = 1893603832049143/2227707598259143`
[01_certificate_cycle1.md (11)]. -/
theorem two_sub_inv_cPC : 2 - 1 / cPC = 1893603832049143 / 2227707598259143 := by
  rw [cPC_eq]; norm_num

/-- `2 − D_pc` is the same number. -/
theorem two_sub_DPC : 2 - DPC = 1893603832049143 / 2227707598259143 := by
  rw [DPC]; norm_num

/-- **A2, fourth identity**: `2 − 1/c_pc > 17/20`. -/
theorem two_sub_inv_cPC_gt : (17 : ℝ) / 20 < 2 - 1 / cPC := by
  rw [two_sub_inv_cPC]; norm_num

/-- **A2, the strict margin**: `(2 − 1/c_pc) − 17/20 = 1047470577429/44554151965182860`
[01_certificate_cycle1.md (12)]. -/
theorem margin_eq :
    (2 - 1 / cPC) - 17 / 20 = 1047470577429 / 44554151965182860 := by
  rw [two_sub_inv_cPC]; norm_num

/-- and it is positive. -/
theorem margin_pos : (0 : ℝ) < (2 - 1 / cPC) - 17 / 20 := by
  rw [margin_eq]; norm_num

/-- `D_pc < 23/20`, the form the trace budget is used in
[01_certificate_cycle1.md (4), (6)]. -/
theorem DPC_lt : DPC < 23 / 20 := by rw [DPC]; norm_num

/-! ### The certificate as an integer identity

The two halves of `c_pc = λA²/(B + λJ)` are exact rationals with small numerators; recording them
separately makes the cross-multiplication a `decide`-grade statement about integers, independent of
`norm_num`'s rational normalizer. -/

/-- `λ·A² = 152003423/144000000` (numerator `143·1031²`, denominator `100·1200²`). -/
theorem lam_mul_A_sq :
    lam * (∫ s in (-(1:ℝ)/2)..(1/2), vProf s) ^ 2 = 152003423 / 144000000 := by
  rw [integral_vProf, lam]; norm_num

/-- `B + λ·J = 2561811364469143/2110412304000000`; its numerator is exactly the denominator of
`c_pc`. -/
theorem B_add_lam_mul_J :
    (∫ s in (-(1:ℝ)/2)..(1/2), vProf s ^ 2) + lam * jSat
      = 2561811364469143 / 2110412304000000 := by
  rw [integral_vProf_sq, jSat_eq, lam]; norm_num

/-- the cross-multiplication behind `cPC_eq`, on the integers:
`152003423 · 2110412304000000 = 144000000 · 2227707598259143`. -/
theorem cPC_cross_mult :
    152003423 * 2110412304000000 = 144000000 * 2227707598259143 := by
  decide

/-! ## 2. Achievable saturated-kernel costs -/

/-- `J(σ, v) = ∬_{[−1/2,1/2]²} min(σ|s−t|,1)·v(s)v(t) ds dt`, written in the one-dimensional
autocorrelation form the sources use  [01_certificate_cycle1.md (9),
07_root_gain_support_1p01.md]:
`2·(σ·∫₀^{1/σ} u·g(u) du + ∫_{1/σ}^{1} g(u) du)`, `g(u) = ∫_{−1/2}^{1/2−u} v(s)v(s+u) ds`. -/
def satJ (σ : ℝ) (v : ℝ → ℝ) : ℝ :=
  2 * (σ * (∫ u in (0:ℝ)..(1 / σ), u * (∫ s in (-(1:ℝ)/2)..(1/2 - u), v s * v (s + u)))
     + ∫ u in (1 / σ)..(1:ℝ), (∫ s in (-(1:ℝ)/2)..(1/2 - u), v s * v (s + u)))

/-- **`D` is an achievable normalized Frobenius cost at connected support `σ`** for the saturated
pair kernel `K(t) = min(σ|t|, 1)`: there is a profile `v`, strictly positive on `[−1/2,1/2]`, with

  `D = (∫v² + σ·J(σ,v)) / (σ·(∫v)²)`,

i.e. `D = 1/c_pc(σ,v)` in the notation of `01_certificate_cycle1.md` (5).  Written multiplicatively
so that no division-by-zero side condition is needed. -/
def SaturatedWindowCost (σ D : ℝ) : Prop :=
  ∃ v : ℝ → ℝ, (∀ s, |s| ≤ 1 / 2 → 0 < v s) ∧
    0 < (∫ s in (-(1:ℝ)/2)..(1/2), v s) ∧
    D * (σ * (∫ s in (-(1:ℝ)/2)..(1/2), v s) ^ 2)
      = (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + σ * satJ σ v

/-- for the certificate window, `J(λ, v) = J`  (`Window.jSat`). -/
theorem satJ_lam_vProf : satJ lam vProf = jSat := by
  simp only [satJ, jSat, integral_autocorr]

/-- **The support-143/100 window cost is PROVED**: `D_pc` is an achievable saturated cost at
`σ = 143/100`, realized by `v(s) = 1 − (169/100)s²`.  This is Phase A in the form the prime-side
hypothesis of `RH/Zeta85/Hypotheses.lean` consumes; the two lower rungs, whose optimal windows solve
an Euler equation with transcendental data, have their costs as axioms instead. -/
theorem windowCost_143 : SaturatedWindowCost lam DPC := by
  refine ⟨vProf, fun s hs => vProf_pos hs, ?_, ?_⟩
  · rw [integral_vProf]; norm_num
  · rw [satJ_lam_vProf, integral_vProf, integral_vProf_sq, jSat_eq, DPC, lam]
    norm_num

/-! ## 3. The count lemma (A3) -/

set_option linter.unusedVariables false in
/-- **A3, the count lemma**  [01_hybrid_cycle1.md §1, (1)–(3)].  With
`s` = simple critical-line mass, `d` = distinct multiple critical-line mass, `p` = off-line pair mass,
`N` = total zero count with multiplicity, the two accepted constraints

  `s + 2d + 2p ≤ N`  (the multiplicity count [eq (1)]) and
  `3s + 4d + 4p ≥ (4 − C)·N`  (the optimized rank–trace charge [eq (2)])

force `s ≥ (2 − C)·N` [eq (3)].  Purely linear: `(2)` minus twice `(1)` is `s ≥ (4−C)N − 2N`.

The nonnegativity hypotheses `s, d, p ≥ 0` are part of the statement as the source writes it (they
are the zero-population interpretation); the proof does not need them, since `(2) − 2·(1)` is already
the conclusion.  Hence the `unusedVariables` linter is switched off for the two declarations below —
they are kept so that the Lean statement is the source's statement verbatim. -/
theorem count_lemma {s d p N C : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hp : 0 ≤ p)
    (h1 : s + 2 * d + 2 * p ≤ N) (h2 : (4 - C) * N ≤ 3 * s + 4 * d + 4 * p) :
    (2 - C) * N ≤ s := by
  nlinarith [h1, h2, hs, hd, hp]

set_option linter.unusedVariables false in
/-- **A3, the specialization `C = 23/20 − η`**  [01_hybrid_cycle1.md (2)–(3)]:
the trace budget `tr(B_T²) ≤ (23/20 − η)·N` gives `s ≥ (17/20 + η)·N`. -/
theorem count_lemma_85 {s d p N η : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hp : 0 ≤ p)
    (h1 : s + 2 * d + 2 * p ≤ N) (h2 : (4 - (23 / 20 - η)) * N ≤ 3 * s + 4 * d + 4 * p) :
    (17 / 20 + η) * N ≤ s := by
  have h := count_lemma hs hd hp h1 h2
  have : (2 - (23 / 20 - η)) = (17 / 20 + η) := by ring
  rwa [this] at h

/-- The two lemmas combine at the certificate's own constant: at `C = D_pc` the count lemma
yields exactly the 85 % constant of `01_certificate_cycle1.md` (11), with the strictly positive
margin `η = 1047470577429/44554151965182860` over `17/20`. -/
theorem count_lemma_at_DPC {s d p N : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hp : 0 ≤ p) (hN : 0 ≤ N)
    (h1 : s + 2 * d + 2 * p ≤ N) (h2 : (4 - DPC) * N ≤ 3 * s + 4 * d + 4 * p) :
    (1893603832049143 / 2227707598259143 : ℝ) * N ≤ s ∧ (17 / 20 : ℝ) * N ≤ s := by
  have h := count_lemma hs hd hp h1 h2
  rw [two_sub_DPC] at h
  refine ⟨h, le_trans ?_ h⟩
  have : (17 : ℝ) / 20 ≤ 1893603832049143 / 2227707598259143 := by norm_num
  exact mul_le_mul_of_nonneg_right this hN

end Zeta85
end RH

end
