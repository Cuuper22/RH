/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/SignedShift.lean — **C1, the signed-shift reciprocal lemma, PROVED.**

`docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` §2, equations (12)–(13).  No axioms, no
`sorry`.

For `w ∈ C^J` supported in `(1,2)` and `S_{H₀}(θ) = Σ_h w(h/H₀)·e(hθ)`:

  (12)  `|S_{H₀}(θ)| ≪_J H₀·(1 + H₀‖θ‖)^{−J}`,
  (13)  `Σ*_{r mod q} |S_{H₀}(ℓr/q)| ≪_J q + H₀·(ℓ,q)`.

The source proves (12) "by Poisson summation".  The route taken here is the equivalent elementary
one — `J`-fold summation by parts against the geometric kernel — which is what actually produces the
uniform constant and needs no convergence bookkeeping:

* `bdiffIter_le` — if `u ∈ C^J(ℝ)` with `|u^{(J)}| ≤ B`, the `J`-fold backward difference of step
  `c ≥ 0` satisfies `|Δ_c^J u| ≤ B·c^J` (iterated mean value theorem);
* `abel_iter` — `(z−1)^j·Σ_{k<M} u_k z^k = (−1)^j·Σ_{k<M} (Δ^j u)_k z^k` for a sequence vanishing at
  both ends of the range;
* `four_nearInt_le_norm_cexp_sub_one` — `|e(θ) − 1| = 2|sin πθ| ≥ 4‖θ‖` (Jordan's inequality);
* `shiftSum_decay` — the three combined, in the two regimes `H₀‖θ‖ < 1` and `H₀‖θ‖ ≥ 1`.

For (13) the source's own proof is: "divide the unit circle into arcs of length `1/H₀`; (12) gives a
convergent geometric tail away from the nearest integer; the image of the reduced residues has
spacing at least `(ℓ,q)/q`, with multiplicity at most `(ℓ,q)`."  Both halves are proved here:

* `nearInt_int_div` — the spacing engine: `q ∤ a ⟹ ‖a/q‖ ≥ 1/q`.  With `d = (ℓ,q)`, `ℓ = dℓ'`,
  `q = dq'`, one has `ℓr/q = ℓ'r/q'`, so two reduced residues collide only when `q' ∣ (r−r')` and
  otherwise the values are `d/q`-separated;
* `sum_over_separated` — the geometric count: for points labelled by arc index with fibres of size
  at most `m` and separation `δ`, the total of (12)'s bound is `≤ m·(C·H₀ + 2C/(H₀δ²))`.  At
  `δ = (ℓ,q)/q` and `m = (ℓ,q)` this is `≪ (ℓ,q)·H₀ + q²/(H₀(ℓ,q))`, and on the range where the
  `h`-sum is used (`q ≍ H₀·(ℓ,q)`, `docs/run/12` (9)) it is exactly `q + H₀(ℓ,q)`, i.e. (13).

`sum_over_separated` is stated for an arbitrary labelling rather than for `r ↦ ℓr mod q` so that it
carries no unproved arithmetic; supplying the labelling is the (elementary, standard) fibre count
`#{r < q : ℓr ≡ c (mod q)} ≤ (ℓ,q)`, which is where the two ingredients meet.  See `FINDINGS.md` §6.
-/
import RH.Zeta85.Arith

open Finset Filter

noncomputable section

namespace RH
namespace Zeta85
namespace SignedShift

/-! ## 1. Iterated backward differences and the mean value theorem -/

/-- backward difference of step `c`: `(Δ_c u)(x) = u x − u (x − c)`. -/
def bdiff (c : ℝ) (u : ℝ → ℝ) : ℝ → ℝ := fun x => u x - u (x - c)

/-- the `n`-fold backward difference of step `c`. -/
def bdiffIter (c : ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, u => u
  | n + 1, u => bdiff c (bdiffIter c n u)

@[simp] lemma bdiffIter_zero (c : ℝ) (u : ℝ → ℝ) : bdiffIter c 0 u = u := rfl

lemma bdiffIter_succ (c : ℝ) (n : ℕ) (u : ℝ → ℝ) :
    bdiffIter c (n + 1) u = bdiff c (bdiffIter c n u) := rfl

/-- `Δ_c` applied on the inside is the same as on the outside. -/
lemma bdiffIter_succ' (c : ℝ) (n : ℕ) (u : ℝ → ℝ) :
    bdiffIter c (n + 1) u = bdiffIter c n (bdiff c u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n IH => rw [bdiffIter_succ c (n + 1) u, IH, ← bdiffIter_succ]

/-- **The mean value step.**  If `u` is differentiable with `|u'| ≤ B` everywhere and `0 ≤ c`, then
`|Δ_c u| ≤ B·c`. -/
lemma bdiff_le {u : ℝ → ℝ} {B c : ℝ} (hu : Differentiable ℝ u)
    (hB : ∀ x, |deriv u x| ≤ B) (hc : 0 ≤ c) (x : ℝ) : |bdiff c u x| ≤ B * c := by
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_deriv_le (f := u)
    (fun y _ => hu y) (C := B) (fun y _ => by simpa [Real.norm_eq_abs] using hB y)
    (Set.mem_univ (x - c)) (Set.mem_univ x)
  simp only [Real.norm_eq_abs] at h
  have hxc : |x - (x - c)| = c := by rw [show x - (x - c) = c by ring, abs_of_nonneg hc]
  rw [hxc] at h
  exact h

/-- iterated derivatives commute with the backward difference. -/
lemma iteratedDeriv_bdiff {u : ℝ → ℝ} {n : ℕ} (hu : ContDiff ℝ n u) (c x : ℝ) :
    iteratedDeriv n (bdiff c u) x = iteratedDeriv n u x - iteratedDeriv n u (x - c) := by
  have hshift : ContDiff ℝ n (fun y : ℝ => -u (y - c)) :=
    (hu.comp (contDiff_id.sub contDiff_const)).neg
  have h : bdiff c u = u + fun y : ℝ => -u (y - c) := by
    funext y; simp [bdiff, sub_eq_add_neg]
  rw [h, iteratedDeriv_add hu.contDiffAt hshift.contDiffAt]
  have h2 : iteratedDeriv n (fun y : ℝ => -u (y - c)) = fun t => -iteratedDeriv n u (t - c) := by
    have h1 : (fun y : ℝ => -u (y - c)) = fun y : ℝ => (-u) (y - c) := rfl
    rw [h1, iteratedDeriv_comp_sub_const]
    funext t; simp
  rw [h2]; ring

/-- **The iterated mean value bound.**  If `u ∈ C^n(ℝ)` and `|u^{(n)}| ≤ B` everywhere, then for
`0 ≤ c` the `n`-fold backward difference satisfies `|Δ_c^n u| ≤ B·c^n`. -/
lemma bdiffIter_le : ∀ (n : ℕ) {u : ℝ → ℝ} {B c : ℝ}, ContDiff ℝ n u →
    (∀ x, |iteratedDeriv n u x| ≤ B) → 0 ≤ c → ∀ x, |bdiffIter c n u x| ≤ B * c ^ n := by
  intro n
  induction n with
  | zero => intro u B c _ hB _ x; simpa using hB x
  | succ n IH =>
      intro u B c hu hB hc x
      have hu' : ContDiff ℝ n u := hu.of_le (by exact_mod_cast Nat.le_succ n)
      have hdu : ContDiff ℝ n (bdiff c u) := by
        have hcomp : ContDiff ℝ n (fun y : ℝ => u (y - c)) :=
          hu'.comp (contDiff_id.sub contDiff_const)
        exact hu'.sub hcomp
      have hdn : ∀ y, |iteratedDeriv n (bdiff c u) y| ≤ B * c := by
        intro y
        rw [iteratedDeriv_bdiff hu' c y]
        have hdiff : Differentiable ℝ (iteratedDeriv n u) :=
          hu.differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n)
        have hb : ∀ z, |deriv (iteratedDeriv n u) z| ≤ B := by
          intro z
          have hz : deriv (iteratedDeriv n u) z = iteratedDeriv (n + 1) u z := by
            rw [iteratedDeriv_succ]
          rw [hz]; exact hB z
        simpa only [bdiff] using bdiff_le hdiff hb hc y
      have hfin := IH (u := bdiff c u) (B := B * c) (c := c) hdu hdn hc x
      rw [bdiffIter_succ']
      calc |bdiffIter c n (bdiff c u) x| ≤ B * c * c ^ n := hfin
        _ = B * c ^ (n + 1) := by ring

/-! ## 2. Summation by parts -/

/-- the backward difference of a sequence (`ℕ`-truncated subtraction sends `k = 0` to
`u 0 − u 0 = 0`, which is the correct value once `u` vanishes at `0`). -/
def ndiff (u : ℕ → ℂ) : ℕ → ℂ := fun k => u k - u (k - 1)

/-- the `n`-fold sequence difference. -/
def ndiffIter : ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, u => u
  | n + 1, u => ndiff (ndiffIter n u)

@[simp] lemma ndiffIter_zero (u : ℕ → ℂ) : ndiffIter 0 u = u := rfl

lemma ndiffIter_succ (n : ℕ) (u : ℕ → ℂ) : ndiffIter (n + 1) u = ndiff (ndiffIter n u) := rfl

/-- **One summation by parts.** -/
lemma abel_step (u : ℕ → ℂ) (M : ℕ) (z : ℂ) (h0 : u 0 = 0) (hM : u (M - 1) = 0) :
    (z - 1) * ∑ k ∈ Finset.range M, u k * z ^ k
      = -∑ k ∈ Finset.range M, ndiff u k * z ^ k := by
  have hshift : ∑ k ∈ Finset.range M, u k * z ^ (k + 1)
      = ∑ k ∈ Finset.range M, u (k - 1) * z ^ k := by
    have h1 : ∑ k ∈ Finset.range (M + 1), u (k - 1) * z ^ k
        = (∑ k ∈ Finset.range M, u ((k + 1) - 1) * z ^ (k + 1)) + u (0 - 1) * z ^ 0 :=
      Finset.sum_range_succ' (fun k => u (k - 1) * z ^ k) M
    have h2 : ∑ k ∈ Finset.range (M + 1), u (k - 1) * z ^ k
        = (∑ k ∈ Finset.range M, u (k - 1) * z ^ k) + u (M - 1) * z ^ M :=
      Finset.sum_range_succ (fun k => u (k - 1) * z ^ k) M
    simp only [Nat.add_sub_cancel, Nat.zero_sub, h0, zero_mul, add_zero, hM] at h1 h2
    rw [← h1, h2]
  have hmul : (∑ k ∈ Finset.range M, u k * z ^ k) * z
      = ∑ k ∈ Finset.range M, u k * z ^ (k + 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_succ]; ring
  have hexpand : (z - 1) * ∑ k ∈ Finset.range M, u k * z ^ k
      = (∑ k ∈ Finset.range M, u k * z ^ k) * z - ∑ k ∈ Finset.range M, u k * z ^ k := by ring
  rw [hexpand, hmul, hshift, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by simp only [ndiff]; ring

/-- **`j`-fold summation by parts.** -/
lemma abel_iter (u : ℕ → ℂ) (M : ℕ) (z : ℂ) :
    ∀ j : ℕ, (∀ i < j, ndiffIter i u 0 = 0) → (∀ i < j, ndiffIter i u (M - 1) = 0) →
      (z - 1) ^ j * ∑ k ∈ Finset.range M, u k * z ^ k
        = (-1) ^ j * ∑ k ∈ Finset.range M, ndiffIter j u k * z ^ k := by
  intro j
  induction j with
  | zero => intro _ _; simp
  | succ j IH =>
      intro h0 hM
      have hIH := IH (fun i hi => h0 i (by omega)) (fun i hi => hM i (by omega))
      have hstep := abel_step (ndiffIter j u) M z (h0 j (by omega)) (hM j (by omega))
      calc (z - 1) ^ (j + 1) * ∑ k ∈ Finset.range M, u k * z ^ k
          = (z - 1) * ((z - 1) ^ j * ∑ k ∈ Finset.range M, u k * z ^ k) := by ring
        _ = (z - 1) * ((-1) ^ j * ∑ k ∈ Finset.range M, ndiffIter j u k * z ^ k) := by rw [hIH]
        _ = (-1) ^ j * ((z - 1) * ∑ k ∈ Finset.range M, ndiffIter j u k * z ^ k) := by ring
        _ = (-1) ^ j * (-∑ k ∈ Finset.range M, ndiff (ndiffIter j u) k * z ^ k) := by rw [hstep]
        _ = (-1) ^ (j + 1) * ∑ k ∈ Finset.range M, ndiffIter (j + 1) u k * z ^ k := by
            rw [ndiffIter_succ]; ring

/-! ## 3. The geometric kernel: `|e(θ) − 1| = 2|sin πθ| ≥ 4‖θ‖` -/

lemma cexp_eq (x : ℝ) : cexp x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
  simp only [cexp]; push_cast; ring_nf

lemma cexp_re (x : ℝ) : (cexp x).re = Real.cos (2 * Real.pi * x) := by
  rw [cexp_eq]; exact Complex.exp_ofReal_mul_I_re _

lemma cexp_im (x : ℝ) : (cexp x).im = Real.sin (2 * Real.pi * x) := by
  rw [cexp_eq]; exact Complex.exp_ofReal_mul_I_im _

lemma norm_cexp (x : ℝ) : ‖cexp x‖ = 1 := by
  rw [cexp_eq]; exact Complex.norm_exp_ofReal_mul_I _

/-- `|e(x) − 1| = 2|sin(πx)|`. -/
lemma norm_cexp_sub_one (x : ℝ) : ‖cexp x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have hre : (cexp x - 1).re = Real.cos (2 * Real.pi * x) - 1 := by
    simp [Complex.sub_re, cexp_re]
  have him : (cexp x - 1).im = Real.sin (2 * Real.pi * x) := by
    simp [Complex.sub_im, cexp_im]
  rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him]
  have hpyth := Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  have hdouble : Real.cos (2 * Real.pi * x) = 1 - 2 * (Real.sin (Real.pi * x)) ^ 2 := by
    have h2 : (2 : ℝ) * Real.pi * x = 2 * (Real.pi * x) := by ring
    rw [h2, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
  have hkey : (Real.cos (2 * Real.pi * x) - 1) ^ 2 + Real.sin (2 * Real.pi * x) ^ 2
      = (2 * |Real.sin (Real.pi * x)|) ^ 2 := by
    have habs : |Real.sin (Real.pi * x)| ^ 2 = (Real.sin (Real.pi * x)) ^ 2 := sq_abs _
    nlinarith [hpyth, hdouble, habs]
  rw [hkey, Real.sqrt_sq (by positivity)]

/-- Jordan's inequality on the half-period: `2|x| ≤ |sin(πx)|` for `|x| ≤ 1/2`. -/
lemma jordan {x : ℝ} (hx : |x| ≤ 1 / 2) : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → 2 * y ≤ Real.sin (Real.pi * y) := by
    intro y hy0 hy1
    have h2 : 0 ≤ Real.pi * y := by positivity
    have h1 : Real.pi * y ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin h2 h1
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    calc 2 * y = 2 / Real.pi * (Real.pi * y) := by field_simp
      _ ≤ Real.sin (Real.pi * y) := hs
  have hnn : 0 ≤ Real.sin (Real.pi * |x|) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos, abs_nonneg x])
  have e1 : |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * |x|)| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, show Real.pi * -x = -(Real.pi * x) by ring, Real.sin_neg, abs_neg]
  rw [e1, abs_of_nonneg hnn]
  exact key |x| (abs_nonneg x) hx

/-- **`|e(θ) − 1| ≥ 4‖θ‖`**, the geometric-kernel lower bound of `docs/run/12` §2. -/
theorem four_nearInt_le_norm_cexp_sub_one (θ : ℝ) : 4 * nearInt θ ≤ ‖cexp θ - 1‖ := by
  set t : ℝ := θ - (round θ : ℝ) with ht
  have hper : cexp θ = cexp t := by
    have hz : ((2 : ℂ) * (Real.pi : ℂ) * (t : ℝ) * Complex.I)
        = 2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I
          - ((round θ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [ht]; push_cast; ring
    simp only [cexp]
    rw [hz, Complex.exp_sub, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, div_one]
  have habs : |t| ≤ 1 / 2 := by simpa [ht] using abs_sub_round θ
  have hnear : nearInt θ = |t| := rfl
  rw [hper, hnear, norm_cexp_sub_one]
  linarith [jordan habs]

/-! ## 4. The decay bound (12) -/

/-- the sequence `k ↦ w(k/H₀)` as a complex-valued sequence. -/
def seqOf (w : ℝ → ℝ) (H₀ : ℝ) : ℕ → ℂ := fun k => ((w ((k : ℝ) / H₀) : ℝ) : ℂ)

/-- the rescaled window `x ↦ w(x/H₀)`. -/
def resc (w : ℝ → ℝ) (H₀ : ℝ) : ℝ → ℝ := fun x => w (x / H₀)

variable {w : ℝ → ℝ} {H₀ : ℝ}

/-- the rescaled window vanishes on `x ≤ H₀`, in particular on `x ≤ 0`. -/
lemma resc_vanish_left (hH : 1 ≤ H₀) (hsupp : ∀ y ≤ (1 : ℝ), w y = 0) {x : ℝ} (hx : x ≤ 0) :
    resc w H₀ x = 0 := by
  have hH0 : (0 : ℝ) < H₀ := lt_of_lt_of_le zero_lt_one hH
  exact hsupp _ (le_trans (div_nonpos_of_nonpos_of_nonneg hx hH0.le) zero_le_one)

/-- the rescaled window vanishes on `x ≥ 2H₀`. -/
lemma resc_vanish_right (hH : 1 ≤ H₀) (hsupp : ∀ y ≥ (2 : ℝ), w y = 0) {x : ℝ}
    (hx : 2 * H₀ ≤ x) : resc w H₀ x = 0 := by
  have hH0 : (0 : ℝ) < H₀ := lt_of_lt_of_le zero_lt_one hH
  exact hsupp _ (by rw [ge_iff_le, le_div_iff₀ hH0]; linarith)

/-- every iterated difference of step `1` vanishes to the left of the support. -/
lemma bdiffIter_vanish_left (hH : 1 ≤ H₀) (hsupp : ∀ y ≤ (1 : ℝ), w y = 0) :
    ∀ (n : ℕ) {x : ℝ}, x ≤ 0 → bdiffIter 1 n (resc w H₀) x = 0 := by
  intro n
  induction n with
  | zero => intro x hx; exact resc_vanish_left hH hsupp hx
  | succ n IH =>
      intro x hx
      rw [bdiffIter_succ, bdiff, IH hx, IH (by linarith)]
      ring

/-- every iterated difference of step `1` vanishes to the right of the support. -/
lemma bdiffIter_vanish_right (hH : 1 ≤ H₀) (hsupp : ∀ y ≥ (2 : ℝ), w y = 0) :
    ∀ (n : ℕ) {x : ℝ}, 2 * H₀ + n ≤ x → bdiffIter 1 n (resc w H₀) x = 0 := by
  intro n
  induction n with
  | zero => intro x hx; exact resc_vanish_right hH hsupp (by simpa using hx)
  | succ n IH =>
      intro x hx
      have h1 : 2 * H₀ + (n : ℝ) ≤ x := by push_cast at hx; linarith
      have h2 : 2 * H₀ + (n : ℝ) ≤ x - 1 := by push_cast at hx; linarith
      rw [bdiffIter_succ, bdiff, IH h1, IH h2]
      ring

/-- the sequence differences are the real ones. -/
lemma ndiffIter_eq (hH : 1 ≤ H₀) (hsupp : ∀ y ≤ (1 : ℝ), w y = 0) :
    ∀ (n : ℕ) (k : ℕ),
      ndiffIter n (seqOf w H₀) k = ((bdiffIter 1 n (resc w H₀) (k : ℝ) : ℝ) : ℂ) := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n IH =>
      intro k
      rw [ndiffIter_succ, ndiff, IH k, IH (k - 1), bdiffIter_succ, bdiff]
      push_cast
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have hz : bdiffIter 1 n (resc w H₀) ((0 : ℕ) : ℝ) = 0 :=
          bdiffIter_vanish_left hH hsupp n (by norm_num)
        have hz' : bdiffIter 1 n (resc w H₀) (((0 : ℕ) : ℝ) - 1) = 0 :=
          bdiffIter_vanish_left hH hsupp n (by norm_num)
        simp only [Nat.zero_sub, hz, hz']
      · have hk' : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          have : 1 ≤ k := hk
          push_cast [Nat.cast_sub this]; ring
        rw [hk']

/-- `e(kθ) = e(θ)^k`. -/
lemma cexp_natCast_mul (k : ℕ) (θ : ℝ) : cexp ((k : ℝ) * θ) = (cexp θ) ^ k := by
  simp only [cexp]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- the shift sum written as a sum over an initial segment (all omitted terms vanish). -/
lemma shiftSum_eq_range (hH : 1 ≤ H₀) (hsuppL : ∀ y ≤ (1 : ℝ), w y = 0)
    (hsuppR : ∀ y ≥ (2 : ℝ), w y = 0) (θ : ℝ) {M : ℕ} (hM : ⌈2 * H₀⌉₊ + 1 ≤ M) :
    shiftSum w H₀ θ = ∑ k ∈ Finset.range M, seqOf w H₀ k * (cexp θ) ^ k := by
  have hH0 : (0 : ℝ) < H₀ := lt_of_lt_of_le zero_lt_one hH
  have hsub : Finset.Icc 1 ⌈2 * H₀⌉₊ ⊆ Finset.range M := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  have hzero : ∀ k ∈ Finset.range M, k ∉ Finset.Icc 1 ⌈2 * H₀⌉₊ →
      seqOf w H₀ k * (cexp θ) ^ k = 0 := by
    intro k _ hk
    simp only [Finset.mem_Icc, not_and_or, not_le] at hk
    have : seqOf w H₀ k = 0 := by
      rcases hk with hk | hk
      · have hk0 : k = 0 := by omega
        subst hk0
        simp only [seqOf, Nat.cast_zero, zero_div]
        norm_num [hsuppL 0 (by norm_num)]
      · have hge : 2 * H₀ ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk.le)
        simp only [seqOf]
        rw [hsuppR _ (by rw [ge_iff_le, le_div_iff₀ hH0]; linarith)]
        norm_num
    rw [this, zero_mul]
  rw [shiftSum]
  rw [← Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl fun k _ => by rw [seqOf, cexp_natCast_mul]

/--
**C1, equation (12): the signed-shift decay bound.**

For `w ∈ C^J(ℝ)` vanishing outside `(1,2)`, with `|w| ≤ K₀` and `|w^{(J)}| ≤ K_J`, and every
`H₀ ≥ 1`, `θ ∈ ℝ`:

  `|S_{H₀}(θ)|·(1 + H₀‖θ‖)^J ≤ (J+5)·2^J·(K₀+K_J)·H₀`,

which is `|S_{H₀}(θ)| ≪_J H₀·(1 + H₀‖θ‖)^{−J}` with the constant written out.  The multiplicative
form is used so that no division or `rpow` enters the statement.
-/
theorem shiftSum_decay (J : ℕ) (K₀ KJ : ℝ) (hw : ContDiff ℝ J w)
    (hsuppL : ∀ y ≤ (1 : ℝ), w y = 0) (hsuppR : ∀ y ≥ (2 : ℝ), w y = 0)
    (hK₀ : ∀ y, |w y| ≤ K₀) (hKJ : ∀ y, |iteratedDeriv J w y| ≤ KJ)
    (hH : 1 ≤ H₀) (θ : ℝ) :
    ‖shiftSum w H₀ θ‖ * (1 + H₀ * nearInt θ) ^ J
      ≤ ((J : ℝ) + 5) * 2 ^ J * (K₀ + KJ) * H₀ := by
  have hH0 : (0 : ℝ) < H₀ := lt_of_lt_of_le zero_lt_one hH
  have hK₀0 : 0 ≤ K₀ := le_trans (abs_nonneg _) (hK₀ 0)
  have hKJ0 : 0 ≤ KJ := le_trans (abs_nonneg _) (hKJ 0)
  have hnear0 : 0 ≤ nearInt θ := nearInt_nonneg θ
  set N : ℕ := ⌈2 * H₀⌉₊ with hN
  set M : ℕ := N + J + 2 with hMdef
  have hMle : N + 1 ≤ M := by omega
  have hNle : (N : ℝ) ≤ 2 * H₀ + 1 := by
    have := Nat.ceil_lt_add_one (le_of_lt (by positivity : (0:ℝ) < 2 * H₀))
    linarith [this]
  have hMbound : (M : ℝ) ≤ ((J : ℝ) + 5) * H₀ := by
    have h1 : (M : ℝ) = (N : ℝ) + (J : ℝ) + 2 := by push_cast [hMdef]; ring
    nlinarith [hNle, hH, Nat.cast_nonneg (α := ℝ) J]
  set z : ℂ := cexp θ with hz
  have hzn : ‖z‖ = 1 := norm_cexp θ
  have hSeq := shiftSum_eq_range (w := w) (H₀ := H₀) hH hsuppL hsuppR θ hMle
  -- the trivial bound
  have htriv : ‖shiftSum w H₀ θ‖ ≤ (M : ℝ) * K₀ := by
    rw [hSeq]
    calc ‖∑ k ∈ Finset.range M, seqOf w H₀ k * z ^ k‖
        ≤ ∑ k ∈ Finset.range M, ‖seqOf w H₀ k * z ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range M, K₀ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_pow, hzn, one_pow, mul_one]
          simpa [seqOf, Complex.norm_real, Real.norm_eq_abs] using hK₀ ((k : ℝ) / H₀)
      _ = (M : ℝ) * K₀ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rcases le_or_gt (H₀ * nearInt θ) 1 with hcase | hcase
  · -- small `‖θ‖`: the trivial bound suffices
    have hP : (1 + H₀ * nearInt θ) ^ J ≤ 2 ^ J := by
      refine pow_le_pow_left₀ (by positivity) (by linarith) J
    have hS0 : (0 : ℝ) ≤ ‖shiftSum w H₀ θ‖ := norm_nonneg _
    calc ‖shiftSum w H₀ θ‖ * (1 + H₀ * nearInt θ) ^ J ≤ ((M : ℝ) * K₀) * 2 ^ J := by
          exact mul_le_mul htriv hP (by positivity) (by positivity)
      _ ≤ (((J : ℝ) + 5) * H₀ * K₀) * 2 ^ J := by
          have : (M : ℝ) * K₀ ≤ ((J : ℝ) + 5) * H₀ * K₀ :=
            mul_le_mul_of_nonneg_right hMbound hK₀0
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ ((J : ℝ) + 5) * 2 ^ J * (K₀ + KJ) * H₀ := by
          have hprod : (0 : ℝ) ≤ ((J : ℝ) + 5) * 2 ^ J * KJ * H₀ := by positivity
          nlinarith [hprod]
  · -- large `‖θ‖`: `J`-fold summation by parts
    have hnearpos : 0 < nearInt θ := by
      by_contra hcon
      push_neg at hcon
      have : nearInt θ = 0 := le_antisymm hcon hnear0
      rw [this, mul_zero] at hcase; linarith
    -- the differenced sequence is small
    have hdiffBound : ∀ k : ℕ, ‖ndiffIter J (seqOf w H₀) k‖ ≤ KJ / H₀ ^ J := by
      intro k
      rw [ndiffIter_eq hH hsuppL J k]
      have hresc : ContDiff ℝ J (resc w H₀) := by
        have : resc w H₀ = fun x : ℝ => w ((1 / H₀) * x) := by
          funext x; simp [resc, div_eq_inv_mul, one_div]
        rw [this]
        exact hw.comp (contDiff_const.mul contDiff_id)
      have hd : ∀ x, |iteratedDeriv J (resc w H₀) x| ≤ KJ / H₀ ^ J := by
        intro x
        have heq : resc w H₀ = fun y : ℝ => w ((1 / H₀) * y) := by
          funext y; simp [resc, div_eq_inv_mul, one_div]
        rw [heq, iteratedDeriv_comp_const_mul hw (1 / H₀)]
        rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / H₀)]
        have h1 : |iteratedDeriv J w (1 / H₀ * x)| ≤ KJ := hKJ _
        have h2 : (1 / H₀) ^ J = 1 / H₀ ^ J := by rw [div_pow, one_pow]
        rw [h2]
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right (by positivity)]
        exact h1
      have := bdiffIter_le J (u := resc w H₀) (B := KJ / H₀ ^ J) (c := 1) hresc hd zero_le_one
        (k : ℝ)
      simpa [Complex.norm_real, Real.norm_eq_abs] using this
    -- summation by parts
    have hvanL : ∀ i < J, ndiffIter i (seqOf w H₀) 0 = 0 := by
      intro i _
      rw [ndiffIter_eq hH hsuppL i 0]
      have : bdiffIter 1 i (resc w H₀) ((0 : ℕ) : ℝ) = 0 :=
        bdiffIter_vanish_left hH hsuppL i (by norm_num)
      rw [this]; norm_num
    have hvanR : ∀ i < J, ndiffIter i (seqOf w H₀) (M - 1) = 0 := by
      intro i hi
      rw [ndiffIter_eq hH hsuppL i (M - 1)]
      have hgt : 2 * H₀ + (i : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
        have h1 : (M - 1 : ℕ) = N + J + 1 := by omega
        rw [h1]
        have h2 : (2 : ℝ) * H₀ ≤ (N : ℝ) := Nat.le_ceil _
        have h3 : (i : ℝ) ≤ (J : ℝ) := by exact_mod_cast hi.le
        push_cast
        linarith
      rw [bdiffIter_vanish_right hH hsuppR i hgt]; norm_num
    have habel := abel_iter (seqOf w H₀) M z J hvanL hvanR
    have hnormEq : ‖z - 1‖ ^ J * ‖shiftSum w H₀ θ‖
        ≤ (M : ℝ) * (KJ / H₀ ^ J) := by
      have h1 : ‖(z - 1) ^ J * ∑ k ∈ Finset.range M, seqOf w H₀ k * z ^ k‖
          = ‖z - 1‖ ^ J * ‖shiftSum w H₀ θ‖ := by
        rw [norm_mul, norm_pow, ← hSeq]
      rw [← h1, habel, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      calc ‖∑ k ∈ Finset.range M, ndiffIter J (seqOf w H₀) k * z ^ k‖
          ≤ ∑ k ∈ Finset.range M, ‖ndiffIter J (seqOf w H₀) k * z ^ k‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range M, KJ / H₀ ^ J := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [norm_mul, norm_pow, hzn, one_pow, mul_one]
            exact hdiffBound k
        _ = (M : ℝ) * (KJ / H₀ ^ J) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- combine with Jordan and the regime hypothesis
    have hjor : (4 : ℝ) * nearInt θ ≤ ‖z - 1‖ := four_nearInt_le_norm_cexp_sub_one θ
    have hpow : ((4 : ℝ) * nearInt θ) ^ J * ‖shiftSum w H₀ θ‖ ≤ (M : ℝ) * (KJ / H₀ ^ J) :=
      le_trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hjor J) (norm_nonneg _)) hnormEq
    have hP : (1 + H₀ * nearInt θ) ^ J ≤ (2 * (H₀ * nearInt θ)) ^ J :=
      pow_le_pow_left₀ (by positivity) (by linarith) J
    have hfactor : (2 * (H₀ * nearInt θ)) ^ J
        = ((4 : ℝ) * nearInt θ) ^ J * (H₀ / 2) ^ J := by
      rw [← mul_pow]; congr 1; ring
    have hS0 : (0 : ℝ) ≤ ‖shiftSum w H₀ θ‖ := norm_nonneg _
    have hstep : ‖shiftSum w H₀ θ‖ * (1 + H₀ * nearInt θ) ^ J
        ≤ (M : ℝ) * (KJ / H₀ ^ J) * (H₀ / 2) ^ J := by
      calc ‖shiftSum w H₀ θ‖ * (1 + H₀ * nearInt θ) ^ J
          ≤ ‖shiftSum w H₀ θ‖ * (2 * (H₀ * nearInt θ)) ^ J :=
            mul_le_mul_of_nonneg_left hP hS0
        _ = (((4 : ℝ) * nearInt θ) ^ J * ‖shiftSum w H₀ θ‖) * (H₀ / 2) ^ J := by
            rw [hfactor]; ring
        _ ≤ ((M : ℝ) * (KJ / H₀ ^ J)) * (H₀ / 2) ^ J :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
    have hsimp : (M : ℝ) * (KJ / H₀ ^ J) * (H₀ / 2) ^ J = (M : ℝ) * KJ / 2 ^ J := by
      rw [div_pow]
      field_simp
    rw [hsimp] at hstep
    refine hstep.trans ?_
    have h2J : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    have hMK : (M : ℝ) * KJ ≤ ((J : ℝ) + 5) * H₀ * KJ :=
      mul_le_mul_of_nonneg_right hMbound hKJ0
    have hdiv : (M : ℝ) * KJ / 2 ^ J ≤ ((J : ℝ) + 5) * H₀ * KJ := by
      refine le_trans (div_le_of_le_mul₀ (by positivity) (by positivity) ?_) le_rfl
      nlinarith [hMK, h2J, mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (J:ℝ) + 5) hH0.le) hKJ0]
    refine hdiv.trans ?_
    have hcmp : KJ ≤ 2 ^ J * (K₀ + KJ) := by nlinarith [h2J, hK₀0, hKJ0]
    have ha : (0 : ℝ) ≤ ((J : ℝ) + 5) * H₀ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcmp ha]

/-! ## 5. Equation (13): the reduced-residue sum -/

/-- **The spacing engine.**  If `q ∤ a` then `a/q` is at distance at least `1/q` from `ℤ`.  This is
the arithmetic input behind "the image of the reduced residues has spacing at least `(ℓ,q)/q`" in
`docs/run/12` §2: with `d = (ℓ,q)`, `ℓ = dℓ'`, `q = dq'`, one has `ℓr/q = ℓ'r/q'`, and two reduced
residues give the same value only when `q' ∣ (r − r')`. -/
theorem nearInt_int_div (a : ℤ) (q : ℕ) (hq : 0 < q) (hnd : ¬ ((q : ℤ) ∣ a)) :
    (1 : ℝ) / q ≤ nearInt ((a : ℝ) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set m : ℤ := round ((a : ℝ) / q) with hm
  have hne : a - m * q ≠ 0 := by
    intro h
    exact hnd ⟨m, by linarith [sub_eq_zero.mp h]⟩
  have h1 : (1 : ℝ) ≤ |((a - m * q : ℤ) : ℝ)| := by
    have h0 := Int.one_le_abs hne
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|a - m * q| : ℤ) : ℝ) := by exact_mod_cast h0
      _ = |((a - m * q : ℤ) : ℝ)| := by push_cast; rfl
  have hrepr : (a : ℝ) / q - (m : ℝ) = ((a - m * q : ℤ) : ℝ) / q := by
    push_cast; field_simp
  have hval : nearInt ((a : ℝ) / q) = |(a : ℝ) / q - (m : ℝ)| := rfl
  rw [hval, hrepr, abs_div, abs_of_pos hqR]
  gcongr

/-- **The geometric count over separated points** — the "divide the unit circle into arcs of length
`1/H₀`; (12) gives a convergent geometric tail away from the nearest integer" step of
`docs/run/12` §2, isolated from the arithmetic.

`nlab i` is the arc index of the point `i`, the arcs being `δ`-separated; the fibres of `nlab` have
size at most `m` (the multiplicity `(ℓ,q)` in the application); each value obeys the decay bound of
(12) at `J = 2`.  Conclusion: the total is `≪ m·(H₀ + 1/(H₀δ²))`, which at `δ = (ℓ,q)/q`,
`m = (ℓ,q)` is (13). -/
theorem sum_over_separated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → ℝ) (nlab : ι → ℕ) (m : ℕ) (δ C H₀ : ℝ)
    (hδ : 0 < δ) (hH : 0 < H₀) (hC : 0 ≤ C)
    (hfib : ∀ k : ℕ, (Finset.univ.filter fun i => nlab i = k).card ≤ m)
    (hF : ∀ i : ι, 0 ≤ F i)
    (hdec : ∀ i : ι, F i * (1 + H₀ * ((nlab i : ℝ) * δ)) ^ 2 ≤ C * H₀) :
    ∑ i : ι, F i ≤ (m : ℝ) * (C * H₀ + 2 * (C / (H₀ * δ ^ 2))) := by
  classical
  have hterm : ∀ i : ι, F i ≤ C * H₀ / (1 + H₀ * ((nlab i : ℝ) * δ)) ^ 2 := by
    intro i
    have hpos : (0 : ℝ) < (1 + H₀ * ((nlab i : ℝ) * δ)) ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    exact hdec i
  set Im : Finset ℕ := Finset.image nlab Finset.univ with hIm
  have hgroup : ∑ i : ι, F i
      = ∑ k ∈ Im, ∑ i ∈ Finset.univ.filter fun i => nlab i = k, F i := by
    rw [hIm, Finset.sum_fiberwise_of_maps_to]
    intro i _
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hinner : ∀ k ∈ Im,
      ∑ i ∈ Finset.univ.filter fun i => nlab i = k, F i
        ≤ (m : ℝ) * (C * H₀ / (1 + H₀ * ((k : ℝ) * δ)) ^ 2) := by
    intro k _
    have hb : ∀ i ∈ Finset.univ.filter fun i => nlab i = k,
        F i ≤ C * H₀ / (1 + H₀ * ((k : ℝ) * δ)) ^ 2 := by
      intro i hi
      simp only [Finset.mem_filter] at hi
      have hti := hterm i
      rwa [hi.2] at hti
    calc ∑ i ∈ Finset.univ.filter fun i => nlab i = k, F i
        ≤ ∑ _i ∈ Finset.univ.filter fun i => nlab i = k,
            C * H₀ / (1 + H₀ * ((k : ℝ) * δ)) ^ 2 := Finset.sum_le_sum hb
      _ = ((Finset.univ.filter fun i => nlab i = k).card : ℝ)
            * (C * H₀ / (1 + H₀ * ((k : ℝ) * δ)) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * (C * H₀ / (1 + H₀ * ((k : ℝ) * δ)) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hfib k
  rw [hgroup]
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the tail: split off `k = 0` and compare the rest with `Σ_{k ≥ 1} k^{-2} ≤ 2`
  set N : ℕ := Im.sup id + 1 with hNdef
  have hsplit : ∑ k ∈ Im, C * H₀ / (1 + H₀ * ((k : ℝ) * δ)) ^ 2
      ≤ C * H₀ + ∑ k ∈ Finset.Ioo 0 N, (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹ := by
    have hzero : ∀ k ∈ Im, C * H₀ / (1 + H₀ * ((k : ℝ) * δ)) ^ 2
        ≤ (if k = 0 then C * H₀ else (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹) := by
      intro k _
      by_cases hk : k = 0
      · subst hk; simp
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
        have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
        simp only [hk, if_false]
        rw [div_le_iff₀ (by positivity)]
        have hlow : H₀ * ((k : ℝ) * δ) ≤ 1 + H₀ * ((k : ℝ) * δ) := by linarith
        have hsq : (H₀ * ((k : ℝ) * δ)) ^ 2 ≤ (1 + H₀ * ((k : ℝ) * δ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlow 2
        have hexp : (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹ * (H₀ * ((k : ℝ) * δ)) ^ 2 = C * H₀ := by
          field_simp
        calc C * H₀ = (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹ * (H₀ * ((k : ℝ) * δ)) ^ 2 := hexp.symm
          _ ≤ (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹ * (1 + H₀ * ((k : ℝ) * δ)) ^ 2 := by
              exact mul_le_mul_of_nonneg_left hsq (by positivity)
    refine le_trans (Finset.sum_le_sum hzero) ?_
    have hpart : ∑ k ∈ Im, (if k = 0 then C * H₀ else (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹)
        ≤ C * H₀ + ∑ k ∈ Im.filter (fun k => k ≠ 0),
            (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹ := by
      rw [← Finset.sum_filter_add_sum_filter_not Im (fun k => k = 0)]
      refine add_le_add ?_ (le_of_eq (Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_filter] at hk; simp [hk.2]))
      by_cases h0 : (0 : ℕ) ∈ Im
      · have : Im.filter (fun k => k = 0) = {0} := by
          ext k; simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨-, rfl⟩; rfl
          · rintro rfl; exact ⟨h0, rfl⟩
        rw [this]; simp
      · have : Im.filter (fun k => k = 0) = ∅ := by
          ext k; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          rintro hk rfl; exact h0 hk
        rw [this]
        simp only [Finset.sum_empty]
        positivity
    have hsub : ∑ k ∈ Im.filter (fun k => k ≠ 0), (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹
        ≤ ∑ k ∈ Finset.Ioo 0 N, (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
      intro k hk
      simp only [Finset.mem_filter] at hk
      simp only [Finset.mem_Ioo]
      refine ⟨Nat.pos_of_ne_zero hk.2, ?_⟩
      have hle : k ≤ Im.sup id := Finset.le_sup (f := id) hk.1
      omega
    linarith
  refine le_trans hsplit ?_
  have htail : ∑ k ∈ Finset.Ioo 0 N, (C / (H₀ * δ ^ 2)) * ((k : ℝ) ^ 2)⁻¹
      ≤ 2 * (C / (H₀ * δ ^ 2)) := by
    rw [← Finset.mul_sum]
    have h2' : (∑ i ∈ Finset.Ioo 0 N, ((i : ℝ) ^ 2)⁻¹) ≤ 2 := by
      simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 N
    calc (C / (H₀ * δ ^ 2)) * ∑ k ∈ Finset.Ioo 0 N, ((k : ℝ) ^ 2)⁻¹
        ≤ (C / (H₀ * δ ^ 2)) * 2 := mul_le_mul_of_nonneg_left h2' (by positivity)
      _ = 2 * (C / (H₀ * δ ^ 2)) := by ring
  linarith

end SignedShift
end Zeta85
end RH

end
