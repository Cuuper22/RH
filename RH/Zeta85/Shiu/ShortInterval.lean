/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Arith

/-!
# Short-interval and progression transfer toolkit

The glue toolkit for transferring initial-segment divisor-sum bounds to short intervals and to
`progressionSum`'s window.  Everything here is elementary and unconditional counting/splitting;
the *transfer* lemmas are conditional in the campaign's sense — their inputs are **named
hypotheses** (`hB`, `hL`), never axioms — so that a sibling unit's initial-segment bound
`∑_{n ≤ N, n ≡ r (q)} f n ≤ B N` becomes a short-interval bound on `(x, x+y]` by a single
application.

Contents:

* **Unconditional interval counts** — `shortInt_multiples_card` (exact count of multiples of `d`
  in `(x, x+y]` as a difference of ℕ-divisions), the real-valued envelopes
  `shortInt_multiples_le` / `shortInt_multiples_ge` (`y/d ± 1`), and the arithmetic-progression
  envelopes `shortInt_ap_card_le` (`y/q + 1`, any residue) and `shortInt_ap_card_ge`
  (`y/q - 1`, genuine residues `r < q`).
* **Segment splitting** — `shortInt_Icc_split` / `shortInt_Icc_disjoint` split `[1, z]` into
  `[1, x] ⊔ (x, z]`, with the exact sum identities `shortInt_sum_split` and
  `shortInt_sum_split_filter`.
* **Conditional transfer** — `shortInt_transfer_of_nonneg` / `shortInt_transfer_of_monotone`
  (nonneg summand: initial-segment bounds restrict to short intervals),
  `shortInt_transfer_sub` / `shortInt_transfer_sandwich` (exact-difference and two-sided forms),
  `shortInt_transfer_real_bound` (real-argument bound shapes `G : ℝ → ℝ`), and the
  instantiation-ready polylog shapes `shortInt_transfer_polylog` /
  `shortInt_transfer_polylog_rpow` with `B N = K·N/φ(q)·(1 + log N)^E`.
* **`progressionSum` glue** — `shortInt_progressionSum_eq` (definitional unfold),
  `shortInt_progressionSum_le_of_bound` (an initial-segment bound evaluates the window at
  `⌈2P⌉₊`), and the numeric window bridge `⌈2P⌉₊ ≤ 2P + 1 ≤ 3P` (`shortInt_ceil_window_bridge`
  and friends) so that `B`-monotonicity arguments can continue in `ℝ`
  (`shortInt_progressionSum_le_of_real_bound`).
-/

open scoped BigOperators

namespace RH
namespace Zeta85
namespace Shiu

/-! ## Cast estimates for ℕ-division -/

/-- Real lower estimate for natural division: `n/d - 1 ≤ ⌊n/d⌋` as reals.  Companion of
`Nat.cast_div_le`; part of the glue toolkit for transferring initial-segment divisor-sum bounds
to short intervals and to `progressionSum`'s window. -/
lemma shortInt_cast_div_lower (n d : ℕ) (hd : 0 < d) :
    (n : ℝ) / d - 1 ≤ ((n / d : ℕ) : ℝ) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h : n < (n / d + 1) * d := by
    have h0 : n % d < d := Nat.mod_lt n hd
    have h1 : d * (n / d) + n % d = n := Nat.div_add_mod n d
    calc n = d * (n / d) + n % d := h1.symm
      _ < d * (n / d) + d := Nat.add_lt_add_left h0 _
      _ = (n / d + 1) * d := by ring
  have h' : (n : ℝ) < (((n / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast h
  rw [sub_le_iff_le_add, div_le_iff₀ hd']
  exact h'.le

/-! ## Unconditional interval counts over `Finset.Ioc` -/

/-- Exact count of multiples of `d` in the short interval `(x, x+y]`: it is
`(x+y)/d - x/d` in ℕ-division (no positivity of `d` is needed: for `d = 0` both sides
vanish).  Part of the glue toolkit for transferring initial-segment divisor-sum bounds to short
intervals and to `progressionSum`'s window. -/
lemma shortInt_multiples_card (x y d : ℕ) :
    ((Finset.Ioc x (x + y)).filter (d ∣ ·)).card = (x + y) / d - x / d := by
  have h1 : ((Finset.Ioc 0 x).filter (d ∣ ·)).card = x / d :=
    Nat.Ioc_filter_dvd_card_eq_div x d
  have h2 : ((Finset.Ioc 0 (x + y)).filter (d ∣ ·)).card = (x + y) / d :=
    Nat.Ioc_filter_dvd_card_eq_div (x + y) d
  have hunion : Finset.Ioc 0 x ∪ Finset.Ioc x (x + y) = Finset.Ioc 0 (x + y) :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) (Nat.le_add_right x y)
  have hdisj :
      Disjoint ((Finset.Ioc 0 x).filter (d ∣ ·)) ((Finset.Ioc x (x + y)).filter (d ∣ ·)) :=
    Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)
  have hadd : x / d + ((Finset.Ioc x (x + y)).filter (d ∣ ·)).card = (x + y) / d := by
    rw [← h1, ← h2, ← hunion, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  rw [← hadd, Nat.add_sub_cancel_left]

/-- Real upper envelope for the count of multiples of `d` in `(x, x+y]`: at most `y/d + 1`,
uniformly in the left endpoint `x`.  Part of the glue toolkit for transferring initial-segment
divisor-sum bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_multiples_le (x y d : ℕ) (hd : 0 < d) :
    (((Finset.Ioc x (x + y)).filter (d ∣ ·)).card : ℝ) ≤ (y : ℝ) / d + 1 := by
  have hmono : x / d ≤ (x + y) / d := Nat.div_le_div_right (Nat.le_add_right x y)
  rw [shortInt_multiples_card x y d, Nat.cast_sub hmono]
  have hA : (((x + y) / d : ℕ) : ℝ) ≤ ((x : ℝ) + y) / d := by
    have h0 : (((x + y) / d : ℕ) : ℝ) ≤ ((x + y : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
    push_cast at h0
    exact h0
  have hB : (x : ℝ) / d - 1 ≤ ((x / d : ℕ) : ℝ) := shortInt_cast_div_lower x d hd
  have hsplit : ((x : ℝ) + y) / d = (x : ℝ) / d + (y : ℝ) / d := add_div _ _ _
  linarith

/-- Real lower envelope for the count of multiples of `d` in `(x, x+y]`: at least `y/d - 1`,
uniformly in the left endpoint `x`.  Part of the glue toolkit for transferring initial-segment
divisor-sum bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_multiples_ge (x y d : ℕ) (hd : 0 < d) :
    (y : ℝ) / d - 1 ≤ (((Finset.Ioc x (x + y)).filter (d ∣ ·)).card : ℝ) := by
  have hmono : x / d ≤ (x + y) / d := Nat.div_le_div_right (Nat.le_add_right x y)
  rw [shortInt_multiples_card x y d, Nat.cast_sub hmono]
  have hA : ((x : ℝ) + y) / d - 1 ≤ (((x + y) / d : ℕ) : ℝ) := by
    have h0 := shortInt_cast_div_lower (x + y) d hd
    push_cast at h0
    exact h0
  have hB : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := Nat.cast_div_le
  have hsplit : ((x : ℝ) + y) / d = (x : ℝ) / d + (y : ℝ) / d := add_div _ _ _
  linarith

/-- Arithmetic-progression count in a short interval: the number of `n ∈ (x, x+y]` with
`n % q = r` is at most `y/q + 1`, uniformly in the left endpoint `x` and in the residue `r`.
Proof: shifting by `q - r` maps the progression injectively onto multiples of `q` in a
translated interval of the same length; residues `r ≥ q` give the empty set.  Part of the glue
toolkit for transferring initial-segment divisor-sum bounds to short intervals and to
`progressionSum`'s window. -/
lemma shortInt_ap_card_le (x y q r : ℕ) (hq : 0 < q) :
    (((Finset.Ioc x (x + y)).filter (fun n => n % q = r)).card : ℝ) ≤ (y : ℝ) / q + 1 := by
  rcases Nat.lt_or_ge r q with hr | hr
  · -- shift `n ↦ n + (q - r)` lands in the multiples of `q` in `(x + (q-r), x + (q-r) + y]`
    have hcard : ((Finset.Ioc x (x + y)).filter (fun n => n % q = r)).card
        ≤ ((Finset.Ioc (x + (q - r)) (x + (q - r) + y)).filter (q ∣ ·)).card := by
      apply Finset.card_le_card_of_injOn (fun n => n + (q - r))
      · intro n hn
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
        obtain ⟨⟨hn1, hn2⟩, hmod⟩ := hn
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        have hdm : q * (n / q) + r = n := by rw [← hmod]; exact Nat.div_add_mod n q
        have hrq : r + (q - r) = q := by omega
        refine ⟨n / q + 1, ?_⟩
        calc n + (q - r) = q * (n / q) + r + (q - r) := by rw [hdm]
          _ = q * (n / q) + (r + (q - r)) := by rw [Nat.add_assoc]
          _ = q * (n / q) + q := by rw [hrq]
          _ = q * (n / q + 1) := by ring
      · intro a _ b _ hab
        exact Nat.add_right_cancel hab
    have hcard' : (((Finset.Ioc x (x + y)).filter (fun n => n % q = r)).card : ℝ)
        ≤ (((Finset.Ioc (x + (q - r)) (x + (q - r) + y)).filter (q ∣ ·)).card : ℝ) := by
      exact_mod_cast hcard
    exact hcard'.trans (shortInt_multiples_le (x + (q - r)) y q hq)
  · -- a residue `r ≥ q` occurs for no `n` at all
    have hempty : (Finset.Ioc x (x + y)).filter (fun n => n % q = r) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro n _ hcon
      have hlt : n % q < q := Nat.mod_lt n hq
      rw [hcon] at hlt
      exact absurd hlt (not_lt.mpr hr)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- Arithmetic-progression lower envelope in a short interval: for a genuine residue `r < q`,
the number of `n ∈ (x, x+y]` with `n % q = r` is at least `y/q - 1`, uniformly in the left
endpoint `x`.  Proof: the multiples of `q` in the translated interval
`(x + (q-r), x + (q-r) + y]` inject back into the progression via `m ↦ m - (q - r)`, and
`shortInt_multiples_ge` counts them.  (The hypothesis `r < q` is necessary: an empty residue
class `r ≥ q` has no lower bound of this shape.)  Part of the glue toolkit for transferring
initial-segment divisor-sum bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_ap_card_ge (x y q r : ℕ) (hr : r < q) :
    (y : ℝ) / q - 1 ≤ (((Finset.Ioc x (x + y)).filter (fun n => n % q = r)).card : ℝ) := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have hcard : ((Finset.Ioc (x + (q - r)) (x + (q - r) + y)).filter (q ∣ ·)).card
      ≤ ((Finset.Ioc x (x + y)).filter (fun n => n % q = r)).card := by
    apply Finset.card_le_card_of_injOn (fun m => m - (q - r))
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm ⊢
      obtain ⟨⟨hm1, hm2⟩, hdvd⟩ := hm
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      obtain ⟨k, hk⟩ := hdvd
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · exfalso
        rw [hk, Nat.mul_zero] at hm1
        exact Nat.not_lt_zero _ hm1
      · have hkk : q * (k - 1) + q = q * k := by
          calc q * (k - 1) + q = q * (k - 1 + 1) := by ring
            _ = q * k := by rw [Nat.sub_add_cancel hk1]
        have hn : m - (q - r) = q * (k - 1) + r := by
          rw [hk, ← hkk, Nat.add_sub_assoc (Nat.sub_le q r), Nat.sub_sub_self hr.le]
        rw [hn, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at ha hb
      have hab' : a - (q - r) = b - (q - r) := hab
      omega
  have hcard' : (((Finset.Ioc (x + (q - r)) (x + (q - r) + y)).filter (q ∣ ·)).card : ℝ)
      ≤ (((Finset.Ioc x (x + y)).filter (fun n => n % q = r)).card : ℝ) := by
    exact_mod_cast hcard
  exact le_trans (shortInt_multiples_ge (x + (q - r)) y q hq) hcard'

/-! ## Segment splitting -/

/-- Splitting the initial segment: for `x ≤ z`, `[1, z] = [1, x] ∪ (x, z]`.  Part of the glue
toolkit for transferring initial-segment divisor-sum bounds to short intervals and to
`progressionSum`'s window. -/
lemma shortInt_Icc_split (x z : ℕ) (hxz : x ≤ z) :
    Finset.Icc 1 z = Finset.Icc 1 x ∪ Finset.Ioc x z := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
  omega

/-- The two pieces of `shortInt_Icc_split` are disjoint.  Part of the glue toolkit for
transferring initial-segment divisor-sum bounds to short intervals and to `progressionSum`'s
window. -/
lemma shortInt_Icc_disjoint (x z : ℕ) :
    Disjoint (Finset.Icc 1 x) (Finset.Ioc x z) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [Finset.mem_Icc] at hn
  simp only [Finset.mem_Ioc] at hn'
  omega

/-- Exact sum splitting: for `x ≤ z`, the short-interval sum over `(x, z]` is the difference of
the two initial-segment sums.  Part of the glue toolkit for transferring initial-segment
divisor-sum bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_sum_split (f : ℕ → ℝ) (x z : ℕ) (hxz : x ≤ z) :
    ∑ n ∈ Finset.Ioc x z, f n
      = ∑ n ∈ Finset.Icc 1 z, f n - ∑ n ∈ Finset.Icc 1 x, f n := by
  rw [shortInt_Icc_split x z hxz, Finset.sum_union (shortInt_Icc_disjoint x z)]
  ring

/-- Exact sum splitting along any decidable predicate (e.g. a congruence class): for `x ≤ z`,
the filtered short-interval sum over `(x, z]` is the difference of the two filtered
initial-segment sums.  Part of the glue toolkit for transferring initial-segment divisor-sum
bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_sum_split_filter (f : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p] (x z : ℕ)
    (hxz : x ≤ z) :
    ∑ n ∈ (Finset.Ioc x z).filter p, f n
      = ∑ n ∈ (Finset.Icc 1 z).filter p, f n - ∑ n ∈ (Finset.Icc 1 x).filter p, f n := by
  rw [shortInt_Icc_split x z hxz, Finset.filter_union,
    Finset.sum_union (Finset.disjoint_filter_filter (shortInt_Icc_disjoint x z))]
  ring

/-! ## Conditional transfer: initial-segment bounds to short intervals

The hypotheses `hB` (and `hL`) below are the campaign's named-hypothesis interface: a sibling
unit's initial-segment bound is consumed as `hB`, never as an axiom. -/

/-- **Transfer, nonneg summand, any predicate.**  If `f ≥ 0` and every initial segment obeys
`∑_{n ≤ N, p n} f n ≤ B N`, then every short interval obeys
`∑_{x < n ≤ x+y, p n} f n ≤ B (x+y)`, by positivity and `(x, x+y] ⊆ [1, x+y]`.  Part of the
glue toolkit for transferring initial-segment divisor-sum bounds to short intervals and to
`progressionSum`'s window. -/
lemma shortInt_transfer_of_nonneg (f B : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p]
    (hf : ∀ n, 0 ≤ f n)
    (hB : ∀ N : ℕ, ∑ n ∈ (Finset.Icc 1 N).filter p, f n ≤ B N) (x y : ℕ) :
    ∑ n ∈ (Finset.Ioc x (x + y)).filter p, f n ≤ B (x + y) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hB (x + y))
  · apply Finset.filter_subset_filter
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    omega
  · intro n _ _
    exact hf n

/-- **Transfer along a progression, nonneg summand.**  If `f ≥ 0` and every initial segment
obeys `∑_{n ≤ N, n % q = r} f n ≤ B N`, then every short interval `(x, x+y]` obeys the same
bound evaluated at the right endpoint `x + y`.  Instantiate `hB` with a sibling unit's
initial-segment majorant; the conclusion is the short-interval majorant.  (The name records
the mechanism — for `f ≥ 0` the filtered partial sums are *monotone* in the endpoint, so the
`[1, x+y]` bound dominates the `(x, x+y]` piece; no hypothesis on `B` itself is used.  For a
bound consumed through monotonicity of `B` in ℝ see
`shortInt_progressionSum_le_of_real_bound`.)  Part of the glue toolkit for transferring
initial-segment divisor-sum bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_transfer_of_monotone (f B : ℕ → ℝ) (q r : ℕ)
    (hf : ∀ n, 0 ≤ f n)
    (hB : ∀ N : ℕ, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r), f n ≤ B N) :
    ∀ x y : ℕ, ∑ n ∈ (Finset.Ioc x (x + y)).filter (fun n => n % q = r), f n ≤ B (x + y) :=
  fun x y => shortInt_transfer_of_nonneg f B (fun n => n % q = r) hf hB x y

/-- **Transfer along a progression, exact-difference form.**  With an upper bound `B` and a
lower bound `L` for the initial-segment sums, the short-interval sum over `(x, x+y]` — which is
*exactly* the difference of the two initial-segment sums (`shortInt_sum_split_filter`) — is at
most `B (x+y) - L x`.  No positivity of `f` is needed.  Part of the glue toolkit for
transferring initial-segment divisor-sum bounds to short intervals and to `progressionSum`'s
window. -/
lemma shortInt_transfer_sub (f B L : ℕ → ℝ) (q r : ℕ)
    (hB : ∀ N : ℕ, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r), f n ≤ B N)
    (hL : ∀ N : ℕ, L N ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r), f n) :
    ∀ x y : ℕ, ∑ n ∈ (Finset.Ioc x (x + y)).filter (fun n => n % q = r), f n
      ≤ B (x + y) - L x := by
  intro x y
  rw [shortInt_sum_split_filter f (fun n => n % q = r) x (x + y) (Nat.le_add_right x y)]
  have h1 := hB (x + y)
  have h2 := hL x
  linarith

/-- **Transfer along a progression, two-sided sandwich.**  With an upper bound `B` and a lower
bound `L` for the initial-segment sums, the short-interval sum over `(x, x+y]` is sandwiched:
`L (x+y) - B x ≤ ∑ ≤ B (x+y) - L x`.  Part of the glue toolkit for transferring
initial-segment divisor-sum bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_transfer_sandwich (f B L : ℕ → ℝ) (q r : ℕ)
    (hB : ∀ N : ℕ, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r), f n ≤ B N)
    (hL : ∀ N : ℕ, L N ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r), f n) :
    ∀ x y : ℕ,
      L (x + y) - B x ≤ ∑ n ∈ (Finset.Ioc x (x + y)).filter (fun n => n % q = r), f n
      ∧ ∑ n ∈ (Finset.Ioc x (x + y)).filter (fun n => n % q = r), f n ≤ B (x + y) - L x := by
  intro x y
  rw [shortInt_sum_split_filter f (fun n => n % q = r) x (x + y) (Nat.le_add_right x y)]
  constructor
  · have h1 := hL (x + y)
    have h2 := hB x
    linarith
  · have h1 := hB (x + y)
    have h2 := hL x
    linarith

/-- **Transfer with a real-argument bound shape.**  Same transfer as
`shortInt_transfer_of_monotone`, but the bound is a real-argument shape `G : ℝ → ℝ` evaluated
at casts, and the conclusion arrives with `↑(x+y)` already split as `(x : ℝ) + y` — the form in
which analytic estimates for `G` continue in ℝ.  Part of the glue toolkit for transferring
initial-segment divisor-sum bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_transfer_real_bound (f : ℕ → ℝ) (G : ℝ → ℝ) (q r : ℕ)
    (hf : ∀ n, 0 ≤ f n)
    (hB : ∀ N : ℕ, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r), f n ≤ G N) (x y : ℕ) :
    ∑ n ∈ (Finset.Ioc x (x + y)).filter (fun n => n % q = r), f n ≤ G ((x : ℝ) + y) := by
  have h := shortInt_transfer_of_nonneg f (fun N : ℕ => G N) (fun n => n % q = r) hf hB x y
  have hcast : ((x + y : ℕ) : ℝ) = (x : ℝ) + y := Nat.cast_add x y
  simpa only [hcast] using h

/-- **Instantiation-ready polylog shape, ℕ log-exponent.**  If the initial segments obey the
Shiu-type shape `∑_{n ≤ N, n % q = r} f n ≤ K·N/φ(q)·(1 + log N)^E`, then the short interval
`(x, x+y]` obeys the same shape at the right endpoint, with `↑(x+y)` already split as
`(x : ℝ) + y`.  Purely formal: instantiates `shortInt_transfer_real_bound`.  Part of the glue
toolkit for transferring initial-segment divisor-sum bounds to short intervals and to
`progressionSum`'s window. -/
lemma shortInt_transfer_polylog (f : ℕ → ℝ) (K : ℝ) (E q r : ℕ)
    (hf : ∀ n, 0 ≤ f n)
    (hB : ∀ N : ℕ, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r), f n
      ≤ K * N / (Nat.totient q : ℝ) * (1 + Real.log N) ^ E) (x y : ℕ) :
    ∑ n ∈ (Finset.Ioc x (x + y)).filter (fun n => n % q = r), f n
      ≤ K * ((x : ℝ) + y) / (Nat.totient q : ℝ) * (1 + Real.log ((x : ℝ) + y)) ^ E :=
  shortInt_transfer_real_bound f
    (fun t => K * t / (Nat.totient q : ℝ) * (1 + Real.log t) ^ E) q r hf hB x y

/-- **Instantiation-ready polylog shape, real log-exponent (`rpow`).**  Same statement as
`shortInt_transfer_polylog` with the logarithmic exponent `E : ℝ`.  Part of the glue toolkit
for transferring initial-segment divisor-sum bounds to short intervals and to
`progressionSum`'s window. -/
lemma shortInt_transfer_polylog_rpow (f : ℕ → ℝ) (K E : ℝ) (q r : ℕ)
    (hf : ∀ n, 0 ≤ f n)
    (hB : ∀ N : ℕ, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r), f n
      ≤ K * N / (Nat.totient q : ℝ) * (1 + Real.log N) ^ E) (x y : ℕ) :
    ∑ n ∈ (Finset.Ioc x (x + y)).filter (fun n => n % q = r), f n
      ≤ K * ((x : ℝ) + y) / (Nat.totient q : ℝ) * (1 + Real.log ((x : ℝ) + y)) ^ E :=
  shortInt_transfer_real_bound f
    (fun t => K * t / (Nat.totient q : ℝ) * (1 + Real.log t) ^ E) q r hf hB x y

/-! ## `progressionSum` glue -/

/-- Definitional unfold of `progressionSum` as a filtered initial-segment sum over the window
`[1, ⌈2P⌉₊]`.  Part of the glue toolkit for transferring initial-segment divisor-sum bounds to
short intervals and to `progressionSum`'s window. -/
@[simp] lemma shortInt_progressionSum_eq (c : ℕ → ℝ) (P : ℝ) (q r : ℕ) :
    progressionSum c P q r
      = ∑ p ∈ (Finset.Icc 1 ⌈2 * P⌉₊).filter (fun p => p % q = r % q), |c p| := rfl

/-- An initial-segment bound for `∑_{n ≤ N, n ≡ r (q)} |c n|` evaluates `progressionSum`'s
window at `N = ⌈2P⌉₊`.  Part of the glue toolkit for transferring initial-segment divisor-sum
bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_progressionSum_le_of_bound (c : ℕ → ℝ) (B : ℕ → ℝ) (P : ℝ) (q r : ℕ)
    (hB : ∀ N : ℕ, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q), |c n| ≤ B N) :
    progressionSum c P q r ≤ B ⌈2 * P⌉₊ := by
  rw [shortInt_progressionSum_eq]
  exact hB ⌈2 * P⌉₊

/-- Numeric window bridge, upper half: `⌈2P⌉₊ ≤ 2P + 1` in ℝ, for `P ≥ 0`.  Part of the glue
toolkit for transferring initial-segment divisor-sum bounds to short intervals and to
`progressionSum`'s window. -/
lemma shortInt_ceil_le_two_mul_add_one (P : ℝ) (hP : 0 ≤ P) :
    ((⌈2 * P⌉₊ : ℕ) : ℝ) ≤ 2 * P + 1 :=
  (Nat.ceil_lt_add_one (by linarith)).le

/-- Numeric window bridge: `⌈2P⌉₊ ≤ 2P + 1 ≤ 3P` in ℝ, for `P ≥ 1`, packaged so that
`B`-monotonicity arguments can continue in ℝ.  Part of the glue toolkit for transferring
initial-segment divisor-sum bounds to short intervals and to `progressionSum`'s window. -/
lemma shortInt_ceil_window_bridge (P : ℝ) (hP : 1 ≤ P) :
    ((⌈2 * P⌉₊ : ℕ) : ℝ) ≤ 2 * P + 1 ∧ 2 * P + 1 ≤ 3 * P :=
  ⟨shortInt_ceil_le_two_mul_add_one P (by linarith), by linarith⟩

/-- Numeric window bridge, composed form: `⌈2P⌉₊ ≤ 3P` in ℝ, for `P ≥ 1`.  Part of the glue
toolkit for transferring initial-segment divisor-sum bounds to short intervals and to
`progressionSum`'s window. -/
lemma shortInt_ceil_le_three_mul (P : ℝ) (hP : 1 ≤ P) :
    ((⌈2 * P⌉₊ : ℕ) : ℝ) ≤ 3 * P :=
  le_trans (shortInt_ceil_window_bridge P hP).1 (shortInt_ceil_window_bridge P hP).2

/-- Numeric window bridge, lower half: `2P ≤ ⌈2P⌉₊` in ℝ.  Part of the glue toolkit for
transferring initial-segment divisor-sum bounds to short intervals and to `progressionSum`'s
window. -/
lemma shortInt_two_mul_le_ceil (P : ℝ) :
    2 * P ≤ ((⌈2 * P⌉₊ : ℕ) : ℝ) :=
  Nat.le_ceil _

/-- The window `⌈2P⌉₊` is a positive length for `P ≥ 1`.  Part of the glue toolkit for
transferring initial-segment divisor-sum bounds to short intervals and to `progressionSum`'s
window. -/
lemma shortInt_ceil_window_pos (P : ℝ) (hP : 1 ≤ P) : 0 < ⌈2 * P⌉₊ :=
  Nat.ceil_pos.mpr (by linarith)

/-- **`progressionSum` under a real-argument majorant.**  If the initial segments obey
`∑_{n ≤ N, n ≡ r (q)} |c n| ≤ B ↑N` for a bound function `B : ℝ → ℝ` monotone on `[0, ∞)`,
then `progressionSum c P q r ≤ B (3P)` for `P ≥ 1` — the ℝ-side continuation of the window
bridge.  Part of the glue toolkit for transferring initial-segment divisor-sum bounds to short
intervals and to `progressionSum`'s window. -/
lemma shortInt_progressionSum_le_of_real_bound (c : ℕ → ℝ) (B : ℝ → ℝ) (P : ℝ) (q r : ℕ)
    (hP : 1 ≤ P)
    (hB : ∀ N : ℕ, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r % q), |c n| ≤ B N)
    (hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → B s ≤ B t) :
    progressionSum c P q r ≤ B (3 * P) := by
  have h1 : progressionSum c P q r ≤ B ((⌈2 * P⌉₊ : ℕ) : ℝ) := by
    rw [shortInt_progressionSum_eq]
    exact hB ⌈2 * P⌉₊
  refine h1.trans (hmono _ _ (Nat.cast_nonneg _) ?_)
  exact shortInt_ceil_le_three_mul P hP

/-! ## Axiom audit -/

#print axioms shortInt_cast_div_lower
#print axioms shortInt_multiples_card
#print axioms shortInt_multiples_le
#print axioms shortInt_multiples_ge
#print axioms shortInt_ap_card_le
#print axioms shortInt_ap_card_ge
#print axioms shortInt_Icc_split
#print axioms shortInt_Icc_disjoint
#print axioms shortInt_sum_split
#print axioms shortInt_sum_split_filter
#print axioms shortInt_transfer_of_nonneg
#print axioms shortInt_transfer_of_monotone
#print axioms shortInt_transfer_sub
#print axioms shortInt_transfer_sandwich
#print axioms shortInt_transfer_real_bound
#print axioms shortInt_transfer_polylog
#print axioms shortInt_transfer_polylog_rpow
#print axioms shortInt_progressionSum_eq
#print axioms shortInt_progressionSum_le_of_bound
#print axioms shortInt_ceil_le_two_mul_add_one
#print axioms shortInt_ceil_window_bridge
#print axioms shortInt_ceil_le_three_mul
#print axioms shortInt_two_mul_le_ceil
#print axioms shortInt_ceil_window_pos
#print axioms shortInt_progressionSum_le_of_real_bound

end Shiu
end Zeta85
end RH
