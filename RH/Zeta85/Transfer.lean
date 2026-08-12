/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Transfer.lean — the **two-trace certificate** interface and its (fully proved) conversion
into the repository's ε-form.  No axioms, no `sorry`: this file is the load-bearing derivation that
turns the prime-side hypotheses of `RH/Zeta85/Hypotheses.lean` into the statements of
`RH/Zeta85/Statement.lean`.

## What the interface records

`TwoTraceData Z D trGh frGh err` says that a zero configuration `Z` carries, at every large height
`T`, a Gram matrix in hat units whose real trace is `trGh T`, whose squared Frobenius norm is
`frGh T`, and for which

  (zeroSide)  `4·tr Ĝ − ‖Ĝ‖²_F − 2·N(T,2T) − err T ≤ N₀ˢ(T,2T)`,
  (trace1)    `tr Ĝ = N(T,2T)·(1 + o(1))`,
  (trace2)    `‖Ĝ‖²_F ≤ (D + o(1))·N(T,2T)`,
  (errSmall)  `err T = o(N(T,2T))`.

`zeroSide` is **exactly** the shape of the repository's Seam A,
`Zeta23.Assembly.seamA_mult2` (`Zeta23/Assembly/SeamMult.lean:46`):

  `4·rtrace Ĝ − frobSq Ĝ − 2·N − 3·N_II − B·(4 + 2·√(frobSq Ĝ) + B) ≤ N₀ˢ`,

with `err T := 3·N_II(T) + B·(4 + 2·√(frobSq Ĝ) + B)`; `seamA_shape` below records that this is a
literal rearrangement.  Seam A is proved in the base repository for an *arbitrary* `Zeta23.Params`
family: it consumes only `PhiHatConj`, `PhiHatReal`, `PoissonSq` and `TailInputs`, none of which
mentions `λ ≤ 1` (the Poisson identity `Zeta23/Poisson.lean:367` needs only `TaperProfile ϱ`,
`0 < w`, `2w ≤ L`).  The restriction `λ ≤ 1` of `Zeta23.Params.Valid` lives entirely on the prime
side and in the error bookkeeping `Zeta23.Params.calE`.  That is why the 85 % axiom set is
prime-side only; see `docs/REUSE_MAP.md` §6.

## The two derivations

* `epsForm_of_twoTraceCert` — the trace algebra, mirroring `Zeta23.ThmD.N0star_lower_c`
  (`Zeta23/ThmD/AssemblyD.lean:41`), and routed through the **count lemma of Phase A3**
  (`RH.Zeta85.count_lemma`, `01_hybrid_cycle1.md` (1)–(3)) so that the linear-programming step of
  the source is the step actually taken: put `s := N₀ˢ`, `d := (N − s)/2`, `p := 0`, so that
  `s + 2d + 2p = N` and the certificate supplies `3s + 4d + 4p ≥ (4 − D − ε)N`.
* `epsForm_of_countCert` — the same conclusion directly from the source's linear program, for the
  reader who prefers `01_hybrid_cycle1.md` (1)–(2) as the interface.
-/
import RH.Zeta85.Certificate
import Zeta23.Assembly.SeamMult
import Zeta23.Defs.Counting

open Filter Topology

noncomputable section

namespace RH
namespace Zeta85

open Zeta23

/-! ## 1. The interface -/

/-- The two-trace certificate data at normalized Frobenius cost `D`, for the dyadic windows
`(T, 2T]` of a zero configuration `Z`.  See the module docstring. -/
structure TwoTraceData (Z : ZeroConfig) (D : ℝ) (trGh frGh err : ℝ → ℝ) : Prop where
  /-- Seam A: `4·tr Ĝ − ‖Ĝ‖²_F − 2N − err ≤ N₀ˢ` (`Zeta23.Assembly.seamA_mult2`). -/
  zeroSide : ∀ᶠ T in atTop,
    4 * trGh T - frGh T - 2 * (Z.N T (2 * T) : ℝ) - err T ≤ (Z.N0s T (2 * T) : ℝ)
  /-- `tr Ĝ = N + o(N)` — the paper's [eq:tr1] at this support. -/
  trace1 : ∀ ε > 0, ∀ᶠ T in atTop,
    |trGh T - (Z.N T (2 * T) : ℝ)| ≤ ε * (Z.N T (2 * T) : ℝ)
  /-- `‖Ĝ‖²_F ≤ (D + o(1))·N` — the second-moment budget at this support. -/
  trace2 : ∀ ε > 0, ∀ᶠ T in atTop, frGh T ≤ (D + ε) * (Z.N T (2 * T) : ℝ)
  /-- the tail/`N_II` remainder is `o(N)`. -/
  errSmall : ∀ ε > 0, ∀ᶠ T in atTop, err T ≤ ε * (Z.N T (2 * T) : ℝ)

/-- `Z` admits a two-trace certificate at normalized cost `D`. -/
def TwoTraceCert (Z : ZeroConfig) (D : ℝ) : Prop :=
  ∃ trGh frGh err : ℝ → ℝ, TwoTraceData Z D trGh frGh err

/-- The certificate is monotone in the cost: a certificate at cost `D` is one at any larger cost. -/
theorem TwoTraceCert.mono {Z : ZeroConfig} {D D' : ℝ} (h : TwoTraceCert Z D) (hD : D ≤ D') :
    TwoTraceCert Z D' := by
  obtain ⟨trGh, frGh, err, hdata⟩ := h
  refine ⟨trGh, frGh, err, ⟨hdata.zeroSide, hdata.trace1, ?_, hdata.errSmall⟩⟩
  intro ε hε
  filter_upwards [hdata.trace2 ε hε] with T hT
  refine hT.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

/-- **Seam A has exactly the `zeroSide` shape.**  Writing `err := 3·N_II + B·(4 + 2√frGh + B)`, the
left-hand side of `Zeta23.Assembly.seamA_mult2` is `4·trGh − frGh − 2N − err`.  (A rearrangement;
recorded so that the reader can check the interface against the base repository's seam without
re-deriving it.) -/
theorem seamA_shape (trGh frGh N NII B : ℝ) :
    4 * trGh - frGh - 2 * N - 3 * NII - B * (4 + 2 * Real.sqrt frGh + B)
      = 4 * trGh - frGh - 2 * N - (3 * NII + B * (4 + 2 * Real.sqrt frGh + B)) := by
  ring

/-! ## 2. The derivation, through the Phase-A3 count lemma -/

/-- **The main derivation.**  A two-trace certificate at cost `D` yields the repository's ε-form
`∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 − D − ε)·N(T,2T) ≤ N₀ˢ(T,2T)`.

The linear-programming step is `RH.Zeta85.count_lemma` (Phase A3, `01_hybrid_cycle1.md` (1)–(3))
applied with `s := N₀ˢ(T,2T)`, `d := (N − s)/2`, `p := 0`, which is legitimate because
`N₀ˢ ≤ N` (`Zeta23.ZeroConfig.trivial_chain`). -/
theorem epsForm_of_twoTraceCert {Z : ZeroConfig} {D : ℝ} (h : TwoTraceCert Z D) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - D - ε) * (Z.N T (2 * T) : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) := by
  obtain ⟨trGh, frGh, err, hdata⟩ := h
  intro ε hε
  set δ : ℝ := ε / 6 with hδdef
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ T in atTop,
      (2 - D - ε) * (Z.N T (2 * T) : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hdata.zeroSide, hdata.trace1 δ hδ, hdata.trace2 δ hδ, hdata.errSmall δ hδ]
      with T hzs h1 h2 h3
    set N : ℝ := (Z.N T (2 * T) : ℝ) with hN
    set s : ℝ := (Z.N0s T (2 * T) : ℝ) with hs
    have hN0 : 0 ≤ N := Nat.cast_nonneg _
    have hs0 : 0 ≤ s := Nat.cast_nonneg _
    -- N₀ˢ ≤ N, so the adversarial population d := (N − s)/2 is admissible
    have hsN : s ≤ N := by
      have := (Z.trivial_chain T (2 * T)).1.trans
        ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
      rw [hs, hN]
      exact_mod_cast this
    -- unpack the two trace bounds
    have htr : N - δ * N ≤ trGh T := by
      have := (abs_le.mp h1).1; linarith
    -- the certificate's charge, in the form the count lemma consumes
    have hcharge : (4 - (D + 6 * δ)) * N ≤ 3 * s + 4 * ((N - s) / 2) + 4 * 0 := by
      have hzs' : 4 * trGh T - frGh T - 2 * N - err T ≤ s := hzs
      have : 3 * s + 4 * ((N - s) / 2) + 4 * 0 = s + 2 * N := by ring
      rw [this]
      nlinarith [htr, h2, h3, hN0]
    have hcount := count_lemma (s := s) (d := (N - s) / 2) (p := 0) (N := N) (C := D + 6 * δ)
      hs0 (by linarith) le_rfl (by linarith) hcharge
    have : (2 - D - ε) = (2 - (D + 6 * δ)) := by rw [hδdef]; ring
    rw [this]
    exact hcount
  exact eventually_atTop.mp hev

/-! ## 3. The same conclusion from the source's linear program -/

/-- The linear-programming form of the certificate, i.e. `01_hybrid_cycle1.md` (1)–(2) verbatim:
populations `s ≤ N₀ˢ`, `d`, `p ≥ 0` with `s + 2d + 2p ≤ N` and `3s + 4d + 4p ≥ (4 − D − o(1))N`. -/
structure CountData (Z : ZeroConfig) (D : ℝ) (s d p : ℝ → ℝ) : Prop where
  s_nonneg : ∀ T, 0 ≤ s T
  d_nonneg : ∀ T, 0 ≤ d T
  p_nonneg : ∀ T, 0 ≤ p T
  s_le : ∀ᶠ T in atTop, s T ≤ (Z.N0s T (2 * T) : ℝ)
  /-- `N ≥ s + 2d + 2p`  [01_hybrid_cycle1.md (1)]. -/
  multCount : ∀ᶠ T in atTop, s T + 2 * d T + 2 * p T ≤ (Z.N T (2 * T) : ℝ)
  /-- `3s + 4d + 4p ≥ (4 − D − ε)N`  [01_hybrid_cycle1.md (2)]. -/
  charge : ∀ ε > 0, ∀ᶠ T in atTop,
    (4 - D - ε) * (Z.N T (2 * T) : ℝ) ≤ 3 * s T + 4 * d T + 4 * p T

/-- `Z` admits the linear-programming certificate at cost `D`. -/
def CountCert (Z : ZeroConfig) (D : ℝ) : Prop := ∃ s d p : ℝ → ℝ, CountData Z D s d p

/-- **The linear program gives the same ε-form** — `01_hybrid_cycle1.md` (3). -/
theorem epsForm_of_countCert {Z : ZeroConfig} {D : ℝ} (h : CountCert Z D) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - D - ε) * (Z.N T (2 * T) : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) := by
  obtain ⟨s, d, p, hdata⟩ := h
  intro ε hε
  have hev : ∀ᶠ T in atTop,
      (2 - D - ε) * (Z.N T (2 * T) : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hdata.s_le, hdata.multCount, hdata.charge ε hε] with T hle h1 h2
    have hcount := count_lemma (C := D + ε) (hdata.s_nonneg T) (hdata.d_nonneg T)
      (hdata.p_nonneg T) h1 (by convert h2 using 2; ring)
    have : (2 - D - ε) = (2 - (D + ε)) := by ring
    rw [this]
    exact hcount.trans hle
  exact eventually_atTop.mp hev

/-! ## 4. Numerical corollary at the 85 % certificate -/

/-- At `D = D_pc` the ε-form constant is exactly `1893603832049143/2227707598259143`
[01_certificate_cycle1.md (11)]. -/
theorem epsForm_at_DPC {Z : ZeroConfig} (h : TwoTraceCert Z DPC) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1893603832049143 / 2227707598259143 - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  simpa only [two_sub_DPC] using epsForm_of_twoTraceCert h

end Zeta85
end RH

end
