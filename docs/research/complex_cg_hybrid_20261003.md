# A hybrid route to the complex Cheer–Goldston inequality (**)

Research note, 2026-10-03. Companion script
[`verify/complex_cg_hybrid.py`](../../verify/complex_cg_hybrid.py) (output
`verify/complex_cg_hybrid.out`, default run about 4 minutes on 4 cores). Builds on
[`positivity_class_20261003.md`](positivity_class_20261003.md) (definitions of (**),
Σ_Z, Lemma 0, Prop. 2, Prop. 4), [`complex_cg_proof_20261003.md`](complex_cg_proof_20261003.md)
(the certified test ρ, identity (1.1), Theorems 1–4) and
[`complex_cg_adversary_20261003.md`](complex_cg_adversary_20261003.md). Labels: PROVED
(complete argument here), CHECKED (computation with explicit error allowances, floating
point), NUMERICAL (optimisation without certificate), CONJECTURE, REFUTED.

Throughout, ρ is the certified test of the proof memo: P(ρ) = 1.3210847, R = ∫ρ = 1.0124602,
ρ(0) = 1.004442, r = r_in − s ≥ 0 on **R** (CHECKED), κ = r(0) = 1. Target: (**) with κ'
for all finite conjugation-invariant Z beats the frontier 0.6725162800 iff
κ' > P/(2 − 0.67251628) = **0.995180**.

## 0. Summary

* **The Lemma-R split, quantified (Prop. 2.1, CHECKED).** The largest autocorrelation
  σ* = φ*⋆φ̃* (φ* ≥ 0 on [−1/2, 1/2]) found below ρ has ∫σ* = **0.987962**; it equals ρ on
  |α| ≥ 0.75 and at α = 0. The remainder ρ_r = ρ − σ* ≥ 0 is a bump of mass 0.0245 supported
  in |α| ≤ 0.72, with **ρ_r(0) = 0**. Lemma R then gives (**) with κ = 0.987962 for *every*
  Z at *every* height (PROVED), i.e. 0.662819, below Montgomery–Taylor. A column-generation
  LP over mixtures of autocorrelations does not improve 0.987962 (NUMERICAL).
* **Barriers for the hybrid (Props. 2.3–2.6, PROVED).** (i) Any mixture of autocorrelations
  below ρ has mass ≤ P(ρ)/c_MT = 0.995168 < 0.995180: Lemma R plus positivity can never reach
  the frontier, and with the actual split an all-height proof must find **0.00722 per unit
  cost** beyond Lemma R. (ii) The remainder alone carries no real constant (κ_real(ρ_r) = 0),
  so the Cheer–Goldston excess is entirely an interaction effect. (iii) Mechanism (b), "high
  pairs are paid by Lemma R, everything else at κ = 1", gives at worst
  (2 − P − ε)/(1 − ε) = 0.670994 (ε = 0.02408). It beats the frontier only if κ_H > 0.99023,
  or if fewer than 26.6 % of the zeros lie in high pairs. (iv) Putting the remainder on
  [−a, a] stretches Theorem 4's height range by 1/a, but beats the frontier only for
  a > 0.98661 (bandwidth-one ceiling) or a > 0.7533 (unconditionally, via Lemma 4). The
  stretch is therefore at most 1.4 %.
* **No per-pair height surplus exists (Section 3, PROVED).** A unit lattice of pairs at a
  common height v has Σ/cost = ρ(0) = 1.004442 for *every* v. It also exerts *zero lifting
  field* on any real atom (Poisson summation plus ρ(±1) = 0). For the triangle test, Lemma R
  is exactly tight on these lattices at every height. So a localized Lemma R with a
  height-growing surplus per pair (mechanism (a)) is REFUTED. Any cosh surplus depends on the
  configuration, and pairs near other pairs can be as tight as real atoms.
* **Theorem H1 (new, PROVED modulo CHECKED constants).** For the certified ρ and κ = 1, (**)
  holds for every Z made of arbitrary real atoms (any multiplicities, any clustering) plus
  **one conjugate pair of any multiplicity at any height v > 0**. The pair's cosh-amplified
  self-excess pays every interaction with the real environment. The proof is a cell-packing
  bound with integer penalties, swept rigorously over v ∈ [0.0795, 20] (918 intervals,
  certified ratio ≤ 0.950), plus an analytic Plancherel bound for v ≥ 20 (≤ 0.765, decreasing)
  and Theorem 4 for v ≤ 0.08. This is the first all-height result in which an off-line pair
  coexists with arbitrary real zeros. Mechanism (b) therefore works pair-against-reals; what
  remains is pair against pair at unequal heights.
* **Targeted adversary (NUMERICAL).** 9 600 local optimisations (28 800 in `full` mode) with
  pairs forced to v ∈ [v_lo, 0.6], embedded in near-tight real designs with dense clusters,
  heavy neighbours, doubles and pair lattices, up to 104 atoms per period. **No violation.**
  The minimum excess per mid-height pair is 0.0178 = 4(ρ(0) − 1) at every v_lo, attained by
  pair lattices. Lifted near-tight designs reach 0.029–0.40 and single pairs in real designs
  0.06–3.1. The minimum ratio among configurations containing such a pair is 1.0013–1.0045.
* **No unconditional proportion above 0.6725162800 is obtained.** (**) for several pairs at
  unequal middle heights remains open.

## 1. Notation

Atoms j have positions x_j, heights v_j ≥ 0 and weights W_j. A real atom of multiplicity m
has W = m and cost 1 (m = 1) or 2m. A pair x ± iv of multiplicity m has W = 2m and cost 4m.
Write c_j(α) = cosh(2παv_j) and

  Σ_Z(ρ) = ∫ρ |Σ_j W_j c_j(α) e(αx_j)|² dα,
  Q_v(x) = ∫ρ(α)(cosh(2παv) − 1) cos(2παx) dα,  X(v) = ∫ρ sinh²(2παv),  G_v = r + Q_v.

For a split ρ = σ + ρ_r with σ an autocorrelation φ⋆φ̃ (φ ≥ 0, supported in an interval of
length ≤ 1), Lemma 0 and Lemma R give Σ_Z(ρ) = Σ_Z(σ) + Σ_Z(ρ_r) ≥ ∫σ·(2N − s₁) + Σ_Z(ρ_r)
for every Z (parent memo, Prop. 4). This holds for all heights.

## 2. The split and its limits

**Proposition 2.1 (CHECKED).** Let φ* be the piecewise-constant function on the 0.01 grid of
[−1/2, 1/2] computed in Part 1 of the script. Then σ* = φ*⋆φ̃* ≤ ρ on [−1, 1] and
∫σ* = (∫φ*)² = 0.987962. Both σ* and ρ are piecewise linear on the same nodes k/100, so the
inequality is exactly the 101 node inequalities, and these hold after a scaling by
1 − 10⁻¹². The remainder ρ_r = ρ − σ* is ≥ 0 and has ∫ρ_r = 0.024498. It satisfies
ρ_r(0) = 2·10⁻¹² and ρ_r = 0 for |α| ≥ 0.72, with maximum 0.0345 at |α| = 0.21. Also
σ*(0) = ρ(0), Var(φ*) = σ*(0) − ∫σ* = 0.016479, and P(σ*)/∫σ* = 1.330655.

**Corollary 2.2 (PROVED).** For every finite conjugation-invariant Z, with no height
restriction, Σ_Z(ρ) ≥ 0.987962 (2N − s₁). This is the all-height floor of the hybrid route:
2 − P/0.987962 = 0.662819.

*Optimality of the split (NUMERICAL).* SLSQP from several starts returns the same value.
Column generation over the convex cone of autocorrelations stalls at 0.987962. The initial
columns are indicators, cosine powers, the Montgomery–Taylor profile and φ*; the script runs
25 pricing rounds and a longer scratch run 80, with the same result.

**Proposition 2.3 (PROVED; Lemma R cannot reach the frontier).** Let σ be any finite
positive combination of autocorrelations φ_i⋆φ̃_i (φ_i ≥ 0, each supported in an interval
of length ≤ 1) with σ ≤ ρ. Then ∫σ ≤ P(ρ)/c_MT = 0.995168, where
c_MT = 1/2 + 2^{−1/2}cot 2^{−1/2} = 1.3274993.

*Proof.* Each r_i = |φ̂_i|² ≥ 0 has r̂_i supported in [−1, 1]. Montgomery–Taylor's extremal
problem gives P(r̂_i) ≥ c_MT r_i(0) = c_MT ∫φ_i⋆φ̃_i. Sum these, and use
P(ρ) − P(σ) = P(ρ − σ) ≥ 0 for the nonnegative function ρ − σ. □

Since 0.995168 < 0.995180, no choice of split makes Lemma R alone sufficient. With the split
actually available, the remaining obligation for κ' = 0.995180 is

  Σ_Z(ρ_r) + [Σ_Z(σ*) − 0.987962 (2N − s₁)] ≥ 0.00722 (2N − s₁)  for all Z,       (2.1)

and 0.01204 for κ' = 1. The bracket is the Lemma-R slack. It vanishes when the vectors
e_z = √φ* e(z·) are orthonormal, for example two simple real atoms at a zero of |φ̂*|².
There ρ_r pays alone; for the full ρ such configurations have ratio R + r_in(d) ≥ 1.0077.

**Proposition 2.4 (PROVED; the remainder carries no real constant).** κ_real(ρ_r) ≤ ρ_r(0)
by Lemma 4 of the adversary memo (lattices of spacing below 1 see only α = 0), so
κ_real(ρ_r) = 0. Hence (2.1) cannot be split as "Lemma R for σ*, a Cheer–Goldston argument
for ρ_r". The 0.012 excess of the real case lives in the interaction between the Lemma-R
slack and ρ_r. This sharpens Prop. 4 of the parent memo: the Cheer–Goldston gain over
Montgomery–Taylor is invisible to every split.

**Proposition 2.5 (PROVED; mechanism (b) at face value).** Suppose one could show
Σ_Z(ρ) ≥ cost(non-high part) + κ_H·cost(high pairs), with high pairs charged only the
Lemma-R constant. For zeta, Prop. 2 of the parent memo gives 2N − s₁ ≤ NP + ε N_H with
ε = 2(1 − κ_H), where N_H is the number of zeros in high pairs. Since N_H ≤ N − s₁, this
yields s₁/N ≥ (2 − P − ε)/(1 − ε). With κ_H = 0.987962 that is 0.670994, below
Montgomery–Taylor. The frontier is beaten iff κ_H > 0.99023, or iff N_H/N < 0.2658. No
density theorem gives the latter at scale |β − 1/2| ≍ 1/log T. So the high pairs must be
charged at least 0.99023, i.e. at least 0.0091 per simple pair more than Lemma R gives.

**Proposition 2.6 (PROVED; localized splits, mechanism (a) variant).** Suppose ρ_r is
supported in [−a, a] and write ρ̃(β) = ρ_r(aβ). Then Σ_Z(ρ_r) = a Σ_{aZ}(ρ̃), and scaling
leaves costs unchanged. So a Theorem-4-type certificate for ρ̃ up to height V₀ covers ρ_r up
to height V₀/a, and Lemma R covers σ at every height: this is the hybrid in its cleanest form.
The price: κ_real(ρ_r) = a κ_real(ρ̃) ≤ a ρ̃(0), while P(ρ_r) = ρ̃(0) + a²∫|β|ρ̃. Hence

  P(ρ_r)/κ_r ≥ min over the CG class of [1 + (c_CG − 1)a²]/a,

and P(σ)/∫σ ≥ c_MT. To beat the frontier one needs [1 + (c_CG − 1)a²]/a < 1.3274837. The
three available values of c_CG give

* a > 0.7533 unconditionally (c_CG ≥ 1, from Lemma 4);
* a > 0.98661 using the repository's bandwidth-one ceiling 0.6818287 (c_CG ≥ 1.3181713,
  under that theorem's hypothesis EnclOK and up to its stated smoothness correction);
* a > 0.99051 using the LP value 1.32095 (NUMERICAL).

The height range of Theorem 4 can therefore grow by at most a factor 1.0136, i.e. from
0.0796 to 0.081. The Cheer–Goldston gain needs the remainder at the edge of the band, which
is exactly where cosh amplification is strongest.

**Remark (mechanism (c)).** A rank–inertia formulation of the Cheer–Goldston slack would be
a positive-semidefinite certificate. The real-case slack Σ_{j≠k}W_jW_k r(Δ_jk) is
*entrywise*, not spectral. Theorem 2 of the proof memo shows that no "nonnegative + PSD"
kernel on the half-plane exists, and Prop. 2.3 shows that every PSD (autocorrelation) part
stops at Montgomery–Taylor. A Lemma-R-style operator argument can therefore handle only the
σ part. Using the off-band test on the real part alone means treating the real atoms by
r ≥ 0 and the pairs by something else; Section 4 does exactly this for one pair.

## 3. Pair lattices: no per-pair height surplus

**Lemma 3.1 (PROVED).** Let ρ be even, continuous, supported in [−1, 1], with ρ(±1) = 0.
Take the unit lattice of pairs {n ± iv : n ∈ **Z**}, multiplicity m, any v ≥ 0. Its periodic
ratio is Σ/cost = ρ(0), so each pair has excess 4m²(ρ(0) − 1) whatever its height.

*Proof.* The period-1 sum is T(α) = 2m cosh(2παv) and only the frequencies α ∈ **Z** occur
(Lemma 1 of the adversary memo). In [−1, 1] these are 0 and ±1, where ρ vanishes at ±1.
Hence Σ per period = ρ(0)·4m² and cost = 4m. □

For the certified ρ the ratio is 1.004442 and the excess per simple pair is 0.0178.

**Lemma 3.2 (PROVED; zero lifting field).** For every real x and v,
Σ_{n∈**Z**} Q_v(x − n) = 0.

*Proof.* By Poisson summation the sum is Σ_k f_v(k) e(kx) with f_v = ρ(cosh(2παv) − 1).
Here f_v(0) = 0 and f_v(±1) = 0. □

So a real atom feels no net lifting force from a unit pair lattice at any height. The
script's truncated sums at v = 0.6 are O(10⁻⁴), against Q_v(0.5) = −0.487.

**Corollary 3.3 (REFUTED: per-pair surplus in Lemma R).** Let σ = (1 − |α|)₊ = φ⋆φ̃ with
φ = 1_{[−1/2,1/2]}, so ∫σ = 1. On the pair lattice of Lemma 3.1, Σ_Z(σ)/cost = σ(0) = 1 at
every height. Lemma R is therefore exactly tight on configurations of arbitrarily high pairs,
and no inequality Σ_Z(σ) ≥ ∫σ·cost + Σ_k θ(v_k) with θ > 0 can hold. For σ* the slack on the
lattice is Var(φ*) per unit cost, independent of height.

*Consequence.* A proof of (**) must use the self-excess X(v) of a pair only against
neighbours that do not form real-like structures with it. Against real atoms this works
(Section 4). Against other pairs it cannot work termwise: in a common-height lattice the
pair–pair bonds cancel the self-excess exactly, so those configurations must be reduced to
the real case, as in Prop. 5(ii) of the parent memo.

## 4. Theorem H1: one pair of any height among arbitrary real zeros

**Theorem H1 (PROVED modulo the CHECKED constants).** Let ρ be the certified test and
κ = r(0) = 1. Let Z consist of finitely many real atoms with arbitrary positive integer
multiplicities and one conjugate pair x₀ ± iv of multiplicity m ≥ 1, with v > 0. Then
Σ_Z(ρ) ≥ 2N − s₁.

For v ≤ 0.08 this is a special case of Theorem 4 of the proof memo. The proof below covers
v ≥ 0.0795.

**Step 1 (identity, PROVED; checked numerically to 10⁻¹⁴).** Put x₀ = 0. Let Z₀ be the
real multiset with the pair collapsed to a real atom of weight 2m. Using r_in = r + s and
κ = R − s(0) = 1,

  Σ_Z(ρ) − cost(Z) = Σ_j (W_j² − cost_j) + Σ_{j≠k} W_jW_k r(x_j − x_k)
                    + 4m Σ_j W_j G_v(x_j) + 4m² X(v) + 4m(m − 1) + ∫ŝ|S_{Z₀}|²,      (4.1)

where the sums run over the real atoms. The only negative terms are the field terms
4mW_jG_v(x_j) with G_v(x_j) < 0.

**Step 2 (reduction).** Drop ∫ŝ|S_{Z₀}|² ≥ 0. Every real atom with G_v(x_j) ≥ 0 contributes
only nonnegative terms (r ≥ 0), so remove it. G_v ≥ 0 on [−1/4, 1/4], because Q_v ≥ 0 there.
Partition the rest of the line into cells c of diameter d_c and drop the r-terms between
different cells. Inside a cell all mutual distances are ≤ d_c, so r ≥ ρ_c := min_{[0,d_c]} r.
For atoms of weights W_j in a cell with total weight w,

  Σ(W_j² − cost_j) + ρ_c(w² − ΣW_j²) ≥ pen_c(w) := ρ_c(w² − 2w) + [w = 1]ρ_c + [w odd ≥ 3] min(ρ_c, 3 − 3ρ_c).

This is the exact minimum over partitions: doubles are optimal, plus one simple atom or one
triple when w is odd. With g_c ≥ sup_c(−G_v)₊, the cell contributes at least −Ψ_c(m g_c),
where Ψ_c(y) = max_{w∈**Z**≥0}(4yw − pen_c(w)). It suffices that

  Σ_c Ψ_c(m g_c) ≤ 4m² X(v) + 4m(m − 1).                                              (4.2)

Two facts about Ψ_c (PROVED): Ψ_c(y) = 8y for y ≤ min(ρ_c, 3/4), and
Ψ_c(y) ≤ 4y²/ρ_c + 8y for all y. So (4.2) for all m ≥ 2 follows from
A₂/(4X) + A₁/(8X) ≤ 1, with A₂ = Σ_c 4g_c²/ρ_c and A₁ = Σ_c 8g_c over both sides. The case
m = 1 is checked with the exact Ψ_c.

**Step 3 (certified sweep, CHECKED).** For each interval [v₀, v₁]:

* **Exact field.** Q_{v₀} and Q′_{v₀} are computed in closed form, since ρ is piecewise
  linear: ∫_0^1 ρ e^{λα} = −ρ(0)/λ + λ^{−2}[s₀ − s₉₉e^λ + Σ j_k e^{λα_k}]. They agree with
  40-digit quadrature to 3·10⁻¹⁴ relative, and a rounding allowance of 10⁻¹³ times the sum of
  moduli is added. r and r′ come from the jump representation.
* **Grid in x.** h = 10⁻³ on [1/4, X_F], with X_F = 60 for v < 1/2 and 20 beyond, and a
  second-order Taylor bound on each grid cell, |F″| ≤ ‖r″‖ + 4π²∫α²ρ(cosh − 1).
* **Uniformity in v.** |∂_v Q_v(x)| ≤ min(∫2π|α|ρ sinh(2παv₁), TV((ρ g)′)/(4π²x²)) with
  g = ∂_v(cosh(2παv) − 1), together with X(v) ≥ X(v₀).
* **Cells.** The components of {G < 0} (certified) cut into pieces of length
  ≤ ℓ ∈ {0.5, 0.6, 0.7}, with ρ_c a certified lower bound for min_{[0,d]} r.
* **Tail.** On |x| > X_F use cells of length 1/2 or 1 and g ≤ T(v₁)/x², with
  T = TV((ρ(cosh − 1))′)/(4π²).

Result: 918 contiguous intervals cover [0.0795, 20]. The largest certified left side of
(4.2) divided by its right side, per range:

| v | max ratio (m = 1) | max ratio (all m ≥ 2) |
|---|---|---|
| [0.08, 0.13) | 0.944 | 0.476 |
| [0.13, 0.25) | 0.937 | 0.496 |
| [0.25, 0.40) | 0.945 | 0.784 |
| [0.40, 0.60) | 0.949 | 0.842 |
| [0.60, 1) | 0.949 | 0.871 |
| [1, 2) | 0.948 | 0.948 |
| [2, 20) | 0.950 | 0.950 |

The values near 0.95 are an artefact of the adaptive step, which enlarges the v-intervals
until the ratio reaches 0.95. At fixed v the bound is 0.85–0.94 for v ≤ 0.4 and decays like
0.35/v beyond.

**Step 4 (v ≥ 20, analytic, PROVED with computed constants).** Use cells of length 1/2
starting at 1/4, so ρ_c ≥ rmin(1/2) = 0.4710. Bound g_c ≤ sup_c|Q_v|, using r ≥ 0. Then

  Σ_c sup_c Q_v² ≤ 2‖Q_v‖₂² + 2‖Q_v‖₂‖Q_v′‖₂ ≤ (2 + 4π)‖f_v‖₂²,  f_v = ρ(cosh(2παv) − 1)  (Plancherel),

and the linear terms are bounded by ‖Q_v‖₁ ≤ 4√(Q̄T) and the analogous bound for Q_v′. Split
the α-integrals at α₁ = 0.9, where ℓ₁ = 0.4442 ≤ ρ(α)/(1 − α) ≤ L₁ = 0.5874. This gives

  (2 + 4π)‖f_v‖²/(rmin(1/2)·X(v)) ≤ (2 + 4π)/0.471 · [4L₁²/(4πv) + 2ρ_max²(4πv)e^{−4π(1−α₁)v}]
                                         / [(ℓ₁/2)(1 − e^{−y}(1 + y)) − ℓ₁(1 − α₁)²(4πv)²e^{−4πv}/2],

with y = 4πv(1 − α₁). Every piece is monotone for v ≥ 0.80, so the bound decreases: 0.7647
at v = 20, 0.6118 at 25, 0.3824 at 40. The linear part is ≤ 2·10⁻⁴⁷. So (4.2) holds for all
v ≥ 20 and every m. □

**Remarks.** (a) No Lemma R, and no κ below 1, is needed: one pair pays all its interactions
with an arbitrary real environment out of 4m²X(v). Mechanism (b) works without the
autocorrelation part. (b) Integrality is used exactly where Theorem 2 of the proof memo says
it must be: in pen_c (doubles are free, larger clusters pay). That theorem shows that the
real-weight relaxation already fails for one pair at v = 0.85 next to a real atom of weight
≈ 40. (c) The adversary (Section 5, mode "single") finds a single-pair excess of 0.058–3.1,
i.e. 27–38 % of 4X(v) for v_lo ≤ 0.4. At fixed v, H1 certifies at least 6–15 % of 4X(v),
which is consistent. (d) The proof extends to several pairs
that are far apart, but not to pairs within distance ≍ v of each other. Lemma 3.1 shows why:
pair–pair bonds can cancel the self-excess completely.

## 5. Targeted adversary at middle heights (NUMERICAL)

Setup: periodic configurations (exact per-period quadratic form, analytic gradients,
L-BFGS-B). At least one pair (the "mid pairs") is constrained to v ∈ [v_lo, 0.6]. Seeds
come from 160–320 optimised near-tight real designs (best ratio 1.000792). Modes:

* single: one mid pair in a 1–4-fold replicated tight design;
* two: two mid pairs plus a heavy neighbour (weight 2–6);
* cluster: a dense cluster of 2–5 simple atoms within 0.3 of distance 0.6–1.2 from a mid pair;
* alllift: every double turned into a pair at height ≥ v_lo;
* plattice: a near-unit lattice of 4–15 mid pairs with real atoms or doubles inserted;
* random: mixed patterns with 5–40 atoms.

Default run: 9 600 optimisations, 4–80 atoms per period; the `full` run is three times
larger, with up to 104 atoms.

| v_lo | min ratio, configs with a pair at v ≥ v_lo | min excess per mid pair | 4X(v_lo) | single pair in real design | lifted designs |
|---|---|---|---|---|---|
| 0.08 | 1.00144 (single, 33 atoms) | 0.0178 (pair lattice) | 0.155 | 0.0575 | 0.0289 |
| 0.15 | 1.00201 (single, 72) | 0.0178 (pair lattice) | 0.587 | 0.165 | 0.067 |
| 0.25 | 1.00368 (single, 72) | 0.0178 (pair lattice) | 1.976 | 0.540 | 0.154 |
| 0.40 | 1.00453 (pair lattice) | 0.0181 (pair lattice) | 8.140 | 3.09 | 0.395 |

(The `full` run, 28 800 optimisations with up to 104 atoms per period, gives minimum ratios
1.00133, 1.00184, 1.00314 and 1.004442 (pair lattice) for v_lo = 0.08, 0.15, 0.25 and 0.40,
with the same minimum excess 0.0178, again from pair lattices.)

Findings.

1. **No violation.** Every ratio is above 1.0013.
2. **The infimum restricted to configurations containing a middle-height pair is the real
   infimum.** Embed one mid pair in a growing tight real design: its excess stays bounded (by
   H1 it is positive), so the ratio tends to κ_real ≈ 1.0003–1.0008. The meaningful measure
   is the excess per mid pair.
3. **Excess per mid pair.** The infimum found is 4(ρ(0) − 1) = 0.0178 at every v_lo. It is
   attained by pair lattices, which are height-independent by Lemma 3.1, and nothing lower
   was found. Near-tight designs with all doubles lifted come next: 0.029, 0.067, 0.15, 0.40.
   They are dominated by the lattice from v ≈ 0.1 on. Single pairs, two pairs and dense
   clusters next to heavy mass cost far more (0.06–3.3), as H1 predicts.
4. **How much room.** The κ' = 0.99518 allowance is 0.0193 per simple pair and 0.0048 per
   simple real atom. Pair lattices use 0.0178 of the 0.0193 by themselves. So a proof may
   waste almost nothing on pairs that sit in pair lattices, while pairs among real atoms have
   a large margin (H1 certifies ≥ 6 % of 4X; the adversary sees ≥ 27 %).

## 6. What remains

* (**) for configurations with **several pairs at unequal heights**, in particular several
  pairs within distance O(v) of each other whose heights differ, mixed with real atoms.
  Equal heights reduce to the real case (parent Prop. 5(ii)); pairs against reals are handled
  by H1's mechanism; pairs at v ≤ 0.08 by Theorem 4. The missing tool is still the
  "two-height" inequality of the proof memo §5. Section 3 adds a constraint: it must be
  exact on unit pair lattices, where every termwise bound fails.
* A natural next theorem: H1 for k pairs with pairwise distances ≥ D(v) (pair–pair bonds are
  O(e^{2π(v+v′)}/Δ²) against self-excess O(e^{2π(v+v′)}/(vv′))), combined with Theorem 4 for
  low pairs. It would not by itself give an unconditional result.
* Prop. 2.5 converts any proof that charges high pairs ≥ 0.99023 into a frontier-beating
  proportion. That is a weaker target than (**) and may be the right intermediate goal.
* The parallel two-regime memo `complex_cg_highheight_20261003.md` did not exist when this
  note was written, so no comparison is made.

**Certified unconditional bound from this route: none above 0.6725162800.** New PROVED
results: Cor. 2.2 (all heights, κ = 0.987962, not useful alone); Props. 2.3–2.6 (barriers);
Lemmas 3.1–3.2 and Cor. 3.3; Theorem H1.

## 7. Self-check

| step | status | RH / real-zero use | uniform in \|Z\| | integer multiplicities | conjugation closure |
|---|---|---|---|---|---|
| σ* ≤ ρ, ∫σ* = 0.987962 | CHECKED (PL node inequalities) | none | n/a | n/a | n/a |
| Cor. 2.2 | PROVED (Lemma 0 + Lemma R) | none | yes | yes (Lemma R's k_c) | used by Lemma 0 / Lemma R |
| Props. 2.3–2.6 | PROVED (2.6 uses the bandwidth-one ceiling as an input) | none | — | — | — |
| κ_mix = κ_auto | NUMERICAL (column generation) | — | — | — | — |
| Lemmas 3.1–3.2, Cor. 3.3 | PROVED | none | periodic limit (adversary Lemma 1) | yes | yes |
| identity (4.1) | PROVED; checked numerically | none | yes | yes | the pair enters as x₀ ± iv with weight 2m |
| cell reduction, pen_c, Ψ_c bounds | PROVED | uses r ≥ 0 on **R** (CHECKED) | yes (cells, no count) | essential | — |
| sweep v ∈ [0.0795, 20] | CHECKED (closed forms, Taylor bounds in x, monotone bounds in v, rounding allowance) | none | yes | m = 1 exact, m ≥ 2 uniform | — |
| v ≥ 20 | PROVED with computed constants | none | yes | all m | — |
| v ≤ 0.08 | Theorem 4 of the proof memo | none | yes | yes | — |
| adversary | NUMERICAL (local optimisation) | — | periodic | yes | yes |

Nothing above uses β = 1/2. The only arithmetic input of the whole programme remains the
unconditional pair-correlation evaluation in Prop. 2 of the parent memo. Everything here is
about the abstract inequality (**).
