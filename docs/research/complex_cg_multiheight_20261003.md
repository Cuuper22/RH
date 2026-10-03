# The multi-height case of the complex Cheer–Goldston inequality (**)

Script: `verify/complex_cg_multiheight.py` (output `complex_cg_multiheight.out`, about 6 minutes on 4
cores; it imports the LP, closed forms and cell machinery of `verify/complex_cg_hybrid.py`).
Parent memos: [proof](complex_cg_proof_20261003.md) (Theorems 1–4), [hybrid](complex_cg_hybrid_20261003.md)
(Theorem H1), [high-height](complex_cg_highheight_20261003.md) (Lemma A, Lemmas 3.1–3.2),
[adversary](complex_cg_adversary_20261003.md). Notation as there: atoms j with positions x_j, heights
v_j ≥ 0 (0 for real atoms), weights W_j (m for a real atom, 2m for a pair), a_j = 2παv_j,
c_j = cosh a_j, s_j = sinh a_j, e_j = e(αx_j), S_Z = Σ_j W_j c_j e_j, cost_j = 2m − [m = 1] (real) or
2W_j (pair), κ = r(0) = 1 for the certified ρ (R = 1.012460, ρ(0) = 1.004442, ρ_* = min_{[0,1/2]} r ≥ 0.4710).

## 0. Summary and verdict

* **(**) is not complete.** The remaining case is not closed here; the unconditional proportion stays
  at 0.6725162800 (the conditional value 0.6789153 of Theorem 1 is unchanged).
* **A gap in the status table (correction).** The row "pairs at one common height: PROVED" covers
  *pairs only* (parent Prop. 5(ii)). Two or more pairs at a common height v > 0.08 **together with real
  atoms** are not covered by any proved result (H1 is one pair; its proof does not extend, Section 3).
  This "one-layer" case O2 is the simplest instance of the open case and is recorded as OPEN.
* **Height-difference form (Prop. 1.1, PROVED).** For every Z,
  Σ_Z(ρ) − cost ≥ ∫ρ|U|² + Σ_j (W_j² − cost_j) + Σ_{j≠k} W_jW_k G_{|v_j − v_k|}(Δ_jk), U = Σ_j W_j s_j e_j,
  G_u = r + Q_u. The only possibly negative terms are bonds between atoms at *different* heights; bonds
  at equal height are r ≥ 0. Together with the Abel/layer form (Prop. 1.2) this is the bookkeeping in
  which every proved case is one line, and in which the open case is a statement about one quantity.
* **Theorem C (PROVED).** If no cross-height bond is negative, (**) holds with κ = 1. Since
  G_u(Δ) ≥ 0 for |Δ| ≤ 1/4 and every u, (**) holds for every Z whose atoms at distinct heights are
  pairwise within 1/4 — in particular for any cluster of pairs at arbitrary unequal heights, with any
  real atoms, inside an interval of length 1/4. The admissible distance Δ*(u) is 1.03 (u = 0.02),
  0.55 (u = 0.5), 0.38 (u = 1), 0.27 (u = 5) (NUMERICAL table, Section 2).
* **Cauchy–Schwarz bound (Prop. 1.3, PROVED).** For one layer of pairs P at height v and reals R,
  Σ_Z(ρ) ≥ Σ_{Z₀}(ρ) − Σ_R(ρ tanh²(παv)); so (**) holds whenever the collapsed slack
  Σ_{Z₀}(ρ) − cost exceeds Σ_R(ρ tanh²(παv)). This is exact on the extremal direction
  S_P = −S_R/(c + 1), which no positive integer configuration realises; it is far from sharp on real
  configurations (Section 1) and shows that the integrality of P is essential also in O2.
* **The joint-field mechanism (NUMERICAL, Section 3).** On lattice segments of n pairs at a common
  height, H1's cell bookkeeping applied with the *joint* field Σ_k 4G_v(x − x_k) against the exact
  resource E_P = ∫ρ sinh²|S_P|² closes with ratios 0.68–0.80 (v = 0.2), 0.31–0.50 (v = 0.5),
  0.11–0.37 (v = 1) for n = 2…12, while the pair-by-pair bookkeeping fails by factors up to 4.6 for
  v ≤ 0.5. The missing lemma for O2 is therefore identified precisely (Conjecture 3.2): a bound for
  the negative part of the joint field of an arbitrary positive configuration by its sinh²-energy.
* **Targeted search (NUMERICAL).** Minimal open sub-cases — O1 (three pairs alone, free heights), O2
  (2–3 pairs at a common height with reals), O3 (two pairs at free unequal heights plus one real atom)
  — give minimum ratios 1.0167, 1.047 (v = 0.15), 1.0143; no violation.

## 1. Exact forms of Σ_Z and the Cauchy–Schwarz bound

**Proposition 1.1 (height-difference form; PROVED, CHECKED to 3·10⁻¹⁶).** For every finite
conjugation-invariant Z,

    Σ_Z(ρ) = ∫ρ|U|² + Σ_{j,k} W_jW_k t(0, |v_j − v_k|, Δ_jk),      U = Σ_j W_j sinh(a_j) e_j,     (1.1)
    Σ_Z(ρ) − κ·cost ≥ ∫ρ|U|² + Σ_j (W_j² − cost_j) + Σ_{j≠k} W_jW_k G_{|v_j−v_k|}(Δ_jk),          (1.2)

with t(0, u, Δ) = ∫ρ cosh(2παu) cos(2παΔ), G_u(Δ) = r(Δ) + Q_u(Δ), Q_u = FT[ρ(cosh(2πα u) − 1)].

*Proof.* (1.1) is Lemma 3.1 of the high-height memo integrated: c_jc_k = s_js_k + cosh(a_j − a_k).
Subtract Σ_{j,k} W_jW_k s(Δ_jk) = ∫ŝ|S_{Z₀}|² ≥ 0 (Lemma 0 for the collapsed real multiset Z₀); the
diagonal gives W_j²(R − s(0)) = κW_j² ≥ κ cost_j, and off the diagonal t(0,u,Δ) − s(Δ) = r(Δ) + Q_u(Δ). □

Remarks. (a) The self-excess of a pair, W²X(v), is not a separate resource any more: it sits inside
∫ρ|U|², which for several pairs can be far smaller than Σ_k W_k²X(v_k) (two equal pairs at distance
1/2 and height v: ∫ρ|U|² ≈ 2W²X(v)/(16v²) for large v). This is the exact form of the "−√(C C')"
obstruction of the high-height memo: it is not a negative bond but a cancellation inside |U|².
(b) Pair–pair bonds enter at the height *difference*: two pairs at equal height have bond r ≥ 0
regardless of their distance; the pair–real bond is G_v, exactly as in H1.
(c) The real case, Prop. 5(ii), Lemma A and H1 are all instances: U = 0 for the first two; for H1,
∫ρ|U|² = W²X(v) and the bonds are 2W Σ_j W_j G_v(x_j).

**Proposition 1.2 (layer form; PROVED, CHECKED).** Let 0 = v₀ < v₁ < … < v_n be the distinct heights,
S_ℓ the real exponential sum of the atoms at height v_ℓ, c_ℓ = cosh(2παv_ℓ), and T_ℓ = Σ_{ℓ'≥ℓ} S_ℓ'
the collapsed sum of all atoms at height ≥ v_ℓ. Then S_Z = Σ_ℓ c_ℓ S_ℓ = Σ_ℓ (c_ℓ − c_{ℓ−1}) T_ℓ
(c_{−1} := 0): a complex configuration is a nonnegative, α-dependent combination of the real sums of
the nested multisets Y_ℓ = {atoms at height ≥ v_ℓ}. For one layer (n = 1, P at height v, reals R):

    Σ_Z(ρ) = Σ_{Z₀}(ρ) + E_P + 2 Σ_{j∈R, k∈P} W_jW_k Q_v(x_j − x_k),   E_P = ∫ρ sinh²(2παv)|S_P|²,  (1.3)
           = Σ_{Z₀}(ρ cosh) + Σ_P(ρ cosh(cosh − 1)) − Σ_R(ρ(cosh − 1)),                            (1.4)

where Σ_Y(τ) = ∫τ|S_Y|². All three terms of (1.4) are "real configurations with a nonnegative test";
the negative one is the real atoms alone with the test ρ(cosh − 1), whose κ_real is 0 (it vanishes at
α = 0; adversary Lemma 4). So no completion-type argument applied layer by layer can work.

**Proposition 1.3 (Cauchy–Schwarz; PROVED).** For one layer, pointwise in α,
(c + 1)|S_P|² + 2 Re(S_R S̄_P) = (c + 1)|S_P + S_R/(c + 1)|² − |S_R|²/(c + 1), hence by (1.3)

    Σ_Z(ρ) ≥ Σ_{Z₀}(ρ) − Σ_R(ρ tanh²(παv)),                                                        (1.5)

with equality iff S_P = −S_R/(c + 1) almost everywhere on supp ρ. Consequently (**) holds for one
layer whenever Σ_R(ρ tanh²(παv)) ≤ Σ_{Z₀}(ρ) − cost(Z₀) (slack of the collapsed real configuration,
which is ≥ Σ_j(W_j² − cost_j) + Σ_{j≠k} W_jW_k r(Δ_jk) + ∫ŝ|S_{Z₀}|²). For R = ∅ this is Prop. 5(ii).

The bound (1.5) is weak on actual configurations: in 60 random one-layer configurations the right
side divided by cost was 0.76–0.99 where the true ratio was 1.1–7800 (script Part 1(d)). The reason
is that the extremal S_P = −S_R/(c + 1) is not an exponential sum with positive weights ≥ 2; the
integrality of P must be used. This is Theorem 2 of the proof memo seen from the P side.

## 2. Theorem C: configurations without negative cross-height bonds

**Theorem C (PROVED).** Let Z be any finite conjugation-invariant multiset such that
G_{|v_j − v_k|}(x_j − x_k) ≥ 0 for every two atoms j ≠ k at different heights. Then
Σ_Z(ρ) ≥ κ(2|Z| − s₁) with κ = r(0) = 1.

*Proof.* In (1.2) every term on the right is ≥ 0: ∫ρ|U|² ≥ 0, W_j² ≥ cost_j, G_0 = r ≥ 0 for atoms
at equal height, and the cross-height bonds by hypothesis. □

**Corollary C1 (PROVED).** G_u(Δ) ≥ 0 for every u ≥ 0 and |Δ| ≤ 1/4: r ≥ 0 on **R** (Theorem 1) and
Q_u(Δ) = ∫_{−1}^{1} ρ (cosh(2παu) − 1) cos(2παΔ) dα has a nonnegative integrand when |2παΔ| ≤ π/2.
Hence (**) holds, with κ = 1, for every Z whose atoms at distinct heights are pairwise within
distance 1/4 — in particular for any number of pairs at arbitrary unequal heights and multiplicities,
with arbitrary real atoms, all inside an interval of length 1/4. (Atoms at equal height may be
anywhere.) New instances: clusters of ≥ 2 pairs at unequal heights ≥ 0.08, and ≥ 2 common-height
pairs with reals, within 1/4.

**Admissible distance (NUMERICAL, grid 10⁻⁴).** Δ*(u) := sup{d : G_u ≥ 0 on (0, d]}:

| u | 0.02 | 0.05 | 0.08 | 0.1 | 0.15 | 0.2 | 0.3 | 0.4 | 0.5 | 0.7 | 1 | 1.5 | 2 | 3 | 5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Δ*(u) | 1.026 | 0.992 | 0.958 | 0.936 | 0.879 | 0.823 | 0.716 | 0.624 | 0.552 | 0.457 | 0.383 | 0.329 | 0.305 | 0.284 | 0.269 |

Δ*(u) ↓ 1/4 as u → ∞ (Q_u concentrates at |α| = 1 where the sign of cos(2παΔ) changes at
Δ = 1/4), and Δ*(u) → the first zero of r (≈ 1.03) as u → 0. Theorem C applies to a given
configuration whenever each cross-height distance is ≤ Δ*(height difference); the table is
indicative, the certified statement is Corollary C1 with 1/4. Random clusters of diameter ≤ 1/4
(2–4 pairs at heights in [0.05, 2], 0–2 reals, script Part 2) have ratio ≥ 2.81 and certificate
∫ρ|U|² + Σ(W² − cost) ≥ 6.06: the cluster case is far from tight, as expected (the tight
configurations are lattices with spacing ≈ 1, where cross-height bonds at Δ ≈ 1/2 mod 1 are
negative).

Remark. Theorem C is where Theorem 2 of the proof memo is *not* in force: on clusters, (1.2) is a
sum of nonnegative terms, and the real-weight relaxation is true. Everything tight lives at
cross-height distances near 1/2 (mod 1), which is also where Prop. 4.1 of the high-height memo
refutes pair removal.

## 3. The remaining case, precisely

**3.1 Minimal open sub-cases.** Writing (1.2) for a configuration, the negative bonds are
cross-height bonds at distances where G_u < 0; the resources are ∫ρ|U|², the integer slack
Σ(W² − cost) and the equal-height r-bonds. The proved cases are: U = 0 (real, Prop. 5(ii)); one
pair (H1: ∫ρ|U|² = W²X(v) is a fixed resource and cells pay the field); two pairs alone (Lemma A,
by a different algebra); all heights ≤ 0.08 (Theorem 4, second-order in v); clusters (Theorem C).
The smallest configurations outside all of these:

* **O2 — one layer with reals:** k ≥ 2 pairs at a common height v > 0.08 within O(1) of each other,
  plus real atoms. Here U = sinh(a) S_P, ∫ρ|U|² = E_P, and E_P can be far below Σ_k W_k²X(v)
  (lattice-like P: Section 3.3), so H1's per-pair accounting has no resource. The status table's
  "common height: PROVED" does not cover this (Prop. 5(ii) has no real atoms).
* **O3 — two pairs at unequal heights plus one real atom** (the smallest configuration with a
  cross-height pair–pair bond and a real atom). Lemma A covers the two pairs alone; the real atom
  adds the two fields 2W_k m₀ G_{v_k}(x_k) and nothing pays them when W₁s₁ and W₂s₂ cancel in U.
* **O1 — three pairs alone at unequal heights.** Lemma 3.2 (shift to one pair plus a real double)
  needs ∫ρ|U|² ≥ ∫ρ|U'|², refuted in general (Prop. 3.3); the three-term Lemma-A algebra
  |S|² = ½Σ_{j<k}(w_j − w_k)² + 2Σ_{j<k} w_jw_k(½ + cos θ_jk) has terms of both signs.

The two-layer case (heights v₁ < v₂ with reals) reduces, by Prop. 1.2 with S = c₁T₁ + (c₂ − c₁)T₂
and the pointwise identity c_j = c₁cosh(a_j − a₁) + s₁sinh(a_j − a₁), to
S = S_R + c₁V + s₁U', V = S_{Z'} (pairs lowered by v₁), U' = Σ_P W sinh(a − a₁)e. So every multi-layer
configuration is a one-layer configuration (reals R, layer V at height v₁) *perturbed by the sinh-sum
U'*; O2 is the unavoidable first step of any induction on the number of heights.

**3.2 Why the proved methods stop at O2.** By (1.3), O2 is the inequality

    E_P + 2 Σ_{j∈R} W_j Φ(x_j) + slack(Z₀) ≥ 0,     Φ(x) := Σ_{k∈P} W_k G_v(x − x_k)   (joint field),   (3.1)

slack(Z₀) ≥ Σ_j(W_j² − cost_j) + Σ_{j≠k} W_jW_k r(Δ_jk). H1 proves (3.1) for |P| = 1 by cells: the atoms
in the negative set of Φ are grouped into cells c of diameter ≤ 0.7, the cell slack is
pen_c(w) ≥ ρ_c(w² − 2w), and the damage is Σ_c Ψ_c(sup_c Φ⁻/4) with Ψ_c(y) = max_w(4yw − pen_c(w)).
The argument is valid verbatim for any P — with the joint field. What breaks for |P| ≥ 2 is only the
*resource side*: H1 pays Σ_cΨ_c from W²X(v); for several pairs the available amount is E_P, and
E_P ≪ Σ_k W_k²X(v) whenever S_P is small near |α| = 1 (lattice-like P). The per-pair sup bounds
Σ_k Σ_c Ψ_c(m_k sup_c(−G_v(· − x_k))₊) destroy the cancellation in Φ that goes with the cancellation
in E_P (Lemma 3.2 of the hybrid memo: a full unit lattice has E_P = 0 and Φ ≡ 0). Two further facts
(PROVED, one line each from (1.3)):

* pointwise bound of the joint field by the energy: since cosh a − 1 = sinh(a) tanh(a/2),
  |Φ_Q(x)| ≤ √(τ₀(v) E_P) for every x, Φ_Q = Q_v ∗ μ_P, τ₀(v) = ∫ρ tanh²(παv) < R; and Plancherel
  ‖Φ_Q‖₂² = ∫ρ²(c − 1)²|S_P|² ≤ sup_α[ρ tanh²(παv)] · E_P. Neither controls Σ_c sup_c Φ⁻ (an L¹-type
  quantity over the cells that carry real atoms), which is what the damage needs; the loss in passing
  from L² to cell sums is a factor (2 + 4π)ρ(0)/ρ_* ≈ 31 (H1 Step 4), far too much below v ≈ 20.
* the slack of a cell can be used once: for several pairs the damages are superadditive
  (Ψ_c(y₁ + y₂) ≥ Ψ_c(y₁) + Ψ_c(y₂)), so even well separated pairs cannot simply be treated by H1
  one at a time; Jensen splitting Ψ_c(Σy_k) ≤ Σ_k λ_kΨ_c(y_k/λ_k) inflates the quadratic part by
  1/λ_k, and the far fields (|Q_v(x)| ≤ T(v)/x², sign-indefinite for v ≳ 0.3) decay too slowly to
  make the inflation cheap below v ≈ 1. A "separated pairs" theorem is therefore not a corollary of H1
  without a density hypothesis on the reals; we did not pursue it (it is not the open case).

**3.3 The joint-field bookkeeping closes where the per-pair one fails (NUMERICAL, script Part 3c).**
Lattice segments P = {0, 1, …, n−1} of pairs of weight 2 at height v, real atoms anywhere, cells as in
H1 (components of the negative set cut into pieces ≤ 0.5–0.7, ρ_c = rmin(piece), exact Ψ_c), x ∈ [−40, n + 40]:

| v | n | E_P | Σ_k W_k²X | joint damage | per-pair damage | joint / (E_P + r-bonds) | per-pair / (E_P + r-bonds) |
|---|---|---|---|---|---|---|---|
| 0.2 | 1 | 1.134 | 1.134 | 0.966 | 0.966 | 0.852 | 0.852 |
| 0.2 | 2 | 1.485 | 2.269 | 1.204 | 1.932 | 0.801 | 1.286 |
| 0.2 | 3 | 1.674 | 3.403 | 1.324 | 2.898 | 0.775 | 1.697 |
| 0.2 | 4 | 1.808 | 4.537 | 1.407 | 3.865 | 0.757 | 2.080 |
| 0.2 | 6 | 1.993 | 6.806 | 1.519 | 5.798 | 0.731 | 2.790 |
| 0.2 | 8 | 2.125 | 9.075 | 1.594 | 7.731 | 0.710 | 3.446 |
| 0.2 | 12 | 2.309 | 13.612 | 1.692 | 11.600 | 0.678 | 4.645 |
| 0.5 | 1 | 19.787 | 19.787 | 14.488 | 14.488 | 0.732 | 0.732 |
| 0.5 | 2 | 34.491 | 39.574 | 17.390 | 28.956 | 0.504 | 0.839 |
| 0.5 | 3 | 43.762 | 59.360 | 18.879 | 43.427 | 0.431 | 0.992 |
| 0.5 | 4 | 50.434 | 79.147 | 19.900 | 57.899 | 0.394 | 1.147 |
| 0.5 | 6 | 59.857 | 118.721 | 21.275 | 86.849 | 0.355 | 1.449 |
| 0.5 | 8 | 66.544 | 158.294 | 22.199 | 115.805 | 0.333 | 1.737 |
| 0.5 | 12 | 75.970 | 237.441 | 23.440 | 173.737 | 0.308 | 2.281 |
| 1.0 | 1 | 2394.849 | 2394.849 | 1283.330 | 1283.330 | 0.536 | 0.536 |
| 1.0 | 2 | 6590.268 | 4789.697 | 2436.679 | 2566.045 | 0.370 | 0.389 |
| 1.0 | 3 | 10353.989 | 7184.546 | 2769.702 | 3848.566 | 0.268 | 0.372 |
| 1.0 | 4 | 13438.020 | 9579.394 | 2880.459 | 5131.111 | 0.214 | 0.382 |
| 1.0 | 6 | 18124.680 | 14369.092 | 2946.807 | 7696.339 | 0.163 | 0.425 |
| 1.0 | 8 | 21583.687 | 19158.789 | 2964.751 | 10261.738 | 0.137 | 0.475 |
| 1.0 | 12 | 26554.223 | 28738.183 | 2977.186 | 15393.000 | 0.112 | 0.580 |

(The row n = 1 is H1 with these slightly cruder cells; H1's certified sweep gives 0.905 at v = 0.2 and
0.768 at v = 0.5.) With the joint field, the damage grows like log n while E_P grows at least as fast,
and the ratio *decreases* in n at every height; with per-pair sup bounds the damage grows linearly in n
against a resource that saturates, and the bookkeeping fails from n = 2 (v = 0.2) or n = 4 (v = 0.5) on. So the H1
mechanism, run with the joint field against the exact energy, is the right shape for O2; what is
missing is the inequality that makes it uniform over all P.

**Conjecture 3.2 (joint-field inequality; what would prove O2).** For every finite real multiset P
with weights W_k ≥ 2 and every v > 0.08, with the H1 cells of the negative set of Φ = Σ_k W_kG_v(· − x_k),

    Σ_c Ψ_c(sup_c Φ⁻/4) ≤ E_P + Σ_{k≠k'} W_kW_k' r(x_k − x_k') + Σ_k W_k(W_k − 2).                     (3.2)

By (1.3) and H1's cell reduction, (3.2) implies (**) for one layer with arbitrary reals. For |P| = 1
it is H1. Both sides are invariant under the cancellations of lattice-like P (left: Φ small; right:
E_P small); (3.2) is NUMERICAL on lattice segments (table) and on the random one-layer configurations of
Part 1. Its two-layer analogue replaces E_P by ∫ρ|U|² and Φ by Σ_k W_k G_{v_k}(· − x_k) with the
cross-height pair–pair bonds added to the left side; it would give the open case by induction on the
number of heights through the decomposition S = S_R + c₁V + s₁U' of Section 3.1.

## 4. Targeted search on O1–O3 (NUMERICAL; script Part 3)

Nelder–Mead from six random starts per job, exact Gauss-node evaluation, 55 jobs, no periodicity:

| case | minimum of Σ/cost | attained at |
|---|---|---|
| O2, v = 0.15: 2–3 pairs (W = 2) + reals (1 simple, 1 double, 2 simples, 1 triple, simple + double) | 1.0473 | 3 pairs, simple + double; pairs at spacing ≈ 1 |
| O2, v = 0.30 | 1.1659 | 3 pairs, simple + double |
| O2, v = 0.50 | 1.5680 | 3 pairs, simple + double |
| O2, v = 1.00 | 31.1 | 2 pairs + triple |
| O3: real atom m₀ ∈ {1,2,3} + two pairs W ∈ {(2,2),(2,4),(4,2),(4,4)}, heights free in [0.05, 2] | 1.0143 | m₀ = 2, W = (2,2), both heights at the lower bound 0.05, x = 0, 2.06, 3.14 |
| O1: three pairs alone, W ∈ {(2,2,2),(2,2,4),(2,4,4)}, heights free | 1.0167 | W = (2,2,2), heights 0.05, x = 0, 1.07, 2.15 |

In O1 and O3 the optimiser pushes all heights to the lower bound: lifting costs, as in every earlier
search. The one-layer minima at fixed v ≥ 0.15 are well above the pair-lattice value ρ(0) = 1.0044
and above the adversary memo's lifted designs (1.0013–1.0045, which are periodic and much larger); a
finite O2 configuration is not where (**) is tight, but it is where the *proof* is missing.

## 5. Self-check

| item | status | RH / reality of zeros | uniform in \|Z\| | integer multiplicities | conjugation closure |
|---|---|---|---|---|---|
| Prop. 1.1 (1.1)–(1.2) | PROVED; (1.1) CHECKED 3·10⁻¹⁶ | none; uses r ≥ 0 (Thm 1) and ŝ ≥ 0 (Lemma 0 on Z₀) | yes | W_j² ≥ cost_j | Z₀ is a real multiset by closure |
| Prop. 1.2 (layer form) | PROVED; CHECKED 3·10⁻¹⁶ | none | yes | — | — |
| Prop. 1.3 (CS bound) | PROVED; CHECKED (60 configs) | none | yes | not used (hence weak) | — |
| Theorem C, Cor. C1 | PROVED | none | yes | W_j² ≥ cost_j | yes |
| Δ*(u) table | NUMERICAL (10⁻⁴ grid, closed forms) | — | — | — | — |
| Section 3.2 facts | PROVED (one-line consequences of (1.3)) | none | — | — | — |
| Part 3c table, Conj. 3.2 | NUMERICAL / CONJECTURE | — | — | essential (Ψ_c) | — |
| Section 4 minima | NUMERICAL (local optimisation) | — | finite configs | yes | yes |

No step uses β = 1/2. Theorem C and Cor. C1 are uniform in |Z| and use integrality only through
W_j² ≥ cost_j. Nothing here changes the certified unconditional proportion (0.6725162800) or the
conditional one (0.6789153 under heights ≤ 1/(4π)); (**) remains CONJECTURE in general, with O2
(≥ 2 common-height pairs with reals, v > 0.08) now recorded as the first open sub-case.
