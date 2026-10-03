# The joint-field inequality for sub-case O2: a counterexample, and what must replace it

Script: `verify/complex_cg_jointfield.py` (output `complex_cg_jointfield.out`, about 6 minutes on one core;
imports the LP, closed forms and cell machinery of `verify/complex_cg_hybrid.py` and
`verify/complex_cg_multiheight.py`). Parent memos: [multi-height](complex_cg_multiheight_20261003.md) (Prop. 1.1–1.3,
Section 3, Conjecture 3.2), [hybrid](complex_cg_hybrid_20261003.md) (Theorem H1, Ψ_c, pen_c),
[proof](complex_cg_proof_20261003.md) (the certified ρ, r = r_in − s ≥ 0, κ = r(0) = 1, R = 1 + s(0) = 1.012460).
Labels: PROVED, CHECKED, NUMERICAL, CONJECTURE, REFUTED, and HEURISTIC (a computation in a continuum limit
whose transfer to integer configurations is argued but not proved; nothing depends on it).

Notation as in the parents. P is a finite multiset of pairs x_k ± iv at one height v, with weights W_k = 2m_k;
μ_P = Σ W_k δ_{x_k}, S_P = μ̂_P, c = cosh(2παv), f_v = ρ(c − 1), Q_v = f̌_v, G_v = r + Q_v,
E_P = ∫ρ sinh²(2παv)|S_P|², and the joint field is Φ = Σ_k W_k G_v(· − x_k) = Φ_r + Φ_Q, with
Φ_r = r ∗ μ_P ≥ 0 and Φ_Q = Q_v ∗ μ_P. The Fourier transform of r is the PL function c_LP of the LP
(c_LP = ρ on [−1, 1], c_LP = −ŝ ≤ 0 on 1 < |α| < 2.5).

## 0. Verdict

* **O2 is not closed, and (**) is not complete.** The unconditional proportion stays at 0.6725162800; the
  conditional value 0.6789153 (Theorem 1) is unchanged.
* **Conjecture 3.2 is REFUTED** (Section 2), together with its two-layer analogue, which contains it.
  Counterexample: the pair-lattice segment P = {0, 2, 4, …, 2(n − 1)}, W = 2, at v = 0.5. The left side of
  (3.2) exceeds the right side by 8 % at n = 20 and 14 % at n = 40. The failure persists for every partition
  of the negative set into cells (optimal partitions: 7 % and 13 %). In the periodic limit the ratio is 1.24
  at v = 0.5 and 2.1 at v = 2, and it does not decay with v (Section 3). The numerical support for 3.2 came
  from unit-spacing segments, where Φ cancels.
* **(**) itself holds on these configurations with margin ≥ 46 %** (NUMERICAL, Section 2.3). The cell
  bookkeeping fails, not the inequality: inside one negative component of length 0.7–1, any H1 partition
  drops the bond between neighbouring cells. Here r(0.37) = 0.68, while a single cell of length 0.74 has
  ρ_c = r(0.74) = 0.15.
* **Corrected reduction (Prop. 4.1, PROVED) and corrected conjecture (3.2′, CONJECTURE).** Keep all r-bonds
  between real atoms in the same negative component of Φ. The resulting component-local inequality implies
  O2 exactly as 3.2 did. On every configuration that refutes 3.2, and on 236 lattices and motifs at
  v ∈ [0.2, 2], it holds with ratio ≤ 0.87 (NUMERICAL).
* **Field–energy duality (Lemma 5.1, PROVED; constants NUMERICAL).** Φ_Q(y)² ≤ τ₀(v)E_P with
  τ₀ = ∫ρ tanh²(παv). This is sharp over signed P. Positivity of P lowers it by only about 5 %; adding
  the pair r-bonds lowers it to 0.11, 0.38, 0.63 at v = 0.5, 1, 2. A large-sieve-by-the-energy argument
  therefore controls the quadratic part of the damage of one component at moderate heights, but the
  constant tends to R > 1 as v → ∞.
* **A large-height warning (HEURISTIC, Section 6).** In the continuum limit there are one-layer
  configurations with Σ_Z(ρ) − ∫ŝ|S_{Z₀}|² < 0 at order Λ² for v ≳ 66: a smooth positive pair density
  shaped like a sech hole, plus one heavy real atom. If this transfers to integer configurations, as argued
  in Section 6, then no bookkeeping that discards ∫ŝ|S_{Z₀}|² (3.2, 3.2′, H1-type) can prove O2 at large
  heights. The ŝ-part of the collapsed real configuration must then be kept.

## 1. The statement under test, with the normalisation fixed

By (1.3) of the multi-height memo, for one layer P at height v and real atoms R (weights W_j, cost_j = 2W_j or
1 for simples),

    Σ_Z(ρ) − cost(Z) = E_P + Σ_{k≠k'∈P} W_kW_{k'} r(Δ) + Σ_P W_k(W_k − 2)
                     + Σ_R (W_j² − cost_j) + Σ_{j≠j'∈R} W_jW_{j'} r(Δ) + 2 Σ_{j∈R} W_j Φ(x_j) + ∫ŝ|S_{Z₀}|².      (1.1)

This is an identity: (1.2) of the parent memo with equality, using R − s(0) = 1. In H1's reduction, real
atoms with Φ(x_j) ≥ 0 are discarded. The rest are grouped into cells c, and the bonds between cells and
∫ŝ|S_{Z₀}|² are dropped. A cell of total real weight w then contributes at least
pen_c(w) − 2w sup_c Φ⁻ = pen_c(w) − 4w·(sup_c Φ⁻/2). Hence the damage is Σ_c Ψ_c(sup_c Φ⁻/2), and the
inequality that implies O2 is

    Σ_c Ψ_c(sup_c Φ⁻/2) ≤ E_P + Σ_{k≠k'} W_kW_{k'} r(x_k − x_{k'}) + Σ_k W_k(W_k − 2).                      (3.2)

**Normalisation (correction).** The parent memo writes the argument as sup_c Φ⁻/4 with Φ = Σ W_kG_v. That
is half the field that enters (1.1), and in that form (3.2) does not imply O2. The parent script uses
Ψ_c(sup_c(Σ_k 4G_v)⁻/4), which for W = 2 equals Ψ_c(sup_c Φ⁻/2). So its numbers refer to the form above,
and so does everything here.

## 2. Counterexample to Conjecture 3.2 (REFUTED)

**2.1 The configuration.** n pairs of multiplicity 1 (W = 2) at x_k = 2k, 0 ≤ k < n, height v = 0.5. The
joint field has one negative component between consecutive pairs, centred at the odd integers. It has
length 0.736 and depth min Φ = −1.495 in the periodic limit. E_P is small because S_P peaks at α ∈ ½**Z**:
the peak at α = 1 is killed by ρ(1) = 0, and only α = ½ contributes.

**2.2 The numbers (Part 1; NUMERICAL, robust).** Grid h = 10⁻³ on [−60, 2n + 58], exact closed forms for
G_v at lattice-aligned distances, and E_P from the Gauss nodes. Every approximation lowers the left side:
ρ_c is the grid minimum of r on [0, d_c] (≥ the true minimum), sup Φ⁻ is taken over grid points (≤ the true
supremum), and cells beyond the window are omitted.

| n | E_P + bonds | H1 cells ℓ = 0.5 / 0.6 / 0.7 | best H1 ratio | optimal partition (mesh 0.01, cells ≤ 1.02) |
|---|---|---|---|---|
| 8 | 105.495 | 1.042 / 1.005 / 0.964 | 0.964 | 0.961 |
| 20 | 237.664 | 1.117 / 1.098 / 1.080 | **1.080** | **1.074** |
| 40 | 453.145 | 1.156 / 1.149 / 1.139 | **1.139** | **1.133** |

The ratio rises with n towards the periodic value 1.236 (H1) or 1.224 (optimal cells) of Section 3. The
margins are 7–14 %, against grid and rounding effects of order 10⁻³, all of which push the other way. So
(3.2) fails for every n ≥ 20, with every cell length allowed in H1, and with optimal partitions.
The two-layer analogue (E_P → ∫ρ|U|², pair–pair cross-height bonds added on the left) reduces to (3.2)
when all heights coincide, so it fails too.

**2.3 The inequality itself is not tight there (Part 2; NUMERICAL).** Put real atoms of multiplicity m at the
field minima 1, 3, …, 2n − 3. Then Σ_Z/cost = 2.85, 1.82, 1.67, 1.73 (m = 1, 2, 3, 4) at n = 20, and 2.70,
1.71, 1.58, 1.65 at n = 40. For the infinite lattice, the best one or two real atoms per period
(multiplicities ≤ 24, Nelder–Mead) give 1.459 at v = 0.5, L = 2 (one triple at the midpoint). They give
5.24 at v = 1, L = 2 and 3.33 at v = 0.7, L = 1.75.

**2.4 Why the cells lose.** At the midpoint one real triple sees Φ = −1.495 and contributes
9 − 6 − 6·1.495 = −5.97, against E_P = 10.57 per period. The H1 bookkeeping cuts the component of length
0.736 into two cells of length ≈ 0.37 (ρ_c ≈ r(0.37) = 0.68). It puts a heavy atom in each cell and drops
their mutual bond 2W²r(0.37), which is what forbids that configuration. A single cell instead has
ρ_c = r(0.736) = 0.148, and its quadratic damage 4y²/ρ_c is 4.6 times larger. No partition avoids both
losses. In general the negative components of these lattices have length 0.54–1.27 (v = 0.5, L ∈ [1.5, 3]). That
is longer than the H1 cell lengths (≤ 0.7), and it spans the range where r falls from 0.47 (at ½) to 0 (at 1.03).

## 3. Periodic pair lattices: where the cell bookkeeping fails (Part 3; NUMERICAL, exact forms)

For the lattice L**Z** of pairs (W = 2), Poisson summation gives exact per-period quantities.
Φ(x) = (2/L)Σ_k Ĝ_v(k/L)e(kx/L) with Ĝ_v = c_LP + f_v; E_P = (4/L)Σ_{|k|<L} ρ(k/L) sinh²(2πkv/L); and the
pair bonds are 4[(1/L)Σ_k c_LP(k/L) − 1]. The table gives damage/(E_P + bonds) per period for three
bookkeepings: H1 cells (best ℓ ∈ {0.5, 0.6, 0.7}), optimal cell partitions (DP, mesh 0.01, cells ≤ 1.02), and
the component-local functional of Section 4.

| v \ L | 1.25 | 1.5 | 1.75 | 2 | 2.5 | 3 | 4 | 6 |
|---|---|---|---|---|---|---|---|---|
| 0.2 | 0 / 0 / 0 | 0 / 0 / 0 | .32/.32/.32 | .87/.87/.87 | .10/.10/.10 | .87/.87/.87 | .86/.86/.86 | .86/.86/.86 |
| 0.3 | 0 / 0 / 0 | .15/.15/.15 | .55/.55/.55 | .79/.79/.79 | .36/.36/.36 | .82/.82/.82 | .81/.81/.81 | .81/.81/.81 |
| 0.5 | .15/.15/.15 | .53/.53/.33 | **1.01**/.94/.49 | **1.24/1.22**/.57 | .41/.41/.35 | .92/.90/.58 | .81/.81/.58 | .77/.77/.56 |
| 0.7 | .42/.37/.20 | .90/.81/.36 | **1.24/1.15**/.46 | **1.45/1.38**/.52 | .59/.51/.26 | **1.10/1.01**/.46 | .91/.83/.41 | .78/.71/.38 |
| 1 | .57/.47/.23 | **1.08**/.94/.38 | **1.47/1.27**/.46 | **1.79/1.50**/.50 | .61/.51/.24 | **1.14/1.00**/.41 | .88/.76/.33 | .68/.59/.27 |
| 1.5 | .61/.50/.23 | **1.16**/.99/.39 | **1.61/1.33**/.47 | **2.04/1.56**/.50 | .61/.51/.23 | **1.16**/.99/.39 | .83/.70/.30 | .56/.46/.21 |
| 2 | .61/.51/.23 | **1.17**/.99/.39 | **1.63/1.34**/.47 | **2.10/1.58**/.50 | .61/.51/.23 | **1.17**/.99/.39 | .82/.69/.30 | .51/.42/.20 |

Reading. (i) The failure region of 3.2 is v ≥ 0.5 and L ∈ [1.5, 3]. It does not shrink as v grows: for
L = 2 the H1 ratio rises from 1.24 to 2.10, and for optimal cells it tends to about 1.6. (ii) For small v
all three bookkeepings agree (0.79–0.87). That is the isolated-pair value of H1, and there the damage
consists of doubles in cells of length ≤ 0.5 (Ψ_c(y) = 8y). (iii) For L = 2 the component-local ratio
tends to ρ(1/2) = 0.4988. Asymptotically the field is 2ρ(½)(cosh πv − 1)cos πx and the energy per period
is 4ρ(½)sinh²(πv). One atom of weight ≈ |min Φ| at the midpoint gains ≈ min Φ², which is ρ(½) times
the energy. (iv) The parent memo found 3.2 true on unit-spacing segments (ratios 0.11–0.80) because there
Φ_Q cancels (Lemma 3.2 of the hybrid memo). Spacing 2 is the opposite case: E_P is minimal (only
α = ½ survives), and the field is not small.

## 4. The corrected reduction and Conjecture 3.2′

For a component I of {Φ < 0}, let

    D_I(Φ) := sup over finite real multisets R ⊂ I with integer multiplicities of
              −[ Σ_R (W_j² − cost_j) + Σ_{j≠j'∈R} W_jW_{j'} r(x_j − x_{j'}) + 2 Σ_R W_j Φ(x_j) ].

D_I is finite. Cut I into pieces of length ≤ ½ and drop the bonds between pieces (r ≥ 0). This gives
D_I ≤ Σ_pieces Ψ_c(sup Φ⁻/2) with ρ_c ≥ rmin(½) = 0.471. For any partition of I into cells, D_I is at most
the H1 damage of that partition, so 3.2′ below is implied by 3.2 and is strictly weaker.

**Proposition 4.1 (PROVED).** Let P be a finite set of pairs at height v with integer multiplicities.
Suppose

    Σ_I D_I(Φ) ≤ E_P + Σ_{k≠k'} W_kW_{k'} r(x_k − x_{k'}) + Σ_k W_k(W_k − 2).                      (3.2′)

Then (**) with κ = 1 holds for every Z = P ∪ R, where R is any finite real multiset.

*Proof.* Use the identity (1.1). Drop ∫ŝ|S_{Z₀}|² ≥ 0. A real atom with Φ(x_j) ≥ 0 contributes
W_j² − cost_j ≥ 0, bonds r ≥ 0 with every other atom, and a field term ≥ 0: drop it. For the remaining atoms,
drop the bonds between atoms in different components (r ≥ 0). The real atoms in one component I then
contribute at least −D_I. □

The proposition is uniform in |Z| and in the multiplicities. It uses conjugation closure only through the
pair form of S_Z, and it uses no RH-type hypothesis.

**Conjecture 3.2′ (CONJECTURE for 0.08 < v ≤ V₁, with some V₁ < 66; see Section 6 for why an upper limit is
needed).** (3.2′) holds for every finite P at height v.

*Evidence (NUMERICAL, Parts 3–4).* D_I is computed exhaustively over ≤ 2 atoms on a mesh of 0.02, plus a
unit-weight local search from six starts. On the 56 lattices of Section 3 the worst ratio is 0.868
(v = 0.2, L = 2). On 120 two-pair motifs {0, d} + L**Z** (v ∈ [0.2, 1.5], L ∈ [2, 5], d ∈ [0.25, 1.25]) it
is 0.833, attained at (0.2, 3, 1), while the H1 ratio there reaches 2.10. On 60 random motifs (2–4 pairs,
W ∈ {2, 4}, period 3–8) it is 0.318. On every configuration that refutes 3.2 the component-local ratio is
0.33–0.58. The computed D_I is a lower estimate (local optimisation), so these are NUMERICAL, not
certificates. The binding regime is small v, where 3.2′ coincides with H1's bookkeeping for isolated pairs
(0.81–0.87).

**What a proof of 3.2′ needs.** Two things, neither available. (a) A rigorous upper bound for D_I. The
continuum part is a copositive QP on the component; the integer part is H1's pen. (b) A uniform bound of
Σ_I D_I by the energy. For (b) the quadratic part is the multi-point duality of Section 5, and the linear
part (doubles are free, D_I ≈ 4 sup_I Φ⁻ for small fields) needs Σ_I sup_I Φ⁻ ≲ E_P + bonds. That
L¹-against-L² bound holds only because a negative component needs Φ_Q < −Φ_r there, and Φ_r ≥ r ∗ μ_P is
large near every pair. No such estimate is proved here.

## 5. Field–energy duality (the Cauchy–Schwarz/large-sieve idea, made exact)

Let m_v(α) = ρ(α) tanh²(παv) and M_v(x) = ∫ m_v(α) e(αx) dα, so that M_v(0) = τ₀(v).

**Lemma 5.1 (PROVED).** Let P have real weights W_k of either sign. For any points y_1, …, y_N and any b ∈ **R**^N,

    (Σ_c b_c Φ_Q(y_c))² ≤ E_P · Σ_{c,d} b_c b_d M_v(y_c − y_d).

In particular Φ_Q(y)² ≤ τ₀(v)E_P, and Σ_c Φ_Q(y_c)² ≤ λ_max([M_v(y_c − y_d)]) E_P. The constant τ₀(v) is sharp
over signed P.

*Proof.* Φ_Q(y) = ∫ f_v(α) \bar S_P(α) e(αy) dα. Put B = Σ_c b_c e(αy_c). Cauchy–Schwarz with the weight
ρ sinh²(2παv) gives |∫ f_v \bar S_P B|² ≤ ∫ρ sinh²|S_P|² · ∫ (f_v²/(ρ sinh²))|B|². Moreover
f_v²/(ρ sinh²) = ρ(c − 1)²/(c² − 1) = ρ(c − 1)/(c + 1) = m_v. Equality holds when S_P ∝ \bar B/(c + 1).
For N = 1 this is the signed measure −(1/2)FT[sech²(παv)](· − y), which is approached by finite signed
sums. □

**Corollary 5.2 (PROVED).** For positive P, Φ⁻(y)² ≤ τ₀(v)·(E_P + Σ_{k≠k'} W_kW_{k'} r(Δ)) at every y.
(Indeed Φ ≥ Φ_Q because Φ_r ≥ 0, and the bonds are ≥ 0.) Values: τ₀(v) = 0.0092 (v = 0.08), 0.054 (0.2),
0.236 (0.5), 0.486 (1), 0.713 (2), 0.886 (5), 0.949 (10), 0.981 (20), 0.9997 (50), 1.006 (100). Also
τ₀(v) ↑ R = 1.01246 as v → ∞, and **τ₀(v) = 1 at v = 51.3**.

*Positive P (NUMERICAL, Part 5).* The quantity sup_{P ≥ 0} Φ⁻(y)²/(E_P + bonds) can be computed as a convex
QP over densities on a window [−6, 6] with mesh 0.1; integrality is irrelevant at large scale. The window
values are lower bounds: κ(0.2) ≥ 0.0033, κ(0.5) ≥ 0.111, κ(1) ≥ 0.381, κ(2) ≥ 0.635, against the
upper bounds τ₀. Without the bonds the QP gives 0.94τ₀–0.95τ₀, and its optimiser spreads to the window
edges. It forms a positive background with a hole at y, the construction of Section 6. For comparison,
one pair alone reaches only max_t Q_v⁻(t)²/X(v) = 0.018, 0.073, 0.085, 0.033. So the per-pair duality
of H1 is 5–20 times better than the joint duality. The joint field gives up that factor and gains the
cancellation.

*Consequence for 3.2′.* For one component with one heavy atom, D_I ≈ (Φ⁻ + 1)². By Corollary 5.2 its
quadratic part is at most τ₀(v) times the resource. That leaves room for v < 51 but none beyond. Below
v ≈ 2 the positive-P constant κ(v) ≤ 0.71 leaves room for a multi-component version, provided the
multi-point Gram matrix stays close to diagonal. In the computed cases, two points at distance 1 and
three points at spacing 2 give 0.16–0.39 and 0.39–0.53 at v = 1–2 (scratch runs, not in the default
script). The linear part (Section 4(b)) remains the obstacle at small v.

## 6. Large heights: the ŝ-term cannot be dropped (HEURISTIC; continuum computation CHECKED, Part 6)

Every H1-type reduction, including 3.2 and 3.2′, discards ∫ŝ|S_{Z₀}|² in (1.1). Here ŝ = −c_LP ≥ 0 on
1 < |α| < 2.5, and ∫ŝ = s(0) = R − 1 = 0.012460. The following one-layer family shows that this loses (**)
at order Λ² once v ≳ 66.

Take b(x) = sech(πx/(2v))/(2v), whose Fourier transform is sech(2παv) = 1/c, and
β(x) = sech(πθx/(2v))/(2v) with θ = ½, so β ≥ b. Put pairs of density Λν, with ν = β − b ≥ 0 of mass 1, at
height v, and one real atom of weight Λ at 0. Then S_Z/Λ = 1 + c(β̂ − 1/c) = cβ̂ exactly, and

    [Σ_Z(ρ) − ∫ŝ|S_{Z₀}|²]/Λ² = ∫ρ c²|β̂|² − ∫ŝ|1 + ν̂|² =: Q(v).

The first term is ≈ 0.82/v, because c²|β̂|² = 4cosh²(2παv)/cosh²(4παv) decays like e^{−4π|α|v}. The second
term is s(0) up to e^{−2πv}. Quadrature gives Q = +0.070 (v = 10), +0.029 (20), +0.004 (50), −0.00001 (66),
−0.0042 (100) and −0.0084 (200). So Σ_Z(ρ) − cost − ∫ŝ|S_{Z₀}|² = Λ²Q + O(Λ log Λ) < 0 for large Λ when
v ≥ 70. Meanwhile Σ_Z(ρ)/cost → ∞: (**) is not threatened, only the reductions are.

*Transfer to integer configurations (not proved).* Realise Λν by weight-2 pairs at its quantiles, truncated
where the density falls to 1. That changes ν̂ on |α| ≤ 2.5 by O(v) in absolute terms (second-order
quadrature error, and an O(v) tail mass). So Σ_Z changes by O(Λ v e^{2πv} + v²e^{4πv}). Taking
Λ ≫ v e^{2πv}/|Q| gives finite configurations violating every ŝ-free bookkeeping, 3.2′ included. This is
consistent with Section 5: the duality constant τ₀ crosses 1 at v = 51.3. It is consistent with H1,
because a single pair cannot form the hole. The adversarial searches never reached v ≳ 50.

*Consequence.* At heights v ≳ 50, a proof of O2, and a fortiori of (**), must keep the ŝ-energy of the
collapsed configuration, or must avoid (1.1). This is why Conjecture 3.2′ is stated only up to some V₁ < 66.

## 7. What remains, and self-check

**State of O2.** It remains OPEN. The precise missing statements are (a) and (b) of Section 4 for
0.08 < v ≤ V₁, plus, for large v, an argument that uses ∫ŝ|S_{Z₀}|². For example: bound the field of a
"hole" configuration by the ŝ-energy of the hole's own real counterpart, since 1 − R(1 − s(0)) = s(0)² > 0
is the exact asymptotic margin of a single heavy atom facing the extremal hole. The full (**) still
needs O1, O3 and the multi-layer induction of the parent memo. The two-layer analogue of 3.2 is refuted
with 3.2 (Section 2.2). Its component-local version is the natural replacement, and it inherits the
large-height caveat.

**Unconditional proportion.** Unchanged, 0.6725162800. Nothing here is a certificate for (**) in a new
case, so no row is added to the status table.

| item | status | RH / reality of zeros | uniform in \|Z\| | integer multiplicities | conjugation closure |
|---|---|---|---|---|---|
| normalisation of (3.2) | PROVED (reduction rechecked) | none | yes | via pen_c | yes |
| counterexample to 3.2, n = 20, 40 | REFUTED; NUMERICAL, all approximations conservative | none | finite P | W = 2 | yes |
| (**) on those configurations, ratio ≥ 1.46 | NUMERICAL | none | finite / periodic | yes | yes |
| Prop. 4.1 (3.2′ ⇒ O2) | PROVED | none | yes | W² ≥ cost, r ≥ 0 | yes |
| Conj. 3.2′, v ≤ V₁ | CONJECTURE; NUMERICAL on 236 configurations, worst 0.87 | none | — | essential | — |
| Lemma 5.1, Cor. 5.2 | PROVED | none | yes | not used | — |
| κ(v) window values, τ₀(v) | NUMERICAL / CHECKED quadrature | none | — | irrelevant at scale | — |
| Section 6, Q(v) < 0 for v ≥ 70 | continuum computation CHECKED; transfer HEURISTIC | none | needs Λ ≫ e^{2πv} | via quantile discretisation | yes |

No step uses β = 1/2. The status-table caveat of the parent memo stands: O2 (≥ 2 common-height pairs
with reals, v > 0.08) is the first open sub-case. The route proposed there (3.2) is now closed, and the
replacement (3.2′) is open for moderate v and blocked at large v unless ∫ŝ|S_{Z₀}|² is used.
