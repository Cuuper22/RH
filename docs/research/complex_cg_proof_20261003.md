# Towards a proof of the complex Cheer–Goldston inequality (**)

Research note, 2026-10-03. Companion script
[`verify/complex_cg_proof.py`](../../verify/complex_cg_proof.py) (output
`verify/complex_cg_proof.out`). Builds on `positivity_class_20261003.md` (the
parent memo; its notation is used) and on the adversary memo
`complex_cg_adversary_20261003.md`. Labels: PROVED (complete argument here),
CHECKED (floating-point computation with explicit error allowances; the LP
constants are not interval-certified but every inequality below has a
margin far above double-precision error), NUMERICAL (optimisation without
certificate), CONJECTURE, REFUTED.

## 0. Summary

* **Real case certified (Theorem 1, PROVED + CHECKED).** A Cheer–Goldston test
  r̂ (piecewise linear on the 0.01 grid of [0, 2.5], r̂ ≤ 0 on [1, 2.5]) with
  r(0) = 1, P(ρ) = ρ(0) + ∫|α|ρ = **1.3210847**, R = ∫ρ = 1.0124602, and
  **r ≥ 0 on all of R proved exactly** through the jump representation
  r(u) = −T(u)/(2π²u²) with T an even 100-periodic trigonometric polynomial.
  Hence κ_real(ρ) ≥ 1 (Prop. 3 of the parent memo), and (**) for complex Z with
  this ρ would give the unconditional proportion 2 − P = **0.6789153**. The
  parent memo's LP test was only grid-positive (min r = −2·10⁻⁵).
* **The natural strengthenings are false (Theorems 2–3, REFUTED, CHECKED).**
  (i) The real-weight relaxation of (**) — copositivity of the kernel
  t(v_j, v_k, Δ_jk) − κδ_jk on R₊ⁿ — fails for two atoms (a real atom and a
  pair at height 0.85 and distance 0.71, weight ratio ≈ 40). Therefore **no
  "r + s" certificate on the half-plane** (nonnegative kernel plus positive
  definite kernel, the only structure that proves the real case) can prove
  (**): every proof must use the integer cost structure, i.e. the slack
  κ(W² − cost) of heavy atoms. (ii) Σ_Z(ρ) ≥ Σ_{Z₀}(r) is false. (iii) For every
  piecewise-linear ρ (any nodes) and every w > 0, the termwise bounded-height
  condition Re r_in(u + iw) ≥ s(u) fails at arbitrarily large u (echo of the
  kinks); numerically, the LP that enforces it on [0, 60] already costs
  P = 1.3264 at heights ≤ 0.025 and crosses the frontier before 0.05. The
  termwise route is dead.
* **Bounded-height theorem (Theorem 4, PROVED modulo CHECKED constants).** For
  the certified ρ and κ = 1, (**) holds for every conjugation-invariant
  multiset Z whose conjugate pairs have scaled height ≤ V₀, uniformly in |Z|,
  for V₀ = **V0STAR** (the script prints the largest admissible value in its
  list). The proof pays the lifting loss of a pair out of its own self-term
  excess ∫ρ sinh²(2παv) ≥ 4π²q(0)v² when its neighbourhood is sparse (weight
  ≤ 2 at each critical distance) and out of the clustering slack
  Σ W_jW_k r(Δ_jk) + κ(W² − cost) when it is dense. Two numerical inequalities
  (A), (B) between computed constants close the argument. For zeta this is
  the statement: *if all zeros with T < γ ≤ 2T satisfy |β − 1/2| ≤ 2πV₀/log T,
  then at least 67.89 % of them are simple and on the line* (BGSTB 2023,
  Thm. 2, prove 61.7 % under |β − 1/2| < 1/(2 log T), i.e. V₀ = 1/(4π) =
  0.0796; our V₀ is smaller, so the two results are not comparable).
* **Open.** (**) for unbounded heights. The adversary memo found no
  counterexample (infimum 1.00025, attained by real designs) and conjectures
  κ_C = κ_real for nonincreasing ρ. Section 5 records why the obstacles found
  here (Theorem 2) make a "soft" proof unlikely and what a complete proof must
  contain. **No unconditional proportion above 0.6725043820976 is certified.**

## 1. Setting and the basic reduction

Atoms j = 1..n with positions x_j ∈ R, integer weights W_j ≥ 1 and heights
v_j ≥ 0: a real atom of multiplicity m has W = m, v = 0, cost 2m − [m = 1]; a
conjugate pair x ± iv of multiplicity m has W = 2m ≥ 2, cost 4m = 2W. Always
cost_j ≤ W_j² and W_j² − cost_j ≥ W_j(W_j − 2)₊. Then

    S_Z(α) = Σ_j W_j cosh(2παv_j) e(αx_j),   Σ_Z(ρ) = Σ_{j,k} W_jW_k t_jk,
    t_jk = t(v_j, v_k, Δ_jk) = ∫ρ(α) cosh(2παv_j) cosh(2παv_k) cos(2παΔ_jk) dα,

Δ_jk = x_j − x_k, all integrals over [−1, 1]. Let r = r_in − s be the CG test
(r̂ = ρ − ŝ, ŝ ≥ 0 supported in 1 ≤ |α| ≤ 2.5, r ≥ 0 on R, κ = r(0) = R − s(0)).

**Step 1 (PROVED).** Σ_{j,k} W_jW_k s(Δ_jk) = ∫ŝ|S_{Z₀}|² ≥ 0 (Lemma 0 of the
parent memo for the collapsed real multiset Z₀). Since t_jj − s(0) = R − s(0)
+ ∫ρ sinh²(2παv_j) = κ + X_j,

    Σ_Z(ρ) − κ·cost ≥ Σ_j W_j² X_j + Σ_{j≠k} W_jW_k G_jk + κ Σ_j (W_j² − cost_j),      (1.1)
    X_j = ∫ρ sinh²(2παv_j) ≥ 4π²q(0) v_j²,   q(u) = ∫ρ α² cos(2παu),
    G_jk = t_jk − s(Δ_jk)   (= r(Δ_jk) when both atoms are real).

All three groups on the right are "resources" except the negative values of
G_jk, which occur only for bonds involving a pair.

## 2. Theorem 1: a certified real constant

**Theorem 1 (PROVED, constants CHECKED).** There is an even piecewise-linear
r̂ on the 0.01 grid of [−2.5, 2.5] with r̂ ≤ 0 on 1 ≤ |α| ≤ 2.5, r(0) = 1,
r ≥ 0 on R, P(ρ) = 1.3210847 (ρ = r̂·1_{[−1,1]} ≥ 0, R = 1.0124602, ρ(0) =
1.004442). Consequently κ_real(ρ) ≥ 1 and κ_real(ρ) ≤ ρ(0) = 1.004442
(adversary memo, Lemma 4).

*Proof.* The LP of the parent memo is re-solved with the constraint
r(u) ≥ 10⁻⁶ on the grid u ∈ 0.001·Z ∩ [0, 50] (the margin costs 1.4·10⁻⁴ in P;
without it the fine grid alone gives 1.3209465). Positivity on all of R is
then exact: for a continuous piecewise-linear r̂ with nodes α_k = k/100 and
jumps J_k of r̂' at the nodes, two integrations by parts give, for u ≠ 0,

    r(u) = −T(u)/(2π²u²),   T(u) = J₀/2 + Σ_{k≥1} J_k cos(2πα_k u),

so T is an even trigonometric polynomial with period 100, and r ≥ 0 on R iff
T ≤ 0 on [0, 50]. Near 0, r(u) ≥ r(0) − u·2π∫|α||r̂| = 1 − 2.0986u > 0 for
u ≤ u₀ = 0.4289, so T ≤ 0 on [0, u₀]. On [u₀, 50] the script covers the
interval by cells of length h = 5·10⁻⁴ and uses T(u) ≤ T(u_i) + T'(u_i)(u − u_i)
+ ‖T''‖_∞ (u − u_i)²/2 with ‖T''‖_∞ ≤ 4π²Σ|J_k|α_k² = 89.65; the cell maxima
are all ≤ −2.2·10⁻⁶ (floating point, with 4·10⁻¹² Σ|J_k| added for rounding).
The representation itself is checked against direct quadrature to 2·10⁻¹⁶.
Finally κ_real ≥ r(0) is Prop. 3 of the parent memo (Cheer–Goldston). □

Remarks. (a) The LP forces r(100) = 0 exactly (T(100) = T(0) = 0), which is why
a margin cannot be imposed beyond u = 50; periodicity makes it unnecessary.
(b) The adversary memo's tight real designs (period 7, five doubles) give
ratio 1.0007 for this ρ on a 60-period block, consistent with κ_real ∈
[1, 1.0044].

## 3. Theorems 2–3: what cannot work

**Theorem 2 (REFUTED, CHECKED): the real-weight relaxation.** Let (**)_cont be
the statement ∫ρ|Σ_j W_j cosh(2παv_j)e(αx_j)|² ≥ κ Σ_j W_j² for all real
W_j ≥ 0, x_j, v_j ≥ 0, i.e. copositivity of [t_jk − κδ_jk]. For the certified
ρ and κ = 1 it fails for n = 2: with a real atom at 0 and a pair at
0.71 ± 0.85i, t(0, 0.85, 0.71) = −3.322 < −√(g₀g') = −1.280, where
g₀ = R − 1 = 0.01246, g' = t(0.85, 0.85, 0) − 1 = 131.5; the 2×2 matrix
[[g₀, t], [t, g']] has a negative eigenvalue with an eigenvector of constant
sign (weight ratio W₀/W₁ ≈ 40). In the integer problem this configuration
needs a real zero of multiplicity ≈ 40–900 and is harmless because of the cost
slack κ(m² − 2m).

*Consequence (PROVED).* Any certificate of the form t(v, v', Δ) = r̃(v, v', Δ) +
σ(v, v', Δ) with r̃ ≥ 0, r̃(v, v, 0) ≥ κ and σ a positive-definite kernel on the
half-plane {(x, v)} (translation invariant in x; by Bochner,
σ = ∫e(αΔ)dM_{vv'}(α) with M a positive-definite-kernel-valued measure) proves
(**)_cont, hence does not exist. The real case is proved by exactly such a
certificate (r + s). So every proof of (**) must use that W_j are integers
and that cost_j < W_j² for heavy atoms. In the same vein the intermediate
inequality Σ_Z(ρ) ≥ Σ_{Z₀}(r) (which would reduce (**) to the real case) is
false: Z = {0^{512}} ∪ {0.70 ± 1.18i} gives 247 339 < 262 534, while (**)
holds there with ratio 240.

**Theorem 3 (PROVED; echo obstruction).** Let ρ be even, continuous,
piecewise linear with finitely many nodes (any positions), supported in
[−1, 1], and let s be any completion with ŝ'' ∈ L¹ (in particular any
piecewise-linear ŝ). Then for every w > 0 there are arbitrarily large u with
G(u, w) := Re r_in(u + iw) − s(u) = ∫ρ cosh(2παw) cos(2παu) − s(u) < 0.

*Proof.* Put f_w = ρ cosh(2πα w). Then f_w'' = Σ_k J_k cosh(2πα_k w) δ_{α_k}
+ g_w with g_w = 2ρ'(2πw) sinh(2παw) + ρ(2πw)² cosh(2παw) ∈ L¹, so
FT(f_w)(u) = −(4π²u²)⁻¹[T_w(u) + FT(g_w)(u)] with the trigonometric sum
T_w(u) = Σ_k J_k cosh(2πα_k w) e(α_k u). Two integrations by parts give
T_w(0) = ∫cosh(2παw) dρ'(α) = (2πw)² ∫ρ cosh(2παw) > 0. T_w is a finite
trigonometric sum, hence almost periodic: for every ε there are arbitrarily
large u with T_w(u) > T_w(0) − ε. By Riemann–Lebesgue FT(g_w)(u) → 0 and
FT(ŝ'')(u) → 0, so s(u) = o(u⁻²), and G(u, w) ≤ −(T_w(0)/2)/(4π²u²) + o(u⁻²) < 0
along such u. □

For the grid-PL class the obstruction is concrete: T_w has period 100, so
G(100, w) = −(2πw)² ∫ρ cosh(2παw)/(4π²·10⁴) + FT(g_w)(100)/(4π²10⁴); the script
finds G(100, 0.02) = −4.06·10⁻⁸, G(100, 0.05) = −2.55·10⁻⁷, G(100, 0.1) =
−1.04·10⁻⁶, each equal to the predicted leading term to three digits. For a ρ
with kinks only at 0 and ±1 (C² in between) the same computation shows the
necessary condition |ρ'(0⁺)| ≥ |ρ'(1⁻)| cosh(2πw) − ŝ'(1⁺); for the LP shape
(|ρ'(0⁺)| ≈ 0.39 < |ρ'(1⁻)| ≈ 0.59) this already fails at w = 0, and the
re-optimised LP with G(u, w) ≥ 0 imposed for w ≤ W on a grid u ≤ 60
(NUMERICAL, `lp_height` runs recorded in the scratch output) gives
P = 1.32644 (W = 0.05), 1.34265 (0.10), 1.40329 (0.20), 1.73300 (0.50): the
proportion drops below the frontier before W = 0.1. Termwise domination, even
for bounded heights, is therefore not the way; the self-term excess X_j must
be used.

## 4. Theorem 4: (**) for bounded heights

Fix V₀ > 0 and write m(Δ) = sup_{0<|w|≤2V₀} (−Q_w(Δ)/w²) with
Q_w(Δ) = ∫ρ(cosh(2παw) − 1) cos(2παΔ) dα, m₊ = max(m, 0). (As w → 0,
−Q_w/w² → −2π²q(Δ), so m₊ ≈ 2π²[−q]₊; m₊(Δ) ≤ C_m/Δ² with the explicit
C_m = sup_w ‖(ρ(cosh(2πα w) − 1))''‖_TV /(4π²w²).) Define

    β(Δ) = [m₊(Δ) − r(Δ)/(2V₀²)]₊,     r₁(Δ) = (r(Δ) − 2V₀² m₊(Δ))·1[β(Δ) = 0] ≥ 0.

**Lemma 4.1 (PROVED).** For 0 ≤ v_j, v_k ≤ V₀: G_jk ≥ r₁(Δ_jk) − β(Δ_jk)(v_j² + v_k²).

*Proof.* cosh a cosh b = [cosh(a + b) + cosh(a − b)]/2 gives
G_jk = r(Δ) + [Q_{v_j+v_k}(Δ) + Q_{v_j−v_k}(Δ)]/2 ≥ r(Δ) − m₊(Δ)[(v_j+v_k)² +
(v_j−v_k)²]/2 = r(Δ) − m₊(Δ)(v_j² + v_k²), using |v_j ± v_k| ≤ 2V₀. If β(Δ) = 0
then m₊ ≤ r/(2V₀²) and G_jk ≥ r − 2V₀²m₊ = r₁. If β(Δ) > 0 then, as
v_j² + v_k² ≤ 2V₀² and r ≥ 0, G_jk ≥ (v_j² + v_k²)(r/(2V₀²) − m₊) = −β(v_j² + v_k²). □

**Windows and clusters.** supp β ∩ (0, ∞) is a union of intervals ("windows"),
all contained in |Δ| ≥ 0.9 (β = 0 where r is not small). Group consecutive
windows into *clusters* C₁, C₂, …: disjoint intervals of diameter ≤ w* = 1/2
covering supp β ∩ (0, ∞), and put β_c = sup_{C_c} β. (The script forms the
clusters greedily on [0.5, 150]; for Δ > 150 it uses r(Δ)Δ² = r(δ)δ²,
δ = dist(Δ, 100Z), from the periodicity of T, so that β(Δ) > 0 forces
r(δ)δ² < 2V₀²C_m, i.e. δ ∈ E := {δ ∈ [−50, 50] : r(δ)δ² < 2V₀²C_m}; the far
clusters are the components of 100n + E, n ≥ 2, each with β_c ≤ C_m/(100n − 50)²,
and the script checks that the components of E have diameter ≤ 1/2.) Put

    Σβ := Σ_c β_c  (all clusters),   ρ* := min_{0≤Δ≤w*} (r(Δ) − 2V₀² m₊(Δ)) = min_{[0,w*]} r₁.

**Theorem 4 (PROVED, given the CHECKED constants).** Suppose

    (A)  4 Σβ ≤ 4π² q(0),        (B)  24 V₀² Σβ ≤ ρ*.

Then Σ_Z(ρ) ≥ κ(2|Z| − s₁(Z)) with κ = r(0) = 1 for every finite
conjugation-invariant multiset Z all of whose pairs have height ≤ V₀.

*Proof.* Let P be the set of pairs. By (1.1) and Lemma 4.1,

    Σ_Z(ρ) − cost ≥ Σ_{k∈P} W_k² X_k − 2 Σ_{k∈P} v_k² W_k L_k + S,
    L_k := Σ_{j≠k} W_j β(Δ_jk),   S := Σ_{j≠k} W_jW_k r₁(Δ_jk) + Σ_j (W_j² − cost_j),

because Σ_{j≠k} W_jW_k β(Δ_jk)(v_j² + v_k²) = 2Σ_k v_k² W_k L_k (v_k = 0 off P).

*Slack.* Let ψ_j := Σ_{j'} W_{j'} 1[|x_{j'} − x_j| ≤ w*] ∈ Z, ψ_j ≥ W_j. Since
r₁ ≥ ρ* on [−w*, w*] (there are no windows there),
Σ_{j≠k} W_jW_k r₁(Δ_jk) ≥ ρ* Σ_j W_j(ψ_j − W_j), and Σ_j(W_j² − cost_j) ≥
Σ_j W_j(W_j − 2)₊. Per atom, ρ*(ψ − W) + (W − 2)₊ ≥ max(0, ρ*(ψ − 2)) (for W ≥ 2
use ρ* ≤ 1; for W = 1 it is ρ*(ψ − 1)). Hence

    S ≥ ρ* Σ_j W_j (ψ_j − 2)₊.                                                     (4.1)

*Sparse load, paid by the excess.* Split L_k = L_k^a + L_k^b with
L_k^a = Σ_j W_j β(Δ_jk) min(1, 2/ψ_j). For a cluster C and a sign ±, the atoms
j ∈ x_k ± C are pairwise within w*, so ψ_j ≥ A := Σ_{j∈x_k±C} W_j for each of
them and Σ_{j∈x_k±C} W_j min(1, 2/ψ_j) ≤ min(A, 2) ≤ 2. Summing over the
clusters and signs, L_k^a ≤ 4Σβ, so by (A) and W_k ≥ 2,

    2 v_k² W_k L_k^a ≤ 2 v_k² W_k · 4π² q(0) ≤ 4π² q(0) W_k² v_k² ≤ W_k² X_k.

*Dense load, paid by the slack.* L_k^b = Σ_{j: ψ_j≥3} W_j β(Δ_jk)(1 − 2/ψ_j) (the
terms with ψ_j ≤ 2 vanish; ψ_j is an integer). Bound v_k² ≤ V₀² and charge the
bond (j, k) to atom j if ψ_k ≤ ψ_j and to the pair k otherwise. Atom j receives
at most 2V₀² W_j Σ_{k∈P, ψ_k≤ψ_j} W_k β(Δ_jk); the pairs k in x_j ± C have
ψ_k ≥ B := their total weight, so if any of them has ψ_k ≤ ψ_j then B ≤ ψ_j, and
the sum is ≤ Σ_{C,±} β_c min(B, ψ_j) ≤ 2Σβ·ψ_j. A pair k receives at most
2V₀² W_k Σ_{j: 3≤ψ_j<ψ_k} W_j β(Δ_jk) ≤ 2V₀² W_k · 2Σβ · ψ_k by the same argument
(the atoms j ∈ x_k ± C have ψ_j ≥ A, so A < ψ_k if one of them is charged).
Every receiving atom has ψ ≥ 3, hence ψ − 2 ≥ ψ/3, and receives at most
8V₀² Σβ · W ψ ≤ (ρ*/3) W ψ ≤ ρ* W (ψ − 2) by (B). Summing over atoms and
using (4.1), the dense load is at most S.

Adding the two parts, Σ_Z(ρ) − cost ≥ 0. □

**Constants (CHECKED by the script; see `complex_cg_proof.out`).** With
q(0) = 0.148400 the budget in (A) is π²q(0) = 1.4646 for Σβ. The script
evaluates β on the grid 0.001 of [0.5, 150] with the sup over w on a grid of
24 values in (0, 2V₀], forms the clusters, bounds the far tail as described,
and reports:

TABLE4

The windows sit at the near-zeros of r (near the integers, where r has
double zeros of size ≈ 10⁻⁶ by the LP margin) and the first cluster, around
Δ ≈ 1.05 where q = −0.046, carries most of Σβ (β_c ≈ 0.95 ≈ 2π²·0.046). (B)
holds with a large margin (ρ* ≈ 0.47); (A) is the binding constraint, and it
fails from V₀ ≈ 0.04–0.05 on because the windows widen and merge and the
Taylor remainder of cosh grows. The admissible V₀ = V0STAR corresponds for
zeta to |β − 1/2| ≤ 2π V₀/log T = SCALED/log T.

Remarks. (a) Nothing in the proof depends on |Z|; all heights ≤ V₀ including
zero are allowed, so the real case is recovered (with Theorem 1). (b) The
proof uses only: r ≥ 0, ŝ ≥ 0 (Lemma 0), the two-sided structure of
cosh a cosh b, and counting; no RH, no reality of zeros. (c) The constant 2 in
min(1, 2/ψ_j) is forced by W_k ≥ 2 (pairs of multiplicity one are cost-tight:
cost = W² = 4); the margin in (A) at V₀ = 0.03 is about 10 %, so the method
cannot reach heights of order 0.1 without a new idea — for instance using
the slack ∫ŝ|S_{Z₀}|² (not used here) or the exact bond structure instead of
the cluster suprema.

## 5. What remains, and an honest assessment

* (**) is open for heights above V₀ ≈ 0.03–0.04 (scaled), i.e. for zeros with
  |β − 1/2| ≳ 0.2/log T. Lifting lowers Σ only near heavy mass (adversary
  memo), and every such configuration found has ratio ≥ 1.087, but Theorem 2
  shows that any proof must track the integer cost slack — there is no
  positive-definite/nonnegative kernel decomposition behind (**).
* A proof for all heights along the lines of Theorem 4 would need to replace
  the budget inequality (A), which compares the pair excess 4π²q(0)v² with the
  sparse load 2·(2Σβ)v² at second order in v, by an argument valid when the
  excess ∫ρ sinh²(2παv) ≈ e^{4πv}/(32π²v²)·|ρ'(1)| is exponentially large but
  the cross terms Re r_in(Δ + i(v+v')) ≈ −e^{2π(v+v')}/(8π²(v+v')²)·|ρ'(1)| at
  Δ ≡ 1/2 mod 1 are of the same exponential order when v' ≈ v. The common-height
  factorisation (Prop. 5(ii) of the parent memo) shows that these large
  cross terms are always dominated after summation, but a termwise or cluster
  bookkeeping as in Section 4 does not see the cancellation; the missing tool
  is a lower bound for ∫ρ|S|² that keeps the quadratic structure of the pairs
  at different heights (a "two-height" Prop. 5).
* The adversary's conjecture κ_C(ρ) = κ_real(ρ) for nonincreasing ρ is
  plausible but a layer-cake proof fails because the indicators 1_{[−a,a]} have
  κ_real(1_{[−a,a]}) = a·κ_real(1_{[−1,1]}) ≤ a, so ∫κ_real dμ ≤ ∫₀¹ρ = R/2 ≈ 0.51:
  the sum of the infima is far below the infimum of the sum.
* **Certified unconditional bound from this class: none above 0.6725043820976.**
  Theorem 1 fixes the conditional value at 0.6789153 (κ = 1) and Theorem 4
  proves the required inequality for all configurations with pair heights
  ≤ V0STAR.

## 6. Self-check

| step | status | RH / real-zero use |
|---|---|---|
| r ≥ 0 on R for the certified test | CHECKED (exact jump representation, cell bounds, floating point) | none |
| κ_real(ρ) ≥ 1 | PROVED (Prop. 3 of parent memo) | real differences only |
| (**)_cont false; no half-plane r + s certificate | REFUTED / PROVED | — |
| Σ_Z(ρ) ≥ Σ_{Z₀}(r) | REFUTED | — |
| echo obstruction, PL ρ | PROVED; CHECKED at u = 100 | — |
| termwise bounded-height LP cost | NUMERICAL (grid u ≤ 60, not a certificate) | — |
| Lemma 4.1, slack bound (4.1), bookkeeping | PROVED | none |
| constants Σβ, ρ*, C_m, E | CHECKED (grids 0.001 in Δ, 24 values in w) | — |
| (**) for heights ≤ V0STAR | PROVED modulo the CHECKED constants | none |
| (**) for all heights | CONJECTURE (no counterexample; adversary memo) | — |
