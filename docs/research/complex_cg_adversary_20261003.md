# Adversarial test of the complex Cheer–Goldston inequality (**)

Research note, 2026-10-03. Companion script
[`verify/complex_cg_adversary.py`](../../verify/complex_cg_adversary.py)
(output `verify/complex_cg_adversary.out`, default run about 4 minutes on 4 cores).
Builds on [`positivity_class_20261003.md`](positivity_class_20261003.md) and its script,
whose LP (Part A) is copied verbatim to produce ρ. Labels: PROVED (full argument here),
CHECKED (exact or 30-digit evaluation in the script), NUMERICAL (optimisation without
certificate), CONJECTURE, REFUTED.

## 0. Verdict

* **(\*\*) for the LP-optimal ρ with κ = 1 is not refuted.** Over about 2,400 local
  optimisations of periodic configurations (exact per-period quadratic form; up to
  40 atoms per period, multiplicities up to 3, pairs of multiplicity up to 2,
  heights v ∈ [0, 2]), 128 finite configurations with 15–60 atoms, fixed-height scans,
  and density-1 restricted runs, the smallest ratio Σ_Z(ρ)/(2N − s₁) found is
  **1.0002544** (CHECKED at 30 digits). It is attained by a **real** design. Every
  minimiser with ratio below 1.01 has all heights v = 0 (NUMERICAL).
* Lifting a pair off the line does lower Σ at some local minima, by up to 8% relative to
  the configuration collapsed at the same positions. Every such local minimum has ratio
  ≥ 1.087, far from tight (NUMERICAL).
* **Correction to the earlier memo.** Its control ρ = 1_{[1/2,1]} does not show a
  complex-only failure. Its true real infimum is 0, not 0.1496: real lattices with spacing
  below 1 send the ratio to 0 (Lemma 4, PROVED; CHECKED: N = 1000 points give 0.0011).
  The memo's real search used at most 12 points.
* **A genuine complex-only gap does exist for some ρ ≥ 0.** For an explicit piecewise
  linear ρ₅₉ (§4), a periodic configuration with two pairs at height 0.4426 gives ratio
  0.214933 (CHECKED). The best real value found is 0.250534 (NUMERICAL). Along the path
  (1−λ)ρ_LP + λρ₅₉ the gap first opens at λ* ≈ 0.91, so the LP ρ is far from admitting
  the mechanism. Across 96 random ρ ≥ 0 this was the only genuine gap. Across 48 random
  **nonincreasing** ρ there was none.
* No cutting plane was triggered, because no configuration violates (\*\*) for the LP ρ. For
  this ρ the route can give at most κ ≤ 1.0002544, i.e. a proportion of at most
  **0.679419**. With κ = 1 it gives 0.679083.

## 1. Setup, scaling, periodic reduction

Same objects as the parent memo: Z is a finite multiset closed under conjugation, and
S_Z(α) = Σ m_j e(αx_j) + Σ 2m_k cosh(2παv_k) e(αx_k). The cost 2N − s₁ is 1 per simple
real atom, 2m per real atom of multiplicity m ≥ 2, and 4m per pair of multiplicity m.

**Scaling (from parent memo §1).** The zero ½ + iγ + (β − ½) maps to z = γ − i(β − ½),
multiplied by L = log T/(2π). Scaled zeros have mean spacing 1 (density 1). A zero off the
line has scaled height v = (β − ½) log T/(2π).

**Lemma 1 (periodic reduction; PROVED, CHECKED).** Let Z_P be P consecutive periods of a
configuration with period M, and let T(α) be S of one period. Then

  Σ_{Z_P}(ρ)/P → (1/M) Σ_{|n|<M} ρ(n/M) |T(n/M)|²   (P → ∞),

for ρ continuous on [−1,1] with ρ(±1) = 0. The LP ρ has ρ(1) = 0.

*Proof.* |S_{Z_P}|² = |T|²·|Σ_{k<P} e(αkM)|². The second factor divided by P is a Fejér
kernel, which converges weakly to (1/M)Σ_n δ(α − n/M), and ρ|T|² is continuous. □

The number of periods P is unrelated to the quantity P(ρ) = 1.32092. A right-continuous
endpoint (ρ(1) ≠ 0) gives the left limit at integer M, and that limit is attained by
periods M − ε. Part 1 checks Lemma 1: a mixed configuration gives 17.8275 / 17.8287 with
50 / 200 periods, against 17.8292 from the formula.

A violation found in the periodic class would therefore give a violation for finite Z,
with an error of order 1/P.

## 2. Exact structural facts

**Lemma 4 (PROVED).** For every even ρ ≥ 0 supported in [−1,1] and continuous at 0,
κ_C(ρ) ≤ κ_real(ρ) ≤ ρ(0).

*Proof.* Take the real lattice {ka : 0 ≤ k < N} with a < 1. Every nonzero frequency n/a
has modulus greater than 1, so by Lemma 1 the ratio Σ/N tends to ρ(0)/a. Now let a → 1⁻. □

For the LP ρ, ρ(0) = 1.003873, so κ = 1 sits 0.39% below this ceiling. For the control
ρ = 1_{[1/2,1]}, ρ(0) = 0, so κ_real = 0. The script also computes exact finite-lattice
sums at spacing 0.9: 0.110, 0.0114 and 0.00114 for N = 10, 100, 1000. Hence the parent
memo's "complex 0.0071 vs real 0.1496" for the control is **REFUTED** as evidence of a
complex-only effect.

**Lemma 2 (pairs-only rigidity; PROVED).** Take p pairs per period M, put
ζ_k^± = e((x_k ∓ iv_k)/M), and let T(n) be the power sum p_n of these 2p points. If
T(1) = … = T(p−1) = 0, then all heights are equal and the pairs form a regular p-gon. In
that case |T(p)| = 2p cosh(2πpv/M) ≥ 2p.

**Lemma 3 (general rigidity; PROVED).** Take D points per period, counted with
multiplicity: each simple real atom is one point e(x/M), and each pair gives two points
ζ^±. If T(n) = 0 for 1 ≤ n ≤ (D−1)/2, then every point is a simple real atom and the
points form a regular D-gon, i.e. a real lattice with spacing M/D.

*Proof of Lemmas 2 and 3.* Let Q(X) = Π(X − ζ). The multiset of points is invariant
under ζ ↦ 1/ζ̄: real atoms lie on the unit circle, and ζ⁺ ↔ ζ⁻ for pairs. Hence
X^D·conj(Q(1/X̄)) = (−1)^D·conj(Q(0))·Q(X), so the coefficients satisfy
conj(q_j) ∝ q_{D−j}. Newton's identities turn p_1 = … = p_m = 0 into
q_{D−1} = … = q_{D−m} = 0, hence q_1 = … = q_m = 0.

- If m ≥ (D−1)/2, then Q = X^D + q₀ with |q₀| = 1. Its roots are simple and lie on the
  unit circle, so the configuration is a regular D-gon. This is Lemma 3.
- In Lemma 2, D = 2p and m = p−1, so Q = X^{2p} + aX^p + q₀. Each ζ^p is one of the two
  roots Y₁, Y₂, with |Y₁Y₂| = 1.
- The roots with ζ^p = Y₁ all have modulus |Y₁|^{1/p}, which forces a common height.
  Each ζ⁺ and ζ⁻ share an argument, so arg Y₁ = arg Y₂.
- Then |T(p)| = p|Y₁ + Y₂| = p(r + 1/r) ≥ 2p. □

Interpretation: complex lifting cannot make the low-frequency spectrum more crystalline
than a real lattice. A periodic configuration whose ratio equals its n = 0 term
ρ(0)N²/(MC) needs T(n) = 0 for 0 < n < M. For a configuration with pairs this is
impossible when M ≥ (D+1)/2. Part 1 illustrates Lemma 3 numerically: the minimal residual
Σ_{n ≤ (D−1)/2} |T(n)|² is bounded below whenever a pair is present (1.0–10 in the cases
run), with v = 0 at the minimiser.

**Second-order lifting (from parent Prop. 5).** Lift a real double at x_j to x_j ± iv.
Then Σ changes by 2(2πv)²C_j + O(v⁴), where C_j = Σ_k m_k q(x_j − x_k) and
q(u) = ∫ρα²cos(2παu). For the LP ρ: q(0) = 0.14875 and min q = −0.08649 at u = 0.775. A
heavy neighbour of mass ratio t lowers Σ only if t > t* = q(0)/|min q| = 1.720.

## 3. Numerics for the LP ρ

ρ is the verbatim LP of the parent script: P = 1.3209166550, R = 1.01261107,
ρ(0) = 1.00387347, ρ(1) = 0, ρ'(1⁻) = −0.448.

| search (script part) | size | min ratio | lifted minimisers |
|---|---|---|---|
| 2a random multiplicity patterns, periodic, M free | 320 patterns × 8 starts | — | — |
| 2b lattice-like starts (K = 6–40 atoms, pair fraction 5–80%, heights started at 0.05–0.6) | 400 runs × 4 | 1.0002544 (2a+2b) | 109 of 720 have v > 10⁻³; all ≥ 1.0868 |
| 2c near-tight real designs with doubles, then every double turned into a pair at v₀ ∈ {.05,.15,.3,.5} and re-optimised | 400 | 1.0002969 | 0 end lifted; min C_j = 0.0408 > 0 |
| 3 finite configurations, 15–60 atoms | 128 | 1.002225 | 11 lifted, all ≥ 1.2397 |
| 6 density exactly 1 (M = N) | 120 patterns × 5 | 1.000861 | none |

**Minimiser (CHECKED, 30 digits): 1.00025443606.** Period M = 7 with atoms at
0, 1.040694, 2.085658, 4.020347, 5.955036. All atoms are doubles, written in the run as two
real doubles plus three pairs at v = 0. Gaps: 1.0407, 1.0450, 1.9347, 1.9347, 1.0450.
Because Σ and cost both scale by 4, five simple atoms at the same positions give the same
ratio.

**Second near-tight design (CHECKED): 1.00029694.** M = 13, eight doubles at 0, 1.982,
3.968, 5.950, 7.903, 8.953, 9.997, 11.047.

These designs sit where the full test r vanishes. The gaps are ≈ 1.04, ≈ 1.95 or ≈ 2.9.
The near-zeros of r are at 1.045, 1.965, 2.125, …, with values of order 10⁻⁵ to 10⁻⁷.

**Fixed-height scan (Part 4).** Start from the M = 13 design and lift one double to a pair
at fixed v, re-optimising everything else. The ratio is 1.000297, 1.000537, 1.001813,
1.006597, 1.029661, 1.138, 1.545 for v = 0, .02, .05, .1, .2, .35, .5. Lifting all doubles
(heights v, 1.5v, 0.5v) grows faster still. The minimum is at v = 0 with positive
curvature.

**Lifted local minima (where lifting helps).** Largest gain: M = 21, two simple atoms
plus 16 pairs (three of multiplicity 2), heights up to 0.573. Ratio 1.25411 against
1.36573 collapsed at the same positions (CHECKED). Coordinates are printed in Part 7.
The pattern is always a pair adjacent (distance ≈ 0.8–1) to heavy mass: a multiplicity-2
pair or a triple, i.e. t ≥ 2 > t*. Heavy atoms cost 2 per unit weight and carry
self-energy m²R, so these configurations are never near 1.

**Restricted adversary (Part 6).** Constraints: density 1, off-line fraction ≤ 7/12, and
off-line fraction ≤ 1/3. Minima: 1.000861, 1.000861 and 1.000989 respectively, all at
v = 0.

Two cautions on the constraints:
- "At most 1/3 off the line" is **not** a theorem. The proved bound is that more than
  5/12 of zeros lie on the line (Pratt–Robles–Zaharescu–Zeindler 2020), so at most 7/12
  are off it. Both caps were run.
- Selberg's N(σ,T) ≪ T^{1−(σ−½)/4} log T gives #{v' ≥ v} ≪ N e^{−πv/2} in scaled units.
  This is no constraint at the relevant heights v ≲ 0.5.

Since the unrestricted search finds no violation, the restricted one cannot either. The
real application also fixes the form factor on [−1,1] (Montgomery/BGSTB), which is a much
stronger constraint and was not imposed.

## 4. Mechanism and margin (task 2)

Two interpolation families toward the old control behave the same way:
- Along (1−λ)ρ_LP + λ1_{[1/2,1]}, the real infimum tracks ρ_λ(0) (Lemma 4).
- Along ρ_LP + λ1_{[1/2,1]}, the real infimum stays at ρ(0) = 1.00387.

In both, the complex pattern infimum stays at or above the real infimum for every λ
tested. So that control is uninformative.

**Genuine example (NUMERICAL, value CHECKED).** ρ₅₉ is piecewise linear through the knots
(0, 0.116944, 0.377430, 0.587747, 0.826066, 1) with values (0.357250, 0.307421, 0.011162,
1.865539, 0, 0). It is then sampled at step 0.005, interpolated linearly, and normalised
to R = 1. It is generated reproducibly by `random_rho(59)`.

- Complex minimiser: period M = 32/3 with five pairs of multiplicity 1 at x = 1.265936,
  9.416564, 6.900529 (v = 0) and x = 4.478061, 3.688404 (v = 0.442649).
- Its ratio is 0.214932720 (mpmath, exact per-period form).
- Best real found: 0.250534, at M = 8.43373 with m = (1,1,2,2) at x = 0, 2.53207, 3.39175,
  5.92382. Lattices give 0.2967 and ρ₅₉(0) = 0.357.

So κ_C(ρ₅₉) ≤ 0.2149, at least 14% below the best real value found. Mechanism: the n = 6
frequency 6/M = 0.5625 sits on the peak of ρ₅₉, while ρ₅₉(0) is small. The two lifted
pairs, 0.79 apart, raise their weights at α ≈ 0.56 to cancel the three doubles there.
This is Prop. 5 with the "heavy neighbour" replaced by collective cancellation.

**Interpolation (1−λ)ρ_LP + λρ₅₉** (two-pass continuation over 384 pooled
configurations). The table gives the real infimum minus the lifted-complex infimum:

| λ | 0 | 0.5 | 0.8 | 0.85 | 0.875 | 0.9 | 0.925 | 0.95 | 1 |
|---|---|---|---|---|---|---|---|---|---|
| real − lifted | −0.505 | −0.049 | −0.023 | −0.015 | −0.009 | −0.002 | +0.005 | +0.014 | +0.036 |

The gap opens at λ* ≈ 0.91. This is a search-limited estimate: a deeper search can only
lower both curves. The LP ρ therefore has to be about 90% replaced by ρ₅₉ before complex
configurations beat real ones.

Across 96 random 5-knot ρ ≥ 0, a complex-only gap survived an intensified real search
only for ρ₅₉. Across 48 random nonincreasing ρ there was none.

**CONJECTURE** (moderate numerical support): if ρ is even, ≥ 0 and nonincreasing on
[0,1], then κ_C(ρ) = κ_real(ρ). The LP ρ is nonincreasing. If true, (\*\*) for the LP ρ
follows from the real Cheer–Goldston inequality, i.e. Prop. 3 of the parent memo. This
looks like the right target for the prover. Lemmas 2–3 and the positive second-order
coefficients are the structural reasons that monotone ρ resists lifting. ρ₅₉, whose peak
is away from 0, shows the monotonicity (or something like it) cannot simply be dropped.

## 5. Where (\*\*) is tight: data for the prover

1. **Tightness is real.** The infimum is approached by real designs at the zeros of the
   CG test r: gaps ≈ 1.04 and ≈ 1.95, ratio 1.00025–1.0003. Multiplicity does not matter
   at fixed positions, because all-double designs have the same ratio as all-simple ones.
2. **Unit lattice.** At density 1 the unit lattice gives exactly ρ(0) = 1.003873, so
   κ ≤ ρ(0) (Lemma 4). The density-1 infimum found is 1.00086.
3. **Lifting margin at near-tight designs.** Over 400 near-tight designs with doubles, the
   second-order coefficient satisfies C_j ≥ 0.0408, against a self part of 2q(0) = 0.2975.
   A proof must keep lifting curvature positive at these designs. Termwise bounds cannot
   do this (parent Prop. 6).
4. **Where lifting does help.** Next to heavy mass (t ≥ 2), at ratios ≥ 1.087.
5. **Caveat on κ = 1 itself.** The LP enforces r ≥ 0 only on a 0.01 grid, and
   min r = −2.0·10⁻⁵ at u = 1.045 (Part 0). So even the real inequality with κ = r(0) = 1
   is certified only up to this. Taking κ = 0.9999 gives 0.678951, still above the
   frontier 0.6725043820976.

## 6. Cutting plane (task 4)

The task's trigger was not met: no configuration violates (\*\*) for the LP ρ, so no
constraints were added and the LP was not re-solved. The upper bounds on this route are:

- For the LP ρ: κ_C ≤ κ_real ≤ 1.0002544 (CHECKED design), so the proportion is at most
  2 − 1.3209166550/1.0002544 = 0.679419.
- For any ρ: κ ≤ ρ(0) (Lemma 4), so the proportion is at most 1 − ∫|α|ρ/ρ(0).

## 7. Self-checks

| check | status |
|---|---|
| ρ is the LP ρ | Part 0 reruns the parent LP verbatim; P and R match to 10 and 8 digits |
| integer multiplicities, conjugation closure | patterns are integer lists; each pair enters S as 2m·cosh·e(αx) |
| s₁ counting | only real atoms with m = 1 cost 1; pairs cost 4m even at v = 0 |
| periodic formula | checked against 50- and 200-period truncations (Part 1) |
| float vs exact | reported minimisers re-evaluated in mpmath at 30 digits (Part 7); agreement to ≥ 10 digits |
| optimiser | analytic gradients, L-BFGS-B; heights bounded in [0, 1.5] or [0, 2]. Larger v is useless: common height reduces to the real case (Prop. 5ii), and the highest-height group dominates. |

Confidence that (\*\*) holds for the LP ρ with κ = 1, up to the grid caveat in §5.5:
moderately high (about 85%). The searches are local and cannot exclude an exotic basin.
However, every structured attack (heavy neighbours, dense near-real pairs, lattice
defects, density-1, and continuation from a ρ where the mechanism is genuine) stays at
least 0.0003 above 1, and lifted basins stay at least 0.087 above 1.
