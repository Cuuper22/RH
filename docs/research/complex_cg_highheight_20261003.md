# The high-height regime of the complex Cheer–Goldston inequality (**)

Research note, 2026-10-03. Companion script
[`verify/complex_cg_highheight.py`](../../verify/complex_cg_highheight.py) (output
`verify/complex_cg_highheight.out`, default run about 6 minutes). Builds on the positivity
memo `positivity_class_20261003.md` (notation), the proof memo `complex_cg_proof_20261003.md`
(certified ρ with P = 1.3210847, R = 1.0124602, κ = r(0) = 1; Theorem 4 for heights
≤ V₀ = 1/(4π)), the adversary memo `complex_cg_adversary_20261003.md`, and the parallel hybrid
memo `complex_cg_hybrid_20261003.md` (Theorem H1: one pair of any height among arbitrary real
atoms; Lemma 3.1: unit pair lattices have ratio ρ(0) at every height). Labels: PROVED (complete
argument here), CHECKED (exact or 30-digit evaluation in the script, or floating point with
margins far above rounding), NUMERICAL (optimisation, no certificate), CONJECTURE, REFUTED.

Throughout, an atom j has position x_j, integer weight W_j and height v_j ≥ 0: a real atom of
multiplicity m has W = m, v = 0, cost 2m − [m = 1]; a conjugate pair x ± iv of multiplicity m
has W = 2m, cost 2W. With a_j = 2παv_j and e_j = e(αx_j),

    S_Z(α) = Σ_j W_j cosh(a_j) e_j,   Σ_Z(ρ) = ∫_{−1}^{1} ρ|S_Z|²,   (**): Σ_Z(ρ) ≥ κ·cost(Z).

## 0. Summary and verdict

* **The task's primary strategy (two-regime closing) cannot work as posed (REFUTED, Section 4).**
  There is no height V₁ above which a pair can be removed, or is self-dominated, uniformly in
  its neighbours: for two pairs of weight 2 at distance 1/2 and heights v ≥ v′,
  Σ_Z − Σ_{Z∖{higher pair}} ≈ W²[C(v) − 2√(C(v)C(v′))] is negative as soon as v′ > v − 0.11,
  e.g. −1.4·10³ at v = v′ = 1 and −1.3·10⁸ at v = v′ = 2, although (**) holds there with
  ratios 127 and 2·10⁶. The pair–pair kernel at Δ ≡ 1/2 (mod 1) is ≈ −√(C(v)C(v′)), the same
  exponential order as the self-terms, and the hybrid memo's Lemma 3.1 (unit pair lattices have
  ratio ρ(0) at every height) shows that the cancellation is exact in lattices. Self-domination
  holds only against *real* neighbours (Theorem H1 of the hybrid memo, which supersedes the
  one-pair bookkeeping of Section 4 here).
* **Strategy (ii), enlarging V₀, is priced (Section 5, NUMERICAL).** Forcing the Theorem-4
  windows closed by linear LP constraints costs P ≈ 1.33–1.35 already at V₀ ≈ 0.1 and crosses
  the frontier P < 1.3274837 there, in line with the termwise LP of the proof memo. Since no V₁
  exists, "V₀ ≥ V₁" is unattainable whatever ρ is used.
* **New exact results (PROVED).** Lemma A: *any two pairs*, of any heights and multiplicities,
  satisfy (**) with κ = 1.00777 > 1. The two-height identity
  |S|² = |Σ_j W_j sinh(a_j) e_j|² + Σ_{j,k} W_jW_k cosh(a_j − a_k) cos(2παΔ_jk), whose second
  part is invariant under a common shift of all pair heights, and the two-pair reduction lemma:
  if the higher pair is at least as heavy, Σ(pairs at v₁ ≥ v₂) ≥ Σ(pair at v₁ − v₂, real atom
  of weight W₂). The natural multi-height extension — Σ is nonincreasing under the common
  downward shift v ↦ v − v_min of all pair heights — is **REFUTED** (CHECKED at 30 digits) for
  ≥ 4 equal pairs and for 2 pairs next to heavy real atoms; every counterexample has ratio
  ≥ 1.5. A multi-height factorisation that is exact on lattices therefore cannot be a pure
  monotonicity statement; it must carry the integer cost slack of heavy clusters.
* **(**) for all heights remains open; no κ′ > 0.99504 is proved for all Z. Certified
  unconditional bound from this route: none above 0.6725162800.** The open case is exactly the
  one isolated by the hybrid memo: several pairs at *unequal* heights within distance O(v) of
  each other (equal heights reduce to the real case; one pair among reals is H1; two pairs
  alone are Lemma A; heights ≤ 0.08 are Theorem 4).

## 1. Resources and the structure of the obstruction

From the proof memo, (1.1): with t_jk = ∫ρ cosh(a_j)cosh(a_k) cos(2παΔ_jk), X(v) = ∫ρ sinh²(2παv) =
C(v) − R, C(v) = ∫ρ cosh²(2παv) = (B(2v) + R)/2, B(w) = ∫ρ cosh(2παw) = Re r_in(iw),

    Σ_Z(ρ) − cost ≥ Σ_j W_j² X_j + Σ_{j≠k} W_jW_k (t_jk − s(Δ_jk)) + Σ_j (W_j² − cost_j).

Exact node sums (ρ piecewise linear with nodes k/100, jumps J_k of ρ′): B(w) =
Σ_k J_k cosh(2πα_k w)/(2πw)², so B(w) ≈ 2|ρ′(1)| e^{2πw}/(2πw)² with |ρ′(1)| = 0.44417, and
C(v) ≈ |ρ′(1)| e^{4πv}/(4πv)². Numerically (script Part 4): B = 1.58, 10.9, 1.2·10³ and
X = 2.0, 6.0·10², 3.6·10⁷ at v = 0.4, 1, 2. The three relevant kernels are:

* pair–real: t(0, v, Δ) = Re r_in(Δ + iv), of size ≤ B(v) with Lorentzian envelope
  ≈ B(v) v²/(v² + Δ²) and sign cos(2πΔ) at the edge; summable over a density-one environment
  (≈ πv B(v)), and *exponentially* smaller than X(v) ≈ B(2v)/2;
* pair–pair: t(v, v′, Δ) = [Re r_in(Δ + i(v + v′)) + Re r_in(Δ + i(v − v′))]/2, of size up to
  B(v + v′)/2 ≈ √(C(v)C(v′)) when v ≈ v′ — the *same* exponential order as the self-terms;
* the cost slack W_j(W_j − 2)₊ + ρ_* Σ_{bonds within 1/2} W_jW_k of heavy clusters, which is
  quadratic in the cluster weight A: ≥ ρ_* A(A − 2), ρ_* = min_{[0,1/2]} r ≈ 0.46.

So a pair's self-excess dominates everything real around it (this is Theorem H1), but nothing
of comparable height: Section 4.

## 2. Lemma A: two pairs of any heights (PROVED)

**Lemma A.** For two pairs (x₁ ± iv₁, W₁ = 2m₁), (x₂ ± iv₂, W₂ = 2m₂), any v₁, v₂ ≥ 0,

    Σ_Z(ρ) ≥ 2W₁W₂ (R + r_in(Δ)) + ∫ρ (W₁ cosh a₁ − W₂ cosh a₂)² ≥ 2W₁W₂ (R + min r_in) ≥ 1.00777·cost(Z).

*Proof.* |S|² = (W₁c₁ − W₂c₂)² + 2W₁W₂ c₁c₂ (1 + cos 2παΔ) with c_j = cosh a_j ≥ 1 and
1 + cos ≥ 0, so |S|² ≥ (W₁c₁ − W₂c₂)² + 2W₁W₂(1 + cos 2παΔ); integrate. The constant
min_Δ (R + r_in(Δ)) = 1.007865 (attained at Δ = 2.098, CHECKED on a 5·10⁻⁴ grid; the script
prints 1.007865, the summary rounds down) and W₁W₂ ≥ W₁ + W₂ = cost/2 for W_j ≥ 2. □

Lemma A is sharp in the sense that its lower bound is attained at v₁ = v₂ = 0, Δ = 2.098
(ratio 1.00787): two pairs are never closer to tight than two real doubles. It also covers the
"deletion failure" configurations of Section 4 with ratios 4 … 2·10⁶.

## 3. The two-height identity, the two-pair reduction, and the limits of height shifting

**Lemma 3.1 (two-height identity, PROVED; CHECKED to 10⁻¹²).** For any configuration (real atoms
have a_j = 0),

    |S_Z(α)|² = |U(α)|² + Φ(α),   U = Σ_j W_j sinh(a_j) e_j,   Φ = Σ_{j,k} W_jW_k cosh(a_j − a_k) cos(2παΔ_jk).

*Proof.* cosh a cosh b = sinh a sinh b + cosh(a − b). □

For pairs-only configurations Φ depends on the heights only through their differences, so a
common shift v_j ↦ v_j − v_min of all pair heights (which turns the lowest pair into a real atom
of weight W ≥ 2 at the same cost 2W) leaves ∫ρΦ unchanged and changes Σ by
∫ρ(|U|² − |U′|²), U′ = Σ_j W_j sinh(a_j − a_min) e_j. With real atoms present the pair–real
part of Φ changes as well (cosh a_j ↦ cosh(a_j − a_min)); the common-height factorisation of the
positivity memo (Prop. 5(ii)) is the case U′ = 0.

**Lemma 3.2 (two-pair reduction, PROVED).** Let v₁ ≥ v₂ and W₁ ≥ W₂. Then

    Σ({x₁ ± iv₁ (W₁), x₂ ± iv₂ (W₂)}) ≥ Σ({x₁ ± i(v₁ − v₂) (W₁), real atom of weight W₂ at x₂}),

and both sides have the same cost. *Proof.* By Lemma 3.1 the difference is
∫ρ[|W₁ sinh a₁ e₁ + W₂ sinh a₂ e₂|² − W₁² sinh²(a₁ − a₂)] ≥ ∫ρ[(W₁ sinh a₁ − W₂ sinh a₂)² −
W₁² sinh²(a₁ − a₂)], and W₁ sinh a₁ − W₂ sinh a₂ ≥ W₁(sinh a₁ − sinh a₂) ≥ W₁ sinh(a₁ − a₂)
pointwise, since W₂ ≤ W₁ and sinh is superadditive on [0, ∞). □

Lemma 3.2 reduces two pairs to one pair plus a real atom, i.e. to Theorem H1, but only in the
absence of further atoms. The hypothesis W₁ ≥ W₂ cannot simply be dropped: for W₁ = 2, W₂ = 4
and v₁ = 2v₂ small, (W₁ sinh a₁ − W₂ sinh a₂)² = O(α⁶) while W₁² sinh²(a₁ − a₂) = O(α²).

**Proposition 3.3 (REFUTED: common-shift monotonicity).** The statement "Σ_Z(ρ) does not
increase when all pair heights are lowered by v_min" is false, even for pairs of equal
multiplicity one and no real atoms. Certified counterexamples (30-digit closed-form
evaluation of the per-cell integrals ∫ρe^{λα}, script Part 2):

| configuration (x; v) | Σ(v) − Σ(shifted) | ratio Σ/cost |
|---|---|---|
| 4 pairs W = 2: x = (1.58, 0.815, 0.045, 1.58), v = (0.05, 0.236, 0.05, 0.05) | −0.0720 | 1.692 |
| 6 pairs W = 2: x = (2.585, 0.169, 1.018, 1.825, 1.018, 1.018), v = (0.05, 0.205, 0.05, 0.289, 0.05, 0.05) | −0.432 | 2.160 |
| 2 pairs + real quadruple: x = (1.98, 1.222, 2.751), v = (0.282, 0.15, 0) | −0.509 | 1.680 |
| 2 pairs + two real doubles: x = (2.466, 3.232, 1.697, 1.697), v = (0.223, 0.05, 0, 0) | −0.218 | 1.685 |
| pair W = 2 next to pair W = 4: x = (2.27, 1.495), v = (0.093, 0.004) | −0.00085 | 1.840 |

The mechanism is the one of the positivity memo (Prop. 5): a pair adjacent (distance 0.75–0.8)
to heavy mass of relative weight ≥ 1.72 has negative lifting curvature; three stacked pairs or
a real quadruple provide the heavy mass. In an adversarial search over 15 multiplicity patterns
with v_min ∈ {0.05, 0.15, 0.4} (script scratch run, NUMERICAL), no counterexample with ratio
below 1.5 was found; with 2 or 3 equal pairs and no real atoms none was found at all. So the
shift is monotone exactly where the configuration is not tight, and the slack it needs is the
cost slack W(W − 2) + ρ_*A(A − 2) of the heavy cluster — the same integer structure that
Theorem 2 of the proof memo says every proof must use.

*Consequence for a "multi-height Prop. 5".* Any inequality that reduces a multi-height
configuration to a lower one and is exact on common-height lattices must be of the form
Σ(v) ≥ Σ(v′) − (cost slack present in Z), not Σ(v) ≥ Σ(v′). Lemma 3.1 identifies the exact
obstruction term: ∫ρ(|U|² − |U′|²) = ∫ρ sinh(a_min)[sinh(a_min)(|U′|² + |V|²) + 2cosh(a_min) Re(U′V̄)],
V = Σ_j W_j cosh(a_j − a_min) e_j, which is negative only where Re(U′V̄) < 0 with |V| ≳ |U′|,
i.e. where a heavy lower layer is anti-aligned with the lifted upper layer.

## 4. No high regime: removal and self-domination of a pair fail against comparable pairs

**Proposition 4.1 (REFUTED: the removal step).** Let Z consist of two pairs of weight 2 at
distance 1/2 with heights v ≥ v′, and Z′ = Z minus the higher pair. The step "delete the pair
and keep an inequality of the same form for the rest" needs Σ_Z − Σ_{Z′} ≥ cost(pair) = 4. But
Σ_Z − Σ_{Z′} = 4C(v) + 8 t(v, v′, 1/2), and t(v, v′, 1/2) = ∫ρ cosh a cosh a′ cos(πα) → −√(C(v)C(v′))
up to a factor 1 − o(1) as v, v′ → ∞ (the integrand concentrates at α → 1, where cos πα → −1).
Hence Σ_Z − Σ_{Z′} ≈ 4[C(v) − 2√(C(v)C(v′))] < 0 whenever C(v′) > C(v)/4, i.e. v′ > v − log 4/(4π) − o(1)
= v − 0.11. CHECKED (script Part 3): Σ_Z − Σ_{Z′} = −1.39·10³ (v = v′ = 1), −494 (v = 1, v′ = 0.95),
−1.3·10⁸ (v = v′ = 2), −9.2·10⁶ (v = 2, v′ = 1.9), while Σ_Z/cost = 127 … 2·10⁶ by Lemma A. At
v = v′ = 0.5 the gain is still positive (+8.9) because C(0.5) = 5.96 is not yet large. □

So there is no threshold V₁: the higher a pair, the larger the set of configurations in which
its removal destroys the inequality. The same computation shows that the *self-domination*
bookkeeping — pay all bonds of the pair from W²X(v) — is impossible against a pair of comparable
height: a single bond already costs 2W²√(C(v)C(v′)) ≈ 2W²C(v) > W²X(v). Lemma 3.1 of the hybrid
memo is the extreme case: in a unit lattice of pairs the bonds cancel the self-excess exactly at
every height.

**What self-domination does achieve (one pair against arbitrary low neighbours).** For
completeness, script Part 4 tabulates the resources of one pair of height v against arbitrary
atoms of height ≤ V₀ = 1/(4π), with the Theorem-4 bookkeeping (cells of length 1/2; sparse cells
of weight ≤ 2 charged linearly to the pair; dense cells of weight A ≥ 3 charged by AM–GM against
the cluster slack ρ_*A(A − 2), of which Theorem 4 leaves the fraction 1 − ν = 0.52). With
Γ(v) = Σ_cells sup g_v and Γ₂(v) = Σ_cells sup g_v², g_v ≥ sup_{u≤V₀} [s(Δ) − t(u, v, Δ)]₊ (certified
cell bounds on [0, 60], 1/Δ² tail), the requirement is φ(v) = 2Γ/X + c_D Γ₂/X ≤ 1 with
c_D = 3/((1 − ν)ρ_*) = 12.5:

| v | B(v) | X(v) | 2Γ/X (sparse) | c_DΓ₂/X (dense) | φ |
|---|---|---|---|---|---|
| 0.4 | 1.58 | 2.04 | 2.00 | 2.12 | 4.12 |
| 1.0 | 10.9 | 603 | 0.19 | 4.19 | 4.38 |
| 2.0 | 1.2·10³ | 3.6·10⁷ | 0.0008 | 2.57 | 2.57 |
| 3.0 | 2.6·10⁵ | 4.3·10¹² | 0.0000 | 1.62 | 1.62 |

The sparse load vanishes exponentially (Γ ≈ πvB(v), X ≈ B(2v)/2), but the dense load decays only
like 1/v: Γ₂ ≈ (πv/2)B(v)² while X/B(v)² → π²v²/(4|ρ′(1)|) = 5.55v². With these crude constants
the bookkeeping closes only for v ≳ 5 (NUMERICAL extrapolation). Theorem H1 of the hybrid memo
closes the same mechanism at every v ≥ 0.0795 by using the exact integer penalty of each cell
instead of ρ_*A(A − 2) and cells adapted to the sign of the field; we did not duplicate it. The
decay of H1's certified ratio like 0.35/v is the 1/v of the dense load above.

**Where the magnitudes leave the problem.** Against real neighbours a pair has an exponential
margin; against pairs of comparable height it has none, and the only exact tool is the
common-height factorisation. The missing statement is a lower bound for ∫ρ|S|² for several
pairs at *unequal* heights within distance O(v) of each other, mixed with real atoms, that is
exact on common-height lattices and uses the integer slack of heavy clusters (Prop. 3.3). Lemma
A settles the case of two pairs alone; Lemma 3.2 settles two pairs with the heavier one higher.

## 5. Strategy (ii): the price of enlarging V₀ (NUMERICAL)

Theorem 4's binding inequality (A) compares 4Σβ with 4π²q(0), where β(Δ) =
[m₊(Δ) − r(Δ)/(2V₀²)]₊ measures how far the negative part of the pair–real kernel exceeds the
real slack r. The cheapest way to enlarge V₀ is to make β ≡ 0 by LP constraints: the two
endpoint conditions r(Δ) ≥ 4π²V₀²(−q(Δ)) (w → 0 in −Q_w/w²) and r(Δ) ≥ −Q_{2V₀}(Δ)/2 (w = 2V₀),
imposed on the grid Δ ∈ 0.02·Z ∩ [0.5, 60] (both linear in the node values of r̂), then Theorem 4
holds for that V₀ with κ = r(0), up to the far tail Σβ ≈ 0.08 (which (A) and (B) absorb easily).
Minimising P under the original LP constraints plus these (script Part 5; scratch run on a 0.01
grid, Part 5 uses 0.02):

| V₀ forced | P | 2 − P | ρ(0) |
|---|---|---|---|
| 0 (Theorem 1) | 1.3210847 | 0.6789153 | 1.00444 |
| 0.04 | 1.3280253 | 0.6719747 | 1.01329 |
| 0.08 | 1.3489071 | 0.6510929 | 1.04216 |
| 0.10 | 1.3643012 | 0.6356988 | 1.06215 |

The frontier P < 1.3274837 is already lost at V₀ = 0.04, i.e. below the V₀ = 0.0796 that
Theorem 4 obtains from the same ρ by *spending* the budget (A) instead of forcing β = 0. (The
intermediate option — allow a sum of window heights up to the budget — is a nonconvex design
problem; its gain is bounded by the margin structure of Theorem 4, whose first window at Δ ≈ 1.05
alone carries β_c ≈ 0.95 of the budget 1.46.) Combined with Section 4 — no V₁ exists — the
two-regime closing "V₀ ≥ V₁" is unattainable for every ρ in the class: not for lack of margin
in V₀ but because the high regime does not exist.

## 6. Assessment: what the two-regime programme reduces to

1. *Low regime.* Theorem 4 (heights ≤ 0.0796) is the only place where the budget inequality
   (A) is used; it has 0.4 % margin and Section 5 shows that re-optimising ρ buys at most a few
   hundredths in V₀ before the frontier is lost.
2. *High regime.* A pair is self-dominated against real atoms at every height (H1), against a
   second pair of any height if there is nothing else (Lemma A), and against a lower *lighter*
   pair in isolation (Lemma 3.2). It is never self-dominated against a pair of comparable height
   with other mass around (Prop. 4.1, hybrid Lemma 3.1). So the regimes do not meet at any V₁;
   the obstruction is not the size of V₀ but the pair–pair kernel −√(C(v)C(v′)) at Δ ≡ 1/2.
3. *The remaining case* is a configuration with pairs at two or more distinct heights within
   distance O(v) of each other, mixed with real atoms. Numerically its ratio is ≥ 1.0013 (hybrid
   memo, 28 800 optimisations), and the per-pair excess is at least the lattice value
   4(ρ(0) − 1) = 0.0178 against an allowance of 4(1 − 0.99518) = 0.0193 at the frontier: a proof
   must be exact to within 8 % on pair lattices, where every termwise bound fails, while
   Prop. 3.3 shows that exact reductions must carry the cost slack of heavy clusters. The two
   ingredients a proof must combine are therefore the identity of Lemma 3.1 (which isolates the
   height dependence in |U|², with Φ shift-invariant) and the integer penalties of H1's Step 2.
   We did not find the combination.
4. *Mechanism (b) target.* Prop. 2.5 of the hybrid memo would accept Σ_Z(ρ) ≥ cost(non-high) +
   κ_H cost(high) with κ_H > 0.99023. Lemma A gives κ_H = 1.00777 for two isolated pairs and H1
   gives κ_H = 1 for one pair among reals, but the unit pair lattice (ratio ρ(0) at every height,
   excess 0.0178 per pair shared with nothing) shows that any κ_H must be earned from the real
   inequality on the collapsed lattice, not from height. No κ_H > 0.987962 is proved for all Z.

## 7. Self-check

| claim | status | RH / real-zero use | uniformity |
|---|---|---|---|
| Lemma A (two pairs, any heights, κ = 1.00777) | PROVED; constant CHECKED | none | all m₁, m₂, v₁, v₂, Δ |
| Lemma 3.1 (two-height identity) | PROVED; CHECKED 10⁻¹² | none | any Z |
| Lemma 3.2 (two-pair reduction, W₁ ≥ W₂) | PROVED | none | pairs-only, two atoms |
| Prop. 3.3 (common-shift monotonicity false) | REFUTED; 30-digit CHECKED | — | counterexamples have ratio ≥ 1.5 |
| Prop. 4.1 (no removal step, no V₁) | REFUTED; CHECKED | — | two-pair example, Lemma A ratio |
| magnitude table for one pair vs low atoms | NUMERICAL (certified cell bounds, crude constants) | — | superseded by H1 |
| Pareto price of V₀ (LP with endpoint constraints) | NUMERICAL | — | not a certificate of Theorem 4 at that V₀ |
| (**) for several pairs at unequal heights | OPEN (CONJECTURE, no violation known) | — | — |

Nothing above uses β = 1/2 or the reality of zeros. **No unconditional proportion above
0.6725162800 is certified by this note.**
