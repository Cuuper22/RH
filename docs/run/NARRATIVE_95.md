# Narrative of the 95% Campaign

## Overview

The 95% campaign set out to prove that at least 95% of the nontrivial
zeros of the Riemann zeta function lie on the critical line and are
simple. The starting point was the accepted 85% result, which relied on
a saturated pair-trace theorem at Fourier support less than 3/2 and the
rank--trace inequality for the Weil compression matrix. The campaign
reached its goal: at least 95.063% of zeros are simple and on-line. The
proof combines two independently established results -- an arithmetic
extension of the pair trace to support less than 2, and a zero-side
spectral certificate using a deliberately nonflat nested block -- neither
of which requires any hypothesis beyond the accepted framework.

## The key idea

Two mechanisms drive the improvement from 85% to 95%.

First, the pair-trace arithmetic was extended from connected Fourier
support less than 3/2 to support less than 2. This alone raised the
floor from roughly 86.6% to 93.2%.

Second, a nested principal block of bandwidth less than 1/2 was embedded
inside the full Weil compression. Because the block's fourth trace has
total Fourier support less than 2, its spectral moments are
unconditional. A stability inequality converts excess positive spectral
energy in this block into additional certified simple zeros. Choosing a
nonflat (top-hat) symbol for the block, rather than the uniform profile
used in earlier cycles, produces enough extra spectral energy to cross
95% at the already-proved support.

## Chronological narrative

### Phase 1: Quartic exploration at support 3/2 (files 13--17)

**Establishing the barrier (file 13).** The first cycle quantified the
distance to 95% under the existing method. At the proved support
endpoint (sigma just below 3/2), the optimized second-trace cost gives a
floor of 86.567%. Reaching 95% with the pair trace alone would require
extending support to approximately 2.261 -- far beyond the proved range.
This file established the numerical target and showed that no
rearrangement of Frobenius observables within the support-3/2 class
could help.

**The three-translate increment and scalar class kill (file 14).** A
geometric observation -- that three nearby critical-line atoms cannot all
be mutually orthogonal under translation -- yielded a tiny but strict
unconditional gain (86.568%). More importantly, this file proved a
precise impossibility: the entire class of scalar PRZZ proportions,
Routh identities, and xi-prime percentages cannot improve the pair-trace
floor. An explicit finite model with double zeros satisfies all those
scalar inputs while sitting at the equality point. The file also showed
that if arithmetic could reach support 2, a PRZZ residual union would
need only 40% of its thinning benchmark, rather than 97%.

**Nested quartic stability (files 15--16).** Rather than extending
prime-pair support, the next cycles introduced the stability form of the
rank--trace inequality. A principal block of absolute bandwidth less than
1/2 has unconditional centered moments up to order four. Embedding a
rational quartic polynomial that separates positive from negative
eigenvalue directions, one extracts positive spectral energy that the
nonsimple-zero budget cannot absorb. File 15 proved a floor of 86.717%
at support 3/2, a gain of 0.15 percentage points without any new
arithmetic. File 16 refined this to 86.723% by solving the fixed-point
equation in closed form, eliminating any iterative approximation.

**Quantifying the mixed certificate (file 17).** This cycle unified the
saturated-kernel threshold and the quartic block into a single
certificate. Three conclusions emerged. The pair trace alone needs
support 2.261 for 95%. The quartic block reduces that requirement to
2.142, saving 0.118 units of support. At the prospective support 2, the
combined certificate would already reach 93.83%. The nested block's
fourth trace stays inside 4 mu < 2, so no new correlation input is
needed -- only the pair-trace arithmetic at the required support.

### Phase 2: The arithmetic breakthrough (file 18)

File 18 extended the signed-shift pair-trace theorem from support less
than 3/2 to every fixed support less than 2. The construction changed
the factorization of the bilinear form at the point where the previous
split would cease to exist (the old factor length would drop below 1).
An asymmetric split with different short and long variables on the two
sides handled the supercritical range 1/2 < eta < 1. All Type-I, pole,
tail, and zero-mode blocks transferred from the earlier cycles.

The resulting floor was 93.228% -- an absolute gain of 6.66 percentage
points over the support-3/2 baseline. This was the single largest
numerical advance in the campaign.

The same file also mapped the exact obstruction to going further. At the
95% support threshold (eta approximately 1.261), the missing factor is
L = H/T, a positive power of T. The reciprocal-L^1 termwise method
class -- taking absolute values separately in each Kloosterman variable
after the smooth shift sum -- was proved incapable of recovering this
factor. Outside that class, the first coefficient-sensitive object was
identified: a shifted correlation of the actual Heath--Brown
coefficients, reduced at depth five to a concrete bilinear block.

### Phase 3: Merging the arithmetic and quartic results (file 19)

With the pair trace proved for support less than 2, and the quartic
block requiring only total fourth-trace support less than 2, the two
results applied simultaneously. The merged certificate produced a floor
of 93.831%, improving the raw pair-trace value by 0.603 percentage
points. The remaining distance to 95% was 1.169 percentage points.

This file also verified that no endpoint interchange was needed: the
certificate works at any fixed strict sigma < 2 and mu < 1/2, and the
limiting constant is obtained by continuity. The input inventory was
limited to the Weil compression, the signed-shift arithmetic, the
principal-compression construction, the four diagonal moments, and the
rational trimmed-moment dual.

### Phase 4: Supercritical-support exploration (files 20--23)

The remaining 1.17 percentage points could in principle be closed either
by extending the arithmetic past support 2, or by strengthening the
zero-side certificate. The next four files pursued the arithmetic route.

**Depth-nine identity and one-sided blocks (file 20).** To use the
signed shift average (of length L) as a resource for cancellation, every
individual Heath--Brown factor must be shorter than L. This requires HB
depth at least 9 (depth 8 just barely fails). At depth 9, every actual
one-sided block -- where one coefficient is smooth and the other has a
single truncated HB factor -- was resolved. The estimate used Poisson
summation inside the signed shift progression before taking absolute
values. However, the genuinely two-sided blocks, where both coefficients
contain short Mobius-weighted factors, remained open. The file
formulated the precise multilinear dispersion moment (MD9) that would
suffice and proved that no one-shot Kloosterman insertion could close it.

**Dependency-hypergraph barrier (file 21).** A natural hope was to
iterate the Blomer--Pascadi bilinear Kloosterman bound four times,
gaining H^{-1/32} at each stage. This file proved that the four gains
cannot be tensored: every possible four-cycle in MD9 shares the common
shift vertex, and separating it costs L^{1/2} per additional application.
Since rho/2 > 1/32, each additional copy is strictly worse than the
first. The maximum useful packing number is exactly one.

Outside that class, the file computed an exact discriminant polynomial
for the Kloosterman four-cycle and averaged the resulting quadratic
character over the shift variable. This gave a genuine new orthogonality
bound, but for prime terminal moduli of size H it remained weaker than
the trivial shift-by-shift estimate.

**Selector--quartic identity and translation-class kill (file 22).** An
independent hybrid approach combined a PRZZ simple-zero selector with
the quartic stability tail. Deleting certified simple zeros before
applying the stability lemma produces an additive joint certificate. The
file also optimized and killed the entire weighted three-translate class:
its best possible output is 93.248%, below even the unrefined
support-two floor. This ruled out further refinement of the
three-translate route.

**Divisor-switch checkpoint (file 23).** The final arithmetic attempt
used the exact difference-of-squares form of the BP discriminant to
switch from the large prime Kloosterman modulus to a small divisor of
the determinant (of scale L^2). The switch is exact and useful for
zero-winding terms, but nonzero-winding terms retain the original large
modulus. For prime terminal moduli, the conductor cannot be lowered
uniformly. The first object outside this class -- a q-van-der-Corput
determinant correlation -- was identified but not pursued further.

### Phase 5: The terminal certificate (file 24)

While the supercritical arithmetic was in progress, a zero-side
construction crossed 95% using only the already-proved support less
than 2.

The key insight was that the earlier flat nested block (uniform symbol
r = 1 on the block interval) left unused the freedom to choose the
block's shape. A nonflat top-hat symbol -- r_p(x) = (1/p) times the
indicator of [-p/2, p/2] for p < 1 -- concentrates the block's spectral
mass and changes all four centered moments in a favorable direction.

At the fixed strict parameters sigma = 1.9999, mu = 0.4999, p = 0.83,
the profile-sensitive moments force substantially more positive-square
spectral energy than the nonsimple-zero budget can absorb. An exact
rational quartic dual polynomial, verified by global sign checks on
three factored remainders, certifies the increment. The result:

> At least 95.063832% of nontrivial zeros are simple and on the
> critical line.

The same file also proved that multi-block budget-sharing (distributing
the nonsimple positive-index count across disjoint blocks) is impossible,
via an exact 4-dimensional simultaneous dilation counterexample. This
killed the only remaining route that would have avoided the nonflat
construction.

## The final result

The proved floor is 95.063832...%, exceeding the 95% target by about
0.064 percentage points. The proof uses:

1. The saturated pair-trace theorem at the single fixed support
   sigma = 1.9999 < 2 (from the arithmetic branch).
2. A nonflat top-hat nested block of bandwidth mu = 0.4999, with
   fourth-trace support 4 mu = 1.9996 < 2 (from the certificate branch).
3. An exact rational quartic dual polynomial satisfying global
   interpolation and sign conditions.

No Riemann Hypothesis assumption, pair-correlation conjecture, or
endpoint interchange is involved. Both the pair-trace support and the
block's fourth-trace support are strictly less than 2, so all arithmetic
inputs are unconditional within the accepted framework.

## Superseded work

Several lines of investigation were completed but ultimately not needed
for the 95% result:

- **Supercritical arithmetic (files 20--21, 23):** The depth-nine HB
  identity, dependency-hypergraph analysis, quadratic-character
  orthogonality, and divisor-switch constructions explored extending the
  pair trace past support 2. These produced precise method-class
  impossibility theorems and identified the first objects outside each
  killed class, but the terminal zero-side certificate made the support
  extension unnecessary.

- **Selector--quartic hybrid (file 22):** The joint PRZZ-selector plus
  quartic-tail identity was a viable route to 95% conditional on
  evaluating two specific PRZZ observables. It was superseded when the
  nonflat block crossed 95% without any selector input.

- **Weighted three-translate class (file 22, section 2):** The full
  all-k weighted-translate optimization was carried out and killed with a
  ceiling of 93.248%, confirming that translation-geometry refinements
  alone cannot approach 95%.

- **Divisor-switch beyond prime moduli (file 23):** The q-van-der-Corput
  determinant correlation was the correct next object but was not pursued
  after the terminal certificate was completed.

These files are preserved as rigorous method-class kills and as
reusable identities for any future campaign beyond 95%.

## File reference

| File | Role | Key output |
|------|------|------------|
| `13_root95_cycle1_second_trace_threshold.md` | Barrier quantification | 95% needs support 2.261 with pair trace alone |
| `14_hybrid95_cycle1_three_translate_increment.md` | Scalar class kill, three-translate gain | 86.568%, PRZZ/Routh/xi' class killed |
| `15_root95_cycle2_nested_quartic_86p7170.md` | First quartic stability increment | 86.717% at support 3/2 |
| `16_root95_cycle3_quartic_fixed_point_86p7233.md` | Closed-form quartic fixed point | 86.723% at support 3/2 |
| `17_certificate95_cycle1_quartic_86p7254_support_2p14234.md` | Mixed certificate thresholds | 95% support reduced to 2.142; 93.83% at support 2 |
| `18_arithmetic95_cycle1_support_2_93p2283.md` | Pair trace extended to support < 2 | 93.228%; reciprocal-L^1 class killed |
| `19_root95_cycle4_unconditional_93p8313.md` | Arithmetic + quartic merge | 93.831% unconditional |
| `20_arithmetic95_cycle2_depth9_md9.md` | Depth-9 HB, one-sided blocks solved | One-shot class killed; MD9 formulated |
| `21_arithmetic95_cycle3_dependency_hypergraph.md` | Dependency-hypergraph barrier | Packing number = 1; character orthogonality computed |
| `22_hybrid95_cycle2_selector_quartic_handoff.md` | Selector--quartic identity, translation kill | All-k class ceiling 93.248%; joint certificate (superseded) |
| `23_arithmetic95_cycle4_divisor_switch_checkpoint.md` | Divisor-switch analysis | Optimal scale L^2; prime-modulus barrier (superseded) |
| `24_TERMINAL_certificate95_cycle2_95p063832.md` | Terminal nonflat-block certificate | **95.064%**; multi-block sharing killed |
| `00_FINAL_95_RESULT_95p063832.md` | Summary of the combined result | **95.063832%** final floor |
