# The 85% Campaign: A Narrative

## Overview

On August 10, 2026, a timed research run set out to prove that at least
85% of the nontrivial zeros of the Riemann zeta function are simple and
lie on the critical line. The campaign began from an accepted baseline of
67.25%, the best proportion certifiable using only "bandwidth-one"
pair-correlation data (Fourier support up to 1). Over roughly eight hours
of structured 90-minute cycles, three parallel research tracks explored
different routes past this barrier. The run succeeded: the final result
is a strict unconditional proportion of 85.00235...% at effective Fourier
support 143/100, with a limiting certificate of 86.57% as the support
approaches 3/2. No assumption of the Riemann Hypothesis, the
Hardy-Littlewood conjecture, or any pointwise prime-pair asymptotic is
required in the final construction.


## The Problem in Plain Language

The Riemann zeta function has infinitely many "nontrivial" zeros in a
vertical strip of the complex plane. The Riemann Hypothesis asserts they
all sit on one vertical line, the critical line Re(s) = 1/2. Short of
proving that, one can ask: what fraction of them provably sit there, and
are "simple" (i.e., the function crosses through zero rather than merely
touching it)?

The answer depends on how much information about prime numbers one can
bring to bear. The key parameter is called the "support" (often written
sigma or lambda), which measures how far into the Fourier domain the
prime-number data extends. At support 1, the existing pair-correlation
theory gives 67.25%. To reach 85%, the support must be pushed past 1,
which requires new estimates on correlations among prime numbers at
longer ranges.


## The Three Research Tracks

The campaign ran three agents in parallel, each attacking from a
different angle. Their roles were:

**Arithmetic track.** This agent worked directly on the prime-number
side. Its job was to prove that certain weighted averages of prime-pair
correlations behave as predicted, at effective support beyond 1. The
central technical challenge was a "factor-H" loss: existing theorems
(particularly the quadratic-divisor theorem of Bettin-Bui-Li-Radziwill,
or BBLR) lose a polynomial factor when applied to the signed, weighted
shift averages that the trace method requires. The arithmetic agent
explored Fourier-first dispersion, reciprocal-cell decompositions,
Heath-Brown factorizations, and ultimately found that summing the signed
shift average *before* applying Watt-type bounds breaks the old barrier.

**Certificate track.** This agent worked on the zero side, designing the
optimal "test function" (window profile) that converts prime-side
information into the strongest possible conclusion about zeros. It
computed exact rational certificates, proved that no bandwidth-one
construction can exceed 67.25% regardless of how clever the test
function is, and identified which prime-side statistics genuinely escape
that obstruction. It also explored polynomial eigenvalue tests (quartic
residuals) and adversary models that formalize exactly why certain
approaches fail.

**Hybrid track.** This agent tried to combine two existing theorems --
the pair-correlation result (67.25% of zeros are simple and on-line) and
the Levinson/PRZZ mollifier result (at least 40.75% are simple and
on-line) -- into a joint certificate exceeding either one alone. It
developed residual-matrix methods, Routh-Hermite index certificates, and
weighted intersection currents. These ideas contributed structural
insights even though the hybrid route itself did not produce the final
85% argument.


## Chronological Narrative

### Cycle 1: Setting the Targets

All three agents began by identifying their precise numerical targets.

The **arithmetic agent** laid out the prime-pair sum that must be
controlled. It showed that for a connected profile at support 1.43, the
required statement is a "signed, weighted aggregate" estimate (labeled
(AS) in the logs). Unlike the published almost-all-shifts theorem, which
allows exceptions, the trace method needs the full weighted average to
be evaluated without taking absolute values over individual shifts. The
agent also proposed a "sparse lobe" construction -- three separated
copies of the optimal bandwidth-one window -- that would reach 89.08% if
the aggregate estimate could be proved, while only sampling the prime
correlation at already-known frequencies and at frequencies above 33/25,
where published technology (Matomaki-Radziwill-Tao) applies.

The **certificate agent** found the exact window that minimizes the
amount of new prime information needed. It produced a concrete rational
certificate: the quadratic profile v(s) = 1 - (169/100)s^2 at support
lambda = 143/100 gives a normalized Frobenius cost of 1.14998..., just
below the 85% threshold of 23/20 = 1.15. This is the specific test
function used in the final result.

The **hybrid agent** proved that simply adding the 67.25% and 40.75%
proportions is logically invalid: the zeros certified by the mollifier
method could be entirely contained in the set already certified by pair
correlation. It formulated an exact "joint certificate" requiring a
mixed selector-correlation statistic (labeled (H85)) that measures the
overlap between the two sets.

### Cycle 2: Fourier-First Dispersion and the Transfer Lemma

The **arithmetic agent** made a conceptual advance by rewriting the
prime-pair problem in Fourier space before taking absolute values. The
signed h-average becomes a local L^2 integral of a prime exponential
polynomial on a band of width 1/H near a rational frequency. This
"fixed-mode short-interval BDH" formulation (labeled (FM-BDH))
identifies the correct object to estimate and shows exactly why standard
Bombieri-Vinogradov loses: it sums over all additive Fourier modes,
while the trace selects just one.

The **certificate agent** proved the exact transfer lemma connecting
prime-pair discrepancies to the Frobenius trace. It showed that
logarithmic-accuracy almost-all-shifts theorems cannot transfer to the
trace: exceptional shifts, even if rare in a logarithmic sense, carry
enough weight in the endpoint kernel to swamp the entire second-moment
scale. The transfer requires either uniform power-saving accuracy or the
directly weighted aggregate (18) that avoids pointwise shift estimates.

The **hybrid agent** reduced the joint certificate to an explicit
quadratic functional of the Fourier transform of a hard set of simple
zeros, and showed that the standard PRZZ/Levinson calculation does not
supply the required lower bound. The mollifier argument proves that many
simple zeros exist but does not label them or control their Fourier
statistics.

### Cycle 3: The BBLR Barrier and the Bandwidth-One Obstruction

This cycle brought both a crucial discovery and a definitive negative
result.

The **arithmetic agent** carried out the detailed exponent substitution
into BBLR Proposition 3.1 and found the hard barrier. For the terminal
Heath-Brown block with arbitrary short coefficients of length H = T^eta,
two error terms arise: T^{1/2 + 3*eta} (from the large-divisor/AB term)
and T^{3/4 + 2*eta} (from the Watt/Kuznetsov term). Both must be below
the trace scale T^{1+eta}. The Watt term permits only eta < 1/4, i.e.,
support sigma < 5/4 -- far short of the 1.43 needed for 85%. At the
target eta = 0.43, the Watt error exceeds trace grade by T^{0.18}. The
2025 amplified-fourth-moment theorem does not improve this, because its
total paired twist length remains T^{1/4}.

The best the BBLR machinery can deliver is support approaching 5/4,
which gives a limiting **79.72%** -- a major improvement over 67.25% but
not enough for 85%.

The **certificate agent** proved that no construction using only
bandwidth-one pair-correlation data, including signed Fourier tails,
number variance, and positivity constraints, can exceed 67.25%. The
Montgomery-Taylor kernel is already optimal in the larger signed-tail
extremal problem. It identified the "centered local von Mangoldt energy"
at frequency T/X as the first statistic that genuinely escapes the
bandwidth-one obstruction. It also showed that nested small-band
compressions with moments through degree four cannot improve the bound
either, because the adversary has explicit dilations matching all those
moments.

The **hybrid agent** introduced a different approach: the
Routh-Hermite index identity for the auxiliary function
A_c(s) = xi'(s) - c*xi(s). This gives an exact formula counting simple
zeros in terms of a "mixed defect" involving off-line zeros and multiple
zeros, with the advantage that the prime-side arithmetic stays at
support one. However, the strongest unconditional bound on this defect
gives only 67.25% again.

### Cycle 4: Correction, Consolidation, and the Geometric Mollifier

The **arithmetic agent** corrected an important error from cycle 3:
the first BBLR error term is AB, not (AB)^{1/2}. This changes the
exponent from T^{1/2 + 2*eta} to T^{1/2 + 3*eta}. Remarkably, the
all-block support ceiling of sigma < 5/4 remains the same, but now
because *two* terms (not one) meet the trace scale at eta = 1/4. The
agent produced a rigorous unconditional theorem: 79.7214...% of zeros
are simple and on the critical line, conditional only on the accepted
PDF infrastructure. It also formulated the first "coefficient-sensitive"
estimate (CSQD) that would break the barrier by exploiting the actual
structure of the Heath-Brown coefficients rather than treating them as
arbitrary bounded sequences.

The **certificate agent** designed one-sided sieve majorants and proved
that fixed-sign Selberg/Brun upper bounds cannot give a finite
normalized second-moment constant beyond support one. The Selberg sieve
factor of 2 leaves a loss that grows as H/L^2, which diverges for any
fixed support beyond 1. The effective sieve factor must be
1 + o(L^2/H), which no fixed upper sieve achieves.

The **hybrid agent** put the Routh defect into the Littlewood-Levinson
machine, reducing the 85% target to a single mean-square inequality
(labeled (MV85)). It also constructed an "all-orders geometric
mollifier" that formally inverts the perturbed zeta function using all
powers of the logarithmic derivative, with total Dirichlet length T
(support one). The first-order geometric correction (K=1) collapses to
the standard one-piece Mobius mollifier and gives no improvement. The
first genuinely new term is K=2.

### Cycles 5-6: The Geometric Mollifier Fails

The **hybrid agent** carried the all-orders geometric inverse through
to its analytic consequences. The formal inverse perfectly cancels
within the half-plane of absolute convergence, but analytic continuation
to the shifted line crosses the very zeros being counted, creating
residue terms that are precisely the Routh defect. The cancellation does
not survive the continuation.

In cycle 6, the complete K=2 geometric moment was evaluated with all
six cross-term blocks retained. The optimized result: 40.75%, strictly
weaker than the accepted 67.25%. Adding K=3 gives the already known
40.7511%. The finite geometric thread was terminated. It demonstrated
that merely having support-one coefficients does not manufacture
effective long mollification.

### Cycle 7: The Root Construction and the Weighted Intersection Current

Two important developments arrived together.

The **arithmetic agent** (in a separate "root construction" cycle)
proved a strict unconditional improvement at the small support
lambda = 101/100. At this support, all Heath-Brown blocks lie well
inside the BBLR range, and the quadratic-divisor theorem closes every
block with fixed power savings. The result: 67.92% of zeros are simple
and on the critical line. This is a modest but genuine unconditional gain
over 67.25%, requiring no new lemma -- just the observation that the
accepted BBLR theorem already covers slightly beyond support 1.

The **hybrid agent** proved a canonical weighted Levinson intersection
current that exactly identifies the simple-zero counting measure. Every
simple critical-line zero of xi is a transverse crossing of the
imaginary axis by the perturbed curve, with the same positive
orientation. Every multiple zero is a zero of the perturbed curve itself
and contributes nothing to the current. This is a local identity, not an
asymptotic count. It gives a precise weighted-Levinson target: the sum
of "non-diagonal Gram marginals" over simple zeros must exceed
0.1056*N.

### Cycle 8: The Exact Sawtooth Cancellation

The hybrid agent completed the phase calculation for the weighted
current and discovered an exact cancellation. The favorable diagonal
from the prime-side logarithmic derivative (worth about 0.307*N) is
entirely consumed by the continuous sawtooth correction on components
with no crossing. The remaining discontinuous part is exactly the
weighted simple-zero measure one is trying to bound. The completed
decomposition gives only M_s >= 0 -- no positive increment.

This is not an insufficient estimate; it is an identity. The separated
diagonal-plus-sawtooth approach was formally killed. The agent
identified the next construction outside this killed class: a two-scale
Gram kernel whose incommensurate zeros remove the sharp orthogonal
model.

### Arithmetic Cycle 5: The Breakthrough

The decisive breakthrough came from the arithmetic track. Instead of
trying to improve the spectral large sieve or find better Kloosterman
estimates, the agent realized that the key step is to **sum the signed
shift average before applying the Watt bound**, not after.

Concretely: in the BBLR framework, the standard approach converts the
terminal sixfold sum into an operator norm (via Cauchy-Schwarz), which
creates the regular diagonal T^{1/2 + 3*eta} and makes it insensitive
to the sign of the h-weight. The new approach instead:

1. Retains the smooth signed h-sum as a one-dimensional exponential sum.
2. Applies Poisson summation to that sum, getting rapid decay away from
   the nearest integer of the reciprocal fraction.
3. Uses standard fixed-divisor progression majorants for the
   Heath-Brown coefficients.
4. Only then sums over the Poisson frequency and the gcd.

The resulting remainder satisfies R_HB << (T^{1+eta} + T^{1/2+2*eta})
* (log T)^C. The first term is at the natural signed scale (always
trace-grade). The second term requires only eta < 1/2, i.e.,
support sigma < 3/2. This replaces both BBLR errors and does not
require the stronger pointwise CSQD inequality.

The key insight is that the gain over the Watt route is exactly
T^{2*eta - 1/2} whenever eta > 1/4: the precise power previously
missing from the AB line. The construction uses only the exact Poisson
identity from BBLR Proposition 3.1 (not its Watt majorization), Poisson
summation for the smooth signed shift, and the standard progression
upper bound -- applied before the finite Heath-Brown factors are
collapsed.


## The Final Result

With connected support extending to every fixed sigma < 3/2, the
optimal window profile at support 143/100 = 1.43 gives:

**Strict fixed-parameter result:**

> liminf N_0^s(T,2T) / N(T,2T) >= 0.8500235101...

This uses the exact rational certificate: sigma = 143/100 with profile
v(s) = 1 - (169/100)s^2, yielding a normalized Frobenius cost of
D = 1.14998... The proportion 2 - D = 0.85002... strictly exceeds 85%.

**Limiting checkpoint as support approaches 3/2:**

> liminf N_0^s(T) / N(T) >= 0.865674254456636...

This optimizes the saturated kernel K(t) = min(|t|, 1) over all
connected profiles as sigma approaches 3/2.

The input inventory for the final theorem is short:

1. The accepted zero-side framework (explicit-formula compression,
   rank-trace transfer) from the two supplied PDFs.
2. The exact Poisson-stage identity underlying BBLR Proposition 3.1.
3. Poisson summation for the retained smooth signed shift.
4. Standard fixed-divisor progression majorants, applied before
   collapsing the finite Heath-Brown factors.
5. The completed Type-I, pole, tail, zero-mode, and normalization
   transfer from arithmetic cycles 1-4.


## What Worked, What Didn't, and Why

**Successful approaches:**

- The Fourier-first dispersion idea (cycle 2), which recast the
  prime-pair problem as a local L^2 estimate rather than a
  shift-by-shift correlation theorem.
- The exact rational certificate (certificate cycle 1), which
  identified the specific test function used in the final result.
- The "sum the signed shift first" construction (arithmetic cycle 5),
  which broke the BBLR barrier by preserving the oscillation of the
  h-weight through the Watt step.
- The BBLR error correction (arithmetic cycle 4), which correctly
  identified the two terminal exponents and the support-5/4 checkpoint.

**Approaches that contributed insight but did not directly produce the
final result:**

- The sparse-lobe construction (arithmetic cycle 1) motivated the
  correct spectral gap but required the same aggregate estimate as the
  connected profile.
- The Routh-Hermite certificate (hybrid cycle 3) gave an elegant
  algebraic framework but could not improve the unconditional bound.
- The weighted intersection current (hybrid cycle 7) proved the exact
  topological identity for simple zeros but led to the sawtooth
  cancellation rather than a positive bound.

**Approaches that were definitively terminated:**

- Bandwidth-one certificates of any kind (certificate cycle 3): killed
  by the SDP obstruction and the feasibility of the flat adversary.
- The finite geometric mollifier K=1,2,3 (hybrid cycles 4-6): the
  all-orders cancellation does not survive analytic continuation past
  the zeros.
- Separated phase-error bounds (hybrid cycle 8): killed by the exact
  sawtooth cancellation identity.
- Scalar hybrids adding 67.25% + 40.75% (hybrid cycle 1): killed by
  the adversarial population that makes both bounds tight
  simultaneously.
- Exceptional-spectrum and fixed-modulus Kloosterman refinements
  (arithmetic cycle 4): these do not address the regular/large-divisor
  AB term.


## File Reference

| File | Role |
|---|---|
| `00_run_manifest.md` | Run configuration: target, timeline, accepted infrastructure |
| `00_FINAL_RESULT_85_PERCENT_CROSSED.md` | Final unconditional certificate and input inventory |
| `01_arithmetic_cycle1.md` | Prime-pair targets, sparse-lobe construction, aggregate estimate (AS) |
| `01_certificate_cycle1.md` | Exact rational certificate at support 1.43, sufficient condition for 85% |
| `01_hybrid_cycle1.md` | Joint certificate, residual-matrix method, scalar hybrid impossibility |
| `02_arithmetic_cycle2.md` | Fourier-first dispersion, reciprocal-cell reduction, (FM-BDH) formulation |
| `02_certificate_cycle2.md` | Exact transfer lemma, logarithmic-exception obstruction |
| `02_hybrid_cycle2.md` | Selector functional, weighted Levinson bottleneck |
| `03_arithmetic_cycle3.md` | BBLR exponent substitution, Watt barrier at eta=1/4, support-5/4 ceiling |
| `03_certificate_cycle3.md` | Bandwidth-one SDP obstruction, local energy statistic, quartic nesting failure |
| `03_hybrid_cycle3.md` | Routh-Hermite index identity, xi/xi' resultant certificate |
| `04_certificate_cycle4.md` | One-sided sieve majorant failure, effective sieve factor requirement |
| `04_hybrid_cycle4.md` | Littlewood reduction, geometric mollifier, K=1 no-gain lemma |
| `05_hybrid_cycle5.md` | All-orders inverse, Perron continuation, residue-tail obstruction |
| `06_hybrid_cycle6.md` | Complete K=2 moment evaluation, finite geometric thread terminated |
| `07_root_gain_support_1p01.md` | Unconditional gain at support 1.01 (67.92%) |
| `08_arithmetic_cycle4_unconditional_79p7214.md` | Corrected BBLR barrier, rigorous 79.72% checkpoint, CSQD target |
| `09_certificate_cycle5_adversary_constraints.md` | Explicit 67.25% adversary, quartic residual as first separating statistic |
| `10_hybrid_cycle7_weighted_levinson_current.md` | Positive intersection-current lemma, weighted Gram coupling |
| `11_hybrid_cycle8_phase_cancellation.md` | Exact sawtooth cancellation, separated phase-error class killed |
| `12_arithmetic_cycle5_support_3over2_86p5674.md` | Signed-shift-first construction, support extended to 3/2, 85% crossed |
