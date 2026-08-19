# The Withdrawn 100% Density Campaign

> **This entire research program's terminal result has been WITHDRAWN.**
> The density-one claim recorded in `FINAL_100_RESULT.md` is wrong.
> Its premises contradict each other at the claimed endpoint, and the
> feasible class of block profiles satisfying all stated conditions is
> empty. Every file in `docs/run/100/` belongs to this withdrawn program.
> None of its conclusions beyond the previously accepted ~96.25% floor
> are valid.

## What was attempted

The Zeta-100 campaign began on 2026-08-10 with a single goal: prove that
the proportion of nontrivial zeros of the Riemann zeta function that are
both simple and on the critical line tends to one in high dyadic windows.
In symbols, the target was

    lim inf  N_{0,simple}(T,2T) / N(T,2T)  =  1.

The accepted starting floor was approximately 0.95064, inherited from the
completed 85% and 95% forks. The campaign aimed to close the remaining
~5% gap using only the already-proved strict pair-trace support below 2
and optimized spectral certificates.

## The research approach

The campaign advanced along three parallel tracks.

**Arithmetic track.** Seven cycles (`arithmetic100_cycle1` through
`cycle8`) attempted to extend the pair-correlation support beyond the
critical threshold of 2. Cycle 1 identified a concrete obstruction: the
Type-III block in the Heath-Brown expansion cannot be handled by one-shot
Blomer-Pascadi grouping. Subsequent cycles pursued Poisson completion,
second dispersion, reciprocity, and multilinear Kloosterman strategies.
None achieved a support extension; every cycle ended with a method-class
kill and a first calculation outside the killed class.

**Certificate track.** Five cycles (`certificate100_cycle1` through
`cycle5`) optimized the spectral certificate -- the polynomial dual and
block profile that convert a pair-trace bound into a lower bound on the
simple-zero proportion. Cycle 1 introduced a two-phase cap-following
profile that raised the floor to ~96.249%. Later cycles explored
higher-moment duals (sixth-order polynomials), cubic certificates, and
wider block widths. Cycle 5 produced the final (now withdrawn) quadratic
that claimed to force density one.

**Hybrid track.** Four cycles (`hybrid100_cycle1` through `cycle4`)
attempted to combine the certificate machinery with selector-deletion
arguments, proving that removing a carefully chosen subset of zeros from
the spectral matrix cannot destroy enough of the tail residual to prevent
a density-one conclusion.

## What was discovered: a self-contradiction

The terminal claim in `FINAL_100_RESULT.md` rests on two premises that
cannot both be true.

**Premise 1 (the stability bound).** The "charged stability" inequality
keeps track of eigenvalues above 2, not just eigenvalues above 1. When
applied at the endpoint s/N = 1, this inequality requires

    M2  <  64517303 / 172727100  =  0.373521601...

where M2 is the centered second moment of the block profile. A second
quadratic gives the slightly weaker ceiling M2 < 0.374009..., but both
ceilings are binding.

**Premise 2 (the construction).** The outer-gap profile used in the final
cycle has a second moment that satisfies

    M2  >  18717 / 50000  =  0.37434.

This is not an approximation; it is a rigorous lower bound stated as an
exact rational inequality.

The two premises are incompatible. The exact gap between the assumed lower
bound and the required upper bound is

    18717/50000 - 64517303/172727100  =  6425437/25000000000  >  0.

No profile can simultaneously have M2 above 0.37434 and below 0.37352.
The set of admissible profiles satisfying all stated conditions is empty.

## The independent numerical verification

The file `verify/withdrawn_100_claim.py` reconstructs the contradiction
from scratch using exact rational arithmetic (Python's `fractions.Fraction`)
and high-precision numerics (`mpmath` at 80 decimal digits).

It performs two independent checks:

1. **Exact endpoint audit.** Starting from the source's own rational
   parameters (mu = 333333/500000, delta = 3385873/50000000, and the two
   displayed quadratic duals), it computes the M2 ceilings implied by each
   quadratic at s/N = 1. Both ceilings fall strictly below the claimed
   M2 > 0.37434. The script verifies this with exact rational comparisons
   and asserts that the "score gaps" are positive.

2. **Profile reproduction.** The script reconstructs the Euler cap
   V_sigma at sigma = 1.9999 with mu = 2/3, solves for the outer-gap
   profile that has mean one, and evaluates its second moment to 80-digit
   precision. The result is M2 = 0.374347517..., confirming that the
   profile's actual M2 exceeds the claimed maximum of 0.3144 by nearly
   0.06. The bound M2 <= 0.3144 would require an additional admissibility
   condition that is not stated anywhere in the source files.

The output (`verify/withdrawn_100_claim.out`) records the verdict:

    density-one premise package: INCONSISTENT AT s/N = 1
    claimed pointwise maximum M2 <= 0.3144: NOT REPRODUCED

## Why the claim cannot stand

The density-one argument works by deriving a lower bound on s/N that
exceeds 1, producing a contradiction against the tautological ceiling
s/N <= 1. This contradiction is supposed to prove that no subsequential
limit below one can exist.

But the lower bound exceeding 1 depends on M2 being large enough (above
0.37434) to make the quadratic score exceed delta = D - 1. The stability
inequality, in turn, requires M2 to be small enough (below 0.37352) for
the charged eigenvalue penalty to be affordable. Since no real number is
simultaneously above 0.37434 and below 0.37352, the argument has no valid
instantiation. The contradiction it derives is a consequence of mutually
inconsistent hypotheses, not of the zeta function's structure.

## Files in the 100/ directory

All 28 files listed below belong to the withdrawn campaign:

| File | Role |
|------|------|
| `00_RUN_100_MANIFEST.md` | Campaign charter, cycle contract, starting parameters |
| `FINAL_100_RESULT.md` | Terminal claim (withdrawn), with caution banner |
| `arithmetic100_cycle1` through `cycle8` | Arithmetic track: Type-III obstructions, Poisson, reciprocity |
| `certificate100_cycle1_96p249017923.md` | Optimized two-phase cap profile, floor ~96.249% |
| `certificate100_cycle2_higher_moment_class_kill.md` | Sixth/eighth-moment method kill |
| `certificate100_cycle3_cubic_96p512081.md` | Cubic certificate attempt |
| `certificate100_cycle4_cubic_96p518798.md` | Wider cubic certificate |
| `certificate100_cycle5.md` | Final (withdrawn) charged quadratic forcing density one |
| `hybrid100_cycle1.md` and `hybrid100_cycle1_95p67290.md` | Cap-profile increment, top-hat obstruction |
| `hybrid100_cycle2.md` through `cycle4` | Deletion-stable tail, signed Levinson contrast |
| `root100_cycle1` through `cycle5` | Root-level incremental floor improvements |
| `sixth_block_cycle2_method_kill.md` | Standalone sixth-moment block (below quartic floor) |
| `sixth_block_search.py` | Numerical search script for sixth-moment contractions |
| `bangbang_opt_cycle1_profile_search.md` | Bang-bang profile optimization |

The verification files `verify/withdrawn_100_claim.py` and
`verify/withdrawn_100_claim.out` sit outside this directory and provide
the independent disproof.

## Status

The last accepted unconditional result from this line of work remains the
~96.25% floor established in `certificate100_cycle1_96p249017923.md`. The
density-one claim and everything built on top of it -- the charged
stability argument, the wider-block quadratic certificate, and the
endpoint contradiction -- are retracted. The arithmetic track produced no
support extension beyond sigma < 2. The files are retained as source
history, not as accepted mathematics.
