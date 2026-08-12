# Actual-block centering bridge for R1b

## Scope

`RH/Zeta85/Discharge/RSBlockMomentBridge.lean` closes one finite/formal gap
between the existing Rudnick--Sarnak contraction calculation and
`BlockMomentLimits`.  The RS main term is naturally an uncentered trace
moment, while `QuarticGramFamily.centeredBlockMoment` is the normalized trace
of `(block T - 1)^k`.

No published theorem, Poisson formula, height-removal estimate, finite-grid
estimate, or new axiom is introduced.  The module is intentionally not
imported by `Main.lean` and does not construct an analytic input instance.

## Exact finite theorem

For the literal principal block, define

\[
 c_a(T)=\frac{\operatorname{Re}\operatorname{tr}(\operatorname{block}(T)^a)}
                  {\operatorname{blockDim}(T)}.
\]

Lean's division convention makes this definition total even at dimension
zero.  No positivity premise is needed for the polynomial identity

\[
 \frac{\operatorname{Re}\operatorname{tr}
   ((\operatorname{block}(T)-I)^k)}{\operatorname{blockDim}(T)}
 =\sum_{a=0}^k(-1)^{k-a}\binom{k}{a}c_a(T),
 \qquad 0\le k\le4.
\]

This is `centeredBlockMoment_eq_centeredTransform`.  The proof expands the
matrix polynomial before using additivity of the real trace.  It is valid for
the actual finite matrix and does not use Hermitianity or a limiting argument.

## Exact analytic boundary

`UncenteredRSBlockLimits F` is the remaining actual-block/cyclic-contraction
statement:

```lean
moments : forall k, k <= 4 ->
  Tendsto (uncenteredBlockMoment F k) atTop
    (nhds (uncenteredContractionMoment (topHatR3Terms p) mu k))
```

This is an assumption boundary, not a proved RS consequence.  It says exactly
that the literal principal block's uncentered moments converge to formula
(27), after the cyclic RS contractions have been evaluated.  Degree zero is
included because finite binomial centering uses its normalized identity
trace; its target is `1`.  In the intended construction this clause is the
elementary eventual-positive-dimension check, not an application of the RS
all-tuples theorem.

Given this boundary and `PrincipalCyclicBlock F`,
`centered_moment_limits` applies finite-sum continuity and the already proved
`topHat_centeredContraction_eq_formula21`.  It returns the four centered
formula-(21) limits requested by `BlockMomentLimits.moments`.

The two off-RH complex-Poisson obligations are deliberately not folded into
`UncenteredRSBlockLimits`:

- summability of every complex alias family at actual `ZIprime` zeros;
- cancellation of each such alias sum.

`blockMomentLimits_of_uncenteredRS` takes those two clauses separately and
constructs the existing `BlockMomentLimits` structure.  Thus the formal
constructor cannot make complex alias cancellation follow from a real-axis
identity or from moment convergence.

## Smallest missing analytic theorem

For one constructed family `F`, the smallest next analytic conclusion is

```lean
UncenteredRSBlockLimits F
```

from the already separate `PrincipalCyclicBlock F` and
`RS1996ZetaInputs Z`, together with proofs of the two complex-alias clauses.
The proof must supply, rather than assume implicitly, the following steps:

1. prove smoothness and strict total Fourier support for each actual cyclic
   symbol formed from the distinguished local profile;
2. apply the smoothed unconditional RS theorem with one common height
   normalization for all degrees `1 <= k <= 4`, and prove the degree-zero
   normalized identity trace tends to `1` from eventual positive dimension;
3. derive the complex-frequency Poisson expansion at the actual enlarged
   zero set, using the separately stated summability and cancellation;
4. prove the finite/infinite-grid interchange and end errors for the third
   and fourth cyclic traces (the existing reusable proof reaches degree two);
5. carry `log T` versus `l(T)=log(T/(2*pi))`, so the effective bandwidth
   tends to `mu` without replacing it by equality;
6. remove height smoothing simultaneously through degree four; and
7. use the locally uniform translated-product convergence already recorded
   in `PrincipalCyclicBlock` to pass to the sharp top-hat contractions.

Steps 1--7 are analytic.  Binomial centering, passage of a finite sum through
`Tendsto`, and identification with formula (21) are now formal theorems.

## Validation

```bash
lake build RH.Zeta85.Discharge.RSBlockMomentBridge
lake env lean comparator/PrintAxioms/RSBlockMomentBridge.lean
python3 verify/rs_block_moment_bridge_exact.py > /tmp/rs_block_moment_bridge_exact.out
diff -u verify/rs_block_moment_bridge_exact.out \
  /tmp/rs_block_moment_bridge_exact.out
```

The dependency printer covers the finite identity, the limit theorem, and the
constructor.  The exact verifier independently expands `(X-1)^k` through
degree four.  Its printed interface inventory is descriptive; the Lean
printer and theorem statements, rather than Python, check that split.
