> **Canonical reference**: [AXIOMS.md](../../AXIOMS.md) (Axioms 2–4: trace transfer). See also [GUIDE.md](../../GUIDE.md) topic index.

# Rudnick--Sarnak pair-integral bridge

## Scope

`RH/Zeta85/Discharge/RSPairIntegrals.lean` evaluates every one- and two-pair
term in `rsMainTerm (weightedCyclicSymbol mu r)` through degree four.  This is
the analytic contraction bridge inside the published RS main term.  It is not
the height-smoothing, complex-Poisson, finite-grid, or principal-block bridge.

No new primitive declaration, proof placeholder, structure field, block
hypothesis, or calibrated numeric constant is introduced.

## One-pair evaluation

For real functions `f` and `g`, define

\[
 I_{\mu}(f,g)=
 \int_{\mathbb R}|w|\,\mu
   \int_{\mathbb R}f(x)g(x+w/\mu)\,dx\,dw
\]

and

\[
 D(f,g)=\int_{\mathbb R}f(x)
   \int_{\mathbb R}|y-x|g(y)\,dy\,dx.
\]

For `mu > 0`, `integral_abs_mul_shift_div` proves the inner substitution

\[
 \int |w|g(x+w/\mu)\,dw
 =\mu^2\int |y-x|g(y)\,dy.
\]

If the literal two-variable kernel `onePairIntegrand mu f g` is integrable,
`onePairCoordinateIntegral_eq` applies Fubini and proves

\[
 I_{\mu}(f,g)=\mu^3D(f,g).
\]

The base theorem assumes the ordinary Mathlib `Integrable` statement for the
displayed kernel.  It does not assume the desired equality or a moment
conclusion.  `distanceIntegral_comm` separately proves `D(f,g)=D(g,f)` from
integrability of the literal distance kernel.  The later compact-support
specialization proves these premises rather than postulating them.

The module proves the corresponding `rsPairIntegral` equality for the unique
degree-two pair, all three degree-three pairs, and all six degree-four pairs.
At degree four, the four adjacent pairs reduce to
`D (r^3) r` and the two opposite pairs reduce to `D (r^2) (r^2)`.
`normalized_k4_onePairSum` proves their exact normalized sum:

\[
 \frac{\text{six one-pair terms}}{\mu}
 =\mu^2\left(4D(r^3,r)+2D(r^2,r^2)\right).
\]

## Normalization

`weightedCyclicSymbol mu r 0` is `mu * \int r^k`.  A one-pair contraction is
`mu^3` times its distance integral.  Formula (27) is therefore the RS main
term divided by `mu`.  The definition `normalizedRSMainTerm` records this
division explicitly, and the module proves

\[
\begin{aligned}
 \frac{\operatorname{RSMain}_1}{\mu}&=\int r,\\
 \frac{\operatorname{RSMain}_2}{\mu}&=\int r^2+\mu^2D(r,r),\\
 \frac{\operatorname{RSMain}_3}{\mu}&=\int r^3+3\mu^2D(r^2,r),\\
 \frac{\operatorname{RSMain}_4}{\mu}&=\int r^4
 +\mu^2\bigl(4D(r^3,r)+2D(r^2,r^2)\bigr)
 +\mu^4\bigl(2P(r)+\mathcal X(r)\bigr),
\end{aligned}
\]

where

\[
 P(r)=\int r(x)^2h(x)^2\,dx,
 \qquad h(x)=\int |y-x|r(y)\,dy.
\]

Thus no factor of `mu` is hidden: a `q`-pair term has power
`mu^(1+2*q)` before division by `mu`, hence powers `mu^2` and `mu^4` for
one and two pairs after normalization.

## Degree-four two-pair classification

The three canonical pairings are machine-classified pointwise:

| pairing | partial sums | coordinate core |
|---|---|---|
| `([0,2],[1,3])` | `0,u,0,v` | `mu * \int r(x)^2 r(x+u/mu) r(x+v/mu) dx` |
| `([0,1],[3,2])` | `0,u,u+v,u` | `mu * \int r(x) r(x+u/mu)^2 r(x+(u+v)/mu) dx` |
| `([0,1],[2,3])` | `0,u,u+v,v` | `mu * \int r(x) r(x+u/mu) r(x+(u+v)/mu) r(x+v/mu) dx` |

`integral_fin_two` proves the measure-preserving identification
`(Fin 2 -> R) = R x R` at the level of Bochner integrals.
`rsPairIntegral_k4_separated_coordinate`,
`rsPairIntegral_k4_nested_coordinate`, and
`rsPairIntegral_k4_crossing_coordinate` then identify the actual
`rsPairIntegral`s with the two-coordinate integrals of these cores.

## Two-pair evaluation

For the literal three-variable kernels, Fubini followed by two sequential
applications of `w = mu * (y - x)` proves

\[
\begin{aligned}
 \text{separated}&=\mu^5P(r),\\
 \text{nested}&=\mu^5P(r),\\
 \text{crossing}&=\mu^5\mathcal X(r).
\end{aligned}
\]

The crossing functional is exactly

\[
 \mathcal X(r)=\iiint |x-y||y-z|r(x)r(y)r(z)r(x+z-y)\,dz\,dy\,dx,
\]

which is the variable convention in `docs/audit/rs_reduction.md`.
`rsPairIntegral_k4_separated_eq`, `rsPairIntegral_k4_nested_eq`, and
`rsPairIntegral_k4_crossing_eq` are the corresponding actual RS-contraction
equalities.  These theorems are discharged under their explicit literal
`Integrable` hypotheses; that qualification is part of their statements.

## Primitive analytic hypotheses

The module also proves that no displayed `Integrable` premise needs to be an
external input for the intended smooth profiles.  If

```lean
hmu : 0 < mu
hr  : Continuous r
hrc : HasCompactSupport r
```

then compact images under the explicit linear coordinate maps contain the
supports of the one-pair and all three two-pair kernels.  Continuity plus
compact support gives their integrability.  The nested symmetry premise is
also derived: `pairDistancePotential r` is continuous as the convolution of
`r` with `abs`, so `nestedAuxProfile r` is continuous and compactly
supported.  The wrapper theorems

- `normalizedRSMainTerm_k2_of_continuous_compactSupport`,
- `normalizedRSMainTerm_k3_of_continuous_compactSupport`, and
- `normalizedRSMainTerm_k4_of_continuous_compactSupport`

therefore consume only these three primitive hypotheses.  A smooth compactly
supported profile supplies `Continuous r` and `HasCompactSupport r`, but the
separate proof that its full cyclic symbol satisfies the published RS test's
smoothness and strict total-support condition is not asserted here.

## Exact remaining scope

The internal `rsMainTerm` evaluation through degree four is complete.  It
does not instantiate `RS1996ZetaInputs.theorem31`, identify the normalized
main term with a finite matrix block, or prove any `BlockMomentLimits` field.
The independent R1b blockers remain: admissibility of the cyclic symbols for
the published theorem with strict total support, common
height-smoothing normalization, `log T` versus `l(T)`, complex-frequency
Poisson summability at actual zeros, and the third/fourth finite-grid and end
estimates.  R1a principal-block identification is also independent.

## Validation

The exact local gates are

```bash
lake build RH.Zeta85.Discharge.RSPairIntegrals
lake env lean comparator/PrintAxioms/RSPairIntegrals.lean
python3 verify/rs_pair_integrals_exact.py > /tmp/rs_pair_integrals_exact.out
diff -u verify/rs_pair_integrals_exact.out /tmp/rs_pair_integrals_exact.out
```

The dependency printer covers the scaling, Fubini, one-pair evaluations,
degree-four one-pair sum, all three two-pair classifications and evaluations,
the compact-support discharge, and the normalized degree-one through
degree-four formulas.  Every selected line reports exactly
`[propext, Classical.choice, Quot.sound]`.

`verify/rs_pair_integrals_exact.py` independently enumerates the exact
pairing counts, recomputes every displayed partial-sum profile, and checks the
symbol/Jacobian scaling powers `mu^3 -> mu^2` and `mu^5 -> mu^4`.  Its
committed output ends in `PASS`.
