> **Canonical reference**: [FINDINGS.md](../../FINDINGS.md) (BBLR error correction). See also [GUIDE.md](../../GUIDE.md) topic index.

# K=4 smooth Heath--Brown to BBLR grouping audit

Status: **the fixed-scale literal-slot construction is impossible; the
source-matched coefficient construction and the analytic estimate remain
open**.

## Exact method class

Bettin--Bui--Li--Radziwill Proposition 3.1 starts from

\[
 \alpha_a\beta_b
 W_1(m_1/M_1)W_2(m_2/M_2)
 W_3(n_1/N_1)W_4(n_2/N_2)
\]

on the equation

\[
              am_1m_2-bn_1n_2=\pm h.
\]

Thus there is one arbitrary coefficient sequence on each side, on \(a\) and
\(b\), and two one-dimensional smooth variables on each side.  In the
nonzero Poisson family, the exact source allocation is

\[
 d_1d_2=d_3d_4=d,
 \qquad p=am_1,
 \qquad q=bn_1,
\]

after the gcd factors have been removed.  The conditions
\((a,d_2)=(b,d_4)=1\) make this allocation canonical.  The theorem
`BBLRGCDAllocation.collapsedCoeff_eq_divisorSum` proves that this operation
reindexes the supplied pair \(\alpha_a W_1(m_1/M_1)\) with multiplicity one.
It does not manufacture either \(W_1\) or \(W_2\), and \(W_2\) remains in the
Fourier integral.  Therefore the gcd allocation solves the source indexing
problem but not the preceding smooth Heath--Brown grouping problem.

The method class audited here is the literal-slot construction asserted by
the block-grouping discussion in
`docs/run/08_arithmetic_cycle4_unconditional_79p7214.md` and the fixed
asymmetric specialization in
`docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md`: after a dyadic
Heath--Brown decomposition,
all coefficient-bearing slots are placed in the one arbitrary outer
sequence, while each BBLR inner variable is one original unrestricted
\(\mathbf 1\)- or \(\log\)-slot with its own smooth dyadic weight.  In
particular, this class does not multiply several HB slots and then call the
result a smooth \(W_i\).  Such multiplication produces a Dirichlet-convolution
coefficient, which BBLR Proposition 3.1 does not accept on its inner
variables.

This is a deliberately narrow method class.  The result below does not say
that the shifted convolution itself is impossible to estimate.

## Exact K=4 counterexample

Fix

\[
 \eta=\frac{43}{100},\qquad X=T^{1+\eta}=T^{143/100},
 \qquad X^{1/4}=T^{143/400}.
\]

The zero-based \(j=1\) component of the proved sharp depth-four identity
(the two-Möbius summand) is

\[
 -6\,\mu_Z*\mu_Z*\zeta*\log.
\]

This inventory is checked directly against `HBDepthFour.hbAtom` by
`hb_component_one_inventory`, while `hb_component_one_scalar` checks the
coefficient (-6).  Moreover `muCut_ne_coefficientOne` proves, once
(Z\geq2), that a truncated Möbius slot cannot be treated as an unrestricted
coefficient-one slot: the two functions already differ at (2).  Thus in the
literal-slot class the two Möbius atoms must remain in the outer arbitrary
coefficient.  Consider the dyadic exponent block

\[
 \left(\frac{43}{200},\frac{43}{200},
       \frac25,\frac35\right),                         \tag{1}
\]

where the first two entries are the truncated Möbius slots and the last two
are the zeta and log slots.  It satisfies all of the exponent conditions used
by the terminal grouping dichotomy:

\[
 2\frac{43}{200}+\frac25+\frac35=\frac{143}{100},
 \qquad
 2\frac{43}{200}=\frac{43}{100},                         \tag{2}
\]

\[
 0<\frac{43}{200}<\frac{143}{400},
 \qquad
 0<\frac25,\frac35<\frac XH\text{-exponent}=1.           \tag{3}
\]

Hence the two irregular slots already form an outer coefficient of the
claimed length \(A=H=T^{43/100}\), neither irregular atom violates the K=4
cutoff, and neither unrestricted atom triggers the stated Type-I alternative.
The remaining literal smooth lengths, however, are

\[
                         T^{2/5},\qquad T^{3/5}.             \tag{4}
\]

They are not the run-12 left pair

\[
                         T^{1/2},\qquad T^{1/2},             \tag{5}
\]

and every available slot has exponent distance exactly \(1/10\) from
\(1/2\).  They are also not the right pair

\[
                         T^{7/100},\qquad T^{93/100};        \tag{6}
\]

the minimum distance to either requested right exponent is \(33/100\).
Consequently fixed dyadic constants do not help, and any \(T^{o(1)}\)
support cushion is eventually smaller than the fixed \(1/10\) left gap.

The Lean predicate `LiteralSideGrouping M1 M2 eps` permits a permutation of
the two literal smooth slots and exponent error at most `eps`.
`no_left_literal_grouping` proves impossibility for every
\(\varepsilon<1/10\); `no_right_literal_grouping` proves impossibility for
every \(\varepsilon<33/100\); and `no_asymmetric_literal_grouping` kills the
full two-sided assignment for every \(\varepsilon<1/10\).  The conclusion is
about the universal exponent-grouping lemma.  It does not assert a lower
bound for the shifted sum supported on (1).

## Why collapsing slots does not repair the stated method

If two coefficient-one slots are collapsed to their product \(r=uv\), the
coefficient of \(r\) is

\[
                       \sum_{uv=r}1=d_2(r),                 \tag{7}
\]

not one.  The module defines this exact factor-pair multiplicity as
`twoUnitSlotMultiplicity`, proves that it equals \(2\) at \(r=2\) and \(3\)
at \(r=4\), and proves that it is exactly the arithmetic-function convolution
\(\zeta*\zeta\).  Collapsing a Möbius or log slot similarly leaves a signed
or logarithmic convolution coefficient.  Mellin separation can separate
already smooth weights; it does not erase these arithmetic multiplicities.

Accordingly the sentence in
`docs/run/12_arithmetic_cycle5_support_3over2_86p5674.md` that a deeper finite
identity and a support cushion handle the factor-grouping slack is not a construction for
the K=4 block (1).  Increasing the depth gives more slots, but by itself does
not force two unrestricted slots to have the prescribed exponents on every
dyadic block.

## Finish-or-kill verdict and narrow survivors

The exact requested class is finished and killed:

> A universal K=4 grouping which assigns every terminal dyadic component to
> \(A=B=H=T^{43/100}\),
> \(M_1=M_2=T^{1/2}\),
> \(N_1=T^{7/100}\), and \(N_2=T^{93/100}\), while keeping the BBLR inner
> variables as literal smooth HB slots, does not exist.

The obstruction does not indict BBLR Proposition 3.1 or the proved gcd
allocation.  It indicts the fixed asymmetric identification premise used
before them.  The surviving constructions are narrower and must be supplied
explicitly:

1. retain the actual block-dependent smooth scales (for (1), \(2/5\) and
   \(3/5\)) and prove a uniform all-scale estimate which preserves
   simultaneous cancellation before a progression majorant is taken.  On
   this exact block, `ActualScaleBBLR.lean` proves that direct use of BBLR
   Proposition 3.1 misses trace by \(9/50\) even in its smaller error term,
   while the run-12 progression majorant applied after equation (14) misses
   by \(23/100\) at \(d=1\);
2. prove a new exact coefficient identity expressing each HB block as a
   controlled finite or integrable superposition of BBLR forms with the
   desired inner scales, including pointwise equality, support, derivative
   norms, and recombination errors; or
3. prove a higher-dimensional quadratic-divisor estimate which retains the
   several HB factor variables and their arithmetic coefficients instead of
   forcing them into the two smooth BBLR slots.

The source-audited one-shot tests in
`docs/audit/premajorant_di_one_shot.md` further narrow the first survivor
without eliminating it.  Collapsing the two Möbius pairs and
\((|\ell|,h)\) into three arbitrary coefficient norms, applying Drappeau
Theorem 2.1 once, and integrating gives exponent \(179/100\), an exact
\(9/25\) excess over trace.  That direct collapsed class is power-killed.
The different literal completed \(r=a\) Pascadi map is structurally
inapplicable because completion supplies \(k\bar a\), not \(ka\), and its
\(k=0\) term is outside the cited dyadic sum.  The conditional Pascadi
exponent substitution is not a bound.  A source-faithful
\((q,a)\)-dependent reindex with a separate zero-frequency treatment remains
open, as does a simultaneous coefficient-sensitive estimate before those
norms are taken.

None of these survivors is constructed by the existing files, so the
coefficient-sensitive `(WG-HB)` estimate remains unproved for the actual
cycle-5 coefficients.

## Reproduction

```sh
lake build RH.Zeta85.Discharge.HBToBBLRSmoothGrouping
lake env lean comparator/PrintAxioms/HBToBBLRSmoothGrouping.lean
python3 verify/a1_smooth_grouping.py
diff -u verify/a1_smooth_grouping.out <(python3 verify/a1_smooth_grouping.py)
```

The Lean module contains no declared research premise or proof placeholder.
The independent verifier uses exact `fractions.Fraction` arithmetic.
