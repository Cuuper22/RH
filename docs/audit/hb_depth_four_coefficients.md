# Exact depth-four Heath--Brown coefficient layer

Status: **the sharp-cutoff algebraic layer is proved; it is not identified
with the coefficients asserted in run 12, and no A1 estimate is proved**.

## Constructed object

RH/Zeta85/Discharge/HBDepthFour.lean defines
\(\mu_Z(n)=\mu(n)1_{n\leq Z}\) and the arithmetic function

\[
 H_{4,Z}
 =4\mu_Z*\log-6\mu_Z^2*\zeta*\log
  +4\mu_Z^3*\zeta^2*\log-\mu_Z^4*\zeta^3*\log .
\]

The formal remainder identity is

\[
 \Lambda-H_{4,Z}=(\mu-\mu_Z)^4*\zeta^3*\log .
\]

Every nonzero factor in \(\mu-\mu_Z\) is larger than \(Z\), so the
right-hand side vanishes coefficientwise for \(n\leq Z^4\).  Hence
hb4_eq_vonMangoldt and sum_hbComponent_eq_vonMangoldt prove the exact
depth-four identity in that range.

Each of the four signed summands is represented by eight literal factor
slots: up to four truncated Möbius factors, up to three zeta factors, and
one logarithm factor.  HBGroupingPlan chooses a subset of those slots for
each summand and each common dyadic scale.  For every such choice,
hbGrouped_factorization proves that the two grouped arithmetic functions
multiply back to the original signed summand.  The plan has data fields
only; it carries no estimate, closure assertion, or analytic hypothesis.

For grouped functions \(\alpha,\beta\), the reduced coefficient is the
finite sum

\[
 C_{\alpha,\beta}(d_1,d_2;p)
 =\sum_{xy=p}\alpha(d_1x)\beta(d_2y),
\]

and the divisor-split coefficient is

\[
 C_{\alpha,\beta}(d;p)
 =\sum_{d_1d_2=d}C_{\alpha,\beta}(d_1,d_2;p).
\]

reducedCoeff_eq_convolution identifies the first sum with the Dirichlet
convolution of the two dilated functions.  abs_reducedCoeff_le and
abs_splitCoeff_le prove the literal termwise absolute majorants; no
unspecified divisor-bound constant is inserted.

CommonScaleGeometry uses one index \(j\) for

\[
 H_j=H_0\,2^j,\qquad P_j=H_jQ,\qquad Y_j=P_jQ=H_jQ^2.
\]

HBBlockAddress then carries the shared
\((j,d,\ell,p,q,\text{left term},\text{right term})\) index.
plannedLeftBlockCoeff and plannedRightBlockCoeff localize the explicit
divisor-split coefficient candidates to the exact natural-number blocks

\[
 p\in[\lfloor P_j/d\rfloor,2\lfloor P_j/d\rfloor],\qquad
 q\in[\lfloor Q/d\rfloor,2\lfloor Q/d\rfloor].
\]

Their support and absolute-majorant theorems are proved.  These closed blocks
can overlap at endpoints and are not asserted to reconstruct the source's
smooth dyadic partition.  The separate hard half-open decomposition
dyadicPart is exact and its finite sum reconstructs every positive-index
coefficient, but no theorem identifies it with the planned blocks.

fixedQKernelSum and fixedQKernelL1 expose the fixed-modulus inner family and
its outer \(q\)-norm.  commonScaleLeadingSum then sums the same explicit
addresses over \(j,d,p,q\) and a supplied finite nonzero \(\ell\)-range
before taking an absolute value; its scale weight can carry the future
\(T/Y_j\) factor.  Thus finite candidate forms of the WG-HB and cross-
\(Y\) targets are syntactically expressible on the constructed
coefficients.  The infinite \(\ell\)-tail and its decay are not proved.
plannedKernelTerm imposes \((p,q)=1\).  The kernel remains an explicit
argument because run 12 does not construct its claimed \(F_{d,\ell}\),
inverse-residue phase, or signed \(h\)-sum.

The two nested sums in splitCoeff exactly expose
\(d_1d_2=d\), respectively \(d_3d_4=d\), and the reduced products.
They take \(d\) as supplied data: they do not prove
\(d=\gcd(am_1,bn_1)\), a unique allocation/bijection, or the multiplicities
of the source change of variables.  Nor do they insert source smooth weights
or factor-allocation restrictions.  Those belong to the missing
source-matched grouping and kernel construction; coprimality of \(p,q\) is
imposed only later by plannedKernelTerm.

Finally, progressionZeroMode is the mean of a generic family over all
residue classes, and sum_centeredProgressionCell proves that its centered
cells sum to zero.  The source Poisson block is supported on reduced classes,
and no theorem connects this generic mean to plannedKernelTerm or proves
unit-class cancellation.  SingularSeriesCentering names the pointwise
equality that would identify a future zero mode from the actual BBLR block
with the subtraction \(S(h)X I_V\); no instance is asserted.

## Exact remaining blocker

Run 12 equations (5)--(11) do not specify:

1. the cutoff \(Z=Z(T,Y)\) or a proof that its smoothly truncated identity
   equals the sharp identity above on every relevant integer;
2. the scale-dependent grouping plan and smooth dyadic partition that map
   the eight slots to the BBLR variables \(a,m_1,b,n_1\);
3. the exact separated Fourier factor \(F_{d,\ell}\), including its
   dependence on the selected grouping and divisor split; or
4. the zero-frequency formula whose full signed recombination is to equal
   the prime-pair singular-series term pointwise in \(h\).

The narrow missing construction is therefore an explicit plan and smooth
partition together with a proved equality from the resulting
plannedLeftBlockCoeff/plannedRightBlockCoeff sum to BBLR equation (14),
followed by

    SingularSeriesCentering zeroModeHB S X IV

for the zero mode produced by that same equality.  Until these identities
are supplied, the module's coefficients must not be renamed as run 12's
\(c_{d,p}\) and \(e_{d,q}\), and (EDB), the common-scale cross-\(Y\)
target, and (WG-HB) are not statements about source-identified
coefficients.

There is also an exact nonuniqueness result for product-only recovery.
empty_singleton_groupings_distinct proves that the empty left grouping and
the singleton-Möbius left grouping are different arithmetic functions,
while hbGrouped_factorization proves that both groupings have the same full
signed component product.  Therefore the recombined product alone cannot
uniquely recover the individual coefficient factors.  This theorem does not
rule out recovery from additional source constraints; it proves only that a
grouping cannot be inferred from the product identity by itself.

## Validation

    lake build RH.Zeta85.Discharge.HBDepthFour
    lake env lean comparator/PrintAxioms/HBDepthFour.lean

The dependency printer covers 24 selected public theorems, each of which
prints exactly [propext, Classical.choice, Quot.sound].  The module and printer contain no
declared research assumption or proof placeholder.

No numerical verifier was added: this milestone contains exact finite
convolution identities and no calibrated numerical claim.
