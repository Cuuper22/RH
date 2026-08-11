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
argument in this module.  The primary-source inverse-residue phase and
Poisson integral are now recorded in `bblr_gcd_allocation.md`, and its finite
reindexing theorem accepts them as a supplied kernel, but the smooth
Heath--Brown instantiation and analytic derivative/tail estimates are not
constructed.

The two nested sums in splitCoeff exactly expose
\(d_1d_2=d\), respectively \(d_3d_4=d\), and the reduced products.
They take \(d\) as supplied data and omit the canonical source restrictions
\((a,d_2)=1\), respectively \((b,d_4)=1\).  Consequently splitCoeff and the
planned block coefficients built from it are raw candidates, not BBLR's
coefficients.  The regression in `BBLRGCDAllocation.lean` makes the defect
literal: at \(d=p=2\) with unit weights, the raw sum has four terms while the
canonical filtered sum has three.

The separate module `RH/Zeta85/Discharge/BBLRGCDAllocation.lean` now proves
the missing finite arithmetic for supplied BBLR sequences.  Allocation by
\(d_1=\gcd(A_0,d)\), \(d_2=d/d_1\) is a multiplicity-one equivalence with
the filtered splits, and the resulting coefficient is exactly

\[
 \sum_{d_1d_2=d}\sum_{\substack{am=p\\(a,d_2)=1}}
   \alpha_{d_1a}\,W_1(d_2m/M_1)
 =\sum_{A_0M_0=dp}\alpha_{A_0}W_1(M_0/M_1).
\]

The two-sided theorem also proves the finite \((p,q)\)-kernel reindexing and
the equivalence \(\gcd(dp,dq)=d\iff(p,q)=1\).  This discharges the gcd
allocation, bijection, and multiplicity subproblem.  It does not choose which
sharp Heath--Brown factors become the supplied outer sequence \(\alpha\) and
which residual factor is the genuine smooth variable carrying \(W_1\); that
is still the source-matched grouping obstruction.

The original progressionZeroMode is the mean of a generic family over all
residue classes, and sum_centeredProgressionCell proves that its centered
cells sum to zero.  The source nonzero Poisson block is supported on reduced
classes.  Accordingly reducedResidues, reducedProgressionZeroMode, and
reducedCenteredProgressionCell now construct the literal unit-class mean,
with

\[
 \sum_{\substack{r\bmod q\\(r,q)=1}}
   \left(C(q,r)-\frac1{\varphi(q)}
     \sum_{\substack{s\bmod q\\(s,q)=1}}C(q,s)\right)=0.
\]

The theorem is specialized both to one planned left component and to the
signed sum of all four planned left components.  The exact theorem
allClass_zeroMode_ne_reduced_zeroMode shows that the two means cannot be
interchanged: for mass supported at \(n=2\) on the block \([1,2]\) modulo
\(2\), the all-class mean is \(1/2\), while the reduced-class mean is zero.

This correction is finite coefficient bookkeeping, not an evaluation of the
source's frequency \(\ell=0\) term.
reducedCentering_alone_not_sufficient gives an exact logical countermodel to
the inference from centered unit cells to SingularSeriesCentering.  No
theorem connects either mean to the actual BBLR frequency \(\ell=0\) term or
proves a singular-series identity.

## Primary-source frequency \(\ell=0\) audit

The frequency \(\ell=0\) term in [Bettin--Bui--Li--Radziwiłł, Proposition 3.1,
equation (14)](https://arxiv.org/pdf/1609.02539) is not a residue-class mean
of \(c_{d,p}\).  Their Poisson summation eliminates the long variable
\(m_2\) modulo \(bn_1/d\), where \(d=(am_1,bn_1)\).  Before the later
\(d_1d_2=d_3d_4=d\) split, equation (14) has frequency factor

\[
 e\!\left(\mp \ell h\frac{\overline{am_1/d}}{bn_1/d}\right)
 F(a,b,m_1,n_1,d,\ell),
\]

and its \(\ell=0\) term is the proposition's gcd/integral main term

\[
 \sum_{\substack{a,b,m_1,n_1,h,d\\(am_1,bn_1)=d}}
 \alpha_a\beta_b W_0(dh/H)W_1(m_1/M_1)W_3(n_1/N_1)
 \int_0^\infty
 W_2\!\left(\frac{bn_1x}{dM_2}\right)
 W_4\!\left(\frac{am_1x}{dN_2}\right)\,dx.
\]

Reduced residues enter only after splitting \(d\) in the nonzero-frequency
family: then \(p=(a/d_1)(m_1/d_2)\),
\(q=(b/d_3)(n_1/d_4)\), and \((p,q)=1\).  Thus replacing the BBLR
\(\ell=0\) integral by reducedProgressionZeroMode is the wrong literal
method, even though reduced centering is the correct way to define the
progression error in route EDB.

The primary paper evaluates the four off-diagonal main terms only after
Mellin inversion and full summation of the quadratic-divisor problem.  It
does not state that an arbitrarily grouped, sharply truncated Heath--Brown
coefficient has a pointwise residue mean equal to the prime-pair singular
series.  The run archives likewise only assert that the four zero-frequency
terms "recombine"; they do not supply the smooth HB allocation, the
resulting \(\ell=0\) integral, or its Euler/Ramanujan evaluation.  In the
formal repository the singular-series function in signedPairAggregate is
existential data, not the Ramanujan series
\(\sum_q\mu(q)^2\varphi(q)^{-2}c_q(h)\).

Consequently the inference class using only reduced-cell centering is
finished and killed by the exact countermodel.  This does not kill a proof
from the actual smooth HB construction.  The surviving theorem would have
to construct that block, prove equality to the full BBLR Poisson formula
including its frequency \(\ell=0\) integral and the preliminary
shift-replacement error, and then evaluate the signed sum of those integrals
against the explicit Ramanujan singular series, with every remaining error
and logarithmic exponent displayed.  No such construction or estimate is
asserted here.  SingularSeriesCentering remains only a schema for the
equality component of that missing theorem.

## Exact remaining blocker

Run 12 equations (5)--(11) do not specify:

1. the cutoff \(Z=Z(T,Y)\) or a proof that its smoothly truncated identity
   equals the sharp identity above on every relevant integer;
2. the scale-dependent grouping plan and smooth dyadic partition that map
   the eight slots to supplied BBLR outer sequences and genuine smooth inner
   variables carrying \(W_1,W_3\);
3. the instantiation of the proved canonical \((p,q)\) collapse with those
   actual grouped sequences and the integrated Fourier factor
   \(F_{d,\ell}\), including its derivative bounds and infinite-frequency
   tail; or
4. the BBLR \(\ell=0\) gcd/integral formula after the actual smooth HB
   allocation, and its full signed Euler/Ramanujan recombination with the
   prime-pair singular-series term, including the non-exact replacement
   errors.

The narrow missing construction is therefore an explicit plan and smooth
partition together with a proved equality from each signed Heath--Brown
block to the supplied outer/smooth inputs of `collapsedCoeff`, followed by an
instantiation of `collapsedKernelSum_eq_originalFibers` with the full BBLR
equation (14) kernel and a constructed zeroModeHB satisfying an identity of
the form

    zeroModeHB h = S h * X * IV + zeroModeError h

with a bound for the signed aggregate of zeroModeError at the exact required
logarithmic exponent.  SingularSeriesCentering is only the zero-error special
case; neither it nor the required error bound is asserted.  Until these
identities are supplied, the coefficients in `HBDepthFour.lean` must not be
renamed as run 12's \(c_{d,p}\) and \(e_{d,q}\).  The corrected
`BBLRGCDAllocation.collapsedCoeff` is the source collapse for supplied
sequences, but it is not yet instantiated by the actual signed
Heath--Brown blocks.  Therefore (EDB), the common-scale cross-\(Y\) target,
and (WG-HB) remain unproved for the cycle-5 coefficients.

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

The dependency printer covers 29 selected public theorems, each of which
prints exactly [propext, Classical.choice, Quot.sound].  The module and
printer contain no declared research assumption or proof placeholder.

No numerical verifier was added: this milestone contains exact finite
convolution identities and no calibrated numerical claim.

The canonical gcd-allocation correction and its independent \(d=p=2\)
enumeration are audited separately in `docs/audit/bblr_gcd_allocation.md`.
