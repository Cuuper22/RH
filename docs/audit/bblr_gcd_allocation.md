> **Canonical reference**: [FINDINGS.md](../../FINDINGS.md) (BBLR error correction). See also [GUIDE.md](../../GUIDE.md) topic index.

# BBLR gcd allocation and the cycle-5 coefficient map

Status: **the gcd allocation, its multiplicity, and the generic finite-kernel
reindexing are proved exactly; the run's Heath--Brown grouping and analytic
kernel estimates are not identified by this result**.

## Primary-source formula

The source checked is S. Bettin, H. M. Bui, X. Li, and M. Radziwill,
*A quadratic divisor problem and moments of the Riemann zeta-function*,
[arXiv:1609.02539](https://arxiv.org/abs/1609.02539), Proposition 3.1 and its
proof.  In the arXiv TeX source the
Poisson display has label `asd`, which is the display referred to as equation
(14) in the run.  The full \(d_1d_2=d_3d_4=d\) reparametrization occurs later
in the proof of the estimate labeled `sbfz`.

Use capital letters for the variables before the gcd allocation.  The source
first sets

\[
 d=\gcd(A_0M_0,B_0N_0),
\]

eliminates one long variable, applies one Poisson summation, and changes the
old shift to \(dh\).  Its nonzero-frequency integrand contains

\[
 \alpha_{A_0}\beta_{B_0}W_0(dh/H)
 W_1(M_0/M_1)W_3(N_0/N_1)
 e\!\left(\mp \ell h\frac{\overline{A_0M_0/d}}{B_0N_0/d}\right)
\]

times

\[
 \int_0^\infty
 W_2\!\left(\frac{(B_0N_0/d)x}{M_2}\right)
 W_4\!\left(\frac{(A_0M_0/d)x}{N_2}\right)e(\ell x)\,dx.
\]

This is a single Poisson integral containing both long-variable weights.  The
paper does not introduce symbols \(c_{d,p}\) and \(e_{d,q}\) in this display;
those symbols are a valid derived collapse only after the following exact
change of variables.

## Canonical allocation

Define

\[
\begin{aligned}
 d_1&=\gcd(A_0,d),&d_2&=d/d_1,&
 a&=A_0/d_1,&m&=M_0/d_2,\\
 d_3&=\gcd(B_0,d),&d_4&=d/d_3,&
 b&=B_0/d_3,&n&=N_0/d_4.
\end{aligned}
\]

Then

\[
 d_1d_2=d_3d_4=d,\qquad
 (a,d_2)=(b,d_4)=1,qquad (am,bn)=1.
\]

Conversely, these three coprimality conditions and the two divisor splits
recover

\[
 A_0=d_1a,\quad M_0=d_2m,\quad B_0=d_3b,\quad N_0=d_4n
\]

with \(\gcd(A_0M_0,B_0N_0)=d\).  In particular the allocation has
multiplicity one.  The conditions \((a,d_2)=1\) and \((b,d_4)=1\) are not
optional bookkeeping: they are what recover \(d_1=\gcd(A_0,d)\) and
\(d_3=\gcd(B_0,d)\).

`RH/Zeta85/Discharge/BBLRGCDAllocation.lean` proves this as the equivalence

```text
allocationEquiv d hd : DivisiblePair d ≃ SplitPair d
```

and proves both the forward reduced-product coprimality and the converse gcd
identity in `allocated_reduced_products_coprime` and
`gcd_merged_products`.

## Exact collapsed coefficients

Put \(p=am\) and \(q=bn\).  The source-matched one-side coefficients are

\[
 c_{d,p}=
 \sum_{d_1d_2=d}\ \sum_{\substack{am=p\\(a,d_2)=1}}
 \alpha_{d_1a}W_1(d_2m/M_1),
\]

\[
 e_{d,q}=
 \sum_{d_3d_4=d}\ \sum_{\substack{bn=q\\(b,d_4)=1}}
 \beta_{d_3b}W_3(d_4n/N_1).
\]

The Lean definition `collapsedCoeff alpha smooth d p` is this formula with
`smooth k` standing for the evaluated smooth weight.  For positive \(d,p\),
`collapsedCoeff_eq_divisorSum` proves the exact finite identity

\[
 c_{d,p}=
 \sum_{A_0M_0=dp}\alpha_{A_0}\,\mathrm{smooth}(M_0).
\]

The proof uses an explicit finite-sum bijection, so this statement includes
the multiplicities rather than merely comparing supports.

The claimed block scales also follow without an extra allocation choice.  If
\(\alpha_{d_1a}\) is supported on \(d_1a\asymp A\) and
\(W_1(d_2m/M_1)\) on \(d_2m\asymp M_1\), then
\(p=am\asymp AM_1/(d_1d_2)=AM_1/d\).  Likewise
\(q\asymp BN_1/d\).  These conclusions retain the actual smooth weights;
they do not replace them by endpoint indicators.

At fixed \(d,h,\ell,x\), the remaining kernel is exactly

\[
 K_{d,h,\ell,x}(p,q)=W_0(dh/H)
 e\!\left(\mp\ell h\frac{\bar p}{q}\right)
 W_2(qx/M_2)W_4(px/N_2)e(\ell x).
\]

For explicit finite positive ranges \(P,Q\),
`collapsedKernelSum_eq_originalFibers` proves that the collapsed sum

\[
 \sum_{p\in P}\sum_{\substack{q\in Q\\(p,q)=1}}
 c_{d,p}e_{d,q}K(p,q)
\]

equals the sum over the original factor pairs
\(A_0M_0=dp\), \(B_0N_0=dq\), with the literal condition
\(\gcd(A_0M_0,B_0N_0)=d\).  The proof uses

\[
 \gcd(dp,dq)=d\gcd(p,q).
\]

Thus the combinatorial source map through \(p,q\), including every smooth
weight displayed above, is complete.

## Correction to the previous HB candidate

`HBDepthFour.splitCoeff` sums over \(d_1d_2=d\) and \(am=p\) but omits
\((a,d_2)=1\).  It is therefore not the BBLR coefficient.  The formal
regression at \(d=p=2\), with unit weights, is

```text
collapsedCoeff_two_two_unit    : collapsedCoeff ... 2 2 = 3
rawCollapsedCoeff_two_two_unit : rawCollapsedCoeff ... 2 2 = 4
```

The four raw representations merge to

\[
 (1,4),(2,2),(2,2),(4,1),
\]

whereas the canonical filter keeps each of the three original factor pairs
once.  The independent check is `verify/bblr_gcd_allocation.py`, with committed
output in `verify/bblr_gcd_allocation.out`.

## Exact remaining boundary

This correction does not identify the arbitrary grouping in
`HBDepthFour.lean` with BBLR's inputs.  BBLR Proposition 3.1 accepts arbitrary
coefficients only on its outer variables \(A_0,B_0\); its inner variables
carry the smooth weights \(W_1,W_3\).  A source-matched depth-four use still
requires all of the following:

1. a cutoff and dyadic partition reconstructing each relevant
   Heath--Brown summand;
2. an explicit grouping proving that the grouped irregular coefficients are
   precisely the BBLR sequences \(\alpha,\beta\), while the residual
   \(M_0,N_0\) factors are precisely smooth BBLR variables;
3. the full recombination of the resulting zero frequencies with the
   singular-series subtraction; and
4. any Mellin separation or decay estimate required after the exact kernel
   above is integrated in \(x\).

No theorem in this milestone supplies those analytic or grouping statements.
Consequently the corrected `collapsedCoeff` may be called the source BBLR
collapse for supplied sequences, but neither it nor `HBDepthFour.splitCoeff`
may yet be called the actual recombined Heath--Brown coefficient of cycle 5.

## Validation

```sh
lake build RH.Zeta85.Discharge.BBLRGCDAllocation
lake env lean comparator/PrintAxioms/BBLRGCDAllocation.lean
python3 verify/bblr_gcd_allocation.py
diff -u verify/bblr_gcd_allocation.out <(python3 verify/bblr_gcd_allocation.py)
```

The module contains no declared assumption and no proof placeholder.
