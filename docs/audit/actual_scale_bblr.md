> **Canonical reference**: [FINDINGS.md](../../FINDINGS.md) (BBLR error correction). See also [GUIDE.md](../../GUIDE.md) topic index.

# Actual-scale BBLR exponent audit

Status: **both the Proposition 3.1 black-box class and the run-12
progression majorant applied after equation (14) fail by fixed powers on the
exact `(2/5,3/5)` block; cancellation before the progression majorant
remains open**.

## Scope and primary source

The block audited here is the symmetric two-sided block left by the literal
Heath--Brown component in
`docs/audit/hb_to_bblr_smooth_grouping.md`:

\[
 A=B=H=T^{43/100},\qquad
 M_1=N_1=T^{2/5},\qquad
 M_2=N_2=T^{3/5}.                                      \tag{1}
\]

Thus each side has exponent

\[
 \frac{43}{100}+\frac25+\frac35=\frac{143}{100},       \tag{2}
\]

and \(M_1\le M_2\), \(N_1\le N_2\).  Moreover

\[
 H=(AB)^{1/2},                                          \tag{3}
\]

so the shift is exactly at the power boundary of the strengthened error's
range \(H\ll(AB)^{1/2+\varepsilon}\).

The primary source checked is S. Bettin, H. M. Bui, X. Li, and
M. Radziwill, *A quadratic divisor problem and moments of the Riemann
zeta-function*, [arXiv:1609.02539](https://arxiv.org/pdf/1609.02539),
Proposition 3.1 and equation (14) in its proof.  Proposition 3.1 gives

\[
 E\ll_\varepsilon
 (ABMNH^2)^{1/4+\varepsilon}
 \left(
   AB+H^{1/4}(A+B)^{1/2}(ABMN)^{1/8}
 \right),                                               \tag{4}
\]

where \(M=M_1M_2\) and \(N=N_1N_2\).  In equation (14), after
\(d=(am_1,bn_1)\), the nonzero Poisson phase has reduced numerator and
modulus lengths

\[
 P_d\asymp \frac{AM_1}{d},\qquad
 Q_d\asymp \frac{BN_1}{d}.                              \tag{5}
\]

The exact canonical allocation behind (5), including its multiplicity, is
proved in `BBLRGCDAllocation.lean`.  The later estimate
\(P_d(Q_d+H_d)\) is not a statement of Proposition 3.1; it is the explicit
progression-majorant route applied to the nonzero-frequency family of
equation (14), with \(H_d=H/d\).  These two method classes must therefore be
audited separately.

All conclusions below are power-exponent conclusions.  They grant, rather
than prove, every coefficient, smoothness, zero-frequency, and recombination
hypothesis needed to reach the displayed analytic bounds.

## 1. Proposition 3.1 as a black box

At (1), the exponent of \(ABMN\) is

\[
 2\frac{43}{100}
 +2\left(\frac25+\frac35\right)
 =\frac{143}{50}.                                       \tag{6}
\]

Consequently the outside factor in (4), before its nonnegative
\(\varepsilon\)-loss, has exponent

\[
 \frac14\left(\frac{143}{50}+2\frac{43}{100}\right)
 =\frac{93}{100}.                                       \tag{7}
\]

The corrected first term in (4) is \(AB\), not \((AB)^{1/2}\).  It therefore
gives

\[
 E_{AB}:\quad
 \frac{93}{100}+2\frac{43}{100}
 =\frac{179}{100},                                      \tag{8}
\]

which exceeds the trace exponent \(143/100\) by

\[
 \frac{179}{100}-\frac{143}{100}=\frac9{25}.             \tag{9}
\]

For the second term, the fixed factor \(2\) in
\(A+B=2T^{43/100}\) does not change its power exponent.  Its exponent inside
the parentheses is

\[
 \frac14\frac{43}{100}
 +\frac12\frac{43}{100}
 +\frac18\frac{143}{50}
 =\frac{17}{25}.                                        \tag{10}
\]

Thus

\[
 E_{\mathrm W}:\quad
 \frac{93}{100}+\frac{17}{25}
 =\frac{161}{100},                                      \tag{11}
\]

exceeding trace by

\[
 \frac{161}{100}-\frac{143}{100}=\frac9{50}.            \tag{12}
\]

The \(\varepsilon\) in the exponent of (4) adds a nonnegative power slack;
it cannot reverse either strict inequality.

Define the **actual-scale Proposition 3.1 black-box class** to apply (4) to
this dyadic block and to use its displayed positive error terms separately,
without cancellation between blocks or before the proposition.  Equations
(9) and (12) finish and kill this exact class.  They do not assert that the
original signed error is at least either power.

## 2. Equation (14) followed by the progression majorant

At \(d=1\), equation (5) and (1) give

\[
 P=T^{43/100+2/5}=T^{83/100},\qquad
 Q=T^{43/100+2/5}=T^{83/100}.                            \tag{13}
\]

There is a source-level cancellation which must be accounted for before
using these lengths.  The Fourier integral in equation (14) has physical
scale

\[
 x\asymp \frac{M_2}{BN_1}
   \asymp \frac{N_2}{AM_1}
   =T^{-23/100}.                                         \tag{14}
\]

On this block, however, the paper's integration-by-parts cutoff is

\[
 L\asymp \frac{AM}{M_2N_2}=T^{23/100},                  \tag{15}
\]

with the proposition's \(T^\varepsilon\) slack suppressed.  Hence the
\(T^{-23/100}\) size of each low-frequency Fourier integral is accompanied
by \(T^{23/100}\) nonzero frequencies.  Their net power is zero.  Retaining
the decay envelope

\[
 T^{-23/100}
 \left(1+|\ell|T^{-23/100}\right)^{-J}
\]

instead of summing a sharp cutoff gives the same conclusion.  Thus the
physical scale does not supply an extra \(T^{-23/100}\) after the
nonzero-frequency sum.

The two contributions to the run-12 progression majorant \(P(Q+H)\),
applied after equation (14), therefore have exponents

\[
 \operatorname{exp}(PQ)=\frac{83}{50},\qquad
 \operatorname{exp}(PH)=\frac{63}{50}.                  \tag{16}
\]

They compare with trace as

\[
 \frac{83}{50}-\frac{143}{100}=\frac{23}{100},\qquad
 \frac{143}{100}-\frac{63}{50}=\frac{17}{100}.          \tag{17}
\]

Thus the obstruction is exactly the \(PQ\) part: because \(Q>H\) on the
power scale, \(P(Q+H)\) has exponent \(83/50\), missing trace by
\(23/100\).  This failure is present with logarithmic exponent \(C=0\); log
accounting cannot repair a fixed positive power excess.  The preliminary
zero-shift Taylor error \(H^2\) is harmless here, lying below trace by

\[
 \frac{143}{100}-2\frac{43}{100}=\frac{57}{100}.         \tag{18}
\]

Define the **actual-scale run-12 equation-(14) progression-majorant class**
to start from equation (14), use the exact gcd allocation, replace the
reduced progression family by the absolute/progression estimate
\(P_d(Q_d+H_d)\), and require that estimate to be trace-grade block by block.
Its \(d=1\) member already fails by (17), so this exact class is finished and
killed.

This is a failure of the available upper-bound mechanism, not a lower bound
for the signed Poisson remainder.  In particular, it does not rule out an
estimate that retains simultaneous cancellation in \(p,q,h,\ell\), signed
recombination across smooth blocks, or a higher-dimensional treatment before
the residue/progression absolute values are taken.

## Formal and independent checks

`RH/Zeta85/Discharge/ActualScaleBBLR.lean` proves:

- the exact block geometry and the Proposition 3.1 range boundary;
- the four black-box exponents in (7)--(12), including arbitrary
  nonnegative power slack;
- the exact \(d=1\) lengths in (13), both terms in (16), and the dominant
  maximum;
- the exact Fourier physical scale and frequency-count cancellation in
  (14)--(15);
- the excesses and savings in (17)--(18).

The formal statements declare no premise and contain no proof placeholder.
Their dependency printer reports only `[propext, Classical.choice,
Quot.sound]`.

```sh
lake build RH.Zeta85.Discharge.ActualScaleBBLR
lake env lean comparator/PrintAxioms/ActualScaleBBLR.lean
python3 verify/a1_actual_scale_bblr.py
diff -u verify/a1_actual_scale_bblr.out \
  <(python3 verify/a1_actual_scale_bblr.py)
```

The independent verifier uses exact `fractions.Fraction` arithmetic and
commits its complete output.
