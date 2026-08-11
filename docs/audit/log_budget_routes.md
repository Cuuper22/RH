# Cycle-5 logarithmic budget: ordered route audit

## Outcome

The cycle-5 hole remains open.  The accounting can be sharpened, but none of
the four prescribed routes supplies the missing estimate from the stated
premises.

The corrected accounting has three distinct models:

| model | trace contribution from \(E_Y\ll Y(\log T)^C\) | closes when |
|---|---:|---:|
| globally recombined | \(T(\log T)^{C+1}\) | \(C<2\) |
| literal dyadic \(Y\)-sum | \(T(\log T)^{C+2}\) | \(C<1\) |
| separately dyadicized \(Y\) and \(h\), both triangle-summed | \(T(\log T)^{C+3}\) | \(C<0\) |

The middle line is the literal reading of
`docs/run/02_certificate_cycle2.md` (14): its outer sum is over dyadic
\(Y\), but its inner sum is directly over \(h\).  The last line is a valid
fully adversarial overdecomposition, not a forced reading of that formula.
All three dichotomies are proved in
`RH/Zeta85/Discharge/LogBudget.lean`.

At the 85-percent exponent the depth condition still gives \(K\ge4\), and
the run's divisor-majorant accounting gives \(C\ge K-1\ge3\).  Hence this
correction does not close the budget.

## Route 1: adjudicate generous versus dyadic accounting

On \(n\asymp Y\) and \(h\asymp H_Y=Y/T\), equation (10) of certificate
cycle 2 gives

\[
 |\mathcal W_{Y,h}(n)|
 \ll \frac{TL}{Y}+\frac{\log L}{Y}.
\tag{1}
\]

An already \(h\)-summed error \(E_Y\) therefore contributes

\[
 \frac{TL}{Y}E_Y.
\tag{2}
\]

For \(E_Y\ll Y(\log T)^C\), (2) is
\(T(\log T)^{C+1}\).  Summing the \(O(\log X)\) displayed dyadic
\(Y\)-blocks by triangle inequality gives
\(T(\log T)^{C+2}\).  There is no displayed dyadic \(h\)-sum in (14), so
charging another factor there is an additional proof choice.

The exact transfer condition is \(M_{\rm err}=o(TL^3)\).  The condition
`(AS)`, which asks for \(Y(\log Y)^{-A}\) for every \(A\), is a convenient
strictly stronger sufficient statement.  Thus the comparison “positive log
loss versus `(AS)`” explains why the current Lean predicate is not
discharged, but it is not an independent proof that every positive \(C\)
misses the trace budget.

**Route-1 verdict:** the correct forced blockwise threshold is \(C<1\),
between the previously recorded \(C<2\) and \(C<0\) readings.  The
\(C\ge3\) obstruction survives.

## Route 2: retain signs across scales

### Shift scales

The second triangle loss is avoidable at the level of the \(h\)-weights.
Join the two orientations \(h>0\) and \(h<0\), insert the \(h=0\) term, and
subtract that diagonal term separately.  The remaining dyadic partition then
recombines to one smooth compactly supported weight

\[
 W_H(h)=W(h/H),\qquad h\in\mathbb Z.
\tag{3}
\]

There is no boundary at \(h=0\) in the bilateral sum.  Repeated summation by
parts therefore applies directly to (3) and gives

\[
 \left|\sum_{h\in\mathbb Z}W(h/H)e(h\theta)\right|
 \ll_J H(1+H\lVert\theta\rVert)^{-J}.
\tag{4}
\]

This is the same construction as the proved signed-shift lemma, with the
diagonal isolated instead of forcing every component to live on \((1,2)\).
It prevents a separate factor \(\log T\) from the \(h\)-scale partition.

### Prime scales

No corresponding cancellation follows across the dyadic prime blocks.
At the natural shift \(h\asymp Y/T\),

\[
 T\log(1+h/n)=\frac{Th}{n}+O(T^{-1})\asymp1,
\tag{5}
\]

uniformly on every \(n\asymp Y\) block.  The phase therefore does not
oscillate as a function of the dyadic scale \(Y\).  Error terms on different
\(Y\)-blocks can have the same sign and phase while satisfying every
per-block estimate used in cycle 5.  A nonnegative partition of unity cannot
create cancellation between them.

Removing this last logarithm would require a genuinely global estimate such
as

\[
 \left|\sum_{Y\ \mathrm{dyadic}}
       \frac{T}{Y}E_Y\right|
 \ll T(\log T)^C
\tag{6}
\]

with the sum taken before absolute values.  Neither the Shiu majorant nor the
per-block Poisson estimate implies (6); both take absolute values inside the
\(Y\)-sum.

**Route-2 verdict:** the optional shift-scale logarithm can be removed, but
the prime-scale logarithm cannot be removed from the available hypotheses.
The remaining threshold is \(C<1\).

## Route 3: reduce Heath--Brown depth

At \(\eta=43/100\), the raw depth-\(K\) atom has exponent

\[
 \frac{1+\eta}{K}.
\tag{7}
\]

Depth three is too long by the exact amount

\[
 \frac{143}{300}-\frac{43}{100}=\frac7{150}>0,
\tag{8}
\]

whereas depth four is shorter than the shift scale by

\[
 \frac{43}{100}-\frac{143}{400}=\frac{29}{400}>0.
\tag{9}
\]

These equalities are formalized as `depth_three_excess` and
`depth_four_margin`.  Thus depth four is the first possible integer depth for
the grouping rule used in cycles 4--5.  Under the run's own relation
\(C\ge K-1\), lowering the logarithmic exponent below two by lowering
\(K\) is impossible.

An alternative identity could only help by decoupling logarithmic complexity
from atom depth.  No Vaughan/Heath--Brown decomposition with all terminal
atoms at most \(T^{43/100}\), the same BBLR block geometry, and an explicitly
constructed progression majorant with \(C<1\) is present in either run.

**Route-3 verdict:** the existing identity cannot be shaved.  A replacement
identity must be supplied with its complete terminal-block construction; an
unspecified “lower-depth” identity is not enough.

## Route 4: Weil-grade power injection

Any fixed power saving would absorb all fixed logarithmic losses.  The place
to inject it is the leading \(P_dQ_d\) term in cycle 5, equation (18), which
is exactly at the natural scale

\[
 P_dQ_d\asymp T^{1+\eta}d^{-2}.
\tag{10}
\]

Before the coefficient \(p\) is collapsed, its relevant scales are

\[
 p=am,\qquad a\asymp H=T^\eta,\qquad
 m\asymp q\asymp Q=T^{1/2}.
\tag{11}
\]

There is an important failed shortcut.  Expand the signed transform back
into its \(h\)-sum and, for each fixed \((a,h,q)\), complete \(m\) modulo
\(q\).  Even granting a square-root Weil bound \(q^{1/2}\) for every
resulting complete inverse sum, absolute summation over
\(a\asymp H\), \(h\asymp H\), and \(q\asymp Q\) gives

\[
 H^2Q^{3/2}=T^{2\eta+3/4}.
\tag{12}
\]

At \(\eta=43/100\), this is worse than the natural scale
\(HQ^2=T^{1+\eta}\) by

\[
 \left(2\eta+\frac34\right)-(1+\eta)
 =\eta-\frac14=\frac9{50}.
\tag{13}
\]

The last equality is formalized as `fixed_modulus_weil_excess`.  Thus a
fixed-modulus Weil estimate followed by triangle inequality is not a power
injection in this range.

The actual sufficient target has to retain cancellation in more than one of
the remaining variables.  Write the factorized fixed-modulus block as

\[
 \mathcal R_{q,\ell}
 =\sum_{a\asymp H}\alpha_a
   \sum_{m\asymp Q}\beta_m F_{q,\ell}(a,m)
   S_H\!\left(\ell\overline{am}/q\right).
\tag{14}
\]

After restoring the summable \(d\)- and \(\ell\)-weights from cycle 5, the
following coefficient-sensitive average would be sufficient for any fixed
\(\delta>0\):

\[
 \boxed{
  \sum_{q\asymp Q}|\mathcal R_{q,\ell}|
  \ll H Q^2 T^{-\delta}(\log T)^{O(1)}.}
\tag{WG-HB}
\]

Indeed, `(WG-HB)` replaces the leading \(T^{1+\eta}\) term by
\(T^{1+\eta-\delta}(\log T)^{O(1)}\), and the proved theorem
`power_beats_log` then absorbs every fixed logarithmic loss.  This is a
sufficient target, not a claimed estimate.  It is deliberately stated for
the actual depth-four coefficients and smooth factor \(F_{q,\ell}\); an
arbitrary divisor-bounded operator norm cannot supply it.

**Route-4 verdict:** the isolated fixed-modulus Weil bound fails by the exact
power \(T^{9/50}\).  The averaged target `(WG-HB)` would close the hole, but
it is not supplied by the current Shiu or BBLR inputs.  Proving it requires
simultaneous cancellation in the retained Möbius factorization and the
\(h\)- or \(q\)-average; it cannot be obtained by completing one variable
and summing the rest absolutely.

## Route 5: evaluate the progression sums instead of bounding them

This route asks whether the \((\log T)^{K-1}\) in the Shiu majorant can be
removed by evaluating the depth-four progression sums, then cancelling their
main terms against the singular-series subtraction already present in the
signed aggregate.

At the cycle-5 endpoint \(\eta=43/100\), suppressing the summable \(d\)- and
\(\ell\)-weights, the exact scales are

\[
 P=T^{93/100},\qquad Q=T^{1/2},\qquad H=T^{43/100},
 \qquad P=HQ,
\tag{15}
\]

so \(Q=P^{50/93}\) and \(\log P/\log Q=93/50\).  After a progression main
term has been subtracted, a literal \(C=0\) estimate must in particular
control an aggregate of the form

\[
 \boxed{
 \sum_{q\asymp Q} e_q
  \sum_{r\bmod q}^{*}
  S_H(\ell\bar r/q)E_c(P;q,r)
  \ll PQ.}
\tag{EDB}
\]

Here \(c\) and \(e\) are the actual signed, smoothly truncated
Möbius/Heath--Brown convolutions and \(E_c\) is their *centred* progression
sum.  In addition to `(EDB)`, the route needs a pointwise identity matching
the main terms of every signed Heath--Brown block and gcd splitting with the
prime-pair singular-series subtraction.  Neither requirement may be replaced
by the corresponding statement for the nonnegative majorant \(d_4\).

### The available published mean values

Nguyen's Theorem 3 states, for \(k\geq4\),

\[
 \sum_{d\leq D}\sum_{(a,d)=1}
 |\Delta(\tau_k;X,d,a)|^2
 \ll
 \left(D+X^{1-1/(6(k+2))}\right)
 X(\log X)^{k^2-1}.
\tag{16}
\]

See [Nguyen, *Generalized divisor functions in arithmetic progressions: I*,
Theorem 3](https://arxiv.org/pdf/2308.06839).  At \(k=4\) this contains the
term \(P^{35/36}P(\log P)^{15}\).

For prime \(q\leq x^{4/7}\), Parry's Theorems 1--2 give, in his additive
notation,

\[
 \sum_{a=1}^{q}|\Delta(a/q)|^2
 \ll x^{3/2+\varepsilon}q^{7/8},
 \qquad
 \sum_{a=1}^{q}|E_x(q,a)|
 \ll x^{3/4+\varepsilon}q^{7/16}.
\tag{17}
\]

See [Parry, *The distribution of \(d_4(n)\) in arithmetic progressions*,
Theorems 1--2](https://arxiv.org/pdf/2404.04749).  The range includes the
needed exponent because \(4/7-50/93=22/651>0\).

Wei--Xue--Zhang's fixed-residue theorem for appropriately smooth squarefree
moduli stops at exponent \(293/584\); it misses the required modulus exponent
by

\[
 \frac{50}{93}-\frac{293}{584}=\frac{1951}{54312}>0.
\tag{18}
\]

See [Wei--Xue--Zhang, *General divisor functions in arithmetic progressions
to large moduli*, Theorem 1](https://arxiv.org/pdf/1512.01470).  The
unconditional range in Rodgers--Soundararajan's Theorem 1 is
\(\log X/\log Q\leq(k+2)/k-\delta\), hence below \(3/2\) for \(k=4\), while
the required ratio is \(93/50\).  Their extension to this ratio assumes GRH.
See [Rodgers--Soundararajan, *The variance of divisor sums in arithmetic
progressions*, Theorem 1](https://arxiv.org/pdf/1610.06900).

### Exact loss after the necessary norm bounds

If \((\ell,q)=1\), \(H<q\), and \(w\) is supported on an interval of length
\(H\) with \(|w|\leq1\), discrete Parseval gives the explicit construction

\[
\begin{aligned}
 \sum_{r\bmod q}^{*}|S_H(\ell\bar r/q)|^2
 &\leq \sum_{a\bmod q}|S_H(a/q)|^2\\
 &=q\sum_{h_1\equiv h_2\pmod q}
     w(h_1/H)\overline{w(h_2/H)}\\
 &=q\sum_h|w(h/H)|^2
 \leq q(\lceil H\rceil+1).
\end{aligned}
\tag{19}
\]

The third line uses the support length \(<q\), so congruent supported
integers are equal.  Combining (16) and (19) by Cauchy, even after replacing
the actual coefficients by \(d_4\), setting \(e_q=1\), and granting all
needed smooth uniformity, produces

\[
 QH^{1/2}P^{71/72}(\log P)^{15/2}
 =T^{3917/2400}(\log T)^{15/2}.
\tag{20}
\]

This exceeds \(PQ=T^{143/100}\) by
\(T^{97/480}(\log T)^{15/2}\).  Likewise, (17), Parseval, (19), and absolute
summation over \(q\asymp Q\) give

\[
 P^{3/4+\varepsilon}H^{1/2}Q^{23/16}
 =T^{261/160+\varepsilon},
\tag{21}
\]

which exceeds \(PQ\) by \(T^{161/800+\varepsilon}\).  Even a hypothetical
natural-order variance \(\ll QP(\log P)^{15}\) gives exactly
\(PQ(\log P)^{15/2}\) after (19): it has zero power margin and retains a
positive logarithmic loss.

There are also two statement mismatches.  The published results concern
\(d_4\), not the signed truncated coefficients \(c\); pointwise domination
recovers the Shiu loss instead of evaluating \(E_c\).  Parry's main term

\[
 M_x(q,a)=\frac1q\sum_{d\mid q}c_d(a)F_x(d)
\tag{22}
\]

comes from an additive Estermann series for \(d_4\).  No cited result or
in-repository derivation identifies the aggregate of these main terms for
the actual signed blocks with the prime-pair singular-series subtraction.

**Route-5 verdict:** the exact method class “published \(d_4\) progression
mean value, followed by a norm bound in the residue variable and
absolute/Cauchy aggregation in \(q\)” is impossible at (15): it misses by a
fixed power before the coefficient and main-term mismatches are addressed.
This does **not** disprove `(EDB)`.  It proves that `(EDB)` needs a new
estimate correlated with \(S_H(\ell\bar r/q)\), the signs of \(e_q\), or the
simultaneous Heath--Brown factorization.  Those are the cross-\(Y\) and
`(WG-HB)` routes, not a consequence of the cited divisor-progression
theorems.  The exact fractions are independently recomputed by
`verify/a1_1_method_kill.py`, with committed output in
`verify/a1_1_method_kill.out`.

## Program status

The target remains frozen.  The support-\(143/100\) theorem still depends on
`signedPair_traceGrade_lt_3_2`.  The ordered attack narrows the analytic gap
as follows:

1. A constructed per-block estimate with literal exponent \(C=0\) closes
   the budget **by itself**, because it contributes \(T(\log T)^2\), which
   is \(o(T(\log T)^3)\).  No cross-\(Y\) estimate is needed in that case.
   Route 5 kills only the published-\(d_4\)-plus-norm method class for
   obtaining this estimate; `(EDB)` itself remains the exact resisted
   statement.
2. Failing that, prove the cross-\(Y\) signed estimate (6), with all
   logarithmic exponents explicit.
3. Failing that, prove the fixed-power inverse-residue estimate `(WG-HB)`
   for the actual depth-four coefficients.
