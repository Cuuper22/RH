> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Zeta-100 arithmetic, cycle 1: the Type-III hole in one-shot BP grouping

## 0. Terminal output

This cycle takes the permitted **method-class kill plus first outside
calculation** branch.  It does not claim a support extension.

At the proposed first supercritical point

\[
 \sigma=2.001,\qquad \eta=1.001,\qquad
 H=T^{\eta},\qquad L=H/T=H^\rho,
 \qquad \rho={1\over1001},                                  \tag{1}
\]

the terminal resonance from the accepted support-two argument asks for a
saving of precisely

\[
                         L=H^{1/1001}.                       \tag{2}
\]

The balanced Blomer--Pascadi saving would be much larger than (2): at
square-root length it is \(H^{-1/32+o(1)}\).  However, a complete
Heath--Brown expansion contains an honest Type-III block with three smooth
factors of length \(H^{1/3}\) on each side.  For the terminal modulus
\(c\asymp H\), every one-shot multiplicative grouping of this block has
length exponent \(1/3\) or \(2/3\).  Substitution in the *full unbalanced*
Blomer--Pascadi bound gives no saving in any of the four possible pairings;
the best quoted bound is actually worse than the appropriate elementary
bound.  Thus the factor-grouping step cannot be completed for every block.

This proves a precise impossibility theorem for the one-shot BP grouping
class defined in Section 3.  In particular, it prevents the attractive but
false inference

\[
 {1\over32}>{1\over1001}\quad\Longrightarrow\quad
 \hbox{support }2.001.                                      \tag{3}
\]

The mandatory first calculation outside that class is completed in
Section 4.  Keeping the three factors separate through the MD moment shows
that the full product diagonal of the Type-III block is only

\[
 \boxed{H^{1+\rho+o(1)}},                                   \tag{4}
\]

whereas the admissible MD budget is

\[
 \boxed{H^{2-\rho+o(1)}}.                                   \tag{5}
\]

Thus the diagonal is below budget by the fixed power

\[
 H^{-1+2\rho}=H^{-999/1001}.                                \tag{6}
\]

This is a concrete coefficient-sensitive reduction: the Type-III problem is
not caused by multiplicative coincidences or by the zero mode.  It lies
entirely in the off-diagonal determinant strata, which must be attacked
before collapsing the three factors.

The unconditional arithmetic endpoint therefore remains

\[
                         \boxed{\sigma<2}.                    \tag{7}
\]

With the accepted capped-outer quartic certificate, the rigorous floor
remains

\[
 \boxed{\displaystyle
 \liminf_{T\to\infty}{N_{0,\mathrm{simple}}(T)\over N(T)}
 >0.96250068026-o(1).}                                      \tag{8}
\]

For scale only: if (7) had extended to \(2.001\), the same fixed profile and
\(D_{2.001}=1.0676345525547115\ldots\) would have produced
\(0.96261844035\ldots\).  That number is **not claimed**.

## 1. The accepted terminal object at the tiny extension

The accepted support-two construction reduces the first supercritical
remainder to

\[
 R_{\rm res}=T\sum_{0<|r|,|k|\le(\log T)^B}
 \sum_{\ell\asymp L}\omega_{r,k}(\ell/L)
 \sum_{rp-kq=\ell}c_p e_qV_{r,k}(p/H,q/H)
 +O_A(X\log^{-A}T),                                        \tag{9}
\]

where \(p,q\asymp H\), and \(c_p,e_q\) are the actual unrecombined finite
Heath--Brown coefficients.  Trace grade is equivalent to

\[
 \mathcal S_{r,k}:=
 \sum_{\ell\asymp L}\omega_{r,k}(\ell/L)
 \sum_{rp-kq=\ell}c_pe_qV_{r,k}(p/H,q/H)
 \ll H(\log H)^C.                                         \tag{10}
\]

The termwise estimate is \(HLH^{o(1)}\); hence (10) asks for exactly (2).
Equivalently, after one Cauchy step, it is enough to prove

\[
 \sum_{\ell\asymp L}|E_{r,k}(\ell)|^2
 \ll {H^2\over L}H^{o(1)}=H^{2-\rho+o(1)},                 \tag{11}
\]

after removing the accepted zero mode.

## 2. Exact substitution in the unbalanced BP theorem

Write \(M=H^m,N=H^n,c\asymp H\).  Theorem 5.5 of
[Blomer--Pascadi](https://arxiv.org/abs/2607.24311) bounds the bilinear
Kloosterman form by

\[
 \|\alpha\|_2\|\beta\|_2c^{1+o(1)}\mathcal H(M,N,c).       \tag{12}
\]

For exponent bookkeeping, the five terms of \(\mathcal H\) have powers

\[
\begin{aligned}
e_1={}&{m\over8}+{\max(1,m+n)\over16}
 +{\max(1,2n)\over16}-{1\over4}
 +{\min(1-m,1/2)\over16},\\
e_2={}&{1\over16}\max\{2n-2,\ n/2+m+\max(1,2n)-5/2\},\\
e_3={}&\max(m/3-1/5,n/3-1/5),\\
e_4={}&\max(m/2+n/6,m/6+n/2)-7/18,\\
e_5={}&\max(m,n)/15-1/15.                                  \tag{13}
\end{aligned}
\]

Thus (12) has factor \(H^{1+\max e_i+o(1)}\).  On the desired
near-balanced line \(m+n=1\), choosing \(0.405\le m,n\le0.595\) would save
at least \(H^{-1/600+o(1)}\), comfortably more than \(H^{-1/1001}\).
This is the valid part of the proposed route.

The problem is that not every HB block admits such a grouping.

## 3. The all-smooth Type-III counterblock

Use a finite Heath--Brown identity of depth at least three.  Its \(j=3\)
piece contains

\[
 C_3(p)=
 \sum_{a_1a_2a_3d_1d_2d_3=p\atop a_i\le V}
 \mu(a_1)\mu(a_2)\mu(a_3)\log d_1.                         \tag{14}
\]

Take the nonempty dyadic subblock

\[
 a_1,a_2,a_3\asymp1,qquad
 d_1,d_2,d_3\asymp P,qquad P=H^{1/3},                     \tag{15}
\]

and the analogous block on the \(q\)-side.  Constants and the logarithm are
absorbed into smooth weights.  This is a legitimate term of the exact
identity, not an artificial arbitrary coefficient.

Define the **one-shot BP grouping class** \(\mathscr C_{\rm BP,1}\) to
consist of arguments which:

1. expand each von Mangoldt coefficient by a fixed-depth HB identity and
   dyadically localize;
2. close a Type-I block only by completing one individual unrestricted
   smooth factor longer than \(H^{1/2+o(1)}\);
3. otherwise partition the multiplicative factors on each side into two
   groups, collapse each group to an arbitrary divisor-bounded sequence,
   and use at most one fixed-modulus BP bilinear estimate with
   \(c\asymp H\);
4. bound the remaining variables by \(L^2\) norms, divisor bounds, and
   triangle inequality.

The block (15) is not Type I: no individual unrestricted factor is longer
than \(H^{1/2}\).  Every nontrivial two-group partition has exponent pair
\((1/3,2/3)\).  Allowing the BP variables to be chosen from either side gives
only

\[
 (m,n)\in\{(1/3,1/3),(1/3,2/3),(2/3,1/3),(2/3,2/3)\}.     \tag{16}
\]

Substitution in (13) is exact:

\[
\begin{array}{c|c|c|c}
(m,n)&\max_i e_i&\text{BP factor exponent}&
 \text{elementary factor exponent}\\ \hline
(1/3,1/3)&-2/45&43/45&5/6\\
(1/3,2/3)& 1/45&46/45&1\\
(2/3,1/3)& 1/45&46/45&1\\
(2/3,2/3)& 1/18&19/18&1
\end{array}                                                  \tag{17}
\]

Here the last column is

\[
 \min\{1,(m+n+1)/2\},                                      \tag{18}
\]

coming from the elementary complete/Fourier and Weil bounds.  In every row
the BP estimate is weaker.  In particular, it cannot supply even
\(H^{-\varepsilon}\), let alone (2).

Consequently:

> **Type-III one-shot barrier.**  No argument in
> \(\mathscr C_{\rm BP,1}\) proves (10) for any fixed \(\rho>0\).  The
> obstruction is already the explicit dyadic \(j=j'=3\) block (15).

This theorem is deliberately about the stated method class, not about
support \(>2\).  Recombining HB pieces before triangle inequality, retaining
three factors through a higher moment, or using a genuine multilinear
Kloosterman theorem lies outside the class.

## 4. First calculation outside the class: retain the Type-III diagonal

For the block (15), let

\[
 r_3(n)=\sum_{d_1d_2d_3=n\atop d_i\asymp P}
          u_1(d_1)u_2(d_2)u_3(d_3),                         \tag{19}
\]

with fixed smooth weights and one logarithmic derivative allowed.  The
divisor bound gives, uniformly for \(n\asymp H\),

\[
                         |r_3(n)|\ll H^{o(1)}.               \tag{20}
\]

Retain these coefficients in (11), rather than replacing them by arbitrary
sequences.  On expanding the second moment, the full product diagonal is

\[
 p_1=p_2,qquad q_1=q_2.                                    \tag{21}
\]

The shift condition restricts it to

\[
 |rp-kq|\ll L,qquad p,q\asymp H.                           \tag{22}
\]

For every \(p\), (22) leaves \(O(L+1)\) integers \(q\), uniformly for the
polylogarithmic \(r,k\) in (9).  Equations (20)--(22) therefore give the
unconditional bound

\[
\begin{aligned}
 \mathcal D_{\rm III}
 &\ll H^{o(1)}
   \#\{p,q\asymp H:|rp-kq|\ll L\}\\
 &\ll H(L+1)H^{o(1)}
  =H^{1+\rho+o(1)}.                                        \tag{23}
\end{aligned}
\]

Comparing (23) with (11) gives

\[
 {\mathcal D_{\rm III}\over H^2/L}
 \ll H^{-1+2\rho+o(1)}
 =H^{-999/1001+o(1)},                                      \tag{24}
\]

which proves (4)--(6).  The same estimate covers all exact multiplicative
coincidences, because

\[
 \sum_n\left|\sum_{uv=n}\alpha_u\beta_v\right|^2
 \le \max_{n\ll H}\tau(n)\,\|\alpha\|_2^2\|\beta\|_2^2
 =H^{o(1)}\|\alpha\|_2^2\|\beta\|_2^2.                    \tag{25}
\]

Equation (25) is the first useful structural fact discarded by arbitrary
coefficient collapse.  It removes the product diagonal with almost a full
power of \(H\) to spare.  The constructive continuation is therefore forced
to keep at least the three \(H^{1/3}\) factors through the first completion
and spend its cancellation only on the off-diagonal determinant strata;
another one-shot regrouping cannot help by (17).

## 5. Handoff

* Required supercritical saving at \(\sigma=2.001\): \(H^{-1/1001}\).
* Near-balanced BP blocks would save at least \(H^{-1/600}\).
* Exact survivor: the legitimate all-smooth \(j=j'=3\) HB block with factor
  exponents \((1/3,1/3,1/3)\).
* Rigorous kill: every one-shot grouping of that block falls in (16), and
  the full BP formula is non-saving in all four cases.
* First attack outside the killed class is complete: its entire product
  diagonal is \(H^{1+\rho+o(1)}\), below the MD allowance by
  \(H^{-999/1001+o(1)}\).
* No support extension is claimed; the accepted strict percentage remains
  \(0.96250068026-o(1)\).