# Pre-majorant one-shot DI/Kuznetsov audit

Status: **finished and killed for the direct Drappeau one-shot class defined
in Section 6: its exponent is \(179/100\), exceeding trace by \(9/25\).
The proposed one-variable-completed Pascadi route is
UNRESOLVED-APPLICABILITY: literal completion has the wrong placement of the
outer factor inside the Kloosterman sum. Its \(179/100\) value is conditional
arithmetic only and is excluded from the finish/kill claim.**

This audit uses only two primary, published sources:

- Sary Drappeau, *Sums of Kloosterman sums in arithmetic progressions, and
  the error term in the dispersion method*, Proc. Lond. Math. Soc. 114
  (2017), 684--732, Theorem 2.1
  ([published DOI](https://doi.org/10.1112/plms.12022),
  [author version](https://arxiv.org/pdf/1504.05549)).
- Alexandru Pascadi, *Smooth numbers in arithmetic progressions to large
  moduli*, Compositio Math. 161 (2025), 1923--1974, Theorem 10.3
  ([published DOI](https://doi.org/10.1112/S0010437X2500747X),
  [published PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D8E4EE07BDAA6D41CCD8C5455D81CD7A/S0010437X2500747Xa.pdf/smooth-numbers-in-arithmetic-progressions-to-large-moduli.pdf)).

No later preprint is used.

## 1. Exact source sum and the current formal boundary

The surviving actual-scale block is

\[
 A=B=H=T^{43/100},\qquad
 M_1=N_1=T^{2/5},\qquad M_2=N_2=T^{3/5}.       \tag{1}
\]

At \(d=(am_1,bn_1)=1\), equation (14) of
Bettin--Bui--Li--Radziwiłł has the nonzero-frequency sum

\[
\begin{aligned}
 Z_\pm(x)={}&
 \sum_{\substack{a,b,m_1,n_1,h\\(am_1,bn_1)=1}}
 \sum_{0<|\ell|\le L}
 \alpha_a\beta_b
 W_0(h/H)W_1(m_1/M_1)W_3(n_1/N_1)\\
 &\quad\times
 W_2(bn_1x/M_2)W_4(am_1x/N_2)
 e\!\left(\mp\frac{\ell h\overline{am_1}}{bn_1}\right)e(\ell x),
                                                        \tag{2}
\end{aligned}
\]

where

\[
 L=T^{23/100},\qquad |x|\asymp T^{-23/100}.             \tag{3}
\]

The two signs of \(\ell\) are separated below, and \(n=|\ell|h\) has
exponent

\[
 \frac{23}{100}+\frac{43}{100}=\frac{33}{50}.           \tag{4}
\]

`BBLRGCDAllocation.lean` proves that the source gcd allocation reindexes the
*supplied* outer and smooth sequences with multiplicity one. At \(d=1\), its
variables are exactly \(p=am_1\) and \(q=bn_1\). It does not prove that a
Heath--Brown component equals the candidate smooth BBLR input.
`HBDepthFour.lean` proves the depth-four identity, while
`HBToBBLRSmoothGrouping.lean` records the surviving
\((43/200,43/200,2/5,3/5)\) component. A smooth partition and recombination
identity connecting that component to (2) is still absent. Accordingly,
this audit grants the candidate block (2) and tests only the proposed
published-theorem estimate after it. It does not mark an actual-cycle
coefficient identification as proved.

For the one-shot test, each pair of \(T^{43/200}\) Möbius variables is
collapsed into \(\alpha_a\) or \(\beta_b\), and \((|\ell|,h)\) is collapsed
into the numerator coefficient. The elementary multiplicative-energy
parameterization

\[
 uv=u'v',\quad u=ga,\quad u'=gb,\quad v=bk,\quad v'=ak,
 \quad (a,b)=1                                             \tag{5}
\]

gives, for bounded dyadic weights, one factor \((\log T)^{1/2}\) in each of
the three collapsed \(L^2\) norms. More precisely, if
\(\gamma_n=\sum_{\ell>0,\,\ell h=n}W_0(h/H)e(\pm\ell x)\), the constructed
bounds are

\[
 \|\alpha\|_2,\|\beta\|_2
 \ll T^{43/200}(\log T)^{1/2},\qquad
 \|\gamma\|_2\ll T^{33/100}(\log T)^{1/2}.             \tag{6a}
\]

Their product has power and logarithmic exponents

\[
 \|b_{n,r,s}\|_2
 \ll T^{(33/50+43/100+43/100)/2}(\log T)^{3/2}
 =T^{19/25}(\log T)^{3/2}.                              \tag{6}
\]

If the two original long logarithmic Heath--Brown weights are not divided
by \(\log T\), their two sup-norm factors add exactly \((\log T)^2\), making
the exponent in (6) \(7/2\). These are the only coefficient logarithms used
in the calculation. The power obstruction below persists after granting
logarithmic exponent zero and granting the published theorems' positive
\(T^\varepsilon\) losses to be zero.

## 2. Drappeau Theorem 2.1: hypotheses and direct map

Here is the source theorem in the notation needed to check applicability.
Let \(C,D,N,R,S\ge1\), and let \(q_0,c_0,d_0\in\mathbb N\) satisfy
\((c_0d_0,q_0)=1\). The complex sequence \(b_{n,r,s}\) is supported in

\[
 (0,N]\times(R,2R]\times(S,2S]\cap\mathbb N^3.          \tag{7}
\]

The function \(g:\mathbb R_+^5\to\mathbb C\) is smooth, compactly supported
in

\[
 (C,2C]\times(D,2D]\times(\mathbb R_+^*)^3,             \tag{8}
\]

and, for some small \(\varepsilon_0>0\) and every fixed
\(\nu_1,\ldots,\nu_5\ge0\), satisfies

\[
 \frac{\partial^{\nu_1+\cdots+\nu_5}g}
 {\partial c^{\nu_1}\partial d^{\nu_2}\partial n^{\nu_3}
  \partial r^{\nu_4}\partial s^{\nu_5}}
 \ll_{\nu_1,\ldots,\nu_5}
 \left(c^{-\nu_1}d^{-\nu_2}n^{-\nu_3}
 r^{-\nu_4}s^{-\nu_5}\right)^{1-\varepsilon_0}.        \tag{9}
\]

Theorem 2.1 states

\[
\begin{aligned}
 &\sum_{\substack{c\equiv c_0\ (q_0)\\d\equiv d_0\ (q_0)\\
                    (q_0rd,sc)=1}}
 b_{n,r,s}g(c,d,n,r,s)
 e\!\left(\frac{n\overline{rd}}{sc}\right)\\
 &\qquad\ll_{\varepsilon,\varepsilon_0}
 (q_0CDNRS)^{\varepsilon+O(\varepsilon_0)}
 q_0^{3/2}K(C,D,N,R,S)\|b\|_2,                         \tag{10}
\end{aligned}
\]

where the summation in (10) is over all five integer variables and

\[
\begin{aligned}
 K(C,D,N,R,S)^2={}&q_0CS(RS+N)(C+RD)\\
 &+C^2DS\sqrt{(RS+N)R}+D^2NRS^{-1}.                    \tag{11}
\end{aligned}
\]

For each sign of \(\ell\), the direct parameter map is:

| Drappeau variable | Object in (2) | Power exponent |
|---|---|---:|
| \(q_0,c_0,d_0\) | \(1,1,1\) | \(0\) |
| \(c\), scale \(C\) | \(n_1\) | \(2/5\) |
| \(d\), scale \(D\) | \(m_1\) | \(2/5\) |
| \(n\), scale \(N\) | \(|\ell|h\) | \(33/50\) |
| \(r\), scale \(R\) | \(a\) | \(43/100\) |
| \(s\), scale \(S\) | \(b\) | \(43/100\) |

Explicitly,

\[
 b_{n,r,s}=\alpha_r\beta_s
 \sum_{\substack{\ell>0\\\ell h=n}}
 W_0(h/H)e(\pm\ell x),                                 \tag{12}
\]

with one sign at a time. The factors \(W_1,W_3,W_2,W_4\) go into \(g\).
A fixed low/high cutoff
\(\chi_{\rm lo}(n/H)\chi_{\rm hi}(n/(LH))\), equal to one on the support of
(12), makes the \(n\)-support compact. Its transitions occur at \(n\asymp H\)
and \(n\asymp LH\), so its \(j\)-th derivative is bounded by a fixed multiple
of \(n^{-j}\), which is stronger than (9) for \(n\ge1\). The normalized
derivatives of the other fixed smooth weights satisfy (9) in the same way.
The source condition

\[
 (q_0rd,sc)=1
\]

is exactly \((am_1,bn_1)=1\), and the inverse phase in (10) is the phase in
(2) for one sign. The opposite sign has the same bound by complex
conjugating the summand; this preserves the support, derivative conditions,
and \(L^2\) norm. Thus the direct route is an incomplete-sum application: it
does not first complete the \(m_1\) variable.

## 3. Drappeau direct exponent

With the preceding map, the three terms of \(K^2\) have exact exponents

\[
\begin{aligned}
 CS(RS+N)(C+RD)&:\quad \frac{63}{25},\\
 C^2DS\sqrt{(RS+N)R}&:\quad \frac{91}{40},\\
 D^2NRS^{-1}&:\quad \frac{73}{50}.                     \tag{13}
\end{aligned}
\]

The first dominates, hence

\[
 \operatorname{exp}K=\frac12\frac{63}{25}=\frac{63}{50}.
                                                               \tag{14}
\]

Combining (6) and (14), the fixed-\(x\) exponent is

\[
 \frac{63}{50}+\frac{19}{25}=\frac{101}{50}.           \tag{15}
\]

The product \(CDNRS\) in (10) has exponent \(58/25\). Thus the normalized
coefficient version of this specific upper-bound chain is

\[
 |Z_\pm(x)|
 \ll T^{101/50+(58/25)(\varepsilon+O(\varepsilon_0))}
       (\log T)^{3/2},                                  \tag{16}
\]

and the unnormalized two-log-slot version replaces \(3/2\) by \(7/2\).
Integrating the absolute value over the physical range in (3) subtracts
\(23/100\), so even after setting every positive power and logarithmic loss
to zero, (16) gives

\[
 \frac{101}{50}-\frac{23}{100}=\frac{179}{100}.         \tag{17}
\]

## 4. Pascadi Theorem 10.3: hypotheses and the failed completed map

Pascadi's published Theorem 10.3 assumes \(C,M,N,R,S\ge1\), a complex
sequence \(b_{n,r,s}\), a fixed \(\omega\in\mathbb R/\mathbb Z\), and a
five-variable smooth function \(g(t_1,\ldots,t_5)\) compactly supported where
all \(t_i\asymp1\), with

\[
 \left\|\partial_{t_1}^{j_1}\cdots
 \partial_{t_5}^{j_5}g\right\|_\infty
 \ll_{j_1,\ldots,j_5}1                                  \tag{18}
\]

for every fixed nonnegative \(j_i\). It states

\[
\begin{aligned}
 &\sum_{\substack{r\sim R,s\sim S\\(r,s)=1}}
   \sum_{m\sim M,n\sim N}e(m\omega)b_{n,r,s}
   \sum_{\substack{c\\(c,r)=1}}
   g\!\left(\frac cC,\frac mM,\frac nN,\frac rR,\frac sS\right)
   S(mr,\pm n;sc)\\
 &\ll_\varepsilon (CMNRS)^\varepsilon
 \left(1+\frac{CS\sqrt R}
 {\max(M,RS)\sqrt{\max(N,RS)}}\right)^{\theta_{\max}}
 \sqrt{MRS}\,\|b\|_2\\
 &\qquad\times
 \frac{(CS\sqrt R+\sqrt{MN}+C\sqrt{SM})
       (CS\sqrt R+\sqrt{MN}+C\sqrt{SN})}
      {CS\sqrt R+\sqrt{MN}}.                           \tag{19}
\end{aligned}
\]

The paper records the unconditional value
\(\theta_{\max}\le7/32\).

The attempted route completes the original \(m_1\)-sum modulo
\(q=bn_1\). Write its original length as \(D_0=M_1\), to avoid confusing it
with Pascadi's variables. Poisson completion supplies the prefactor
\(D_0/q=D_0/(SC)\) and dual length \(M=q/D_0=SC/D_0\). The *candidate*
parameter map used by the arithmetic calculation is:

| Pascadi variable | Candidate completed object | Power exponent |
|---|---|---:|
| \(C\) | \(n_1\) | \(2/5\) |
| \(M=SC/D_0\) | dual of \(m_1\) | \(43/100\) |
| \(N\) | \(|\ell|h\) | \(33/50\) |
| \(R\) | \(a\) | \(43/100\) |
| \(S\) | \(b\) | \(43/100\) |
| \(D_0/(SC)\) | completion prefactor | \(-43/100\) |

The scale rows and the coprimalities \((r,s)=1\), \((c,r)=1\) are compatible
with (19), but the Kloosterman row is not. Let
\(\sigma\in\{-1,1\}\), let \(\bar a\) be the inverse of \(a\pmod q\), and
let \(k\) be the literal Poisson frequency. Completing

\[
 e\!\left(\frac{\sigma n\overline{a m_1}}q\right)
 =e\!\left(\frac{\sigma n\bar a\,\overline{m_1}}q\right)
\]

gives the exact residue sum

\[
 \sum_{u\bmod q}^{*}
 e\!\left(\frac{ku+\sigma n\bar a\,\bar u}{q}\right)
 =S(k,\sigma n\bar a;q)
 =S(k\bar a,\sigma n;q).                              \tag{20a}
\]

The final equality follows by the source-faithful change
\(u=\bar a v\). Pascadi (19), with the required choice \(r=a\), instead
needs

\[
 S(ma,\sigma n;q).                                     \tag{20b}
\]

Matching (20a) to (20b) would require

\[
 m\equiv k\bar a^2\pmod q.                            \tag{20c}
\]

This is an \(a\)- and \(q\)-dependent permutation of residue classes. The
literal \(k\)-coefficient is supported on a short smooth interval of length
\(q/D_0=T^{43/100}\), whereas \(q=T^{83/100}\). No proof shows that (20c)
preserves a dyadic integer support \(m\asymp T^{43/100}\), produces the fixed
phase \(e(m\omega)\) required by (19), or preserves a coefficient independent
of the smooth modulus variable. Setting \(m=k\) would require
\(a^2\equiv1\pmod q\), which is not a source condition.

The exact formal regression
`zmod_five_literal_outer_mismatch` records that in \(\mathbb Z/5\mathbb Z\)
the choice \(a=2\) has \(\bar a=3\ne2=a\). It illustrates why the literal
identification of the completed first argument with Pascadi's \(r=a\) fails.
It does not rule out a new \((a,q)\)-dependent reindex or a different
multilinear theorem.

There is a second untreated piece: Poisson completion also produces the
\(k=0\) Ramanujan-sum term \(S(0,\sigma n\bar a;q)\). Theorem 10.3 sums over
\(m\sim M\) with \(M\ge1\), so this zero-frequency term is not covered by
(19). No separate estimate and recombination for it has been supplied.

Therefore (19) is **not currently applicable** to the literal completion.
The remaining calculations in Section 5 answer only the counterfactual
question: what exponent would the displayed Pascadi expression have if a
source-faithful support- and smoothness-preserving reindex were proved?

## 5. Pascadi candidate arithmetic and the inactive theta factor

Conditionally on the missing reindex after (20c), the components in (19)
would have exponents

\[
\begin{array}{c|c}
\text{component}&\text{exponent}\\ \hline
CS\sqrt R&209/200\\
\sqrt{MN}&109/200\\
C\sqrt{SM}&83/100\\
C\sqrt{SN}&189/200\\
\sqrt{MRS}&129/200.
\end{array}                                             \tag{20}
\]

The denominator inside the theta factor has exponent

\[
 \max\!\left(\frac{43}{100},\frac{86}{100}\right)
 +\frac12\max\!\left(\frac{66}{100},\frac{86}{100}\right)
 =\frac{129}{100}.                                      \tag{21}
\]

Therefore its ratio is

\[
 \frac{209}{200}-\frac{129}{100}=-\frac{49}{200}.       \tag{22}
\]

For \(T\ge1\), the complete theta factor is consequently at most

\[
 (1+T^{-49/200})^{\theta_{\max}}\le2^{7/32},            \tag{23}
\]

so it has power exponent zero. Setting
\(\theta_{\max}=0\), as under Selberg's conjecture, does not alter any
subsequent exponent.

In both numerator parentheses in (19), and in its denominator, the dominant
term is \(CS\sqrt R\). The rational factor therefore has exponent

\[
 \frac{209}{200}+\frac{209}{200}-\frac{209}{200}
 =\frac{209}{200}.                                      \tag{24}
\]

Before the completion prefactor, the candidate substitution gives

\[
 \frac{129}{200}+\frac{19}{25}+\frac{209}{200}
 =\frac{49}{20}.                                        \tag{25}
\]

Restoring the prefactor \(T^{-43/100}\) gives the same fixed-\(x\) exponent
as (15):

\[
 \frac{49}{20}-\frac{43}{100}=\frac{101}{50}.           \tag{26}
\]

The product \(CMNRS\) in (19) has exponent \(47/20\). Thus the candidate
arithmetic for a maximal dual block is

\[
 T^{101/50+(47/20)\varepsilon}(\log T)^{3/2},           \tag{27}
\]

or logarithmic exponent \(7/2\) with the two long log slots unnormalized.
For a lower dual exponent \(m\le43/100\), the right-hand side before physical
integration is \(T^{361/200+m/2}\) before the positive epsilon and logarithmic
losses, so the dyadic dual blocks form a geometrically dominated family; no
additional logarithmic exponent is inserted in (27). Physical integration
again subtracts \(23/100\), and the maximal-block arithmetic is \(179/100\).
Because the reindex and zero-frequency treatment are missing, (27) is not a
proved bound for the literal completed sum.

## 6. Exact finish-or-kill statement

### Verdict 1: direct collapsed Drappeau class

Define the **direct collapsed Drappeau class** to consist of exactly the
following operations:

1. grant the candidate \(d=1\) smooth block (2);
2. collapse each pair of Möbius slots into \(\alpha,\beta\), and collapse
   \((|\ell|,h)\) into \(n\);
3. use the multiplicative-energy \(L^2\) bound (6), without cancellation
   inside those norms;
4. apply Drappeau Theorem 2.1 once at fixed \(x\);
5. integrate the resulting fixed-\(x\) absolute bound, with no cancellation
   between signs, \(x\)-values, Heath--Brown components, or scales.

This prescribed chain has power exponent

\[
 \frac{179}{100},\qquad
 \frac{179}{100}-\frac{143}{100}=\frac9{25}.            \tag{28}
\]

Adding the actual positive \(T^\varepsilon\) or logarithmic factors only
increases the displayed upper bound. Hence this direct class cannot
establish the required fixed-\(x\) exponent \(83/50\), equivalently the
integrated trace exponent \(143/100\), with any logarithmic exponent.
Equation (28) is a statement about the output of the prescribed upper-bound
chain. It is not a lower bound for \(Z_\pm(x)\) and does not prove that the
signed remainder itself has size \(T^{179/100}\).

### Verdict 2: literal completed \(r=a\) Pascadi map

Define the **literal completed \(r=a\) Pascadi class** to complete \(m_1\),
keep the literal Poisson frequency \(k\) as the proposed theorem variable
\(m\), set Pascadi's \(r=a\), and apply Theorem 10.3 directly. This class is
structurally inapplicable and therefore killed: its source residue sum is
(20a), while its required residue sum is (20b). The \(\mathbb Z/5\mathbb Z\)
regression shows that replacing \(\bar a\) by \(a\) is not an identity, and
the \(k=0\) term is outside the theorem's \(m\sim M\) sum.

A new source-faithful reindex using (20c), with proved dyadic support,
smoothness, coefficient independence, fixed additive phase, and a separate
zero-frequency treatment, is outside this literal class and remains open.
The conditional \(179/100\) arithmetic in Section 5 is not a bound and plays
no role in either finish/kill verdict.

The exact surviving target is therefore still

\[
 |Z_\pm(x)|\ll T^{83/50}(\log T)^C,
 \qquad
 \int_{|x|\asymp T^{-23/100}}|Z_\pm(x)|\,dx
 \ll T^{143/100}(\log T)^C,
 \qquad C<1,                                             \tag{29}
\].

In particular, this audit leaves open:

- a coefficient-sensitive multilinear/Kuznetsov theorem retaining all four
  separate Möbius variables instead of replacing each pair by one \(L^2\)
  coefficient;
- signed cancellation across Heath--Brown components or dyadic scales before
  an absolute-value theorem is applied;
- simultaneous treatment of \(x\) and \(\ell\), instead of a fixed-\(x\)
  estimate followed by \(\int|Z_\pm(x)|dx\);
- a source-faithful \((a,q)\)-dependent completion reindex satisfying every
  support and coefficient hypothesis of Theorem 10.3, together with the
  \(k=0\) term;
- construction and exact recombination of the source smooth Heath--Brown
  partition itself.

No conclusion here concerns those routes or the \(d>1\) family.

## 7. Formal and independent checks

`RH/Zeta85/Discharge/PreMajorantDI.lean` proves, with exact rational
arithmetic:

- the source, numerator, physical, and coefficient-\(L^2\) power exponents;
- all three Drappeau \(K^2\) terms and the direct final exponent;
- the finite \(\mathbb Z/5\mathbb Z\) inverse mismatch;
- the candidate completion scale, every candidate Pascadi factor, and the
  negative theta ratio as arithmetic only;
- the direct \(9/25\) excess and its strict failure after any nonnegative
  power slack.

The module declares no analytic theorem, no premise, and no proof
placeholder. It formalizes the direct exponent finish/kill, the finite
literal-map regression, and the conditional Pascadi exponent substitution.
It does not formalize or assert the missing reindex. The dependency printer
covers every headline calculation.

```sh
lake build RH.Zeta85.Discharge.PreMajorantDI
lake env lean comparator/PrintAxioms/PreMajorantDI.lean
python3 verify/a1_premajorant_di.py
diff -u verify/a1_premajorant_di.out \
  <(python3 verify/a1_premajorant_di.py)
```

The verifier uses only exact `fractions.Fraction` arithmetic and commits its
complete output.
