# Zeta-95 arithmetic, cycle 1: support two and the first supercritical resonance

## 0. Delivered result

Continue from `zeta85/agents/arithmetic_cycle5.md` as accepted.  This cycle
gives the unconditional extension

\[
 \boxed{\sigma<2}
\]

for the connected prime-side kernel.  The limiting optimized second-trace
certificate is

\[
 \boxed{
 \liminf_{T\to\infty}\frac{N_{0,\mathrm{simple}}(T)}{N(T)}
 \ge 0.932282623935296\ldots .}                              \tag{1}
\]

This is an absolute improvement of

\[
 0.932282623935296-0.865674254456636
 =0.066608369478660\ldots                                   \tag{2}
\]

over cycle 5.

The optimized connected support needed for 95 percent is

\[
 \boxed{\sigma_{95}=2.26078781\ldots,\qquad
        \eta_{95}:=\sigma_{95}-1=1.26078781\ldots .}          \tag{3}
\]

Thus support two does not yet reach 95 percent.  For (3), this cycle also
reduces the first genuinely supercritical term to one explicit averaged
correlation of the actual Heath--Brown coefficients.  A termwise
inverse-residue $L^1$ argument provably cannot supply the required saving;
the exact resonant correlation and its depth-five exponents are given below.

## 1. Connected variational benchmark for 95 percent

For an interval of length $\sigma$, let

\[
 (\mathcal K_\sigma f)(x)
 =\int_{-\sigma/2}^{\sigma/2}\min(|x-y|,1)f(y)\,dy.
\]

If $g_\sigma$ solves

\[
                    (I+\mathcal K_\sigma)g_\sigma=1,          \tag{4}
\]

then normalization gives

\[
 D_\sigma^*=\left(\int_{-\sigma/2}^{\sigma/2}
                         g_\sigma(x)\,dx\right)^{-1}.         \tag{5}
\]

The solution is positive in the range used here.  Solving the piecewise
delay equation obtained by differentiating (4), with value and derivative
matching at the points separated by one, gives

\[
 D_{\sigma_{95}}^*=1.05,qquad
 \sigma_{95}=2.26078781\ldots .                              \tag{6}
\]

At the endpoint delivered in this cycle,

\[
 D_2^*=1.067717376064704\ldots,qquad
 2-D_2^*=0.932282623935296\ldots .                           \tag{7}
\]

The relevant shift exponent at the 95-percent point is

\[
 \theta_{95}:=\frac{\log(H/T)}{\log H}
 =1-\frac1{\eta_{95}}
 =0.206845123288430\ldots .                                  \tag{8}
\]

## 2. A new terminal factorization for $1/2<\eta<1$

Retain the notation of cycle 5:

\[
 X=T^{1+\eta},\qquad A=B=H=T^\eta,qquad M=N=T.              \tag{9}
\]

For $1/2<\eta<1$, use the asymmetric split

\[
 M_1=T^{1-\eta},\qquad M_2=T^\eta,qquad
 N_1=1,qquad N_2=T.                                        \tag{10}
\]

It respects $M_1\le M_2$ and $N_1\le N_2$.  After the gcd split
$d_1d_2=d_3d_4=d$, the two inverse-residue variables and the signed-shift
length are

\[
 P_d\asymp\frac{AM_1}{d}=\frac{T}{d},\qquad
 Q_d\asymp\frac{BN_1}{d}=\frac{H}{d},\qquad
 H_d=\frac Hd.                                               \tag{11}
\]

The physical Fourier scale and dual-frequency length are

\[
 \frac{dN_2}{AM_1}\asymp d,qquad
 \frac{AM}{dM_2N_2}\asymp\frac1d.                           \tag{12}
\]

Consequently the signed-shift reciprocal lemma (cycle 5, equation (16)),
with the actual Fourier decay retained, gives

\[
 \begin{aligned}
 R_{\rm term}
 &\ll \sum_d P_d(Q_d+H_d)(1+d)^{-2}(\log T)^C\\
 &\ll TH(\log T)^C
 =X(\log T)^C.                                               \tag{13}
 \end{aligned}

The preliminary zero-shift replacement costs

\[
 H^2(\log T)^C\le TH(\log T)^C                              \tag{14}
\]

precisely for $\eta\le1$.  All Type-I, pole, tail and zero-mode blocks are
the accepted ones from cycles 1--5.  Hence every fixed $\eta<1$, or
equivalently every fixed connected support $\sigma<2$, is trace-grade.
Taking $\sigma\uparrow2$ in (7) proves (1).

This construction uses no new spectral theorem.  It simply changes the
factorization at the point where the cycle-5 choice
$N_1=T^{1/2-\eta}$ would cease to exist.

## 3. The exact loss once $\eta>1$

When $\eta>1$, positivity of factor lengths forces

\[
 M_1,N_1\ge1,qquad P=AM_1\ge H,qquad Q=BN_1\ge H.          \tag{15}
\]

The smallest terminal choice is therefore

\[
 M_1=N_1=1,qquad M_2=N_2=T,qquad P=Q=H.                   \tag{16}
\]

Put

\[
                         L:=H/T=T^{\eta-1}.                  \tag{17}
\]

Now the physical Fourier scale is $T/H=L^{-1}$, while the nonzero dual
frequency has length $L$.  The reciprocal $L^1$ majorant has size

\[
                         H^2(\log T)^C,                      \tag{18}
\]

against trace scale

\[
                         TH=H^2/L.                           \tag{19}
\]

Thus the exact missing factor is

\[
 \boxed{L=H/T=T^{\eta-1}.}                                  \tag{20}
\]

At the 95-percent exponent this is

\[
 L=T^{0.26078781\ldots}
  =H^{0.206845123288430\ldots}.                              \tag{21}
\]

## 4. Impossibility for the termwise inverse-residue $L^1$ class

Define the **reciprocal-$L^1$ class** to consist of arguments which

1. perform the smooth $h$-sum in the Kloosterman fraction;
2. take absolute values separately in $p,q,\ell$ afterwards; and
3. use only fixed-divisor majorants for the two collapsed HB coefficients.

This class cannot improve (18).  Indeed, for every
$1\le\ell\le cL$, select the terms

\[
                            p=q+\ell.                         \tag{22}
\]

Then $\bar p\equiv\bar\ell\pmod q$; in particular, after restricting to
$(\ell,q)=1$, the least reciprocal residue in
$\ell\bar p\pmod q$ is $1$.  On a fixed sub-box $q\asymp H$, the
smooth shift transform has magnitude

\[
 \left|\sum_h w(h/H)e(\ell h\bar p/q)\right|
 \asymp H\,|\widehat w(H/q)|\gg_w H.                        \tag{23}
\]

The Fourier coefficient in the $m_2$-Poisson step has size
$L^{-1}\widehat F(\ell/L)$ on a fixed positive proportion of
$1\le\ell\le L$.  There are $\asymp H$ pairs (22) per $\ell$.
Therefore the termwise absolute majorant contains

\[
 \frac1L\cdot L\cdot H\cdot H\asymp H^2.                   \tag{24}
\]

This is a lower bound for the **method's majorant**, not for the signed
arithmetic sum.  It proves that no refinement which remains inside the three
rules above can recover the factor $L$ in (20), even with perfect treatment
of all nonresonant residues.

## 5. Calculation outside that class: the actual HB resonance

Do not take absolute values after the $h$-sum.  Poisson summation gives

\[
 \sum_h w(h/H)e(\ell h\bar p/q)
 =H\sum_j\widehat w\!\left(H(j-\ell\bar p/q)\right).         \tag{25}
\]

Let $r=\ell\bar p-jq$.  Since $H/q\asymp1$, Fourier decay restricts
$|r|\le(\log T)^B$.  The congruence is exactly

\[
                         rp-kq=\ell                          \tag{26}
\]

for an integer $k$ with $|k|\ll(\log T)^B$.  The zero residue cannot
occur because $0<|\ell|\le L<q/T^{1-o(1)}$.  Since the physical Fourier
factor $L^{-1}$ times the shift-transform factor $H$ is $T$, the
supercritical remainder is

\[
 R_{\rm res}
 =T\sum_{\substack{0<|r|,|k|\le(\log T)^B}}
   \sum_{\ell\asymp L}\omega_{r,k}(\ell/L)
   \sum_{\substack{q\asymp H\\rp-kq=\ell}}
       c_p\,e_q\,V_{r,k}(p/H,q/H)
 +O_A(X\log^{-A}T).                                         \tag{27}
\]

Here $c_p,e_q$ are the **un-collapsed, recombined HB coefficients**.  The
leading resonance $r=k=1$ is

\[
 T\sum_{\ell\asymp L}\omega(\ell/L)
   \sum_{q\asymp H}c_{q+\ell}e_qV(q/H).                     \tag{28}
\]

Thus 95 percent is reduced to the concrete coefficient-sensitive estimate

\[
 \boxed{
 \sum_{\ell\asymp L}\omega_{r,k}(\ell/L)
   \sum_{rp-kq=\ell}c_p e_qV_{r,k}(p/H,q/H)
 \ll H(\log T)^C,}                                          \tag{IR-HB}
\]

uniformly for polylogarithmic $r,k$, at the exact lengths (21).  This is
not a generic shifted-correlation conjecture: $c,e$ are the finite
Möbius/log convolution pieces before the HB identities are recombined.

## 6. Depth-five attempt and the remaining bilinear block

At scale $H=T^{\eta_{95}}$, a depth-five HB/fractional-zeta decomposition
has every irregular factor of length at most

\[
 V=H^{1/5}=T^{0.252157562\ldots}.                            \tag{29}
\]

The shift average is genuinely longer:

\[
 L=T^{0.260787810\ldots},qquad
 \frac LV=T^{0.008630248\ldots},qquad
 \frac{\log L}{\log H}-\frac15
 =0.006845123288430\ldots.                                  \tag{30}
\]

Keeping these factors separate converts (IR-HB), after the Type-I zero modes
are removed, to finitely many blocks whose hardest balanced representative is

\[
 \boxed{
 \begin{aligned}
 \mathcal B_{95}:={}&
 \sum_{\ell\asymp L}\omega(\ell/L)
 \sum_{a,b\asymp V}\alpha_a\beta_b
 \sum_{\substack{m,n\asymp H/V\\ r a m-k b n=\ell}}
 u_m v_n\,W(a,b,m,n) -\mathcal M_{r,k}\\
 &\hspace{35mm}\ll H(\log H)^C,
 \end{aligned}}                                             \tag{BI-95}
\]

where $\alpha_a,\beta_b$ are the actual bounded short Möbius/fractional-HB
pieces and $u_m,v_n$ are positive convolution powers of $1$, with their
log derivatives retained.  The main term $\mathcal M_{r,k}$ is the double
zero mode and is already part of the accepted singular-series term.

This is the first calculation outside the impossible class: it exposes a
strict $L>V$ margin and keeps the signed $\ell$-average through the actual
depth-five factors.  A single Poisson completion in $m$, however, produces
modulus $bn\asymp H$ and short/dual variables of size at most

\[
                         V=H^{1/5}.                           \tag{31}
\]

The arbitrary-coefficient Blomer--Pascadi bound becomes nontrivial only at
length $H^{13/28+o(1)}$, and the MQW threshold is still larger.  Hence a
one-shot bilinear Kloosterman black box does not prove (BI-95).  The unused
resource is precisely the simultaneous $\ell$-average of length
$L=H^{0.206845\ldots}>V$; it must enter a multilinear dispersion estimate
before completion.

## 7. Handoff

* Unconditional connected support delivered: every $\sigma<2$.
* New rigorous limiting percentage: $93.2282623935296\%$.
* Minimal optimized connected support for 95 percent:
  $\sigma_{95}=2.26078781\ldots$.
* Exact missing saving there: $L=H/T=T^{0.26078781}$.
* Precise method impossibility: reciprocal-$L^1$ termwise absolute values
  necessarily retain $H^2$.
* First coefficient-sensitive object outside it: (IR-HB), reduced at depth
  five to (BI-95), with the positive exponent margin $L/V=T^{0.008630248}$.
* Next construction: a four-variable dispersion inequality for (BI-95) that
  uses the $\ell$-average before completing either long variable.
