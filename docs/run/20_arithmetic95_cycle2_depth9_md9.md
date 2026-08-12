# Zeta-95 arithmetic, cycle 2: depth nine and the two-sided resonance barrier

## 0. Terminal result

Take the support-two theorem of arithmetic cycle 1 and the mixed
pair-plus-quartic certificate as accepted.  At the mixed 95-percent target the
parameters are

\[
 \sigma_*=2.14233794449584,\qquad
 \eta_*:=\sigma_*-1=1.14233794449584,
\tag{1}
\]

\[
 H=T^{\eta_*},\qquad L=H/T=T^{0.14233794449584}
       =H^\rho,
 \qquad
 \rho=0.1246023080837601868\ldots .
\tag{2}
\]

This cycle does **not** claim an unconditional extension past connected
support two.  It proves a precise impossibility statement for the one-shot
completion/Kloosterman class and then performs the first estimate outside
that class:

\[
 \boxed{\mathcal T_I-\mathcal M_I
        \ll H^{0.962707944411972+o(1)}} .
\tag{3}
\]

Equation (3) handles every actual depth-nine HB block having one truncated
factor and a smooth long companion on at least one side.  In particular it
handles the complete \(j=1\) HB subfamily, with its actual Möbius and logarithm
coefficients, at better than the required \(H\operatorname{polylog}H\) scale.
It is obtained by summing the signed \(\ell\)-progression before absolute
values.

The survivor is a genuinely two-sided multilinear dispersion moment.  It
needs the power

\[
                    L^2=H^{0.249204616167520\ldots}          \tag{4}
\]

beyond the trivial second-moment bound.  A single arbitrary-coefficient
Kloosterman insertion can save at most the quoted modulus power \(H^{-1/32}\)
even in its ideal square-root range, and the actual depth-nine atom has length
only \(H^{1/9}\), below the \(H^{13/28}\) nontriviality threshold.  Thus the
one-shot method cannot prove the target.  This is an impossibility theorem
about the explicitly defined method class below, not about (IR-HB) itself.

The rigorously supported endpoint remains

\[
 \boxed{\sigma<2,\qquad
 \liminf \frac{N_{0,\mathrm{simple}}}{N}
 \ge 0.938313327050949\ldots}                               \tag{5}
\]

when the accepted nested-quartic certificate is included.  The right side of
(5) is the limiting value as \(\sigma\uparrow2\).

## 1. Why depth nine is the first usable identity

At scale \(H\), use the exact depth-\(k\) Heath--Brown identity in the form

\[
 \Lambda(n)=\sum_{j=1}^{k}(-1)^{j-1}{k\choose j}
 \sum_{\substack{a_1\cdots a_jd_1\cdots d_j=n\\a_i\le V}}
 \mu(a_1)\cdots\mu(a_j)\log d_1,
 \qquad n\asymp H,                                         \tag{6}
\]

with \(V=(2H)^{1/k}\).  Dyadic partitions make every displayed long
variable smooth; their number is fixed.  The same expansion applies to the
finite log derivatives occurring in the accepted recombined coefficients.

The signed resonance average has length \(L=H^\rho\).  To make it longer
than every individual irregular factor requires

\[
                         \frac1k<\rho .                     \tag{7}
\]

Numerically,

\[
 \rho^{-1}=8.02553351843033\ldots .                         \tag{8}
\]

Thus depth eight misses, while depth nine has a fixed power margin:

\[
\begin{array}{c|c|c}
k&V\text{ as a power of }T&L/V\text{ as a power of }T\\ \hline
8&T^{0.142792243061980}&T^{-0.000454298566140}\\
9&T^{0.126926438277316}&T^{\phantom{-}0.015411506218524}
\end{array}                                                  \tag{9}
\]

Equivalently, at depth nine

\[
 V=H^{1/9},\qquad
 \frac LV=H^\gamma,qquad
 \gamma=\rho-\frac19
       =0.0134911969726490757\ldots .                       \tag{10}
\]

This strict margin is the resource used in (3).

## 2. The exact location of the lost factor

Cycle 1 reduced the supercritical terminal remainder to

\[
 R_{\rm res}=T\sum_{0<|r|,|k|\le (\log T)^B}
 \sum_{\ell\asymp L}\omega_{r,k}(\ell/L)
 \sum_{rp-kq=\ell}c_p e_qV_{r,k}(p/H,q/H)
 +O_A(X\log^{-A}T).                                        \tag{11}
\]

The required trace bound is therefore

\[
 \mathcal S_{r,k}:=
 \sum_{\ell\asymp L}\omega_{r,k}(\ell/L)
 \sum_{rp-kq=\ell}c_pe_qV_{r,k}(p/H,q/H)
 \ll H(\log H)^C.                                          \tag{12}
\]

There are \(L\) shifts and a fixed-shift divisor majorant is \(H^{1+o(1)}\).
Taking the absolute value shift by shift therefore gives \(HL\), losing
exactly \(L\).  The equivalent loss after one Cauchy--Schwarz is even more
useful.  Write \(E_{r,k}(\ell)\) for the inner sum after removal of its
accepted zero mode.  Then (12) follows from

\[
 \boxed{
 \sum_{\ell\asymp L}|E_{r,k}(\ell)|^2
 \ll \frac{H^2}{L}(\log H)^C
 =H^{1.875397691916240\ldots+o(1)}.}                        \tag{MS9}
\]

The trivial moment is \(H^2L=H^{2.124602308083760\ldots}\).
Consequently (MS9) asks for the precise saving (4), not a full pointwise
prime-pair asymptotic.

## 3. Impossibility for the one-shot completion class

Define \(\mathscr C_{\rm one}\) to be the following proof class.

1. Expand \(c_p,e_q\) by a fixed-depth HB identity and dyadically localize.
2. Collapse all but at most one truncated factor on each side into arbitrary
   divisor-bounded coefficients.
3. Take a triangle inequality or one Cauchy--Schwarz in the \(\ell\)-variable
   before a second independent factor average is used.
4. Complete one remaining variable and use one arbitrary-coefficient
   bilinear Kloosterman estimate.  All remaining sums are bounded by large
   sieve, divisor bounds, and triangle inequality.

This includes direct one-shot substitutions of the general-modulus
Blomer--Pascadi bound into the terminal BBLR/dispersion stage.  It is more
generous than the actual parameter range: grant that the Kloosterman theorem
is in its ideal square-root range and grants its full \(H^{-1/32}\) saving.

Before that insertion, the method has the trivial amplitude \(HL\).  Hence
the best exponent available to \(\mathscr C_{\rm one}\) is still

\[
 H^{1+\rho-1/32+o(1)}
 =H^{1.093352308083760\ldots+o(1)},                          \tag{13}
\]

whereas (12) requires \(H^{1+o(1)}\).  Equivalently, after squaring, even a
generous doubled saving \(H^{-1/16}\) leaves

\[
 H^{2+\rho-1/16+o(1)}=H^{2.062102308083760\ldots+o(1)},      \tag{14}
\]

above the (MS9) exponent by

\[
              2\rho-\frac1{16}
              =0.186704616167520\ldots .                    \tag{15}
\]

For the actual depth-nine balanced atom the black box does not even reach
the optimistic line (13): its free atom has length \(V=H^{1/9}\), whereas
the quoted arbitrary-coefficient nontriviality threshold is
\(H^{13/28+o(1)}\).  The exponent deficit is

\[
 \frac{13}{28}-\frac19
 =0.353174603174603\ldots .                                 \tag{16}
\]

Thus no member of \(\mathscr C_{\rm one}\) can recover the missing \(L\)
at (1).  Increasing the HB depth can place a grouped variable in the
square-root range, but it cannot change the one-shot saving comparison
\(1/32<\rho\).  This proves the stated method-class impossibility.

For scale, four *independent* amplitude savings of size \(H^{-1/32}\) would
just suffice:

\[
 \frac4{32}-\rho
 =0.000397691916239813\ldots .                              \tag{17}
\]

The word independent is essential.  After the first completion the next HB
factor is coupled to the preceding dual frequency and inverse residue, so the
arbitrary-coefficient theorem cannot simply be iterated four times.

## 4. A completed estimate outside that class: the one-sided HB blocks

Here is the promised coefficient-sensitive calculation.  Consider an actual
depth-nine block in which the \(q\)-coefficient has its \(j=1\) shape

\[
                         e_{bn}=\beta_b\log n,
 \qquad b\asymp B\le V,\quad b\le V,\quad bn\asymp H,       \tag{18}
\]

where \(\beta_b=\mu(b)\) times a fixed smooth dyadic cutoff.  Allow the
\(p\)-coefficient \(a_p\) to be any of the actual remaining HB blocks; its
fixed-divisor majorant gives

\[
                 \sum_{p\asymp H}|a_p|\ll H(\log H)^C.      \tag{19}
\]

After absorbing \(\log n\) into the smooth weight, put

\[
 \mathcal T_I=
 \sum_{\ell}\omega(\ell/L)
 \sum_{\substack{p\asymp H,\ b\asymp B,\ n\\
                  rp-kbn=\ell}}
 a_p\beta_bW(p/H,bn/H).                                    \tag{20}
\]

For fixed \(p,b\), the integer \(n\) exists precisely when

\[
                       \ell\equiv rp\pmod{|k|b}.            \tag{21}
\]

Set

\[
 F_{p,b}(x)=\omega(x/L)
 W\!\left(\frac pH,\frac{rp-x}{kH}\right),                 \tag{22}
\]

including the smooth logarithm and dyadic cutoffs in \(W\).  Since \(L<H\),

\[
 \widehat F_{p,b}(y)
 \ll_A L(\log H)^C(1+L|y|)^{-A}.                           \tag{23}
\]

Poisson summation in the progression (21), **before any absolute value in
\(\ell\)**, gives

\[
 \sum_{\ell\equiv rp\ (|k|b)}F_{p,b}(\ell)
 =\frac1{|k|b}\sum_{t\in\mathbb Z}
 e\!\left(\frac{trp}{|k|b}\right)
 \widehat F_{p,b}\!\left(\frac{t}{|k|b}\right).           \tag{24}
\]

The \(t=0\) term is the block's zero mode \(\mathcal M_I\), already included
in the accepted singular integral.  Because \(|k|=H^{o(1)}\) and
\(L/B\ge H^{\gamma-o(1)}\), (23) gives for the nonzero frequencies

\[
 \frac1{|k|b}\sum_{t\ne0}
 \left|\widehat F_{p,b}\!\left(\frac{t}{|k|b}\right)\right|
 \ll_A \left(\frac{|k|b}{L}\right)^{A-1}(\log H)^C.        \tag{25}
\]

Summing (25) with (19) and
\(\sum_{b\asymp B}|\beta_b|\ll B\) yields the explicit estimate

\[
 \boxed{
 \mathcal T_I-\mathcal M_I
 \ll_A HB\left(\frac{B}{L}\right)^{A-1}H^{o(1)}.}          \tag{26}
\]

Take \(A=12\), \(B\le H^{1/9}\), and use (10).  Then

\[
 1+\frac19-11\gamma
 =0.962707944411971\ldots,                                  \tag{27}
\]

which proves (3).  The same proof works with the roles of \(p,q\) reversed,
with signed \(\ell\), and uniformly for the polylogarithmic \(r,k\) in
(11).  More generally it resolves any opened block for which the entire
progression modulus on one side is at most \(H^{1/9+o(1)}\) and the companion
coefficient is smooth.

This is a genuine use of the actual HB structure: replacing \(\beta_b\log n\)
by an arbitrary collapsed coefficient destroys the progression Poisson step.

## 5. The precise two-sided block left after (26)

For \(j,j'\ge2\), define the uncollapsed HB pieces

\[
 C_j(p)=
 \sum_{\substack{a_1\cdots a_jd_1\cdots d_j=p\\a_i\le V}}
 \mu(a_1)\cdots\mu(a_j)\log d_1,                            \tag{28}
\]

and define \(D_{j'}(q)\) analogously, with every variable dyadically
localized.  After subtracting the zero mode, the only unsolved family is

\[
 E_{j,j';r,k}(\ell)=
 \sum_{\substack{r a_1\cdots a_jd_1\cdots d_j
              -k b_1\cdots b_{j'}e_1\cdots e_{j'}=\ell}}
 \Big(\prod_i\mu(a_i)\Big)
 \Big(\prod_i\mu(b_i)\Big)
 (\log d_1)(\log e_1)W-\mathcal M_{j,j';r,k}(\ell).        \tag{29}
\]

Every \(a_i,b_i\le V=H^{1/9}\), but products of two or more of them can
exceed \(L\).  That is exactly why the one-progression argument (24) no
longer applies.

Squaring (29) shows that (MS9) is the following concrete multilinear
dispersion problem, not an unspecified prime-pair assertion:

\[
\begin{aligned}
 &\sum_{\substack{\mathbf a^{(1)},\mathbf a^{(2)},
                   \mathbf b^{(1)},\mathbf b^{(2)}\\
 r(A_1D_1-A_2D_2)=k(B_1E_1-B_2E_2)\\
 |rA_\nu D_\nu-kB_\nu E_\nu|\asymp L}}
 \prod_{\nu=1}^{2}
 \mu(\mathbf a^{(\nu)})\mu(\mathbf b^{(\nu)})
 (\log d^{(\nu)}_1)(\log e^{(\nu)}_1)
 \mathcal W
 \\
 &\hspace{35mm}\ll H^{2-\rho+o(1)},                        \tag{MD9}
\end{aligned}
\]

after removal of the explicitly known double zero mode.  Here
\(A_\nu=\prod a_i^{(\nu)}\), \(D_\nu=\prod d_i^{(\nu)}\), and similarly for
\(B_\nu,E_\nu\).  The diagonal
\(A_1D_1=A_2D_2,\ B_1E_1=B_2E_2\) is only \(H^{1+o(1)}\), safely below the
right side.  The task is solely the off-diagonal.

The first viable construction beyond \(\mathscr C_{\rm one}\) must retain
\(\ell\) and at least four independent HB factor averages through the
completion.  At the exponent level, a four-stage modulus saving would give

\[
 H^{2+\rho-8/32+o(1)}
 =H^{1.874602308083760\ldots+o(1)},                          \tag{30}
\]

which beats the required exponent \(2-\rho\) by
\(0.000795383832480\ldots\).  Formula (30) is not asserted as a theorem:
it records the exact margin and explains why discarding even one of the four
factor averages fails.  The missing new input is a genuinely iterated
multilinear inverse-residue inequality for the explicit sum (MD9), with the
dual frequencies from one stage retained as structured coefficients in the
next stage.

## 6. Handoff

* Mixed 95-percent target: \(\sigma_*=2.14233794449584\),
  \(\rho=0.124602308083760\ldots\).
* Depth nine is minimal; its usable margin is
  \(L/V=H^{0.0134911969726491\ldots}\).
* The exact absolute-value loss is \(L\), or \(L^2\) after the dispersion
  square.
* The one-shot completion/arbitrary-coefficient Kloosterman class cannot
  close: even its optimistic saving \(H^{-1/32}\) is less than
  \(H^{-\rho}\), and the actual atom is below its nontrivial range.
* The actual one-sided HB blocks are now closed by (26), with the numerical
  power saving (3).
* The sole survivor is the explicit two-sided off-diagonal (MD9).  A
  four-stage, coefficient-preserving inverse-residue dispersion inequality
  would close the full combined 95-percent target with the very small margin
  in (30).
