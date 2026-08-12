# Zeta-100 arithmetic, cycle 3: full Type-III stratification and reciprocity

## 0. Terminal output

This cycle takes the permitted **precise two-dispersion class kill plus
concrete reciprocity calculation** branch.  No support extension is claimed.

Use

\[
 \rho={1\over1001},\qquad L=H^\rho,\qquad P=H^{1/3},
 \qquad M=P^2=H^{2/3}.                                     \tag{1}
\]

The full \(j=j'=3\) Type-III MD moment is expanded and stratified below.
The following families are closed unconditionally:

\[
\begin{array}{c|c|c}
\text{stratum}&\text{bound}&\text{ratio to }H^{2-\rho}\\ \hline
\text{full product diagonal}
 &H^{1+\rho+o(1)}&H^{-1+2\rho+o(1)}\\
\text{same two-factor bases}
 &H^{4/3+\rho+o(1)}&H^{-2/3+2\rho+o(1)}\\
\text{all proportional bases }(D=0)
 &H^{4/3+\rho+o(1)}&H^{-2/3+2\rho+o(1)}\\
0<|D|\le M/L^2
 &H^{2-\rho+o(1)}&H^{o(1)}\\
g_1,g_2\ge L
 &H^{2-\rho+o(1)}&H^{o(1)}\\
\max(g_1,g_2)>2L
 &0&0 .
\end{array}                                                 \tag{2}
\]

Here

\[
 D=A_1B_2-A_2B_1,\qquad g_\nu=(rA_\nu,kB_\nu),             \tag{3}
\]

after writing \(p_\nu=A_\nu u_\nu,q_\nu=B_\nu v_\nu\) with
\(A_\nu,B_\nu\asymp M\) and \(u_\nu,v_\nu\asymp P\).

The sole two-dispersion survivor is therefore explicit:

\[
 |D|>M/L^2,\qquad \min(g_1,g_2)<L,\qquad g_1,g_2\le2L.     \tag{4}
\]

In this generic entangled range, any argument which expands the centered
moment and takes absolute values before recombining its zero modes has
majorant

\[
                         H^{2}L\,H^{o(1)},                   \tag{5}
\]

against the MD allowance \(H^2/L\).  The exact method loss is

\[
                         \boxed{L^2=H^{2/1001}}.             \tag{6}
\]

Section 5 turns this into an impossibility theorem for the precisely defined
absolute two-dispersion class.  This is not a claim that the Type-III block
itself is impossible.

The mandatory calculation outside that class keeps the Poisson phase and
uses additive reciprocity.  Uniformly on the generic coprime core,

\[
 e\!\left({z\bar a\over b}\right)
 =
 e\!\left(-{z\bar b\over a}\right)
 +O\!\left({|z|\over ab}\right).                            \tag{7}
\]

At the forced Type-III lengths

\[
 |z|\ll PL,\qquad a,b\asymp P^2,                           \tag{8}
\]

the total error in replacing every phase by its reciprocal partner,
including the Poisson prefactor \(P^{-1}\), is

\[
 \boxed{\mathcal E_{\rm rec}
 \ll P L^2 H^{o(1)}
 =H^{1/3+2\rho+o(1)}}.                                     \tag{9}
\]

This is trace grade with the fixed saving

\[
 {H^{1/3+2\rho}\over H}
 =H^{-2/3+2\rho}
 =H^{-0.664668664\ldots}.                                  \tag{10}
\]

Thus reciprocity may be imposed **for free at trace scale** before the third
difference.  This is a completed signed-phase calculation outside the
killed class, not a restatement of a missing lemma.

The arithmetic endpoint and accepted percentage remain

\[
 \boxed{\sigma<2,\qquad
 \liminf_{T\to\infty}{N_{0,\mathrm{simple}}(T)\over N(T)}
 >0.96250068026-o(1).}                                     \tag{11}
\]

## 1. Full second-dispersion equations

For the two copies of the Type-III block, write

\[
 p_\nu=A_\nu u_\nu,\qquad q_\nu=B_\nu v_\nu,\qquad
 A_\nu,B_\nu\asymp M,\quad u_\nu,v_\nu\asymp P,
 \qquad \nu=1,2.                                           \tag{12}
\]

Equality of the signed shifts is the exact equation

\[
 rA_1u_1-kB_1v_1
 =rA_2u_2-kB_2v_2
 =\ell,\qquad \ell\asymp L.                                \tag{13}
\]

Equivalently,

\[
 r(A_1u_1-A_2u_2)=k(B_1v_1-B_2v_2),                        \tag{14}
\]

together with either copy of the selector in (13).  The MD budget is

\[
 \sum_{\ell\asymp L}|E_{\rm III}(\ell)|^2
 \ll {H^2\over L}H^{o(1)}
 =H^{2-\rho+o(1)}.                                        \tag{15}
\]

All two-factor convolution coefficients are \(H^{o(1)}\) by the divisor
bound and will be suppressed.

For a fixed pair \(A,B\), put \(g=(rA,kB)\).  Since the left side of

\[
                         rAu-kBv=\ell                       \tag{16}
\]

is divisible by \(g\), a nonzero selected shift forces

\[
                              g\mid\ell.                     \tag{17}
\]

In particular, if the fixed support of the \(\ell\)-weight is contained in
\([L,2L]\), then

\[
                              g>2L\Longrightarrow0.          \tag{18}
\]

For \(g\le2L=o(P)\), each fixed admissible \(\ell\) has at most

\[
                         1+{Pg\over M}=1+{g\over P}=O(1)    \tag{19}
\]

solutions \(u,v\asymp P\), since solutions differ by
\((kB/g,rA/g)\).

## 2. Diagonal and proportional-base strata

The full product diagonal was evaluated in cycle 1:

\[
 p_1=p_2,\ q_1=q_2
 \quad\Longrightarrow\quad
 \mathcal D_{\rm product}\ll H^{1+\rho+o(1)}.               \tag{20}
\]

Cycle 2 allowed the third factors to move while keeping
\(A_1=A_2,B_1=B_2\), obtaining

\[
 \mathcal D_{\rm same\ base}\ll H^{4/3+\rho+o(1)}.          \tag{21}
\]

We now close the entire determinant-zero family

\[
                         D=A_1B_2-A_2B_1=0.                 \tag{22}
\]

Parameterize it by

\[
 A_1=sa,\quad B_1=sb,\quad A_2=ta,\quad B_2=tb,
 \qquad (a,b)=1.                                           \tag{23}
\]

Equation (13) becomes

\[
\begin{aligned}
 s(rau_1-kbv_1)&=\ell,\\
 t(rau_2-kbv_2)&=\ell.                                    \tag{24}
\end{aligned}
\]

Because \(\ell\ne0\), (24) forces \(s\mid\ell,t\mid\ell\), hence
\(s,t\le2L\).  For fixed \(\ell,s,t\), the ranges
\(sa,sb,ta,tb\asymp M\) contain

\[
                         \ll {M^2\over\max(s,t)^2}H^{o(1)} \tag{25}
\]

primitive pairs \(a,b\).  As \(a,b\asymp M/\max(s,t)\gg
P\), each line in (24) has \(O(1)\) points in the \(P\)-box.  Divisor
summation in \(s,t\mid\ell\) gives

\[
\begin{aligned}
 \mathcal D_{D=0}
 &\ll \sum_{\ell\asymp L}
 \sum_{s,t\mid\ell}{M^2\over\max(s,t)^2}H^{o(1)}\\
 &\ll M^2L\,H^{o(1)}
 =P^4L\,H^{o(1)}
 =H^{4/3+\rho+o(1)},                                      \tag{26}
\end{aligned}
\]

which proves the third row of (2).

## 3. A quantitative near-determinant band

Use the elementary determinant count

\[
 \#\{A_1,A_2,B_1,B_2\asymp M:
       0<|A_1B_2-A_2B_1|\le Z\}
 \ll M^{2+o(1)}Z.                                         \tag{27}
\]

For completeness, fix the nonzero determinant \(d\), remove the pairwise
gcds, and parameterize the resulting primitive \(2\times2\) matrices;
the divisor bound gives \(M^{2+o(1)}\) matrices for each \(d\).  Summing
\(1\le|d|\le Z\) gives (27).

For a fixed base quadruple, the first selected line in (13) contains at
most

\[
 (1+L/g_1)(1+g_1/P)\ll L H^{o(1)}                           \tag{28}
\]

points, and the second line at the same \(\ell\) has \(O(1)\) points by
(19).  Hence the band \(|D|\le Z\) contributes at most

\[
                         M^{2+o(1)}ZL.                      \tag{29}
\]

Choose

\[
                              Z={M\over L^2}.                \tag{30}
\]

Since \(M^3=P^6=H^2\), (29) becomes

\[
 M^2{M\over L^2}L\,H^{o(1)}
 ={H^2\over L}H^{o(1)},                                   \tag{31}
\]

exactly the MD budget.  This proves the fourth row of (2).

## 4. Gcd strata

Let \(g_\nu=(rA_\nu,kB_\nu)\).  Equation (18) removes
\(\max(g_1,g_2)>2L\) identically.

For fixed \(\ell\), the number of Type-III representations in one copy with
\(g\ge G\) is

\[
 \ll {P^3\over G}H^{o(1)}.                                 \tag{32}
\]

Indeed, for every divisor \(d\mid\ell,d\ge G\), write
\(A=dA',B=dB'\).  The equation

\[
                         rA'u-kB'v={\ell\over d}            \tag{33}
\]

has \(O(P^3/d)\) choices after summing \(u,v\asymp P\) and the
one-dimensional solution lattice in \(A',B'\); summing the
\(H^{o(1)}\) divisors of \(\ell\) proves (32).

If both copies have \(g_\nu\ge G\), their contribution to (15) is therefore

\[
                         \ll {P^6L\over G^2}H^{o(1)}.       \tag{34}
\]

Taking \(G=L\) gives

\[
                         {P^6L\over L^2}
                         ={H^2\over L},                     \tag{35}
\]

which closes the double-large-gcd row of (2).

The mixed range \(g_1\ge L>g_2\), as well as the fully small-gcd range, is
not closed by (32): the absolute estimate is \(H^2H^{o(1)}\), still a
factor \(L\) over (15).  These ranges are included in the generic survivor
(4).

## 5. Exact obstruction for absolute two-dispersion

Define \(\mathscr C_{\rm III}^{(2,\mathrm{abs})}\) to consist of arguments
which:

1. expand the centered Type-III moment (15) into two copies of (13);
2. separate the product diagonal, determinant bands, and gcd bands;
3. after this separation, take absolute values of the raw--raw,
   raw--zero-mode, and zero-mode--zero-mode pieces before recombining them;
4. use only lattice counts, divisor/gcd sums, and at most the two Poisson
   transforms of cycle 2.

The accepted \(h=0\) calculation says that the raw Type-III block has a
smooth zero mode of size

\[
                              \mathcal M(\ell)\asymp H H^{o(1)}
                                                                    \tag{36}
\]

on the selected shifts.  Centering writes

\[
 |E(\ell)|^2
 =|F(\ell)-\mathcal M(\ell)|^2
 =|F(\ell)|^2-2\Re(F(\ell)\overline{\mathcal M(\ell)})
  +|\mathcal M(\ell)|^2.                                  \tag{37}
\]

The cancellation among the three terms in (37) is precisely the
zero-frequency recombination.  Rule 3 of the class destroys it.  Each
resulting majorant has scale

\[
 \sum_{\ell\asymp L}|\mathcal M(\ell)|^2
 =H^2L\,H^{o(1)}.                                         \tag{38}
\]

The closed strata (20)--(35) do not contain the full zero-mode volume; it
lies in the generic range (4).  Comparing (38) with (15) gives the
unavoidable class loss

\[
 {H^2L\over H^2/L}=L^2=H^{2/1001},                         \tag{39}
\]

proving:

> **Absolute two-dispersion barrier.**  No argument in
> \(\mathscr C_{\rm III}^{(2,\mathrm{abs})}\) proves the Type-III MD
> estimate at any fixed \(\rho>0\).  At \(\rho=1/1001\), the exact missing
> exponent is \(2/1001\).

The conclusion is about the defined order of operations.  It says that the
next step must preserve the signed zero-mode recombination on the generic
stratum; it does not posit a new arithmetic conjecture.

## 6. Outside the class: reciprocity before the third difference

Return to the nonzero Poisson form from cycle 2:

\[
 {1\over P}\sum_{|z|\ll PL}\delta_z
 \sum_{a,b\asymp P^2}\alpha_a\beta_b
 e\!\left({z\bar a\over b}\right),\qquad (a,b)=1.           \tag{40}
\]

Additive reciprocity is the exact congruence

\[
                    {\bar a\over b}+{\bar b\over a}
                    \equiv {1\over ab}\pmod1.              \tag{41}
\]

Therefore

\[
\begin{aligned}
 e\!\left({z\bar a\over b}\right)
 &=e\!\left(-{z\bar b\over a}\right)e\!\left({z\over ab}\right)\\
 &=e\!\left(-{z\bar b\over a}\right)
   +O\!\left({|z|\over ab}\right),                         \tag{42}
\end{aligned}
\]

uniformly at (8).  Before cancellation, (40) has at most

\[
 {1\over P}\,(PL)(P^2)(P^2)H^{o(1)}
 =P^4L\,H^{o(1)}                                          \tag{43}
\]

weighted terms.  Since

\[
                         {|z|\over ab}\ll {PL\over P^4}
                         ={L\over P^3},                     \tag{44}
\]

the accumulated replacement error is

\[
 P^4L\,{L\over P^3}H^{o(1)}
 =PL^2H^{o(1)}
 =H^{1/3+2\rho+o(1)},                                     \tag{45}
\]

which proves (9)--(10).

Thus the generic phase can be symmetrized between the two HB sides before
any third Cauchy or difference:

\[
 e(z\bar a/b)\rightsquigarrow e(-z\bar b/a)                \tag{46}
\]

at a cost almost \(H^{2/3}\) below trace scale.  The arithmetic information
discarded by the killed class is now explicit: the two denominator readings
are the same signed observable up to the harmless Archimedean phase
\(e(z/ab)\), rather than two unrelated absolute-value blocks.

## 7. Handoff

* Closed: product diagonal, same bases, all \(D=0\), the determinant band
  \(0<|D|\le M/L^2\), double-large-gcd, and impossible gcds \(>2L\).
* Exact survivor: (4), the large-determinant generic range with at least one
  small gcd.
* Exact absolute two-dispersion loss: \(L^2=H^{2/1001}\).
* First calculation beyond that class: reciprocity replacement (42), with
  total error \(H^{1/3+2\rho+o(1)}=o(H)\).
* No support extension is claimed; the accepted floor remains
  \(0.96250068026-o(1)\).
