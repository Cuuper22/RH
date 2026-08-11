# Reduction of the block moment formula

## Status and primary source

The relevant number-theoretic input is Theorem 3.1 of:

> Z. Rudnick and P. Sarnak, *Zeros of principal L-functions and random
> matrix theory*, Duke Math. J. **81** (1996), 269--322,
> DOI: 10.1215/S0012-7094-96-08115-6.

The audited primary copy is the
[author-hosted PDF](https://www.math.tau.ac.il/~rudnick/papers/nlevelDuke.pdf),
SHA-256
`83010c4f68efc5f5628a71a589ff3a374220b25902384e9c1a34b3d6cd0834d6`.

The primary-source statement is the **smoothed** correlation theorem on
pp. 284--285.  Write \(e(x)=e^{2\pi i x}\), let
\(g_j\in C_c^\infty(\mathbb R)\), and put

\[
 h_j(r)=\int_{\mathbb R}g_j(u)e^{iru}\,du,
 \qquad
 \kappa(h)=\int_{\mathbb R}h_1(r)\cdots h_n(r)\,dr.
\]

For an automorphic principal \(L\)-function of degree \(m\), Rudnick--Sarnak
set \(L=m\log T\).  If \(\Phi\in C_c^1(\mathbb R^n)\) is supported in

\[
 \sum_{j=1}^n |\xi_j|<\frac2m
\tag{1}
\]

and

\[
 f(x)=\int_{\mathbb R^n}\Phi(\xi)
       \delta(\xi_1+\cdots+\xi_n)e(-x\mathbin\cdot\xi)\,d\xi,
\]

then their equations (3.8)--(3.9) say

\[
\begin{aligned}
 &\sum_{\gamma_1,\ldots,\gamma_n}
   \prod_{j=1}^n h_j(\gamma_j/T)\,
   f\!\left(\frac{L\gamma_1}{2\pi},\ldots,
            \frac{L\gamma_n}{2\pi}\right) \\
 &\quad=\kappa(h)\frac{TL}{2\pi}
 \Bigg[\Phi(0)+
  \sum_{q=1}^{\lfloor n/2\rfloor}
  \sum_{\substack{q\text{ disjoint pairs}\\i(a)<j(a)}}
  \int_{\mathbb R^q}\prod_{a=1}^q|v_a|\,
  \Phi\!\left(\sum_{a=1}^qv_a(e_{i(a)}-e_{j(a)})\right)d\mathbf v
 \Bigg]+O(T).
\end{aligned}
\tag{2}
\]

The sum in (2) is over all ordered zero tuples, **not** only distinct tuples.
Zeros are counted with multiplicity.  This matches the multiplicities arising
when a matrix trace is expanded.  Without RH, the numbers \(\gamma\) defined
by \(\rho=1/2+i\gamma\) may be complex; the compact Fourier support makes the
test function entire in the required variables.

For the Riemann zeta function \(m=1\), so \(L=\log T\) and (1) is the strict
support condition \(\sum|\xi_j|<2\).  Proposition 2.4, p. 283, says that the
paper's technical Hypothesis H is trivial for \(m=1\).  Thus Theorem 3.1 in
this specialization is unconditional and does not assume RH.  Since
\(\Phi\) has compact support in the open set (1), it is equivalent in an
application to exhibit a fixed \(\varepsilon>0\) for which
\(\Phi=0\) when \(\sum|\xi_j|>2-\varepsilon\).

Rudnick--Sarnak Theorem 3.2 is different: it replaces the smooth height
weights by sharp/unsmoothed zero sums and **explicitly assumes RH**.  It may
not be used in an unconditional rung.  Any sharp-height block application of
Theorem 3.1 therefore needs its own smoothing and limiting argument.

The calculations below verify the cyclic symbols and contraction integrals
on the right side of (2).  They do **not** by themselves prove that the
finite distinguished block in the rung construction has those moments.  The
principal-compression construction is the separate R1a dependency audited in
`r1a_power_complementary_partition.md`; the finite-grid and height-smoothing
passage is R1b.

## What RS Lemmas 4.2--4.3 actually say

Let

\[
 K(x)=\frac{\sin \pi x}{\pi x},\qquad K(0)=1,
 \qquad f_2=\mathbf 1_{[-1/2,1/2]}.
\]

Lemma 4.2, p. 310, is the distributional Fourier identity

\[
\begin{aligned}
 &\int_{\mathbb R^m}K(x_1-x_2)\cdots K(x_m-x_1)
       e(u_1x_1+\cdots+u_mx_m)\,d\mathbf x\\
 &\quad=\delta(u_1+\cdots+u_m)
   \int_{\mathbb R}f_2(v)f_2(v+u_1)\cdots
      f_2(v+u_1+\cdots+u_{m-1})\,dv.
\tag{3}
\end{aligned}
\]

The translation direction on the left of (3) produces the Dirac delta.  A
Lean statement should fix one spatial coordinate, integrate the remaining
\(m-1\) coordinates, and state the coefficient of the delta as an ordinary
integral.  Treating the full left side as an ordinary Bochner integral would
not be a faithful rendering.

Lemma 4.3, p. 312, says that if

\[
 u_1+\cdots+u_m=0,\qquad \sum_j|u_j|<2,
\]

and \(s_k=u_1+\cdots+u_k\), \(M=\max s_k\),
\(m_0=\min s_k\), \(V=M-m_0\), then

\[
 \int_{\mathbb R}f_2(v)f_2(v+u_1)\cdots
 f_2(v+u_1+\cdots+u_m)\,dv=1-V.
\tag{4}
\]

Its proof is the length of the intersection of the translated intervals.
These lemmas identify the flat cyclic sinc symbol.  They do **not** state the
nonflat formula (18) below, and they do not state the numerical integrals
\(1/3\), \(7/60\), or \(1/30\).  Those are separate elementary calculations.

## 1. The flat cyclic block kernel

Set

\[
 K_\mu(x)
 :=\int_{-\mu/2}^{\mu/2}e(tx)\,dt
 =\frac{\sin(\pi\mu x)}{\pi x},
 \qquad K_\mu(0)=\mu.
\tag{5}
\]

The test function after expansion of an \(r\)-th matrix trace is

\[
 F_{r,\mu}(x_1,\ldots,x_r)
 :=\prod_{a=1}^r K_\mu(x_a-x_{a+1}),
 \qquad x_{r+1}=x_1.
\tag{6}
\]

Introduce edge frequencies \(t_a\in[-\mu/2,\mu/2]\).  Expansion of (6)
gives

\[
 \xi_a=t_a-t_{a-1},\qquad t_0=t_r,
\tag{7}
\]

so \(\sum_a\xi_a=0\).  Put

\[
 s_0=0,\qquad s_a=\xi_1+\cdots+\xi_a
 \quad(1\le a<r).
\tag{8}
\]

All solutions of (7) have the form \(t_a=t_0+s_a\).  The allowed values of
\(t_0\) form the intersection of \(r\) intervals of length \(\mu\).  Hence

\[
 \boxed{
 \Phi_{r,\mu}(\xi)
 =\left(\mu-\max_{0\le a<r}s_a+\min_{0\le a<r}s_a\right)_+.}
\tag{9}
\]

In particular, \(\Phi_{r,\mu}(0)=\mu\).  This is a consequence of the
kernel (5), not of the scalar zero-alias identity
\(\sum_j\varphi_j^2=v\).

## 2. Flat support check

On the support of (9), all \(t_a\) lie in a common interval of length
\(\mu\).  Therefore

\[
 \sum_{a=1}^r|\xi_a|
 =\sum_{a=1}^r|t_a-t_{a-1}|
 \le r\mu.
\tag{10}
\]

The RS support condition has a fixed margin whenever \(r\mu<2\).  Thus the
single condition \(\mu<1/2\) suffices for all moments through \(r=4\).

## 3. Formal RS contraction specialization

If R1a and R1b identify a finite block of dimension
\(\mu N+o(N)\) with the cyclic test (6), normalize the height factor in
(2), and make all end errors \(o(N)\), then (2), divided by that dimension,
gives

\[
\begin{aligned}
 m_r(\mu)
 =\frac1\mu\Bigg[
 &\Phi_{r,\mu}(0)\\
 &+\sum_{q=1}^{\lfloor r/2\rfloor}
   \sum_{\substack{(i_1,j_1),\ldots,(i_q,j_q)\\
                   \text{disjoint unordered pairs}}}
   \int_{\mathbb R^q}
   \prod_{a=1}^q|v_a|\,
   \Phi_{r,\mu}\!\left(
      \sum_{a=1}^qv_a(e_{i_a}-e_{j_a})
   \right)
   d\mathbf v
 \Bigg].
\end{aligned}
\tag{11}
\]

The qualification in the preceding sentence is essential: equation (11) is
the verified specialization of the RS main term, not yet a proved theorem
about the repository's finite distinguished block.

Scaling \(v_a=\mu w_a\) in a \(q\)-pair term gives a factor
\(\mu^{1+2q}\) before division by \(\mu\).  One-pair terms therefore have
degree \(\mu^2\), and two-pair terms degree \(\mu^4\).

## 4. Flat one-pair integral

For any pair \(i<j\), the partial sums take only \(0\) and \(v\).  At unit
bandwidth,

\[
 \Phi_{r,1}(v(e_i-e_j))=(1-|v|)_+.
\]

Thus every one-pair term is

\[
 \int_{\mathbb R}|v|(1-|v|)_+\,dv
 =2\int_0^1v(1-v)\,dv
 =\frac13.
\tag{12}
\]

There are \(1,3,6\) such terms for \(r=2,3,4\), respectively.

## 5. Flat two-pair integrals for \(r=4\)

There are three perfect matchings.  For \((12)(34)\), and likewise for
\((14)(23)\),

\[
 \Phi_{4,1}(v,-v,w,-w)
 =\left(1-\operatorname{range}\{0,v,w\}\right)_+.
\tag{13}
\]

The same-sign and opposite-sign quadrant integrals are

\[
 2\int_{0\le w\le v\le1}vw(1-v)\,dw\,dv=\frac1{20},
\tag{14}
\]

and

\[
 \int_{\substack{a,b\ge0\\a+b\le1}}
 ab(1-a-b)\,da\,db=\frac1{120}.
\tag{15}
\]

Each of these two matchings contributes

\[
 2\cdot\frac1{20}+2\cdot\frac1{120}=\frac7{60}.
\tag{16}
\]

For the crossing matching \((13)(24)\), the partial sums are
\(0,v,v+w,w\), so

\[
 \int_{\mathbb R^2}|vw|(1-|v|-|w|)_+\,dv\,dw
 =\frac1{30}.
\tag{17}
\]

The total two-pair coefficient is

\[
 2\cdot\frac7{60}+\frac1{30}=\frac4{15}.
\tag{18-flat}
\]

These values are constructed directly from (9); they are not constants
quoted from Lemmas 4.2--4.3.

## 6. Flat first four moments

Substitution into (11) gives

\[
\begin{aligned}
 m_1(\mu)&=1,\\
 m_2(\mu)&=1+\frac{\mu^2}{3},\\
 m_3(\mu)&=1+\mu^2,\\
 m_4(\mu)&=1+2\mu^2+\frac{4\mu^4}{15}.
\end{aligned}
\tag{19}
\]

For \(Y=C-I\) and \(Z=Y/\mu\), these become

\[
 \mathbb EZ=\mathbb EZ^3=0,
 \qquad
 \mathbb EZ^2=\frac13,
 \qquad
 \mathbb EZ^4=\frac4{15}.
\tag{20}
\]

The constants in (19)--(20) are unchanged.  Their use for a finite principal
block remains subject to R1a and R1b.

## 7. R3: the nonflat cyclic symbol and file-24 formula (18)

Let \(I=[-1/2,1/2]\), extend \(r\) by zero outside \(I\), and assume

\[
 r\ge0,\qquad \int_I r(x)\,dx=1.
\tag{21}
\]

Define the weighted bandwidth-\(\mu\) kernel

\[
 K_{\mu,r}(x)=\mu\int_Ir(t)e(\mu tx)\,dt.
\tag{22}
\]

For a \(k\)-cycle, put \(s_0=0\) and
\(s_a=\xi_1+\cdots+\xi_a\).  Direct expansion of (22) gives the cyclic
Fourier symbol

\[
 \boxed{
 \Phi_{k,\mu,r}(\xi)
 =\mu\int_{\mathbb R}
   \prod_{a=0}^{k-1}r\!\left(x+\frac{s_a}{\mu}\right)dx.}
\tag{23}
\]

Consequently

\[
 \Phi_{k,\mu,r}(0)=\mu\int_Ir(x)^k\,dx,
 \qquad
 \operatorname{supp}\Phi_{k,\mu,r}
 \subseteq\left\{\xi:\sum_a|\xi_a|\le k\mu\right\}.
\tag{24}
\]

For a smooth compactly supported \(r\), equation (23) is an admissible RS
test whenever \(k\mu<2\).  A nonsmooth top hat must be obtained only after a
separate smooth limiting argument.

Define

\[
 h(x)=\int_I|x-y|r(y)\,dy
\tag{25}
\]

and

\[
 \mathcal X(r)=
 \iiint_{\substack{x,y,z\in I\\x+z-y\in I}}
 |x-y||y-z|r(x)r(y)r(z)r(x+z-y)\,dx\,dy\,dz.
\tag{26}
\]

Applying the contraction main term (2) to (23), with the R1a/R1b bridge
still understood, gives the uncentered moments

\[
\begin{aligned}
 c_1={}&\int r,\\
 c_2={}&\int r^2+\mu^2\int rh,\\
 c_3={}&\int r^3+3\mu^2\int r^2h,\\
 c_4={}&\int r^4+4\mu^2\int r^3h
 +2\mu^2\iint_{I^2}|x-y|r(x)^2r(y)^2\,dx\,dy\\
 &\quad+2\mu^4\int r^2h^2+\mu^4\mathcal X(r).
\end{aligned}
\tag{27}
\]

The coefficients in \(c_4\) have an explicit contraction construction:

- the four adjacent one-pairs give \(4\int r^3h\);
- the two opposite one-pairs give the coefficient \(2\) of the
  \(r(x)^2r(y)^2\) integral;
- \((12)(34)\) and \((14)(23)\) each give \(\int r^2h^2\);
- the crossing matching \((13)(24)\) gives \(\mathcal X(r)\).

Let \(q=r-1\), set \(c_0=1\), and center by

\[
 M_j=\sum_{a=0}^j(-1)^{j-a}\binom ja c_a.
\tag{28}
\]

Expanding (28) in (27) gives exactly formula (18) of
`24_TERMINAL_certificate95_cycle2_95p063832.md`:

\[
\boxed{\begin{aligned}
 M_1&=\int_Iq,\\
 M_2&=\int_Iq^2+\mu^2\int_Irh,\\
 M_3&=\int_Iq^3+3\mu^2\int_Iqrh,\\
 M_4&=\int_Iq^4+4\mu^2\int_Iq^2rh\\
 &\quad+2\mu^2\iint_{I^2}q(x)r(x)q(y)r(y)|x-y|\,dx\,dy\\
 &\quad+2\mu^4\int_Ir(x)^2h(x)^2\,dx+\mu^4\mathcal X(r).
\end{aligned}}
\tag{18}
\]

For \(r=1\), (18) reduces to (20):

\[
 \int_Irh=\frac13,
 \qquad
 \int_Ir^2h^2=\frac7{60},
 \qquad
 \mathcal X(r)=\frac1{30}.
\]

Thus R3 is a full algebraic specialization of the RS disjoint-pair main
term once the weighted symbol (23) is supplied.  It is not a verbatim
consequence of RS Lemmas 4.2--4.3, and it is not yet the R1b theorem relating
that main term to the finite block.

## 8. Correct R1b source mapping

There is no \(k=2\) trace passage in `Zeta23/Taper.lean`.  That file is an
umbrella for one-variable taper, Fourier, and decay facts.  The reusable
repository results are:

- `Zeta23/Poisson.lean`, lines 345--364:
  `Taper.hasSum_phiHatR_mul`, the bilinear infinite-grid Poisson identity;
- `Zeta23/Poisson.lean`, lines 366--400: its diagonal-square specialization
  and the `Params` facade;
- `Zeta23/PrimeSideA/EndsCore.lean`, lines 259--321: the \(k=2\) trace
  expansion, Fubini justification, and finite/infinite-kernel decomposition.

For \(k\le4\), the intended extension is to expand

\[
 \operatorname{tr}G^k
 =\sum_{i_1,\ldots,i_k}G_{i_1i_2}\cdots G_{i_ki_1},
\]

interchange the finite grid sums with the zero or density sums, and apply the
bilinear Poisson identity at every grid vertex.  The infinite-grid expression
then becomes a cyclic product of \(k\) kernels.  The existing \(k=2\) file
does not prove the \(k=3,4\) interchange or end estimates.

Moreover, `Taper.hasSum_phiHatR_mul` is currently stated only for real
arguments.  Expanding `ZeroConfig.Gz` off RH evaluates the Fourier transforms
at complex \(\gamma_\rho\).  R1b therefore needs either a complex-argument
Poisson theorem with locally uniform summability or a different rigorous
bridge to the real prime-side matrix.

## 9. Exact remaining formal blockers

1. **Published input interface -- stated, not instantiated.**
   `RH/Zeta85/Inputs95.lean` now defines the gauge-fixed all-tuples test,
   disjoint-pair main term, height factor, and multiplicity-weighted tuple
   sum.  `RS1996ZetaInputs.theorem31` transcribes Theorem 3.1 with its exact
   \(O(T)\), strict support, smoothness, summability, and multiplicity clauses.
   It remains a Prop field with no constructed instance.

2. **Dirac-delta rendering -- interface discharged.**  `rsZeroSumLift` and
   `rsGaugeTest` eliminate one coordinate explicitly; the delta is not
   interpreted as an ordinary Bochner integral.  Applying the published
   field to the terminal tests remains part of the R1b derivation.

3. **R1a block identification.**  The scalar identity
   \(\sum_j\varphi_j^2=v\) still does not construct a distinguished finite
   principal block with cyclic symbol (23).

4. **Complex Poisson extension.**  The existing Poisson theorem covers real
   arguments only, whereas off-line zeros give complex \(\gamma_\rho\).
   `BlockMomentLimits` now exposes the exact missing statement: summability
   and cancellation of the complex alias family at every pair of actual
   zeros in `ZIprime T`.  No proof or instance is supplied.

5. **Higher finite-grid errors.**  Absolute convergence, Fubini, and
   \(o(N)\) end errors exist only for the second trace.  They must be proved
   for the third and fourth cyclic traces.

6. **Height smoothing.**  The unconditional RS theorem is smoothed.  A fixed
   smooth height envelope has factors
   \(\kappa_k=\int h(r)^k\,dr\), which need not agree for different \(k\).
   Recovering the common moment normalization requires a proved simultaneous
   limit \(\kappa_k\to1\) for \(1\le k\le4\).  Theorem 3.2 cannot supply it
   unconditionally because it assumes RH.

7. **Normalization bridge.**  The repository uses
   \(\ell(T)=\log(T/2\pi)\), while RS uses \(\log T\).  The effective
   bandwidth is \(\mu_T=\mu\ell(T)/\log T\to\mu\); support and every moment
   limit must carry this explicitly.

8. **Smooth profile and ordered limits.**  A top hat does not give the
   \(C_c^1\) test required by Theorem 3.1.  One must first fix a smooth
   admissible \(r_{p,\eta}\), take \(T\to\infty\), and only then take
   \(\eta\to0\), using a strict pointwise admissibility margin and dominated
   convergence for every term in (18).  No uniform \(O(T)\) in \(\eta\) may
   be assumed without proof.

9. **Machine-checked contraction algebra -- scalar layer discharged.**
   `TopHatMoments.lean` proves the formula-(21) scalar contractions, including
   the determinant-one crossing reduction, and `TrimmedMoment.lean` proves
   the terminal quartic algebra.  The remaining blocker is the actual
   finite-grid/block limit recorded by `BlockMomentLimits.moments`, not a
   missing scalar integral.

## Audit conclusion

The primary-source theorem needed for R3 is genuinely unconditional for
zeta at strict total Fourier support below \(2\), and its all-tuples convention
has the correct multiplicity semantics.  The flat constants
\(1/3,7/60,1/30,4/15\) and the weighted algebra leading to file-24 formula
(18) have explicit constructions above; no constant is being attributed to
RS without that construction.

What is verified at present is the RS main-term specialization and the
finite-dimensional contraction calculation.  Application to the nested
certificate remains conditional on the exact blockers in Section 9,
especially R1a, complex Poisson, the \(k=3,4\) finite-grid estimates, and the
unconditional height-smoothing limit.  A contradiction arising after
assuming any of those bridges would indict that bridge, not establish a
headline rung.
