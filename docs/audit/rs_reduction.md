# Reduction of the block moment formula

## Status and source

The Rudnick--Sarnak reduction is verified for the Riemann zeta function and
for a block whose cyclic kernel is the flat bandwidth-\(\mu\) kernel defined
below.  The number-theoretic input is Theorem 3.1 of:

> Z. Rudnick and P. Sarnak, *Zeros of principal L-functions and random
> matrix theory*, Duke Math. J. **81** (1996), 269--322,
> DOI: 10.1215/S0012-7094-96-08115-6.

For degree \(m=1\), i.e. the zeta function, the theorem is unconditional and
does not assume RH.  Its restricted-support condition is

\[
 \Phi(\xi_1,\ldots,\xi_r)=0
 \quad\text{when}\quad
 \sum_{j=1}^r|\xi_j|>2-\varepsilon.
\tag{1}
\]

The calculation below identifies the block-moment integrals with the terms
in that theorem.  It does **not** construct the block as a principal
compression of the full matrix; that is the separate R1a dependency audited
in `r1a_power_complementary_partition.md`.

## 1. The cyclic block kernel

Use the Fourier convention \(e(x)=e^{2\pi i x}\) and set

\[
 K_\mu(x)
 :=\int_{-\mu/2}^{\mu/2}e(tx)\,dt
 =\frac{\sin(\pi\mu x)}{\pi x},
 \qquad K_\mu(0)=\mu.
\tag{2}
\]

The test function occurring after expansion of an \(r\)-th matrix trace is

\[
 F_{r,\mu}(x_1,\ldots,x_r)
 :=\prod_{a=1}^r K_\mu(x_a-x_{a+1}),
 \qquad x_{r+1}=x_1.
\tag{3}
\]

Introduce edge frequencies \(t_a\in[-\mu/2,\mu/2]\).  Expanding every
factor in (3) shows that the frequency at vertex \(a\) is

\[
 \xi_a=t_a-t_{a-1},\qquad t_0=t_r,
\tag{4}
\]

so \(\sum_a\xi_a=0\).  Given \(\xi\) on this hyperplane, put

\[
 s_0=0,\qquad s_a=\xi_1+\cdots+\xi_a
 \quad(1\le a<r).
\tag{5}
\]

All solutions of (4) have the form \(t_a=t_0+s_a\).  The allowed values of
\(t_0\) form the intersection of \(r\) intervals of length \(\mu\).  Hence
the cyclic Fourier symbol is exactly

\[
 \boxed{
 \Phi_{r,\mu}(\xi)
 =\left(\mu-max_{0\le a<r}s_a+min_{0\le a<r}s_a\right)_+.}
\tag{6}
\]

In particular,

\[
 \Phi_{r,\mu}(0)=\mu.
\tag{7}
\]

Equation (6) is the claimed cyclic block symbol.  It is a consequence of
the flat kernel (2), not of a scalar identity
\(\sum_j\varphi_j^2=v\).

## 2. Support check

On the support of (6), all \(t_a\) lie in a common interval of length
\(\mu\).  Therefore

\[
 \sum_{a=1}^r|\xi_a|
 =\sum_{a=1}^r|t_a-t_{a-1}|
 \le r\mu.
\tag{8}
\]

Thus (1) holds with a fixed margin whenever

\[
 r\mu<2.
\tag{9}
\]

For all moments through \(r=4\), the single condition \(\mu<1/2\) is
sufficient.  Smooth compactly supported approximations may be inserted before
applying Theorem 3.1; the strict inequality in (9) preserves the support
margin, and the flat symbols are recovered by the standard limiting
argument.

## 3. Rudnick--Sarnak specialization

Theorem 3.1, specialized to a translation-invariant \(r\)-variable test,
has one zero-frequency term and terms indexed by collections of disjoint
pairs.  After division by the block dimension \(\mu N+o(N)\), it gives

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
\tag{10}
\]

This is the block-moment formula.  It matches the trace expansion because
Theorem 3.1 sums over all zero tuples, with multiplicity, just as the matrix
trace does; no distinct-tuple correction has to be added.

Scaling \(v_a=\mu w_a\) in a \(q\)-pair term gives a factor
\(\mu^{1+2q}\) before the outer division by \(\mu\).  Consequently the
one-pair terms contribute in degree \(\mu^2\), and the two-pair terms in
degree \(\mu^4\).

## 4. The one-pair integral

For any pair \(i<j\), the partial sums in (5) take only the two values
\(0\) and \(v\).  At unit bandwidth,

\[
 \Phi_{r,1}(v(e_i-e_j))=(1-|v|)_+.
\tag{11}
\]

Therefore every one-pair term equals

\[
 \int_{\mathbb R}|v|(1-|v|)_+\,dv
 =2\int_0^1v(1-v)\,dv
 =\frac13.
\tag{12}
\]

There are \(1,3,6\) such terms for \(r=2,3,4\), respectively.

## 5. The two-pair integrals for \(r=4\)

There are three perfect matchings.

For \((12)(34)\), and likewise for \((14)(23)\), equation (6) gives

\[
 \Phi_{4,1}(v,-v,w,-w)
 =\left(1-\operatorname{range}\{0,v,w\}\right)_+.
\tag{13}
\]

In the two same-sign quadrants,

\[
 2\int_{0\le w\le v\le1}vw(1-v)\,dw\,dv
 =\frac1{20}
\tag{14}
\]

per quadrant.  In each opposite-sign quadrant,

\[
 \int_{\substack{a,b\ge0\\a+b\le1}}
 ab(1-a-b)\,da\,db
 =\frac1{120}.
\tag{15}
\]

Thus each of these two matchings contributes

\[
 2\cdot\frac1{20}+2\cdot\frac1{120}=\frac7{60}.
\tag{16}
\]

For the crossing matching \((13)(24)\), the partial sums are
\(0,v,v+w,w\), so their range is \(|v|+|w|\).  Hence

\[
\begin{aligned}
 &\int_{\mathbb R^2}|vw|
   (1-|v|-|w|)_+\,dv\,dw\\
 &\qquad=4\int_{\substack{a,b\ge0\\a+b\le1}}
   ab(1-a-b)\,da\,db
 =\frac1{30}.
\end{aligned}
\tag{17}
\]

The total two-pair coefficient is therefore

\[
 2\cdot\frac7{60}+\frac1{30}=\frac4{15}.
\tag{18}
\]

These are the block integrals corresponding to the elementary integrals in
Rudnick--Sarnak's Lemmas 4.2--4.3.

## 6. The first four moments

Substituting (7), (12), and (18) into (10) gives

\[
\begin{aligned}
 m_1(\mu)&=1,\\
 m_2(\mu)&=1+\frac{\mu^2}{3},\\
 m_3(\mu)&=1+\mu^2,\\
 m_4(\mu)&=1+2\mu^2+\frac{4\mu^4}{15}.
\end{aligned}
\tag{19}
\]

For \(Y=C-I\) and \(Z=Y/\mu\), (19) is equivalent to

\[
 \mathbb EZ=\mathbb EZ^3=0,
 \qquad
 \mathbb EZ^2=\frac13,
 \qquad
 \mathbb EZ^4=\frac4{15}.
\tag{20}
\]

## Audit conclusion

The number-theoretic reduction and all constants in (19)--(20) follow from
Rudnick--Sarnak Theorem 3.1 with \(m=1\), the explicit cyclic symbol (6), and
the constructed integrals (12)--(18).  The reduction is unconditional for
zeta under \(4\mu<2\).  Its application to the nested certificate remains
conditional on R1a supplying a principal block with symbol (6), rather than
only the zero-alias identity \(\sum_j\varphi_j^2=v\).
