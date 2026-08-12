# Root 95% cycle 3: closed-form quartic fixed point

## Result

Cycle 2 proved the stability inequality

\[
\sum_{i>b}(\lambda_i(C)-1)_+^2
\le s-(2-D_0)N,
\qquad b\le\frac{N-s}{2},
\tag{1}
\]

for every principal compression \(C\) of the support-
\(\sigma_0=1.499999\) matrix, with

\[
D_0=1.134325953.
\]

Applying one rational trimmed-moment certificate directly with the unknown
\(s\), rather than freezing \(b\) at the old lower bound and iterating,
gives

\[
\boxed{
\liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
\ge 0.8672327101131\ldots .}
\tag{2}
\]

## Exact dual polynomial

Keep the absolute-bandwidth principal block

\[
\mu=\frac{499}{1000}<\frac12,
\]

whose centered and scaled eigenvalue \(Z=(C-I)/\mu\) has moments

\[
\mathbb EZ=\mathbb EZ^3=0,
\qquad
\mathbb EZ^2=\frac13,
\qquad
\mathbb EZ^4=\frac4{15}.
\tag{3}
\]

Put

\[
a=-\frac{81}{100},
\qquad b_0=\frac8{55},
\qquad c=\frac{1027}{1000}.
\]

Let the quartic \(P\) and constant \(L\) be the unique rational solution of

\[
P(a)=P'(a)=0,
\quad P(b_0)=b_0^2,
\quad P'(b_0)=2b_0,
\quad P(c)=L,
\quad P'(c)=0.
\tag{4}
\]

Its coefficients are

\[
\begin{aligned}
p_0&=-\frac{2371761774702144}{175337011095659525},\\
p_1&= \frac{6467268805064496}{35067402219131905},\\
p_2&= \frac{7947849444403220}{21040441331479143},\\
p_3&=-\frac{260716671644000}{21040441331479143},\\
p_4&=-\frac{4472897011000000}{21040441331479143},\\
L&=\frac{703830875873538941}{2169788731719000000}.
\end{aligned}
\tag{5}

Exactly as in cycle 2,

\[
P(z)\le0\ (z\le0),
\qquad P(z)\le z^2\ (z\ge0),
\qquad P(z)\le L\ (z\ge0).
\tag{6}
\]

The differences factor by \((z-a)^2\), \((z-b_0)^2\), and
\((z-c)^2\), respectively.  The remaining quadratic for \(P\) has
negative leading coefficient and two positive roots; the other two
quadratics have positive leading coefficient and negative discriminant.

Define

\[
A=p_0+\frac{p_2}{3}+\frac{4p_4}{15}
=0.0556974628260\ldots .
\tag{7}
\]

If \(z=s/N\), at most

\[
\theta=\frac{1-z}{2\mu}
\]

of the small block can be removed as the \(b\) free positive directions.
The dual inequality therefore gives the charged energy

\[
\frac1N\sum_{i>b}(\lambda_i(C)-1)_+^2
\ge \mu^3(A-L\theta)
=\mu^3A-\frac{\mu^2L}{2}(1-z).
\tag{8}
\]

Insert (8) into the stability upper bound (1).  With

\[
c_0=\frac{\mu^2L}{2}=0.0403851742248\ldots,
\]

one obtains

\[
(1-c_0)z
\ge (2-D_0)+\mu^3A-c_0.
\tag{9}
\]

The right side is rational.  Division gives the exact certificate

\[
z\ge
\frac{35020104682575465786049152683}
     {40381438885077201583684516123}
=0.8672327101131853\ldots,
\]

which proves (2).  No numerical fixed-point assumption or additional
arithmetic input is present.

## Next operation

At the prospective support-\(<2\) cost, the same inequality has a much
smaller free-direction budget and supplies an increment of several tenths
of a percentage point.  The certificate is ready to transfer immediately
when the rebalanced signed-shift arithmetic is completed.
