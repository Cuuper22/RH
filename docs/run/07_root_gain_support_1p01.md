# Root construction cycle 1: an unconditional support-1.01 gain

## Terminal result

Take the two uploaded PDFs and their zero-side rank--trace certificate as
established.  Recombine the reciprocal cells before estimating, and apply the
quadratic-divisor estimate to the resulting signed smooth shift average, as in
arithmetic cycles 1--3.  At

\[
    \lambda=\frac{101}{100},\qquad X=T^\lambda,
    \qquad H=X/T=T^{1/100},
\]

the complete Heath--Brown family lies far inside the quadratic-divisor range.
With the explicit Montgomery--Taylor window

\[
                  v(s)=\cos(\sqrt2\,s),\qquad |s|\le \frac12,
\]

and the actual continued pair kernel

\[
                  K_\lambda(s,t)=\min(\lambda|s-t|,1),
\]

the normalized Frobenius cost is

\[
 \boxed{
 D_{1.01}(v)
 =\frac{\displaystyle \int v^2
       +\lambda\!\iint K_\lambda(s,t)v(s)v(t)\,ds\,dt}
      {\displaystyle \lambda\left(\int v\right)^2}
 =1.32075113693\ldots .}
\]

Consequently the accepted matrix inequality gives the unconditional bound

\[
 \boxed{
 \liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
 \ge 2-D_{1.01}(v)
 =0.67924886307\ldots .}
\]

This is a gain of

\[
             0.00674815937\ldots
\]

over the accepted (0.6725007037\ldots) constant.  No RH, Hardy--Littlewood
conjecture, or support-(1.43) estimate is used.

## Explicit numerical certificate

Put \(k=\sqrt2\).  The one-dimensional integrals are

\[
 I_1=\int_{-1/2}^{1/2}v(s)\,ds
     =\frac{2\sin(k/2)}{k}
     =0.9187253698655684\ldots,
\]

\[
 I_2=\int_{-1/2}^{1/2}v(s)^2\,ds
     =\frac12+\frac{\sin k}{2k}
     =0.8492279993183042\ldots .
\]

For (0\le d\le1), the autocorrelation is

\[
 A(d)=\int_{-1/2+d}^{1/2}v(s)v(s-d)\,ds
 =\frac{1-d}{2}\cos(kd)
  +\frac{\sin(k(1-d))}{2k}.
\]

Thus the only two-dimensional integral reduces exactly to

\[
 J_\lambda
 =2\lambda\int_0^{1/\lambda}dA(d)\,dd
  +2\int_{1/\lambda}^1 A(d)\,dd
 =0.27396852346630846\ldots .
\]

Substitution into

\[
                 D_\lambda(v)=
        \frac{I_2+\lambda J_\lambda}{\lambda I_1^2}
\]

gives the displayed constant.  The accepted compactly supported smooth taper
sequence converges to this window in all three integrals.  The numerical margin
(0.0067) permits fixing one sufficiently narrow taper once and for all; no
endpoint limit is needed in the theorem statement.

## Where the arithmetic closes

For the terminal arbitrary-coefficient quadratic-divisor block, use

\[
 A=B=H=T^\eta,\qquad M=N=T,\qquad \eta=\frac1{100}.
\]

In the corrected form of the quadratic-divisor proposition, the two errors are

\[
 E_A\ll T^{1/2+3\eta+\varepsilon},
 \qquad
 E_W\ll T^{3/4+2\eta+\varepsilon}.
\]

At \(\eta=1/100\), these are \(T^{0.53+\varepsilon}\) and
\(T^{0.77+\varepsilon}\), while the required trace grade is

\[
                         X=T^{1.01}.
\]

Both therefore have fixed power savings.  The remaining Heath--Brown blocks
are no worse, and the signed (h)-average is kept intact until the proposition
is applied; the factor-(H) loss from taking absolute values shift by shift is
never introduced.  The zero-frequency terms give the singular-series main
term, which is exactly the saturated kernel (K_\lambda) above.

## Input inventory

1. The uploaded paper's unconditional explicit-formula compression and
   rank--trace inequality.
2. A fixed-depth Heath--Brown identity for the von Mangoldt coefficient.
3. The published quadratic-divisor estimate in its strong
   (H\le(AB)^{1/2+\varepsilon}) range, applied to the recombined signed shift
   average.
4. Standard prime-number-theorem and prime-power cleanup already present in
   the accepted trace calculation.

There is no new unproved lemma in this cycle.  The stronger endpoint
(lambda\uparrow5/4) is handled separately; it is not needed for this strict
improvement.
