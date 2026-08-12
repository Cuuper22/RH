# Certificate 95, cycle 1: saturated threshold and the nested-quartic gain

## Outcome

Write

\[
 K(x)=\min(|x|,1),\qquad
 D_\sigma=\min_{\substack{u\geq0,\;\operatorname{supp}u\subset[-\sigma/2,\sigma/2]\\
                                  \int u=1}}
 \left\{\int u^2+\iint K(x-y)u(x)u(y)\,dx\,dy\right\}.
 \tag{1}
\]

There are three quantitative conclusions.

1. A saturated-pair-trace certificate by itself reaches \(95\%\) at

   \[
   \boxed{\sigma_{95}^{(2)}=2.26079256254958\ldots,\qquad
          D_{\sigma_{95}^{(2)}}=1.05.}
   \tag{2}
   \]

2. A nested block of absolute bandwidth \(\mu<1/2\), using only its
   unconditional fourth moment, lowers the required saturated-pair support to

   \[
   \boxed{\sigma_{95}^{(2+4)}=2.14233794449584\ldots.}
   \tag{3}
   \]

   Thus the mixed/higher-trace certificate saves
   \(0.11845461805374\ldots\) units of pair support.  At the prospective
   endpoint \(\sigma=2\) it would already give

   \[
   \frac{N_{0,\mathrm{simple}}}{N}\geq
   0.93831332705095\ldots .
   \tag{4}
   \]

3. At the presently accepted support endpoint \(\sigma\uparrow3/2\), the
   same construction is unconditional and kills the stated equality
   adversary.  In the limit \(\mu\uparrow1/2\),

   \[
   \boxed{
   \liminf_{T\to\infty}\frac{N_{0,\mathrm{simple}}(T,2T)}{N(T,2T)}
   \geq0.86725400194550\ldots .}
   \tag{5}
   \]

   This is a strict increment over
   \(0.865674254456636\ldots\), without extending the accepted prime-pair
   support.  For the fixed strict choice \(\mu=.499\), the corresponding
   number is \(0.867232931186429\ldots\).

The input beyond the accepted support theorem is an exact nested principal
compression.  Its fourth trace has total Fourier support \(4\mu<2\), so no
new prime-pair or Hardy--Littlewood input occurs.

## 1. Exact saturated-kernel threshold

The Euler equation for (1) is

\[
 u(x)+\int K(x-y)u(y)\,dy=C.                                  \tag{6}
\]

For \(2<\sigma<3\), put

\[
 r=\frac{\sigma-2}{2},\qquad a=1+r,qquad
 \omega_\pm=\sqrt{2\pm\sqrt2}.
\tag{7}
\]

The even solution of (6) is elementary.  On the positive half-interval write

\[
\begin{aligned}
u_0(x)&=\sqrt2 A\cos(\omega_-x)-\sqrt2 B\cos(\omega_+x),
 &&0\leq x\leq r,\\
u_1(x)&=D\cos(x-\tfrac12)+E\sin(\sqrt3(x-\tfrac12)),
 &&r\leq x\leq1-r,\\
u_2(1-x)&=A\cos(\omega_-x)+B\cos(\omega_+x)-C_0\sin(\sqrt2x),
 &&0\leq x\leq r,\\
u_2(1+x)&=A\cos(\omega_-x)+B\cos(\omega_+x)+C_0\sin(\sqrt2x),
 &&0\leq x\leq r.
\end{aligned}                                                   \tag{8}
\]

The five coefficients are determined up to common scale by the four matching
conditions

\[
\begin{aligned}
u_0(r)&=u_1(r),&u_0'(r)&=u_1'(r),\\
u_2(1-r)&=u_1(1-r),&u_2'(1-r)&=u_1'(1-r).
\end{aligned}                                                   \tag{9}
\]

This is the explicit solution of the delay equation obtained by differentiating
(6) twice,

\[
 u''(x)+2u(x)-u(x-1)-u(x+1)=0,                                \tag{10}
\]

where \(u\) is extended by zero outside \([-a,a]\).  In the central interval,
the three coupled functions \(u(x),u(1+x),u(1-x)\) have frequencies
\(\omega_-,\omega_+,\sqrt2\); in the middle interval the reflection equation
has frequencies \(1,\sqrt3\).  Thus (8)--(9) are not a discretization.

For any nonzero solution of (9),

\[
 D_\sigma=
 \frac{u(0)+2\int_0^1xu(x)\,dx+2\int_1^a u(x)\,dx}
      {2\int_0^a u(x)\,dx}.                                  \tag{11}
\]

The solution is positive in the range used here.  Solving
\(D_\sigma=1.05\) in (11) gives (2).  For reference,

\[
 D_2=1.067717376064704\ldots .                                \tag{12}
\]

## 2. Stability version of the simple-zero inequality

Normalize the full matrix by

\[
 \operatorname{tr}G=N,\qquad \|G\|_F^2\leq DN.                \tag{13}
\]

On the zero side use the accepted decomposition

\[
G=P+Q,quad P\succeq0,quad \operatorname{rank}P\leq s,quad
\operatorname{tr}P\leq s,\qquad n_+(Q)\leq b,\qquad s+2b\leq N. \tag{14}
\]

Write \(Q=Q_+-Q_-\) and \(R=P-Q_-\).  Since
\(\operatorname{rank}Q_+\leq b\), Weyl interlacing gives

\[
 \lambda_{b+j}(G)\leq\lambda_j(R).                            \tag{15}
\]

Moreover \(n_+(R)\leq s\), and hence

\[
\sum_{i>b}(\lambda_i(G)-1)_+^2
 \leq\sum_j(\lambda_j(R)-1)_+^2
 \leq\|R\|_F^2-2\operatorname{tr}R+s.                        \tag{16}
\]

The rank--trace slack controls the last expression.  Indeed,

\[
\begin{aligned}
&\|G\|_F^2-4\operatorname{tr}G+3s+4b
 -(\|R\|_F^2-2\operatorname{tr}R+s)\\
&=\|Q_+\|_F^2-4\operatorname{tr}Q_++4b
 +2\operatorname{tr}(PQ_+)+2\operatorname{tr}Q_-
 +2(s-\operatorname{tr}P)\geq0.                              \tag{17}
\end{aligned}
\]

The first group on the second line is
\(\sum(q_j-2)^2+4(b-\operatorname{rank}Q_+)\).  If

\[
 \frac{s}{N}=2-D+\varepsilon,                                 \tag{18}
\]

then \(b\leq(N-s)/2\), (13), and (16)--(17) give

\[
 \boxed{
 \frac1N\sum_{i>b}(\lambda_i(G)-1)_+^2\leq\varepsilon.}
\tag{19}
\]

For every principal compression \(C\) of \(G\), ordinary compression
interlacing transfers (19) to \(C\).  This is the stability information absent
from the unrefined two-trace count.

## 3. The exact trimmed four-moment problem

Take a nested compression of absolute bandwidth \(\mu<1/2\), of dimension
\(\mu N+o(N)\), in mean-one normalization.  Put

\[
 Y=C-I,\qquad Z=Y/\mu.                                        \tag{20}
\]

Because \(4\mu<2\), its accepted diagonal moments are

\[
 \mathbb E1=1,qquad \mathbb EZ=\mathbb EZ^3=0,qquad
 \mathbb EZ^2=\frac13,qquad \mathbb EZ^4=\frac4{15}.         \tag{21}
\]

The \(b\) exceptional positive directions in (19) may remove a fraction

\[
 \alpha=\frac{b}{\mu N}leq
 \frac{D-1-\varepsilon}{2\mu}                                \tag{22}
\]

of the block law.  Define the sharp residual

\[
 \mathcal L_\mu(\alpha)=\mu^3
 \inf_{\rho,\,0\leq\nu\leq\rho}
 \left\{\int_{z>0}z^2\,d(\rho-\nu):
 \begin{array}{l}
  \rho\text{ has moments }(21),\\
  \nu\text{ is supported on }z>0,\ \nu(\mathbb R)\leq\alpha
 \end{array}\right\}.                                      \tag{23}
\]

Its polynomial dual is

\[
\mathcal L_\mu(\alpha)=\mu^3\sup_{p,\ell\geq0}
 \left(p_0+\frac{p_2}{3}+\frac{4p_4}{15}-\alpha\ell\right),  \tag{24}
\]

where \(p(z)=\sum_{0}^{4}p_jz^j\) satisfies

\[
 p(z)\leq0\ (z\leq0),qquad
 p(z)\leq z^2\ (z\geq0),qquad
 p(z)\leq\ell\ (z\geq0).                                   \tag{25}
\]

There is an exact three-atom primal and dual solution.  Given the mass
\(q=\alpha\) and the high positive atom \(t\), set

\[
\begin{array}{lll}
A=1-q,&B=-qt,&C=\frac13-qt^2,\\
F=-qt^3,&E=\frac4{15}-qt^4,&H=AC-B^2,
\end{array}                                                   \tag{26}
\]

and

\[
 S=\frac{AF-BC}{H},\qquad P=\frac{BF-C^2}{H}.                 \tag{27}
\]

The two untrimmed atoms \(a<c\) are the roots of
\(x^2-Sx+P=0\).  The fourth-moment equation determining \(t\) is

\[
 \boxed{EH=AF^2-2BCF+C^3.}                                   \tag{28}
\]

Their masses are

\[
 u=\frac{c(1-q)+qt}{c-a},\qquad v=1-q-u,                     \tag{29}
\]

and

\[
 \mathcal L_\mu(q)=\mu^3vc^2.                               \tag{30}
\]

For the matching dual, \(p\) and \(\ell\) are uniquely defined by

\[
\begin{array}{lll}
p(a)=p'(a)=0,&p(c)=c^2,&p'(c)=2c,\\
p(t)=\ell,&p'(t)=0.&
\end{array}                                                   \tag{31}
\]

The inequalities (25) are global: \(p\), \(z^2-p\), and \(\ell-p\) have,
respectively, the double roots \(a,c,t\); the remaining quadratic factor of
\(p\) has its other roots positive, while the remaining quadratic factors of
\(z^2-p\) and \(\ell-p\) have positive leading coefficient and negative
discriminant.  Equations (28)--(31) therefore give both primal and dual
equality, not merely a numerical LP value.

Combining (19), (22), and (23) gives the fixed-point certificate

\[
 \boxed{
 \varepsilon\geq
 \mathcal L_\mu\!\left(\frac{D-1-\varepsilon}{2\mu}\right).}
\tag{32}
\]

On the relevant contact branch the derivative of the right side is
\(\mu^2\ell/2<1\), so (32) forces \(\varepsilon\) to be at least its unique
fixed point.

## 4. Killing the support-\(3/2\) equality adversary

At the accepted endpoint,

\[
D_{3/2}=1.134325745543364\ldots,\quad
s_0=2-D_{3/2}=0.865674254456636\ldots,                         \tag{33}
\]

\[
d_0=\frac{D_{3/2}-1}{2}=0.067162872771682\ldots.              \tag{34}
\]

Thus the proposed \(0/1/2\) adversary has only \(d_0N\) directions above
one available to absorb the positive centered spectrum of the small block.
For the strict block \(\mu=.499\), the fixed point of (32) is

\[
\begin{aligned}
\varepsilon&=0.001558676729793\ldots,\\
q&=0.133033135083739\ldots,\\
(a,c,t)&=(-0.809603185273756,\ 0.145599572823942,\\
          1.027286763622529),\\
(u,v,q)&=(0.275222387865178,\ 0.591744477051083,\\
          0.133033135083739).
\end{aligned}                                                  \tag{35}
\]

One corresponding dual is

\[
\begin{aligned}
p(z)={}&-0.013543946074091
 +0.184472105677702z+0.378188135429298z^2\\
&-0.012156619518572z^3-0.212846589791075z^4,\\
\ell={}&0.324844968207806.
\end{aligned}                                                  \tag{36}
\]

It is certified globally by the factor test following (31).  Letting
\(\mu\uparrow1/2\) through strict values gives

\[
\varepsilon_{3/2}=0.001579747488868\ldots                     \tag{37}
\]

and hence (5).  The equality adversary is therefore infeasible for the joint
two-trace plus nested-quartic constraint family.

## 5. How much the quartic block lowers the 95% support

For a target simple proportion \(s=0.95\), the non-simple positive-index
budget is at most \(0.025N\).  At \(\mu\uparrow1/2\), this is precisely the
trim fraction

\[
 \alpha_{95}=0.05.                                            \tag{38}
\]

Solving (28)--(31) at \(q=.05,\mu=.5\) gives

\[
\begin{aligned}
(a,c,t)&=(-0.736326224857611,\ 0.307620032266044,\\
          1.33772573\ldots),\\
\mathcal L_{1/2}(.05)&=0.007168140450802\ldots .
\end{aligned}                                                  \tag{39}
\]

Consequently the pair trace may have cost as large as

\[
 D_{95}^{(2+4)}=1.05+\mathcal L_{1/2}(.05)
 =1.057168140450802\ldots,                                    \tag{40}
\]

instead of \(1.05\).  Solving \(D_\sigma=D_{95}^{(2+4)}\) using
(8)--(11) gives (3).

At \(\sigma=2\), equations (12) and (32), with
\(\mu\uparrow1/2\), give

\[
\varepsilon_2=0.006030703115653\ldots,qquad
2-D_2+\varepsilon_2=0.938313327050949\ldots,                  \tag{41}
\]

which quantifies the intermediate checkpoint.

## Terminal handoff

The direct saturated-kernel target for \(95\%\) is support
\(2.26079256255\).  The exact zero-side addition needed to improve it is not
another scalar moment of the full matrix: it is the stability tail (19) paired
with one nested quartic block.  That block:

* already raises the accepted support-\(3/2\) result to
  \(0.86725400195\) in the endpoint limit;
* would raise a support-2 pair theorem to \(0.93831332705\);
* reduces the pair support sufficient for \(95\%\) to
  \(2.14233794450\).

The remaining unsupported input for an actual \(95\%\) theorem is therefore a
saturated pair-trace theorem through support \(2.14233794450\), not a new
higher-level correlation: the quartic part of the certificate is already in
the strict total-support range \(4\mu<2\).
