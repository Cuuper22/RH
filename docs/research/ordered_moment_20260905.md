# An ordered fourth moment inside the unconditional support range

Research derivation, 2026-09-05. The signed-orthant extension below is a new
derivation from the explicit formula; it is **not** a statement quoted from
Rudnick--Sarnak. Their relevant input is the proof of Theorem 3.1 in
[*Zeros of principal L-functions and random matrix theory*](https://www.math.tau.ac.il/~rudnick/papers/nlevelDuke.pdf),
Duke Math. J. 81 (1996), 269--322, especially pp.285--300, equations
(3.13)--(3.21), Lemmas 3.2--3.10. For zeta this smooth-height theorem is
unconditional and permits complex ordinates. Their sharp-height Theorem 3.2
assumes RH and is not used here.

The analytic inputs in this note also feed the later
[sharpened comparison](sharpened_cubic_gain_20260905.md), which improves the
increment from `1/35280000` to `1/272000`. The original proof below is
retained to make that dependency clear.

## 1. Actual complex zeros and the ordered operator

Write $L=\log T$, $\mathcal N=TL/(2\pi)$, and

$$
 z_\rho=(\rho-1/2)/i,\qquad |\Im z_\rho|\le1/2.
$$

Zeros are counted with their multiplicities $m_\rho$. Fix a nonnegative
smooth density $u$, of integral one, supported in an interval of width
$\lambda<1$, centered at zero. With the entire height cutoff constructed
below, define the Hermitian integral operator

$$
 A_T(x,y)=\sqrt{u(x)u(y)}\sum_\rho m_\rho h_T(z_\rho/T)
                         e^{iLz_\rho(x-y)},\qquad
 V_T(x,y)=\mathbf1_{x>y}A_T(x,y).
$$

Hermiticity follows by pairing $z_\rho$ with $\bar z_\rho$, including
the conjugate height multipliers. No imaginary displacement is discarded.
The height decay makes the zero series and the integrations below absolutely
convergent for each $T$. The exact Hilbert--Schmidt identity is

$$
 \|V_T^2\|_{\rm HS}^2=
 \int_{x>y>z,\ x>t>z}A_T(x,y)A_T(y,z)A_T(z,t)A_T(t,x)
                         \,dx\,dy\,dz\,dt.                 \tag{1}
$$

Its four frequencies are

$$
 (\xi_1,\xi_2,\xi_3,\xi_4)=(x-y,y-z,z-t,t-x).
$$

They have signs $++--$, sum zero, and satisfy the crucial exact equality

$$
 \sum_j|\xi_j|=2(x-z)\le2\lambda<2.                 \tag{2}
$$

On the hyperplane $\sum\xi_j=0$, with measure $d\xi_1d\xi_2d\xi_3$,
the smooth pushforward density is

$$
 \Psi(\xi)=\int u(s)u(s+\xi_2)
                  u(s+\xi_1+\xi_2)u(s-\xi_3)\,ds.   \tag{3}
$$

Choose a fixed smooth compact cutoff equal to one on the intersection of
the closed $++--$ orthant with $\operatorname{supp}\Psi$, and supported
in $\sum|\xi_j|<2$. Such a cutoff exists by (2). Henceforth $\Psi$
includes this cutoff. The test in (1) is exactly
$\Psi\mathbf1_{++--}$, with a fixed strict support gap.

## 2. Concentrating height weights and quantitative Fourier bounds

Here are the height facts needed in this proof. For any fixed collar
$0<\epsilon<1/4$, any prescribed $B,J$, and any prescribed finite number
of derivatives, one can choose real entire $h_T$ such that

* $0\le h_T\le1$ on the real axis and
  $h_T\longrightarrow\mathbf1_{[1,2]}$ in $L^p$, every fixed finite $p\ge1$;
* $\widehat h_T\in C_c^\infty$, supported in $[-R,R]$, $R=O(\log T)$,
  with fixed-order seminorms bounded by powers of $\log T$;
* outside $[1-\epsilon,2+\epsilon]$, also for $|\Im r|\le1/(2T)$,
  $|h_T(r)|\ll T^{-B}(1+|\Re r|)^{-J}$, with the prescribed derivative bounds.

Indeed, convolve $\mathbf1_{[1,2]}$ with the probability kernel
$c_m(\sin(\delta_0r)/(\delta_0r))^{2m}$, $m=\lceil A\log T\rceil$.
Reserve finitely many sinc factors for algebraic decay; the remaining
factors give the arbitrary power saving outside the collar. Multiply by
$\phi(T^{-C}r)^2$, where $\phi$ is the Fourier transform of an even
nonnegative smooth compactly supported probability density. Taking $A,C$
large gives all the stated properties and smooths the Fourier B-spline.
Fixed Fourier derivatives can be placed on that B-spline, avoiding inverse
powers of its mollifier scale.

Use the Fourier convention
$\widehat f(y)=(2\pi)^{-1}\int f(r)e^{-iry}\,dr$, and put
$b_T(r)=h_T(r)\Omega(Tr)$, where the exact zeta archimedean density satisfies
$\Omega(t)=\log(|t|/(2\pi))+O(1/|t|)$ away from zero. Then

$$
 |\widehat b_T(y)|\ll_M(\log T)^{C_M}(1+|y|)^{-M},\qquad
 \|b_T/L-h_T\|_4=O(1/L).                            \tag{4}
$$

For the first estimate, integrate by parts on the real axis. Near the
height interval, every fixed derivative of $\Omega(Tr)$ is bounded by
powers of $\log T$. Near zero its derivatives can be $O(T^j)$, but the
prescribed derivatives of $h_T$ are $T^{-B}$ times powers of $\log T$.
Choose $B$ after the required fixed integration-by-parts order. At infinity
use the reserved algebraic decay. This proves (4) without a contour shift
that could introduce $e^{O(R)}$. The second estimate follows from Stirling
on $|r|\ge1/2$, bounded weighted logarithmic integrals there, and the
power-small height weight on $|r|<1/2$.

## 3. Keep the coordinate half-lines in the explicit formula

The zeta explicit formula writes each single-zero sum as an archimedean
factor $T\widehat b_T(\pm TL\xi)$, minus prime factors

$$
 T\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
   \left[\widehat h_T(T(L\xi-\log n))+
         \widehat h_T(T(L\xi+\log n))\right],       \tag{5}
$$

and the zeta-pole terms. A simultaneous change of all Fourier signs has no
effect on the constants below. Since $\log 2>R/T$ for large $T$, a prime
factor has exactly its indicated frequency sign. There is no prime-side
boundary approximation, including for the smallest prime. An archimedean
factor instead retains its literal half-line $y=TL\xi>0$ or $y<0$.
We never smooth these half-lines or Taylor-expand their indicators.

For completeness, the error reductions remain valid with these indicators:

1. If the symbol is supported in $\sum|\xi_j|\le2-\delta$, the product of
   all prime arguments is at most $T^{2-\delta+o(1)}$. Truncate each
   archimedean Fourier variable at $Y=T^\theta$, $0<\theta<\delta/3$.
   In an omitted integral, eliminate one large archimedean variable using
   the zero-sum constraint and use its supremum bound from (4); use $L^1$
   bounds for all other factors. Even the crude unrestricted prime weight
   sum is $O(T^{1-\delta/2+o(1)})$. Thus choosing the fixed $M$ sufficiently
   large makes the entire omitted contribution $o(\mathcal N)$.
2. Write $M_0,N_0$ for the products of positive-side and negative-side
   prime arguments. The retained constraint implies
   $|\log(M_0/N_0)|\ll(R+Y)/T$. If the integers differ, the elementary
   lower bound is $\gg(M_0N_0)^{-1/2}\ge T^{-1+\delta/2+o(1)}$, a
   contradiction. Thus only $M_0=N_0$ remains, exactly as in RS Lemma 3.3.
3. On this diagonal, change to the residual variables in (5) and Taylor-
   expand only the fixed smooth $\Psi$ at the central prime frequencies
   and zero archimedean frequencies. The error is $O((R+Y)/(TL))$ times
   an absolute convolution bound with polynomial logarithmic growth.
   The diagonal arithmetic weight is $O(L^s)$ for $s\le4$ prime slots,
   so this error is $o(\mathcal N)$. The archimedean half-lines remain
   unchanged during this step.
4. Unique factorization gives the same prime partitions as RS Lemmas
   3.8--3.9. A prime appearing in at least three slots contributes a
   convergent sum; a matched prime power $p^a$, $a\ge2$, does likewise.
   Only disjoint matched ordinary primes have the leading $L^s$ weight.
   These assertions also follow directly here from convergence of
   $\sum_p(\log p)^j/p^{j/2}$, $j\ge3$, and
   $\sum_{p,a\ge2}(\log p)^2/p^a$. All other partitions are lower order.

The products of restricted Fourier factors have bounded main convolution
constants: by Hölder and boundedness of the Hardy projections on $L^4$,
their inverse transforms are products of $h_T$, $P_+b_T$, and $P_-b_T$
with $L^4$ norms $O(1),O(L),O(L)$. This also supplies the uniform bound
needed for every lower-order prime partition in step 4.

Finally, prime partial summation uses only the smooth central symbol:

$$
 L^{-2}\sum_p\frac{(\log p)^2}{p}F(\log p/L)
       =\int_0^\infty vF(v)\,dv+O_F(1/L).          \tag{6}
$$

For two pairs, apply (6) twice. No derivative of an orthant wall occurs.
The endpoint $v=0$ has no atom: the contribution from $p\le T^\eta$,
after normalization, is $O(\eta^2+1/L)$. Equation (4) and $L^4$ Hardy
boundedness make the archimedean replacement error $O(1/L)$ in normalized
convolutions. Thus these genuine logarithmic errors are $O(T)$, not
$T$ times an uncontrolled power of $\log T$. Zeta-pole factors contain
$h_T(\pm i/(2T))=O(T^{-B})$; crude polynomial bounds on the other three
factors suffice, choosing $B$ large, to make every polar term negligible.
This covers all strata of the four-factor explicit-formula expansion.

## 4. Boundary contractions and the exact profile constant

The identity

$$
 \int_{\sum y_j=0}\prod_j\widehat f_j(y_j)\,dy_1dy_2dy_3
                   ={1\over2\pi}\int\prod_j f_j(r)\,dr
$$

fixes all convolution constants. Let $P_\pm$ restrict Fourier frequencies
to the positive or negative half-line. For four archimedean slots the
height factor, after dividing by $L^4$, tends to
$C_0=\int|P_+\mathbf1_{[1,2]}|^4$. One positive/negative prime pair leaves
one archimedean slot of each sign, giving
$C_1=\int_{1}^{2}|P_+\mathbf1_{[1,2]}|^2$. Two prime pairs give
$C_2=\int\mathbf1_{[1,2]}^4=1$. Each prime slot has a minus sign in (5),
so every surviving paired contribution is positive. There are exactly four
one-pair choices and two perfect matchings; a positive prime frequency is
integrated only once, over $v>0$.

These height constants are explicit:

$$
 C_0=\frac16,\qquad C_1=\frac13,\qquad C_2=1.       \tag{7}
$$

Indeed $g=P_+\mathbf1_{[1,2]}$ equals
$\frac12\mathbf1_{[1,2]}+\frac{i}{2\pi}\log|(r-1)/(r-2)|$, up to conjugation.
The logarithm-square integral over $[1,2]$ is $\pi^2/3$, giving $C_1=1/3$.
Also $\int g^4=0$: close its analytic logarithm representation in the
appropriate half-plane; the large semicircle and small endpoint arcs vanish.
Expanding $(g+\bar g)^4$ then gives $1=4C_1-2C_0$, proving (7).
Thus the frequency walls have been integrated exactly. Their values on the
walls themselves never enter a finite-$T$ integral.

The resulting new ordered-moment conclusion is

$$
 {\|V_T^2\|_{\rm HS}^2\over\mathcal N}\longrightarrow Q(u),             \tag{8}
$$

where

$$
\begin{aligned}
 Q(u)={}&\frac16\int u(x)^4\,dx\\
 &+\frac13\int_{x>z}(x-z)u(x)u(z)(u(x)+u(z))^2\,dx\,dz\\
 &+\int_{v,w>0}vw\int_{\mathbb R}\big[
 u(z+v+w)u(z+w)^2u(z)\\
 &\hspace{43mm}+u(z+v+w)u(z+w)u(z+v)u(z)\big]\,dz\,dv\,dw.
\end{aligned}                                                        \tag{9}
$$

For example, the four one-pair contractions of (3) are
$u(z)^2u(z+v)^2$, $u(z)^3u(z+v)$, $u(z)u(z+v)^3$, and
$u(z)^2u(z+v)^2$. They give exactly the second line of (9), each with the
prime measure $v\,dv$ from (6). The two perfect matchings give the two
last integrands. The overall scaling is
$T^4/(TL)^3$, the height convolution contributes $L^{4-s}/(2\pi)$,
and $s$ paired prime slots contribute $L^s$, producing precisely
$\mathcal N=TL/(2\pi)$ in every case.

For the flat density $u=1/\lambda$ on an interval of width $\lambda$,
the polynomial integrals in (9) evaluate to

$$
 Q_{\rm flat}=\frac{1}{6\lambda^3}+\frac{2}{9\lambda}
                                  +\frac{\lambda}{60}.               \tag{10}
$$

This evaluates the formula; applying (8) itself uses smooth profiles.
More generally, for $0\le u\le6/5$ supported in an interval of width at
most one, positivity of every integrand bounds (9) by

$$
 Q(u)\le(6/5)^4\left(\frac16+\frac29+\frac1{60}\right)
        =(6/5)^4\frac{73}{180}=0.84096<1.             \tag{11}
$$

## 5. Finite height truncation and scope

If $A_{T,\rm in}$ retains only zeros with real heights in
$[(1-\epsilon)T,(2+\epsilon)T]$, the feature-vector bound and
Riemann--von Mangoldt give

$$
 \|E_T\|_1:=\|A_T-A_{T,\rm in}\|_1
                  \ll\mathcal N T^{\lambda/2-B}.
$$

Triangular restriction is contractive in Hilbert--Schmidt norm, so
$\|V_T-V_{T,\rm in}\|_{\rm HS}\le\|E_T\|_1$. The unconditional second
moment gives $\|A_T\|_{\rm HS}=O(\sqrt{\mathcal N})$, hence the same
bound for $\|V_T\|_{\rm HS}$. Consequently

$$
 \|V_T^2-V_{T,\rm in}^2\|_{\rm HS}
 \le(\|V_T\|_{\rm HS}+\|V_{T,\rm in}\|_{\rm HS})\|E_T\|_1,
$$

which preserves (8) when $B$ is sufficiently large. No trace-norm
boundedness of triangular truncation is asserted or needed.

The new estimate concerns $\|V_T^2\|_{\rm HS}^2$, whose two monotone paths
give (2). It does not establish $\operatorname{tr}(A_T^4)=O(\mathcal N)$
at width one, or an effective finite dimension for centered quartic blocks.
Any counting improvement requires a separate zero-side inequality using
this ordered statistic. Such an inequality must retain the complex-zero
Hermitian structure, the height collar, and multiplicities.

The feature space also does not supply a block dimension aN: the finite
span of actual zero vectors can have dimension comparable to N. A
centered quartic with a nonzero constant term cannot charge an invented
aN null-mode count. All statistics used below are invariant under zero
padding and use only the actual zero-vector span where a rank is needed.

## 6. A comparison operator supplied by the zero-side slack

Here is that inequality. Work first with a finite zero multiset of total
multiplicity N. Write its Hermitian operator as G=P+Q, where P is the sum
of the simple on-line atoms. Thus P>=0, tr P<=S, rank P<=S, where S is
the number of those zeros. The other atoms give n_+(Q)<=b, S+2b<=N.
These statements also hold with the real height weights 0<=h_T<=1 on
the on-line atoms and conjugate complex weights on off-line pairs.

Set C=Q_-, B=Q_+, A=P-C, and let E and F be the positive spectral
projections of A and B. Put H=E+2F and

$$
 \Delta=\operatorname{tr}G^2-4\operatorname{tr}G+2N+S.
$$

All these projections act in the span of the actual zero vectors. No
frequency-grid dimension is assigned. Since BC=0, direct expansion gives

$$
\begin{aligned}
 &\|A-E\|_2^2+\|B-2F\|_2^2+2\operatorname{tr}(PB)
                                  +2\operatorname{tr}(A_-)\\
 &=\operatorname{tr}G^2-4\operatorname{tr}G+2\operatorname{tr}P
             -2\operatorname{tr}C+\operatorname{rank}E+4\operatorname{rank}F\\
 &\le\Delta-2\operatorname{tr}C\le\Delta .             \tag{12}
\end{aligned}
$$

Every term on the left is nonnegative. We used rank E<=rank P<=S,
rank F<=b, and 3S+4b<=2N+S. Consequently

$$
 \|G-H\|_2^2\le2\Delta,\qquad
 \|H\|_{\rm op}\le3,\qquad
 \operatorname{tr}H\le N,\qquad \|H\|_2^2\le3N.       \tag{13}
$$

For p(t)=t^3-3t^2+2t, projection algebra gives

$$
 \operatorname{tr}p(H)=6\operatorname{tr}(EF)\ge0.      \tag{14}
$$

E and F need not be orthogonal. This avoids incorrectly assuming that
the comparison operator has spectrum only in {0,1,2}.

## 7. Ordered fourth energy controls the negative cubic defect

Let V and W be the continuous triangular restrictions of G and H, and
Z=V-W. Products following a strictly triangular cycle have zero trace.
In particular tr G^3=6 Re tr(V^2 V*). The exact difference is

$$
 \operatorname{tr}(V^2V^*-W^2W^*)
   =\operatorname{tr}(V^2Z^*)+\operatorname{tr}(ZVW^*)
                                      +\operatorname{tr}(WZW^*).
$$

In the last two terms replace W* by H-W. The all-triangular products
have zero trace. Hilbert--Schmidt Cauchy--Schwarz gives

$$
 |\operatorname{tr}G^3-\operatorname{tr}H^3|
 \le6\|Z\|_2\big[\|V^2\|_2+
                    \|H\|_{\rm op}(\|V\|_2+\|W\|_2)\big].           \tag{15}
$$

Triangular restriction halves the squared Hilbert--Schmidt norm of a
Hermitian kernel, so ||Z||_2=||G-H||_2/sqrt(2), and similarly for V,W.
There is no logarithmic norm bound for triangular truncation in (15).

Suppose tr G=N, tr G^2/N<=D, ||V^2||_2^2/N<=Q_0, and
-tr p(G)/N>=kappa>0. The common span of G and H has dimension at most
N, since it is generated by the actual zero vectors. Thus
|tr(G-H)|<=sqrt(N)||G-H||_2. Combining (13)--(15) and
|tr(G^2-H^2)|<=||G-H||_2(||G||_2+||H||_2) yields

$$
 \kappa\le\sqrt{2\Delta/N}\,
      [3\sqrt{2Q_0}+12(\sqrt D+\sqrt3)+2].            \tag{16}
$$

Hence the finite certificate is

$$
 \boxed{\displaystyle
 \frac SN\ge2-D+
 \frac{\kappa^2}
 {2[3\sqrt{2Q_0}+12(\sqrt D+\sqrt3)+2]^2}.}           \tag{17}
$$

For tr G=N+o(N), use the exact slack in (12); the resulting o(1)
errors disappear. For the height-collar construction, first take T to
infinity at fixed collar and profile, then remove the O(epsilon N)
extra zeros and let the collar shrink. Equivalently all displayed
normalizations differ from the actual finite count by O(epsilon)+o(1).

## 8. The resulting small improvement

The smooth-symbol version of the same explicit-formula calculation gives
the first three raw moments 1,D(u),M_3(u), with

$$
 D(u)=\int u^2+\iint|x-y|u(x)u(y),\qquad
 M_3(u)=\int u^3+3\iint|x-y|u(x)^2u(y).
$$

All triangle perimeters are twice their range, so width less than one
suffices for the cubic moment. No RH or full fourth-moment premise is
added. Consider the limiting optimal cosine

$$
 u_*(x)=\frac{\cos(\sqrt2x)}{\sqrt2\sin(1/\sqrt2)},\quad |x|\le1/2,
 \qquad D_* =\frac12+\frac1{\sqrt2}\cot\frac1{\sqrt2}.
$$

Its Euler identity u_*(x)+int |x-y|u_*(y)dy=D_* on the support gives
M_3=3D_* int u_*^2-2 int u_*^3. Direct integration, enclosed by
rational alternating Taylor series, proves

$$
 D_*<4/3,\qquad \|u_*\|_\infty<6/5,\qquad
 M_3-3D_*+2<-1/100.
$$

The cubic defect is approximately -0.01177531280037. Smooth normalized
profiles of strict width less than one approach u_* in L^4, preserving
these three strict inequalities. Their costs approach D_*. Equation
(11) gives Q_0<1 uniformly for this family. Using the limiting inputs
in (17), the bracket is less than 42, and therefore

$$
 \liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
 \ge 2-D_*+\frac1{35280000}
 > \frac{168125183}{250000000}=0.672500732.           \tag{18}
$$

Take T to infinity separately for each fixed smooth profile and collar,
then take their limits. No uniform error estimate in the shrinking
support gap is used. The usual dyadic summation gives the same cumulative
liminf. The absolute improvement in proportion is at least
1/35280000, about 2.83447e-8; this is far below the 85% objective.

**Verification status:** (18) is a new ordinary mathematical derivation,
including the explicit-formula extension in §§1--5. It is not a new
machine-checked repository headline. The
[rational verifier](../../verify/volterra_constants.py) checks the scalar
Taylor enclosures and numerical constants. The
[final scalar lemma](../../verify/volterra_gap_scalar.lean) was checked by
AXLE in `lean-4.31.0` with only `[propext, Classical.choice, Quot.sound]`;
that check does not certify the analytic extension or the operator lemmas.

## 9. A concrete continuation beyond the cubic certificate

For alpha>0, Volterra quasinilpotence defines
R_alpha=(I-alpha V)^(-1)V. Exact multiplication gives the congruence

$$
 (I-\alpha V)^{-1}(I-\alpha G)(I-\alpha V^*)^{-1}
                    =I-\alpha^2R_\alpha R_\alpha^*.
$$

Thus n_>(G,1/alpha)=n_>(alpha^2 R_alpha R_alpha*,1).
Every fixed mixed trace tr(V^m(V*)^n) still follows two monotone paths,
with perimeter twice their range. This supplies an all-degree ordered
family within the same support. It does not justify interchanging an
infinite resolvent series with the T limit. Higher singular moments of
the resolvent introduce alternating paths, and shallow off-line pairs
also prevent a free alpha-to-infinity passage. No 85% certificate has
been obtained from this identity.


Continuation: [the finite ordered hierarchy](ordered_hierarchy_20260905.md) now gives all two-path polynomial moments. [Certificate limits](certificate_limits_20260905.md) show that the elementary Cayley continuation above cannot reach 85%, even granting its unresolved asymptotic passage. The [normalized Bezoutian route](bezoutian_20260905.md) provides a separate proved counting mechanism; its required arithmetic inequality remains open.
