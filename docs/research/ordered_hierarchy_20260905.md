# General ordered moments and a finite polynomial functional

Research derivation, 2026-09-05. This extends the coordinate-orthant
explicit-formula argument in ordered_moment_20260905.md.
No RH is assumed. All statements about actual zero operators below are for
fixed polynomial degree, with the concentrating height cutoff chosen for
that degree. The rational resummation in the last section is a computable
symbol functional; its identification with an actual zero-operator
resolvent is deliberately not asserted.

## 1. Every mixed two-path moment

Let $V$ be the lower-triangular part of the actual Hermitian complex-zero
feature kernel for a smooth density $u$ of width $\lambda<1$.
For fixed $m,n\ge1$, the cycle in $\operatorname{tr}(V^m(V^*)^n)$ consists
of one increasing and one decreasing path with common endpoints.
Its frequency signs are $m$ plus signs followed by $n$ minus signs, and
its total absolute frequency is twice the endpoint distance, below $2$.

The same proof as for the ordered fourth moment therefore applies.
Use $L^{m+n}$ Hardy boundedness instead of $L^4$; the cutoff exponent and
real integration-by-parts order may depend on the fixed degree.
Only $r$ disjoint positive/negative prime pairs survive, with
$0\le r\le\min(m,n)$.
Their height coefficient is

$$
 H_{mnr}=
 \begin{cases}
 \displaystyle\int_{\mathbb R}g(t)^m\overline{g(t)}^n\,dt,&r=0,\\
 \displaystyle\int_1^2 g(t)^{m-r}\overline{g(t)}^{n-r}\,dt,&r\ge1,
 \end{cases}
 \qquad g=P_+\mathbf1_{[1,2]}.
$$

Each prime pair has positive measure $v\,dv$.
The coordinate-wall, smallest-prime, integer-diagonal, repeated-prime,
pole, normalization, and height-tail arguments are unchanged for fixed
degree. This establishes the mixed moments without interchanging degree
and the zero-height limit.

All the height coefficients are explicit rationals. If
$D_{ab}=\int_1^2g^a\bar g^b$, then

$$
 D_{ab}=2^{-a-b}\mathbb E[(1+iY)^a(1-iY)^b],\qquad
 \mathbb E Y^{2j}=(2^{2j}-2)|B_{2j}| \quad(j\ge1),
$$

with odd moments zero and $\mathbb E1=1$. Here $\pi Y$ has logistic density.
For $C_{mn}=\int_{\mathbb R}g^m\bar g^n$, use

$$
 C_{mn}=\sum_{j=0}^{m-1}(-1)^{m-1-j}D_{j,m+n-1-j}.
$$

This follows from $g+\bar g=\mathbf1_{[1,2]}$ and $\int g^k=0$ for $k\ge2$.

## 2. Closed flat formula

For $u=1/\lambda$ on an interval of width $\lambda$, interpreted as the
limit of smooth profiles, every matching has the same spatial contraction.
Writing $S=\sum_{i=1}^r v_i$, it is
$(\lambda-S)_+/\lambda^{m+n}$, and

$$
 \int_{v_i>0}\prod_i v_i\,(\lambda-S)_+\,dv
                         =\frac{\lambda^{2r+1}}{(2r+1)!}.
$$

Consequently the exact limiting mixed moment is

$$
 M_{mn}=\lambda^{1-m-n}
 \sum_{r=0}^{\min(m,n)}
 \binom mr\binom nr r!\,
 \frac{\lambda^{2r}}{(2r+1)!}H_{mnr}.                 \tag{1}
$$

More usefully, for any polynomial $f$ with $f(0)=0$,

$$
 \lim_{T\to\infty}\frac{\|f(V_T)\|_{\rm HS}^2}{\mathcal N}
 =\lambda\int_{\mathbb R}|f(g/\lambda)|^2
 +\lambda\sum_{r=1}^{\deg f}\frac1{r!(2r+1)!}
                         \int_1^2|f^{(r)}(g/\lambda)|^2.              \tag{2}
$$

This is a finite identity, not a power-series interchange.
Polarization supplies the entire polynomial Gram form.
It follows directly by summing
$\sum_{m\ge r}c_m\binom mr\lambda^{-m}g^{m-r}
=\lambda^{-r}f^{(r)}(g/\lambda)/r!$ in (1).

At $\lambda=1$, the leading monomial Gram matrix is

$$
 \begin{pmatrix}
 2/3&1/3&1/12&-1/30\\
 1/3&73/180&31/120&1/36\\
 1/12&31/120&59/168&47/210\\
 -1/30&1/36&47/210&30173/75600
 \end{pmatrix}.
$$

## 3. General density: divided differences replace enumeration

There is a corresponding positive finite functional for arbitrary $u$.
For $r\ge1$, put

$$
 S=\sum_{i=1}^r v_i,\quad x_j=z+\sum_{i=1}^jv_i,\quad
 B_{f,r}(z,v;g)=
 \sqrt{u(z)u(z+S)}\prod_{j=1}^{r-1}u(x_j)\,
 f^{[r]}(gu(x_0),\ldots,gu(x_r)),
$$

where $f^{[r]}$ denotes a divided difference, with continuous coincident-node
value $f^{(r)}/r!$. Then the exact fixed-polynomial limiting functional is

$$
 \begin{aligned}
 \mathcal L_u[f]={}&
 \int_{\mathbb R}\!\int_{\mathbb R}|f(g(t)u(x))|^2\,dx\,dt\\
 &+\sum_{r=1}^{\deg f}\frac1{r!}
 \int_1^2dt\int_{\mathbb R}dz\int_{v_i>0}\prod_i v_i\,
 \left|\sum_{\pi\in S_r}B_{f,r}(z,v_\pi;g(t))\right|^2\,dv .
 \end{aligned}                                                       \tag{3}
$$

Indeed, archimedean edges inserted between successive prime edges give
the complete homogeneous polynomial in the visited vertex densities.
For the monomial $f(X)=X^m$ this is precisely
$f^{[r]}(gu_0,\ldots,gu_r)=g^{m-r}h_{m-r}(u_0,\ldots,u_r)$.
Fix the order of the positive prime edges and sum over the $r!$ orders
on the negative path. The integration measure is permutation-invariant,
so the sum of cross products equals $1/r!$ times the squared modulus of
the symmetrized path amplitude. This proves (3) and its positivity.
For constant $u$, it reduces to (2).

This form is computationally practical at moderate degree: evaluate
complete homogeneous polynomials recursively, rather than unstable
divided-difference quotients. The height integrations use the exact
rational matrix $D_{ab}$. The remaining simplex integral can use the
Dirichlet law with parameters $(2,\ldots,2,2)$, followed by a uniform
basepoint in the remaining interval; its total mass is
$\lambda^{2r+1}/(2r+1)!$.

The accompanying script ../../verify/ordered_polynomial_functional.py implements
exact flat moments and this general-profile quadrature for the normalized
cosine $u(x)=\sqrt2\cos(\sqrt2x)/(2\sin(1/\sqrt2))$.
The script computes exact flat Gram entries through any requested fixed degree.
Its exploratory cosine degree-5 diagonal is approximately

$$
 (0.66374948,\ 0.39896254,\ 0.34592558,\ 0.40147719,\ 0.70986937).
$$

The cosine matrix is numerical, not a certificate: two Sobol scrambles
differed by at most $1.47\cdot10^{-6}$ entrywise.

## 4. Rational resummation: explicit domain and a genuine obstruction

For the flat profile, substitute $f_\alpha(z)=z/(1+\alpha z)$ into the
right side of (2), allowing its now-infinite positive derivative series.
For $\Re\alpha>0$ this series converges, and gives the explicit functional

$$
 J_\lambda(\alpha)=
 \frac1\lambda\int_{\mathbb R}\frac{|g|^2}{D}
 +\frac{\lambda}{|\alpha|^2}\int_1^2
       \frac{\mathcal S(|\alpha|^2/D)-1}{D},
 \quad
 D=|1+\alpha g/\lambda|^2,
$$

$$
 \mathcal S(z)=\sum_{r\ge0}\frac{r!z^r}{(2r+1)!}
 =\int_0^1e^{zt(1-t)}\,dt
 =e^{z/4}\frac{\sqrt\pi}{\sqrt z}\operatorname{erf}(\sqrt z/2).
$$

The last expression has its continuous value at $z=0$.
For $\Re\alpha>0$, $D$ is bounded away from zero on the two boundary lines
$\Re g=0,1/2$, and on the height interval $|\alpha|^2/D\le4\lambda^2$.
Thus this is a convergent computable functional on that half-plane.
For real $\alpha>0$, the archimedean integral can also be reduced to

$$
 J_{\lambda,0}(\alpha)
 =\frac{1-I(q)}{2\alpha},\quad q=\alpha/\lambda,\qquad
 I(q)=\frac{\psi_1(1+1/q)}{q(1+q/2)},
$$

where $\psi_1$ is the trigamma function.
The general-density analogue follows by inserting

$$
 f_\alpha^{[r]}(a_0,\ldots,a_r)
            =\frac{(-\alpha)^{r-1}}{\prod_{j=0}^r(1+\alpha a_j)}
$$

in (3). For real positive $\alpha$, bounded $u$ and the simplex factorial
give an explicit summable majorant for the path series.

However, this does **not** by itself prove convergence of the actual
zero-operator resolvent norm. The raw moment Taylor series has zero radius,
because the Hardy logarithm has factorially growing moments.
More decisively, let $a_N=(\log N)^2$ and
$W_N(x,y)=-a_N\mathbf1_{x>y}$ on $[0,1]$.
Every fixed mixed moment of $W_N$, divided by $N$, tends to zero. But

$$
 W_N(I+\alpha W_N)^{-1}(x,y)
       =-a_Ne^{\alpha a_N(x-y)}\mathbf1_{x>y},
$$

whose squared Hilbert--Schmidt norm divided by $N$ diverges for every
$\alpha>0$. Adding this as a direct-sum block preserves every fixed
limiting mixed moment while destroying resolvent convergence.
An actual resolvent theorem therefore needs a zero-specific stability
estimate. Finite polynomial applications of (2) or (3) have no such gap.


# Marked translation geometry

Independent research derivation, 2026-09-05.
These calculations concern the actual complex-zero convolution kernel and
the abstract translation models distinguished below. They do not prove 85%.

## 1. Exact displacement identities

For the flat frequency window $[0,1]$, write $G(x,y)=F(x-y)$ and
$V(x,y)=\mathbf1_{x>y}F(x-y)$. On the appropriate $H^1$ domain,
$D=d/dx$ satisfies

$$
 [D,G]f(x)=F(x)f(0)-F(x-1)f(1),\qquad
 [D,V]f(x)=F(x)f(0).
$$

These are boundary displacement identities. Boundary evaluation is
unbounded on $L^2$; treating them as bounded finite-rank commutators without
their domain is invalid.
Every truncated forward translation $S_a$ commutes with $V$, because both
are causal convolutions. In particular the integration operator commutes
with $V$.

There is also a bounded, quantitatively useful commutator:

$$
 [S_a,G](x,y)=
 \big(\mathbf1_{x>a}-\mathbf1_{y<1-a}\big)F(x-y-a).
$$

Its two corner regions have no archimedean diagonal mass. The ordinary
second explicit-formula moment gives, in the width-one profile limit,

$$
 \frac{\|[S_a,G_T]\|_{\rm HS}^2}{\mathcal N}
                         \longrightarrow a(1-a).
$$

Indeed each corner contributes $a(1-a)/2$ after integration of the
prime-pair weight $|x-y-a|$.
For width $\lambda<1$ and normalized flat density $1/\lambda$, the answer
is $a(\lambda-a)/\lambda$, $0\le a\le\lambda$.

## 2. A complete total-range measure

Let $X$ be multiplication by the physical frequency coordinate.
The kernel of $[X,V^m]$ is $(x-y)V^m(x,y)$.
More generally conjugation by $e^{itX}$ inserts the bounded factor
$e^{it(x-y)}$ without changing the zero-tuple Fourier support.
Thus the orthant proof computes an arbitrary fixed smooth multiplier
$H(x-y)$ in every ordered mixed Hilbert--Schmidt product.

For normalized flat density on width $\lambda$, the measure associated to
$\operatorname{tr}(V^m(V^*)^n)$ has an atom at range zero of mass
$\lambda^{1-m-n}C_{mn}$ and continuous density

$$
 \lambda^{-m-n}(\lambda-S)
 \sum_{r=1}^{\min(m,n)}
 \binom mr\binom nr r!\,D_{m-r,n-r}
                      \frac{S^{2r-1}}{(2r-1)!},
 \qquad 0<S<\lambda.                                  \tag{1}
$$

Here $C_{mn}=\int_{\mathbb R}g^m\bar g^n$,
$D_{ab}=\int_1^2g^a\bar g^b$, and $g=P_+\mathbf1_{[1,2]}$.
Equation (1) follows by fixing the total positive prime range:

$$
 \int_{\substack{v_j>0\\\sum v_j=S}}\prod_jv_j\,dv_1\cdots dv_{r-1}
                              =\frac{S^{2r-1}}{(2r-1)!}.
$$

For a polynomial $f(0)=0$, the resulting positive continuous density is

$$
 \rho_f(S)=
 \sum_{r=1}^{\deg f}
 \frac{S^{2r-1}(\lambda-S)}
      {r!(2r-1)!\lambda^{2r}}\int_1^2|f^{(r)}(g/\lambda)|^2.
                                                               \tag{2}
$$

At width one,

$$
 \rho_V(S)=S(1-S),\qquad
 \rho_{V^2}(S)=\frac43S(1-S)+\frac13S^3(1-S).
$$

In particular,

$$
 \frac{\|[X,V_T]\|_{\rm HS}^2}{\mathcal N}\to\frac1{20},
 \qquad
 \frac{\|[X,V_T^2]\|_{\rm HS}^2}{\mathcal N}\to\frac{47}{630},
 \qquad
 \frac{\|[X,G_T]\|_{\rm HS}^2}{\mathcal N}\to\frac1{10}.
$$

These are additional finite mixed invariants; no unbounded-resolvent
interchange or effective block dimension is needed.

## 3. The Jordan obstruction already has translation geometry

Let $a_r=r!/(2r+1)!$ and $w_n=a_{n-1}-2a_n+a_{n+1}$, as in the flat
Jordan obstruction. Choose $n$ with probability $p_n=nw_n$.
On $L^2[0,1]$, take the truncated forward shift $K=S_{1/n}$.
Writing $x=s+j/n$, $0\le s<1/n$, decomposes $K$ into $J_n$ fibers.
The fiber trace integrated over $s$ has $\tau(I)=1$.
Therefore the mixed model $V=g(t)I+S_{1/n}$ is exactly the existing Jordan
tracial model: it reproduces all flat unmarked moments and its
approximately $69.9874\%$ generic simple population.

This model commutes with every forward translation and integration, and
has the standard causal-convolution displacement identity. Those bare
identities alone do not exclude the adversary.
This is a semifinite limiting tracial construction, not an actual finite
sum of exponential zero atoms or an actual finite-$T$ Volterra spectrum.

Frequency marks do exclude this particular model:

$$
 \tau|[X,V]|^2
  =\sum_{n\ge1}w_n\left(\frac1n-\frac1{n^2}\right)
  =0.03702926726145223\ldots < \frac1{20}.
$$

There is a stronger obstruction for every random
single-shift mixture $V=gI+tS_a$: matching the first marked density forces
$q_1(a)=\mathbb E[t^2;da]/da=a$.
Matching the isolated two-pair range density then forces
$q_2(a)=\mathbb E[t^4;da]/da=(16/3)a^3$ for $0<a<1/2$.
Cauchy--Schwarz would require probability density at least
$q_1^2/q_2=3/(16a)$, which is not integrable near zero.
Thus all the first two marked path densities rule out that entire family.
Turning finitely many marks into a useful count inequality remains open.

## 4. Translation models still have a significant unconstrained direction

There is a larger model that matches even the general-profile path
functional. On a fine physical grid let

$$
 V=g(t)I+\sum_{j>0}c_jS_{v_j},
 \qquad \mathbb E c_j=0,\quad
 \mathbb E c_j\bar c_k=\delta_{jk}\,v_j\Delta v.
$$

Independent infinitesimal Gaussian coefficients select exactly the
prime-pair contractions in every fixed ordered word.
Repeated-label contributions vanish as the grid is refined.
This model has literal truncated-translation geometry.
Its unmarked and marked moment limits are the derived functionals,
although it is not asserted to come from zeta zeros.

Crucially, a monotone path of span below one contains at most one step
$v>1/2$. The entire high-step field therefore enters all the proved
ordered/profile/marked moments only through its conditional second
covariance. It may be replaced by one random high translation
$Ae^{i\theta}S_v$, present with probability $3/(8A^2)$, with $v$ density
$(8/3)v$ on $(1/2,1)$ and uniform phase. Keep the Gaussian low steps.
For $A^2\ge3/8$ this is a valid mixture and preserves every such moment.
The amplitude may even depend on the low realization and on $v,\theta$,
provided the conditional sampling probability is adjusted so the second
covariance remains fixed, and the two signs of the high shift are averaged
equally to preserve its zero conditional mean.

This is genuine remaining freedom, not an assumption that the model's
full fourth spectral moment equals the unavailable full-support formula.
The high-step-only model has mean bad fraction $1/(6A^2)$ for $A>1$.
Adding the compulsory low steps changes that conclusion.

Exploratory Hermitian Toeplitz simulations gave roughly $92.5\%$ spectral
mass in $(0,2)$ for the fully Gaussian model.
With one random high translation and Gaussian low steps, the minimum
observed average was about $88.5\%$ near $A=1$.
An initial pointwise amplitude optimization omitted that last sign
symmetrization; its numerical value is discarded.
The corrected sign-symmetrized run, at matrix size 160 with 80 draws,
gave $87.213\%$ with Monte Carlo standard error $0.634$ percentage points.
These computations neither establish a below-85 adversary nor prove an
85 bound. They identify the high-step distribution as a concrete freedom
that any proposed characterization must address.


## A finite spatial-mark certificate

Let X be multiplication by physical position and d(A)=[X,A]. Put

    U = V d²(V) − d(V)².

Every term in ||U||HS² is a two-monotone-path quartic with bounded polynomial spatial marks. Its support is twice the endpoint range, so the fixed-degree ordered-moment transfer applies. The argument uses no effective block dimension or resolvent limit.

For a causal convolution, d(V) and V commute. Writing the two positive increments as v,w, the two-prime path coefficient in U is (v−w)²/2. The zero-prime coefficient vanishes. The one-prime coefficient is g v², with g=P₊1_[1,2]. Since ∫_[1,2]|g|²=1/3,

    τ||d²(V)||² = ∫₀¹ v⁵(1−v)dv = 1/42,
    one-prime contribution to τ||U||² = 1/126.

The two Wick matchings give

    2∫_{v,w>0;v+w<1} vw(1−v−w) ((v−w)²/2)² dv dw
      = (1/2)∫₀¹ S⁷(1−S)dS ∫₀¹ t(1−t)(2t−1)⁴dt
      = 1/10080.

Consequently

    τ||U||² = 1/126 + 1/10080 = 9/1120.

In a random single-translation model V=gI+tS_a, where the jump law is independent of the height variable, direct multiplication gives

    U = g t a² S_a.

Matching τ||d²(V)||²=1/42 therefore forces τ||U||²=1/126, contradicting the actual value by 1/10080. This excludes arbitrary amplitude/length mixtures in that class with a finite pair of marked polynomial equalities. The older full-density nonintegrability argument is unnecessary for this class.

The height-independence qualification matters: it is part of the original single-shift/Jordan model. If amplitudes depend on g, additional marked mixed moments are needed to fix the g-weighted covariance. More generally, replace the single first constraint by the actual one-prime marked Gram entry fixing ∫|g|² E|t|²a⁴(1−a)=1/126. Neither statement excludes the Gaussian-low-plus-covariance-only-high model: its two unequal low increments supply the missing positive term.

## What a universal finite count program must retain

Let normalized trace be τ and g₀=V+V*. A necessary zero-side decomposition at proposed simple proportion s is

    g₀=P+B−C;   P,B,C≥0; BC=0;
    τP=s;      τg₀=1;
    P=EPE;     B=FBF;
    E²=E=E*;   F²=F=F*;
    τE≤s;      τF≤(1−s)/2.

One may additionally introduce Z²=Z=Z*, g₀Z=g₀ and τZ≤1 for the finite zero-feature support. These are necessary conditions; they do not assert that every feasible decomposition comes from zeta zeros.

A finite tracial moment relaxation adds the known ordered marked moments, positivity moment matrices, P/B/C localizing matrices, and the operator inequalities 0≤X≤I. Use only Hilbert–Schmidt anchored words for the unweighted moment matrix: the algebra generated by X,V is not confined to the rank≤N zero-feature space, so τI=1 is invalid. P/B/C localizing matrices may include the empty word because their traces are finite. Unknown higher moments need not be assumed bounded: a dual certificate is a finite operator inequality valid before taking the height limit.

A valid dual lower bound is a finite linear combination of these equalities and positive trace polynomials whose evaluated known-moment part exceeds the target. A numerical optimizer output alone is not such a certificate; its coefficients and PSD factorizations must subsequently be verified.

The simpler relaxation retaining only an exact-root comparison H=E₀+2F₀, E₀F₀=0, and

    τ||g₀−H||² ≤ D−2+s

appears inadequate for 85. In the full Gaussian translation model, choose H=0 on the lowest7.5% of g₀ eigenvalues, H=2 on the highest7.5%, and H=1 elsewhere. For sizes128,256,512,24 independent realizations each, the respective mean squared errors were0.17525,0.16894,0.17377, below the flat s=.85 budget0.183333. These are model feasibility diagnostics, not a proved limiting obstruction. The model itself has roughly92.5% simple spectral population, so it does not obstruct the stronger decomposition program above.
