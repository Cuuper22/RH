# Hybrid cycle 3: a Routh--resultant certificate for \(\xi\) and \(\xi'\)

## Outcome

There is an exact mixed certificate which attacks both extremizers left by
the support-one Gram argument.

Fix a real constant \(c>0\), and put

$$
A_c(s):=\xi'(s)-c\xi(s),\qquad A_{-c}(s):=\xi'(s)+c\xi(s).
\tag{1}
$$

In a buffered dyadic window let

- \(Q_c^-(T)\) be the number, with multiplicity, of zeros of \(A_c\)
  strictly to the left of \(\Re s=1/2\);
- \(M_0(T)=\sum_{\rho\in\mathcal M_0}(m_\rho-1)\), where
  \(\mathcal M_0\) is the set of distinct multiple zeros of \(\xi\) on
  the critical line and \(m_\rho=\operatorname{ord}_\rho\xi\);
- \(D_0(T)=|\mathcal M_0|\).

Then the Routh--Hermite index identity gives

$$
\boxed{
N_0^s(T,2T)
=N(T,2T)-2Q_c^-(T)-M_0(T)-D_0(T)+o(N).}
\tag{2}
$$

Equivalently, define the nonnegative mixed defect

$$
\mathfrak R_c(T)
:=Q_c^-(T)+\frac12M_0(T)+\frac12D_0(T).
\tag{3}
$$

Then

$$
\boxed{\frac{N_0^s}{N}=1-2\frac{\mathfrak R_c}{N}+o(1).}
\tag{4}
$$

Thus the exact sufficient inequality for \(85\%\) is

$$
\boxed{\mathfrak R_c(T)\le(0.075-o(1))N.}
\tag{R85}
$$

The common-zero terms in (3) are genuinely a resultant: since \(c\ne0\),

$$
\gcd(A_c,A_{-c})=\gcd(\xi,\xi'),
\tag{5}
$$

and a critical-line zero of this gcd is exactly a multiple critical-line
zero of \(\xi\).  If one does not want to separate distinct from repeated
common factors, \(D_0\le M_0\) gives the slightly stronger but simpler
sufficient condition

$$
\boxed{Q_c^-(T)+M_0(T)\le(0.075-o(1))N.}
\tag{R85$'$}
$$

The prime side of (1) stays at support one.  On \(\Re s>1\), writing

$$
Y(s):=\frac{\xi'}{\xi}(s)=A_\Gamma(s)-P(s),
\qquad
P(s)=\sum_{n\ge2}\frac{\Lambda(n)}{n^s},
\tag{6}
$$

one has

$$
\frac{A_c'}{A_c}(s)
=Y(s)+\frac{Y'(s)}{Y(s)-c}.
\tag{7}
$$

For fixed \(c\), \(A_\Gamma(s)-c\asymp\log T\) on the right contour, so

$$
\frac{Y'}{Y-c}
=\bigl(A_\Gamma'+P_1\bigr)
\sum_{k\ge0}\frac{P^k}{(A_\Gamma-c)^{k+1}},
\qquad
P_1(s)=\sum_{n\ge2}\frac{\Lambda(n)\log n}{n^s}.
\tag{8}
$$

Every arithmetic term in (8) has frequency
\(\log(n_1\cdots n_k)\).  A Paley--Wiener test of bandwidth
\(L\le\log T\) deletes all products \(n_1\cdots n_k>T\).  Hence the
resultant contour observable uses generalized von Mangoldt coefficients
of total length at most \(T\); it does not cross into the unsupported
prime-pair band \(X>T\).

With the accepted inputs, the strongest numerical conclusion remains

$$
\frac{N_0^s}{N}\ge0.6725007036\ldots .
\tag{9}
$$

Indeed (4) turns that accepted result into only

$$
\mathfrak R_c(T)le
\frac{1-0.6725007036\ldots}{2}N
=0.1637496482\ldots N,
\tag{10}
$$

whereas (R85) needs \(0.075N\).  The exact missing improvement is

$$
0.1637496482\ldots-0.075
=0.0887496482\ldots
\tag{11}
$$

in the resultant defect, equivalently \(0.1774992964\ldots N\) in the
simple-zero proportion.  No scalar theorem presently accepted in the
project reduces (10).

## 1. Finite Routh--Hermite lemma

The algebra behind (2) is elementary and exact.  Let \(F\in\mathbb R[z]\)
have degree \(n\), and define

$$
H_c(z)=F'(z)-icF(z),\qquad c>0.
\tag{12}
$$

Let \(q_c\) be the number of zeros of \(H_c\) in the upper half-plane,
counted with multiplicity.  At a real zero \(x\) of \(F\) of multiplicity
\(m_x\), \(H_c\) has multiplicity \(m_x-1\); these are all of the real
zeros of \(H_c\), because for real \(x\)

$$
H_c(x)=0\quad\Longleftrightarrow\quad F(x)=F'(x)=0.
\tag{13}
$$

The Routh index theorem, obtained by applying the argument principle to
\(H_c/H_c^*\), gives

$$
r_{\rm dist}(F)
=n-2q_c-\sum_{x\in\mathbb R:F(x)=0}(m_x-1),
\tag{14}
$$

where \(r_{\rm dist}(F)\) is the number of distinct real roots of \(F\).
Subtracting one for every distinct multiple real root gives

$$
r_{\rm simple}(F)
=n-2q_c-
\sum_{x\in\mathbb R:m_x\ge2}(m_x-1)
-\#\{x\in\mathbb R:m_x\ge2\}.
\tag{15}
$$

This proves the finite version of (2).  One way to see the index in (14)
directly is to note that \(H_c^*(x)=F'(x)+icF(x)\) on the real axis, so
\(H_c/H_c^*\) has modulus one.  Its winding changes by two units for an
upper-half-plane zero of \(H_c\), while a common real factor contributes
its boundary multiplicity.  The remaining winding is exactly the number
of distinct real crossings of \(F\).

Apply (15) to the canonical products of

$$
F_T(z)=\Xi(z)=\xi(\tfrac12+iz)
\tag{16}
$$

in a window enlarged by \(T^{1/2}\), and then remove the two boundary
strips.  Since

$$
F_T'(z)-icF_T(z)
=i\{\xi'(\tfrac12+iz)-c\xi(\tfrac12+iz)\},
\tag{17}
$$

the upper half of the \(z\)-plane is the left half of the \(s\)-plane.
The accepted tail truncation makes the discarded contribution \(o(N)\),
and (15) becomes (2).

## 2. Exact charge of the sharp obstruction

The certificate distinguishes neither obstruction by wishful labeling;
it charges both with the correct lost simple-zero mass.

### On-line double

If \(\xi(s)=a(s-\rho)^2+\cdots\) with \(\Re\rho=1/2\), then

$$
A_c(s)=(s-\rho)\{2a-ca(s-\rho)+\cdots\}.
\tag{18}
$$

Thus the double contributes

$$
Q_c^-=0,\qquad M_0=1,\qquad D_0=1,
\tag{19}
$$

and hence exactly one unit to \(\mathfrak R_c\), or two lost simple zeros
in (4).

### Off-line conjugate pair

In the real coordinate, the local model of a conjugate pair is

$$
F_\delta(z)=(z-a)^2+\delta^2.
\tag{20}
$$

For every \(\delta\ne0\), the polynomial
\(F_\delta'-icF_\delta\) has one upper-half-plane zero.  Therefore

$$
Q_c^-=1,qquad M_0=D_0=0,
\tag{21}
$$

again giving \(\mathfrak R_c=1\).  At \(\delta=0\) the pair collides into
a double line zero and (21) changes to (19), leaving the total charge
unchanged.  This is the desired robustness against *near-line* pairs.

For the sharp population from cycle 1,

$$
s=0.6725007036\ldots N,qquad
d=0.1637496482\ldots N,qquad p=0,
\tag{22}
$$

every nonsimple block is an on-line double, so
\(\mathfrak R_c=d=0.1637496482\ldots N\).  Replacing those doubles by the
same number of near-line pairs gives \(Q_c^-=p\) and the identical value.
Thus (3) penalizes exactly the full sharp face, not merely one endpoint.

## 3. The resultant block

The two auxiliary functions form the invertible linear transform

$$
\begin{pmatrix}A_c\\A_{-c}\end{pmatrix}
=
\begin{pmatrix}1&-c\\1&c\end{pmatrix}
\begin{pmatrix}\xi'\\\xi\end{pmatrix}.
\tag{23}
$$

Consequently their common-zero module is exactly the common-zero module
of \((\xi',\xi)\).  In a finite canonical-product truncation, the
Sylvester block

$$
\mathcal S_c(u,v)=A_cu+A_{-c}v
\tag{24}
$$

has nullity \(M_0\) on the critical-line factor, and its square-free
nullity is \(D_0\).  Formula (3) may therefore be read as

$$
\text{left index of }A_c
+\frac12\text{(resultant nullity)}
+\frac12\text{(square-free resultant nullity)}.
\tag{25}
$$

For a proof that avoids square-free extraction, count every boundary zero
of \(A_c\) with full multiplicity.  This gives

$$
\mathfrak R_c\le Q_c^-+M_0
\tag{26}
$$

and hence the support-one sufficient condition (R85$'$).  Double zeros,
which are the sharp obstruction, make (26) an equality.

## 4. Prime-side support calculation

The functional equation gives

$$
A_c(1-s)=-A_{-c}(s).
\tag{27}
$$

Thus zeros of \(A_c\) on the left are reflected to zeros of \(A_{-c}\)
on the right, where the Dirichlet expansion is available.  On a fixed
right line \(\Re s=1+\delta\),

$$
A_\Gamma(s)-c\asymp\tfrac12\log T,
\qquad P(s)=O_\delta(1),
\tag{28}
$$

so (8) converges absolutely and uniformly.  More explicitly,

$$
P(s)^k
=\sum_{n\ge1}\frac{\Lambda^{*k}(n)}{n^s},
\tag{29}
$$

where \(*\) is Dirichlet convolution.  Inserting (29) into the argument-
principle contour for \(A_{\pm c}\), a test with
\(\operatorname{supp}\widehat h\subset[-L,L]\), \(L\le\log T\), retains
only

$$
n=n_1\cdots n_k\le e^L\le T.
\tag{30}
$$

The slowly varying factors \((A_\Gamma\mp c)^{-k-1}\) are handled by
partial summation and introduce no new Fourier frequency.  Therefore:

> **Support-one transfer.**  Any smoothed argument-principle or block-
> resultant estimate formed from \(A_c,A_{-c}\) and a bandwidth-one test
> reduces on the prime side to generalized von Mangoldt polynomials of
> total length at most \(T\).

This is the principal advantage over the cycle-2 hard selector.  There is
no labeled subset and no quadratic Fourier transform of such a subset;
the obstruction is absorbed into one analytic pair before the explicit
formula is applied.

What is not automatic is the *one-sided index estimate*.  Absolute
convergence of (8) evaluates the contour symbol, but converting it into

$$
Q_c^-+\frac12M_0+\frac12D_0\le0.075N
\tag{31}
$$

requires a positivity, winding, or block-signature inequality.  Ordinary
first and second traces of \(\xi\) alone allow the value (10), so they
cannot supply (31).

## 5. Infinitesimal \(\xi'\)-zero form

The same certificate has a local form which makes contact with the
accepted \(\xi'\) theorem.  If \(\eta\) is a simple critical-line zero of
\(\xi'\), define

$$
a_\eta=
\begin{cases}
\displaystyle\frac{\xi(\eta)}{\xi''(\eta)},&\xi(\eta)\ne0,\\[2mm]
0,&\xi(\eta)=0.
\end{cases}
\tag{32}
$$

For a noncommon zero, \(a_\eta\) is the residue of \(\xi/\xi'\) at
\(\eta\).  Differentiating \(A_c(s_c)=0\) at \(c=0\) gives

$$
\left.\frac{ds_c}{dc}\right|_{c=0}=a_\eta.
\tag{33}
$$

Thus \(a_\eta<0\) is precisely a simple \(\xi'\) zero which flows into
the left half-plane and \(a_\eta=0\) is a common \(\xi,\xi'\) zero.  The
nonnegative regularized defect

$$
E_\varepsilon(T)
=\sum_{\eta\in\mathcal U_T}
\left(1-\frac{a_\eta}{\sqrt{a_\eta^2+\varepsilon^2}}\right)
\tag{34}
$$

tends to twice the number of bad simple extrema plus the number of common
double zeros.  For the local pair (20), \(a_\eta<0\) for \(\delta\ne0\),
so its limiting charge is \(2\); at \(\delta=0\), (34) contributes \(1\)
and \(D_0\) contributes the other \(1\).

Let \(B_{\rm ns}\) count bad sign-changing non-simple critical points of
\(\Xi\).  The real Sturm index gives

$$
N_0^s(T,2T)
\ge |\mathcal U_T|-lim_{\varepsilon\downarrow0}E_\varepsilon(T)
-B_{\rm ns}(T)-D_0(T)-o(N).
\tag{35}
$$

Using the accepted quartic-window result

$$
|\mathcal U_T|\ge(0.86864\ldots-o(1))N,
\tag{36}
$$

one obtains the alternative sufficient inequality

$$
\boxed{
\lim_{\varepsilon\downarrow0}E_\varepsilon
+B_{\rm ns}+D_0
\le(0.01864\ldots-o(1))N
\quad\Longrightarrow\quad N_0^s\ge0.85N.}
\tag{37}
$$

This explains why the headline \(86.864\%\) theorem for \(\xi'\) cannot
be added to the \(67.25\%\) theorem for \(\xi\): only \(1.864\%\) remains
after all unclassified critical points are charged adversarially.  The
missing datum is the sign/resultant statistic (34), not another count of
\(\xi'\) zeros.

## 6. Strongest unconditional result and next attack

The construction yields two exact targets:

$$
\mathfrak R_c/N\le0.075
\quad\text{or, more strongly but more simply,}\quad
(Q_c^-+M_0)/N\le0.075.
\tag{38}
$$

No accepted scalar input proves either target.  The strongest
unconditional theorem therefore remains (9), and the sharp configuration
(22) shows why no algebraic recombination of the existing proportions can
do better.

The most direct next attack is now finite and support-one:

1. Fix \(c=1\) and a bandwidth-one smooth height/window profile.
2. Form the paired argument-principle symbol
   \(A_c'/A_c\) and \(A_{-c}'/A_{-c}\), retaining the common boundary
   term rather than indenting it away.
3. Insert the absolutely convergent expansion (8) on the right contour.
   Combine the \(+c\) and \(-c\) series before any absolute-value bound;
   their odd powers in \(c\) are the signed Routh index.
4. Seek a one-sided block-signature inequality proving (31).  The exact
   error budget is
   \(0.0887496482\ldots N\) below the presently certified resultant
   defect.
5. If square-free resultant extraction is analytically costly, prove the
   coarse target (R85$'$); it is exact on the double/near-pair extremal
   face and uses only the closed-half-plane zero count of \(A_c\).

The missing lemma is therefore:

> **Support-one Routh bound.**  For one fixed \(c>0\), the paired
> \(A_c,A_{-c}\) explicit-formula block satisfies
> \(Q_c^-+\tfrac12M_0+\tfrac12D_0\le(3/40-o(1))N\).

Together with (2), this lemma proves the requested \(85\%\) result
immediately.
