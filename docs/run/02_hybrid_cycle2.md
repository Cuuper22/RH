# Hybrid cycle 2: exact selector functional and the weighted-Levinson bottleneck

## Outcome

The cycle-1 mixed statistic can be reduced completely to one explicit quadratic functional of the Fourier transform of a hard set of simple critical-line zeros.

Let

$$
\mathscr S_T
=\{\gamma\in[T+T^{1/2},\,2T-T^{1/2}]:
\zeta(\tfrac12+i\gamma)=0,\ \zeta'(\tfrac12+i\gamma)\ne0\}.
$$

Use the localized PRZZ simple-zero result as follows.  For fixed
$\eta>0$ and all sufficiently large $T$, fix

$$
\kappa=0.407511457,\qquad
L_{T,\eta}=\lfloor(\kappa-\eta)N(T,2T)\rfloor.
$$

Write $L_T=L_{T,\eta}$.
Among all subsets of $\mathscr S_T$ of cardinality $L_T$, define
$\mathcal L_T$ to maximize the mixed gain from cycle 1, breaking ties by
lexicographic order of the ordinates.  This is a precise canonical selector,
it consists only of actual simple critical-line zeros, and its atoms can
therefore be deleted from the zero-side Gram matrix without changing any
other block.

Below the harmless $\eta$ subscript is suppressed, and $\eta\downarrow0$
is taken after the $T\to\infty$ limit.

For

$$
Z_{\mathcal L}(y):=\sum_{\gamma\in\mathcal L_T}e^{iy\gamma},
$$

the exact gain over the accepted $0.6725007036\ldots$ bound is

$$
\boxed{
\begin{aligned}
\mathcal J_T(\mathcal L_T)
={}&2\sum_{\gamma\in\mathcal L_T}A_T(\gamma)-L_T\\
&-\frac1{a^2L^2}
\left\{
\int_{-L}^{L}g(y)|Z_{\mathcal L}(y)|^2\,dy
+4\sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}\,
g(\log n)\,\Re Z_{\mathcal L}(\log n)
\right\}
+o(N).
\end{aligned}}
\tag{1}
$$

Here $L=\log(T/2\pi)$, $X=e^L\asymp T$, $\phi$ is the accepted
Montgomery--Taylor window,

$$
a=L^{-1}\int\phi^2,\qquad
g=\phi^2\star\phi^2,
$$

and

$$
A_T(t)=\frac1{a^2L^2}
\int_{\mathbb R}\Phi(t-u)^2\{\mu(u)+\Pi_X(u)\}\,du,
\qquad
\Phi=\widehat{\phi^2}.
\tag{2}
$$

Uniformly in the trimmed window,

$$
A_T(t)=A_\star+o(1),\qquad
A_\star=\frac{b}{a^2}
=1.0061271908\ldots ,
\tag{3}
$$

with

$$
a=\sqrt2\sin(1/\sqrt2),\qquad
b=\frac12+\frac{\sin\sqrt2}{2\sqrt2}.
$$

Thus the desired $85\%$ theorem is reduced to the single explicit assertion

$$
\boxed{\mathcal J_T(\mathcal L_T)
\ge(0.1774992964-o(1))N.}
\tag{4}
$$

No unspecified matrix quantity remains in (4).

The ordinary PRZZ/Levinson calculation does **not** currently imply a
nonzero lower bound for (1).  It evaluates one continuous mollified second
moment and obtains a scalar lower bound for $|\mathscr S_T|$ through a
winding-number argument.  It does not construct a positive counting
submeasure of $\mathscr S_T$, and it gives no estimate for
$Z_{\mathcal L}(y)$ at the continuum of frequencies in (1).  In particular,
the phrase “mollifier-certified set” from cycle 1 cannot be taken literally
without a new weighted form of Levinson's topological lemma.

The strongest unconditional gain obtained in this cycle is therefore still
$0$: choosing $K=0$ recovers $0.6725007\ldots$.  A positive gain for a
nonempty hard selector is not supplied by the accepted inputs.  The exact
new target is now (4), rather than a vague request for “complementarity.”

## 1. Exact normalization of the selector atoms

Let

$$
v_z=(\widehat\phi(z-\tau_k))_{0\le k<d},
\qquad \tau_k=T+\frac{2\pi k}{L}.
$$

For an interior simple line zero $\rho=\tfrac12+it$, its normalized
zero-side atom is

$$
B_t=\frac{v_tv_t^*}{aL^2},\qquad
\operatorname{tr}B_t=1+o(1).
\tag{5}
$$

Poisson summation in the accepted construction gives, uniformly away from
the two ends,

$$
v_t^*v_z=L\Phi(t-z)+o(L).
\tag{6}
$$

Consequently

$$
\operatorname{tr}(B_tB_u)
=W_L(t-u)+o(1),\qquad
W_L(x):=\frac{\Phi(x)^2}{a^2L^2},
\tag{7}
$$

for real $t,u$, and $W_L(0)=1$.

For a selector $\mathcal L\subset\mathscr S_T$, put

$$
K_{\mathcal L}:=\sum_{t\in\mathcal L}B_t.
\tag{8}
$$

This is exactly the $K$ required by the residual certificate: deleting it
removes one whole simple-zero atom for every selected ordinate.

## 2. The $q$ term

Since

$$
\int_{\mathbb R}\Phi(x)^2e^{ixy}\,dx=2\pi g(y),
\qquad \operatorname{supp}g\subset[-L,L],
$$

Fourier inversion and (7) give

$$
\begin{aligned}
\|K_{\mathcal L}\|_F^2
&=\sum_{t,u\in\mathcal L}W_L(t-u)+o(N)\\
&=\frac1{a^2L^2}
\int_{-L}^{L}g(y)|Z_{\mathcal L}(y)|^2\,dy+o(N).
\end{aligned}
\tag{9}
$$

The diagonal part of the integral is exactly

$$
\frac{|\mathcal L|}{a^2L^2}\int_{-L}^{L}g(y)\,dy
=|\mathcal L|,
\tag{10}
$$

because $\int g=(\int\phi^2)^2=a^2L^2$.

## 3. The $x$ term

Let $\widehat G=G/(aL^2)$ be the optimized normalized matrix in the
accepted proof.  From its prime-side integral representation,

$$
\operatorname{tr}(\widehat G B_t)
=\frac1{a^2L^2}
\int_{\mathbb R}\Phi(t-u)^2\nu_X(u)\,du+o(1),
\tag{11}
$$

where

$$
\nu_X(u)=\mu(u)+\Pi_X(u)
-\frac1\pi\sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}\cos(u\log n).
\tag{12}
$$

Using

$$
\int_{\mathbb R}\Phi(t-u)^2\cos(uy)\,du
=2\pi g(y)\cos(ty),
\tag{13}
$$

(11) becomes the explicit Dirichlet polynomial

$$
\operatorname{tr}(\widehat G B_t)
=A_T(t)
-\frac2{a^2L^2}\sum_{n\le X}
\frac{\Lambda(n)}{\sqrt n}g(\log n)\cos(t\log n)
+o(1).
\tag{14}
$$

Summing (14) over $\mathcal L$ gives

$$
\operatorname{tr}(\widehat GK_{\mathcal L})
=\sum_{t\in\mathcal L}A_T(t)
-\frac2{a^2L^2}\sum_{n\le X}
\frac{\Lambda(n)}{\sqrt n}g(\log n)
\Re Z_{\mathcal L}(\log n)
+o(N).
\tag{15}
$$

Substitution of (9) and (15) into

$$
\mathcal J_T
=2\operatorname{tr}(\widehat GK_{\mathcal L})
-\|K_{\mathcal L}\|_F^2-\operatorname{tr}K_{\mathcal L}
\tag{16}
$$

is exactly formula (1).

There is also a useful unconditional sign check that uses only the
zero-side decomposition, not a moment estimate.  Since
$\widehat G-K_{\mathcal L}$ is the sum of all unselected positive
zero-atoms,

$$
\begin{aligned}
\mathcal J_T(\mathcal L)
&=\bigl(\|K_{\mathcal L}\|_F^2-
\operatorname{tr}K_{\mathcal L}\bigr)
+2\operatorname{tr}\{K_{\mathcal L}
(\widehat G-K_{\mathcal L})\}+o(N)\\
&=\sum_{t\ne u\in\mathcal L}\operatorname{tr}(B_tB_u)
+2\operatorname{tr}\{K_{\mathcal L}
(\widehat G-K_{\mathcal L})\}+o(N)\ge-o(N).
\end{aligned}
$$

Thus every hard selector is safe, but the scalar count theorem alone does
not force either nonnegative overlap term to have positive density.  The
sharp equality model from cycle 1 makes the certified simple atoms
orthogonal to one another and to the doubled complement, so a positive
constant cannot be extracted from positivity alone.

## 4. What a weighted Levinson theorem must supply

PRZZ uses

$$
V(s)=Q\!\left(-\frac1{\log T}\frac d{ds}\right)\zeta(s),
\qquad
\sigma_0=\frac12-\frac R{\log T},
\tag{17}
$$

and an explicit mollifier

$$
\psi(s)=\sum_{m\le T^{4/7-\varepsilon}}\frac{b_m}{m^s}.
\tag{18}
$$

Its calculated input is

$$
\mathcal M(Q,\psi,R)
=\frac1T\int_T^{2T}|V(\sigma_0+it)\psi(\sigma_0+it)|^2\,dt.
\tag{19}
$$

Littlewood's lemma and the winding of the associated completed auxiliary
function turn (19) into

$$
|\mathscr S_T|\ge(\kappa-o(1))N.
\tag{20}
$$

The passage (19) $\Rightarrow$ (20) is an inequality between **total
counts**.  It does not label $\kappa N$ zeros, nor does it yield a positive
measure $\sigma_T\le\sum_{\gamma\in\mathscr S_T}\delta_\gamma$ whose
Fourier transform is controlled.

To prove (4), the needed strengthening is:

**Weighted Levinson selection lemma.**  There exists a positive counting
measure

$$
\sigma_T=\sum_{\gamma\in\mathcal L_T}\delta_\gamma,
\qquad
\mathcal L_T\subset\mathscr S_T,\qquad
\sigma_T(\mathbb R)\ge(\kappa-o(1))N,
\tag{21}
$$

such that, with

$$
\widehat\sigma_T(y)
=\int e^{iyt}\,d\sigma_T(t),
\tag{22}
$$

the combined inequality

$$
\begin{aligned}
&2A_\star\sigma_T(\mathbb R)-\sigma_T(\mathbb R)\\
&\quad-\frac1{a^2L^2}\left\{
\int_{-L}^{L}g(y)|\widehat\sigma_T(y)|^2\,dy
+4\sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}
g(\log n)\Re\widehat\sigma_T(\log n)
\right\}\\
&\hspace{35mm}\ge(0.1774992964-o(1))N
\end{aligned}
\tag{WL85}
$$

holds.

This is precisely (4) with (3) inserted.  It is the weakest useful
weighted extension: separate estimates for the quadratic and prime-linear
terms are unnecessary.

## 5. Reduction to mollified shifted integrals

If (21) can be produced by a weighted winding argument, every frequency
needed in (WL85) is generated by inserting a shift into the PRZZ moment.
For $|y|\le L$, define

$$
\mathcal M_y(\alpha,\beta)
=\frac1T\int_T^{2T}
V(\sigma_0+it+\alpha)\psi(\sigma_0+it+\alpha)
\overline{
V(\sigma_0+it+\beta)\psi(\sigma_0+it+\beta)}
e^{iyt}\,dt.
\tag{23}
$$

Expanding (18) and the differential operator in (17) reduces (23) to
finite linear combinations of

$$
\frac1T\int_T^{2T}
\zeta^{(j)}(\sigma_0+it+\alpha)
\zeta^{(k)}(\sigma_0-it+\overline\beta)
\left(\sum_{m\le T^{4/7}}\frac{b_m}{m^{\sigma_0+it+\alpha}}\right)
\left(\sum_{r\le T^{4/7}}
\frac{\overline b_r}{r^{\sigma_0-it+\overline\beta}}\right)
e^{iyt}\,dt.
\tag{24}
$$

For the prime frequencies $y=\log n$, (24) is the relevant twisted
mollified second moment for a *linear* weighted-winding response.  It is
important not to misidentify the quadratic selector energy as another
one-time second moment.  If $H_{Q,\psi}(t)$ denotes the real completed
auxiliary crossing function in a weighted Levinson construction, its
unsigned simple-crossing measure has the explicit regularization

$$
d\omega_\varepsilon(t)
=\frac1\pi\frac{\varepsilon|H'_{Q,\psi}(t)|}
{H_{Q,\psi}(t)^2+\varepsilon^2}\,dt
\ \longrightarrow\
\sum_{H_{Q,\psi}(\gamma)=0\atop H'_{Q,\psi}(\gamma)\ne0}\delta_\gamma.
\tag{25}
$$

A Levinson injection from a chosen set of these crossings to simple zeta
zeros would attach a $0$--$1$ mask $\chi_T$ to (25).  The exact quadratic
quantity to be estimated is then the genuinely two-time integral

$$
\begin{aligned}
\mathcal Q_{\varepsilon}(\chi_T)
&=\frac1{a^2L^2}\int_{-L}^{L}g(y)
\left|\int e^{iyt}\chi_T(t)\,d\omega_\varepsilon(t)\right|^2dy\\
&=\frac1{a^2L^2}\iint
\Phi(t-u)^2\chi_T(t)\chi_T(u)\,
d\omega_\varepsilon(t)d\omega_\varepsilon(u).
\end{aligned}
\tag{26}
$$

After $\varepsilon\downarrow0$, (26) is exactly the first integral in
(WL85).  Thus (23)--(24) expose all of the linear prime-selector twists,
whereas (25)--(26) expose the additional two-level crossing statistic.
The latter is not contained in the scalar PRZZ moment (19); a weighted
topological selection lemma plus a two-time mollified correlation estimate
is genuinely required.

The Dirichlet-polynomial expansion of (24) contains phases

$$
\log\frac{nr}{m}
\tag{27}
$$

with $n\le X\asymp T$ and $m,r\le T^{4/7}$.  Termwise treatment therefore
has effective length as large as $T^{11/7}$; the two-selector expression
has still longer raw products.  The separate moments are outside the
ordinary mean-value range.  Keeping the combination

$$
2\operatorname{tr}(\widehat G K)-\|K\|_F^2
\tag{28}
$$

is essential because it is the only place those longest pieces can cancel
before estimation.

Thus the analytic task is not to recompute the PRZZ scalar moment.  It is
to prove a **weighted winding identity first**, substitute (23)--(26), and
then perform the diagonal/off-diagonal decomposition on (28) as one
object.

## 6. The tractable well-spaced substitute is quantitatively inadequate

One can make a genuinely hard selector analytically manageable by requiring
its ordinates to be separated by

$$
|\gamma-\gamma'|\ge A/L.
\tag{29}
$$

For such a set $S$, the discrete large sieve applied to the prime
polynomial in (14) gives

$$
\sum_{\gamma\in S}
\left|
\sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}
g(\log n)n^{i\gamma}
\right|^2
\ll (T+X)\left(1+\frac LA\right)
\sum_{n\le X}
\frac{\Lambda(n)^2}{n}g(\log n)^2.
\tag{30}
$$

Since

$$
\sum_{n\le X}\frac{\Lambda(n)^2}{n}g(\log n)^2
\ll L^4,
\tag{31}
$$

$D(t)=\sum_{n\le X}b_nn^{it}$ with
$b_n=\Lambda(n)n^{-1/2}g(\log n)$ has discrete mean square
$O(TL^5/A)$.  Thus Cauchy--Schwarz gives, with
$r=|S|/N$,

$$
\operatorname{tr}(\widehat GK_S)
=A_\star|S|+O\!\left(N\sqrt{\frac rA}\right)+o(N).
\tag{32}
$$

The factor $L/A$ in (30) is essential: the ordinates are separated only
on the mean-spacing scale, not by an absolute constant.  Consequently the
prime term is not $o(N)$ for a positive-density selector.

Spacing also gives

$$
\|K_S\|_F^2\le R_\Phi(A)|S|+o(N),
\qquad R_\Phi(A)\longrightarrow1
\quad(A\to\infty),
\tag{33}
$$

by summing the decaying kernel $W_L$ along an $A/L$-separated
sequence.  Hence

$$
\mathcal J_T(S)
\ge\{2A_\star-1-R_\Phi(A)\}|S|
-O\!\left(N\sqrt{\frac rA}\right)+o(N).
\tag{34}
$$

Even if the unresolved prime term in (34) were discarded entirely, the
ideal $A\to\infty$ coefficient would be only

$$
2A_\star-2=0.0122543817\ldots .
\tag{35}
$$

The purely hypothetical product of this coefficient with
$0.407511457N$ is only

$$
0.0049939\ldots,
\tag{36}
$$

which would give about $0.6775$, not $0.85$.  It is not simultaneously
attainable in the $A\to\infty$ limit because packing already forces
$r\le 2\pi/A+o(1)$.  More importantly, the error term in (34) has the same natural
scale as the possible main gain, so this argument proves no positive
constant.  The accepted inputs also do not guarantee a positive-density
$A/L$-separated subset of the simple line zeros for fixed large $A$.

This calculation identifies why the easy selector fails: the discrete
large sieve does not determine the sign of the prime/zero correlation
that supplies the $0.2125N$ thinning gain.  The successful selector must
retain mean-spacing structure and must be analyzed by the combined
twisted moment (28).

## 7. Strongest unconditional statement after cycle 2

For every hard selector $\mathcal L_T\subset\mathscr S_T$, the accepted
matrix theorem plus (1) gives the rigorous implication

$$
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge0.6725007036\ldots
+\frac{\mathcal J_T(\mathcal L_T)}N-o(1).
\tag{37}
$$

Formula (1) is an unconditional exact reduction.  With the presently
accepted inputs:

- $\mathcal L_T=\varnothing$ gives $\mathcal J_T=0$ and recovers
  $0.6725007036\ldots$;
- PRZZ gives enough simple zeros to define a size-$\kappa N$ selector, but
  gives no lower bound for its value in (1);
- a well-spaced tractable selector destroys almost all of the required
  gain and is not known to have the required density.

Therefore no honest unconditional constant above $0.6725007036\ldots$ was
derived on this route in cycle 2.  The blocker is not the old theorem or
matrix bookkeeping.  It is the new weighted two-level statement (WL85).

## 8. Immediate next attack

1. Work with the linear $Q$ used for the PRZZ simple-zero constant, because
   its winding counts simple crossings.
2. Prove a weighted version of the Levinson crossing lemma for test
   functions in the finite cone generated by
   $1$, $\cos(t\log n)$ for $n\le X$, and
   $W_L(t-u)$.  Do not seek all continuous test functions.
3. Apply that lemma directly to the combined functional (28), before
   Cauchy--Schwarz or the arithmetic--geometric mean step in Levinson's
   proof.
4. Expand the resulting object as (23)--(26).  Pair terms with matching
   phase (27) across the $2x-q$ combination before any absolute-value
   estimate.
5. The numerical stopping condition is exactly (WL85); a full asymptotic
   is unnecessary.
