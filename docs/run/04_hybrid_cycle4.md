# Hybrid cycle 4: Littlewood reduction and the optimized linear \(A_c\) mollifier

## Outcome

The exact Routh defect from cycle 3 can be put into the standard
Littlewood--Levinson machine with the common-line multiplicity included,
not discarded as a boundary error.

Let

$$
L=\log(T/2\pi),\qquad
\sigma_0=\frac12-\frac RL,qquad R>0,
\tag{1}
$$

and scale

$$
c=c_T=(a-\tfrac12)L,qquad a>\frac12.
\tag{2}
$$

On the right half-plane the reflected auxiliary function
\(A_{-c}=\xi'+c\xi\), after division by its nonvanishing gamma factor and
by \(aL\), is

$$
V_a(s)=\zeta(s)+\frac1{aL}\zeta'(s)+O(L^{-1})\zeta(s)
=Q_a\!\left(-\frac1L\frac d{ds}\right)\zeta(s)+O(L^{-1})\zeta(s),
\tag{3}
$$

where

$$
Q_a(x)=1-\frac xa.
\tag{4}
$$

Let \(\psi\) be any Dirichlet-polynomial mollifier, and put

$$
I(a,R;\psi)
=\frac1T\int_T^{2T}
|V_a(\sigma_0+it)\psi(\sigma_0+it)|^2\,dt.
\tag{5}
$$

If \(Z_c^+\) denotes the zeros of \(A_{-c}\) in
\(\Re s\ge1/2\), with line zeros counted with their full multiplicity,
then reflection gives

$$
Z_c^+=Q_c^-+M_0.
\tag{6}
$$

Littlewood's lemma and Jensen's inequality give the full one-sided bound

$$
\boxed{
\frac{Q_c^-+M_0}{N}
\le \frac1{2R}\log I(a,R;\psi)+o(1).}
\tag{7}
$$

Consequently the single mean-square inequality

$$
\boxed{I(a,R;\psi)\le e^{0.15R}+o(1)}
\tag{MV85}
$$

implies

$$
Q_c^-+M_0\le(0.075+o(1))N
\quad\Longrightarrow\quad
N_0^s\ge(0.85-o(1))N.
\tag{8}
$$

This is the requested complete Littlewood reduction.  A zero of
\(A_{-c}\) on the line is a common zero of \(\xi,\xi'\); hence (7)
already contains the line-multiplicity charge.  There is no uncounted
resultant boundary term.

Optimizing the rigorously available one-piece mean value at
\(\theta=4/7\) gives only

$$
a=0.9727545\ldots,qquad
R=1.1316935\ldots,qquad
I=1.9670482\ldots,
\tag{9}
$$

and therefore

$$
\frac{Q_c^-+M_0}{N}\le0.2989033937\ldots,\qquad
\frac{N_0^s}{N}\ge0.4021932126\ldots .
\tag{10}
$$

This is weaker than both the accepted multi-piece Levinson result and the
accepted support-one matrix theorem.  The strongest actual unconditional
upper bound for the *exact* resultant defect remains, from the latter,

$$
\boxed{
\limsup_{T\to\infty}\frac{\mathfrak R_c(T)}N
\le0.1637496482\ldots,}
\qquad
\mathfrak R_c=Q_c^-+\frac12M_0+\frac12D_0,
\tag{11}
$$

equivalently \(N_0^s/N\ge0.6725007036\ldots\).  The target is
\(\mathfrak R_c/N\le0.075\), so the unresolved improvement is
\(0.0887496482\ldots N\) in \(\mathfrak R_c\).

The useful new arithmetic object is an explicit geometric mollifier for
\(A_{-c}\).  It has total Dirichlet length \(T\), including *all* powers
of the logarithmic-derivative prime polynomial.  Establishing (MV85) for
that one mollifier is the single mean-value lemma left by this cycle.

## 1. Littlewood inequality with the common-zero boundary

The functional equation gives

$$
A_c(1-s)=-A_{-c}(s).
\tag{12}
$$

Thus every zero of \(A_c\) strictly left of the line reflects to a zero
of \(A_{-c}\) strictly right of it.  On the line,
\(\xi(1/2+it)\) is real and \(\xi'(1/2+it)\) is purely imaginary, so

$$
A_{-c}(\tfrac12+it)=0
\quad\Longleftrightarrow\quad
\xi(\tfrac12+it)=\xi'(\tfrac12+it)=0.
\tag{13}
$$

If \(\xi\) has multiplicity \(m\ge2\) there, \(A_{-c}\) has
multiplicity \(m-1\).  This proves (6).

Apply Littlewood's lemma to \(V_a\psi\) in the rectangle with left edge
\(\sigma_0\).  Every zero with \(\beta\ge1/2\) contributes at least
\(R/L\) to the horizontal zero displacement.  The vertical integral of
\(\log|V_a\psi|\) is bounded by Jensen:

$$
\int_T^{2T}\log|V_a\psi(\sigma_0+it)|\,dt
\le \frac T2\log I(a,R;\psi).
\tag{14}
$$

The right and horizontal sides give \(o(TL)\) after the usual smoothing.
Therefore

$$
2\pi\frac RL Z_c^+
\le\frac T2\log I(a,R;\psi)+o(T),
\tag{15}
$$

and \(N=TL/(2\pi)+o(TL)\) gives (7).  Combining (7) with the coarse
Routh inequality

$$
N_0^s\ge N-2(Q_c^-+M_0)-o(N)
\tag{16}
$$

proves (MV85) \(\Rightarrow\) (8).

The exact square-free correction is weaker:

$$
N_0^s=N-2Q_c^--M_0-D_0+o(N),
\tag{17}
$$

but (16) is preferable analytically because the full boundary
multiplicity is already counted by the same Littlewood rectangle.

## 2. Full optimization of the one-piece mean value

Take \(y=T^\theta\) and

$$
\psi_P(s)=
\sum_{n\le y}\frac{\mu(n)n^{\sigma_0-1/2}}{n^s}
P\!\left(\frac{\log(y/n)}{\log y}\right),
\qquad P(0)=0,\quad P(1)=1.
\tag{18}
$$

For the available one-piece range \(\theta<4/7\), the mollified moment
has the accepted asymptotic

$$
\begin{aligned}
C(P,Q_a,R,\theta)
=1+\frac1\theta\int_0^1\!\int_0^1 e^{2Rv}
\bigl[Q_a(v)P'(u)
+\theta\{RQ_a(v)+Q_a'(v)\}P(u)\bigr]^2\,du\,dv.
\end{aligned}
\tag{19}
$$

This functional can be optimized over *all* admissible \(P\), not just a
finite polynomial ansatz.  Define

$$
\begin{aligned}
A&=\int_0^1e^{2Rv}Q_a(v)^2\,dv,\\
B&=\theta\int_0^1e^{2Rv}Q_a(v)
\{RQ_a(v)+Q_a'(v)\}\,dv,\\
C&=\theta^2\int_0^1e^{2Rv}
\{RQ_a(v)+Q_a'(v)\}^2\,dv,
\qquad k=\sqrt{C/A}.
\end{aligned}
\tag{20}
$$

Since \(\int_0^1PP'=1/2\), (19) is

$$
C(P,Q_a,R,\theta)
=1+\frac1\theta
\left(A\int_0^1P'^2+B+C\int_0^1P^2\right).
\tag{21}
$$

The Euler equation is \(P''=k^2P\), and the minimizing profile is

$$
P_*(u)=\frac{\sinh(ku)}{\sinh k}.
\tag{22}
$$

Polynomial approximations to (22) attain the same infimum.  Integration
by parts yields the closed formula

$$
\boxed{
C_{\min}(a,R,\theta)
=1+\frac{Ak\coth k+B}{\theta}.}
\tag{23}
$$

The certified simple-zero proportion and the corresponding closed Routh
count are

$$
\kappa_{\rm lin}(a,R,\theta)
=1-\frac1R\log C_{\min},
\qquad
\frac{Q_c^-+M_0}{N}
\le\frac{1-\kappa_{\rm lin}}2.
\tag{24}
$$

At \(\theta=4/7\), numerical minimization of the explicit two-variable
function (23) gives (9)--(10).  For comparison, even the *formal*
continuation of (23) to a full one-piece mollifier of length \(T\) gives

$$
\theta=1:\quad
a=1.0656728\ldots,\quad R=0.7611493\ldots,\quad
C_{\min}=1.3698214\ldots,\quad
\kappa_{\rm lin}=0.5865721\ldots .
\tag{25}
$$

At these parameters (MV85) would require

$$
C_{\min}\le e^{0.15R}=1.1209454\ldots,
\tag{26}
$$

so even the formal length-one one-piece model misses the needed moment by
a factor \(1.22202\ldots\).

Continuing the same variational model beyond the unconditional range, the
first mollifier exponent at which it reaches \(85\%\) is

$$
\theta_{85}^{\rm one}=3.0690969\ldots,\quad
R=0.3421613\ldots,\quad a=1.5171189\ldots,\quad
C_{\min}=1.0526641\ldots=e^{0.15R}.
\tag{27}
$$

Equation (27) is not asserted as a theorem.  It quantifies the gap: the
fact that the logarithmic-derivative expansion has support one does not,
by itself, manufacture the effectively \(T^{3.069\ldots}\)-long
mollification demanded by the linear one-piece model.

## 3. The all-orders geometric mollifier at support one

The support observation does produce a substantially sharper *candidate*
than (18).  On the right contour write

$$
Y(s)=\frac{\xi'}{\xi}(s)=A_\Gamma(s)-P_\Lambda(s),
\qquad
P_\Lambda(s)=\sum_{n\ge2}\frac{\Lambda(n)}{n^s}.
\tag{28}
$$

Freezing \(A_\Gamma+c=aL+O(1)\) over the dyadic window gives

$$
\frac{aL}{\zeta(s)\{Y(s)+c\}}
=\frac1{\zeta(s)}
\sum_{k\ge0}\left(\frac{P_\Lambda(s)}{aL}\right)^k.
\tag{29}
$$

Thus define the explicit coefficients

$$
b_a(n;L)
=\sum_{k=0}^{\lfloor\log_2n\rfloor}
\frac{(\mu*\Lambda^{*k})(n)}{(aL)^k},
\tag{30}
$$

where \(\Lambda^{*0}=\delta_1\), and the support-one mollifier

$$
\Psi_{a,W}(s)
=\sum_{n\le T}
\frac{b_a(n;L)n^{\sigma_0-1/2}}{n^s}
W\!\left(\frac{\log(T/n)}L\right).
\tag{31}
$$

Here \(W\) is a fixed smooth taper equal to one away from the two ends.
Every convolution in (30) has total index

$$
n=n_0n_1\cdots n_k\le T.
\tag{32}
$$

Therefore (31) includes all geometric powers without ever asking for an
individual arithmetic frequency above support one.  This is the direct
use of the cycle-3 observation; truncating (29) by the number of powers
would throw away precisely the cancellation it exposes.

The one explicit missing mean-value inequality is

$$
\boxed{
\frac1T\int_T^{2T}
|V_a(\sigma_0+it)\Psi_{a,W}(\sigma_0+it)|^2\,dt
\le e^{0.15R}+o(1)
}
\tag{GMV85}
$$

for at least one \(a>1/2\), \(R>0\), and admissible \(W\).
All coefficients, lengths, and the numerical threshold are explicit in
(30)--(33).  A concrete starting point is

$$
a=1.0656728\ldots,qquad R=0.7611493\ldots,qquad
\text{required right side }=1.1209454\ldots .
\tag{33}
$$

The left side with only the \(k=0\) term is \(1.3698214\ldots\) in the
formal length-one model.  Hence the all-orders terms in (30), kept in
their combined square, must save at least \(0.2488760\ldots\) in the
normalized moment at the starting parameters.

The obstruction to proving (GMV85) is now precise.  Although (31) itself
has length \(T\), opening \(|\zeta\Psi_{a,W}|^2\) term by term recreates
long shifted convolutions.  The support-one advantage survives only if
the identity (29) is used before the diagonal/off-diagonal split.  The
needed theorem is a mean square for the *combined reciprocal symbol*, not
separate estimates for each \(\mu*\Lambda^{*k}\) piece.

## 4. Using the accepted \(86.864\%\) theorem for \(\xi'\)

There is a smaller, local alternative to the global mean (GMV85).  Let
\(\mathcal U_T\) be the simple critical-line zeros of \(\xi'\), and set

$$
a_\eta=
\begin{cases}
\xi(\eta)/\xi''(\eta),&\xi(\eta)\ne0,\\
0,&\xi(\eta)=0.
\end{cases}
\tag{34}
$$

For \(\varepsilon>0\), define

$$
E_\varepsilon
=\sum_{\eta\in\mathcal U_T}
\left(1-\frac{a_\eta}{\sqrt{a_\eta^2+\varepsilon^2}}\right).
\tag{35}
$$

The accepted result gives

$$
|\mathcal U_T|\ge(0.86864\ldots-o(1))N.
\tag{36}
$$

The Sturm--resultant inequality from cycle 3 therefore reduces the target
to

$$
\boxed{
\lim_{\varepsilon\downarrow0}E_\varepsilon
+B_{\rm ns}+D_0
\le(0.01864\ldots-o(1))N.}
\tag{Xi$'$85}
$$

Here \(B_{\rm ns}\) counts bad sign-changing nonsimple critical points.
The arithmetic symbol behind (Xi$'$85) is again support one, because

$$
\frac{\xi}{\xi'}(s)
=\frac1{A_\Gamma(s)-P_\Lambda(s)}
=\sum_{k\ge0}\frac{P_\Lambda(s)^k}{A_\Gamma(s)^{k+1}}
\tag{37}
$$

and a bandwidth-one contour retains only products at most \(T\).

This is the smallest remaining population defect available from the
accepted \(\xi'\) theorem: only \(1.864\%\) of \(N\) may be bad, common,
or bad-nonsimple after the certified simple \(\xi'\) zeros are used.  A
mere additional count of \(\xi'\) zeros cannot help; the sign of the
residue (34) is the required datum.

## 5. Numerical decision and next attack

The actual unconditional bounds after optimization are:

| input | upper bound for a Routh defect | resulting simple-line bound |
|---|---:|---:|
| optimized one-piece \(A_c\), \(\theta=4/7\) | \((Q_c^-+M_0)/N\le0.2989034\) | \(0.4021932\) |
| accepted multi-piece Levinson comparator | \(\approx0.2962443\) | \(0.4075114\) |
| accepted support-one matrix identity | \(\mathfrak R_c/N\le0.16374965\) | \(0.67250070\) |
| required | \(\mathfrak R_c/N\le0.075\) | \(0.85\) |

The construction has not closed \(85\%\).  It has reduced the next cycle
to either one of two explicit inequalities:

1. prove (GMV85) for the coefficients (30), preferably at the numerical
   starting point (33); or
2. prove the residue-sign bound (Xi$'$85), using the all-orders expansion
   (37) before separating its convolution powers.

Of these, (GMV85) is the direct continuation of the Routh certificate and
has a standard Littlewood conversion with no further combinatorics.
