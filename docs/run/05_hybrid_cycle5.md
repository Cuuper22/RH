# Hybrid cycle 5: exact geometric cancellation and the analytic tail

## Outcome

Let

$$
\mathcal P(s)=\sum_{n\ge2}\frac{\Lambda(n)}{n^s}
=-\frac{\zeta'}{\zeta}(s),\qquad
G_a(s)=\zeta(s)+\frac{\zeta'(s)}{aL}
=\zeta(s)\left(1-\frac{\mathcal P(s)}{aL}\right).
\tag{1}
$$

On \(\Re s>1\), the all-orders formal inverse is

$$
B_a(s)=\frac1{G_a(s)}
=\frac1{\zeta(s)}
\sum_{k\ge0}\left(\frac{\mathcal P(s)}{aL}\right)^k
=\sum_{n\ge1}\frac{b_a(n)}{n^s},
\tag{2}
$$

where the first product in (2) is to be read as
\(\zeta(s)^{-1}\sum_{k\ge0}(\mathcal P(s)/(aL))^k\), and

$$
b_a(n)=
\sum_{k=0}^{\lfloor\log_2 n\rfloor}
\frac{(\mu*\Lambda^{*k})(n)}{(aL)^k}.
\tag{3}
$$

For a hard cutoff \(X\), put

$$
\psi_{a,X}(s)=\sum_{n\le X}\frac{b_a(n)}{n^s}.
\tag{4}
$$

Writing

$$
g_a(n)=1-\frac{\log n}{aL},
\qquad
G_a(s)=\sum_{n\ge1}\frac{g_a(n)}{n^s},
\tag{5}
$$

gives the exact renewal identity

$$
\boxed{
G_a(s)\psi_{a,X}(s)
=1+\sum_{m>X}\frac{r_{a,X}(m)}{m^s},\qquad \Re s>1,}
\tag{6}
$$

with

$$
\begin{aligned}
r_{a,X}(m)
&=\sum_{\substack{d\mid m\\d\le X}}
b_a(d)g_a(m/d)\\
&=-\sum_{\substack{d\mid m\\d>X}}
b_a(d)g_a(m/d)
\qquad(m>1).
\end{aligned}
\tag{7}
$$

In particular \(r_{a,X}(m)=0\) for \(2\le m\le X\).  Formula (7)
combines every \(k\) before any absolute value and is the requested
Buchstab/renewal form of the tail.

The decisive obstruction is analytic continuation.  On the shifted line
\(\sigma_0=1/2-R/L\), (6) is not a convergent Dirichlet-series identity.
Perron continuation crosses poles of \(1/G_a\), and the corresponding
residues are precisely the zeros counted by the Routh certificate.  Thus
the support-one coefficient cancellation does not by itself make the
shifted mean square small.

At the concrete length-one starting point from cycle 4,

$$
a=1.0656728\ldots,\qquad R=0.7611493\ldots,
\tag{8}
$$

the stopping condition is

$$
I(a,R;\psi_{a,T})\le e^{0.15R}
=1.12094536\ldots .
\tag{9}
$$

If

$$
G_a(\sigma_0+it)\psi_{a,T}(\sigma_0+it)=1+\mathcal T_a(t),
\tag{10}
$$

then the exact normalized allowance for the complete analytically
continued tail is

$$
\boxed{
2\Re\langle 1,\mathcal T_a\rangle
+\|\mathcal T_a\|_2^2
\le0.12094536\ldots .}
\tag{Tail85}
$$

No unconditional estimate obtained in this cycle proves (Tail85).  The
strongest actual unconditional Routh-defect bound remains

$$
\limsup\frac{\mathfrak R_c(T)}N
\le0.1637496482\ldots ,
\tag{11}
$$

equivalent to the accepted \(0.6725007036\ldots\) simple-line theorem.
The target remains \(0.075\).

The finite-order calculation does produce one rigorous negative result:
the \(K=1\) geometric correction supplies no new mollifier freedom at
all.  With arbitrary smooth cutoffs it collapses exactly to the optimized
one-piece Möbius mollifier.  The first genuinely new arithmetic term is
\(K=2\); estimating its combined tail requires the explicit bilinear form
in Section 4.

## 1. Exact inverse and hard-cutoff tail

Let

$$
x(s)=\frac{\mathcal P(s)}{aL}.
\tag{12}
$$

Since \(G_a=\zeta(1-x)\), one has, absolutely on a fixed line
\(\Re s=1+\delta\),

$$
G_a(s)\,
\frac1{\zeta(s)}\sum_{k\ge0}x(s)^k=1.
\tag{13}
$$

This proves (2)--(3).  If \(b_a^{>X}\) denotes the tail of the inverse,
then

$$
G_a\psi_{a,X}
=1-G_a\sum_{n>X}\frac{b_a(n)}{n^s}.
\tag{14}
$$

Opening the convolution in (14) gives (6)--(7).

For a smooth cutoff \(\omega_X(d)\), the corresponding exact coefficient
is

$$
r_{a,X,\omega}(m)
=\sum_{d\mid m}b_a(d)\omega_X(d)g_a(m/d)-\delta_{m,1}.
\tag{15}
$$

Using the full inverse relation, this can be written in the commutator
form

$$
r_{a,X,\omega}(m)
=\sum_{d\mid m}b_a(d)\{\omega_X(d)-1\}g_a(m/d)
\qquad(m>1).
\tag{16}
$$

Thus smoothing merely redistributes the inverse error from the sharp
boundary \(d=X\); it does not create an additional main term.

The renewal recurrence is also explicit:

$$
b_a(1)=1,\qquad
b_a(n)=-\sum_{\substack{d\mid n\\d<n}}
b_a(d)\left(1-\frac{\log(n/d)}{aL}\right)
\quad(n>1).
\tag{17}
$$

Equations (7), (16), and (17) give three equivalent forms in which all
geometric orders have already been combined.

## 2. Perron continuation and the zero residues

For nonintegral \(X\) and initially \(\Re s>1\), Perron's formula gives

$$
\psi_{a,X}(s)
=\frac1{2\pi i}\int_{(\kappa)}
\frac{X^w}{w\,G_a(s+w)}\,dw,
\qquad
\kappa>1-\Re s.
\tag{18}
$$

Hence

$$
G_a(s)\psi_{a,X}(s)
=\frac1{2\pi i}\int_{(\kappa)}
\frac{G_a(s)}{G_a(s+w)}\frac{X^w}{w}\,dw.
\tag{19}
$$

Moving the \(w\)-contour left crosses \(w=0\), producing the \(1\) in
(6), but it also crosses

$$
w=\rho_a-s,\qquad G_a(\rho_a)=0.
\tag{20}
$$

For a simple zero, the additional residue is

$$
\mathcal R_{\rho_a}(s)
=\frac{G_a(s)}{G_a'(\rho_a)}
\frac{X^{\rho_a-s}}{\rho_a-s}.
\tag{21}
$$

Multiple zeros give the corresponding higher residue.  Therefore the
analytic continuation of (6) to \(\sigma_0\) is

$$
G_a(s)\psi_{a,X}(s)
=1+\sum_{\rho_a\ {\rm crossed}}\mathcal R_{\rho_a}(s)
+\mathcal J_{a,X}(s),
\tag{22}
$$

where \(\mathcal J_{a,X}\) is the final vertical integral in (19).

For the reflected \(A_{-c}\), the zeros \(\rho_a\) crossed between
\(\sigma_0\) and the right half-plane include

$$
Q_c^-+M_0,
\tag{23}
$$

the same closed-half-plane count appearing in the Littlewood bound.
Thus a proof which shifts (19) and simply declares the final integral
small is circular unless it estimates the residue sum (21).  The
geometric frequency support controls the symbol on the initial right
line; it does not remove the zero poles encountered en route to
\(\sigma_0\).

Substituting (22) in (Tail85) gives the exact residue-tail target

$$
\boxed{
2\Re\left\langle1,
\sum_{\rho_a}\mathcal R_{\rho_a}+\mathcal J_{a,T}\right\rangle
+\left\|
\sum_{\rho_a}\mathcal R_{\rho_a}+\mathcal J_{a,T}
\right\|_2^2
\le0.12094536\ldots .}
\tag{24}
$$

This is one explicit nonnegative combined statistic.  It must be
estimated as a whole; separate absolute-value bounds on the residues and
the final contour lose the cancellation which the inverse was designed
to create.

## 3. Finite geometric order

Define

$$
B_{a,K}(s)
=\frac1{\zeta(s)}\sum_{k=0}^Kx(s)^k
=\sum_{n\ge1}\frac{b_{a,K}(n)}{n^s}.
\tag{25}
$$

Before the length cutoff there is an exact telescoping identity

$$
\boxed{G_a(s)B_{a,K}(s)=1-x(s)^{K+1}.}
\tag{26}
$$

After truncation at \(X\),

$$
G_a(s)\sum_{n\le X}\frac{b_{a,K}(n)}{n^s}
=1-x(s)^{K+1}
-G_a(s)\sum_{n>X}\frac{b_{a,K}(n)}{n^s}.
\tag{27}
$$

Thus the two errors are exactly:

1. the geometric residual
   \(-\mathcal P(s)^{K+1}/(aL)^{K+1}\);
2. the cutoff renewal tail.

They must be combined before either is bounded.

For \(K=0\), \(b_{a,0}=\mu\).  For \(K=1\),

$$
(\mu*\Lambda)(n)=-\mu(n)\log n,
\tag{28}
$$

and hence

$$
b_{a,1}(n)
=\mu(n)\left(1-\frac{\log n}{aL}\right).
\tag{29}
$$

Let \(X=T^\theta\) and
\(u=\log(X/n)/\log X\).  Then

$$
1-\frac{\log n}{aL}
=1-\frac{\theta(1-u)}a.
\tag{30}
$$

Even if the \(K=0\) and \(K=1\) pieces are given independent smooth
cutoffs \(W_0(u)\) and \(W_1(u)\), their sum is

$$
\mu(n)\left\{
W_0(u)-\frac{\theta(1-u)}aW_1(u)
\right\}.
\tag{31}
$$

The expression in braces is just one arbitrary smooth one-piece profile.
Conversely, when \(a>\theta\), every admissible one-piece profile is
obtained by a smooth choice of \(W_0,W_1\).  Therefore:

> **No-gain lemma for \(K=1\).**  Adding the first geometric correction,
> with arbitrary smooth cutoff, cannot improve the optimized one-piece
> constant from cycle 4.

The first new divisor-sensitive coefficient is

$$
(\mu*\Lambda*\Lambda)(n)
=\mu(n)(\log n)^2+(\mu*(\Lambda\log))(n).
\tag{32}
$$

For square-free \(n\), this becomes

$$
(\mu*\Lambda*\Lambda)(n)
=\mu(n)\left\{(\log n)^2
-\sum_{p\mid n}(\log p)^2\right\}
=2\mu(n)\sum_{\substack{p<q\\pq\mid n}}\log p\log q.
\tag{33}
$$

This dependence on the individual prime factors cannot be absorbed into
a one-variable cutoff.  Hence \(K=2\) is the first finite-order attack
which can produce an actual improvement.

No new unconditional constant follows merely from (33).  Its shifted
mean requires the \(K=2\) instance of the tail bilinear form below.  If
one suppresses that new piece, the best actual linear-\(A_c\) result
remains the optimized \(0.4021932\ldots\) from cycle 4; the accepted
multi-piece construction remains the stronger Levinson comparator.

## 4. Explicit coefficient tail energy and numerical allowance

Let \(w\) be a fixed smooth probability density supported in \([1,2]\),
and define

$$
\widehat w_T(y)=\int_1^2w(u)e^{-iTuy}\,du.
\tag{34}
$$

For a tail polynomial

$$
\mathcal T_{X,M}(t)
=\sum_{X<m\le M}
\frac{r_{a,X,\omega}(m)}{m^{\sigma_0+it}},
\qquad M\le T,
\tag{35}
$$

its exact height-averaged energy is the explicit bilinear form

$$
\boxed{
\mathcal E_{a,R}(X,M;\omega)
=\sum_{\substack{X<m,n\le M}}
\frac{r_{a,X,\omega}(m)
\overline{r_{a,X,\omega}(n)}}
{(mn)^{1/2-R/L}}\,
\widehat w_T(\log(m/n)).}
\tag{36}
$$

The diagonal is

$$
\mathcal D_{a,R}(X,M;\omega)
=\sum_{X<m\le M}
\frac{|r_{a,X,\omega}(m)|^2}{m^{1-2R/L}}.
\tag{37}
$$

For \(M\le T^{1-\varepsilon}\), smooth Fourier decay gives

$$
\mathcal E_{a,R}
=\mathcal D_{a,R}+o(1)
\tag{38}
$$

under the usual coefficient divisor bounds.  At \(M\asymp T\), (36),
not the separated diagonal, is the correct endpoint object.

At the numerical starting point (8), the complete direct, dual, and
Perron-residue continuation must satisfy

$$
\boxed{
\mathcal E_{\rm direct}
+\mathcal E_{\rm dual}
+2\Re\mathcal E_{\rm cross}
+2\Re\langle1,\mathcal T_a\rangle
\le0.12094536\ldots .}
\tag{39}
$$

The direct term below support one is obtained from (36) with the
coefficients (7) or (16).  The remaining three terms are the analytic
continuation of the portion \(m>T\), equivalently the residue/integral
combination (24).  Equation (39) is the precise coefficient-bilinear
allowance requested in the fallback.

For a hard length-\(T\) inverse, (7) makes

$$
r_{a,T}(m)=0\qquad(2\le m\le T).
\tag{40}
$$

Thus \(\mathcal E_{\rm direct}=0\) throughout the entire evaluable
support-one range.  All of the error has been pushed into the dual and
Perron-residue terms beyond that range.  This is the exact reason the
formal inverse appears perfect on the prime side while (GMV85) remains
unproved.

For \(X<T\), the renewal tail (7) becomes visible inside (36), allowing a
trade between a nonzero direct energy and a shorter continuation tail.
The optimization problem is now explicit:

$$
\inf_{\substack{a>1/2,\ R>0,\ 0<\theta\le1\\
X=T^\theta,\ \omega}}
\left[
\mathcal E_{\rm direct}
+\mathcal E_{\rm dual}
+2\Re\mathcal E_{\rm cross}
+2\Re\langle1,\mathcal T_a\rangle
\right]
\le e^{0.15R}-1.
\tag{41}
$$

## 5. Strongest conclusion and next attack

The all-orders cancellation is exact in the half-plane of absolute
convergence, but a direct unconditional proof of (GMV85) was not obtained.
The obstacle is no longer an uncombined list of convolution powers.  It
is the single residue/dual energy (24), or equivalently the endpoint
bilinear completion in (39).

The strongest actual numerical conclusions are:

- \(K=1\) gives no improvement over the optimized one-piece result,
  rigorously, by (28)--(31);
- \(K=2\) is the first genuinely new finite-order term, with explicit
  coefficient (32)--(33), but its combined shifted mean is not supplied
  by the support-one coefficient identity;
- the exact Routh defect remains bounded by
  \(0.1637496482\ldots N\), not the required \(0.075N\).

The next constructive lemma should be stated in either of two exactly
equivalent forms:

1. **Perron-residue form:** prove (24) with right side
   \(0.12094536\ldots\) at (8);
2. **coefficient form:** prove (39), using (7) inside support one and
   retaining the direct/dual cross term at the endpoint.

Both formulations preserve all geometric orders before estimation.  A
termwise bound for the individual \(\mu*\Lambda^{*k}\) pieces discards the
only cancellation capable of meeting the numerical allowance.
