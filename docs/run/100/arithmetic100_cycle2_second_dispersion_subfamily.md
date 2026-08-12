# Zeta-100 arithmetic, cycle 2: Type-III Poisson and the first off-diagonal stratum

## 0. Terminal output

This cycle takes the permitted **precise method-class kill plus concrete
outside calculation** branch.  It does not claim a support extension.

Retain

\[
 \sigma=2.001,\qquad \eta=1.001,\qquad
 H=T^\eta,\qquad L=H/T=H^\rho,\qquad
 \rho={1\over1001},\qquad P=H^{1/3}.                       \tag{1}
\]

Cycle 1 isolated the legitimate all-smooth \(j=j'=3\) Heath--Brown block.
Writing each side as a product of three variables of length \(P\), this
cycle executes the requested Poisson completion before Cauchy.  The
zero dual frequency is exactly the already accepted singular zero mode.
After removing it, the nonzero dual frequencies reduce to one explicit
trilinear Kloosterman-fraction form with parameters

\[
 K=PL=H^{1/3+\rho},\qquad M=N=P^2=H^{2/3}.                 \tag{2}
\]

The Bettin--Chandee trilinear theorem gives, including the Poisson
prefactor,

\[
 \boxed{\mathcal S_{\rm III}^{\ne0}
        \ll H^{5/4+\rho+o(1)}}.                             \tag{3}
\]

The direct count is \(HLH^{o(1)}=H^{1+\rho+o(1)}\), and trace grade is
\(H^{1+o(1)}\).  Thus the single-Poisson/single-trilinear class is not only
insufficient by the exact factor

\[
                         H^{1/4+\rho};                       \tag{4}
\]

at these parameters it is worse than the direct count by \(H^{1/4}\).
Section 3 makes this a precise class obstruction.  No terminal unproved
lemma is used.

The mandatory step outside that class is a second dispersion.  Cycle 1
already removed the full product diagonal.  Here we close a genuinely
off-diagonal family: the two copies have the same two-factor bases

\[
 A_1=A_2,\qquad B_1=B_2,                                   \tag{5}
\]

but different third factors, so the represented integers themselves are
different.  A lattice count retaining the signed shift gives

\[
 \boxed{\mathcal M_{\rm same\ base}\ll
        P^{4}L\,H^{o(1)}=H^{4/3+\rho+o(1)}}.                \tag{6}
\]

The permitted MD budget is \(H^{2-\rho+o(1)}\), so (6) is safe by

\[
 \boxed{H^{-2/3+2\rho+o(1)}
        =H^{-0.664668664\ldots+o(1)}}.                      \tag{7}
\]

This is the first completed Type-III **off-diagonal** calculation after the
one-shot class was killed.  The arithmetic endpoint remains

\[
                         \boxed{\sigma<2},                   \tag{8}
\]

and the accepted capped-profile floor remains

\[
 \boxed{\displaystyle
 \liminf_{T\to\infty}{N_{0,\mathrm{simple}}(T)\over N(T)}
 >0.96250068026-o(1).}                                     \tag{9}
\]

## 1. The Type-III block before absolute values

Suppress fixed smooth weights and polylogarithmic \(r,k\).  The surviving
block is

\[
 \mathcal S_{\rm III}
 =
 \sum_{\ell\asymp L}\omega(\ell/L)
 \sum_{\substack{x_1x_2x_3\asymp H,\ y_1y_2y_3\asymp H\\
 r x_1x_2x_3-k y_1y_2y_3=\ell}}
 \prod_{i=1}^3u_i(x_i)\prod_{i=1}^3v_i(y_i),               \tag{10}
\]

where all six variables are supported in intervals of length \(P\).
One \(u_i\) and one \(v_i\) may contain a logarithmic derivative.  This
changes only \(H^{o(1)}\).

Put

\[
                     a=x_1x_2,\qquad b=y_1y_2.              \tag{11}
\]

After the standard gcd split \(d=(ra,kb)\), divide the equation by \(d\).
There are \(H^{o(1)}\) divisor cases, so it suffices to display the coprime
case.  For fixed \(a,b,\ell\), solve

\[
                       r a x_3-k b y_3=\ell                 \tag{12}
\]

as the progression

\[
                x_3\equiv \ell\,\overline{ra}\pmod{kb}.     \tag{13}
\]

The \(y_3\)-weight is inserted into the smooth \(x_3\)-weight through
\(y_3=(ra x_3-\ell)/(kb)\).  Poisson summation in (13) gives

\[
 {P\over kb}\sum_{h\in\mathbb Z}
 \widehat W_{a,b,\ell}\!\left({hP\over kb}\right)
 e\!\left({h\ell\overline{ra}\over kb}\right).             \tag{14}
\]

Because \(kb\asymp P^2\), rapid decay restricts

\[
                              |h|\ll P H^{o(1)}.             \tag{15}
\]

The term \(h=0\) is the volume/Ramanujan zero mode already subtracted in
the accepted terminal resonance.  Thus (14) is an exact zero/nonzero
separation, not an estimate.

## 2. The nonzero dual form and its exact exponent

For \(h\ne0\), combine \(z=h\ell\).  The resulting coefficient
\(\delta_z\) is a smooth divisor convolution supported at

\[
                         |z|\ll PLH^{o(1)}                  \tag{16}
\]

and obeys

\[
 \|\delta\|_2\ll (PL)^{1/2}H^{o(1)}.                        \tag{17}
\]

The two-factor coefficients

\[
 \alpha_a=\sum_{x_1x_2=a}u_1(x_1)u_2(x_2),\qquad
 \beta_b=\sum_{y_1y_2=b}v_1(y_1)v_2(y_2)                   \tag{18}
\]

satisfy

\[
 \|\alpha\|_2,\|\beta\|_2\ll (P^2)^{1/2}H^{o(1)}
 =P H^{o(1)}.                                              \tag{19}
\]

Up to unit twists and smooth Mellin separation, the nonzero part of (14)
is therefore

\[
 {1\over P}
 \sum_{z\asymp PL}\delta_z
 \sum_{a\asymp P^2}\sum_{b\asymp P^2}
 \alpha_a\beta_b\,e\!\left({z\bar a\over b}\right).         \tag{20}
\]

For reference, the Bettin--Chandee theorem bounds the unprefactored
trilinear form with lengths \(K,M,N\) by

\[
\begin{aligned}
 \|\delta\|_2\|\alpha\|_2\|\beta\|_2
 (KMN)^{7/20+o(1)}
 \left(1+{K\over MN}\right)^{1/2}
 \big[&(M+N)^{1/4}\\
 &+(KMN)^{1/40}(KM+KN)^{1/8}\big].                         \tag{21}
\end{aligned}
\]

Insert (2).  The four exponent contributions, relative to \(H\), are

\[
\begin{array}{c|c}
\text{factor}&\text{exponent}\\ \hline
\|\delta\|_2\|\alpha\|_2\|\beta\|_2&
 5/6+\rho/2\\
(KMN)^{7/20}&7/12+7\rho/20\\
(M+N)^{1/4}&1/6\\
(KMN)^{1/40}(KM+KN)^{1/8}&1/6+3\rho/20 .
\end{array}                                                 \tag{22}
\]

The last row dominates the other bracket term.  The unprefactored bound is

\[
 H^{\,5/6+\rho/2+7/12+7\rho/20+1/6+3\rho/20+o(1)}
 =H^{19/12+\rho+o(1)}.                                     \tag{23}
\]

Multiplication by the Poisson factor \(P^{-1}=H^{-1/3}\) proves (3).

For comparison, counting (10) directly with the divisor bound gives

\[
                         \mathcal S_{\rm III}\ll HLH^{o(1)}.
                                                                    \tag{24}
\]

Hence (3) loses \(H^{1/4}\) even against (24), and misses trace grade by
(4).

## 3. Precise obstruction for the direct completion class

Define \(\mathscr C_{\rm III}^{(1)}\) to consist of arguments which:

1. open the six smooth Type-III variables in (10);
2. solve one third factor by (13) and perform the single Poisson transform
   (14);
3. remove \(h=0\) as the accepted zero mode;
4. collapse \(x_1x_2\), \(y_1y_2\), and \(h\ell\) to the three sequences
   in (17)--(19);
5. apply one Bettin--Chandee/DFI trilinear-fraction estimate, with all
   remaining operations consisting of divisor bounds, \(L^2\) norms, and
   triangle inequality.

Every member of this class has the forced parameters (2): the modulus has
length \(P^2\), the Poisson dual has length \(P\), and the signed shift
enlarges it to \(PL\).  Formula (21) is homogeneous at these forced
lengths, and the dominating term in (22) gives (3).

Therefore:

> **Direct Type-III completion barrier.**  The class
> \(\mathscr C_{\rm III}^{(1)}\) cannot prove trace grade at any fixed
> \(\rho\ge0\).  At \(\rho=1/1001\) its exact exponent deficit is
> \(1/4+\rho\).

Completing both third variables rather than solving one produces a
two-dimensional complete hyper-Kloosterman sum.  Termwise square-root
(Deligne/Weil) bounds merely restore the direct scale after the two dual
sums; without a second average they do not change (24).  Thus a cosmetic
second Poisson transform does not evade the stated class barrier.

## 4. Outside the class: second dispersion with a signed-shift lattice

Use the MD moment

\[
 \sum_{\ell\asymp L}|E_{\rm III}(\ell)|^2
 \ll H^{2-\rho+o(1)}.                                      \tag{25}
\]

Cycle 1 bounded the full product diagonal.  We now retain the two-factor
bases and evaluate the next collision stratum.

In the two copies write

\[
 p_\nu=A_\nu u_\nu,\qquad q_\nu=B_\nu v_\nu,\qquad
 A_\nu,B_\nu\asymp P^2,\quad u_\nu,v_\nu\asymp P.           \tag{26}
\]

Take

\[
 A_1=A_2=A,\qquad B_1=B_2=B,                               \tag{27}
\]

but do **not** impose \(u_1=u_2\) or \(v_1=v_2\).  Equality of the two
signed shifts gives

\[
                 rA(u_1-u_2)=kB(v_1-v_2).                  \tag{28}
\]

Unless both differences vanish, (28) is off-diagonal in the represented
integers.  Put

\[
                            g=(rA,kB).                       \tag{29}
\]

The integer solutions of (28) have

\[
 u_1-u_2={kB\over g}t,\qquad
 v_1-v_2={rA\over g}t.                                     \tag{30}
\]

For a fixed first pair \((u_1,v_1)\), the number of possible second pairs is
therefore

\[
                         \ll 1+{Pg\over P^2}
                         =1+{g\over P}.                     \tag{31}
\]

The first pair must retain the signed selector:

\[
                         rAu_1-kBv_1\in I,\qquad |I|\ll L.  \tag{32}
\]

The left side of (32) is a multiple of \(g\), so the interval \(I\)
contains \(O(1+L/g)\) admissible values.  For each fixed value, all lattice
solutions differ by
\((kB/g,rA/g)\); hence an interval box of side \(P\) contains
\(O(1+g/P)\) of them.  The elementary lattice-strip bound is therefore

\[
 \#\{u_1,v_1\asymp P:rAu_1-kBv_1\in I\}
 \ll \left(1+{L\over g}\right)
      \left(1+{g\over P}\right).                           \tag{33}
\]

Combining (31)--(33), the contribution for fixed \(A,B\) is

\[
                    \ll\left(1+{L\over g}\right)
                       \left(1+{g\over P}\right)^2H^{o(1)}.
                                                                    \tag{34}
\]

The two-factor divisor coefficients cost only \(H^{o(1)}\).  For
\(A,B\asymp P^2\), the standard gcd sums are

\[
\begin{aligned}
 \sum_{A,B\asymp P^2}1&\ll P^4,\\
 \sum_{A,B\asymp P^2}(A,B)&\ll P^4\log P,\\
 \sum_{A,B\asymp P^2}(A,B)^2&\ll P^6H^{o(1)}.              \tag{35}
\end{aligned}
\]

The fixed polylogarithmic \(r,k\) are absorbed in \(H^{o(1)}\).  Since
\(L=H^\rho=P^{3\rho}=o(P)\), summing (34) with (35) yields

\[
\begin{aligned}
 \mathcal M_{\rm same\ base}
 &\ll H^{o(1)}
 \left(P^4+LP^4+{P^4\log P\over P}
       +{P^6\over P^2}+{LP^4\log P\over P^2}\right)\\
 &\ll P^4L\,H^{o(1)}
 =H^{4/3+\rho+o(1)},                                      \tag{36}
\end{aligned}
\]

which proves (6).

Comparison with (25) gives

\[
 {H^{4/3+\rho+o(1)}\over H^{2-\rho}}
 =H^{-2/3+2\rho+o(1)},                                     \tag{37}
\]

proving (7).  This calculation includes the subcase \(t=0\), already safe
by cycle 1, but crucially also closes every \(t\ne0\) in (30), where both
represented products move.

## 5. Handoff

* First Poisson zero mode: exactly the accepted singular main term.
* Forced nonzero-dual lengths: \(K=H^{1/3+\rho}\),
  \(M=N=H^{2/3}\).
* Exact single-trilinear output: \(H^{5/4+\rho+o(1)}\), a deficit
  \(H^{1/4+\rho}\) against trace grade.
* Precise killed class: \(\mathscr C_{\rm III}^{(1)}\).
* First second-dispersion output: the same-two-factor-base off-diagonal is
  \(H^{4/3+\rho+o(1)}\), safely inside MD by
  \(H^{-2/3+2\rho+o(1)}\).
* No arithmetic extension is claimed; the strict floor remains
  \(0.96250068026-o(1)\).
