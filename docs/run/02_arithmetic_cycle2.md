# Arithmetic construction, cycle 2: Fourier-first dispersion at the 85% scale

## 0. Outcome

Take all of cycle 1 and the two PDFs as established.  The factor-
\(H\) problem in (AS) can be localized much more sharply than an
exceptional-shift formulation suggests.

For the connected \(85\%\) target

\[
 \sigma=1.42960385087046,
 \qquad H=X/T=X^\theta,
 \qquad \theta=1-\frac1\sigma=0.300505521588293\ldots . \tag{1}
\]

(The convenient rational benchmark \(\sigma=143/100\) gives
\(\theta=43/143=0.300699300699\ldots\).)

Writing the signed \(h\)-average by Fourier inversion before applying
absolute values puts the prime polynomial on a band

\[
             \xi\asymp \frac{T}{X}=\frac1H,
             \qquad |\Delta\xi|\asymp \frac1H.                 \tag{2}
\]

Partitioning this band into the reciprocal cells

\[
              \xi=\frac1q+\eta,qquad q\asymp H,qquad
              |\eta|\ll H^{-2}                                  \tag{3}
\]

turns (AS) into a **fixed-additive-frequency, short-interval
Barban--Davenport--Halberstam estimate**.  The auxiliary short-interval
length is

\[
       Y=H^2=X^{2\theta}=X^{0.601011043176586\ldots}.             \tag{4}
\]

The exact missing estimate has natural size

\[
       XYH=X^{1+3\theta}=X^{1.901516564764879\ldots};             \tag{5}
\]

ordinary BDH, the hybrid large sieve, or the MRT local \(L^2\) estimate
gives \(XYH^2\), losing exactly one factor \(H\).  Thus enlarging the
Farey dissection to \(q\asymp H<X^{1/2}\) identifies the correct object,
but Bombieri--Vinogradov/BDH by itself does not prove it: those theorems
sum all additive frequencies modulo \(q\), whereas the trace selects the
single low frequency \(a=1\).

Sections 1--5 below prove the reduction.  Section 6 states the single
remaining Type-II inequality, with exact variables and exponents.

## 1. Exact Fourier identity for the signed shift average

Put \(e(z)=e^{2\pi iz}\).  Let \(V\in C_c^\infty((1,2))\), and define

\[
 P_X(\xi)=\sum_n\Lambda(n)V(n/X)e(n\xi),
\]

\[
 C_{X,V}(h)=\sum_n\Lambda(n)\Lambda(n+h)
              V(n/X)V((n+h)/X).
\]

For every Schwartz function \(w\), Poisson summation and Parseval give
the exact identity

\[
 \sum_{h\in\mathbb Z}w(h/H)C_{X,V}(h)
 =\int_0^1 |P_X(\xi)|^2 W_H(-\xi)\,d\xi,                         \tag{6}
\]

where

\[
 W_H(\xi)=\sum_{h\in\mathbb Z}w(h/H)e(h\xi)
          =H\sum_{k\in\mathbb Z}\widehat w\bigl(H(k-\xi)\bigr). \tag{7}
\]

For the endpoint kernel coming from (4) of cycle 1, after a smooth
height taper, \(W_H\) is a finite linear combination of functions of
size \(H\), supported (up to rapid decay) on bands

\[
                  c/H\le |\xi|\le C/H                           \tag{8}
\]

with fixed \(0<c<C\).  Therefore a bound

\[
 \int_{c/H}^{C/H}|P_X(\xi)-P_X^{\rm maj}(\xi)|^2\,d\xi
       \ll_A \frac{X}{H}\log^{-A}X                              \tag{9}
\]

after subtracting the explicit diagonal and Ramanujan main terms gives
\(O_A(X\log^{-A}X)\) in (6), which is precisely the missing factor-
\(H\) strength in (AS).  A polylogarithmic version of (9) already removes
the power loss and is trace-grade; a sharp constant or a logarithmic
saving can then be retained according to which of the connected or
sparse certificates is used.

The important point is that (6), rather than a sum of absolute values
over shifts, is the object to estimate.

## 2. Reciprocal-cell decomposition of the local band

It is enough to discuss \([1/H,2/H]\); fixed dilates are identical.  For
integers \(q\in[H/2,H]\), let \(I_q\) be the interval bounded by the
midpoints between \(1/(q-1),1/q,1/(q+1)\).  Then

\[
 [1/H,2/H]=\bigcup_{H/2+O(1)\le q\le H+O(1)} I_q,
 \qquad |I_q|\asymp q^{-2}\asymp H^{-2},                         \tag{10}
\]

and every \(\xi\in I_q\) has a unique representation

\[
                  \xi=1/q+\eta,\qquad |\eta|\ll H^{-2}.          \tag{11}
\]

Choose a smooth bounded-overlap partition \(\{\chi_q\}\) subordinate
to these cells.  The prime polynomial's local major term is

\[
 P_{q}^{\rm maj}(\eta)
   =\frac{\mu(q)}{\varphi(q)}
      \sum_nV(n/X)e(n\eta).                                     \tag{12}
\]

Indeed, equidistribution of primes in the reduced classes modulo \(q\)
gives the Ramanujan sum
\(\sum_{(a,q)=1}e(a/q)=\mu(q)\).  Define the balanced reciprocal-mode
coefficients

\[
 b_q(n)=V(n/X)
       \left(\Lambda(n)e(n/q)-\frac{\mu(q)}{\varphi(q)}\right)    \tag{13}
\]

and

\[
 R_q(\eta)=\sum_n b_q(n)e(n\eta).                               \tag{14}
\]

Poisson summation applied to the smooth \(V\)-sum shows that (14)
differs from
\(P_X(1/q+\eta)-P_q^{\rm maj}(\eta)\) by \(O_A(X^{-A})\), uniformly
on (11).  Consequently

\[
 \int_{1/H}^{2/H}|P_X-P_X^{\rm maj}|^2
 \ll \sum_{q\asymp H}\int_{|\eta|\ll H^{-2}}|R_q(\eta)|^2d\eta
       +O_A(X^{-A}).                                             \tag{15}
\]

No individual shifted-prime estimate has been used.

## 3. Exact short-interval form

Set \(Y=H^2\).  For a fixed smooth \(g\), put

\[
 B_q(x;g)=\sum_n b_q(n)g\left(\frac{n-x}{Y}\right).              \tag{16}
\]

Fourier inversion in \(x\) gives the exact Plancherel identity

\[
 \int_{\mathbb R}|B_q(x;g)|^2dx
   =Y^2\int_{\mathbb R}|R_q(\eta)|^2
                     |\widehat g(Y\eta)|^2d\eta.                 \tag{17}
\]

A finite family of \(g\)'s majorizes the cell cutoffs in (15), without
changing any exponent.  Hence the following lemma implies (9).

### Fixed-mode short-interval BDH lemma

Let \(H=X^\theta\), with \(\theta\) as in (1), and \(Y=H^2\).  For each
of the finitely many smooth windows \(g\) generated by the height/lobe
weights, one has, after subtracting the explicit diagonal and Ramanujan
main term \(\mathcal M_g(X,H)\),

\[
 \boxed{
 \sum_{H/2<q\le H}\int_{\mathbb R}|B_q(x;g)|^2dx
       -\mathcal M_g(X,H)
       \ll_A XYH\log^{-A}X .}                                   \tag{FM-BDH}
\]

The same assertion with \(\log^{C}X\) in place of \(\log^{-A}X\)
removes the forbidden power loss.  For a constant-sensitive \(85\%\)
certificate, retain the diagonal in \(\mathcal M_g\) and require the
one-sided remainder with the corresponding \(\delta\) from Section 7.

### Proof that (FM-BDH) implies (AS)

Divide (FM-BDH) by \(Y^2=H^4\) and apply (17).  Since

\[
             \frac{XYH}{Y^2}=\frac{X}{H},                        \tag{18}
\]

the local balanced energy in (15) is
\(O_A(XH^{-1}\log^{-A}X)\).  Multiplication by the size \(H\) of the
kernel in (7) gives \(O_A(X\log^{-A}X)\).  Expanding (12) and summing
the Ramanujan coefficients reconstructs the singular-series term in
(AS), while the \(h=0\) term in (6) is exactly the diagonal included in
\(\mathcal M_g\).  Smooth dyadic partial summation supplies all
\(n\)-derivatives occurring in the exact weight (7) of cycle 1.  This
proves (AS) for each required cross-lobe weight.  \(\square\)

Thus (FM-BDH), not an almost-all-shifts Hardy--Littlewood theorem, is
the precise aggregate statement.

## 4. Dispersion expansion and the exact factor lost by standard BDH

Let

\[
 K_g(t)=\int_{\mathbb R}g(u)\overline{g(u+t)}\,du.
\]

Expanding (16) before taking an absolute value gives

\[
 \begin{aligned}
 \sum_{q\asymp H}\int|B_q(x;g)|^2dx
  =Y\sum_{q\asymp H}\sum_{n_1,n_2}
   &V(n_1/X)V(n_2/X)K_g((n_1-n_2)/Y)\\
   &\times
   \left(\Lambda(n_1)e(n_1/q)-\frac{\mu(q)}{\varphi(q)}\right)
   \overline{
   \left(\Lambda(n_2)e(n_2/q)-\frac{\mu(q)}{\varphi(q)}\right)}.
                                                                    \tag{19}
 \end{aligned}
\]

The diagonal of (19) has natural size \(XYH\log X\); it is explicit
and belongs to \(\mathcal M_g\).  The off-diagonal is a signed
dispersion sum with \(|n_1-n_2|\ll Y=H^2\) and phase
\(e((n_1-n_2)/q)\).  This is the cancellation which must be retained.

For comparison, write the short-interval discrepancy in residue class
\(a\pmod q\) as \(E_{q,a}(x;Y)\).  The additive mode in (16) is

\[
             A_{q,1}(x;Y)=\sum_{a\bmod q}e(a/q)E_{q,a}(x;Y).      \tag{20}
\]

Parseval over *all* additive modes gives

\[
  \sum_{r\bmod q}|A_{q,r}(x;Y)|^2
       =q\sum_{a\bmod q}|E_{q,a}(x;Y)|^2.                        \tag{21}
\]

A short-interval BDH estimate inserted into (21) yields

\[
       \sum_{q\asymp H}\sum_{r\bmod q}\int|A_{q,r}|^2
          \ll XYH^2\log^C X.                                    \tag{22}
\]

Bounding the selected \(r=1\) term by (22) therefore gives
\(XYH^2\), not \(XYH\).  The hybrid large sieve gives the same result
because its conductor is

\[
                  Y+H^2=2H^2.                                   \tag{23}
\]

After division by \(Y^2\), (22) gives local energy \(O(X\log^C X)\),
which is MRT's scale and is a factor \(H\) above (9).  Numerically,

\[
 \begin{array}{c|c}
 \text{quantity}&\text{power of }X\\ \hline
 \text{required local energy }X/H&0.699494478411707\ldots\\
 \text{MRT/local-BDH energy }X&1\\
 \text{raw hybrid-large-sieve energy }X^2/H^2&1.398988956823414\ldots
 \end{array}                                                       \tag{24}
\]

Bombieri--Vinogradov is applicable to the modulus size
\(q=H<X^{1/2}\), but it controls a residue-class average and does not
provide the missing equidistribution among the \(q\) additive Fourier
modes in (21).  That is the exact reason it does not by itself close
(FM-BDH).

## 5. Heath--Brown/Vaughan decomposition without destroying the signed average

Apply the same finite Heath--Brown decomposition used in the MRT
infrastructure, but apply it inside (19), not separately for each
shift.  Type-I blocks have a short variable and their zero-frequency
terms contribute to \(\mathcal M_g\).  Poisson summation in the long
variable reduces their nonzero frequencies to the right side of
(FM-BDH), with arbitrary logarithmic saving after the dyadic windows
are smoothed.

The remaining blocks are finite linear combinations

\[
 f_j(n)=(\alpha_j*\beta_j)(n)V(n/X),                              \tag{25}
\]

where, writing \(N=X^\nu\) and \(M=X/N\),

\[
 X^\varepsilon\le N\le HX^{-\varepsilon},
 \quad \varepsilon\le\nu\le\theta-\varepsilon,
 \quad M=X^{1-\nu},                                               \tag{26}
\]

and the coefficients are fixed-divisor-bounded and have the good-
cancellation property furnished by the decomposition.  Polarization
must be postponed until after all the blocks have been recombined;
termwise Cauchy--Schwarz would lose the constant and, in its crude
form, the same factor \(H\).

## 6. Narrowest remaining Type-II inequality

For coefficients as in (26), define

\[
 \begin{aligned}
 \mathcal D_{\alpha,\beta}(X,H;g)
 :=\sum_{q\asymp H}\sum_{m_1,m_2\asymp N}
    \sum_{n_1,n_2\asymp M}
   &\alpha_{m_1}\beta_{n_1}
    \overline{\alpha_{m_2}\beta_{n_2}}\\
   &\times V(m_1n_1/X)V(m_2n_2/X)\\
   &\times K_g\!\left(\frac{m_1n_1-m_2n_2}{H^2}\right)
    e\!\left(\frac{m_1n_1-m_2n_2}{q}\right).
                                                                    \tag{27}
 \end{aligned}
\]

Let \(\mathcal M_{\alpha,\beta}\) be the diagonal plus the zero
frequency/Ramanujan terms obtained by setting the dual Poisson
frequencies equal to zero.  The single missing assertion is

\[
 \boxed{
 \mathcal D_{\alpha,\beta}(X,H;g)
       -\mathcal M_{\alpha,\beta}(X,H;g)
       \ll_A XH\log^{-A}X,}                                      \tag{BI\(_\theta\)}
\]

uniformly for

\[
 \theta=0.300505521588293\ldots,quad
 q\asymp H=X^\theta,quad
 |m_1n_1-m_2n_2|\ll H^2=X^{2\theta},quad
 \varepsilon\le\nu\le\theta-\varepsilon.                       \tag{28}
\]

For the rational benchmark \(\theta=43/143\), the exponents in
(BI\(_\theta\)) are

\[
 q=X^{43/143},\qquad |m_1n_1-m_2n_2|\ll X^{86/143},qquad
 (BI)_\theta\text{ remainder }\ll X^{186/143}\log^{-A}X.         \tag{29}
\]

Multiplying (27) by the outer factor \(Y=H^2\) recovers
(FM-BDH), since

\[
                 Y\cdot XH=XH^3=XYH.                             \tag{30}
\]

Thus (BI\(_\theta\)) is exactly the factor-\(H\) Type-II statement,
with no exceptional-shift decomposition and no absolute value taken
before the reciprocal-modulus phase has been used.

A dispersion proof should next proceed by separating
\(d=(m_1,m_2)\), applying additive reciprocity to the \(q\)-phase,
and using a Kuznetsov/reciprocal large sieve on the resulting
Kloosterman family.  The required spectral estimate must save \(H\)
over (22), i.e. it must control the selected additive mode directly,
not by the sum over all modes.  This is the only power-saving sublemma
left by the Fourier-first reduction.

## 7. Weight and lobe optimization: how sharp must the one-sided lemma be?

The scale-free width-one lobe cost accepted from cycle 1 is

\[
                    D_1=1.3274992963205883.                       \tag{31}
\]

Suppose the arithmetic lemma gives cross-lobe kernel at most
\(1+\delta\), rather than the asymptotic value \(1\).  For \(K\)
equal lobes,

\[
 D_K(\delta)\le \frac{D_1}{K}
                   +(1+\delta)\left(1-\frac1K\right).            \tag{32}
\]

The exact admissible error for \(D_K\le1.15\) is

\[
 \boxed{\delta\le
 \delta_K:=\frac{0.15K-(D_1-1)}{K-1}.}                            \tag{33}
\]

In particular,

\[
 \begin{array}{c|c|c}
 K&\delta_K&\text{support diameter with gaps }33/25\\ \hline
 3&0.0612503518397059&5.64\\
 4&0.0908335678931372&7.96\\
 5&0.105625175919853&10.28\\
 6&0.114500140735882&12.60\\
 8&0.124642957668487&17.24\\
 10&0.130277855964379&21.88
 \end{array}                                                       \tag{34}
\]

and \(\delta_K\nearrow0.15\).  Thus strong (AS) is sufficient but not
necessary.  The three-lobe construction asks for a one-sided
fixed-mode dispersion constant \(\le1.06125035184\); increasing the
number of lobes relaxes the arithmetic constant monotonically, with
the limiting threshold \(1.15\).  Smooth B-spline/Gevrey height and
lobe tapers preserve (3), (17), and these constants up to an
arbitrarily small fixed loss.

## 8. Cycle-2 handoff

* **Support attacked:** connected \(\sigma=1.42960385087046\), hence
  \(H=X^{0.300505521588293\ldots}\), and the sparse supports from
  cycle 1.
* **Construction completed:** exact Fourier-to-reciprocal-cell-to-
  short-interval reduction (6)--(18).
* **BDH/BV result:** enlarged moduli \(q\asymp H\) are the correct
  conductor, but standard BDH/BV sums all additive modes and loses
  exactly \(H\), as quantified in (21)--(24).
* **Single blocker:** the reciprocal Type-II dispersion estimate
  (BI\(_\theta\)) in (27)--(29), equivalently fixed-mode short-interval
  BDH (FM-BDH).
* **Next construction:** carry additive reciprocity through (27),
  dyadically separate \(r=m_1n_1-m_2n_2\), and prove the selected-mode
  reciprocal large-sieve bound by Kuznetsov.  The required saving is
  exactly \(H=X^{0.3005055\ldots}\); no shift-exception bookkeeping is
  involved.

## 9. Averaging the sparse-lobe gap parameter

There is a useful but limited second averaging parameter.  Let a base
lobe \(p_L\) have width \(L\), and place the outer lobes at distance
\(aL\).  Schematically,

\[
 \Phi_a(x)=\widehat p_L(x)\bigl(1+2\cos(aLx)\bigr),               \tag{35}
\]

so the hard cross pieces of \(\Phi_a^2\) contain
\(e^{\pm iaLx}\) and \(e^{\pm2iaLx}\).  Averaging over an interval of
normalized gaps of length \(R\) inserts

\[
 \frac1R\int_A^{A+R}e^{iaLx}da
 =e^{i(A+R/2)Lx}\frac{2\sin(RLx/2)}{RLx}.                        \tag{36}
\]

However, the base transform is concentrated on \(|x|\asymp L^{-1}\).
After the change of variable \(y=Lx\), the right side of (36) is
\(\operatorname{sinc}(Ry/2)\), with **no parameter tending to infinity
with \(T\)** when \(R\) is fixed.  Thus averaging over a fixed gap
interval supplies only an \(O_R(1)\) change of the hard kernel, not the
factor \(H=X^\theta\) needed in (AS).

Equivalently, Fourier inversion turns the modulation in (35) into a
translation of the cross-autocorrelation lobe.  Averaging \(a\) spreads
that positive mass over an \(\alpha\)-interval; it does not delete its
expected kernel-one main term.  It averages only the deviation of the
prime form factor from that main term.

For a growing interval one obtains the elementary bound

\[
 \int |\widehat p(y)|^2
       \min\left(1,\frac1{R|y|}\right)dy
       \ll_p \frac{\log(2R)}R,                                  \tag{37}
\]

but recovering a full factor \(H\) this way requires \(R\) of power
size comparable with \(H\).  Then the normalized support diameter, and
hence the prime length exponent, grows with \(T\); the fixed-support
trace asymptotics no longer apply.  Taking a very large but fixed
\(R\) in a two-limit argument only converts the problem into a long
\(\alpha\)-average with a fixed constant.  To certify \(85\%\), that
constant must still be below \(1.15\) (or below
\(1.06125035184\) for three lobes), so fixed gap averaging alone does
not close the arithmetic estimate.

It can nevertheless be combined with (BI\(_\theta\)): an average over
\(R\) separated gaps gives \(R\) selected reciprocal/additive modes and
can save a factor up to \(R\) in the fixed-mode dispersion problem.
This is worthwhile for constants, but a bounded or slowly growing
number of modes cannot replace the power-size saving \(H\).
