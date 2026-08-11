# Arithmetic construction, cycle 3: quadratic-divisor and Watt/Kuznetsov reach

## 0. Result

Take the PDFs and cycles 1--2 as established.  Put

\[
       X=T^\sigma,\qquad H=X/T=T^\eta,
       \qquad \eta=\sigma-1,
       \qquad \theta_X=\frac{\eta}{1+\eta}.                       \tag{1}
\]

At the connected \(85\%\) target,

\[
 \sigma=1.42960385087046,\qquad
 \eta=0.42960385087046,\qquad
 \theta_X=0.300505521588293\ldots .                              \tag{2}
\]

For the rational benchmark used in cycle 2,

\[
 X=T^{143/100},\qquad H=T^{43/100}=X^{43/143}.                    \tag{3}
\]

The quadratic-divisor theorem of Bettin--Bui--Li--Radziwill (BBLR)
does exploit the simultaneous \(h\)-average in exactly the right way,
but its Watt/Kuznetsov error has a hard exponent barrier.  For the
worst arbitrary-coefficient Type-II block the two relevant errors are

\[
                 T^{1/2+2\eta+\varepsilon}
          \quad\hbox{and}\quad
                 T^{3/4+2\eta+\varepsilon},                      \tag{4}
\]

whereas trace grade is

\[
                 X=T^{1+\eta}\operatorname{polylog}T.             \tag{5}
\]

The first term permits \(\eta<1/2\), but the Watt term permits only

\[
              \boxed{\eta<1/4},
              \qquad \boxed{\sigma<5/4},
              \qquad \boxed{\theta_X<1/5}.                       \tag{6}
\]

At \(\eta=43/100\), the Watt error is \(T^{1.61+\varepsilon}\),
while (5) is \(T^{1.43}\): the precise deficit is \(T^{0.18}\).
Thus the existing Watt/Kuznetsov theorem does not prove
\((\mathrm{BI}_\theta)\) at \(43/143\).

The 2025 amplified-fourth-moment result does not improve this total
twist exponent: it allows four copies of an amplifier of individual
length \(T^{1/8-\varepsilon}\), but after pairing them the coefficient
inserted into BBLR has total length \(T^{1/4-\varepsilon}\).

The strongest uniform support furnished by this architecture is
therefore \(\sigma<5/4\).  Optimizing the zeta window for
\(K(t)=\min(|t|,1)\) and taking \(\sigma\uparrow5/4\) gives

\[
             D_{5/4}^*=1.20278584713866\ldots,
 \qquad
             \boxed{2-D_{5/4}^*=0.79721415286134\ldots}.          \tag{7}
\]

So this route reaches a limiting **79.7214153%**, not \(85\%\).

## 1. Returning the reciprocal-cell form to the quadratic-divisor form

Cycle 2 wrote the local arc as reciprocal cells

\[
        \xi=1/q+O(H^{-2}),\qquad q\asymp H,                       \tag{8}
\]

and obtained \((\mathrm{BI}_\theta)\) with a reciprocal phase.  The
individual cell weight oscillates \(H\) times on the associated
\(H^2\)-shift scale, so it does **not** satisfy BBLR's slowly varying
weight hypotheses if fed to their theorem one cell at a time.

The correct comparison is to first sum the partition (8) back to the
original Fourier band.  Fourier inversion then returns the exact
cycle-1 aggregate

\[
 \sum_h w(h/H)
 \sum_{n\asymp X}\bigl(\Lambda(n)\Lambda(n+h)
                    -\mathfrak S(h)\bigr)V(n/X),                 \tag{9}
\]

with \(h\asymp H\) and a fixed smooth \(w\).  No absolute value over
\(h\) is introduced.  After a Heath--Brown decomposition, a block on
one side of (9) has the form

\[
 f(n)=\sum_{a m_1m_2=n}\alpha_a u_1(m_1)u_2(m_2),                \tag{10}
\]

where \(\alpha_a\) contains the short/Moebius factors and \(u_i\) is
a smooth \(1\)- or \(\log\)-weight.  Pairing two such blocks in (9)
gives

\[
 \sum_{a m_1m_2-b n_1n_2=h}
   \alpha_a\overline{\alpha_b}
   w(h/H)W_1(m_1)W_2(m_2)W_3(n_1)W_4(n_2),                      \tag{11}
\]

which is exactly the quadratic-divisor shape in BBLR Proposition 3.1.
Its four zero-frequency terms are the diagonal/Ramanujan main term in
(9); its error is the desired dispersion remainder.

This is the useful relation between \((\mathrm{BI}_\theta)\) and the
BBLR machinery: use the Fourier-cell formulation to identify the
needed signed local energy, then apply the quadratic-divisor theorem
to the equivalent smooth \(h\)-average (11).

## 2. Exact BBLR exponent substitution

Use the notation of BBLR Proposition 3.1:

\[
       a\asymp A,\quad b\asymp B,\quad
       m_1m_2\asymp M,\quad n_1n_2\asymp N,quad h\asymp H_s.
\]

Their Watt-strengthened error, in the range
\(H_s\ll(AB)^{1/2+\varepsilon}\), is

\[
 \begin{aligned}
 E\ll_\varepsilon &(ABMNH_s^2)^{1/4+\varepsilon}\\
 &\times\left((AB)^{1/2}
 +H_s^{1/4}(A+B)^{1/2}(ABMN)^{1/8}\right).                       \tag{12}
 \end{aligned}
\]

For the terminal Type-II block at scale (1), the short factors on the
two sides can both have maximal length \(H\), and the complementary
products have length \(X/H=T\).  Thus

\[
       A=B=H=T^\eta,qquad M=N=T,qquad H_s=H=T^\eta.              \tag{13}
\]

The hypothesis in (12) holds exactly at the boundary:

\[
                   H_s=(AB)^{1/2}.                               \tag{14}
\]

The outside factor in (12) is

\[
       (ABMNH_s^2)^{1/4}=T^{1/2+\eta}.                            \tag{15}
\]

The first term in parentheses is \(T^\eta\), giving

\[
                         E_1=T^{1/2+2\eta+\varepsilon}.           \tag{16}
\]

The Watt/Kuznetsov term in parentheses is

\[
 H_s^{1/4}(A+B)^{1/2}(ABMN)^{1/8}
 \asymp T^{\eta/4}T^{\eta/2}T^{(2\eta+2)/8}
 =T^{1/4+\eta},                                                   \tag{17}
\]

and hence

\[
                         E_2=T^{3/4+2\eta+\varepsilon}.           \tag{18}
\]

The unnormalized signed correlation remainder in (AS) must be
\(O(X\operatorname{polylog}X)=O(T^{1+\eta}\operatorname{polylog}T)\).
The factors \(n^{-1/2}\) in the explicit formula scale the main and
the error equally, so the comparison is directly

\[
 \begin{array}{rcl}
 1/2+2\eta&<&1+\eta \quad\Longleftrightarrow\quad \eta<1/2,\\
 3/4+2\eta&<&1+\eta \quad\Longleftrightarrow\quad \eta<1/4.
 \end{array}                                                       \tag{19}
\]

This proves (6).  At the target \(\eta=43/100\),

\[
 E_1=T^{1.36+\varepsilon}=o(T^{1.43}),\qquad
 E_2=T^{1.61+\varepsilon}\ne O(T^{1.43}),                         \tag{20}
\]

so only the Watt term fails.

### Smooth-coefficient subcase

If there are no arbitrary short factors, set \(A=B=1\) and
\(M=N=X=T^{1+\eta}\).  The unrestricted BBLR error gives

\[
             E\ll T^{3/4+(7/4)\eta+\varepsilon}.                 \tag{21}
\]

Comparison with \(X=T^{1+\eta}\) permits

\[
                \eta<1/3,\qquad \sigma<4/3.                      \tag{22}
\]

This better range is real, but it applies only to the smooth divisor
blocks.  The Moebius/Type-II coefficients in (10) force the worst
case (13), so (22) is not the uniform prime-coefficient range.

## 3. What the twisted second moment does cover

At (3), the short factor has length

\[
                         H=T^{0.43},                              \tag{23}
\]

and the cofactor has length \(X/H=T\).  If that cofactor is a single
smooth \(1\)- or \(\log\)-factor, the block is a finite linear
combination of

\[
          \zeta(1/2+it)A(1/2+it)
 \quad\hbox{and its shift derivatives},                           \tag{24}
\]

where \(A\) is an arbitrary Dirichlet polynomial of length \(T^{0.43}\).
The Bettin--Chandee--Radziwill (BCR) twisted-second-moment theorem
allows arbitrary \(A\) up to

\[
                       T^{17/33-\varepsilon}
                       =T^{0.515151\ldots-\varepsilon}.           \tag{25}
\]

Thus BCR **does close** every block of the form (24), with a positive
exponent margin at (23).  Logarithmic coefficients follow by
differentiating the shift or by partial summation.

This does not close the full Heath--Brown Type-II family.  In the
MRT decomposition, the long coefficient \(\beta\) in
\((\alpha*\beta)(n)\) may itself be a convolution of two or more
large \(1/\log\)-blocks.  The corresponding polynomial is then

\[
             \zeta^2 A,\quad \zeta^3 A,\quad\ldots,               \tag{26}
\]

not \(\zeta A\).  The arbitrary-coefficient theorem (25) cannot be
applied to (26).  BCR's special-shape theorem permits
\(\zeta A_{\rm smooth}B\) with the smooth factor of length at most
\(T^{1/2}\) and the arbitrary factor of length at most \(T^{1/4}\),
but a general short Heath--Brown coefficient of total length
\(T^{0.43}\) need not have such a factorization.  Therefore (25) is a
completed subroute, not a proof of \((\mathrm{BI}_{43/143})\).

## 4. The 2025 amplified fourth moment does not change the exponent

The 2025 theorem of Bui--Hall--Subira Jorge evaluates

\[
       \int |\zeta(1/2+it)|^4|A(1/2+it)|^4w(t/T)\,dt              \tag{27}
\]

for the specified amplifier coefficients with individual length
\(y=T^\vartheta\), \(\vartheta<1/8\).  Its proof combines two copies
of \(A\) into a coefficient supported on

\[
                         x=y^2=T^{2\vartheta}                    \tag{28}
\]

and applies the BBLR twisted fourth moment with error

\[
                     T^{1/2+\varepsilon}x^2
                  +  T^{3/4+\varepsilon}x.                       \tag{29}
\]

The two conditions for (29) to be \(o(T)\) are both

\[
                    2\vartheta<1/4.                              \tag{30}
\]

Hence the refinement accommodates four structured amplifier copies,
but the **total paired twist length remains \(T^{1/4}\)**.  It does
not reach the \(T^{0.43}\) short factor in (23), nor does it improve
the Watt exponent in (18).

## 5. Window optimization at the actual uniform support

The BBLR range \(\eta<1/4\) means

\[
                    \sigma=1+\eta<5/4.                            \tag{31}
\]

On this connected support the evaluated prime kernel is
\(K(t)=\min(|t|,1)\).  The cycle-1 Euler solution for
\(1<\sigma<2\), specialized to \(\sigma=5/4\), has

\[
 \delta=1/4,qquad q=1/8,qquad b=3/8,                             \tag{32}
\]

and, before normalization,

\[
 u(x)=
 \begin{cases}
 \cos(\sqrt2x),&|x|\le3/8,\\
 A\cos(|x|-1/2)+B\sin(\sqrt3(|x|-1/2)),&3/8\le|x|\le5/8,
 \end{cases}                                                      \tag{33}
\]

with

\[
 A=0.765651150533640\ldots,qquad
 B=-0.479300891051646\ldots .                                    \tag{34}
\]

Its mass and Euler constant are

\[
 \int u=1.09716424928793\ldots,qquad
 C=1.31965363103003\ldots,                                       \tag{35}
\]

so

\[
 D_{5/4}^*=\frac{C}{\int u}
           =1.20278584713866\ldots,                              \tag{36}
\]

and the trace certificate tends to

\[
 \boxed{2-D_{5/4}^*=0.79721415286134\ldots}.                      \tag{37}
\]

For comparison, the smooth-only range \(\sigma<4/3\) in (22) would
give

\[
 2-D_{4/3}^*=0.82435609556\ldots,                                 \tag{38}
\]

but it is not uniform over the Type-II prime decomposition.

## 6. Cycle-3 handoff

* **Exact match:** after recombining the reciprocal cells, the signed
  aggregate is BBLR's smoothly averaged equation
  \(am_1m_2-bn_1n_2=h\).
* **Target exponent:** \(H=T^{0.43}\) at \(43/143\).
* **Completed subroute:** BCR handles every genuine
  \(\zeta\cdot A\) block because \(0.43<17/33\).
* **Exact failure:** BBLR's Watt term is \(T^{1.61}\), versus the
  trace-grade \(T^{1.43}\); missing power \(T^{0.18}\).
* **2025 refinement:** preserves the total twist barrier \(1/4\).
* **Strongest uniform support from these tools:**
  \(\sigma<5/4\), yielding a limiting \(79.7214153\%\).
* **Necessary next input:** either a selected-mode reciprocal
  Kloosterman estimate improving the second term of (12), or a
  twisted moment for the residual \(\zeta^jA\) blocks with total
  arbitrary twist exponent at least \(0.43\).  Merely reorganizing the
  existing fourth-moment theorem cannot supply the missing
  \(T^{0.18}\).
