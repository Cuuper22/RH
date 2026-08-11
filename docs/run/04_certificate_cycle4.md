# Certificate architect, cycle 4: one-sided sieve majorants

## Outcome

A fixed-sign Selberg/Brun treatment of the prime-pair terms beyond support one
cannot give a finite normalized second-moment constant, let alone
\(C\le 23/20\).  The obstruction is forced by positivity at zero frequency:
every nonzero height envelope and every Frobenius/time-window kernel have a
positive lobe for

\[
  1\le h\le c\frac{Y}{T}
\tag{1}
\]

on every prime scale \(Y>T\) used by the window.  The sharp Selberg upper
sieve has constant two.  After the deterministic density term has canceled
one copy of the prime-pair main term, the second copy contributes

\[
  \asymp YL,
  \qquad L\asymp\log T,
\tag{2}
\]

whereas the entire admissible trace remainder has size \(TL^3\).  Their ratio
is

\[
  \frac{Y/T}{L^2}=\frac{H_Y}{L^2}\longrightarrow\infty
  \qquad (H_Y:=Y/T)
\tag{3}
\]

for every fixed scale \(Y=T^\alpha\), \(\alpha>1\).

Consequently the optimization collapses back to effective support at most one.
The best rigorous constant in this cone is

\[
 C_{\rm rigorous}
 =\frac12+\frac1{\sqrt2}\cot\!\left(\frac1{\sqrt2}\right)
 =1.3274992963\ldots,
\tag{4}
\]

and hence only

\[
 2-C_{\rm rigorous}=0.6725007037\ldots
\tag{5}
\]

simple on-line zeros.  The minimal new datum is not a lower-bound twin-prime
theorem: it is the one-sided, weighted, *constant-one aggregate* estimate (26)
below.  Equivalently, the effective sieve factor must be
\(1+o(L^2/H_Y)\), rather than the fixed factor two.

## 1. Exact smoothed off-diagonal quadratic form

Let \(q\ge0\) be a height envelope supported in \([1,2]\), and use the
Fourier convention

\[
 \widehat q(\xi)=\int_1^2q(u)e^{iu\xi}\,du.
\tag{6}
\]

Let \(\varphi\) be a time window and put

\[
 v(u)=|\varphi(u)|^2,
 \qquad
 g(y)=\int_{\mathbb R}v(u)v(u+y)\,du\ge0.
\tag{7}
\]

The difference-frequency part of the smoothed prime-prime term is, after
removing its universal positive normalization, the exact quadratic form

\[
\boxed{
 \mathscr Q_{q,g}
 =T\!\sum_{n\ne m}
 \frac{\Lambda(n)\Lambda(m)}{\sqrt{nm}}
 g\!\left(\frac{\log n+\log m}{2}\right)
 \Re\widehat q\!\left(T\log\frac nm\right).}
\tag{8}
\]

To see (8), write the two height variables as
\(t=Tu+x/2\), \(t'=Tu-x/2\).  The height integral is

\[
 T\widehat q\!\left(T\log\frac nm\right),
\]

and Fourier inversion of the squared time kernel gives

\[
 \int_{\mathbb R}\Phi(x)^2
 e^{ix(\log n+\log m)/2}\,dx
 =2\pi g\!\left(\frac{\log n+\log m}{2}\right).
\tag{9}
\]

The factor \(2\pi\), together with the fixed \(1/(2\pi)\) factors in
\(P_X\), is the universal normalization suppressed in (8).  Restoring it
does not change any sign or the ratio (3).

On a smooth dyadic scale \(n\asymp m\asymp Y\), write \(m=n+h\) and
\(H_Y=Y/T\).  Then the coefficient of the shifted correlation is

\[
 k_{Y,h}(n)
 =\frac{T}{Y}
 g(\log Y+O(1))
 \Re\widehat q\!\left(-T\log(1+h/n)\right)
 \left(1+O(h/Y)\right).
\tag{10}
\]

For a bandwidth profile with nonzero mass at
\(\alpha=\log Y/\log T\), one has

\[
 g(\log Y)=L\,G(\alpha)+o(L),
 \qquad G(\alpha)>0.
\tag{11}
\]

Thus the natural coefficient size is \(TL/Y\).

The hard interval formula from Proposition 5.6 has exactly the same local
sign.  With its notation, as \(\delta=\log(1+h/n)\to0\),

\[
 \mathcal K_T(n,h)
 =T\bigl(\alpha_n^++\alpha_n^-\bigr)
   +i\left(\frac{d\alpha_n^+}{d\log n}
           -\frac{d\alpha_n^-}{d\log n}\right)+O(T^2\delta L)
 =2\pi T g(\log n)+O(\log L+T^2\delta L).
\tag{12}
\]

Hence smoothing the height endpoints does not create the obstruction; it only
replaces the endpoint quotient by \(\widehat q\).

## 2. Fourier-positivity obstruction to a negative tail

Put \(M_q=\int_1^2q(u)\,du>0\).  For \(|\xi|\le\pi/6\),

\[
 \Re\widehat q(\xi)
 =\int_1^2q(u)\cos(u\xi)\,du
 \ge\frac12M_q.
\tag{13}
\]

If \(n\asymp Y\) and

\[
 1\le h\le \frac{\pi}{24}\frac{Y}{T},
\tag{14}
\]

then \(|T\log(1+h/n)|\le\pi/6\) after narrowing the harmless dyadic block.
Equations (10), (11), and (13) therefore give

\[
 k_{Y,h}(n)\ge c_{q,G}\frac{TL}{Y}>0.
\tag{15}
\]

This proves the precise sign obstruction.  A coefficient kernel that is
nonpositive on all surviving off-diagonal pairs cannot arise from a nonzero
height weight and a Frobenius window.  The two positivity inputs are forced:

1. the height weight is nonnegative because the trace observable is a weighted
   squared norm;
2. \(g=v\star v\ge0\) because the time contribution is the autocorrelation of
   the nonnegative energy density \(|\varphi|^2\).

A signed combination could cancel (13), but then it is no longer a
nonnegative squared-norm observable and the accepted zero-side rank--trace
inequality does not apply.  If \(g(\alpha L)=0\) for every \(\alpha>1\), the
obstruction disappears only because the construction has effective support at
most one.

## 3. The exact Selberg-sieve majorant

For a nonnegative smooth dyadic weight \(W\), define

\[
 C_Y(h;W)=\sum_n\Lambda(n)\Lambda(n+h)W(n/Y),
 \qquad I_W=\int_0^\infty W(u)\,du.
\tag{16}
\]

The sharp dimension-two Selberg upper-bound sieve gives

\[
 C_Y(h;W)
 \le\bigl(2+o(1)\bigr)\mathfrak S(h)YI_W
\tag{17}
\]

uniformly in the present smoothed range.  Centering by the deterministic
density gives

\[
 D_Y(h;W):=C_Y(h;W)-YI_W
 \le\bigl(2\mathfrak S(h)-1+o(1)\bigr)YI_W.
\tag{18}
\]

For any nonnegative coefficient sequence \(k_h\), the exact sieve-majorant
quadratic form is therefore

\[
\boxed{
 \mathscr M_{\rm sieve}[k]
 :=YI_W\sum_h k_h\bigl(2\mathfrak S(h)-1\bigr).}
\tag{19}
\]

The constant-one Hardy--Littlewood replacement would be

\[
 \mathscr M_{\rm HL}[k]
 :=YI_W\sum_h k_h\bigl(\mathfrak S(h)-1\bigr).
\tag{20}
\]

Thus the sieve loss is not an unspecified error; it is exactly

\[
 \boxed{
 \mathscr M_{\rm sieve}[k]-\mathscr M_{\rm HL}[k]
 =YI_W\sum_h k_h\mathfrak S(h).}
\tag{21}
\]

Negative \(k_h\) cannot help this one-sided argument: bounding
\(k_hC_Y(h;W)\) from above would require a lower bound for \(C_Y(h;W)\), and
discarding it destroys the cancellation in (20).

## 4. Scale of the unavoidable sieve loss

Apply (21) on the positive lobe (14).  The singular series has mean one on
smooth intervals, so (15) gives

\[
\begin{aligned}
 \mathscr M_{\rm sieve}-\mathscr M_{\rm HL}
 &\ge (c+o(1))Y
 \sum_{h\le cH_Y}\frac{TL}{Y}\mathfrak S(h)\\
 &=(c'+o(1))TLH_Y
 =(c'+o(1))YL.
\end{aligned}
\tag{22}
\]

The full Frobenius trace has scale \(TL^3\).  Dividing (22) by that scale
gives (3).  In particular, a fixed improvement obtained from any fixed
\(\alpha>1\) is accompanied by a sieve-majorant loss tending to infinity.

More generally, replacing the Selberg factor two by \(1+\varepsilon_Y\)
leaves normalized loss

\[
 \asymp \varepsilon_Y\frac{H_Y}{L^2}.
\tag{23}
\]

Therefore a finite sharp trace bound requires

\[
 \varepsilon_Y=O(L^2/H_Y),
\]

and an asymptotically exact trace constant requires

\[
 \varepsilon_Y=o(L^2/H_Y).
\tag{24}
\]

No fixed upper-sieve constant larger than one can suffice.

## 5. Optimization and the best rigorous percentage

By Sections 2--4, every admissible fixed-sign construction with a nonzero
tail at \(\alpha>1\) has an infinite limiting sieve-majorant cost.  The only
finite branch has effective support at most one.  Optimizing its time profile
is exactly the accepted Montgomery--Taylor problem, whose value is (4).
The accepted zero-side inequality gives (5).  In particular,

\[
 C_{\rm rigorous}-\frac{23}{20}
 =0.1774992963\ldots.
\tag{25}
\]

This is stronger than merely observing that the classical sieve constant is
numerically too large: the majorant does not approach any finite constant at
all once a fixed amount of support beyond one is used.

## 6. Minimal additional one-sided statistic

Let \(k_{Y,h}\) be the explicit nonnegative coefficient family extracted from
the chosen height and time profiles.  The weakest new input that removes the
obstruction is the single aggregate upper estimate

\[
\boxed{
 \sum_Y\sum_h k_{Y,h}
 \left[
 C_Y(h;W_{Y,h})
 -\mathfrak S(h)YI_{W_{Y,h}}
 \right]
 \le o(TL^3).}
\tag{26}
\]

This is one-sided, already summed over shifts and dyadic ranges, and asks for
no lower bound for any individual twin-prime correlation.  On a single scale
it is equivalent to an effective upper-sieve factor
\(1+o(L^2/H_Y)\), as in (24).  Fourier inversion identifies (26) with the
natural-scale centered local-von-Mangoldt energy estimate isolated in cycle 3.
It is strictly weaker than pointwise Hardy--Littlewood, but strictly stronger
than every fixed-factor Selberg/Brun majorant.
