# Certificate architect, cycle 3: signed kernels, SDP, and the local-energy statistic

## Outcome

A certificate using only the accepted bandwidth-one pair data, positivity of the pair form, number-variance kernels, and signed Fourier tails cannot reach 85%.  The obstruction is quantitative, not merely methodological:

\[
C_{85}=\frac{23}{20}=1.15,
\qquad
C_{\rm BW1}^{\rm opt}=1.3274992\ldots,
\tag{1}
\]

where (C) is the normalized second-moment cost in

\[
\frac{N_0^s(T,2T)}{N(T,2T)}\ge 2-C-o(1).
\tag{2}
\]

Allowing negative Fourier mass outside the known band does not lower the optimum: the Montgomery--Taylor function is already the solution of the larger one-delta signed-tail extremal problem.  The accepted bandwidth-one configuration cap (0.68185) makes this decisive for every configuration-wise matrix/LP certificate based on that data.

The sharp next statistic is instead a **centered local von-Mangoldt energy at frequency (T/X)**.  It is an explicit finite prime-side quantity, requires no assumption on zero locations, retains the cancellation discarded by shiftwise exceptional-set arguments, and is exactly the missing part of the support-(1.43) Frobenius trace.  Its natural-scale estimate is (18) below.

## 1. Signed-Fourier extremal program

Let (F_T(\alpha)\ge0) be the positive pair spectral measure.  On (|\alpha|\le1), its limiting density is accepted bandwidth-one data.  Consider the largest useful signed-tail cone

\[
\mathcal A_1=
\left\{r:\
\begin{array}{l}
r\text{ is real, even, and integrable},\\
r(x)\ge0\quad(x\in\mathbb R),\quad r(0)=1,\\
\widehat r(\alpha)\le0\quad(|\alpha|>1)
\end{array}
\right\}.
\tag{3}
\]

The spatial condition makes the zero-pair sum dominate its coincident-ordinate contribution.  The Fourier-tail condition gives a proved sign for the unknown portion:

\[
\int_{|\alpha|>1}\widehat r(\alpha)F_T(\alpha)\,d\alpha\le0.
\tag{4}
\]

Hence every (r\in\mathcal A_1) gives an upper certificate whose bandwidth-one cost is

\[
\mathcal J(r)
=\widehat r(0)+2\int_0^1\alpha\widehat r(\alpha)\,d\alpha
\tag{5}
\]

in the paper's normalization.  The analytic/SDP extremal problem is

\[
C_{\rm signed}:=\inf_{r\in\mathcal A_1}\mathcal J(r).
\tag{6}
\]

The one-delta duality quoted in the accepted paper gives

\[
C_{\rm signed}
=\frac1{c_1^*}
=\frac12+2^{-1/2}\cot(2^{-1/2})
=1.3274992\ldots.
\tag{7}
\]

The extremizer is the Montgomery--Taylor kernel.  Its Fourier factor is positive on the known band, so it lies both in the original autocorrelation class and in the larger signed-tail class (3).  Thus signed mass outside ([-1,1]) buys exactly zero improvement.

Equation (2) and (7) give only

\[
2-C_{\rm signed}=0.6725007\ldots,
\tag{8}
\]

whereas 85% requires (C\le1.15).  The missing reduction in the second moment is

\[
C_{\rm signed}-\frac{23}{20}=0.1774992\ldots.
\tag{9}
\]

### Why number variance is already inside this program

For an interval window, the pair kernel is

\[
r_R(x)=\left(\frac{\sin \pi R x}{\pi x}\right)^2\ge0,
\qquad
\widehat r_R(\alpha)=(R-|\alpha|)_+.
\tag{10}
\]

At (R\le1), this is a member of the nonnegative compact-support subcone of (3), so it cannot beat (7).  At (R>1), its unknown Fourier tail is positive, not negative, and therefore has the wrong sign for an unconditional upper bound.  Subtracting a tail majorant returns exactly to (3).  Thus positivity/number variance does not create an independent constraint at bandwidth one.

## 2. The finite-dimensional SDP obstruction

Normalize (N=1) and write (C=C_{\rm signed}).  The bandwidth-one trace data admit the spectral law

\[
\mu_C
=\frac{C-1}{2}\,\delta_0
+(2-C)\,\delta_1
+\frac{C-1}{2}\,\delta_2.
\tag{11}
\]

It has

\[
\int1\,d\mu_C=1,
\qquad
\int x\,d\mu_C=1,
\qquad
\int x^2\,d\mu_C=C.
\tag{12}
\]

On the zero side, (11) is the paper's extremal population:

- fraction (2-C) of simple on-line points, represented by eigenvalue (1);
- fraction ((C-1)/2) of double on-line points or spectrally equivalent shallow off-line pairs, represented by eigenvalue (2);
- the remaining ((C-1)/2) coefficient-space directions at eigenvalue (0).

It satisfies the multiplicity identity

\[
(2-C)+2\frac{C-1}{2}=1
\tag{13}
\]

and every first/two-trace, integrality, inertia, number-variance, and signed-tail constraint available from the accepted bandwidth-one data.  Its simple fraction is (2-C=0.67250\ldots).  The paper's stronger configuration extremal raises the absolute ceiling only to (0.68185), still far below (0.85).

This law is also the dual witness for the matrix SDP: any proposed linear combination of bandwidth-one observables that claims 85% evaluates consistently on (11), so its dual objective cannot exceed the cap.  A signed linear combination of Frobenius norms does not evade the witness.  Negative coefficients destroy the positive-semidefinite norm needed by the zero-side rank--trace inequality; nonnegative coefficients remain in the cone already optimized by (6).

## 3. Direct prime-side statistic outside the obstruction

Let

\[
X=T^{143/100+o(1)},
\qquad
H=\frac XT=X^{43/143+o(1)},
\qquad
\beta=\frac{T}{2\pi X}\asymp\frac1H.
\tag{14}
\]

For a smooth dyadic weight (W), define the variance-normalized centered prime polynomial

\[
S_{X,W}(\theta)
:=\frac1{\sqrt{\log X}}
  \sum_n(\Lambda(n)-1)W(n/X)e(n\theta).
\tag{15}
\]

For the finite family of smooth kernels (\Omega) obtained from the exact endpoint phases in cycle 2, define

\[
\boxed{
\mathcal L_{X,H}(W,\Omega)
:=\int_{\mathbb R}
|S_{X,W}(\theta)|^2
\Omega\!\left(H(\theta-\beta)\right)\,d\theta.}
\tag{16}
\]

This is the sharp new statistic.  It is unconditionally accessible in the literal arithmetic sense: it is a finite, positive integral of a known prime sum.  It invokes neither RH nor a zero-density hypothesis.  Fourier inversion gives the exact shifted-prime form

\[
\mathcal L_{X,H}
=\frac1{H\log X}\sum_h
e(-h\beta)\widehat\Omega(h/H)
\sum_n(\Lambda(n)-1)(\Lambda(n+h)-1)
W(n/X)W((n+h)/X).
\tag{17}
\]

Unlike an almost-all-shifts assertion, (16) retains the endpoint phase and sums the correlation errors before taking absolute values.

### Direct local-energy lemma needed for 85%

For each of the finitely many (W,\Omega) generated by

\[
\lambda=\frac{143}{100},
\qquad
v(s)=1-\frac{169}{100}s^2,
\]

it is sufficient to establish the natural-scale major/minor-arc evaluation

\[
\boxed{
\mathcal L_{X,H}(W,\Omega)
\le
\left(\mathcal V(W,\Omega)+o(1)\right)\frac{X}{H},}
\tag{18}
\]

where (\mathcal V(W,\Omega)) is the explicit Ramanujan/Hardy--Littlewood main term obtained by inserting (F(\alpha)=1) on (1<\alpha\le1.43).  Summed over the dyadic partition, these constants are exactly

\[
\int v^2
+\lambda\iint\min(\lambda|s-t|,1)v(s)v(t),
\tag{19}
\]

so (18) gives

\[
\frac{\operatorname{tr}(B_T^2)}N
\le
\frac{
\int v^2+\lambda\iint\min(\lambda|s-t|,1)v(s)v(t)
}{\lambda(\int v)^2}+o(1)
=1.1499764899\ldots+o(1),
\tag{20}
\]

and the accepted zero-side inequality gives

\[
 \frac{N_0^s(T,2T)}{N(T,2T)}
 \ge 2-1.1499764899\ldots-o(1)
 =0.8500235101\ldots-o(1).
\]

### Derivation from the endpoint kernel

For (n=Xu) and (h=O(H)),

\[
T\log(1+h/n)
=\frac{h}{Hu}+O(T^{-1}),
\tag{21}
\]

uniformly on a fixed (u)-block.  Freeze (u) by a smooth partition.  The endpoint factors

\[
e^{-iT\log(1+h/n)},\qquad e^{-2iT\log(1+h/n)}
\]

then become the additive phases (e(-h\beta_u)) in (17), with (\beta_u\asymp1/H).  Fourier inversion converts the weighted (h)-sum to an interval of width (1/H) centered at (\beta_u).  The factor (1/\log(1+h/n)) is canceled by the difference of the two endpoint phases exactly as in cycle 2.  What remains in the Frobenius trace is a fixed profile multiple of (H\mathcal L_{X,H}), plus the diagonal and explicit archimedean terms.  Thus (18), not a list of pointwise shift asymptotics, is the direct missing estimate.

## 4. What existing major/minor-arc technology supplies

The interval in (16) is

\[
\theta\in[\beta-O(1/H),\beta+O(1/H)]
\asymp[T/X,2T/X].
\tag{22}
\]

Rationals (a/q) contributing there have (q\asymp H) for the leading (a=1) arcs.  Since

\[
H=X^{0.300699\ldots}<X^{1/2},
\]

an enlarged-major-arc decomposition up to (q\asymp H) lies inside the Bombieri--Vinogradov/Barban--Davenport--Halberstam modulus range.  Its structured contribution is therefore a plausible source of the explicit constant (\mathcal V(W,\Omega)).

The unresolved term is precise.  The available (8/33) minor-arc estimate gives, on an interval of width (1/H), only

\[
\mathcal L_{X,H}^{\rm minor}\ll X\log^{-A}X.
\tag{23}
\]

The target (18) is (X/H) up to fixed logarithms.  Thus (23) misses by

\[
\frac{H}{\log^{A+O(1)}X},
\tag{24}
\]

a polynomial factor for every fixed (A).  Enlarging the major arcs can move structured mass out of (23), but completion requires the power-strengthened local estimate

\[
\int_{|\theta-\beta|\ll1/H}
|S_{X,W}^{\rm minor}(\theta)|^2\,d\theta
\ll\frac{X}{H}\log^{O(1)}X.
\tag{25}
\]

Equation (25) is the single sharp analytic target.  It avoids pointwise pair correlation and the exceptional-shift obstruction, while lying genuinely outside the bandwidth-one SDP cone.

## 5. Construction priority

1. Expand (S_{X,W}) on Farey arcs with (q\le cH), keeping the (a=1, q\asymp H) arcs that sit in (22).
2. Use BDH/BV to evaluate the aggregate squared progression errors with the exact (\Omega)-weight; insert the Ramanujan expansion before taking absolute values.
3. Prove (25) for the complementary arcs.  A bound at the natural large-sieve scale (X/H), even with a fixed power of (\log X) small enough for (20), closes the full 85% certificate.

## 6. Exact nested compression: construction and quartic obstruction

There is an exact way to embed a bandwidth \(\mu<1/2\) matrix as a
principal compression of the bandwidth-one matrix.  It is therefore legitimate
to ask whether its unconditional third and fourth traces improve the large-scale
two-trace certificate.

Partition the physical interval of length \(L\) into finitely many subbands
\(I_j\) of lengths \(L_j\), with \(L_0=\mu L\), and choose a
power-complementary smooth partition

\[
   \sum_j \varphi_j(u)^2=v(u),
\tag{26}
\]

where \(v\) is the full bandwidth-one profile.  On subband \(j\), use

\[
 f_{j,k}(u)=\left(\frac{L}{L_j}\right)^{1/2}
 \varphi_j(u)e^{-i(T+2\pi k/L_j)u}.
\tag{27}
\]

Poisson summation gives the exact infinite-grid identity

\[
 \sum_{j,k}\widehat f_{j,k}(\tau)
       \overline{\widehat f_{j,k}(\tau')}
 =L\,\widehat v(\tau-\tau').
\tag{28}
\]

Indeed, the contribution of the \(j\)-th grid is
\(L\widehat{\varphi_j^2}(\tau-\tau')\), and (26) finishes the
sum.  Truncating every grid to frequencies in \([T,2T]\) leaves the same end
errors as the accepted construction, and
\(\sum_j L_jT/(2\pi)=LT/(2\pi)+o(N)\).  The \(j=0\) block is a literal
principal submatrix at every finite \(T\), not merely a matrix with the same
limiting law.  In the full bandwidth-one units, its intrinsic matrix is the
usual mean-one sine-kernel Gram matrix at bandwidth \(\mu\).

For \(4\mu<2\), the Rudnick--Sarnak trace-cycle expansion, followed by
Fourier inversion of the sinc factors, gives

\[
\begin{aligned}
m_1(\mu)&=1,\\
m_2(\mu)&=1+\frac{\mu^2}{3},\\
m_3(\mu)&=1+\mu^2,\\
m_4(\mu)&=1+2\mu^2+\frac{4\mu^4}{15}.
\end{aligned}
\tag{29}
\]

Equivalently, for the centered eigenvalue \(Y=x-1\),

\[
 \mathbb EY=\mathbb EY^3=0,
 \qquad
 \mathbb EY^2=\frac{\mu^2}{3},
 \qquad
 \mathbb EY^4=\frac{4\mu^4}{15}.
\tag{30}
\]

These four moments do **not** penalize the two-thirds extremizer.  Put

\[
 a=\frac{2\mu}{\sqrt5},
 \qquad
 \nu_\mu=\frac5{24}\delta_{1-a}
          +\frac7{12}\delta_1
          +\frac5{24}\delta_{1+a}.
\tag{31}
\]

A direct expansion shows that \(\nu_\mu\) has exactly the moments (29).
Now let

\[
 A_\star=I+J,
 \qquad
 \operatorname{spec}(J)=
 \{-1^{(N/6)},0^{(2N/3)},+1^{(N/6)}\}.
\tag{32}
\]

Thus \(\operatorname{tr}A_\star=N\),
\(\operatorname{tr}A_\star^2=4N/3\), and (32) is precisely the
\(2N/3\)-simple plus \(N/6\)-double/off-line equality configuration.
It has a \(d=\mu N\) dimensional subspace whose compression has law
\(\nu_\mu\).  For every desired eigenvalue \(1+a\), take disjoint vectors

\[
 v_+=\sqrt a\,e_++\sqrt{1-a}\,e_0,
 \qquad Je_+=e_+,\qquad Je_0=0;
\tag{33}
\]

for every \(1-a\), use

\[
 v_-=\sqrt a\,e_-+\sqrt{1-a}\,e'_0,
 \qquad Je_-=-e_-;
\tag{34}
\]

and use pure zero-eigenvectors of \(J\) for the atom at \(1\).  These vectors
are orthonormal when their coordinates are chosen disjoint, and their
compression of \(I+J\) is diagonal with law (31).  The required positive and
negative directions are each \((5\mu/24)N<N/6\), and the required
zero-directions total \(\mu N<2N/3\), so the construction is feasible for
every \(\mu<1/2\).

Consequently, the joint SDP consisting of the full bandwidth-one first two
traces, exact principal-compression nesting, interlacing/positivity, and the
small block's first four unconditional traces has a feasible witness with only
\(2/3\) simple on-line zeros.  No matrix inequality using only those data can
improve even the flat-window bound.  The nested quartic route should therefore
be stopped; the local-energy estimate (18)/(25) remains the first statistic in
this cycle that actually excludes the bandwidth-one extremizer.
