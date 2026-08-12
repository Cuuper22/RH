# Hybrid cycle 8: completion of the sawtooth and indentation terms

## Outcome

The favorable diagonal isolated at the end of cycle 7 is

\[
                  \mathcal D_0=-4J(a),N
                  =0.3068446910\ldots N,
\tag{1}
\]

for (a=0.96857558).  The (85\%) weighted-current target is only

\[
                  M_s\ge0.10557169427732\ldots N.
\tag{2}
\]

However, completing the phase calculation shows that (1) is not a lower
main term.  On every component on which the phase has no imaginary-axis
crossing, the continuous sawtooth correction is **exactly**

\[
                  \mathcal C_{\rm cont}=-\mathcal D_0
                  =-0.3068446910\ldots N.
\tag{3}
\]

The remaining discontinuous sawtooth term is precisely the weighted
simple-zero jump measure (M_s) that one is trying to bound.  Indentations
at zeros of the perturbed curve contribute no simple-zero mass under the
intersection-current convention; in an ordinary contour convention they
appear as the equal and opposite boundary charge.

Thus the completed decomposition gives the rigorous lower bound

\[
                         \boxed{M_s\ge0,}
\tag{4}
\]

and no positive increment over

\[
                         \boxed{0.79721415286134\ldots .}
\tag{5}
\]

This kills the class “isolate the logarithmic-derivative diagonal and
bound the sawtooth/indentation terms separately.”  The failure is an exact
cancellation, not an insufficient numerical estimate.

## 1. The diagonal coefficient sum

Keep the notation of cycle 7.  Normalize the proven support-(5/4)
profile (u) to have mass one and let

\[
 \widetilde g(\alpha)=\int u(x)u(x+\alpha)\,dx.
\tag{6}
\]

For the completed perturbation

\[
 V_a(s)=\zeta(s)+{\zeta'(s)\over aL},
\tag{7}
\]

the right-line logarithmic derivative has coefficients

\[
 {V_a'\over V_a}(s)=\sum_{n\ge2}{c_a(n)\over n^s},
 \qquad
 c_a(n)=-\Lambda(n)+
 \sum_{k\ge0}{(\Lambda\log*\Lambda^{*k})(n)\over(aL)^{k+1}}.
\tag{8}
\]

The outer (\Lambda(n)) in the Gram marginal restricts the diagonal to
prime powers.  At a prime,

\[
 c_a(p)=-\log p+{(\log p)^2\over aL},
\tag{9}
\]

and all (k\ge1) convolution terms in (8) vanish.  Prime powers of
exponent at least two are lower order.  Hence

\[
 {1\over L^3}\sum_{n\le T^{5/4}}
 {\Lambda(n)g_5(\log n)c_a(n)\over n}
 \longrightarrow
 J(a)=\int_0^{5/4}\widetilde g(\alpha)
 \left(-\alpha+{\alpha^2\over a}\right)d\alpha.
\tag{10}
\]

Equivalently, for independent (X,Y) with density (u),

\[
 J(a)=-{1\over2}\mathbb E|X-Y|+{\operatorname{Var}(X)\over a}.
\tag{11}
\]

Direct integration of the explicit profile gives

\[
 \mathbb E|X-Y|=0.39343545488223\ldots,
 \qquad
 \operatorname{Var}(X)=0.11623541830329\ldots,
\tag{12}
\]

and therefore

\[
 J(0.96857558)=-0.0767111727608\ldots .
\tag{13}
\]

The (1/2) cosine diagonal and the (-4) in the marginal give (1).

## 2. Exact sawtooth cancellation

Let (E_a(t)=H(1/2+it)V_a(1/2+it)), let
(\Theta_a=\arg E_a) on one component on which (E_a\ne0), and put

\[
 n_a(t)=\left\lfloor{\Theta_a(t)+\pi/2\over\pi}\right\rfloor,
 \qquad
 \mathfrak s(\Theta_a)=n_a-{\Theta_a\over\pi}.
\tag{14}
\]

For a (C^1) weight (m), Stieltjes integration gives the exact identity

\[
\begin{aligned}
 \int m\,dn_a
 ={}&{1\over\pi}\int m(t)\Theta_a'(t)\,dt\\
 &+\big[m(t)\mathfrak s(\Theta_a(t))\big]_{\partial}
 -\int m'(t)\mathfrak s(\Theta_a(t))\,dt.
\end{aligned}
\tag{15}
\]

On a subinterval containing no crossing, (n_a) is constant.  Thus

\[
 \mathfrak s(\Theta_a)=n_a-{\Theta_a\over\pi},
 \qquad
 d\mathfrak s=-{1\over\pi}d\Theta_a,
\tag{16}
\]

and the last two terms of (15) combine to

\[
 \int m\,d\mathfrak s
 =-{1\over\pi}\int m\,d\Theta_a.
\tag{17}
\]

This cancels the first term of (15) identically.  In particular, after
the prime diagonal in the first term is evaluated as (1), the continuous
sawtooth diagonal is necessarily (3).  It is not legitimate to retain
(1) and estimate (3) as an unrelated error.

At a transverse simple crossing, (n_a) jumps by (+1), by the
orientation calculation in cycle 7.  Therefore the only uncancelled
part of (15) is

\[
 \sum_{\gamma\ {m simple}}m(\gamma).
\tag{18}
\]

Taking (m=m_T) is exactly (M_s).  Thus the fully recombined identity
is

\[
 (+0.3068446910N)+(-0.3068446910N)+M_s=M_s.
\tag{19}
\]

This completes, rather than bounds heuristically, the full sawtooth.

## 3. Indentations at multiple zeros

If (\Xi) has a zero of multiplicity (r\ge2), then (8) of cycle 7
shows that (E_a) has a zero of order (r-1).  The positive
intersection current was defined by deleting precisely the points where
(E_a=0), so such a point contributes zero to (18).

In the phase picture, delete a symmetric interval around the point.  The
two endpoint terms in (15), together with the argument change on the
small indentation, equal the local winding of the order-(r-1) zero.
Subtracting that winding to implement (E_a\ne0) leaves zero.  Therefore

\[
                    \mathcal C_{\rm indent}=0
\tag{20}
\]

in the intersection-current normalization.  If instead one uses a
straight argument-principle contour, the same term is the familiar
multiplicity/resultant charge; it cannot be discarded, but it cancels the
spurious staircase jump and leads again to (20).

The two outer endpoints contribute (o(N)) after the accepted trimmed
window and smooth cutoff.

## 4. Why absolute correction bounds cannot repair the route

For reference, even before recognizing the exact cancellation, the best
direct (L^2)-to-(L^1) estimate is far outside the numerical budget.
The prime part of (m_T') has

\[
 {1\over TL^2}\int_T^{2T}|m_T'(t)|^2dt
 \longrightarrow
 8\int_0^{5/4}\alpha^3\widetilde g(\alpha)^2d\alpha.
\tag{21}
\]

For the explicit optimizer,

\[
 \int_0^{5/4}\alpha^3\widetilde g(\alpha)^2d\alpha
 =0.02230002651\ldots,
\tag{22}
\]

so the normalized rms constant is

\[
 \sqrt{8(0.02230002651\ldots)}=0.4223744927\ldots .
\tag{23}
\]

Since (|\mathfrak s|\le1/2), Cauchy gives only

\[
 {1\over N}\left|\int m_T'\mathfrak s(\Theta_a)\right|
 \le\pi(0.4223744927\ldots)+o(1)
 =1.3269286033\ldots+o(1),
\tag{24}
\]

whereas (1) may lose at most

\[
 0.3068446910-0.1055716943
 =0.2012729967\ldots
\tag{25}
\]

to close (85\%).  The first Fourier harmonic alone has the absolute
bound (0.8447489854\ldots N).  No finite Fourier truncation fixes this:
at every sawtooth jump its partial sum is zero while the one-sided
remainder tends to (1/2).  Hence the uniform tail bound never decreases
below (1/2).

Equations (17)--(19) show that this large gap is structural: the
correction is allowed to cancel all of (1), and does so on every
no-crossing component.

## 5. Defined-class kill and immediate outside attack

Define the **separated phase-error class** to consist of arguments that

1. evaluate (\int m_T\Theta_a'/\pi) by a prime diagonal;
2. bound the wrapped-phase term using only
   (|\mathfrak s|\le1/2), finitely many Fourier harmonics, or norms of
   (m_T'); and
3. use only a scalar count for the indentation zeros.

This class cannot give a positive lower bound for (M_s).  The exact
cancellation (17) already supplies an extremizer on every component, and
the orthogonal-simple/identical-double model of cycle 7 realizes
(M_s=0) while satisfying all scalar inputs.

The first attack outside this killed class must evaluate the **jump
measure directly**, without unwrapping it into a smooth phase plus a
separate sawtooth.  A concrete finite construction is the two-scale Gram
current:

\[
 v_t^{(\eta)}=
 \sqrt\eta\,v_t^{(5/4)}\oplus
 \sqrt{1-\eta}\,v_t^{(\lambda)},
 \qquad 0<\lambda<5/4,
\tag{26}
\]

with the rank-one atom

\[
 B_t^{(\eta)}={v_t^{(\eta)}v_t^{(\eta)*}\over
                  \|v_t^{(\eta)}\|^2}.
\tag{27}
\]

Its pair kernel is the explicitly evaluable nonnegative function

\[
 W_\eta(x)=left|
 \eta\Phi_{5/4}(x)+(1-\eta)\Phi_\lambda(x)
 \right|^2,
\tag{28}
\]

after the standard diagonal normalization.  Choosing (\lambda) so that
the nonzero zeros of (\Phi_\lambda) do not coincide with those of
(\Phi_{5/4}) removes the orthogonal-simple extremizer responsible for
(M_s=0).  All Fourier products in (28) remain inside support (5/4), so
the already completed prime-side theorem evaluates its trace and
Frobenius cost.  The next operation is a finite optimization over
((\eta,\lambda)) of

\[
 2-D(W_\eta)+{1\over2N}
 \sum_{\gamma\ {m simple}}
 2\{\operatorname{tr}(G_\eta B_\gamma^{(\eta)})-1\}.
\tag{29}
\]

Unlike (1), (29) does not split a topological jump into two cancelling
terms.  It is the immediate construction outside the killed class.

## Terminal gate

* Certified weighted marginal: (M_s\ge0), and no more, from the completed
  sawtooth/indentation calculation.
* Certified simple-line proportion: (0.79721415286134\ldots).
* Defined class killed: separated diagonal plus absolute/Fourier
  sawtooth bounds, by the exact cancellation (17)--(19).
* Immediate outside attack: optimize the explicit two-scale rank-one
  kernel (26)--(29), whose prime-side support remains (5/4) and whose
  incommensurate zeros remove the sharp orthogonal-simple model.
