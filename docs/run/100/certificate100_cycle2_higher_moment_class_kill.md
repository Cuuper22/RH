> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Certificate 100, cycle 2: sixth trace and the off-block sharing obstruction

## Terminal outcome

Keep the accepted strict pair trace

\[
 D<1.06772567
\]

and the current capped-quartic certificate

\[
 {s\over N}>2-D+\varepsilon_4,
 \qquad \varepsilon_4>0.03021584923,
 \qquad {s\over N}>0.96249017923.                 \tag{1}
\]

This cycle attacks information outside the optimized quartic profile.  It
has two closed conclusions.

1.  A strict-support sixth-moment block can be evaluated completely, but its
    best explicit trimmed certificate is only

    \[
      \varepsilon_6>0.0182117,
      \qquad {s\over N}>0.9504860,                 \tag{2}
    \]

    so separate nesting gives no increment over (1).

2.  The proposed remedy of sharing one trim charge between orthogonal blocks
    through a linear off-block Frobenius penalty is impossible with any
    finite universal coefficient.  The sharp universally valid replacement
    is a square-root distance inequality.  For the natural decomposition of
    the old bandwidth-\(0.4999\) block into bandwidths \(0.3333\) and
    \(0.1666\), that replacement can certify at most

    \[
       0.01627033<\varepsilon_4,                   \tag{3}
    \]

    even if the complete spectra of both diagonal blocks are supplied.

Thus cycle 2 gives no strict increase over (1), but it kills the precise
standalone-sixth plus Frobenius-sharing method class and executes its first
nonlinear mixed substitute.  No unevaluated lemma remains in this class.

## 1. The strict sixth-moment block

Take

\[
 \sigma=1.9999,
 \qquad \mu_6=0.3333,
 \qquad 6\mu_6=1.9998<2.                         \tag{4}
\]

Let \(W(t)=V_{1.9999}(\mu_6t)\) be the accepted Euler allocation cap.  The
best profile in the outer-cap obstacle family is

\[
 r_6(t)=W(t)1_{\{|t|\geq g/2\}},
 \qquad
 2\int_{g/2}^{1/2}W(t)\,dt=1,
\]

with

\[
 g=0.196065856819074\ldots .                      \tag{5}
\]

It is mean one and lies pointwise under the full cap.  Backing off the cap
and tapering the two jumps gives strict smooth approximants with the same
limiting moments.  For \(Y_6=C_6-I\), the complete Fourier-cycle contraction
through degree six gives

\[
\begin{aligned}
0.2845070&<M_2<0.2845083,\\
-0.1548223&<M_3<-0.1548209,\\
0.2178371&<M_4<0.2178387,\\
-0.1840300&<M_5<-0.1840283,\\
0.2030848&<M_6<0.2030865.
\end{aligned}                                      \tag{6}
\]

The degree-six contraction includes all fifteen Wick pairings.  In
particular its flat-symbol normalization is

\[
 M_6/\mu_6^6=32/105.                              \tag{7}
\]

For a fixed exact dual, choose the rational contacts

\[
 a_1=-1,
 \quad a_2=-{49\over200},
 \quad c={393\over1000},
 \quad t={653\over1000}.                          \tag{8}
\]

The degree-six polynomial \(P\) and cap \(L\) are uniquely determined by

\[
 P(a_i)=P'(a_i)=0,
 \quad P(c)=c^2,
 \quad P'(c)=2c,
 \quad P(t)=L,
 \quad P'(t)=0.                                   \tag{9}
\]

Their decimal display is

\[
\begin{aligned}
P(y)={}&-0.00130219043365+0.04703896712652y
 +0.49937793460217y^2\\
&+1.29378771169798y^3+0.13557374098957y^4
 -1.85571189294064y^5-1.14853469927422y^6,\\
L={}&0.31787373079516.
\end{aligned}                                      \tag{10}
\]

Exact rational division at the contacts proves globally that

\[
 P(y)\leq0\ (y\leq0),
 \qquad P(y)\leq y^2\ (y\geq0),
 \qquad P(y)\leq L\ (y\geq0).                    \tag{11}
\]

Substitution of the directed sides of (6) gives

\[
 A_6:=\sum_{j=0}^6p_jM_j>0.07825174.              \tag{12}
\]

The inherited one-block stability fixed point is therefore

\[
 \varepsilon_6\geq
 {\mu_6A_6-\frac L2(D-1)\over1-L/2}>0.0182117,    \tag{13}
\]

which proves (2).  If \(C_6\) is merely nested with the old quartic block,
interlacing supplies

\[
 E_b(G)\geq E_b(C_4),
 \qquad E_b(G)\geq E_b(C_6),                      \tag{14}
\]

and hence only the maximum of the two residuals.  Since
\(\varepsilon_6<\varepsilon_4\), every construction using only these two
separate moment LPs returns (1).

## 2. Why a linear off-block charge cannot share the trim

For a Hermitian matrix \(Y\), order its eigenvalues decreasingly and put

\[
 E_b(Y)=\sum_{j>b}(\lambda_j(Y))_+^2.              \tag{15}
\]

The hoped-for linear sharing rule would have the form

\[
 E_b(B)\leq E_b(Y)+\theta\|Y-B\|_F^2              \tag{16}
\]

for a block pinching \(B=\mathcal P(Y)\), with a finite universal
\(\theta\).  No such \(\theta\) exists.

Indeed, fix \(x>0\), let \(b=1\), and for \(\delta>0\) set

\[
 B_\delta=
 \begin{pmatrix}x&0\\0&x+\delta\end{pmatrix},
 \qquad
 H_\delta=
 \begin{pmatrix}0&\delta^2\\\delta^2&0\end{pmatrix},
 \qquad Y_\delta=B_\delta+H_\delta.              \tag{17}
\]

Then \(B_\delta\) is the two-block pinching of \(Y_\delta\),

\[
 E_1(B_\delta)=x^2,
 \qquad \|H_\delta\|_F^2=2\delta^4,              \tag{18}
\]

whereas the lower eigenvalue of \(Y_\delta\) is

\[
 \lambda_-=x+{\delta\over2}
 -\sqrt{{\delta^2\over4}+\delta^4}
 =x-\delta^3+O(\delta^5).
\]

Consequently

\[
 {E_1(B_\delta)-E_1(Y_\delta)\over
        \|H_\delta\|_F^2}
 ={x\over\delta}+O(\delta)\longrightarrow\infty. \tag{19}
\]

This rules out not only (16), but every block-polynomial argument whose only
bridge back to the unpinched matrix is a fixed multiple of off-block
Frobenius energy.

## 3. The sharp nonlinear replacement

Let

\[
 \mathcal K_b=\{X=X^*:n_+(X)\leq b\}.
\]

Clipping every positive eigenvalue after the largest \(b\) shows exactly

\[
 \operatorname{dist}_F(Y,\mathcal K_b)^2=E_b(Y).  \tag{20}
\]

Distance to any closed set is one-Lipschitz.  Thus, for
\(B=\mathcal P(Y)\) and \(H=Y-B\),

\[
 \boxed{
 E_b(Y)\geq
 \left(\sqrt{E_b(B)}-\|H\|_F\right)_+^2.}         \tag{21}
\]

This square-root loss cannot be replaced by (16), by (17)--(19).

Now apply (21) to the actual capped-quartic block of cycle 1.  Write its
absolute bandwidth as

\[
 \mu=0.4999=\mu_6+\mu_r,
 \qquad \mu_6=0.3333,
 \qquad \mu_r=0.1666.                             \tag{22}
\]

For the fixed capped-outer symbol \(r_g\) of cycle 1, its second centered
moment at bandwidth \(u\) has the exact contraction form

\[
 m_2(u)=A_2+Ju^2,
 \qquad
 A_2=0.15145379266\ldots,
 \quad J=0.36277543054\ldots .                    \tag{23}
\]

Pinch the coefficient space into the two bands in (22), and denote the
block diagonal part by \(B\).  Orthogonality gives the exact energy identity

\[
 {\|B\|_F^2\over N}
 =A_2\mu+J(\mu_6^3+\mu_r^3)
 =0.09082134884\ldots=:V_B,                       \tag{24}
\]

\[
 {\|H\|_F^2\over N}
 =J(\mu^3-\mu_6^3-\mu_r^3)
 =3J\mu\mu_6\mu_r
 =0.03021012821\ldots=:O.                        \tag{25}
\]

Even omniscient block spectral information cannot have
\(E_b(B)>\|B\|_F^2\).  Hence the strongest conclusion obtainable from
(21), after normalization by \(N\), is bounded above by

\[
 \left(\sqrt{V_B}-\sqrt O\right)^2
 =0.01627032790\ldots<0.03021584923.              \tag{26}
\]

This proves (3).  In particular, adding sixth or eighth moments of the two
diagonal blocks cannot repair the loss: (26) already grants the method the
entire block spectra.

For comparison, the balanced split
\(0.4999=0.24995+0.24995\) is still worse:

\[
 V_B=0.08704168318\ldots,
 \qquad O=0.03398979458\ldots,
 \qquad
 (\sqrt{V_B}-\sqrt O)^2=0.01224675584\ldots .     \tag{27}
\]

As a fully executed polynomial instance on that balanced pinching, take the
rational quartic contacts

\[
 a=-{643\over1000},
 \qquad c={233\over1000},
 \qquad t={357\over500}.                          \tag{28}
\]

The associated globally feasible trimmed dual has

\[
\begin{aligned}
P(y)={}&-0.02860818+0.22336111y+0.62753789y^2\\
       &-0.09925410y^3-0.66463065y^4,\\
L={}&0.24192786.
\end{aligned}                                      \tag{29}
\]

The two pinched blocks have the common moment triple

\[
 (M_2,M_3,M_4)
 =(0.17411819\ldots,-0.05398369\ldots,
   0.06071810\ldots).                              \tag{30}
\]

At the current free-direction budget

\[
 {b\over N}={D-1-\varepsilon_4\over2}
 <0.018754911,
\]

(29)--(30) give a shared-trim block residual of only

\[
 {R_B\over N}>0.0182778.                           \tag{31}
\]

Since the off-block energy in (27) is already larger than this certified
residual, (21) returns zero for this explicit mixed certificate.  Equations
(24)--(27) show that this is not a defect of the quartic dual: the natural
sixth/complement split is incapable of recovering (1) through the sharp
universal distance bridge even with all higher block moments.

## Closed handoff

The following avenues are now exhausted as unconditional zero-side
certificates under total arithmetic support below two:

* a standalone degree-six nested block;
* convex combinations or maxima of separate quartic and sixth block LPs;
* a shared trim justified by any finite linear off-block-energy penalty;
* the sharp universal square-root pinching bridge for the natural
  \(0.3333+0.1666\) split, even with complete diagonal-block spectra.

Any later gain must use information that sees the off-diagonal block itself
with sign---for example a directly evaluable mixed trace containing
\(E_1YE_2YE_1\) together with the selector---rather than charging only its
unsigned Frobenius norm.  That is outside the method class closed above.