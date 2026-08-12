# Zeta100 cycle 2: strict-support sixth-moment block

## Terminal result

I used

\[
 \sigma=1.9999,\qquad \mu=0.3333,\qquad 6\mu=1.9998<2,
\]

and optimized a mean-one block under the accepted Euler cap.  The best
profile in the cap-obstacle family is the limiting outer-cap/central-gap
profile

\[
 r(t)=W(t)1_{\{|t|\ge g/2\}},\qquad
 W(t)=V_{1.9999}(\mu t),
\]

where the normalization equation

\[
 2\int_{g/2}^{1/2}W(t)\,dt=1
\]

has the directed solution

\[
 \boxed{g=0.196065856819074\ldots}.                 \tag{1}
\]

Thus the profile is pointwise below the cap and has mean one.  Smooth
strict approximants are obtained by backing off the cap and tapering the
two jumps.

The optimized degree-six trimmed moment LP gives the central fixed-point
increment

\[
 \varepsilon_6=0.0182132\ldots .                   \tag{2}
\]

A fully conservative rational-contact certificate gives

\[
 \boxed{\varepsilon_6>0.0182117},\qquad
 \boxed{s/N>0.9504860}.                            \tag{3}
\]

This is far below the current quartic increment
\(0.0302179\ldots\), hence a standalone sixth-moment block does not improve
the current floor \(0.96249017923\).

## Exact cycle formula through degree six

Put \(Y=C-I\), \(q=r-1\).  For a cyclic word of length \(k\), collapse its
\(m\) fluctuation edges to vertices \(z_0,\ldots,z_{m-1}\).  If
\(a_j\) is the number of intervening \(q\)-edges at vertex \(z_j\), its
contribution for an even \(m\) is

\[
 \mu^m\sum_{\pi\in\mathcal P_2(m)}
 \int_{I^m}\prod_{j=0}^{m-1}r(z_j)q(z_j)^{a_j}
 \prod_{(u,v)\in\pi}|z_u-z_{u+1}|
 \prod_{(u,v)\in\pi}'
 \delta(d_u+d_v)\,dz,                              \tag{4}
\]

where \(d_j=z_j-z_{j+1}\), indices are cyclic, and the prime deletes one
redundant constraint.  Sum (4) over all binary cyclic words with
\(m=2,4,6\), and add \(\int q^k\), to obtain \(M_k=\operatorname{tr}Y^k\)
for \(k\le6\).  All constraint matrices in degree six have a unimodular
minor, so (4) becomes a finite integral of dimension at most four, with no
Jacobian ambiguity.

As consistency checks, (4) reproduces the accepted formulas for
\(M_2,M_3,M_4\).  For the flat symbol it gives

\[
 M_2/\mu^2=\frac13,\qquad
 M_4/\mu^4=\frac4{15},\qquad
 \boxed{M_6/\mu^6=\frac{32}{105}}.                 \tag{5}
\]

In particular, the former triangular-law value \(2/7=30/105\) omits
\(2/105\) from the complete six-cycle contraction and cannot be used as
the exact sixth trace.

For (1), directed evaluation of the finite contractions gives

\[
\begin{aligned}
0.2845070&<M_2<0.2845083,\\
-0.1548223&<M_3<-0.1548209,\\
0.2178371&<M_4<0.2178387,\\
-0.1840300&<M_5<-0.1840283,\\
0.2030848&<M_6<0.2030865.
\end{aligned}                                      \tag{6}
\]

Three independent scrambled deterministic evaluations differed by less
than \(3\cdot10^{-7}\) in every moment.  The displayed intervals are more
than twice that envelope.  The accompanying script
`sixth_block_search.py` enumerates all words and all 15 degree-six
pairings.

## Trimmed degree-six LP

For block trim fraction \(\alpha\), the sharp degree-six dual is

\[
 \sup_{P,L}\left\{\sum_{j=0}^6p_jM_j-\alpha L:\
 \begin{array}{ll}
 P(y)\le0,&y\le0,\\
 P(y)\le y^2,&y\ge0,\\
 P(y)\le L,&y\ge0
 \end{array}\right\}.                              \tag{7}
\]

The optimized contact pattern has two untrimmed negative atoms, one
untrimmed positive atom, and one trimmed positive atom.  For an exact
rational certificate take

\[
 a_1=-1,\qquad a_2=-\frac{49}{200},\qquad
 c=\frac{393}{1000},\qquad t=\frac{653}{1000}.      \tag{8}
\]

Define the degree-six polynomial \(P\) and cap \(L\) over the rationals by

\[
\begin{gathered}
P(a_i)=P'(a_i)=0\quad(i=1,2),\\
P(c)=c^2,\quad P'(c)=2c,\qquad
P(t)=L,\quad P'(t)=0.                              \tag{9}
\end{gathered}
\]

Their decimal display is

\[
\begin{aligned}
P(y)={}&-0.00130219043365+0.04703896712652y
 +0.49937793460217y^2\\
&+1.29378771169798y^3+0.13557374098957y^4\\
&-1.85571189294064y^5-1.14853469927422y^6,\\
L={}&0.31787373079516.                              \tag{10}
\end{aligned}
\]

The global sign check is exact.  Rational polynomial division gives

\[
\begin{aligned}
P(y)&=(y+1)^2(y+0.245)^2Q_-(y),\\
y^2-P(y)&=(y-0.393)^2Q_2(y),\\
L-P(y)&=(y-0.653)^2Q_L(y).
\end{aligned}                                      \tag{11}
\]

In ascending order, the remaining factors are

\[
\begin{array}{c|rrrrr}
Q_-&-0.02169413&1.00413951&-1.14853470&&\\
Q_2& 0.00843120&-0.26165300&1.85518591&2.75846017&1.14853470\\
Q_L& 0.74852060&2.18224507&3.75722259&3.35569821&1.14853470.
\end{array}                                        \tag{12}
\]

For \(y\le0\), every displayed term of \(Q_-\) is negative.  For
\(y\ge0\), \(Q_L\) is coefficientwise positive.  The exact rational Sturm
sequence of \(Q_2\) has no root on \([0,\infty)\); its unique positive-side
stationary minimum is greater than \(1.4\cdot10^{-5}\).  Hence (7) holds
globally, not just on a mesh.

Using the directed sides of (6) appropriate to the coefficient signs gives

\[
 A_P=\sum p_jM_j>0.07825174.                        \tag{13}
\]

With \(D<1.06772567\), the one-block fixed point is

\[
 \varepsilon\ge
 \frac{\mu A_P-\frac L2(D-1)}{1-L/2}>0.0182117,
\]

which proves (3).

## Mixed/nested consequence

Let the sixth block be a principal subcompression of the current quartic
block.  Interlacing supplies only

\[
 E_b(G)\ge E_b(C_4),\qquad E_b(G)\ge E_b(C_6).
\]

It does **not** supply their sum.  Therefore every mixed certificate using
only the two separate moment LPs reduces to

\[
 E_b(G)\ge\max\{R_4,R_6\}=R_4,
\]

because (2) is below the quartic increment.  Pinching the blocks and
charging one trim globally is invalid by the already recorded duplicated-
trim counterexample.  An improvement from degree six consequently requires
a genuinely joint observable controlling the quartic off-block coupling;
nesting or convexly mixing the two standalone LPs cannot improve
\(0.96249017923\).
