# Hybrid 100, cycle 4: charged cubic stability and exact selector deletion

## Superseding terminal theorem: density one

The charged stability identity derived in this cycle admits an exact
quadratic dual which closes the asymptotic problem:

\[
\boxed{\displaystyle
\liminf_{T\to\infty}
\frac{N_{0,\mathrm{simple}}(T,2T)}{N(T,2T)}=1.}
\tag{A1}
\]

This is density one for simple critical-line zeros.  It does not assert that
every individual nontrivial zero is simple or lies on the critical line.

Use the slightly wider strict block

\[
\mu=\frac{333333}{500000}=0.666666,\qquad
3\mu=1.999998<2,
\tag{A2}
\]

and its directed second moment

\[
M_2>\frac{18717}{50000}=0.37434.
\tag{A3}
\]

Take the exact quadratic

\[
\boxed{\displaystyle
P_2(y)=\frac{-49+280y+329y^2}{729}.}
\tag{A4}
\]

Its untrimmed signs are global:

\[
P_2(y)=\frac{(y+1)(329y-49)}{729}\leq0
\quad(-1\leq y\leq0),
\tag{A5}
\]

\[
y^2-P_2(y)=
\frac{400}{729}\left(y-\frac7{20}\right)^2\geq0
\quad(y\geq0).
\tag{A6}
\]

The charged removal cost from (4) is also exact.  On \(0\leq y\leq1\),

\[
P_2(y)\leq P_2(1)=\frac{560}{729},
\tag{A7}
\]

while for \(y\geq1\),

\[
P_2(y)-(y-1)^2
=\frac{609}{400}
-\frac{400}{729}
\left(y-\frac{869}{400}\right)^2.
\tag{A8}
\]

Therefore

\[
\boxed{\displaystyle
L_2^\sharp=
\sup_{y\geq0}\{P_2(y)-(y-1)_+^2\}
=\frac{609}{400}<2.}
\tag{A9}
\]

The block is mean one, so its centered first moment vanishes.  Equations
(A3)--(A4) give

\[
\begin{aligned}
A_2
&=-\frac{49}{729}+\frac{329}{729}M_2\\
&>\frac{3707893}{36450000}
=0.1017254595336\ldots .
\end{aligned}
\tag{A10}
\]

Combining the charged stability inequality (4) with (A5)--(A10) gives

\[
\varepsilon\geq
\mu A_2-\frac{L_2^\sharp}{2}
(D-1-\varepsilon)-o(1).
\tag{A11}
\]

Using only

\[
D-1<\frac{6771746}{100000000},
\tag{A12}
\]

the solved lower endpoint is

\[
\begin{aligned}
\varepsilon_*
&=
\frac{
\frac{333333}{500000}\frac{3707893}{36450000}
-\frac{609}{800}\frac{6771746}{100000000}}
{1-\frac{609}{800}}\\
&=\frac{263525218243}{3867750000000}\\
&=0.068133984420658\ldots .
\end{aligned}
\tag{A13}
\]

But \(s/N\leq1\), together with
\(s/N=2-D+\varepsilon\), forces

\[
\varepsilon\leq D-1<0.06771746.
\tag{A14}
\]

The strict rational gap is

\[
\varepsilon_*-0.06771746
=\frac{201376541}{483468750000}
=0.000416524420658\ldots>0.
\tag{A15}
\]

Thus every subsequential limiting proportion below one is excluded, proving
(A1).  Equivalently, the formal lower expression is

\[
2-1.06771746+\varepsilon_*
=1.000416524420658\ldots ;
\tag{A16}
\]

the excess above one is the closing contradiction, not a claimed
proportion larger than one.

The remainder of this report records the charged cubic intermediate theorem,
the exact selector deletion identity, and the affine-class obstruction from
which the density-one quadratic was found.

## Charged cubic intermediate theorem

Use the strict cubic block

\[
\sigma=1.9999,\qquad \mu=0.6666,\qquad 3\mu=1.9998<2,
\tag{1}
\]

and the exact rational cubic \(P\) described below.  The accepted directed
inputs are

\[
D<1.06771746,\qquad
A_P>0.0690906275363.
\tag{2}
\]

The old cubic proof charged each one of the \(b\) exceptional directions by
the flat cap

\[
L=0.7558836565757286\ldots .
\tag{3}
\]

This cycle proves that the zero-side stability identity retains the additional
top-eigenvalue charge

\[
\boxed{\displaystyle
T_b(C)+H_b(C)\leq \varepsilon N,\qquad
H_b(C)=\sum_{i\leq b}(\lambda_i(C)-2)_+^2.}
\tag{4}
\]

Consequently the correct cubic removal cost is

\[
\boxed{\displaystyle
L^\sharp=\sup_{y\geq0}
\{P(y)-(y-1)_+^2\}
=0.5533263786200\ldots<0.553326379.}
\tag{5}
\]

The resulting fixed point is

\[
\varepsilon>
\frac{\mu A_P-\frac{L^\sharp}{2}(D-1)}
{1-L^\sharp/2}
>0.03777062559,
\tag{6}
\]

and therefore

\[
\boxed{\displaystyle
\liminf_{T\to\infty}
\frac{N_{0,\mathrm{simple}}(T,2T)}{N(T,2T)}
>0.97005316559.}
\tag{7}
\]

This is a strict unconditional gain

\[
0.97005316559-0.96517745659
=0.00487570900
\tag{8}
\]

over the uncharged cubic theorem.

The cycle also completes the exact cubic deletion theorem.  If
\(\mathcal L\) is a hard selector of simple critical-line atoms, then

\[
\boxed{\displaystyle
\frac{s}{N}\geq0.97005316559+
\frac{J_G(\mathcal L)-\lambda J_\mu(\mathcal L)
-B_\lambda|\mathcal L|}
{(1-L^\sharp/2)N}-o(1),}
\tag{9}
\]

for every \(\lambda\geq0\), with the explicit sharp \(B_\lambda\) in
(45) below.  The entire affine pair-current family in (9) has a rigorous
density-only obstruction.  Retaining the exact signed length-two current
instead gives a fully evaluated homogeneous model value \(0.99417\ldots\);
that last number is not claimed unconditionally.

## 1. The rational cubic and the wide profile

Take

\[
c=\frac{259}{1000},\qquad t=\frac{1823}{1000},
\tag{10}
\]

and

\[
P(y)=p_0+p_1y+p_2y^2+p_3y^3,
\tag{11}
\]

where

\[
\begin{aligned}
p_0&=-\frac{66734312579529}{1276719342260000},\\
p_1&= \frac{502619626742471}{1276719342260000},\\
p_2&= \frac{189991065161}{638359671130},\\
p_3&=-\frac{9468590450}{63835967113},\\
L&=\frac{617040463458087}{816316715000000}.
\end{aligned}
\tag{12}
\]

The exact sign factors are

\[
y^2-P(y)=
\frac{9468590450}{63835967113}(y-c)^2
\left(y+\frac{994831809}{189371809}\right),
\tag{13}
\]

\[
L-P(y)=
\frac{9468590450}{63835967113}(y-t)^2
\left(y+\frac{2097753279}{1279539250}\right),
\tag{14}
\]

and

\[
P(y)=(y+1)\{p_0+(p_1-p_0)y+p_3y^2\}.
\tag{15}
\]

The two roots of the quadratic in (15) are positive.  Hence

\[
P(y)\leq0\quad(-1\leq y\leq0),\qquad
P(y)\leq y^2,\quad P(y)\leq L\quad(y\geq0).
\tag{16}
\]

For the pure outer-cap, mass-one profile

\[
r(t)=W(t)1_{\{|t|\geq g/2\}},\qquad
g=0.1761268299240\ldots,
\tag{17}
\]

the accepted degree-three contractions are

\[
M_2=0.37432342789\ldots,\qquad
M_3=-0.06711995084\ldots .
\tag{18}
\]

Writing \(C\) for the local compression and \(Y=C-I\),

\[
\frac{1}{N}\operatorname{tr}P(Y)=\mu A_P,\qquad
A_P=p_0+p_2M_2+p_3M_3.
\tag{19}
\]

All arithmetic in (18)--(19) has total Fourier bandwidth
\(3\mu=1.9998<2\).

## 2. Charged zero-side stability

Use the accepted zero-side decomposition

\[
G=P_0+Q,\qquad
P_0\succeq0,\quad
\operatorname{rank}P_0\leq s,\quad
\operatorname{tr}P_0\leq s,\quad
n_+(Q)\leq b,\quad s+2b\leq N.
\tag{20}
\]

Here \(P_0\) denotes the zero-side simple part and is unrelated to the
polynomial \(P(y)\).

Let the eigenvalues of \(G\succeq0\) be decreasing.  Since \(Q\) has at
most \(b\) positive directions, the positive inertia inequality and the
Ky Fan variational principle give

\[
\#\{i>b:\lambda_i(G)>0\}\leq s,\qquad
\sum_{i>b}\lambda_i(G)\leq\operatorname{tr}P_0\leq s.
\tag{21}
\]

For completeness, the second inequality follows by taking a rank-\(b\)
projection containing the positive spectral subspace of \(Q\) in the
variational formula for \(\sum_{i>b}\lambda_i(G)\).

Pad the positive eigenvalues after the first \(b\) with zeros to obtain
\(\rho_1,\ldots,\rho_s\).  Define

\[
\mathcal A(G)=
\|G\|_F^2-4\operatorname{tr}G+3s+4b.
\tag{22}
\]

For each of the first \(b\) eigenvalues,

\[
(\lambda-2)_+^2\leq\lambda^2-4\lambda+4.
\tag{23}
\]

For a tail eigenvalue \(\rho\geq0\), put

\[
g(\rho)=\rho^2-4\rho+3-(\rho-1)_+^2.
\tag{24}
\]

Then

\[
g(\rho)=
\begin{cases}
(1-\rho)(3-\rho)\geq2(1-\rho),&0\leq\rho\leq1,\\
-2(\rho-1)=2(1-\rho),&\rho\geq1.
\end{cases}
\tag{25}
\]

Therefore (21) implies

\[
\sum_{j=1}^{s}g(\rho_j)
\geq2\left(s-\sum_{j=1}^{s}\rho_j\right)\geq0.
\tag{26}
\]

Combining (22)--(26) proves

\[
\sum_{i\leq b}(\lambda_i(G)-2)_+^2
+\sum_{i>b}(\lambda_i(G)-1)_+^2
\leq\mathcal A(G).
\tag{27}
\]

Now normalize

\[
\operatorname{tr}G=N,\qquad
\|G\|_F^2\leq DN,\qquad
\frac{s}{N}=2-D+\varepsilon.
\tag{28}
\]

Since \(4b\leq2(N-s)\),

\[
\mathcal A(G)
\leq DN-4N+3s+2(N-s)
=\varepsilon N.
\tag{29}
\]

If \(C\) is a principal compression of \(G\), eigenvalue interlacing
transfers both increasing positive-part terms in (27) to \(C\).  Equations
(27)--(29) prove (4).

### Deletion-stable charged form

Let \(K_{\mathcal L}\) be a sum of selected simple rank-one atoms and put

\[
G_{\mathcal L}=G-K_{\mathcal L}.
\tag{30}
\]

The remaining simple part has rank and trace budget \(s-|\mathcal L|\);
the bad-direction budget \(b\) is unchanged.  The exact global selector
score is

\[
J_G(\mathcal L)
=2\operatorname{tr}(GK_{\mathcal L})
-\|K_{\mathcal L}\|_F^2
-|\mathcal L|.
\tag{31}
\]

Consequently

\[
\begin{aligned}
\mathcal A(G_{\mathcal L})
&=\|G-K_{\mathcal L}\|_F^2
-4(N-|\mathcal L|)
+3(s-|\mathcal L|)+4b\\
&=\mathcal A(G)-J_G(\mathcal L).
\end{aligned}
\tag{32}
\]

Applying (27) to \(G_{\mathcal L}\) and then compressing gives the exact
charged selector stability theorem

\[
\boxed{\displaystyle
J_G(\mathcal L)+T_b(C_{\mathcal L})+H_b(C_{\mathcal L})
\leq\varepsilon N.}
\tag{33}
\]

Thus the new charge is fully compatible with rank-one deletion; it is not
only an undeleted full-matrix estimate.

## 3. The improved cubic removal cost

For a centered eigenvalue \(y=\lambda-1\), an untrimmed positive direction
contributes \(y_+^2\), while a direction among the top \(b\) retains the
charge

\[
(\lambda-2)_+^2=(y-1)_+^2.
\tag{34}
\]

Using (16) on the untrimmed directions and subtracting only the excess of
\(P\) over (34) on the trimmed directions gives

\[
T_b(C)+H_b(C)
\geq\operatorname{tr}P(C-I)-L^\sharp b,
\tag{35}
\]

where \(L^\sharp\) is (5).

The value in (5) is elementary.  On \(0\leq y\leq1\), \(P\) is increasing.
For \(y\geq1\), differentiate

\[
P(y)-(y-1)^2.
\tag{36}
\]

Its stationary equation is

\[
3p_3y^2+2(p_2-1)y+(p_1+2)=0.
\tag{37}
\]

The roots are

\[
-4.38393122\ldots,\qquad
y^\sharp=1.2270473536\ldots .
\tag{38}
\]

The negative-leading cubic increases up to \(y^\sharp\) and decreases
afterward.  Directed substitution gives

\[
0.5533263785
<P(y^\sharp)-(y^\sharp-1)^2
<0.553326379,
\tag{39}
\]

which proves (5).

Equations (19), (29), and (35), together with

\[
\frac{b}{N}\leq\frac{D-1-\varepsilon}{2},
\tag{40}
\]

give

\[
\varepsilon\geq
\mu A_P-\frac{L^\sharp}{2}(D-1-\varepsilon).
\tag{41}
\]

Substitution of only the outward-directed bounds

\[
\mu=0.6666,\quad
A_P>0.0690906275363,\quad
D-1<0.06771746,\quad
L^\sharp<0.553326379
\tag{42}
\]

yields (6)--(7).

## 4. Exact cubic rank-one deletion

Let \(A=uu^*\) be one compressed zero atom.  Its trace and unique nonzero
eigenvalue are

\[
a=\operatorname{tr}A=\|u\|^2=\mu=0.6666,\qquad A^2=aA.
\tag{43}
\]

Write \(C=R+A\) with \(R\succeq0\), and put

\[
x=\operatorname{tr}(AR),\qquad z=\operatorname{tr}(AR^2).
\tag{44}
\]

Direct noncommutative expansion around \(R-I\), followed by trace cyclicity,
gives

\[
\boxed{\displaystyle
\operatorname{tr}\{P(R+A-I)-P(R-I)\}
=c_0+c_1x+c_2z,}
\tag{45}
\]

where

\[
\begin{aligned}
c_0&=p_1a+p_2(a^2-2a)+p_3(3a-3a^2+a^3)
   =-0.1449438288560\ldots,\\
c_1&=2p_2+3p_3(a-2)
   =1.1885849307488\ldots,\\
c_2&=3p_3
   =-0.4449806689654\ldots .
\end{aligned}
\tag{46}
\]

Cauchy--Schwarz gives

\[
z=u^*R^2u\geq\frac{(u^*Ru)^2}{u^*u}=\frac{x^2}{a}.
\tag{47}
\]

Since \(c_2<0\), the sharp affine majorant with slope \(2\lambda\) is

\[
c_0+c_1x+c_2z\leq2\lambda x+B_\lambda,
\tag{48}
\]

where

\[
\boxed{\displaystyle
B_\lambda=
c_0+\frac{a(c_1-2\lambda)_+^2}{-4c_2}.}
\tag{49}
\]

The least zero-intercept slope is

\[
\boxed{\displaystyle
\eta_*=
\frac{c_1}{2}-\sqrt{\frac{c_0c_2}{a}}
=0.2832370387412\ldots,}
\tag{50}
\]

with contact at

\[
x_*=\sqrt{\frac{ac_0}{c_2}}
=0.4659742812\ldots .
\tag{51}
\]

Delete the atoms of a hard selector one at a time.  At each step \(2x\) is
the compressed pair energy between the current atom and all atoms not yet
deleted.  Each covered pair is counted exactly once, so

\[
\operatorname{tr}P(C_{\mathcal L}-I)
\geq
\operatorname{tr}P(C-I)
-\lambda J_\mu(\mathcal L)
-B_\lambda|\mathcal L|.
\tag{52}
\]

Combining (33), (35), (40), and (52) proves the signed selector inequality
(9).  This is the charged-cubic generalization of the earlier rank-one
tail theorem; no diagonal Frobenius term remains.

## 5. Kernel-level affine obstruction

For the zero-intercept choice \(\lambda=\eta_*\), the pair contrast kernel is

\[
K_{\eta_*}(d)=|U(d)|^2-\eta_*|A_\mu(d)|^2,
\tag{53}
\]

where \(U\) is the full support-\(1.9999\) amplitude and \(A_\mu\) is the
outer-cap block amplitude.

Its first sign changes are

\[
0.4250515565\ldots,\qquad
1.1465724770\ldots,\qquad
1.4186122894\ldots .
\tag{54}
\]

At the new floor, a positive density of consecutive simple gaps is forced
only after

\[
\frac{1}{0.97005316559}=1.0308713331\ldots,
\tag{55}
\]

which lies inside the negative interval in (54).

The kernel is nevertheless positive definite.  In physical frequency,
directed phase evaluation gives

\[
\inf_{F_\mu(y)>0}\frac{F_G(y)}{F_\mu(y)}
=0.6449348954\ldots>\eta_*,
\tag{56}
\]

and at zero the spectral margin is

\[
0.5221034797\ldots
-\eta_*(0.8095444724\ldots)
=0.2928105006\ldots .
\tag{57}
\]

The obstruction is therefore the removal of the positive diagonal, not a
failure of positive definiteness.

The complete local off-diagonal energy is

\[
j_\mu:=\frac{J_\mu(\mathcal Z)}{N}
=\mu(1+M_2)-\mu^2
=0.4717684370\ldots .
\tag{58}
\]

Give an affine argument its most favorable global scalar total

\[
d:=\frac{J_G(\mathcal Z)}{N}=0.06771746.
\tag{59}
\]

Uniformly mark the allowed simple density and select a marginal density
\(\kappa\).  This is a feasible adversarial population for any method whose
only labelled data are the count and the two scalar pair totals.  The
expected numerator in (9) is

\[
\Gamma_\lambda(\kappa)
=\kappa(2-\kappa)(d-\lambda j_\mu)-\kappa B_\lambda.
\tag{60}
\]

Optimizing the full family (49) gives

\[
\lambda_*(\kappa)=
\frac12\left\{
c_1-\frac{(2-\kappa)j_\mu(-c_2)}{a}
\right\},
\tag{61}
\]

and, with \(h=2-\kappa\),

\[
\frac{\Gamma_*(\kappa)}{\kappa}
=h\left(d-\frac{c_1j_\mu}{2}\right)-c_0
+\frac{h^2j_\mu^2(-c_2)}{4a}.
\tag{62}
\]

For \(0<\kappa\leq0.97005316559\),

\[
1.02994683441\leq h<2.
\tag{63}
\]

The right side of (62) is convex in \(h\), and its endpoint values are

\[
-0.03467472695\ldots,\qquad
-0.1317872594\ldots .
\tag{64}
\]

Hence

\[
\boxed{\Gamma_*(\kappa)<0
\quad(0<\kappa\leq0.97005316559).}
\tag{65}
\]

This is a precise impossibility theorem for the complete affine
pair-current reduction, including every slope and every cardinality rebate.

## 6. First calculation outside the affine class

For a selected matrix

\[
K=\sum_{\gamma\in\mathcal L}A_\gamma,
\tag{66}
\]

the collective cubic deletion is exactly

\[
\begin{aligned}
\operatorname{tr}\{P(Y)-P(Y-K)\}
={}&p_1\operatorname{tr}K
+p_2\{2\operatorname{tr}(YK)-\operatorname{tr}K^2\}\\
&+p_3\{3\operatorname{tr}(Y^2K)
-3\operatorname{tr}(YK^2)+\operatorname{tr}K^3\}.
\end{aligned}
\tag{67}
\]

The final line is the signed length-two path current discarded in (47).
It remains inside support \(3\mu<2\).

For an explicit execution, take homogeneous Bernoulli selection with
density \(q\), and put \(r=1-q\).  The full local traces per zero are

\[
\begin{aligned}
C_1&=\mu,\\
C_2&=\mu(1+M_2)=0.9161239970\ldots,\\
C_3&=\mu(1+3M_2+M_3)=1.3704298319\ldots .
\end{aligned}
\tag{68}
\]

The exact-two and all-equal contractions are

\[
S_{21}=3\mu(C_2-\mu^2)=0.9434425204\ldots,\qquad
S_{111}=\mu^3=0.2962074163\ldots .
\tag{69}
\]

Bernoulli index counting gives

\[
\begin{aligned}
\mathbb E\operatorname{tr}R_q/N
&=rC_1,\\
\mathbb E\operatorname{tr}R_q^2/N
&=r^2C_2+r(1-r)\mu^2,\\
\mathbb E\operatorname{tr}R_q^3/N
&=r^3C_3+(r^2-r^3)S_{21}+(r-r^3)S_{111}.
\end{aligned}
\tag{70}
\]

Centering \(R_q-I\), substituting (70) into \(P\), and preserving every
sign gives the exact contrast polynomial

\[
\boxed{\displaystyle
\Delta_{\mathrm{exact}}(q)
=-0.0822256863366q
+0.0844874949712q^2
+0.0193981750834q^3.}
\tag{71}
\]

Its positive zero is

\[
q_0=0.819162462\ldots .
\tag{72}
\]

At the charged cubic floor \(q=0.97005316559\),

\[
\Delta_{\mathrm{exact}}(q)
=0.01744681298\ldots .
\tag{73}
\]

If the simple labels were homogeneous in this third current, (9) would give

\[
0.97005316559+
\frac{0.01744681298\ldots}{1-L^\sharp/2}
=0.99417306758\ldots .
\tag{74}
\]

Equation (71) is a completed outside-class calculation, not a missing
selector lemma.  The accepted scalar inputs do not force homogeneous labels,
so only (7), not (74), is asserted unconditionally.

## 7. Double atoms and the first scalar two-block calculation

A double atom in the wide block has compressed eigenvalue

\[
2\mu=1.3332,\qquad y_2=2\mu-1=0.3332.
\tag{75}
\]

It is visible both to the true threshold tail and to the cubic:

\[
y_2^2=0.11102224,\qquad
P(y_2)=0.1064600905\ldots>0.
\tag{76}
\]

The charged cubic removal allowance on this direction is

\[
L^\sharp-P(y_2)
=0.4468662881\ldots ,
\tag{77}
\]

already substantially smaller than the old flat allowance
\(L-P(y_2)=0.6494235660\ldots\).

For comparison with the inherited quartic block, a double atom at
\(\mu_4=0.4999\) has

\[
y_4=2\mu_4-1=-0.0002,
\tag{78}
\]

and

\[
P_4(y_4)=-0.0326371211\ldots,\qquad
L_4-P_4(y_4)=0.6118256398\ldots .
\tag{79}
\]

Thus simply appending the old quartic scalar trim adds \(0.6118\ldots\) of
removal freedom to every double direction.  The direct-sum scalar two-block
route cannot improve the charged cubic theorem; it weakens the localization
constraint.  This closes that concrete two-block variant.

## Terminal handoff

The cycle terminates because the \(100\%\) asymptotic target has been reached.

\[
\boxed{\displaystyle
\liminf_{T\to\infty}
\frac{N_{0,\mathrm{simple}}(T,2T)}{N(T,2T)}=1.}
\]

The density-one closure is the exact rational certificate (A2)--(A15).
Its engine is the charged stability identity (20)--(33).  The intermediate
cubic theorem, exact rank-one selector deletion, affine-class obstruction,
and signed length-two calculation are retained as constructive supporting
results.  No further cycle is required.
