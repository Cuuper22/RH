# Hybrid 100, cycle 1: the higher-moment top-hat obstruction and a cap-profile increment

## Terminal outcome

This cycle gives a strict unconditional improvement, using only the already
proved strict arithmetic bandwidth below two:

\[
 \boxed{\displaystyle
 \frac{N_{0,\mathrm{simple}}(T,2T)}{N(T,2T)}
 >0.9567-o(1).}
 \tag{1}
\]

A directed version of the calculation is

\[
 \frac{s}{N}>0.9567290-o(1).
 \tag{2}
\]

This improves the inherited cycle-start floor \(0.95063832187565\) by more
than \(0.00609067\).  It also improves the subsequently saved tightened
top-hat floor \(0.95225662869565\) by more than \(0.00447237\).  The gain is
not added to either earlier certificate: the old block is discarded, one
new principal block is inserted into the same global stability inequality,
and its fixed point is solved from scratch.  Thus there is no overlap or
double counting.

The attempted sixth/eighth-moment top-hat route is also closed below.  Even
granting that route the entire compact limiting law, rather than just the
available moments, its best residual is smaller than the fourth-moment
increment already present at the start of the cycle.  The successful reading
change is therefore a profile-sensitive mixed fourth trace: it retains the
diagonal, two noncrossing, and crossing contractions for a block which follows
the full Euler cap instead of being flat.

Throughout, \(N=N(T,2T)\), \(s=N_{0,\mathrm{simple}}(T,2T)\), and the accepted
pair-cost input is

\[
 \sigma=1.9999,\qquad D\leq1.06772567.
 \tag{3}
\]

## 1. Why a single top-hat sixth or eighth moment cannot improve the floor

For the mean-one top-hat

\[
 r_p(t)=p^{-1}1_{[-p/2,p/2]}(t),
 \tag{4}
\]

the complete centered block law represented by all of its trace moments is

\[
 \rho_{\mu,p}=(1-p)\delta_{-1}
 +p\,\mathcal L\!\left(\frac{1-p}{p}+\mu X\right),
 \tag{5}
\]

where \(X\) has the symmetric triangular density

\[
 f_X(x)=\frac{1-|x|/\sqrt2}{\sqrt2}
 1_{[-\sqrt2,\sqrt2]}(x).
 \tag{6}
\]

Indeed,

\[
 \mathbb E X^{2k}=\frac{2^{k+1}}{(2k+1)(2k+2)},
 \qquad \mathbb E X^{2k+1}=0.
 \tag{7}
\]

In particular, the new flat sixth and eighth contractions would be

\[
 \mathbb E X^6=\frac27,qquad \mathbb E X^8=\frac{16}{45}.
 \tag{8}
\]

This description gives a useful impossibility result stronger than any
finite moment dual.  Let

\[
 \varepsilon_0=0.01836399187565,qquad
 \frac{b_0}{N}=\frac{D-1-\varepsilon_0}{2}
 =0.024680839062175.
 \tag{9}
\]

After the best possible removal of the \(b_0\) largest positive directions,
the exact residual supplied by (5) is

\[
 \mathcal R(\mu,p)=
 \mu p\int_{x_+}^{x_\alpha}
 \left(\frac{1-p}{p}+\mu x\right)^2f_X(x)\,dx,
 \tag{10}
\]

where

\[
 x_+=\max\!\left(-\sqrt2,-\frac{1-p}{\mu p}\right),qquad
 \mathbb P(X\geq x_\alpha)=\frac{b_0}{\mu pN}.
 \tag{11}
\]

The triangular tail inverse used in (11) is elementary:

\[
 x_t=\begin{cases}
 \sqrt2(1-\sqrt{2t}),&0\leq t\leq1/2,\\
 -\sqrt2+\sqrt{\,4(1-t)\,},&1/2\leq t\leq1.
 \end{cases}
 \tag{12}
\]

An order-\(d\) trace must obey \(d\mu<2\).  Pointwise allocation under the
accepted full symbol \(V_\sigma\) also requires

\[
 pV_\sigma(\mu p/2)\geq1.
 \tag{13}
\]

Substitution of (12) makes (10) a piecewise polynomial-radical expression.
Directed differentiation on its two pieces puts its supremum at the limiting
largest bandwidth and the smallest \(p\) allowed by (13).  The resulting
enclosures are

\[
\begin{array}{c|c|c|c}
 d&\mu\uparrow2/d&p_{\min}&\sup\mathcal R(\mu,p)\\ \hline
 6&1/3&0.8080242\ldots&<0.0166770\\
 8&1/4&0.8031468\ldots&<0.0104560
\end{array}
\tag{14}
\]

Both are below \(\varepsilon_0\).  Since access to the entire law (5) is
strictly stronger than access to its first six or eight moments, no
single-top-hat sixth- or eighth-moment dual within strict total bandwidth two
can improve the inherited floor.  This is the precise killed class.

## 2. The outside-class cap profile

Keep

\[
 \mu=0.4999,qquad 4\mu=1.9996<2.
 \tag{15}
\]

Let \(V_\sigma\) be the accepted normalized Euler optimizer.  For

\[
 b_\sigma=\frac{2-\sigma}{2}=0.00005,
\tag{16}
\]

it has the closed form

\[
 V_\sigma(x)=\frac{\sigma}{M}
 \begin{cases}
 \cos(\sqrt2x),&|x|\leq b_\sigma,\\
 A\cos(|x|-1/2)+B\sin(\sqrt3(|x|-1/2)),&|x|\geq b_\sigma,
 \end{cases}
 \tag{17}
\]

with the already accepted directed values

\[
 A=0.8312126609842\ldots,\quad
 B=-0.3551542095561\ldots,\quad
 M=1.5939724172081\ldots .
 \tag{18}
\]

Take the fixed rational cutoff

\[
 a=\frac{403}{1000}
 \tag{19}
\]

and define

\[
 m_a=2\int_0^aV_\sigma(\mu t)\,dt,qquad
 \kappa=m_a^{-1},qquad
 r_*(t)=\kappa V_\sigma(\mu t)1_{[-a,a]}(t).
 \tag{20}
\]

Direct evaluation of the elementary antiderivatives gives

\[
 m_a=1.0010321057860\ldots,qquad
 \kappa=0.9989689583579\ldots<1.
 \tag{21}
\]

Consequently \(\int_I r_*=1\), and, pointwise,

\[
 0\leq r_*(t)<V_\sigma(\mu t)\quad(|t|\leq a),
 \qquad r_*(t)=0\quad(|t|>a).
 \tag{22}
\]

Thus this is a strict admissible principal-block symbol.  As in the accepted
top-hat construction, its endpoint jumps denote the limit of smooth tapers;
the strict factor \(\kappa<1\) leaves room for such a taper while preserving
normalization and (22).

## 3. Its complete mixed fourth trace

Put \(q=r_*-1\) on \(I=[-1/2,1/2]\), and

\[
 h(x)=\int_I|x-y|r_*(y)\,dy.
 \tag{23}
\]

The accepted strict-bandwidth trace identities are

\[
 M_2=\int_Iq^2+\mu^2\int_Ir_*h,
 \tag{24}
\]

\[
 M_3=\int_Iq^3+3\mu^2\int_Iqr_*h,
 \tag{25}
\]

and

\[
\begin{aligned}
M_4={}&\int_Iq^4+4\mu^2\int_Iq^2r_*h\\
&+2\mu^2\iint_{I^2}q(x)r_*(x)q(y)r_*(y)|x-y|\,dx\,dy\\
&+2\mu^4\int_Ir_*(x)^2h(x)^2\,dx+\mu^4\mathcal X(r_*),
\end{aligned}
\tag{26}
\]

where

\[
\mathcal X(r)=\iiint_{x+z-y\in I}|x-y||y-z|
r(x)r(y)r(z)r(x+z-y)\,dx\,dy\,dz.
\tag{27}
\]

For this compact profile, the crossing term can be evaluated without a
three-dimensional indicator.  If \(g_d(y)=r_*(y)r_*(y+d)\), then

\[
 \mathcal X(r_*)=
 2\int_0^{2a}d
 \iint_{[-a,a-d]^2}|y-z|g_d(y)g_d(z)\,dy\,dz\,dd.
 \tag{28}
\]

Splitting the elementary trigonometric integrals at
\(0,\pm b_\sigma/\mu\), and using (28) for the crossing contraction gives the
directed enclosures

\[
 0.3076<M_2<0.3077,qquad
 -0.1350<M_3<-0.1348,qquad
 0.2327<M_4<0.2330.
 \tag{29}
\]

For orientation, the central values before outward rounding are

\[
 (M_2,M_3,M_4)
 =(0.3076628\ldots,-0.1348908\ldots,0.2328382\ldots).
 \tag{30}
\]

The five summands in (26), in order, are

\[
 0.19673996\ldots,\quad0.01522174\ldots,\quad
 0.00758924\ldots,\quad0.01160956\ldots,\quad
 0.00167762\ldots .
 \tag{31}
\]

Thus the gain is genuinely mixed: deleting either the noncrossing or
crossing contractions changes the certificate, and no second block is being
summed into it.

## 4. A global rational quartic dual

Take exact rational contacts

\[
 a_-=-\frac{9209}{10000},qquad
 c=\frac{2647}{10000},qquad
 t=\frac{10363}{10000}.
 \tag{32}
\]

Define the quartic \(P\) and cap \(L\) uniquely by

\[
 P(a_-)=P'(a_-)=0,\quad
 P(c)=c^2,\quad P'(c)=2c,\quad
 P(t)=L,\quad P'(t)=0.
 \tag{33}
\]

This is an exact rational certificate.  Its decimal display is

\[
\begin{aligned}
P(y)={}&-0.03925241077366+0.28264206928260y
 +0.52639755217849y^2\\
&-0.05766484246368y^3-0.26684131318378y^4,\\
L={}&0.44703407935309.
\end{aligned}
\tag{34}
\]

Exact polynomial division gives

\[
 P(y)=(y-a_-)^2Q_-(y),\quad
 y^2-P(y)=(y-c)^2Q_2(y),\quad
 L-P(y)=(y-t)^2Q_L(y).
 \tag{35}
\]

In ascending coefficient order, the three remaining quadratics and their
discriminants are

\[
\begin{array}{c|ccc|c}
 &1&y&y^2&\operatorname{disc}\\ \hline
Q_-&-0.04628511&0.43380348&-0.26684131& 0.13878233\\
Q_2& 0.56021979&0.19893063& 0.26684131&-0.55838574\\
Q_L& 0.45281542&0.61072014& 0.26684131&-0.11034034
\end{array}
\tag{36}
\]

The two roots of \(Q_-\) are \(0.11480\ldots\) and
\(1.51089\ldots\), so \(Q_-<0\) on \((-\infty,0]\).  The other two
quadratics have positive leading coefficient and negative discriminant.
Therefore, globally,

\[
 P(y)\leq0\ (y\leq0),qquad
 P(y)\leq y^2\ (y\geq0),qquad
 P(y)\leq L\ (y\geq0).
 \tag{37}
\]

## 5. One-block fixed point and the new floor

Write

\[
 \frac{s}{N}=2-D+\varepsilon,qquad
 \alpha=\frac{D-1-\varepsilon}{2\mu}.
 \tag{38}
\]

The accepted stability inequality has only one global trim:

\[
 E_b(G)\leq\varepsilon N.
 \tag{39}
\]

Applying (37) to the single compression with law moments (29) gives

\[
 E_b(G)\geq
 \mu N\bigl(A_P-\alpha L\bigr),qquad
 A_P=P_0+P_2M_2+P_3M_3+P_4M_4.
 \tag{40}
\]

The signs in (34) and the directed sides of (29) give, without midpoint
rounding,

\[
 A_P>
 P_0+0.3076P_2-0.1348P_3+0.2330P_4
 >0.0682666.
 \tag{41}
\]

Combining (38)--(41) and solving the affine fixed point once gives

\[
 \varepsilon\geq
 \frac{\mu A_P-\frac L2(D-1)}{1-L/2}
 >0.0244547.
 \tag{42}
\]

Finally,

\[
 \frac{s}{N}=2-D+\varepsilon
 >2-1.06772567+0.0244547
 =0.95672903.
 \tag{43}
\]

Equivalently, the positive/nonsimple-direction budget forced by this same
fixed point drops to

\[
 \frac bN\leq
 \frac{0.06772567-0.0244547}{2}
 =0.021635485.
 \tag{44}
\]

This directly excludes the former near-\(100\%\) adversary: it cannot place
all of its remaining positive directions under the cap-following block's
mixed fourth-trace law.

## Terminal handoff

The single top-hat higher-moment branch is exhausted at sixth and eighth
order by the full-law upper bounds (14).  The first calculation outside that
class is already terminal: the strict cap-following block, its complete
mixed fourth trace, and the exact rational dual (32)--(37) yield the
unconditional floor (1)--(2), with no arithmetic support beyond
\(4\mu=1.9996<2\) and no residual-union assumption.
