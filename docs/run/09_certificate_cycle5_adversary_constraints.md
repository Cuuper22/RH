# Certificate architect, cycle 5: the explicit 67.25% adversary

## Outcome

Let

\[
 C_\star=\frac12+\frac1{\sqrt2}\cot\!\left(\frac1{\sqrt2}\right)
 =1.3274992963205885\ldots.
\tag{1}
\]

The sharp bandwidth-one adversary is

\[
 s_\star=2-C_\star=0.6725007036794115\ldots,
 \qquad
 d_\star=\frac{C_\star-1}{2}=0.1637496481602943\ldots,
 \qquad p_\star=0,
\tag{2}
\]

where \(s\) is simple on-line mass, \(d\) is double on-line mass counted by
distinct ordinates, and \(p\) is off-line pair mass.  It obeys

\[
 s_\star+2d_\star=1,
 \qquad
 s_\star+4d_\star=C_\star.
\tag{3}
\]

I encoded the following unconditional constraint family:

1. total multiplicity, first two bandwidth-one traces, integrality, inertia,
   and distinct-zero count;
2. the accepted simple/critical-line and distinct-zero lower bounds;
3. \(\xi'\)-interlacing and the accepted \(86.864\%\) simple-on-line theorem
   for \(\xi'\);
4. zero-density, multiplicity, zero-gap, and one-point \(S(t)\) capacity
   constraints;
5. every small-band moment in the strict Rudnick--Sarnak range as a separate
   compression constraint, and all blocks when an exact flat
   power-complementary nesting is imposed.

The adversary is feasible for every constraint in this defined family.  The
corresponding LP optimum is exactly \(s_\star\); hence this family cannot give
any numerical gain.

The first explicit statistic outside that family is the positive quartic
residual

\[
\boxed{
 \mathcal R_4(A)
 :=\operatorname{tr}
 \left(I-\frac74A+\frac23A^2\right)^2.}
\tag{4}
\]

The sine-process fourth-moment value is

\[
 \frac{\mathcal R_4(A)}N=\frac5{36},
\tag{5}
\]

which would give the unconditional numerical improvement

\[
 \frac{N_0^s(T,2T)}{N(T,2T)}
 \ge\frac{13}{18}-o(1)
 =0.722222\ldots-o(1).
\tag{6}
\]

The adversary instead has residual \(19/108\), exceeding (5) by exactly
\(1/27\).  Thus (4), not another bookkeeping count, is the first concrete
attack that separates it.  The arithmetic input still missing is a one-sided
prime-side upper bound for this *single combined residual*; separate fourth
trace asymptotics are unnecessary.

## 1. The count LP and its exact optimum

Normalize \(N=1\).  In the no-off-line, multiplicity-at-most-two branch the
count constraints are

\[
 s+2d=1,
 \qquad
 s+4d=C_\star,
 \qquad
 s,d\ge0.
\tag{7}
\]

They have the unique solution (2).  The distinct mass is

\[
 D_\star=s_\star+d_\star
 =\frac{3-C_\star}{2}
 =0.8362503518397058\ldots.
\tag{8}
\]

In particular,

\[
 D_\star-\frac56
 =0.0029170185063725\ldots>0,
\tag{9}
\]

so the accepted \(5/6\) distinct-zero constraint does not remove the
adversary.  Optimizing the bandwidth-one window replaces the flat
\((s,d)=(2/3,1/6)\) point by (2), but leaves the same simple/double geometry.

## 2. Why the additional unconditional counts do not cut it

### Critical line and zero density

The adversary puts every zero on the critical line.  It therefore satisfies
every lower bound for critical-line mass and every upper bound for off-line
density, with slack.

### Multiplicity and gaps

All multiplicities are at most two.  The zero-gap mass among zeros counted
with multiplicity is exactly

\[
 d_\star=0.1637496481\ldots<\frac16.
\tag{10}
\]

Thus every gap theorem whose count consequence is the accepted
\(D\ge5/6\) is already represented by (9).  Pointwise multiplicity bounds and
fixed one-point moment bounds for \(S(t)\) are also satisfied: the adversary
uses only jumps of size one and two and can distribute its distinct ordinates
with the accepted macroscopic density.

### Zeros of \(\xi'\)

Under this on-line model, a double zero of \(\xi\) produces a simple zero of
\(\xi'\) at the same ordinate.  Consecutive distinct zeros of \(\xi\) provide
the remaining interlacing zeros of \(\xi'\).  Choosing those interlacing zeros
simple gives asymptotically \(100\%\) simple on-line zeros of \(\xi'\), so the
accepted \(86.864\%\) lower bound for \(\xi'\) is compatible with (2).  A
lower bound on simple \(\xi'\)-zeros cannot distinguish simple from double
\(\xi\)-zeros; an upper bound on common zeros of \(\xi\) and \(\xi'\) would be
new information equivalent to attacking the double population directly.

## 3. Third traces and all strict small-band moments

The full equality matrix is

\[
 A_\star=I+J,
 \qquad
 \operatorname{spec}(A_\star)
 =\{0^{(d_\star N)},1^{(s_\star N)},2^{(d_\star N)}\}.
\tag{11}
\]

It has

\[
 \frac1N\operatorname{tr}A_\star=1,
 \qquad
 \frac1N\operatorname{tr}A_\star^2=C_\star.
\tag{12}
\]

For the flat endpoint \(d=1/6\), its cubic moment is

\[
 \frac1N\operatorname{tr}A_\star^3
 =\frac23+8\cdot\frac16=2,
\tag{13}
\]

which equals the sine-process value \(m_3(1)=2\).  Hence even an admissible
global cubic trace would not separate the flat adversary.

There is no accepted identity coupling the optimized Montgomery--Taylor
matrix (11) to a flat equal-band partition.  Exact power-complementary equal
subbands reconstruct the flat bandwidth-one window instead.  In that branch,
the collective small-band moments also fail: they admit the following common
dilations of the flat \((s,d)=(2/3,1/6)\) adversary.

For \(r=2\), pair the
\(+1\) and \(-1\) directions of \(J\) and rotate each pair so its two block
diagonals are \(\pm1/2\); put the zero directions in zero fibers.  Each block
then has centered law

\[
 \frac16\delta_{-1/2}+\frac23\delta_0+\frac16\delta_{1/2},
\tag{14}
\]

matching all moments through degree three at \(\mu=1/2\).

For \(r=3\), put \(u=1/(3\sqrt2)\) and use three-dimensional fibers in
proportions

\[
 \frac25:\operatorname{spec}(-1,0,1),\ \operatorname{diag}( -u,0,u),
 \quad
 \frac1{10}:\frac13\mathbf1\mathbf1^T,
 \quad
 \frac1{10}:-\frac13\mathbf1\mathbf1^T,
 \quad
 \frac25:0,
\tag{15}
\]

cycling diagonal permutations.  Every block has centered law

\[
 \frac2{15}\delta_{-u}
 +\frac1{10}\delta_{-1/3}
 +\frac8{15}\delta_0
 +\frac1{10}\delta_{1/3}
 +\frac2{15}\delta_u,
\tag{16}
\]

with

\[
 \mathbb EY^2=\frac1{27},
 \qquad
 \mathbb EY^4=\frac4{1215},
 \qquad
 \mathbb EY=\mathbb EY^3=\mathbb EY^5=0.
\tag{17}
\]

Thus all three blocks simultaneously match every strict moment through degree
five.  These are explicit common dilations, so adding the block constraints to
the flat LP does not improve \(2/3\).  Without a new mixed-trace identity they
also impose no inequality on the optimized matrix (11); treating the matrices
as though they were already the same compression would be an unsupported
coupling.

## 4. The first separating residual

Define

\[
 q(x)=1-\frac74x+\frac23x^2.
\tag{18}
\]

For \(x\le0\), all three terms in the form
\(1+(7/4)|x|+(2/3)x^2\) are nonnegative, so \(q(x)\ge1\).  For \(x>0\),
\(1-q(x)^2\le1\).  Therefore, pointwise on the real line,

\[
 \mathbf1_{x>0}\ge1-q(x)^2.
\tag{19}
\]

For every Hermitian \(N\times N\) matrix \(A\),

\[
 n_+(A)\ge N-\operatorname{tr}q(A)^2.
\tag{20}
\]

The accepted zero-side inertia count gives

\[
 N_0^s(T,2T)\ge2n_+(A)-N-o(N),
\]

and hence the exact implication

\[
\boxed{
 \frac{\mathcal R_4(A)}N\le R+o(1)
 \quad\Longrightarrow\quad
 \frac{N_0^s(T,2T)}N\ge1-2R-o(1).}
\tag{21}
\]

Expanding the single residual gives

\[
 \mathcal R_4(A)
 =N-\frac72\operatorname{tr}A
 +\frac{211}{48}\operatorname{tr}A^2
 -\frac73\operatorname{tr}A^3
 +\frac49\operatorname{tr}A^4.
\tag{22}
\]

At the sine-process moments

\[
 m_1=1,
 \qquad m_2=\frac43,
 \qquad m_3=2,
 \qquad m_4=\frac{13}{4},
\tag{23}
\]

equation (22) is exactly

\[
 1-\frac72+\frac{211}{36}-\frac{14}{3}+\frac{13}{9}
 =\frac5{36}.
\tag{24}
\]

Substitution in (21) gives (6).

For the flat adversary (11), direct evaluation gives

\[
 \frac{\mathcal R_4(A_\star)}N
 =\frac16q(0)^2+\frac23q(1)^2+\frac16q(2)^2
 =\frac{19}{108}.
\tag{25}
\]

The separation is

\[
 \frac{19}{108}-\frac5{36}=\frac1{27}.
\tag{26}
\]

For the optimized adversary, it is enough to prove the weaker strict bound

\[
 \frac{\mathcal R_4(A)}N<d_\star
 =0.1637496481602943\ldots;
\tag{27}
\]

then (21) already beats \(s_\star\).  The predicted \(5/36\) has margin

\[
 d_\star-\frac5{36}=0.0248607592714054\ldots.
\tag{28}
\]

## 5. Prime-side attack outside the impossible family

The construction target is not four separate moment theorems.  It is the
one-sided estimate

\[
\boxed{
 \operatorname{tr}
 \left(I-\frac74A_T+\frac23A_T^2\right)^2
 <\left(0.1637496481+o(1)\right)N.}
\tag{29}
\]

Decompose the bandwidth-one coefficient space into three slightly shrunken
subbands.  Expanding (29) as closed block walks separates:

1. all walks contained in one subband, whose moments through degree four lie
   in the strict support range;
2. two-block backtracking walks, controlled by the accepted global Frobenius
   trace and small-block moments;
3. the genuinely new alternating three-/four-block walks.

Only the third class lies outside the constraint family above.  Keep its
cubic and quartic terms combined with the coefficients \(-7/3\) and \(4/9\)
from (22); splitting them destroys the positivity of (4).  The weakest new
prime statistic is therefore the single mixed-walk upper bound needed to make
(29) hold.  If the cubic value \(m_3=2\) is supplied separately, the equivalent
fourth-moment threshold is only

\[
 \frac1N\operatorname{tr}A_T^4
 <3.305936708360662\ldots,
\tag{30}
\]

whereas the predicted value is \(13/4=3.25\) and the flat adversary gives
\(10/3=3.333\ldots\).

Equation (29) is the first executed attack outside the feasible LP family.  It
has a verified zero-side polynomial, an explicit numerical gate for any gain,
and the full predicted payoff \(13/18\).  Its remaining unsupported input is
one combined mixed quartic prime-side upper bound, not another count or
pointwise Hardy--Littlewood theorem.
