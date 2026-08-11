# Zeta-95 arithmetic, cycle 3: why the four Kloosterman gains do not tensor

## 0. Terminal outcome

Retain the exact MD9 moment and the numerical parameters from cycle 2:

\[
 \rho=0.1246023080837601868\ldots,\qquad
 L=H^\rho,
\tag{1}
\]

\[
 \sum_{\ell\asymp L}|E(\ell)|^2
 \ll H^{2-\rho+o(1)}.                                      \tag{MD9}
\]

The hoped-for fourfold iteration of the \(H^{-1/32}\) Kloosterman saving is
not a valid operation.  The \(1/32\) in Blomer--Pascadi is already the output
of two Cauchy--Schwarz steps and a single four-cycle.  In MD9 every possible
four-cycle contains the same shift vertex \(\ell\).  A second independent
cycle requires separating that vertex by an additional Cauchy step, costing
\(L^{1/2}\).  At (1), this cost is larger than another \(H^{-1/32}\) gain.

For the dependency-hypergraph class defined below, the maximum useful packing
number is therefore

\[
                         \boxed{\nu_{\rm BP}=1}.             \tag{2}
\]

More explicitly, if one forces \(j\) nominal BP applications, their total
possible saving exponent is at most

\[
 g_j=\frac{j}{32}-\frac{j-1}{2}\rho.                        \tag{3}
\]

Numerically,

\[
\begin{array}{c|c|c}
j&g_j&\text{resulting amplitude exponent }1+\rho-g_j\\ \hline
1& \phantom{-}0.031250000000000&1.093352308083760\\
2& \phantom{-}0.000198845958120&1.124403462125640\\
3&             -0.030852308083760&1.155454616167520\\
4&             -0.061903462125640&1.186505770209400
\end{array}                                                   \tag{4}
\]

Thus one application is optimal in this class and still leaves the factor

\[
 H^{\rho-1/32}=H^{0.0933523080837602\ldots}.                 \tag{5}
\]

I then execute a calculation outside that class by retaining \(\ell\) inside
the quadratic-character mechanism.  For the general Kloosterman multiplier
\(a\), the BP four-cycle has discriminant

\[
 \boxed{
 \mathscr D_a(\mathbf h)
 =(P-aQ)(P-aQ+4a^2),
 \quad
 P=h_1h_2h_3h_4,
 \quad Q=(h_1+h_3)(h_2+h_4).}                               \tag{6}
\]

For an odd prime modulus and nonzero dual frequencies this is not a square
polynomial in \(a\).  Complete character orthogonality consequently gives a
square-root saving in the multiplier average.  Applied with \(a=u\ell\), it
gives

\[
 \sum_{\ell}w(\ell/L)
 \left(\frac{\mathscr D_{u\ell}(\mathbf h)}{c}\right)
 \ll c^{1/2+o(1)}                                           \tag{7}
\]

when \(L<c\), and \(\ll Lc^{-1/2+o(1)}\) when \(L\ge c\).
This is the first coefficient/character calculation that genuinely keeps the
common shift after the four-cycle rather than treating it as a fixed
parameter.

For the hard uniform block, however, \(c\asymp H\) and
\(L=H^{0.124602\ldots}<H^{1/2}\), so (7) is worse than the trivial \(L\)
bound by

\[
 H^{1/2-\rho}=H^{0.375397691916240\ldots}.                  \tag{8}
\]

The quadratic-character refinement therefore does not close MD9.  It also
shows exactly why it does not: the available character has the large terminal
modulus, not a depth-nine atom modulus.  A small-modulus version would handle
composite terminal moduli having a divisor \(c_0\le L^2\), but the prime
terminal moduli remain and are part of the required uniform theorem.

Accordingly this cycle takes the permitted **kill plus outside calculation**
branch.  No support \(>2\) is claimed.  The unconditional limiting endpoint
and mixed certificate remain

\[
 \boxed{\sigma<2,\qquad
 \liminf\frac{N_{0,\mathrm{simple}}}{N}
 \ge0.938313327050949\ldots .}                              \tag{9}
\]

## 1. The actual HB factor dependency graph

For one dyadic depth-nine block, pair each short and long HB variable into a
factor group and write

\[
 p=x_1\cdots x_9,qquad q=y_1\cdots y_9,qquad
 \prod_iX_i\asymp\prod_jY_j\asymp H,                       \tag{10}
\]

where \(x_i\asymp X_i\), \(y_j\asymp Y_j\), and the coefficient on each
group is the actual \(\mu\)-, \(1\)-, or logarithmic HB coefficient.  Factors
of length one are allowed.  The resonance is

\[
                r x_1\cdots x_9-k y_1\cdots y_9=\ell.       \tag{11}
\]

It is important not to confuse the nine factor groups in (10) with the four
variables in the BP four-cycle.  To apply a bilinear Kloosterman theorem one
chooses subsets \(I,J\) and collapses

\[
 m=\prod_{i\in I}x_i,\quad m'=\prod_{i\notin I}x_i,qquad
 n=\prod_{j\in J}y_j,\quad n'=\prod_{j\notin J}y_j.         \tag{12}
\]

The collapsed coefficients are legitimate arbitrary sequences.  But the
first Cauchy step in the BP proof removes one such sequence by its \(L^2\)
norm; the second Cauchy step duplicates the other sequence into four copies.
The result is one cyclic product of four Kloosterman sums.  Thus Cauchy
**duplicates** all HB atoms contained in a collapsed coefficient.  It does not
separate them into unused factor groups to which the theorem can be applied
again.

This agrees with the actual statement and proof architecture of
[Blomer--Pascadi, Theorem 1.1](https://arxiv.org/abs/2607.24311): for a fixed
modulus \(c\), fixed multiplier \(a\), and two arbitrary interval-supported
sequences, the square-root-range bound is a single
\(c^{-1/32+o(1)}\) improvement.  Its proof already uses two Cauchy steps and
the four-cycle

\[
 \sum_{n_1,n_2,n_3,n_4}
 S(n_1,n_2;c)S(n_2,n_3;c)S(n_3,n_4;c)S(n_4,n_1;c).          \tag{13}
\]

The four factors in (13) produce one \(1/32\), not four copies of \(1/32\).

## 2. A precise dependency-hypergraph impossibility theorem

Define the hypergraph \(\mathcal H_{\rm MD9}\) as follows.

* Its distinguished vertex is \(z=\ell\).
* It has factor vertices \(X_1,\ldots,X_9,Y_1,\ldots,Y_9\).
* A prospective BP edge is the set of active variables in one completed
  bilinear Kloosterman block obtained from (12).  Because the Kloosterman
  multiplier is \(\ell\) times frozen units, every BP edge contains \(z\).
* BP edges are called independent only if their Cauchy duplications are
  disjoint.  Sharing \(z\) is allowed only after an additional Cauchy step in
  the \(\ell\)-sum; that separation is charged its exact \(L^{1/2}\) norm.

Without separation all BP edges meet at \(z\), so their matching number is
one.  Suppose instead that \(j\) edges are forced to be independent.  The
first uses the original \(z\).  Each of the remaining \(j-1\) edges requires
one further copy of the common shift law.  Repeated Cauchy gives the cost

\[
                         L^{(j-1)/2}.                        \tag{14}
\]

Even granting the ideal square-root saving \(H^{-1/32}\) to every edge, the
net factor relative to the trivial amplitude is

\[
 H^{-j/32}L^{(j-1)/2}
 =H^{-g_j},                                                  \tag{15}
\]

with \(g_j\) as in (3).  Since

\[
 \frac\rho2-\frac1{32}
 =0.0310511540418801\ldots>0,                               \tag{16}
\]

\(g_{j+1}<g_j\) for every \(j\ge1\).  Hence (2) follows.

The same conclusion holds if one Cauchy-squares MD9 first.  The common
difference

\[
 \Delta=\ell_1-\ell_2,qquad |\Delta|\ll L,                 \tag{17}
\]

replaces \(z\); every completed four-cycle contains \(\Delta\), and making a
second independent cycle again costs \(L^{1/2}\).  Thus differencing does not
free four independent copies of the nine factors.

This proves an impossibility theorem for the stated dependency-hypergraph
class.  It does not rule out an estimate which obtains cancellation from the
common shift vertex itself.

## 3. Exact character calculation outside the hypergraph class

We now keep that vertex.  The prime-modulus sketch of BP starts, after its two
Cauchy steps, from the recurrence

\[
                    a x_j+\overline{x}_{j-1}=h_j
                    \pmod c,qquad j\pmod4,                 \tag{18}
\]

where the fixed Kloosterman multiplier is denoted by \(a\).  Introduce the
Möbius matrices

\[
 M_j(a)=\begin{pmatrix}h_j&-1\\a&0\end{pmatrix}.            \tag{19}
\]

The cyclic solutions of (18) are the fixed points of
\(G_a=M_4(a)M_3(a)M_2(a)M_1(a)\).  Direct multiplication, with no estimate,
gives

\[
 \det G_a=a^4,                                              \tag{20}
\]

\[
 \operatorname{tr}G_a
 =h_1h_2h_3h_4-a(h_1+h_3)(h_2+h_4)+2a^2
 =P-aQ+2a^2.                                                \tag{21}
\]

The fixed-point discriminant is therefore precisely (6):

\[
 (\operatorname{tr}G_a)^2-4\det G_a
 =(P-aQ)^2+4a^2(P-aQ)
 =(P-aQ)(P-aQ+4a^2).                                       \tag{22}
\]

For odd prime \(c\), if all \(h_i\not\equiv0\pmod c\), then \(P\ne0\).
If \(Q\ne0\), (22) has odd degree three and cannot be a square polynomial.
If \(Q=0\), it is \(P(P+4a^2)\), again nonsquare because \(P\ne0\).  Hence
the Weil bound, including an additive twist, gives uniformly in \(t\)

\[
 \left|
 \sum_{a\bmod c}
 \left(\frac{\mathscr D_a(\mathbf h)}c\right)e(at/c)
 \right|\ll c^{1/2}.                                       \tag{23}
\]

The zero-frequency cases excluded above are exactly the already separated
BP diagonal/zero modes.  A unit multiple \(a=u\ell\) only permutes residues,
so (23) applies to the actual shift multiplier.

Poisson summation modulo \(c\), using (23), now proves (7).  Indeed,

\[
\begin{aligned}
 &\sum_{\ell}w(\ell/L)
 \left(\frac{\mathscr D_{u\ell}(\mathbf h)}c\right)\\
 &\quad=\frac Lc\sum_{t\in\mathbb Z}
 \widehat w(tL/c)
 \sum_{a\bmod c}
 \left(\frac{\mathscr D_{ua}(\mathbf h)}c\right)e(at/c),
\end{aligned}                                               \tag{24}
\]

and rapid decay of \(\widehat w\) yields

\[
 \ll c^{1/2+o(1)}\left(1+\frac Lc\right).                  \tag{25}
\]

This is a real extra orthogonality calculation: the published theorem treats
\(a\) as fixed, whereas (24) retains the signed \(\ell\)-average through the
quadratic-character stage.

## 4. Why (24) still cannot close the terminal block

In the uniform MD9 terminal block the relevant Kloosterman modulus can be a
prime \(c\asymp H\).  Equations (1) and (25) then give \(H^{1/2+o(1)}\), while
the unestimated \(\ell\)-sum has length only \(H^\rho\).  Thus completion is
nontrivial only for \(L>c^{1/2+o(1)}\), very far from (1).

One may replace completion by a Burgess treatment of the nonsquare cubic
character in (22), but its general-modulus nontriviality begins only beyond
the quarter-modulus scale.  Here

\[
                         \rho<\frac18<\frac14,               \tag{26}
\]

so it also supplies no terminal saving.  The special factorization of the HB
coefficient does not factor the prime Kloosterman modulus; assigning the
character in (22) to a short HB atom would change the congruence and is not a
valid substitution.

For composite \(c\), (24) is useful on a divisor \(c_0\) only when
\(c_0\lesssim L^2\).  But a theorem for the full prime-side kernel must also
cover the prime moduli \(c\asymp H\), so this does not give an unconditional
support increment.

## 5. Exact remaining construction

The calculations above eliminate two tempting but invalid routes:

1. the four variables in the BP four-cycle do not yield four independent
   \(1/32\) savings; and
2. averaging the common multiplier inside its quadratic character is too
   short at the prime terminal modulus.

The next construction must therefore change the modulus before the character
stage.  Concretely, one needs a coefficient-sensitive divisor-switching
identity for (11) that produces a character modulus

\[
                         c_0\le L^2=H^{2\rho},               \tag{27}
\]

while retaining the remaining HB factors in two \(L^2\)-controlled
sequences.  Then (24) gives a genuine multiplier saving, and only one BP
four-cycle is needed afterwards.  Without (27), neither Cauchy iteration nor
quadratic-character orthogonality reaches MD9.

## 6. Handoff

* Dependency-hypergraph maximum: one useful BP gain.
* Four forced gains have net exponent \(-0.0619034621\), not \(+1/8\), after
  the three necessary \(L^{1/2}\) separation costs.
* Exact outside calculation: the general-multiplier discriminant (6) and the
  character-orthogonality bound (25).
* Blocker: for prime terminal modulus \(c\asymp H\), the \(\ell\)-interval is
  below both completion and Burgess ranges.
* Supported endpoint remains \(\sigma<2\), giving the accepted mixed
  pair-plus-quartic value \(0.938313327050949\ldots\).
* Immediate next inequality: divisor-switch MD9 to a character modulus
  \(c_0\le L^2\) before applying (24).
