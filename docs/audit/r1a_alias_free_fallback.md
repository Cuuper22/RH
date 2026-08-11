# R1a A2.2 audit: the alias-free interval fallback

## Verdict

**Finished and killed for the stated method class.**  One window per block,
with support length at most its modulation period, does remove every nonzero
Poisson alias by the accepted Lemma 2.2 mechanism.  It does **not** produce
the mean-one principal block used in files 15--24.  In the base paper's hat
units the literal principal block has first moment $1/\sigma$, not $1$.
The source condition $r\leq V_\sigma$ is missing the factor $\sigma$: a
mean-one literal block requires

\[
  \boxed{\sigma r(t)\leq V_\sigma(x_0+\mu t)}.
\tag{1}
\]

For the quadratic profile used by the support-$143/100$ branch,

\[
  \sup V_\sigma=\frac{1200}{1031}<\frac{143}{100}\leq\sigma,
\tag{2}
\]

Thus (1) is impossible at every support relevant to A2.2.  There is an exact
alias-free interval restriction with intrinsic mean one, but its honest
principal compression is $C=H/\sigma$.  After correcting the stability
threshold, a common five-atom rational law matches the paper-derived closed
moments through degree four and has zero positive tail.  Thus the sharp
corrected $k\leq4$ moment problem has value exactly zero and supplies no quartic
increment over the two-trace bound.

This finish-or-kill result is confined to the finite A2.2 class specified in
the mission: one real window per interval, support no longer than period,
periods summing to the full support, the cycle-3
coefficient count, and the base normalization $G/(aL^2)$.  It does not
exclude a different coefficient count or normalization with a newly proved
zero-side trace budget, spectral information beyond four moments, or a new
modulation architecture outside both A2.1 and A2.2.

## 1. The missing factor in hat units

Use the notation of the accepted base layer:

\[
  \ell=\log(T/2\pi),\qquad L=\sigma\ell,
  \qquad a=\frac1L\int |\varphi|^2,
  \qquad \widehat G=\frac{G}{aL^2}.
\tag{3}
\]

These are the definitions recorded in `Zeta23/Defs.lean` and
`Zeta23/Assembly.lean`.  Cycle 3 chooses a cell period
$L_j=\mu_j\ell$ and

\[
 f_{j,k}(u)=\left(\frac L{L_j}\right)^{1/2}
 \varphi_j(u)e^{-i(T+2\pi k/L_j)u}.
\tag{4}
\]

When $\varphi_j$ is supported in one interval of length at most $L_j$,
Lemma 2.2 kills every nonzero alias.  The diagonal Poisson identity is then

\[
 \sum_{k\in\mathbb Z}|\widehat f_{j,k}(\tau)|^2
 =\frac L{L_j}\,L_j\int|\varphi_j|^2
 =L\int|\varphi_j|^2.
\tag{5}
\]

After division by $aL^2$, one zero contributes
$\int|\varphi_j|^2/(aL)$ to the block trace.  The block dimension is

\[
 d_j\sim\frac{L_jT}{2\pi}=\mu_jN,
 \qquad N\sim\frac{T\ell}{2\pi}.
\tag{6}
\]

Consequently its limiting first moment is

\[
 m_{1,j}
 =\frac{N\int|\varphi_j|^2/(aL)}{\mu_jN}
 =\frac1{a\sigma L_j}\int|\varphi_j|^2.
\tag{7}
\]

If $r_j$ denotes the intrinsic local allocation, normalized so that

\[
 \int_{-1/2}^{1/2}r_j(t)\,dt
 =\frac1{aL_j}\int|\varphi_j|^2,
\tag{8}
\]

then the literal principal mean is

\[
 \boxed{m_{1,j}=\frac1\sigma\int_{-1/2}^{1/2}r_j(t)\,dt.}
\tag{9}
\]

The same identity holds if amplitude is moved between the grid factor and
the window: writing the effective allocation as
$e_j=(\alpha_j^2L_j/L)|\varphi_j|^2$, exact reconstruction says
$\sum_je_j=v$, and (9) applies to $r_j=e_j/a$.  Therefore a prescribed
intrinsic mean-one symbol $r$ consumes the allocation $\sigma ar$, which
is exactly (1).  Multiplying the block by $\sigma$ afterwards gives the
matrix used in the source calculations, but $\sigma C$ is not a principal
compression and compression interlacing cannot be applied to it.

This identifies the precise false sentence in
`docs/run/03_certificate_cycle3.md` after equation (28): its block is
mean-one only at $\sigma=1$.  Terminal file 24 equation (30),
$r\leq V_\sigma$, uses the same omitted factor.

## 2. Exact alias-free construction and its unavoidable normalization

The alias-free geometry itself can be constructed.  Put

\[
 v(s)=1-\frac{169}{100}s^2,
 \qquad A=\int_{-1/2}^{1/2}v=\frac{1031}{1200},
 \qquad V_\sigma(x)=\frac{v(x/\sigma)}A
\tag{10}
\]

on $[-\sigma/2,\sigma/2]$.  For $0<2\mu<\sigma$, let

\[
 x_0=\sqrt{\frac{\sigma^2-\mu^2}{12}}.
\tag{11}
\]

The four points $\pm(x_0\pm\mu/2)$ lie strictly inside the full interval.
They divide it into five half-open intervals.  Assign one window

\[
 \varphi_j(x)=\sqrt{v(x/\sigma)}\,\mathbf1_{I_j}(x)
\tag{12}
\]

to each interval, with modulation period equal to $|I_j|$.  The supports
tile the full interval, so their squares reconstruct $v$ almost everywhere;
each support is one period, so every nonzero alias vanishes separately; and
the periods sum to \(\sigma\), preserving the cycle-3 coefficient count.

For either length-$\mu$ distinguished cell, the intrinsic symbol is

\[
 r(t)=V_\sigma(x_0+\mu t),\qquad -\tfrac12\leq t\leq\tfrac12.
\tag{13}
\]

It has exact mean one, because

\[
 \int_{-1/2}^{1/2}r(t)\,dt
 =\frac1A\left[1-\frac{169}{100}\left(
 \frac{x_0^2}{\sigma^2}+\frac{\mu^2}{12\sigma^2}\right)\right]
 =\frac{1-(169/100)/12}{A}=1.
\tag{14}
\]

Equation (9), however, says that the actual principal block is

\[
 \boxed{C=H/\sigma,}
\tag{15}
\]

where $H$ is the intrinsic mean-one matrix with symbol (13).  Rescaling
$\sqrt v$ or $\sqrt V$ changes $a$ and the unnormalized Gram matrix by
the same scalar and cannot alter (15).

For smooth compactly supported windows, taper each of the ten interval
endpoints over physical width $w$.  Since $0\leq v\leq1$, the absolute
change in the global normalization is at most $10w/(\sigma\ell)$; after
division by $A=1031/1200$, the relative full-energy loss is at most
$10w/(A\sigma\ell)$ and the distinguished intrinsic mean loss is at most
$2w/(A\mu\ell)$.  Taking $w=o(\ell)$ makes all of these losses $o(1)$,
while preserving support-within-period and hence alias-freeness.  These
explicit seam losses do not change the fixed factor $1/\sigma$.

There is also a structural uniqueness statement.  If one window per block
has support length at most its period, the periods sum to $L$, and the
positive full profile is reconstructed almost everywhere on a set of length
$L$, then the support intervals must tile that set up to null boundaries.
Indeed, their union has measure at most the sum of their lengths, namely
$L$, but must cover a set of measure $L$.  Equality forces no positive
overlap and full use of each period.  Thus the A2.2 restriction symbol is not
freely selectable: it is $V_\sigma/\sigma$ on its assigned cell.

Finally,

\[
 \sup V_\sigma=\frac1A=\frac{1200}{1031}
 <\frac{143}{100},
\tag{16}
\]

so no cell at any support in scope has average $V_\sigma$ as large as
$\sigma$.  Hence no A2.2 interval block can have literal mean one.  A flat
target would require $V_\sigma\geq\sigma$ throughout its cell, while the
terminal top hat $p^{-1}\mathbf1_{[-p/2,p/2]}$ would require
$V_\sigma\geq\sigma/p$ on its active set.

## 3. Honest moments

Write

\[
 \delta=\frac\mu\sigma,qquad
 r(t)=1+bt+c\left(t^2-\frac1{12}\right),
\tag{17}
\]

where

\[
 b^2=\left(\frac{4056}{1031}\right)^2
       \frac{\delta^2(1-\delta^2)}{12},
 \qquad c=-\frac{2028}{1031}\delta^2.
\tag{18}
\]

Let $Y=H-I$.  The paper-level substitution of (17) into terminal file 24
equation (18) gives the following rational closed moment formulas:

\[
 M_0=1,\qquad M_1=0,
\tag{19}
\]

\[
 M_2=Q_2+\mu^2H_0,qquad
 M_3=Q_3+3\mu^2H_1,
\tag{20}
\]

\[
 M_4=Q_4+4\mu^2H_2+2\mu^2D_\times+2\mu^4R+\mu^4X.
\tag{21}
\]

The nine rational polynomials $Q_2,Q_3,Q_4,H_0,H_1,H_2,D_\times,R,X$
are evaluated directly in `verify/a2_2_alias_free_scaling.py`.  The script
does not import the source constants: it reconstructs the closed formulas
from (18), checks their exact rational consequences, and independently
evaluates every integral in the moment formula by 55-digit tensor
Gauss--Legendre quadrature, including the crossing contraction.  The
largest calibration error in the committed run is below
$2\cdot10^{-56}$.  This numerical calibration is not an exact formal bridge:
the equality of the closed formulas with Mathlib integrals, and the RS
specialization supplying (18), remain unformalized.

The centered eigenvalue of the literal principal block is not $Y$.  From
(15),

\[
 C-I=\frac{Y-(\sigma-1)}\sigma,
 \qquad
 (C-I)_+^2=\frac1{\sigma^2}
       \bigl(Y-(\sigma-1)\bigr)_+^2.
\tag{22}
\]

Thus every dual polynomial in files 15--24 that is centered at $Y>0$ is
inapplicable to the honest A2.2 block.  Its threshold is
$Y>\sigma-1$.

## 4. Exact degree-four countermodel

Use the common rational atoms

\[
 y=\left(-\frac7{10},-\frac15,-\frac1{10},
          \frac3{10},\frac25\right).
\tag{23}
\]

Their Vandermonde determinant is $99/500000>0$.  For the moment vector
$m=(1,0,M_2,M_3,M_4)^{\mathsf T}$, define $w=V^{-1}m$ using

\[
V^{-1}=\begin{pmatrix}
2/275&1/15&-7/33&-40/33&100/33\\
-14/25&-47/15&74/3&-20/3&-200/3\\
7/5&5/6&-185/6&50/3&250/3\\
7/25&39/10&17/2&-30&-50\\
-7/55&-5/3&-70/33&700/33&1000/33
\end{pmatrix}.
\tag{24}
\]

Exact rational evaluation gives $w_i>1/25$ in every case:

\[
 (\sigma,\mu)\in\left\{
 (143/100,499/1000),
 (1499999/1000000,499/1000),
 (14999/10000,4999/10000),
 (19999/10000,4999/10000)
 \right\},
\tag{25}
\]

and also at the diagnostic endpoint $(2,1/2)$.  By construction,

\[
 \sum_iw_i=1,\qquad \sum_iw_iy_i^k=M_k\quad(1\leq k\leq4).
\tag{26}
\]

Moreover $1+y_i\geq3/10>0$, so the countermodel respects positivity of
$H$.  The largest atom is $2/5$, while the smallest corrected threshold
in (25) is

\[
 \frac{143}{100}-1=\frac{43}{100}>\frac25.
\tag{27}
\]

Therefore the law (23)--(26) has

\[
 \int\bigl(Y-(\sigma-1)\bigr)_+^2\,d\rho=0
\tag{28}
\]

before any rank trim.  Since the objective is nonnegative, the primal
degree-four moment infimum is exactly zero.  By weak duality, every quartic
minorant of the corrected tail has objective at most zero, and the zero
polynomial attains zero.  Hence the sharp corrected quartic dual value is
also exactly zero.  The proved stability inequality reduces only to
$\varepsilon\geq0$; it cannot force a strict density increment.

The law (23) is a moment-method countermodel, not a claim about the actual
spectral law.  It proves exactly that positivity plus the first four moments
of the A2.2 restriction do not suffice.

## 5. Recomputed constants and frozen-rung status

The same exact script recomputes the quadratic window cost from

\[
 D_\sigma=\frac{B+\sigma J_\sigma}{\sigma A^2},\qquad
 J_\sigma=2\left(\sigma\int_0^{1/\sigma}u g(u)\,du
                   +\int_{1/\sigma}^1g(u)\,du\right),
\tag{29}
\]

using the proved autocorrelation polynomial `RH/Zeta85/Window.lean:gPoly`.
Because the quartic increment is zero, A2.2 returns only the following
two-trace baselines:

| support | exact $2-D_\sigma$ |
|---:|---:|
| $143/100$ | $1893603832049143/2227707598259143$ |
| $1499999/1000000$ | $73358068490680122992976509503888283464440727/84754191966816092204313678624469283464440727$ |
| $14999/10000$ | $73327301548498049384225867010727/84720634821781091664283967010727$ |
| $19999/10000$ | $443122700696622332205411020200727/476063683898154328323469120200727$ |
| $2$, diagnostic limit | $277037179/297629080$ |

The first row is the existing R-850 value.  The other rows are method
diagnostics, not named rungs, and none reaches a frozen quartic target.  The
earlier provisional values obtained by applying stability to $H$ rather
than the literal compression $C=H/\sigma$ are withdrawn and are not
recorded as rungs.

Thus A2.2 does not discharge R1a for R-8686, R-9383, or R-9506.  Their
frozen constants and conditional/source-only statuses remain unchanged.

## 6. Reproduction

```bash
python3 -m pip install -r verify/requirements.txt
cmp -s verify/a2_2_alias_free_scaling.out \
  <(python3 verify/a2_2_alias_free_scaling.py)
```

The companion Lean file `RH/Zeta85/Discharge/AliasFallback.lean` checks the
generic rational moment reconstruction, the witness positivity and support
inequalities at every case in (25), and the cycle-3 scaling identity.  Its
finite rational countermodel is conditional on the paper-derived closed
moment definitions; it does not prove their analytic integral or RS bridge.
It introduces no hypothesis, primitive declaration, or `sorry`.
