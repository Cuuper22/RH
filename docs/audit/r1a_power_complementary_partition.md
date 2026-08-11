# R1a audit: power-complementary nesting

## Verdict

**Not verified.**  The three ingested research archives/batches do not contain
a construction that implies the claimed cyclic block symbols.  The first
relevant construction is §6 of `docs/run/03_certificate_cycle3.md`, equations
(26)--(28).  It assumes the scalar identity

\[
  \sum_j \varphi_j(u)^2=v(u),
\tag{1}
\]

and then asserts that the \(j\)-th modulation grid contributes only
\(L\widehat{\varphi_j^2}(\tau-\tau')\).  That conclusion needs additional
alias-cancellation identities which do not follow from (1).

The first use of the missing conclusion is lines 20--31 of
`15_root95_cycle2_nested_quartic_86p7170.md`: it treats the
\(\mu=499/1000\) block as an exact principal compression and assigns it the
centered moments

\[
 \mathbb E Z=\mathbb E Z^3=0,\qquad
 \mathbb E Z^2=\frac13,\qquad
 \mathbb E Z^4=\frac4{15}.
\tag{2}
\]

Consequently (2), and every certificate downstream of it, remains
conditional on a missing R1a construction.  The A2.1 paraunitary proposal is
now finished and killed for the exact finite common-lattice, critical-channel
class used by cycle 3: a fiber-rank obstruction below shows that no choice of
real signs or complex phases can retain the claimed distinguished block.
The A2.2 one-window-per-interval fallback is also finished and killed in
docs/audit/r1a_alias_free_fallback.md: the global hat normalization inserts
an omitted factor \(1/\sigma\), and the honest degree-four moment problem has
value zero after that correction.  These results do not exclude an
oversampled or noncommensurable system with a newly derived coefficient
count and trace budget, and they do not affect the separately proved
stability inequality.

## Archive inventory

The exact case-insensitive search

```text
Gabor | power-complementary | Princen | Bradley | cyclic | block symbol
```

finds:

- the construction claim in `03_certificate_cycle3.md`;
- the dependency claim in `15_root95_cycle2_nested_quartic_86p7170.md`;
- the warning in `09_certificate_cycle5_adversary_constraints.md` that an
  accepted coupling identity is absent; and
- no cyclic-symbol or paraunitary construction in `Rh.zip`, `95maybe.zip`, or
  the terminal-95 batch supplied through Drive.

The terminal batch does contain
`24_TERMINAL_certificate95_cycle2_95p063832.md`.  Its equation (30) adds a
pointwise allocation test for the distinguished symbol, but supplies no
alias-cancelling or paraunitary construction.  Thus both sides of the
file-15/file-24 dependency have now been checked; neither closes R1a.

## Poisson calculation

Use the Fourier convention

\[
 \widehat f(\tau)=\int_{\mathbb R}f(u)e^{i\tau u}\,du
\]

and the functions asserted in cycle 3,

\[
 f_{j,k}(u)=\left(\frac{L}{L_j}\right)^{1/2}
 \varphi_j(u)e^{-i(T+2\pi k/L_j)u}.
\tag{3}
\]

Applying the Dirac-comb form of Poisson summation gives

\[
\begin{aligned}
 &\sum_{k\in\mathbb Z}
   \widehat f_{j,k}(\tau)\overline{\widehat f_{j,k}(\tau')}\\
 &\quad =L\sum_{m\in\mathbb Z}
 e^{i(\tau'-T)mL_j}
 \int_{\mathbb R}
 \varphi_j(u)\overline{\varphi_j(u-mL_j)}
 e^{i(\tau-\tau')u}\,du .
\tag{4}
\end{aligned}
\]

The \(m=0\) term is

\[
 L\widehat{|\varphi_j|^2}(\tau-\tau'),
\tag{5}
\]

but (4) also has all nonzero alias terms.  Summing (5) over \(j\) and using
(1) reconstructs \(L\widehat v(\tau-\tau')\); (1) says nothing about the
terms with \(m\ne0\).

For comparison, Lemma 2.2 of the accepted base paper kills the nonzero
terms because a single window is supported in an interval of length equal to
its modulation period.  Remark 7.1(i) of that paper explicitly says that a
Princen--Bradley power-complementary window instead introduces an additional
aliasing term.  It does not supply the multi-block cancellation asserted in
cycle 3.

## A2.1 finish-or-kill: the common-lattice rank obstruction

The paraunitary equations are not impossible merely because the zero-alias
terms are nonnegative.  For example, on two cells a two-channel
Princen--Bradley pair can use

\[
 \bigl(\varphi_1(x),\varphi_2(x)\bigr)
   =\sqrt{w(x)}(\cos\theta,\sin\theta),
\]

\[
 \bigl(\varphi_1(x+a),\varphi_2(x+a)\bigr)
   =\sqrt{w(x+a)}(-\sin\theta,\cos\theta).
\tag{9}
\]

The cross inner product vanishes.  The obstruction is instead dimension:
(9) consumes two channels for two occupied cells.

Here is the exact method class.  Let the full physical support have length
\(S=Na\), let every modulation period be commensurable,
\(L_j=n_ja\), and retain the coefficient-count identity asserted after
cycle-3 equation (28),

\[
 \sum_jL_j=S,
 \qquad\text{equivalently}\qquad
 \sum_jn_j=N.
\tag{10}
\]

For almost every \(x\in[0,a)\), put \(u_q=x+qa\), \(0\le q<N\).
For each residue class \(0\le r<n_j\), define a vector in
\(\mathbb C^N\) by

\[
 g_{j,r}(x)_q
 =\mathbf1_{q\equiv r\pmod {n_j}}\,
   \omega_{j,q}\varphi_j(u_q),
\tag{11}
\]

where the unit phases \(\omega_{j,q}\) absorb the phase in (4).  The
common-lattice Poisson fiber is therefore

\[
 A_x=\sum_j A_{j,x},
 \qquad
 A_{j,x}=\sum_{r<n_j}g_{j,r}(x)g_{j,r}(x)^*,
 \qquad
 \operatorname{rank}A_{j,x}\le n_j.
\tag{12}
\]

The zero-alias identity (1) together with all nonzero equations (7) says
exactly

\[
 A_x=\operatorname{diag}
   \bigl(v(u_0),\ldots,v(u_{N-1})\bigr).
\tag{13}
\]

Suppose the distinguished window has period \(L_0=n_0a\), is supported in
an interval of length at most \(L_0\), and has energy
\(r=|\varphi_0|^2\).  Each residue class modulo \(n_0\) then contains at
most one occupied cell, apart from null boundaries, so its fiber has no
nonzero aliases and

\[
 A_{0,x}=\operatorname{diag}
   \bigl(r(u_0),\ldots,r(u_{N-1})\bigr).
\tag{14}
\]

If the residual \(w=v-r\) is strictly positive almost everywhere on the
full support, (13)--(14) require the complement to have rank \(N\):

\[
 \operatorname{rank}(A_x-A_{0,x})
 =\operatorname{rank}\operatorname{diag}(w(u_0),\ldots,w(u_{N-1}))
 =N.
\tag{15}
\]

But subadditivity of rank and (10)--(12) give

\[
 \operatorname{rank}(A_x-A_{0,x})
 \le\sum_{j>0}n_j=N-n_0<N,
\tag{16}
\]

a contradiction.  This proof permits arbitrary real signs and complex
phases; it kills every finite common-lattice PB/TDAC system with the scalar
grids (27), the critical count (10), an alias-free distinguished block, and
a full-support positive residual.  It is not a theorem about oversampled
systems, noncommensurable periods, or a different modulation architecture.

### Application to the claimed blocks

This subsection isolates the A2.1 alias equation by provisionally granting
the source's favorable allocation convention \(r\leq V_\sigma\).  The A2.2
audit subsequently shows that this convention is itself mis-scaled in the
base paper's hat units: a mean-one literal compression requires
\(\sigma r\leq V_\sigma\).  Thus the terminal blocks fail normalization
before the rank obstruction is needed.  The argument below remains a valid
independent statement: even under the more favorable source convention, no
critical-count common-lattice PB/TDAC completion exists.

For terminal file 24, equations (28)--(29) construct
\(V_\sigma(x)=\sigma u_\sigma(x)/M\).  Solving the displayed continuity
system gives, with \(b=(2-\sigma)/2\) and \(d=b-1/2\),

\[
\begin{aligned}
 \Delta&=\sqrt3\cos d\cos(\sqrt3d)+\sin d\sin(\sqrt3d),\\
 A&=\frac{\sqrt3\cos(\sqrt2b)\cos(\sqrt3d)
       +\sqrt2\sin(\sqrt2b)\sin(\sqrt3d)}{\Delta},\\
 B&=\frac{\cos(\sqrt2b)\sin d
       -\sqrt2\cos d\sin(\sqrt2b)}{\Delta},
\end{aligned}
\tag{17}
\]

and direct integration gives

\[
\begin{aligned}
 \frac M2={}&\frac{\sin(\sqrt2b)}{\sqrt2}
 +A\left(\sin\frac{\sigma-1}{2}-\sin d\right)\\
 &-\frac B{\sqrt3}
 \left(\cos\frac{\sqrt3(\sigma-1)}2-\cos(\sqrt3d)\right).
\end{aligned}
\tag{18}
\]

`verify/a2_1_tdac_rank.py` evaluates (17)--(18) using exact rational
interval arithmetic: integer-square-root enclosures for \(\sqrt2,\sqrt3\)
and rational Taylor remainders for every sine and cosine.  Its independent
60/100-digit `mpmath` calculation is only a calibration.  The committed
output certifies:

- for R-9506,
  \(\sigma=19999/10000\), \(\mu=4999/10000\), \(p=83/100\), and
  \(\mu p/2=414917/2000000\),
  \[
    V_\sigma(\mu p/2)-1/p>1/1000;
  \]
- for R-8686,
  \(\sigma=14999/10000\), \(\mu=4999/10000\), \(p=89/100\), and
  \(\mu p/2=444911/2000000\),
  \[
    V_\sigma(\mu p/2)-1/p>1/1000;
  \]
- for the later Euler-profile reinterpretation of file 15's flat block,
  \(\sigma=1499999/1000000\), \(\mu=499/1000\), \(p=1\),
  \[
    V_\sigma(\mu/2)-1>1/10.
  \]

The same certificate gives \(A>0\), \(B<0\), \(M>0\), and a positive
endpoint value in all three cases.  On the outer branch, with
\(t=x-1/2\),

\[
 u'(x)=-A\sin t+\sqrt3B\cos(\sqrt3t).
\tag{19}
\]

Throughout the branch \(|t|<1/2\), so \(\cos t\) and
\(\cos(\sqrt3t)\) are positive and \(\sin(\sqrt3t)\) has the sign of
\(t\).  For \(t\ge0\), both terms in (19) are nonpositive and the second
is strict.  For \(t<0\),

\[
 u''(x)=-A\cos t-3B\sin(\sqrt3t)<0,
\]

and continuity gives \(u'(b)=-\sqrt2\sin(\sqrt2b)<0\).  Hence
\(V_\sigma\) decreases on the positive half-support and stays positive.
The terminal top-hat

\[
 r_{\mu,p}(x)=p^{-1}\mathbf1_{|x|\le\mu p/2}
\tag{20}
\]

therefore has \(V_\sigma-r_{\mu,p}>0\) everywhere except irrelevant taper
boundaries.  On the fine rational lattices the rank requirements are

\[
\begin{array}{c|c|c|c}
 &N&n_0&\sum_{j>0}n_j\\ \hline
\text{R-9506}&19999&4999&15000\\
\text{R-8686}&14999&4999&10000\\
\text{file 15}&1499999&499000&1000999.
\end{array}
\tag{21}
\]

Thus (15)--(16) contradict every one of these common-lattice allocations.
A sufficiently narrow smooth taper does not help: it only lowers the
distinguished energy and leaves the residual positive.

For the actual quadratic profile (8), the hat-unit normalization must be
included.  Since

\[
 a=\int_{-1/2}^{1/2}v(s)\,ds=\frac{1031}{1200},
 \qquad V=v/a,
\]

the edge residual of the claimed flat block at \(\mu=499/1000\) is the
positive rational

\[
 V(\mu/2)-1=\frac{42756493}{1031000000}>0.
\tag{22}
\]

Monotonicity of the quadratic makes the residual positive throughout the
central cell, and outside that cell the distinguished symbol is zero while
\(V>0\).  Thus the same rank contradiction applies directly to the original
file-15 profile.  Its normalized central average is, correctly,

\[
 \frac1\mu\int_{-\mu/2}^{\mu/2}V(s)\,ds
 =\frac{1157918831}{1031000000}>1.
\tag{23}
\]

Consequently there is **no** zero-alias average obstruction; the earlier
unnormalized comparison would be false.  The obstruction is precisely the
full paraunitary rank budget (15)--(16).

## What remains outside the two killed classes

The originally requested fallback no longer survives.

1. **A2.2 is killed at normalization.**  Requiring, for every \(j\) and
   every \(m\ne0\),

   \[
    \varphi_j(u)\overline{\varphi_j(u-mL_j)}=0
    \quad\text{for almost every }u.
   \tag{6}
   \]

   does prove the alias-free form of cycle-3 equation (28).  The exact
   interval construction and its taper loss are given in the A2.2 audit.
   However, with \(L=\sigma\ell\), global normalization by \(aL^2\), and
   periods summing to \(L\), its literal block symbol is the intrinsic
   restriction divided by \(\sigma\).  A mean-one block requires the correct
   cap \(\sigma r\leq V_\sigma\), which fails already because
   \(\sup V_\sigma=1200/1031<143/100\leq\sigma\).  For the honest block
   \(C=H/\sigma\), a rational five-atom law matching the paper-derived
   closed moments makes the corrected degree-four stability tail zero.
   Thus this route yields no replacement quartic rung.

2. **A paraunitary multi-window system outside both killed classes.**  For
   every nonzero alias class,
   the full cyclic symbol must vanish:

   \[
    \sum_{j:\,mL_j=r}
      e^{i(\tau'-T)r}
      \varphi_j(u)\overline{\varphi_j(u-r)}=0,
   \tag{7}
   \]

   with the appropriate common-lattice form when the \(L_j\) are
   commensurable.  Equation (1) is only the zero-alias row of this system.
   By (16) and the A2.2 scaling calculation, it must change the cycle-3 count
   and rederive the zero-side trace normalization, make the residual vanish
   on at least \(n_0\) fibers while satisfying \(\sigma r\leq V_\sigma\), or
   use a separately derived noncommensurable modulation system.

In addition, the distinguished block needs its own Gram symbol to be the
claimed mean-one flat symbol (or a proved asymptotic replacement).  A smooth
partition subordinate to disjoint intervals does not automatically do this.
For the profile used in the run,

\[
 v(s)=1-\frac{169}{100}s^2\quad (|s|\le\tfrac12),
 \qquad \min v=\frac{231}{400}>0.
\tag{8}
\]

Thus smooth windows supported in a genuinely disjoint interval partition
all vanish at an internal boundary and cannot satisfy (1) pointwise there.
The boundaries are null for the Gram integral; the A2.2 audit gives the
explicit absolute normalization loss \(10w/(\sigma\ell)\), relative
full-energy loss \(10w/(A\sigma\ell)\), and intrinsic block-mean loss
\(2w/(A\mu\ell)\).
Overlapping ramps can satisfy (1), but they reintroduce precisely the
nonzero terms in (4).  A construction outside both killed classes, with a
new coefficient count and trace normalization proved from its actual grids,
is the remaining R1a dependency.

## Consequence for the program

The contradictions indict the claimed construction and normalization
premises, not the stability algebra.  A2.1 and A2.2 are both closed as exact
method classes; R1a remains open only through an architecture outside them.
The nested-quartic numerical rungs must remain conditional until a valid
construction supplies both:

- the exact or asymptotically controlled principal compression; and
- the cyclic block symbol from which the moments (2) follow.
