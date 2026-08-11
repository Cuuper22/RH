# R1a audit: power-complementary nesting

## Verdict

**Not verified.**  The two archived runs do not contain a construction that
implies the claimed cyclic block symbols.  The only relevant construction is
§6 of `docs/run/03_certificate_cycle3.md`, equations (26)--(28).  It assumes
the scalar identity

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
conditional on a missing R1a construction.  This finding does not affect the
separately proved stability inequality.

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
- no cyclic-symbol or paraunitary construction in either `Rh.zip` or
  `95maybe.zip`.

There is no file numbered 24 in either supplied archive.  Thus a claimed
file-15/file-24 dependency cannot be checked beyond the file-15 side from the
available artifacts.

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

## What would be sufficient

One of the following must be constructed and checked.

1. **Alias-free windows.**  For every \(j\) and every \(m\ne0\),

   \[
    \varphi_j(u)\overline{\varphi_j(u-mL_j)}=0
    \quad\text{for almost every }u.
   \tag{6}
   \]

   Together with (1), this proves equation (28) of cycle 3.  It does not by
   itself prove that the selected block is orthonormal or has moments (2).

2. **A paraunitary multi-window system.**  For every nonzero alias class,
   the full cyclic symbol must vanish:

   \[
    \sum_{j:\,mL_j=r}
      e^{i(\tau'-T)r}
      \varphi_j(u)\overline{\varphi_j(u-r)}=0,
   \tag{7}
   \]

   with the appropriate common-lattice form when the \(L_j\) are
   commensurable.  Equation (1) is only the zero-alias row of this system.

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
all vanish at an internal boundary and cannot satisfy (1) there.  Overlapping
ramps can satisfy (1), but they reintroduce precisely the nonzero terms in
(4).  A sign/phase construction proving (7), followed by a derivation of the
distinguished block symbol and its four moments, is the missing dependency.

## Consequence for the program

The R1a premise is presently a gap, not a contradiction in the stability or
trimmed-moment algebra.  The nested-quartic numerical rungs must remain
conditional until an explicit alias-cancelling construction supplies both:

- the exact or asymptotically controlled principal compression; and
- the cyclic block symbol from which the moments (2) follow.
