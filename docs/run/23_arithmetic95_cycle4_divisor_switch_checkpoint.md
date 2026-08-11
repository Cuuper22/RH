# Zeta-95 arithmetic, cycle 4: divisor-switch checkpoint (superseded)

## Status

This arithmetic branch is **superseded by the terminal zero-side
certificate**: the latter already exceeds 95 percent (reported value
\(95.06594\%\)) using the previously proved connected support
\(\sigma<2\).  No extension of prime-side support is now needed.

The completed divisor-switch calculation is recorded below so that the work
is not lost.  It also identifies why the naive switch to a modulus
\(c_0\le L^2\) is not an exact identity on the hard prime-modulus block.

## 1. Exact factorization retained from the BP four-cycle

Cycle 3 obtained, for the Kloosterman multiplier \(a\),

\[
 \mathscr D_a=(P-aQ)(P-aQ+4a^2),
 \qquad
 P=h_1h_2h_3h_4,
 \quad Q=(h_1+h_3)(h_2+h_4).                               \tag{1}
\]

Put

\[
 U=P-aQ,qquad \tau=U+2a^2.                                \tag{2}
\]

Then the discriminant has the exact difference-of-squares form

\[
                 \boxed{\mathscr D_a=\tau^2-4a^4.}          \tag{3}
\]

At the mixed 95-percent target,

\[
 a\asymp L=H^\rho,qquad
 \rho=0.1246023080837601868\ldots,                          \tag{4}
\]

so the determinant scale in (3) is

\[
 a^2\asymp L^2=H^{0.249204616167520\ldots},qquad
 a^4\asymp L^4=H^{0.498409232335041\ldots}.                \tag{5}

Thus \(L^2\) is indeed the optimal prospective switch cutoff: it is the
square-root divisor scale of the small determinant \(4a^4\).

## 2. Executing the root/divisor switch

For an odd prime terminal modulus \(q\asymp H\), expand the quadratic
character by counting square roots:

\[
 1+\left(\frac{\mathscr D_a}{q}\right)
 =\#\{z\pmod q:z^2\equiv\tau^2-4a^4\pmod q\}.              \tag{6}

For each root set

\[
                       s=z-\tau,qquad t=z+\tau.             \tag{7}

Then (6) is equivalent to the exact hyperbola congruence

\[
                         \boxed{st\equiv-4a^4\pmod q.}      \tag{8}

\]

Choose centered representatives \(|s|,|t|\le q/2\).  The congruence becomes
the integer divisor-switch equation

\[
                         \boxed{st+4a^4=nq}                 \tag{9}

\]

with \(|n|\ll q\).  This cleanly separates two cases.

### Zero winding

If \(n=0\), then

\[
                         st=-4a^4.                           \tag{10}

\]

Pair complementary divisors so that \(|s|\le2a^2\).  Hence the active
divisor is at most

\[
                         |s|\le2L^2,                         \tag{11}

\]

exactly the desired conductor-lowering scale.  This is a genuine small-modulus
piece.  Its divisor multiplicity is \(\tau(4a^4)=H^{o(1)}\), and the
\(s,t\) zero modes coincide with the already separated BP diagonal terms.

### Nonzero winding

If \(n\ne0\), equation (9) is

\[
                         st=-4a^4+nq.                        \tag{12}

\]

The right side is no longer supported on divisors of \(4a^4\).  In
particular, neither \(s\) nor \(t\) is forced below \(L^2\); for generic
\(n\) both have admissible ranges up to \(q\).  Solving instead for the old
modulus gives

\[
                         q=\frac{st+4a^4}{n},                \tag{13}

\]

but the complementary variable \(n\) also has length \(q^{1+o(1)}\).  Thus
(13) has merely exchanged one long modulus variable for another.

The nonzero-winding terms are not exceptional: centered pairs
\((s,t)\pmod q)\) occupy \(q^{2+o(1)}\) possibilities before (8), and their
winding numbers range through \(|n|\ll q\).  Discarding them would discard
the full off-diagonal character sum.

## 3. Optimized cutoff and method-class obstruction

Define the **direct determinant divisor-switch class** to consist of
arguments which:

1. replace the character in (6) by (8);
2. lift (8) to (9);
3. select a divisor of the fixed determinant \(4a^4\) as the new active
   modulus; and
4. apply complete character orthogonality on that divisor.

For a cutoff \(C\), the zero-winding contribution permits

\[
                    c_0\le\min(C,4a^4/C).                   \tag{14}

\]

The maximum of the right side is attained at

\[
                    \boxed{C=2a^2\asymp L^2},               \tag{15}

\]

giving the numerical exponent in (5).  No other cutoff improves it.

However, (14) is an identity only for \(n=0\).  For every \(n\ne0\), the
integer to be factored is \(-4a^4+nq\), which depends on the original prime
modulus and can have no divisor below \(L^2\) other than 1.  Since a prime
\(q\asymp H\) has no proper modulus factor, complete character orthogonality
still has conductor \(q\) on this family.

Therefore:

> **Direct-switch barrier.**  Uniformly over prime terminal moduli
> \(q\asymp H\), no argument in the direct determinant divisor-switch class
> can replace the full discriminant character by characters of conductor
> \(c_0\le L^2\).  It lowers the conductor only on the zero-winding/diagonal
> subfamily; every nonzero winding retains a long complementary variable.

This is a statement about the defined switch class, not an impossibility
result for MD9.

## 4. First calculation outside the direct-switch class

The nonzero winding in (12) must be averaged rather than factored termwise.
The first q-van-der-Corput object is obtained by shifting
\(n\mapsto n+r\) before taking absolute values.  From (12), two copies obey

\[
 \begin{aligned}
 s_1t_1+4a^4&=nq,\\
 s_2t_2+4a^4&=(n+r)q,
 \end{aligned}                                              \tag{16}

\]

and subtraction removes the small determinant exactly:

\[
                         \boxed{s_2t_2-s_1t_1=r q.}          \tag{17}

\]

This is the correct first object outside the direct-switch class: the
coefficient \(4a^4\), and hence the artificial divisor cutoff, disappears;
the remaining task is a bilinear determinant correlation averaged over the
short differencing parameter \(r\).  A successful continuation would choose
\(R\) and prove a power saving for

\[
 \sum_{1\le |r|\le R}
 \sum_{s_2t_2-s_1t_1=rq}
 \mathcal A_{a,\mathbf h}(s_1,t_1)
 \overline{\mathcal A_{a,\mathbf h}(s_2,t_2)},              \tag{18}

\]

while retaining the signed \(a\asymp L\) average.  Ordinary Cauchy alone
costs \((q/R+R)^{1/2}\); no claimed saving for (18) is made here.

This branch is not pursued further because the zero-side certificate has
already crossed the requested 95-percent threshold at the established
support-two arithmetic input.

## 5. Final handoff

* Optimal determinant switch scale: \(c_0\asymp L^2\), exponent
  \(0.249204616167520\ldots\) relative to \(H\).
* The switch is exact and useful only for zero winding \(n=0\).
* Nonzero winding gives \(st+4a^4=nq\) and retains a long complementary
  variable; prime \(q\) prevents uniform conductor lowering.
* First outside-class object: the q-van-der-Corput determinant correlation
  \(s_2t_2-s_1t_1=rq\) in (17)--(18).
* Arithmetic support remains the already proved \(\sigma<2\).
* This is sufficient because the terminal certificate now gives more than
  95 percent at that support; the reported combined value is \(95.06594\%\).
