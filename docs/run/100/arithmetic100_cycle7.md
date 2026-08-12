# Zeta-100 arithmetic, cycle 7: exact \(\mathcal K_3\) correlations and the \(q\)-orthogonality ceiling

## 0. Terminal output

This cycle takes the permitted **precise rank-three moment-class kill plus
explicit cross-\(q\) transformation** branch.  It does not claim support
beyond two.

Retain

\[
 \rho={1\over1001},\qquad L=H^\rho,\qquad
 P=H^{1/3},\qquad a\asymp P^2,                             \tag{1}
\]

and the complete sum from cycle 6,

\[
 \mathcal K_3(n,t,q;a)
 =\sum_{x,u\bmod a}^{*}
 e\!\left({nx+tu-q\overline{xu}\over a}\right).            \tag{2}
\]

The exact complete \((n,t)\)-second moment is

\[
 \boxed{\sum_{n,t\bmod a}|\mathcal K_3(n,t,q;a)|^2
       =a^2\varphi(a)^2.}                                  \tag{3}
\]

Thus the root-mean-square size is \(a=P^2\), exactly the pointwise
dimension-two square-root size used in cycle 6.  More sharply, if a
\(P\times P\) frequency box is translated through
\((\mathbb Z/a\mathbb Z)^2\), its average \(\mathcal K_3\)-energy is

\[
 \boxed{P^6H^{o(1)}}.                                      \tag{4}
\]

This is precisely

\[
 \#\{n,t\}\times|\mathcal K_3|_{\rm rms}^2
 =P^2\cdot P^4=P^6.                                       \tag{5}
\]

Consequently, no argument using only Deligne plus an \((n,t)\)-second
moment can recover any fixed power uniformly for all localized boxes.  The
degeneracy locus is explicit:

\[
                         x_1=x_2,\qquad u_1=u_2.            \tag{6}
\]

Section 2 formalizes the resulting method-class impossibility.

Outside that class, keep the formerly summed variable

\[
                         q=h\ell                           \tag{7}
\]

inside the correlation.  The full cross-\(q\) identity is

\[
 \boxed{
 \sum_{n,t\bmod a}
 \mathcal K_3(n,t,q_1;a)
 \overline{\mathcal K_3(n,t,q_2;a)}
 =a^2\varphi(a)c_a(q_1-q_2).}                              \tag{8}
\]

For prime \(a\) and distinct \(q_1,q_2\) with
\(|q_1-q_2|<a\), the off-diagonal is
\(-a^2\varphi(a)\), a factor \(a\) below the diagonal.  For general
moduli, the Ramanujan large sieve gives the same square-root-in-\(q\)
consequence up to \(a^{o(1)}\).

There are \(P\) available \(h\)'s.  Equation (8) therefore recovers exactly

\[
 \boxed{P\ \text{in energy},\qquad P^{1/2}\ \text{in amplitude}}.
                                                                    \tag{9}
\]

Even granting a lossless restriction from the complete \((n,t)\)-average
to the actual \(P\times P\) box, this improves the cycle-6 termwise output
only from

\[
                         P^4\quad\hbox{to}\quad P^{7/2}     \tag{10}
\]

per shift.  The induced MD output is

\[
                         P^7L\,H^{o(1)},                   \tag{11}
\]

against \(P^6/L\).  The exact remaining deficit is

\[
 \boxed{PL^2=H^{1/3+2\rho}
       =H^{0.335331335\ldots}}.                            \tag{12}
\]

Thus the available \(q=h\ell\) orthogonality recovers only one of the two
missing powers \(P\) in energy and none of the necessary \(L^2\).  This
is a completed correlation calculation, not a terminal unproved lemma.
Any continuation must correlate the variable modulus \(a\) or its
two-factor HB coefficient simultaneously with (8); a \(\mathcal K_3\)
moment in \(n,t,q\) alone is quantitatively exhausted.

The unconditional endpoint and accepted floor remain

\[
 \boxed{\sigma<2,\qquad
 \liminf_{T\to\infty}{N_{0,\mathrm{simple}}(T)\over N(T)}
 >0.96250068026-o(1).}                                    \tag{13}
\]

## 1. Exact Plancherel and the degeneracy locus

Write

\[
 K_q(n,t)=\mathcal K_3(n,t,q;a).                           \tag{14}
\]

Opening two copies gives

\[
\begin{aligned}
 &\sum_{n,t\bmod a}K_q(n,t)\overline{K_q(n,t)}\\
 &=
 \sum_{\substack{x_1,u_1\bmod a\\x_2,u_2\bmod a}}^{*}
 e\!\left(-{q\overline{x_1u_1}\over a}
          +{q\overline{x_2u_2}\over a}\right)
 \sum_{n\bmod a}e(n(x_1-x_2)/a)
 \sum_{t\bmod a}e(t(u_1-u_2)/a).                           \tag{15}
\end{aligned}
\]

The two complete frequency sums force

\[
                         x_1=x_2,\qquad u_1=u_2\pmod a.    \tag{16}
\]

The \(q\)-phase then cancels identically.  There are
\(\varphi(a)^2\) unit pairs and each orthogonality sum contributes \(a\),
proving (3).

Let \(\mathcal B\) be any fixed \(P\times P\) box in the frequency plane
and let \(\mathcal B+\mathbf s\) range over its \(a^2\) translations.
Every frequency pair belongs to exactly \(P^2\) translated boxes.  Hence

\[
\begin{aligned}
 {1\over a^2}\sum_{\mathbf s\bmod a}
 \sum_{(n,t)\in\mathcal B+\mathbf s}|K_q(n,t)|^2
 &={P^2\over a^2}
   \sum_{n,t\bmod a}|K_q(n,t)|^2\\
 &=P^2\varphi(a)^2
 =P^6H^{o(1)},                                             \tag{17}
\end{aligned}
\]

because \(a\asymp P^2\).  This proves (4).

In particular, some translated \(P\times P\) box has energy at least the
right side of (17).  Therefore no estimate uniform in the dyadic
localization can replace \(P^6\) by \(P^{6-\delta}\) for a fixed
\(\delta>0\) using only the complete second moment.

## 2. Impossibility for the \((n,t)\)-moment class

Define \(\mathscr C_{\mathcal K_3}^{(n,t)}\) to consist of arguments which:

1. use the complete-sum representation (2);
2. localize \(n,t\) to intervals of length \(P\);
3. use pointwise complete-sum bounds, Plancherel in \(n,t\), translations
   of the frequency box, and Cauchy/duality;
4. do not retain correlations between distinct \(q=h\ell\) or between
   distinct moduli \(a\).

The pointwise input gives \(P^2\) for each of the \(P^2\) frequency pairs,
and (17) proves that this scale is attained on average over allowed
translations.  Thus:

> **Rank-three frequency-moment barrier.**  No argument in
> \(\mathscr C_{\mathcal K_3}^{(n,t)}\) yields a fixed power saving over
> the cycle-6 \(P^4\) bound per shift.  The exact degeneracy is the
> geometric diagonal (16).

This is an impossibility theorem for the defined uniform moment class, not
a claim that the actual fixed box is extremal.

## 3. First transformation outside the class: retain \(q_1-q_2\)

Now allow two different multipliers \(q_1,q_2\).  Opening the correlation
as in (15), complete orthogonality still forces (16), but the remaining
phase is

\[
                         e\!\left(
 -{(q_1-q_2)\overline{xu}\over a}\right).                  \tag{18}
\]

For each unit \(v=xu\bmod a\), there are exactly \(\varphi(a)\) pairs
\((x,u)\) with product \(v\).  Inversion permutes the units, so

\[
\begin{aligned}
 &\sum_{n,t\bmod a}K_{q_1}(n,t)\overline{K_{q_2}(n,t)}\\
 &=a^2\varphi(a)
   \sum_{v\bmod a}^{*}
   e(-(q_1-q_2)\bar v/a)\\
 &=a^2\varphi(a)c_a(q_1-q_2),                              \tag{19}
\end{aligned}
\]

proving (8).

For prime \(a\),

\[
 c_a(0)=a-1,\qquad
 c_a(r)=-1\quad(0<|r|<a).                                 \tag{20}
\]

Therefore, for coefficients \(\gamma_h\) supported on \(P\) values and
\((\ell,a)=1\),

\[
\begin{aligned}
 &\sum_{n,t\bmod a}
 \left|\sum_{h\asymp P}\gamma_h K_{h\ell}(n,t)\right|^2\\
 &=a^2\varphi(a)
 \left(a\sum_h|\gamma_h|^2-\left|\sum_h\gamma_h\right|^2\right)\\
 &\le a^3\varphi(a)\|\gamma\|_2^2.                         \tag{21}
\end{aligned}
\]

For general \(a\), (19), the divisor formula for \(c_a\), and the
Ramanujan large sieve give

\[
 \sum_{n,t\bmod a}
 \left|\sum_h\gamma_h K_{h\ell}(n,t)\right|^2
 \ll a^{4+o(1)}\|\gamma\|_2^2,                             \tag{22}
\]

after the standard \((\ell,a)\) divisor split.  Since
\(\|\gamma\|_2^2\ll P H^{o(1)}\), (22) is smaller by a factor \(P\)
than summing \(P\) separate \(q\)-energies.

This proves the exact recovery stated in (9).

## 4. Translation to the Type-III exponent

Cycle 6's termwise rank-three estimate gave

\[
                         E_{\rm III}(\ell)\ll P^4H^{o(1)}. \tag{23}
\]

The \(P\) multipliers \(q=h\ell\) were then summed without orthogonality.
The complete correlation (22) replaces this by square-root summation,
recovering \(P^{1/2}\).  Even if one grants, favorably, that restricting
\((n,t)\) from the complete residue plane to the actual \(P\times P\)
box costs nothing, the best resulting amplitude is

\[
                         P^4P^{-1/2}
                         =P^{7/2}.                          \tag{24}
\]

Across the \(L\) selected shifts, this gives the MD scale

\[
                         L(P^{7/2})^2
                         =P^7L.                             \tag{25}
\]

The target is

\[
                         {H^2\over L}
                         ={P^6\over L}.                     \tag{26}
\]

The ratio is

\[
                         {P^7L\over P^6/L}
                         =PL^2
                         =H^{1/3+2\rho},                    \tag{27}
\]

proving (12).

The word “favorably” in (24) matters: ordinary completion of the short
\((n,t)\)-box can only worsen this exponent.  Hence (27) is an optimistic
ceiling for a method using the \(q\)-correlation (19) but no simultaneous
modulus-\(a\) cancellation.

## 5. Handoff

* Exact \((n,t)\) Plancherel:
  \(a^2\varphi(a)^2\); diagonal \(x_1=x_2,u_1=u_2\).
* Local \(P\times P\) boxes have average energy \(P^6\), so the
  \((n,t)\)-moment class is saturated.
* Exact cross-\(q\) correlation:
  \(a^2\varphi(a)c_a(q_1-q_2)\).
* The \(P\) available multipliers recover exactly \(P\) in energy,
  \(P^{1/2}\) in amplitude.
* Even under lossless localization, the MD output is \(P^7L\), leaving
  \(PL^2=H^{1/3+2\rho}\).
* No support extension is claimed; the accepted floor remains
  \(0.96250068026-o(1)\).
