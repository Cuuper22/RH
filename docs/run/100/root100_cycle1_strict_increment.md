> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Root 100, cycle 1: a strict rational-dual increment

## Terminal outcome

This cycle gives a strict unconditional improvement of the inherited floor:

\[
\boxed{
\frac{N_{0,\mathrm{simple}}(T,2T)}{N(T,2T)}
\ge 0.9506383222288020-o(1).}
\]

The preceding certified value was `0.95063832187565`, so the gain is

\[
3.53152015949\times10^{-10}.
\]

No new arithmetic input is used.  The improvement comes from replacing the
rounded quartic dual in `certificate95_cycle2.md` by a closer rational point
on the same exact three-contact dual family.

## Accepted data

Keep the strict parameters

\[
\sigma=1.9999,\qquad \mu=\frac{4999}{10000},\qquad p=\frac{83}{100},
\]

the directed pair-cost bound

\[
D\le \frac{106772567}{10^8},
\]

and the exact centered moments

\[
M_2=\frac{682156116889}{2490000000000},
\]

\[
M_3=-\frac{8293346012887}{68890000000000},
\]

\[
M_4=
\frac{434598816917989781038321}
{2144201250000000000000000}.
\]

All of these are already discharged by the strict support-below-two
arithmetic theorem.

## The new exact dual

Take rational contacts

\[
a=-\frac{908129}{10^6},\qquad
c=\frac{22603}{10^5},\qquad
t=\frac{967751}{10^6}.
\]

Define the quartic \(P\) and cap \(L\) uniquely by

\[
P(a)=P'(a)=0,\quad
P(c)=c^2,\quad P'(c)=2c,\quad
P(t)=L,\quad P'(t)=0.
\]

Since the interpolation system is rational, this defines an exact rational
certificate.  Its directed decimal display is

\[
\begin{aligned}
P(y)={}&-0.03081846311670
 +0.26258222506340y
 +0.47276213516012y^2\\
&-0.07861485344423y^3
 -0.26390110847734y^4,\\
L={}&0.36333505651134.
\end{aligned}
\]

The three global dual inequalities follow from exact polynomial division:

\[
\begin{aligned}
P(y)&=(y-a)^2Q_-(y),\\
y^2-P(y)&=(y-c)^2Q_2(y),\\
L-P(y)&=(y-t)^2Q_L(y).
\end{aligned}
\]

In ascending coefficient order, directed rational evaluation gives

\[
Q_-=(-0.03736937\ldots,\ 0.40069764\ldots,\ -0.26390110\ldots),
\]

with discriminant \(0.12111132\ldots>0\).  Its root product and root sum are
both positive, hence both roots are positive and \(Q_-(y)<0\) for
\(y\le0\).  The other two quadratics have positive leading coefficients and
discriminants

\[
-0.59759626\ldots<0,
\qquad
-0.09687457\ldots<0.
\]

Therefore, globally,

\[
P(y)\le0\ (y\le0),\qquad
P(y)\le y^2\ (y\ge0),\qquad
P(y)\le L\ (y\ge0).
\]

## Exact fixed-point output

Put

\[
A_P=P_0+P_2M_2+P_3M_3+P_4M_4.
\]

Exact rational substitution gives

\[
A_P=0.0546737471895348295\ldots
\]

and the accepted trimmed-tail fixed point gives

\[
\varepsilon\ge
\frac{\mu A_P-\frac L2(D-1)}{1-L/2}
=0.0183639922288020159\ldots .
\]

Consequently

\[
2-D+\varepsilon
=\frac{
17998950914869746631079268517946872624174076880371
}{
18933542330452899601081679136419633361655648000000
}
\]

\[
=0.95063832222880201594948\ldots .
\]

Cross-multiplication against `0.95063832187565` is strictly positive, with
the margin stated above.  This completes the cycle under the unconditional
support-`1.9999` inputs already proved in the inherited branch.

## Next constructive attack

This tiny gain confirms that the rounded dual was essentially locally
optimal for the fixed top-hat.  The next cycle therefore changes the block
profile itself (and, independently, the moment order), rather than spending
more time tuning these three contacts.