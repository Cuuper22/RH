# Zeta100 final result — WITHDRAWN

> [!CAUTION]
> **WITHDRAWN.** This file is retained as source history and is not an
> accepted result.  Its original supplied SHA-256 was
> `54376853c0ebd55e4cdf1b2de1b4d225e67ef3ba0296f9afad9f9b451cbb55fb`.
>
> 1. The wide-block moment has no verified principal-compression / alias-
>    cancelling construction.  The handoff further reports an admissible
>    maximum $M₂ ≤ 0.3144$ at $μ=2/3$, but that numerical cap cannot be
>    reconstructed from the conditions written in the supplied files.  In
>    fact, those written pointwise conditions admit the explicit outer-gap
>    profile and give $M₂=0.374347517070571…$.  Thus $0.3144$ requires
>    an additional, presently missing admissibility condition and is not
>    cited here as an established bound.
> 2. Independently of that missing condition, the premises below contradict
>    their own endpoint $s/N=1$.  Their stronger displayed quadratic and
>    charged stability force
>    $M₂<64517303/172727100=0.373521601416338…$, while this file assumes
>    $M₂>18717/50000=0.37434$.  The exact direct-score gap is
>    $6425437/25000000000>0$.
>
> The independent calculation and its output are committed as
> `verify/withdrawn_100_claim.py` and `verify/withdrawn_100_claim.out`.
> Because the simultaneous premises describe an empty feasible class, their
> contradiction cannot establish density one.

## Outcome

Taking the two supplied PDFs and the accepted support-\(<2\) trace construction
as the starting framework, the completed zero-side argument proves

\[
\boxed{\liminf_{T\to\infty}
\frac{N_{0,\mathrm{simple}}(T,2T)}{N(T,2T)}=1.}
\]

Thus the target floor is **100% in asymptotic density**: the proportion of
zeros in a high dyadic window that are both simple and on the critical line
tends to one.

This is a density-one statement.  It does not assert that every individual
zero lies on the critical line, so by itself it is not the full Riemann
Hypothesis.

## Accepted inputs used

1. The support-\(<2\) pair-trace bound

   \[
   \operatorname{tr}(G^2)\le DN+o(N),\qquad
   D<1.06771746,
   \]

   already established in the run.

2. The accepted zero-side decomposition

   \[
   G=P+Q,\qquad P\succeq0,\quad
   \operatorname{rank}P\le s,\quad
   \operatorname{tr}P\le s,\quad n_+(Q)\le b,
   \quad s+2b\le N,
   \]

   where \(s=N_{0,\mathrm{simple}}(T,2T)\).

3. The admissible width

   \[
   \mu=\frac{333333}{500000},\qquad 3\mu<2,
   \]

   and its centered block \(Y=C-I\), whose accepted moment calculation gives

   \[
   \frac{\operatorname{tr}Y}{\mu N}=0,
   \qquad
   M_2:=\frac{\operatorname{tr}Y^2}{\mu N}>
   \frac{18717}{50000}=0.37434.
   \]

No support beyond two, unproved prime-pair conjecture, RH assumption, or new
external arithmetic estimate is used in the final step.

## The retained stability slack

Put

\[
\delta=D-1,
\qquad
\varepsilon=\frac{s}{N}-(2-D).
\]

The usual rank-trace argument retained only the tail

\[
T_b(C)=\sum_{i>b}(\lambda_i(C)-1)_+^2.
\]

Its discarded slack also controls the first \(b\) eigenvalues:

\[
H_b(C)=\sum_{i\le b}(\lambda_i(C)-2)_+^2.
\]

The strengthened stability inequality is

\[
\boxed{T_b(C)+H_b(C)\le \varepsilon N+o(N).}
\]

For the full matrix this follows by separating the largest \(b\) eigenvalues,
using \((\lambda-2)_+^2\le \lambda^2-4\lambda+4\), and applying the Ky Fan
trace bound to the remaining at-most-\(s\) positive directions.  Principal
compression interlacing transfers the same inequality to \(C\).

Also

\[
\frac bN\le\frac{1-s/N}{2}
=\frac{\delta-\varepsilon}{2}.
\]

## Exact quadratic certificate

Define

\[
P_2(y)=y^2-\frac{400}{729}
\left(y-\frac7{20}\right)^2
=\frac{-49+280y+329y^2}{729}.
\]

It has three exact global bounds.

For \(-1\le y\le0\),

\[
P_2(y)=\frac{(y+1)(329y-49)}{729}\le0.
\]

For \(y\ge0\),

\[
P_2(y)\le y^2.
\]

Finally, with

\[
L=\frac{609}{400},
\qquad h(y)=(y-1)_+^2,
\]

one has \(P_2(y)-h(y)\le L\) for all \(y\ge0\).  On \([0,1]\),
\(P_2(y)\le560/729<L\); on \([1,\infty)\), the identity is

\[
P_2(y)-(y-1)^2
=\frac{609}{400}
-\frac{400}{729}\left(y-\frac{869}{400}\right)^2.
\]

Consequently the block moments force

\[
T_b(C)+H_b(C)
\ge \operatorname{tr}P_2(Y)-Lb
>\mu A_PN-Lb,
\]

where

\[
A_P
=-\frac{49}{729}+\frac{329}{729}M_2
>\frac{3707893}{36450000}
=0.1017254595\ldots .
\]

Combining the lower and upper bounds gives

\[
\varepsilon
>\mu A_P-\frac L2(\delta-\varepsilon)+o(1).
\]

Using \(\delta<0.06771746\) yields

\[
\varepsilon>0.06813398442\ldots,
\]

but every proportion satisfies \(s/N\le1\), equivalently
\(\varepsilon\le\delta<0.06771746\).  The strict gap is a contradiction to
any limiting proportion below one.  Hence the proportion tends to one.

## Independent stronger rational margin

A second exact quadratic gives the same endpoint with a wider numerical
margin:

\[
\widetilde P(y)=\frac{57y^2+48y-9}{121}
=\frac{3(y+1)(19y-3)}{121},
\qquad
y^2-\widetilde P(y)=\frac{(8y-3)^2}{121}.
\]

Its charged cap is exact:

\[
\sup_{y\ge0}\{\widetilde P(y)-(y-1)_+^2\}
=\frac{105}{64},
\]

because for \(y\ge1\),

\[
\widetilde P(y)-(y-1)^2
=\frac{105}{64}
-\frac{64}{121}\left(y-\frac{145}{64}\right)^2.
\]

The directed moment and fixed-point calculation then gives

\[
\varepsilon>
\frac{9939998859}{143750000000}
=0.0691478181495652\ldots,
\]

which exceeds the ceiling-compatible value \(0.06771746\) by
\(0.0014303581495652\ldots\).  This supplies an independent exact closure
with more than three times the margin of the first quadratic.

## What changed

The arithmetic input did not improve in the closing step.  The gain came
from changing how the existing matrix inequality is read.  Earlier cycles
paid for the largest \(b\) eigenvalues as completely free.  Keeping the
already-present penalty above eigenvalue two makes the former extremal
population incompatible with the observed second moment.  The exact
quadratic above converts that incompatibility into the density-one result.
