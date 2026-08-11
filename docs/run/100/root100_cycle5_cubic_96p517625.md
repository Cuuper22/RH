# Root 100, cycle 5: sharpen the wide cubic dual

## Outcome

Keep every arithmetic and block input from `certificate100_cycle3.md`
unchanged:

\[
\sigma_1=1.99999,qquad D<1.06771821,qquad
\mu=0.6666,qquad 3\mu=1.9998<2,
\]

and keep its outer-cap/central-gap symbol and directed moments

\[
M_2>0.37432,qquad M_3<-0.06711.
\]

Changing only the exact rational cubic dual gives the strict unconditional
improvement

\[
\boxed{
\frac{N_{0,\mathrm{simple}}(T,2T)}{N(T,2T)}
>0.96517625-o(1).}
\]

This raises the preceding cubic checkpoint by more than
\(5.54\times10^{-5}\), with no new analytic input.

## 1. Exact rational cubic

Choose

\[
c=\frac{259}{1000},\qquad t=\frac{1823}{1000}.
\]

Let \(P(y)=p_0+p_1y+p_2y^2+p_3y^3\) be determined over the
rationals by

\[
P(-1)=0,qquad P(c)=c^2,qquad P'(c)=2c,qquad P'(t)=0,
\]

and put \(L=P(t)\).  The exact coefficients are

\[
\begin{aligned}
p_0&=-\frac{66734312579529}{1276719342260000},\\
p_1&= \frac{502619626742471}{1276719342260000},\\
p_2&= \frac{189991065161}{638359671130},\\
p_3&=-\frac{9468590450}{63835967113},\\
L&=\frac{617040463458087}{816316715000000}.
\end{aligned}
\]

For orientation,

\[
\begin{aligned}
P(y)={}&-0.05227015082+0.39368059221y
 +0.29762385338y^2-0.14832688966y^3,\\
L={}&0.75588365658.
\end{aligned}
\]

## 2. Global signs on the actual spectral domain

The compression is positive semidefinite, so for \(Y=C-I\) its spectrum
lies in \([-1,\infty)\).  On that domain the required inequalities are
exact.

First,

\[
P(y)=(y+1)\{p_0+(p_1-p_0)y+p_3y^2\}.
\]

For \(-1\le y\le0\), all three displayed terms inside braces are
nonpositive, and the constant term is strictly negative.  Hence
\(P(y)\le0\).

Next, with

\[
k=\frac{9468590450}{63835967113}>0,
\quad d=\frac{994831809}{189371809}>0,
\quad e=\frac{2097753279}{1279539250}>0,
\]

exact polynomial division gives

\[
 y^2-P(y)=k(y-c)^2(y+d),
\]

\[
 L-P(y)=k(y-t)^2(y+e).
\]

Both right sides are nonnegative for \(y\ge0\).  Therefore

\[
P(y)\le0\ (-1\le y\le0),\qquad
P(y)\le y^2\ (y\ge0),\qquad
P(y)\le L\ (y\ge0).
\]

## 3. Directed score and fixed point

Since \(p_2>0>p_3\), the inherited one-sided moment bounds give

\[
\begin{aligned}
A_P&=p_0+p_2M_2+p_3M_3\\
&>p_0+0.37432p_2-0.06711p_3\\
&>0.0690906275363.
\end{aligned}
\]

Write

\[
\frac{s}{N}=2-D+\varepsilon,
\qquad
\frac bN\le\frac{D-1-\varepsilon}{2}.
\]

The same one-trim stability argument as in the cubic theorem gives

\[
\varepsilon\ge
\mu A_P-\frac L2(D-1-\varepsilon),
\]

and hence

\[
\varepsilon>
\frac{0.6666(0.0690906275363)
-\frac L2(1.06771821-1)}{1-L/2}
>0.03289446092.
\]

Consequently

\[
\frac{s}{N}>
2-1.06771821+0.03289446092
=0.96517625092,
\]

which proves the displayed checkpoint.

## Handoff

The cubic dual has now been tightened without changing the profile.  The
active next steps are joint optimization in \(\mu,g,c,t\), the cubic
selector deletion algebra, and the two-compression observable that compares
the wide cubic response \(2\mu>1\) against the narrow quartic response.
