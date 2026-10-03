# Mollified discrete moments over complex zeros: the exact locus of RH in Conrey–Ghosh–Gonek and a quantified obstruction

Research memo, 2026-10-03. Companion script
[`verify/mollified_discrete_moment.py`](../../verify/mollified_discrete_moment.py)
(output `.out` beside it). **No new zero percentage is established.** The memo
(i) isolates precisely where Conrey–Ghosh–Gonek (CGG) and Bui–Heath-Brown (BHB)
use RH, (ii) writes the unconditional complex-zero analogue of their
certificate in the repo's mirror-pairing language, (iii) proves the inequality
that replaces Cauchy–Schwarz when the pairing is indefinite, (iv) computes the
resulting constants, and (v) proves that the remaining loss is uncontrolled by
any count-type information, including the repo's unconditional 2/3 and
0.6725 theorems. The honest outcome is a precise negative result with one
clean open input.

Labels: PROVED (full argument here or verbatim in the cited source), CHECKED
(exact rational / Gaussian-rational verification in the script), NUMERICAL
(floating diagnostics), CONJECTURE, REFUTED.

Sources read for this memo: Conrey–Ghosh–Gonek, *Simple zeros of the Riemann
zeta-function*, Proc. LMS 76 (1998) 497–522, §§2–3 (equations (2.1)–(2.10),
(3.1)–(3.15)); Bui–Heath-Brown, *On simple zeros of the Riemann
zeta-function*, Bull. LMS 45 (2013), arXiv:1302.5018, §2 (Lemma 1, Lemma 2,
(10)); repo notes
[ordered_moment](ordered_moment_20260905.md),
[sharpened_cubic_gain](sharpened_cubic_gain_20260905.md),
[certificate_limits](certificate_limits_20260905.md),
[bezoutian](bezoutian_20260905.md).

## 0. Summary

Write $F(s)=B(s)\zeta'(s)$ with $B(s)=\sum_{k\le y}\mu(k)P(\log(y/k)/\log y)k^{-s}$,
$y=T^\theta$, $P(0)=0$, $P(1)=1$, $L=\log(T/2\pi)$, $N=TL/2\pi$.

1. **Locus of RH (PROVED, literature).** CGG define
   $S_1=\sum_{0<\gamma\le T}F(\rho)$ and
   $S_2=\sum_{0<\gamma\le T}F(\rho)F(1-\rho)$ as residue sums of $\zeta'/\zeta$
   over the rectangle $-1/L<\Re s<1+1/L$, $1<\Im s\le T$; both sums run over
   **all** zeros, with every nonsimple zero contributing $0$. Their asymptotics
   $S_1\sim c_1NL$, $S_2\sim c_2NL^2$ are proved for $\theta<1/2$ with no
   hypothesis (CGG Theorem 2 under GLH; BHB Lemma 1 + Lemma 2 remove GLH). RH
   is used **once**, to write $S_2=\sum|F(\rho)|^2$ (CGG p. 500: "This is the
   only place we need RH"; BHB p. 4, identical sentence).
2. **Complex-zero analogue (PROVED).** $S_2$ is already the holomorphic
   mirror pairing $F(\rho)\overline{F(\sigma\rho)}$, $\sigma\rho=1-\bar\rho$,
   i.e. exactly the Hermitian structure the repo's operator uses
   (§2). On the line it is $|F(\rho)|^2\ge0$; on a mirror pair it is
   $2\Re\big(F(\rho)\overline{F(\rho')}\big)$, indefinite. No degree-two
   holomorphic pairing can be sign-definite on pairs (§3.3).
3. **Replacement for Cauchy–Schwarz (PROVED, CHECKED).** With
   $\Delta=\tfrac12\sum_{\text{pairs}}|F(\rho)-F(\rho')|^2
   =\tfrac12\big(\sum_\rho|F(\rho)|^2-S_2\big)\ge0$,
   $$N_s(T)\ \ge\ \frac{|S_1|^2}{S_2+\Delta},\qquad
     N_0^s(T)\ \ge\ \frac{2|S_1|^2}{S_2+E_{\rm off}}-N(T),$$
   where $N_s$ counts simple zeros anywhere, $N_0^s$ simple zeros on the line,
   and $E_{\rm off}=\sum_{\beta\ne1/2}|F(\rho)|^2$. Both are unconditional.
4. **Constants (CHECKED).** For every $\theta$ the optimal polynomial is
   $P=(1+\theta)x-\theta x^2$ and
   $$\kappa(\theta):=\max_P\frac{c_1^2}{c_2}=1-\frac1{(1+\theta)^3},\qquad
     \kappa(1/2)=\tfrac{19}{27}.$$
   With $\Delta=\delta NL^2$: $N_s/N\ge c_1^2/(c_2+\delta)$ beats the repo's
   $0.6725043820976$ **for simple zeros anywhere** iff $\delta<0.041319$
   (4.64% of $S_2$). For simple **on-line** zeros the certificate gives at
   most $2\kappa-1=11/27=0.4074$ even if $E_{\rm off}=0$; reaching $0.6725$
   would need $\theta\ge0.828$, outside the proved range $\theta<1/2$.
5. **Obstruction (PROVED, CHECKED).** For every $s>0$ there is a configuration
   with $sN$ simple on-line zeros and a **single** off-line mirror pair with
   values $(a,-a)$, $|a|^2=\tfrac12(c_1^2/s-c_2)NL^2$, reproducing $S_1,S_2$
   exactly. Hence $S_1,S_2$ plus any count bound on off-line zeros (the repo's
   $N_{\rm off}\le N/3$, zero-density theorems) give **no** lower bound for
   $N_0^s$, and no bound for $N_s$ beyond trivial. The missing input is an
   energy bound, $\Delta=o(NL^2)$, i.e.
   $\sum_\rho|B\zeta'(\rho)|^2=\sum_\rho B\zeta'(\rho)B\zeta'(1-\rho)+o(TL^3)$,
   a non-holomorphic discrete second moment that no current unconditional tool
   evaluates. The repo's bandwidth-one statistics decouple from $F$ and cannot
   supply it (§5.4).

So: the route does not raise the unconditional frontier. Its value is the
sharp statement of what is missing and the proof that counting information
cannot substitute for it.

## 1. The CGG/BHB certificate and where RH enters

**1.1 Setup (PROVED, CGG §§2–3).** Let $\mathcal C$ be the positively oriented
rectangle with vertices $1-c+i,\ c+i,\ c+iT,\ 1-c+iT$, $c=1+L^{-1}$, with $T$
at distance $\gg L^{-1}$ from every ordinate (no loss of generality,
unconditionally). Then

$$
 S_1=\frac1{2\pi i}\oint_{\mathcal C}\frac{\zeta'}{\zeta}(s)\,\zeta'(s)B(s)\,ds,
 \qquad
 S_2=\frac1{2\pi i}\oint_{\mathcal C}\frac{\zeta'}{\zeta}(s)\,\zeta'(s)\zeta'(1-s)B(s)B(1-s)\,ds .
$$

The residue of $(\zeta'/\zeta)(s)f(s)$ at a zero $\rho$ of multiplicity
$m(\rho)$ is $m(\rho)f(\rho)$, and $f$ contains the factor $\zeta'(s)$, so
every zero with $m(\rho)\ge2$ contributes $0$. Since $1-c<0$, the rectangle
contains every zero with $1<\gamma\le T$, on or off the line. Hence,
unconditionally,

$$
 S_1=\sum_{\substack{0<\gamma\le T\\ \rho\ \text{simple}}}F(\rho),\qquad
 S_2=\sum_{\substack{0<\gamma\le T\\ \rho\ \text{simple}}}F(\rho)F(1-\rho),
 \qquad F:=B\zeta'.
$$

**1.2 Asymptotics (PROVED, literature).** CGG (2.5)–(2.7): for fixed
$\theta<1/2$,

$$
 S_1\sim c_1\,\frac{TL^2}{2\pi},\qquad S_2\sim c_2\,\frac{TL^3}{2\pi},
$$
$$
 c_1=\frac12+\theta\!\int_0^1\!P,\qquad
 c_2=\frac13+\theta\!\int_0^1\!P+\theta^2\Big(\int_0^1\!P\Big)^2
      +\frac1{12\theta}\int_0^1\!P'^2 .
$$

CGG prove this assuming GLH (an average sixth-moment bound for Dirichlet
$L$-functions, used only for the range $L^A<q\le y$ of their character
decomposition (5.12)–(5.14)). BHB Lemma 2 replaces that step by the
generalised Vaughan identity and the large sieve, with error
$y^{1/3}T^{5/6+\varepsilon}+\eta^{-1/2}TL^C$, so the asymptotics are
**unconditional for $\theta<1/2$** (BHB: "Up to this point, all the analysis
is unconditional", and Lemma 2 needs nothing). The remaining ingredients are
the unconditional bounds CGG (3.5)–(3.8) on $\mathcal C$ ($\chi(s)\ll|t|^{1/2-\sigma}$,
$B(s)\ll y^{1-\sigma}L$, $\zeta'(1-s)\ll|t|^{\sigma/2}L^2$,
$(\zeta'/\zeta)(1-s)\ll L^2$ at distance $\gg L^{-1}$ from ordinates) and
Gonek's lemma.

**1.3 The single use of RH (PROVED, literature).** Both papers then write
$S_2=\sum_{0<\gamma\le T}|B\zeta'(\rho)|^2$ "assuming the Riemann Hypothesis
… this is the only place we need RH", and apply Cauchy's inequality
$|S_1|^2\le N_s(T)\,S_2$. With $P=(1+\theta)x-\theta x^2$, $\theta\to1/2$:
$S_1\sim\frac{19}{24}NL$, $S_2\sim\frac{57}{64}NL^2$, giving $19/27$.

The identity $S_2=\sum|F(\rho)|^2$ holds because, with $B$ having real
coefficients, $F(1-\rho)=\overline{F(\bar\rho)}$ and $\bar\rho=1-\rho$ exactly
when $\beta=1/2$. Nothing else in the argument (contour, Gonek's lemma,
arithmetic of the $a_\nu$, the Vaughan decomposition) sees $\beta$.

**1.4 Cross-check (CHECKED).** Block A of the script reproduces
$c_1=19/24$, $c_2=57/64$, $c_1^2/c_2=19/27$ exactly from (2.7).

## 2. The complex-zero analogue is already the mirror pairing

**2.1 (PROVED).** Let $\sigma\rho=1-\bar\rho$ be the mirror involution on the
zero multiset (it preserves multiplicities, fixes exactly the on-line zeros,
and swaps the two zeros $\beta+i\gamma$, $1-\beta+i\gamma$ of an off-line
pair). For holomorphic $f,g$ with real Dirichlet coefficients define

$$
 \langle f,g\rangle_\sigma:=\sum_{0<\gamma\le T}m(\rho)\,f(\rho)\,\overline{g(\sigma\rho)}
 =\sum_{0<\gamma\le T}m(\rho)\,f(\rho)\,g(1-\rho).
$$

This is a Hermitian form (reindex by $\sigma$). On each on-line zero it is
$f(\rho)\overline{g(\rho)}$; on each mirror pair it is the $2\times2$ block
$\begin{pmatrix}0&1\\1&0\end{pmatrix}$ in the basis of the two evaluations,
of inertia $(1,1)$. The CGG sums are
$S_1=\langle F,1\rangle_\sigma$ (restricted to simple zeros by the factor
$\zeta'$) and $S_2=\langle F,F\rangle_\sigma$.

**2.2 Identification with the repo's operator (PROVED).** The repo's kernel
([ordered_moment §1](ordered_moment_20260905.md))
$A_T(x,y)=\sqrt{u(x)u(y)}\sum_\rho m_\rho h_T(z_\rho/T)e^{iLz_\rho(x-y)}$,
$z_\rho=(\rho-\tfrac12)/i$, equals $\sum_\rho m_\rho h_T(z_\rho/T)\,e_x(\rho)\,e_y(1-\rho)$
with the holomorphic test family $e_x(s)=\sqrt{u(x)}\,T^{x(s-1/2)}$: indeed
$e_y(1-\rho)=\sqrt{u(y)}T^{-y(\rho-1/2)}=\overline{e_y(\sigma\rho)}$ and
$e_x(\rho)e_y(1-\rho)=\sqrt{u(x)u(y)}\,e^{iLz_\rho(x-y)}$. So the repo's
operator is the $\sigma$-Gram operator of $\{e_x\}$, and "pairing $z_\rho$
with $\bar z_\rho$" in the repo is literally the mirror pairing above. The
proposed analogue $F(\rho)F^*(1-\rho)$ in the task is therefore not a new
object: it is CGG's own $S_2$, read without RH. What differs between the two
settings is explained in §5.4.

**2.3 Pair blocks (PROVED).** For a mirror pair with $a=F(\rho)$,
$c=F(\rho')$, the pair contributes $a+c$ to $S_1$ and
$2\Re(a\bar c)=\tfrac12|a+c|^2-\tfrac12|a-c|^2$ to $S_2$. Two on-line simple
zeros with the same values would contribute $a+c$ and $|a|^2+|c|^2$. The
pair therefore looks like two on-line atoms whose $S_2$-entry is lowered by
$|a-c|^2=|F(\rho)-F(1-\bar\rho)|^2$. In particular $(a,c)=(a,-a)$ contributes
$0$ to $S_1$ and $-2|a|^2$ to $S_2$: negative mass of the full size of the
atoms.

## 3. The inequality that replaces Cauchy–Schwarz

Let $\mathcal S$ be the simple on-line zeros, $\mathcal P$ the mirror pairs
of simple off-line zeros, $N_s=|\mathcal S|+2|\mathcal P|$ the number of
simple zeros, $E_{\rm off}=\sum_{\mathcal P}(|a|^2+|c|^2)$.

**Theorem 1 (PROVED; CHECKED on random Gaussian-rational configurations).**
Put $\Delta=\tfrac12\sum_{\mathcal P}|a-c|^2$. Then

$$
 \Delta=\tfrac12\Big(\sum_{\rho}|F(\rho)|^2-S_2\Big),\qquad
 S_2+\Delta=\sum_{\mathcal S}|F(\rho)|^2+\tfrac12\sum_{\mathcal P}|a+c|^2,\qquad
 |S_1|^2\le N_s\,(S_2+\Delta).
$$

*Proof.* The two identities are §2.3 summed. For the inequality apply
Cauchy–Schwarz to $S_1=\sum_{\mathcal S}F(\rho)\cdot1+\sum_{\mathcal P}\frac{a+c}{\sqrt2}\cdot\sqrt2$:
$|S_1|^2\le(|\mathcal S|+2|\mathcal P|)(\sum_{\mathcal S}|F|^2+\frac12\sum_{\mathcal P}|a+c|^2)$. $\square$

**Theorem 2 (PROVED; CHECKED).** Weighting each pair once instead,
$|S_1|^2\le(|\mathcal S|+|\mathcal P|)(S_2+E_{\rm off})$, and since
$2|\mathcal P|\le N-|\mathcal S|$,

$$
 N_0^s\ \ge\ |\mathcal S|\ \ge\ \frac{2|S_1|^2}{S_2+E_{\rm off}}-N .
$$

*Proof.* $\sum_{\mathcal P}|a+c|^2=E_{\rm off}+\sum_{\mathcal P}2\Re(a\bar c)=E_{\rm off}+S_2-\sum_{\mathcal S}|F|^2$,
so the Cauchy–Schwarz right side is $(|\mathcal S|+|\mathcal P|)(S_2+E_{\rm off})$. $\square$

Theorem 2 has the shape of the repo's rank–trace count $S\ge2n_+-N$: a pair
costs two zeros but is credited once. With $E_{\rm off}=0$ and the CGG
constants it gives only $2\cdot\frac{19}{27}-1=\frac{11}{27}$.

**3.1 Inertia alone is vacuous here (PROVED).** The $\sigma$-Gram matrix
$M=\begin{pmatrix}N_s&S_1\\ \bar S_1&S_2\end{pmatrix}$ of the family
$\{1_{\rm simple},F\}$ is a sum of PSD rank-one atoms (on-line) and inertia
$(1,1)$ blocks (pairs) with $\det(\text{block})=-|a-c|^2\le0$. The inertia
bound $|\mathcal S|+|\mathcal P|\ge n_+(M)$ is at most $2$. The repo's
inertia certificate works because its test family has dimension comparable to
$N$ and because its Hilbert–Schmidt norm is a computable statistic; see §5.4.

**3.2 Weighted Cauchy–Schwarz is sharp for this data (PROVED).** Any
inequality of the form $|S_1|^2\le(|\mathcal S|+\lambda|\mathcal P|)(\cdot)$
with $\lambda<2$ reintroduces $(1-2/\lambda)\sum_{\mathcal S}|F|^2<0$ on the
right, hence needs an upper bound on the on-line energy, which is circular;
$\lambda>2$ is weaker than Theorem 1. So Theorems 1–2 are the two natural
endpoints.

**3.3 No sign-definite holomorphic pairing of degree two (PROVED).** The
computable pairings on a pair are $2\Re(a^j\bar c^k)$ summed over
$(j,k)\in\{(2,0),(1,1),(0,2)\}$. A real combination
$Q=2\alpha\Re(a\bar c)+2\beta\Re a^2+2\beta'\Re c^2$ is $\ge0$ on the
on-line locus $c=a$ for all $a$ iff $\beta+\beta'=0$, $\alpha\ge0$; then
$Q(a,-a)=-2\alpha|a|^2$. Degree four would require
$\sum_\rho F(\rho)^2F(1-\rho)^2$, a fourth discrete moment that is not
available even under RH (only lower bounds, Milinovich–Ng).

## 4. Constants

**4.1 Optimal polynomial and closed form (CHECKED, Block B).** For fixed
$\theta$ and $I=\int_0^1P$, the strictly convex functional $\int P'^2$ under
the affine constraints $P(0)=0,P(1)=1,\int P=I$ is minimised by the quadratic
$q=x+6(I-\tfrac12)x(1-x)$, with the exact identity
$\int P'^2-\big(1+12(I-\tfrac12)^2\big)=\int(P'-q')^2$ (checked on random
rational polynomials of degree up to 7). Writing $I=\tfrac12+t$, the ratio
$c_1^2/c_2$ has its exact stationary point at $t=\theta/6$ (the derivative
numerator vanishes identically in $\theta$), i.e. $P=(1+\theta)x-\theta x^2$,
CGG's choice, and

$$
 \kappa(\theta)=\frac{\theta(\theta^2+3\theta+3)}{(1+\theta)^3}
             =1-\frac1{(1+\theta)^3},\qquad
 \kappa(\tfrac12)=\tfrac{19}{27},\ \ \kappa(0.49)=0.69770,\ \ \kappa(0.4507)=0.67246 .
$$

A degree-six numerical optimisation (NUMERICAL, Block F) agrees to $10^{-7}$.

**4.2 Mollifier length.** The asymptotics are proved for $\theta<1/2$ only;
CGG state "we assume throughout that $y=T^\vartheta$ with $\vartheta<1/2$",
and BHB's error $y^{1/3}T^{5/6+\varepsilon}$ forces the same. The repo's
bandwidth-one tools concern $\sum_{\rho,\rho'}$ pair statistics of the
family $\{e_x\}$ in frequency support $|x-y|<1$ and do not lengthen a
Dirichlet polynomial multiplying $\zeta'$ inside a residue sum; the
[one-piece derivative-mollifier ceiling](certificate_limits_20260905.md#a-rigorous-ceiling-for-one-piece-derivative-mollification)
and the [mollified Bezoutian test](bezoutian_20260905.md) are the two closed
attempts to use mollifiers inside the repo's framework and are not repeated
here. Values of $\kappa(\theta)$ for $\theta\ge1/2$ in the script are formal
extrapolations of the polynomial formula, not theorems.

**4.3 Comparison with $0.6725$ and $19/27$ (CHECKED/NUMERICAL, Block E).**
With $\Delta=\delta NL^2$ and $\theta\to1/2$:

| statement | value | condition |
|---|---|---|
| $N_s/N\ge c_1^2/(c_2+\delta)$ | $19/27=0.7037$ at $\delta=0$ | unconditional given $\delta$ |
| beats repo's $0.6725043820976$ for $N_s$ | iff $\delta<0.041319$ | $\Delta\le4.64\%$ of $S_2$ |
| beats $2/3$ for $N_s$ | iff $\delta<0.049479$ | |
| $N_s/N\ge1-(1+\theta)^{-3}$ exceeds $0.6725$ | iff $\theta>0.450769$ | inside $\theta<1/2$ |
| $N_0^s/N\ge2c_1^2/(c_2+e_{\rm off})-1$ | $11/27=0.4074$ at $e_{\rm off}=0$ | far below $0.6725$ |
| $1-2(1+\theta)^{-3}\ge0.6725$ | needs $\theta\ge0.8279$ | outside proved range |

Like-with-like: the repo's $0.6725$ is for simple **on-line** zeros and
trivially implies $N_s\ge0.6725N$; the CGG-type bound of Theorem 1 is for
$N_s$. For the headline quantity $N_0^s$ the certificate gives nothing beyond
$11/27$ even in the best case.

## 5. The obstruction, quantified

**5.1 One pair suffices (CHECKED, Block D).** In normalised units
($S_1=c_1NL$, $S_2=c_2NL^2$), take $sN$ simple on-line zeros with the common
value $F=c_1L/s$, one off-line mirror pair with values $(a,-a)$,
$|a|^2=\tfrac12(c_1^2/s-c_2)NL^2$, and all remaining zeros nonsimple. Then
$S_1$ and $S_2$ take the CGG values exactly, for every $0<s\le c_1^2/c_2$. At
$s=0.6725043820976$ the pair needs $|F(\rho)|^2=0.02066\,NL^2$, i.e.
$\Delta=0.0413\,NL^2$, the threshold of §4.3. As $s\to0$ the required energy
grows like $c_1^2/(2s)\,NL^2$ but the pair count stays one. Hence:

> **(PROVED)** From $S_1,S_2$ together with *any* upper bound on the number
> of off-line zeros (the repo's $N_{\rm off}\le N/3$, the pair bound
> $|\mathcal P|\le0.16375N$ implied by the repo's $0.6725$ theorem, or any
> zero-density theorem), $\inf|\mathcal S|/N=0$. Absorption of off-line
> zeros by the 2/3-on-line theorem fails, because that theorem bounds counts
> and the loss is an energy.

**5.2 Pointwise bounds do not rescue it (PROVED, elementary).** The convexity
bound $|\zeta'(\sigma+it)|\ll|t|^{(1-\sigma)/2+\varepsilon}$ and the trivial
$|B|\le y^{1/2}L$ near $\sigma=1/2$ give $|F(\rho)|^2\ll T^{1/2+\theta+\varepsilon}$
at zeros in the strip. The energy $0.0413\,NL^2\asymp TL^3$ then needs about
$T^{1/2-\theta-\varepsilon}$ off-line pairs. Selberg's density bound
$N(\sigma,T)\ll T^{1-(\sigma-1/2)/4}\log T$ excludes only zeros with
$\beta-\tfrac12\ge4(\tfrac12+\theta)>1$, i.e. nothing; stronger modern
density estimates excluding $T^{1/2-\theta}$ zeros would have to be uniform
down to $\beta-\tfrac12\asymp1/L$, which is RH-strength. So neither a
pointwise bound nor a zero-density bound can control $\Delta$.

**5.3 The adversary with an energy cap (NUMERICAL, Block E).** If one grants
a hypothetical cap $E_{\rm off}\le e_0NL^2$ and pair fraction
$|\mathcal P|\le pN$, the infimum of $|\mathcal S|/N$ consistent with the CGG
values is tabulated in the output; e.g. at $p=0.001$ the bound crosses the
repo's $0.6725$ at $e_0\approx0.04$, and at the repo-allowed $p=0.16375$ it is
already $0.6125$ at $e_0=0.01$. No unconditional source for any such cap is
known.

**5.4 Why the repo's certificate survives and this one does not (PROVED).**
Both certificates use only holomorphic mirror pairings. The repo's atoms are
$v_\rho(x)=\sqrt{u(x)}T^{x(\rho-1/2)}$ and its two statistics are
$\operatorname{tr}A=\sum_\rho m_\rho h(z_\rho/T)\int u$ (every zero, on or
off the line, contributes exactly $\int u$) and
$\operatorname{tr}A^2=\|A\|_{\rm HS}^2$, in which an off-line zero at
distance $d$ from the line enters the diagonal with
$\|v_\rho\|^2\|v_{\sigma\rho}\|^2=\int u\,T^{2xd}\int u\,T^{-2xd}>1$. Since
$\operatorname{tr}A^2=D(u)N(1+o(1))$ is pinned by the explicit formula in
bandwidth one, the sizes of off-line atoms are implicitly bounded, and the
rank–trace lemma needs only inertia. In the CGG setting the analogous
operator is $G_F=\sum_\rho m_\rho F(\rho)F(1-\rho)\,e_x(\rho)e_y(1-\rho)$,
whose trace is $S_2$ but whose Hilbert–Schmidt norm is the weighted pair
statistic $\sum_{\rho,\rho'}F(\rho)F(1-\rho)F(\rho')F(1-\rho')\,\widehat{(\cdot)}(z_\rho-\bar z_{\rho'})$,
a twisted fourth-order discrete moment of $\zeta'B$ with no unconditional (or
conditional) evaluation. Without a second computable statistic no
scale-free counting inequality exists: a Hermitian operator's positive index
is not bounded below by its trace alone. Cauchy–Schwarz is the
two-statistic inequality ($(\operatorname{tr})^2/\|\cdot\|^2$ for the
$2\times2$ matrix), and indefiniteness breaks it by exactly $\Delta$.

**5.5 Decoupling from the repo's data (PROVED, formal).** A joint adversary
choosing a zero configuration must satisfy the repo's trace constraints (which
force $|\mathcal S|\ge0.6725N$) and the CGG values. The CGG values involve the
numbers $F(\rho)=B(\rho)\zeta'(\rho)$, which are not functions of the repo's
feature data (positions $z_\rho$ and multiplicities): $\zeta'(\rho)$ depends
on the global Hadamard product. Since §5.1 realises the CGG values with one
pair for any $|\mathcal S|$, the joint constraint set is the repo's
constraint set, and the CGG data add nothing. A coupling identity between
$\zeta'(\rho)B(\rho)$ and local zero geometry would be required, and none is
available.

## 6. The one open input, stated exactly

**OPEN (CONJECTURE, implied by RH).** For some $\theta<1/2$ and admissible $P$,
$$
 \sum_{0<\gamma\le T}\big|B\zeta'(\rho)\big|^2
 =\sum_{0<\gamma\le T}B\zeta'(\rho)\,B\zeta'(1-\rho)+o(TL^3),
$$
equivalently $\sum_{\beta\ne1/2,\,0<\gamma\le T}|F(\rho)-F(1-\bar\rho)|^2=o(TL^3)$.
Granting it, Theorem 1 gives $N_s\ge(19/27-o(1))N$ unconditionally
(simple zeros anywhere), and any version with remainder $\le0.0413\,TL^3/2\pi$
already gives $N_s>0.6725N$; neither gives anything new for $N_0^s$
(Theorem 2 caps the on-line yield at $11/27$).

Status of every analytic input:

| input | status |
|---|---|
| $S_1,S_2$ residue identities over all zeros, nonsimple zeros contribute $0$ | PROVED (CGG §2) |
| $S_1\sim c_1NL$, $S_2\sim c_2NL^2$, $\theta<1/2$ | PROVED unconditionally (CGG + BHB Lemma 2) |
| $S_2=\sum|F(\rho)|^2$ | **RH only**; equivalent to $\Delta=0$ |
| Theorems 1, 2 | PROVED (finite algebra), CHECKED |
| $\kappa(\theta)=1-(1+\theta)^{-3}$, optimal $P$ | CHECKED (exact) |
| $\Delta=o(TL^3)$ | OPEN; no unconditional tool; counts/pointwise bounds insufficient (§5) |
| weighted pair statistic $\|G_F\|_{\rm HS}^2$ | OPEN even under RH |
| extension to $\theta\ge1/2$ | not proved; formal only |

## 7. Adversarial self-check

- *Like-with-like.* The repo's $0.6725$ is for simple on-line zeros; CGG's
  $19/27$ is for simple zeros under RH, where the two notions coincide.
  Unconditionally they differ, and §4.3 keeps the two columns separate. The
  only claim of "beating 0.6725" is for $N_s$ and is conditional on the open
  energy bound of §6.
- *Cherry-picking.* The constants are the published ones, reproduced exactly;
  the optimisation over $P$ is proved complete (convexity + exact stationary
  point), not a search over a few polynomials.
- *Assertion–evidence gap.* The negative result (§5.1) is an explicit
  construction, not a heuristic; its only inputs are the CGG values and the
  real-coefficient symmetry $F(1-\rho)=\overline{F(\sigma\rho)}$. The claim
  that the asymptotics are unconditional rests on the explicit statements in
  CGG p. 500 and BHB p. 4, quoted in §1.3, and on BHB Lemma 2; I did not
  re-derive the main terms. The identification §2.2 is a two-line
  computation. The "repo survives" explanation in §5.4 describes a mechanism
  and is consistent with the repo's proofs, but it is an explanation, not a
  theorem that no CGG-type statistic can ever be added to the repo's
  framework.
- *What was not tried and why.* Shifted pairings $F(\rho+i\delta)F(1-\rho-i\delta)$
  have the same block structure; derivative pairings
  $F'(\rho)F'(1-\rho)$ do not isolate $|F(\rho)-F(\rho')|^2$; the
  antisymmetric $G(s)=F(s)-F(1-s)$ pairs to $-2\Re(F(\rho)-\overline{F(\rho')})^2$,
  not to $\Delta$. None changes §3.3.

## 8. Recommendation

Do not pursue the mollified discrete moment as a route to the unconditional
simple-on-line proportion. The one object worth a separate attack is the
non-holomorphic second moment $\sum_\rho|B\zeta'(\rho)|^2$ at complex zeros;
every known unconditional evaluation technique for sums over zeros (residue
calculus, explicit formula) sees only holomorphic pairings, so a new idea is
required, and even success would raise $N_s$, not $N_0^s$.
