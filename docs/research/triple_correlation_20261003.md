# Triple correlations in the unconditional range: support geometry, two obstructions, and a marked cubic increment

Research note, 2026-10-03. Companion verifier:
[`verify/triple_correlation_certificate.py`](../../verify/triple_correlation_certificate.py)
(output: [`verify/triple_correlation_certificate.out`](../../verify/triple_correlation_certificate.out)).

Labels: **PROVED** (argument written here), **CHECKED** (exact rational or interval
verification in the script), **NUMERICAL** (floating diagnostics only), **CONJECTURE**,
**REFUTED**. Inputs inherited from earlier notes keep their earlier status. I did not
re-audit them here, and I say so wherever they are used.

## 0. Summary

1. **REFUTED: the premise that triple correlations reach new frequencies.** On the
   translation-invariant slice ($\sum\xi_j=0$), the Rudnick–Sarnak region
   $\sum|\xi_j|<2$ equals $\sum(\xi_j)_+<1$. So no single $|\xi_j|$ can reach 1.
   For $n=3$ the region is exactly the hexagon $\max|\xi_j|<1$. That is the set of
   frequency triples $(x-y,y-z,z-x)$ with $x,y,z$ in a window of width $<1$, which
   the repository's $\operatorname{tr}G^3$ already uses (§1, PROVED).
2. **PROVED (given the RS/GUE identification on the support): in this range the triple
   information is mock-Gaussian.** On the hexagon the full 3-level structure factor is
   $\delta\delta+\sum_c\delta(\xi_c)|\xi_a|$, and the third cumulant vanishes
   identically. Every triple statistic $\int\Phi\,G_0G_0G_0$ is evaluated from $\Phi$
   on the diagonal and on the three collapse planes alone (§2).
3. **Obstruction A (PROVED for the flat window; CHECKED by interval arithmetic for the flat
   and Montgomery–Taylor cosine windows).** Take linear spectral certificates
   $S\ge\alpha_1\operatorname{tr}G+\alpha_2\operatorname{tr}G^2+\alpha_3\operatorname{tr}G^3$,
   valid for every configuration. Two shallow off-line pairs force $\alpha_3\ge0$, and
   coalescing simple zeros force $\alpha_3\le0$. So $\alpha_3=0$, and the LP optimum is
   the pair value $2-D(u)$ (§3).
4. **Obstruction B (PROVED in the abstract zero-side class).** A certificate whose only
   arithmetic inputs are $\tau(G),\tau(G^2),\tau(G^3)$ cannot certify more than $2-D$.
   This holds even with a nonlinear dependence on those three numbers. Already at
   cluster displacement $B=4096$ the adversary's simple fraction is below the inherited
   value $2-D+1/271803$ (CHECKED). The inherited gain therefore comes entirely from the
   ordered quartic energy $Q$. Triple information by itself is inert (§4).
5. **New increment (finite operator theorem PROVED; scalar CHECKED; analytic transfer
   inherited).** The general hexagon test gives a *marked* cubic defect
   $\kappa_a=\int a(x)d(x)\,dx$. Its density $d$ is positive in the middle of the window
   and negative near the ends. A marked version of the sharpened ordered-cubic
   inequality converts it into
   $$\liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}\ \ge\ 2-D(u)+\frac1{216600}
   =0.6725053197675\ldots>0.672505319,$$
   compared with $0.6725043820976$. This is an increase of $9.4\cdot10^{-7}$ in the
   proportion, and of 25.5% in the increment (§5). It needs the marked analogues of
   the inherited 3-level and ordered 4-level transfers (§5.3). Their status is the same
   as the inherited unmarked ones.
6. **Feasibility.** This is a small, honest increment. It is not a route to 85%.
   Within $\sum|\xi|<2$, triple data acts only through fourth-order control, and the
   whole mechanism scales like $(\kappa_a/C)^2\sim10^{-6}$ (§6).

## 1. What the unconditional $n$-level input is

**Source and scope.** Rudnick–Sarnak (Duke 81 (1996), Thm 1.1 and §3) treat the
$n$-level correlation sums $\sum h(\gamma_{j_1}/T)\cdots f(L\gamma_{j_1}/2\pi,\dots)$ for
symmetric, translation-invariant $f$ ($f(x+t\mathbf1)=f(x)$) whose Fourier transform,
a distribution on $\{\sum\xi_j=0\}$, is supported in $\sum|\xi_j|<2$. The repository
note [ordered_moment](ordered_moment_20260905.md) §§1–5 records that the smooth-height
version of the proof is unconditional for $\zeta$ and allows complex ordinates. I use
that claim as inherited and have not re-audited it. Hughes–Rudnick mock-Gaussian
moments average over a translation $t$, and the $t$-average forces $\sum\xi_j=0$. They
therefore live on the same slice, with $\operatorname{supp}\hat f\subset[-2/n,2/n]$
inside $\sum|\xi_j|\le2$.

**Proposition 1.1 (PROVED).** If $\sum_j\xi_j=0$ then
$\sum_j|\xi_j|=2\sum_j(\xi_j)_+\ge2\max_j|\xi_j|$. For $n=3$ equality holds:
$\sum|\xi_j|=2\max|\xi_j|$. Hence:

* on the RS region every $|\xi_j|<1$. The premise "single $|\alpha_i|>1$" is REFUTED on
  the translation-invariant slice;
* for $n=3$ the RS region is the hexagon $\{\max|\xi_j|<1\}$. A triple is in it exactly
  when $\xi=(x-y,y-z,z-x)$ for some $x,y,z$ in an interval of length $<1$. Take $y=0$,
  $x=\xi_1$, $z=-\xi_2$; the range of $\{x,y,z\}$ is then $\max|\xi_j|$.

*Proof.* The positive and negative parts have equal sums. With three entries, the entry
whose sign is alone equals minus the sum of the other two. ∎ (Section [1] of the script
checks 40,000 random rational instances exactly.)

Consequences. (i) At window width $<1$, a triangle cycle in $\operatorname{tr}G^3$, or in
any marked $\operatorname{tr}(M_aGM_bGM_cG)$, is automatically admissible. *No new
frequency region exists for triple correlations.* The only new freedom is the shape of
the test function on the hexagon, because the repository uses only the product test
$u\otimes u\otimes u$. (ii) For $n\ge4$, $\sum(\xi_j)_+<1$ is exactly the "total ascent
$<1$" condition. At width one this is the repository's two-monotone-path restriction.
(iii) Remark: non-translation-invariant trace functionals, such as
$\operatorname{tr}(AG^3)$ with a smooth non-diagonal kernel $A$, localise at height
$O(1)$ by Riemann–Lebesgue. They are $o(N)$ and carry no information. Only
diagonal (multiplication) marks survive. I use this remark only as motivation.

## 2. Mock-Gaussian structure of the hexagon data

Write $G_0(x,y)=\sum_\rho m_\rho e^{iLz_\rho(x-y)}$ on the window $[-\frac12,\frac12]$. The
profile operator is $G=\sqrt{u}\,G_0\sqrt u$. In unit-density variables the
"full-sum" structure factors (coincident indices included) are $S_1=1$ and
$S_2(\xi)=\delta(\xi)+|\xi|$ for $|\xi|<1$. For $S_3$, the sine-kernel correlation
$\rho_3=1-\sum K_{ab}^2+2K_{12}K_{23}K_{31}$ and the three partial diagonals give, on
$\sum\xi=0$, the continuous part
$$1-\sum_c(1-|\xi_c|)+2(1-\max|\xi|)=\sum|\xi|-2\max|\xi|=0 .$$
The term $2(1-\max|\xi|)$ is the Fourier transform of $2K_{12}K_{23}K_{31}$: it is the
measure of $\{k\in I:k+\xi_1\in I,\ k-\xi_3\in I\}$.

**Proposition 2.1 (PROVED, granting that RS identifies the $\le3$-level main terms with
the sine kernel on the support).** On the hexagon,
$S_3=\delta(\xi_1)\delta(\xi_2)+\sum_c\delta(\xi_c)|\xi_a|$. Equivalently, the
connected three-point form factor $c_3$ vanishes there. For every smooth $\Phi$ on
$[-\frac12,\frac12]^3$,
$$\lim\frac1N\!\int\!\Phi\,G_0(x,y)G_0(y,z)G_0(z,x)
=\int\Phi(x,x,x)dx+\!\iint\!|x-z|\big[\Phi(x,x,z)+\Phi(x,z,z)+\Phi(x,z,x)\big]dxdz.$$
(Section [2] checks the cancellation exactly at random rational points.) With
$\Phi=u\otimes u\otimes u$ this reproduces the repository's $M_3$. The formula agrees
with the repository's contraction constants: zero-prime coefficient $1$ and one-pair
coefficient $1$ with prime measure $|v|\,dv$.

So, within RS support, the 3-level data is the pair form factor on $|\xi|<1$ plus the
constraint $c_3\equiv0$ on the hexagon. Any arithmetic value depends on $\Phi$ only
through the diagonal and the collapse planes.

**The marked cubic defect.** Take $\Phi=a(x)u(x)u(y)u(z)$, with the mark at the start
vertex of the cycle. With $Kf(x)=\int|x-y|f(y)dy$ and $p(t)=t(t-1)(t-2)$,
$$-\lim\frac{\operatorname{tr}(M_a\,p(G))}{N}=\kappa_a:=\int a\,d,\qquad
d=-\big[u^3+2u^2Ku+uK(u^2)-3u^2-3uKu+2u\big].$$
Here $\int d=\kappa=3D-2-M_3$. For the cosine, NUMERICAL values: $\int d=0.0117755$;
$d>0$ on $|x|\lesssim0.30$ and $d<0$ near the ends ($d(\pm\frac12)\approx-0.027$);
$\int|d|=0.02657\approx2.26\kappa$. The marked defect therefore carries information that
the scalar $\kappa$ discards. A CUE sanity check (NUMERICAL, section [7]) compares the
marked triple trace with this formula. For CUE, triangle cycles lie inside the exact
Diaconis–Shahshahani Gaussian range, so expectations agree up to $O(1/N)$
discretisation. Result: $0.9761\pm0.0042$ (80 samples, $N=160$, step mark) against
the formula's $0.9771$.

## 3. Obstruction A: linear spectral cubic certificates

**Sign structure.** A *zero-side* inequality must hold for every finite configuration:
simple on-line atoms, multiple atoms, and off-line conjugate pairs. In the vector
notation $v_\rho=\sqrt u\,e^{iLz_\rho x}$, a pair gives
$v_zv_{\bar z}^*+v_{\bar z}v_z^*$. *Arithmetic* statements are averaged limits such as
$\operatorname{tr}G^k/N\to(1,D,M_3)$. The class considered here is
$$S\ \ge\ \alpha_1\operatorname{tr}G+\alpha_2\operatorname{tr}G^2+\alpha_3\operatorname{tr}G^3-o(N)
\quad\text{for every configuration},$$
and the LP is: maximise $\alpha_1+\alpha_2D+\alpha_3M_3$.
Since $M_3=3D-2-\kappa$ with $\kappa>0$, a gain would need $\alpha_3<0$.

**Proposition 3.1 (PROVED).** $\alpha_3\le0$. *Proof.* Let $k$ distinct real zeros coalesce.
The Gram matrix tends to the all-ones matrix, so $G$ has the single eigenvalue $k$ with
$S=k$. The inequality forces $\alpha_1k+\alpha_2k^2+\alpha_3k^3\le k$ for all $k$. ∎

**Proposition 3.2 (PROVED for the flat window; CHECKED for flat and cosine).** For every
$c<0$ there is a configuration of two off-line pairs ($S=0$, $N=4$) with
$\operatorname{tr}G^2-2\operatorname{tr}G<|c|\cdot(-\operatorname{tr}p(G))$. Hence any
certificate with $\alpha_3<0$ fails, and $\alpha_3\ge0$.

*Proof (flat window).* Take ordinates $0,\delta$ in units $L\gamma$, and common
displacement $B=L\beta$. Let $I(w)=\int_{-1/2}^{1/2}e^{iwx}dx=2\sin(w/2)/w$. Order the
vectors as $(a_1,a_2,b_1,b_2)$ with $a_j=e^{i(w_j-iB)x}$ and $b_j=e^{i(w_j+iB)x}$. The
pair matrix swaps $a_j\leftrightarrow b_j$, so
$MK=\begin{pmatrix}\Sigma&K_{bb}\\K_{aa}&\Sigma\end{pmatrix}$ with
$\Sigma_{ij}=I(w_j-w_i)$, $K_{aa}=R\tilde A$, $K_{bb}=R\bar{\tilde A}$ and
$R=\sinh B/B$. Exactly:
$$\operatorname{tr}G=4,\quad \operatorname{tr}G^2=2\operatorname{tr}\Sigma^2+2R^2\tau,\quad
\operatorname{tr}G^3=2\operatorname{tr}\Sigma^3+6R^2\Re\operatorname{tr}(\Sigma\tilde A\bar{\tilde A}),$$
where $\tau=\operatorname{tr}(\tilde A\bar{\tilde A})=2+2\Re\alpha^2$, $\alpha=\tilde A_{12}$,
and $\Re\operatorname{tr}(\Sigma\tilde A\bar{\tilde A})=\tau+4s\Re\alpha$ with
$s=I(\delta)$. Directly,
$\alpha=\frac{2B}{2B+i\delta}\cdot\frac{e^{i\delta/2}-e^{-i\delta/2}e^{-2B}}{1-e^{-2B}}$.
Put $\delta=\pi+\gamma/B$ and let $B\to\infty$ with $\gamma$ fixed. Then
$B\Re\alpha\to(\pi-\gamma)/2$, $B^2\tau\to(\gamma-\pi)^2+\pi^2/2$, and $s\to2/\pi$. The
slack is $Q_d=\operatorname{tr}G^2-2\operatorname{tr}G=2R^2\tau+O(1)$ and
$-\operatorname{tr}p(G)=-24sR^2\Re\alpha+O(1)$. Since $R^2/B^2\to\infty$, for
$\gamma>\pi$
$$B\cdot\frac{Q_d}{-\operatorname{tr}p(G)}\to\frac{\pi\,((\gamma-\pi)^2+\pi^2/2)}{12(\gamma-\pi)},$$
which is minimised at $\gamma=\pi(1+1/\sqrt2)$ with value $\pi^2/(6\sqrt2)=1.16314$.
So the ratio tends to 0. ∎

CHECKED (mpmath interval arithmetic, section [3]): ratio $\le0.006168$ at $B=192$ and
$\le2.8421\cdot10^{-4}$ at $B=4096$ (flat), with $B\cdot$ratio approaching $1.1631$. For
the cosine, ratio $\le2.7427\cdot10^{-4}$ at $B=4096$. Realisability: $B=L\beta$ is
admissible as soon as $L>2B$. These are shallow off-line pairs with $\beta\asymp1/\log T$,
at ordinate gap about half a mean spacing. Nothing unconditional excludes them.

**Corollary 3.3 (dual obstruction).** In this LP class $\alpha_3=0$, and the optimum is
$\max_u(2-D(u))=2-D_{MT}$. Triple information enters this class with weight zero. For a
general profile with $u(\pm\frac12)>0$ I expect the same (CONJECTURE). The interval
checks cover only the flat and cosine windows.

## 4. Obstruction B: the three cubic moments alone are inert

**Proposition 4.1 (PROVED, abstract class).** Let $\mathcal K$ be the class of orthogonal
direct sums of: unit simple atoms, double atoms $2ff^*$, and literal two-off-line-pair
blocks of §3, each block in its own copy of $L^2$(window). Every element satisfies
the zero-side axioms used by the rank–trace and ordered-cubic arguments:
$G=P+B-C$ with $\operatorname{rank}P\le S$ and $n_\pm\le b$. Fix $D>1$ and $\kappa>0$.
For every $B$ there are configurations in $\mathcal K$ with
$\operatorname{tr}G/N=1$, $\operatorname{tr}G^2/N=D$, $\operatorname{tr}G^3/N=3D-2-\kappa$
(up to rounding $o(1)$), and
$$S/N=2-D+\kappa\cdot r(B),\qquad r(B)=Q_d/(-\operatorname{tr}p(G))\text{ of one cluster}.$$

*Construction.* Take a tight block of $s$ simple and $d$ double orthonormal atoms, and
$K$ clusters with traces $(4,q_2,q_3)$ and $P_c=q_3-3q_2+8<0$. Choose
$KP_c=-\kappa N$, $s+2d=N-4K$ and $s+4d=DN-Kq_2$. Then
$\operatorname{tr}G^3=(3D-2)N+KP_c$. The rank–trace slack is exactly $KQ_d$, so
$S/N=2-D+KQ_d/N=2-D+\kappa r(B)$. Also $d\approx(D-1)N/2>0$ because
$Kq_2=O(\kappa r N)$. ∎

Hence any certificate, linear or not, that uses only these three numbers and is valid
on $\mathcal K$ certifies at most $\inf_B(2-D+\kappa r(B))=2-D$. CHECKED: at $B=4096$,
$\kappa r\le3.35\cdot10^{-6}<1/271803$. So the inherited increment $1/271803$ cannot come
from $(\operatorname{tr}G,\operatorname{tr}G^2,\operatorname{tr}G^3)$. It comes from the
ordered quartic energy $Q$, which the clusters inflate. This is consistent with the
inherited inequality (6). With $\delta=3.35\cdot10^{-6}$ that inequality forces the
adversary's ordered quartic energy to be at least about $0.49$, above the arithmetic
value $0.399$. So $Q$ excludes this adversary.

Scope: $\mathcal K$ uses orthogonal direct sums. Literal zeros interact across blocks.
Inside one window, a dense tight block of literal exponentials cannot be orthogonal to
the clusters. The proposition is therefore a statement about certificates that use only
these zero-side axioms, as in the repository's tracial adversaries. It is not a
statement about actual zeta zeros.

## 5. A marked ordered-cubic certificate

### 5.1 Finite operator theorem

Use the sharpened-note setting ([sharpened_cubic_gain](sharpened_cubic_gain_20260905.md)
§1): $G=P+B-C$, $\operatorname{tr}G=N$, $\Delta=\operatorname{tr}G^2-2N+S$,
$H=E+2F$ with $EF=0$, $X=G-H$, $d^2=\|X\|_2^2\le\Delta$, and $e,f$ the ranks with
$e\le S$, $S+2f\le N$. Let $V,W$ be the Volterra parts of $G,H$, and $Z=V-W$. Let
$a:[-\frac12,\frac12]\to[1-\beta,1]$ be continuous with $\beta\ge0$, and put
$b=1-a\ge0$, $A=M_a$, $B_m=M_b$, and $\alpha=\max(1,\beta-1)\ge\|A\|$. Define
$\Sigma_A(Y)=AY^2+YAY+Y^2A$.

**Theorem 5.1 (PROVED).**
$$-\operatorname{tr}(A\,p(G))\le6\alpha\Delta+\sqrt\Delta\Big[\beta\sqrt{2N-S}
+\sqrt2\Big(\|\Sigma_A(V)\|_2+(2\alpha+1)\sqrt{\tfrac{4N-3S}3}+\beta\sqrt{2(2N-S)}\Big)\Big].$$
With $\beta=0$ this is exactly the inherited inequality (6).

*Proof.* (a) *Identity.* Words consisting only of $V$ (or only of $V^*$) with a diagonal
$A$ inserted are Volterra, so they have zero trace. Hence
$\operatorname{tr}(AG^3)=2\Re\operatorname{tr}[\Sigma_A(V)V^*]$, and likewise for $H$.
Writing $V^*=Z^*+H-W$ and using $\operatorname{tr}(\Sigma_A(Z))=0$ gives
$$\operatorname{tr}(AG^3)-\operatorname{tr}(AH^3)=\operatorname{tr}(A(H^2X+HXH+XH^2))
+2\Re\operatorname{tr}[(\Sigma_A(V)-\Sigma_A(W))Z^*]+2\Re\operatorname{tr}[\Sigma_A(Z)(H-I)].$$
(Checked to $10^{-13}$ on random zero-diagonal matrices, section [5].) Using
$p(H)=0$ and $\operatorname{tr}(AX^2)=\operatorname{tr}(A(ZZ^*+Z^*Z))$:
$$-\operatorname{tr}(Ap(G))=-\operatorname{tr}(A\,Dp(H)[X])-2\Re\operatorname{tr}[(\Sigma_A(V)-\Sigma_A(W))Z^*]
-2\Re\operatorname{tr}[\Sigma_A(Z)(H-I)]+3\operatorname{tr}(A(ZZ^*+Z^*Z)).$$
(b) *Quadratic terms.* $\|\Sigma_A(Z)\|_1\le3\alpha\|Z\|_2^2$, $\|H-I\|\le1$, and
$\|Z\|_2^2=d^2/2$, so the last two terms are at most $6\alpha d^2$.
(c) *Linear term.* $p$ vanishes on $\{0,1,2\}$, so all divided differences between
distinct nodes vanish and $Dp(H)[X]=2X_{00}-X_{EE}+2X_{FF}$. Then
$-\operatorname{tr}(ADp(H)X)=-L+\operatorname{tr}(B_m(2X_{00}-X_{EE}+2X_{FF}))$, with
$-L\le\Delta-d^2$ by the sharpened note's (3). Here $X_{00}=J_0GJ_0\le0$ (the
negative part of $J(P-C)J$), so $2\operatorname{tr}(B_mX_{00})\le0$. Also
$-\operatorname{tr}(B_mX_{EE})\le\beta\|(X_{EE})_-\|_1\le\beta\sqrt e\,\|X_{EE}\|_2$ and
$2\operatorname{tr}(B_mX_{FF})\le2\beta\sqrt f\,\|X_{FF}\|_2$. By Cauchy–Schwarz the sum
is at most $\beta\sqrt{e+4f}\,d\le\beta\sqrt{2N-S}\,d$. (Checked on 3000 random
abstract configurations, section [5].)
(d) *Comparison side.* $\|AW^2+W^2A\|_2\le2\alpha\|W^2\|_2$ and $WAW=W^2-WB_mW$. Since
$\operatorname{tr}((WB_mW)^2)=0$, writing $W=(H+iK)/2$ gives
$\|WB_mW\|_2^2=\|HB_mK+KB_mH\|_2^2/8\le\|HB_mK\|_2^2/2\le2\beta^2\|K\|_2^2=2\beta^2\|H\|_2^2$.
Here $\|K\|_2=\|H\|_2$ because $\operatorname{tr}W^2=0$ and the diagonal is null. With
$\|W^2\|_2^2\le\operatorname{tr}H^3/3\le(4N-3S)/3$ (sharpened note (4)) and
$\|H\|_2^2=e+4f\le2N-S$:
$\|\Sigma_A(W)\|_2\le(2\alpha+1)\sqrt{(4N-3S)/3}+\beta\sqrt{2(2N-S)}$.
(e) *Assembly.* $|2\Re\operatorname{tr}[(\Sigma_A(V)-\Sigma_A(W))Z^*]|\le\sqrt2\,d(\|\Sigma_A(V)\|_2+\|\Sigma_A(W)\|_2)$.
Finally $\Delta-d^2+6\alpha d^2\le6\alpha\Delta$. ∎

For $\operatorname{tr}G=N+o(N)$, the inherited height-collar reduction applies without
change: only $-L$ sees $M-N$. In scalar form, use $2-s\le D$ and $(4-3s)/3\le D-2/3$.
Then
$$\kappa_a\le6\alpha\delta+\sqrt\delta\,C,\qquad C=3\beta\sqrt D+\sqrt2\sqrt{Q_A}+\sqrt2(2\alpha+1)\sqrt{D-2/3},$$
with $\delta=S/N-(2-D)$, $Q_A=\lim\|\Sigma_A(V)\|_2^2/N$, and $\kappa_a=-\lim\operatorname{tr}(Ap(G))/N$.

### 5.2 Marked ordered energy

$\Sigma_A(V)(x,z)=\int_{x>y>z}(a_x+a_y+a_z)V(x,y)V(y,z)dy$. So $\|\Sigma_A(V)\|_2^2$ is
the inherited ordered quartic (1) with vertex weight
$w=(a_x+a_y+a_z)(a_x+a_t+a_z)$. Inserting $w$ into each contraction of the inherited
(9) gives
$$\begin{aligned}Q_A={}&\tfrac16\!\int9a^2u^4+\tfrac13\!\int_{x>y}(x-y)\big[2u_x^2u_y^2(a_x+2a_y)(2a_x+a_y)+u_xu_y^3(a_x+2a_y)^2+u_x^3u_y(2a_x+a_y)^2\big]\\
&+\!\int_{v,w>0}\!vw\!\int\big[u_\top u_{z+w}u_{z+v}u_z(a_\top+a_{z+w}+a_z)(a_\top+a_{z+v}+a_z)+u_\top u_{z+w}^2u_z(a_\top+a_{z+w}+a_z)^2\big]dz,\end{aligned}$$
with $\top=z+v+w$. At $a\equiv1$ this is $9Q$ (CHECKED exactly, section [6]).

### 5.3 Analytic inputs and their status

* (I1) $\operatorname{tr}(M_aG^k)/N\to$ the $k$-level values with symbol
  $a(x)u(x)u(y)u(z)$ ($k\le3$). This is the same smooth-symbol explicit-formula
  calculation the repository uses for $M_3$, with one extra bounded smooth factor; the
  support is the hexagon (Prop. 1.1). Status: inherited (ordinary derivation, not
  formalised, not re-audited here).
* (I2) $\|\Sigma_A(V_T)\|_2^2/N\to Q_A$. This is the inherited orthant/ordered transfer
  (ordered_moment §§1–5) with $\Psi$ multiplied by the smooth vertex weight $w$. Support
  and constants are unchanged. Status: the same as the inherited $Q$ transfer. The
  collapse bookkeeping of §5.2 is mine and reduces correctly at $a\equiv1$.
* Profile and mark limits: smooth profiles of width $<1$, and correspondingly rescaled
  smooth marks, approximate the polynomial ones in $L^4$. All functionals are continuous
  there, so the strict scalar margin persists, as in the inherited argument.
* No RH, no full fourth moment, no effective block dimension.

### 5.4 Exact certificate (CHECKED)

Profile: the repository's degree-12 rational polynomial. Mark:
$a=\sum_{j=0}^{12}\alpha_jP_{2j}(2x)-\frac1{250000}$, with the 13 rational $\alpha_j$
(denominator $10^{12}$) listed in the script. Sturm counts give
$0<1-a<\beta=\frac{6001}{5000}$ on $[-\frac12,\frac12]$, so $\alpha=1$. Exact rational
integration (sympy in 1D; Grundmann–Möller rational rules in 2D and 3D, exact for
degree 99, cross-checked against a second exact rule) gives

| quantity | value |
|---|---|
| $D$ | 1.3274992970376471 |
| $\kappa$ (unmarked) | 0.0117776203966976 |
| $\kappa_a$ | 0.0202278132161081 |
| $Q$ (unmarked, $=Q_A/9$ at $a\equiv1$) | 0.3989636506914728 |
| $Q_A$ | 1.6234380071702812 |
| $C$ (rational ceiling) | 9.3993289381 |

and $(\kappa_a-6\delta_0)^2-\delta_0C^2=1.62\cdot10^{-7}>0$ for $\delta_0=1/216600$. Since
$6\delta+\sqrt\delta C$ is increasing in $\delta$, this gives $\delta>\delta_0$ and
$$\liminf N_0^s/N\ge2-D+\tfrac1{216600}=0.6725053197675>0.672505319.$$
Comparison with the same exact data and no mark: $1/271803$, i.e. $0.6725043820976$.

### 5.5 Optimisation (NUMERICAL)

For fixed $\beta$, $\kappa_a$ is linear in $a$ and $Q_A$ is a convex quadratic. A sweep
of concave QPs $\max\kappa_a-\mu Q_A$ (cvxpy), with constraints $1-\beta\le a\le1$ on a
grid, traces the Pareto frontier over even polynomial marks. Increment ratio over the
unmarked $1/271803$ (repository profile):

| mark degree in $x$ | 12 | 16 | 20 | 24 | 32 | smoothed step |
|---|---|---|---|---|---|---|
| ratio | 1.201 | 1.222 | 1.240 | 1.256 | 1.267 | ≈1.28 (cosine profile) |

The optimum is a near-step: $a\approx1$ for $|x|\lesssim0.28$ and $a\approx-0.2$ to
$-0.3$ near the ends, with $\beta\approx1.2$–$1.3$. Joint re-optimisation of the profile
was not done. On the unmarked problem it moved the increment by only 0.04%.

What limits the gain: the terms $3\beta\sqrt D$ in $C$, from (c) and (d), cost about
$4.2$ of $C\approx9.4$. If they could be removed, the same data would give
$\delta\approx(\kappa_a/5.3)^2\approx1.5\cdot10^{-5}$. That figure is a rough estimate;
no improved bound is proved. The ceiling on the defect itself is
$\kappa_a\le\int|d|\approx2.26\kappa$.

## 6. Feasibility and adversarial self-check

* **Like with like.** The new bound uses the same profile, the same $D$, and the same
  inherited transfers as the frontier. Only the mark is new. At $\beta=0$ the theorem
  is the inherited one, and the script reproduces the inherited exact data and margin.
* **Cherry-picking.** The exact certificate uses a numerically optimised mark. That is
  legitimate: any admissible mark gives a valid bound. The reported number is the
  exactly verified one, not the optimiser's value.
* **Gaps.** (1) The marked transfers (I1)–(I2) are asserted by analogy with the
  inherited proofs and were not independently audited. They inherit that status. In
  particular the overall result is no stronger than the inherited 0.6725043821 claim.
  (2) Proposition 3.2 is proved for the flat window; the cosine is interval-checked only
  at specific $B$. (3) Proposition 4.1 concerns an abstract direct-sum class, not literal
  interacting zeros. (4) The CUE check is a sanity check, not evidence for zeta.
* **Not progress toward 85%.** Within $\sum|\xi|<2$, triple data is mock-Gaussian. On
  its own (three moments, or linear spectral use) it certifies nothing beyond $2-D$, by
  Obstructions A and B. It acts only through the fourth-order ordered energy, in the
  quadratic-in-$\kappa$ regime $\delta\approx(\kappa_a/C)^2$. Even ideal marks
  ($\kappa_a\le2.26\kappa$) and ideal constants leave increments around $10^{-5}$.

| input | used in | status |
|---|---|---|
| RS smooth $n$-level, complex ordinates, $\sum\lvert\xi\rvert<2$ | §§1–2, I1 | inherited (ordered_moment §§1–5), unconditional per that note |
| ordered orthant transfer with smooth vertex weights | I2 | inherited argument, marked extension not re-audited |
| rank–trace decomposition, comparison $H$, (3),(4) of sharpened note | Thm 5.1 | inherited, independently audited there; marked steps proved here |
| Theorem 5.1 | §5 | PROVED (finite operator algebra) |
| scalar certificate $1/216600$ | §5.4 | CHECKED (exact rationals) |
| Obstruction A | §3 | PROVED (flat), CHECKED (interval; flat, cosine) |
| Obstruction B | §4 | PROVED (abstract class) |
