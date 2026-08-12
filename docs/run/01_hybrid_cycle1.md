# Hybrid cycle 1: a de-overlapped mollifier--pair-correlation certificate

## Outcome

The scalar conclusions of the two methods cannot be added: the accepted pair-correlation theorem already gives

\[
\frac{N_{0}^{s}}N\ge \beta_\star,
\qquad
\beta_\star=2-C_\star=0.6725007036\ldots,
\]

where

\[
C_\star=\frac1{c_\star}
=\frac12+\frac1{\sqrt2}\cot\!\frac1{\sqrt2}
=1.3274992963\ldots .
\]

The PRZZ/Levinson--mollifier result supplies a set of at least

\[
L=\kappa N+o(N),\qquad \kappa=0.407511,
\]

simple critical-line zeros, but this set can lie wholly inside the already-certified (67.25\%\).  A useful hybrid must therefore measure overlap rather than add proportions.

There is a clean way to do that.  Remove the mollifier-certified simple-zero atoms from the accepted Gram matrix and apply the accepted rank--trace inequality to the residual matrix.  This gives an exact joint certificate.  It reaches (85\%\) once one new **mixed selector-correlation inequality** is proved:

\[
\boxed{
2\,\operatorname{tr}(G_TK_T)-\|K_T\|_F^2-\operatorname{tr}K_T
\ \ge\ (0.1774992964-o(1))N.
}
\tag{H85}
\]

Here (G_T) is the optimized matrix from the accepted PDF and (K_T) is the sum of its rank-one atoms over a mollifier-certified set of simple critical-line zeros.  This is the single missing lemma on this route.

Under the natural thinning law for the mollifier-selected zeros, the left side of (H85) is

\[
0.2125328904\ldots N,
\]

and the resulting rigorous algebraic output would be

\[
\frac{N_0^s}{N}\ge 0.8850335940\ldots .
\]

Thus (85\%\) needs only (83.5162\%\) of the thinning benchmark; the mixed estimate can lose (0.03503359N) and still close.

## 1. Why all scalar hybrids stall at (0.6725)

Use the zero populations from the accepted matrix decomposition:

- (s): simple critical-line points;
- (d): distinct multiple critical-line points;
- (p): off-line symmetric pairs.

Ignoring (o(N)) boundary terms, the two relevant constraints are

\[
N\ge s+2d+2p
\tag{1}
\]

and the optimized rank--trace charge

\[
3s+4d+4p\ge (4-C_\star)N.
\tag{2}
\]

They imply (s\ge (2-C_\star)N=\beta_\star N).  Equality is attained by the adversarial population

\[
s=\beta_\star N,
\qquad
d=\frac{C_\star-1}{2}N=0.1637496482\ldots N,
\qquad
p=0,
\tag{3}
\]

with every multiple point double.  It also has

\[
N_d=s+d=\frac{3-C_\star}{2}N=0.8362503518\ldots N,
\]

exactly the accepted distinct-zero constant.  The mollifier demand (s\ge0.407511N) is slack in (3).  The accepted (\xi'\) proportion is also compatible: generically there is one simple real zero of (\Xi') between consecutive distinct real zeros of (\Xi), plus one at every double zero of (\Xi), giving asymptotically (N) simple line zeros of (\xi') in this adversarial model.

Consequently, no linear program using only the published scalar proportions for (\zeta), (\xi'), distinctness, and Levinson-selected zeros can exceed (\beta_\star).  A cross statistic is mandatory.

## 2. Residual-matrix construction

Work in one trimmed dyadic window and in the optimized normalization of the accepted PDF.  Boundary losses are (o(N)).  For every simple critical-line zero (\rho\), let

\[
B_\rho=u_\rho u_\rho^*\succeq0,
\qquad
\operatorname{tr}B_\rho=1+o(1)
\]

be its normalized rank-one atom in the zero-side matrix.  Let (\mathcal L_T\) be a set of mollifier-certified simple line zeros with

\[
|\mathcal L_T|=L=\kappa N+o(N),
\]

and define

\[
K_T:=\sum_{\rho\in\mathcal L_T}B_\rho,
\qquad
R_T:=G_T-K_T.
\tag{4}
\]

After the same harmless truncation used in the PDF, (R_T) is exactly the matrix of the residual zero configuration: the selected (L) simple atoms have been deleted, and every multiple-line and off-line block is untouched.  Its residual zero mass is

\[
N_R=N-L.
\tag{5}
\]

Let (s_R) be the number of residual simple line zeros.  Proposition 4.4(ii) of the accepted machinery, applied to (R_T), gives

\[
s_R\ge4\operatorname{tr}R_T-\|R_T\|_F^2-2N_R-o(N).
\tag{6}
\]

The accepted prime-side estimates and (4) give

\[
\operatorname{tr}G_T=N+o(N),
\qquad
\|G_T\|_F^2=C_\star N+o(N),
\qquad
\operatorname{tr}K_T=L+o(N).
\tag{7}
\]

Since all selected zeros are themselves simple and on the line,

\[
N_0^s\ge L+s_R.
\]

Insert (4)--(7) into (6):

\[
\begin{aligned}
N_0^s
&\ge L+4(N-L)-\|G_T-K_T\|_F^2-2(N-L)-o(N)\\
&=2N-L-\|G_T-K_T\|_F^2-o(N)\\
&=(2-C_\star)N
 +2\operatorname{tr}(G_TK_T)-\|K_T\|_F^2-L-o(N).
\end{aligned}
\tag{8}
\]

Define normalized mixed moments

\[
x_T:=\frac{\operatorname{tr}(G_TK_T)}N,
\qquad
q_T:=\frac{\|K_T\|_F^2}N.
\tag{9}
\]

Then (8) is the joint certificate

\[
\boxed{
\frac{N_0^s}{N}
\ge \beta_\star+2x_T-q_T-\kappa-o(1).
}
\tag{JC}
\]

This is an actual union certificate: the last three terms are precisely the amount by which the mollifier-selected set forces the rank--trace argument to certify zeros outside that set.

Equivalently, writing (G_T=K_T+R_T), its gain over (0.6725) is

\[
\underbrace{\bigl(\|K_T\|_F^2-\operatorname{tr}K_T\bigr)}_{\text{within-selector off-diagonal energy}}
+2\underbrace{\operatorname{tr}(K_TR_T)}_{\text{selector--complement energy}}.
\tag{10}
\]

## 3. Exact (85\%\) threshold

From (JC), (N_0^s/N\ge0.85-o(1)) follows if

\[
2x_T-q_T-\kappa
\ge 0.85-\beta_\star
=C_\star-1.15
=0.1774992963\ldots .
\tag{11}
\]

For (\kappa=0.407511), this is

\[
\boxed{2x_T-q_T\ge0.5850102963\ldots .}
\tag{12}
\]

No separate lower bounds for (x_T) and upper bounds for (q_T) are logically required; only their favorable combination occurs in the proof.

## 4. Thinning benchmark and margin

The optimized total second moment splits into unit diagonal mass and excess pair energy:

\[
\|G_T\|_F^2/N=1+(C_\star-1)+o(1).
\]

If the mollifier-certified set is equidistributed through this pair energy like a density-(\kappa) thinning, then

\[
q_{\mathrm{thin}}
=\kappa+\kappa^2(C_\star-1),
\qquad
x_{\mathrm{thin}}
=\kappa C_\star.
\tag{13}
\]

At (\kappa=0.407511),

\[
q_{\mathrm{thin}}=0.4618972411\ldots,
\qquad
x_{\mathrm{thin}}=0.5409705657\ldots,
\]

and hence

\[
2x_{\mathrm{thin}}-q_{\mathrm{thin}}-\kappa
=\kappa(2-\kappa)(C_\star-1)
=0.2125328904\ldots .
\tag{14}
\]

The joint bound becomes

\[
\beta_\star+0.2125328904\ldots
=0.8850335940\ldots .
\tag{15}
\]

Thus the proof needs only

\[
\frac{0.1774992963\ldots}{0.2125328904\ldots}
=0.8351615\ldots
\]

of the thinning score.  Put differently, the mixed moment may fall short of (13) by (0.0350335940N) and still prove (85\%\).

The same computation at optimized bandwidth (\lambda\) uses

\[
c_\lambda^*
=\frac{\sqrt2\tan(\lambda/\sqrt2)}{1+(\lambda/\sqrt2)\tan(\lambda/\sqrt2)},
\qquad C_\lambda=1/c_\lambda^*.
\]

Under thinning the hybrid output simplifies to

\[
B_{\mathrm{thin}}(\lambda,\kappa)
=2-C_\lambda+\kappa(2-\kappa)(C_\lambda-1)
=1-(1-\kappa)^2(C_\lambda-1).
\tag{16}
\]

For (\kappa=0.407511):

| (\lambda) | base (2-C_\lambda) | thinning hybrid | fraction of thinning gain needed for (0.85) |
|---:|---:|---:|---:|
| 1.00 | 0.672501 | 0.885034 | 0.8352 |
| 0.95 | 0.635679 | 0.872107 | 0.9065 |
| 0.90 | 0.593102 | 0.857160 | 0.9729 |
| 0.87846 | 0.57273 | 0.85000 | essentially 1 |

Therefore shortening the pair-correlation bandwidth below about (0.8785) cannot reach (85\%\) even under exact thinning.  The arithmetic attack should keep (\lambda\) near (1), rather than buying a much easier mixed moment at small support.

## 5. The exact missing lemma

The route closes if one proves the following statement for a canonical set (\mathcal L_T\) of (\kappa N+o(N)) simple critical-line zeros produced by the Levinson/PRZZ construction.

**Selector-correlation lemma.**  With (K_T\) defined by (4) using the same optimized window as (G_T),

\[
2\operatorname{tr}(G_TK_T)-\|K_T\|_F^2-\operatorname{tr}K_T
\ge (C_\star-1.15-o(1))N.
\tag{17}
\]

In zero-pair language, if

\[
\mathcal K_T(\rho,\rho'):=\operatorname{tr}(B_\rho B_{\rho'})
\]

with the symmetric-block interpretation for off-line zeros, then the left side is the single signed two-level statistic

\[
2\sum_{\rho\in\mathcal L_T}\sum_{\rho'}m_{\rho'}\mathcal K_T(\rho,\rho')
-\sum_{\rho,\rho'\in\mathcal L_T}\mathcal K_T(\rho,\rho')
-\sum_{\rho\in\mathcal L_T}\mathcal K_T(\rho,\rho).
\tag{18}
\]

The diagonal in the last sum is (L+o(N)).  Formula (18), not a new global proportion estimate, is the arithmetic object that must be evaluated or bounded.

## 6. Most direct next attack

1. **Make the selector canonical.**  In the PRZZ simple-zero argument, retain one simple Hardy-(Z) zero from each certified sign-change interval and discard a boundary strip of width (T^{1/2}).  This produces an actual set (\mathcal L_T\), not a soft density.

2. **Insert the optimized reproducing kernel before the Levinson contour shift.**  Fourier-expand (\mathcal K_T(\gamma-\gamma')) and write the two sums in (18) as a mollifier-weighted zero sum with one insertion of (-\zeta'/\zeta).  Keep the favorable combination (2x-q) intact; estimating (x) and (q) separately throws away cancellation and demands stronger input.

3. **Target only the numerical inequality (12).**  The thinning values are (2x-q=0.6200438904\ldots); only (0.5850102963\ldots) is needed.  Error terms and exceptional sign-change intervals have a total budget of (0.0350335940N).

4. **Keep effective bandwidth at least (0.90), preferably (1).**  Table (16) shows the hybrid loses all numerical slack below (0.8785).  If the mollifier insertion forces a length tradeoff, split the optimized kernel into a (0.90)-band main piece plus a positive tail and prove the main-piece mixed estimate to at least (97.3\%\) of its thinning value.

5. **If the hard selector blocks the contour calculation, prove an averaged selection lemma.**  It is enough to construct a family of PRZZ-certified sets (\mathcal L_T(\omega)) for which the average of the left side of (17) meets the threshold; one member then does.  Random deletion can be used after certification because for a retained probability (r), the expected gain is

\[
2r(x-\kappa)-r^2(q-\kappa),
\]

which can be optimized in (r\) without changing the zero-side proof.

## 7. Decision for orchestration

Continue this route only through the selector-correlation lemma (17).  Do not spend another cycle combining headline percentages: configuration (3) proves that such combinations cannot move the constant.  The next useful deliverable is either:

- a contour/Dirichlet-polynomial formula for (18) with all main terms exposed, or
- any unconditional lower bound for (18) exceeding (0.1774992964N).

Once either is obtained, (8)--(12) immediately convert it into the requested (85\%\) theorem.
