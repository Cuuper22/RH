# Exact terminal kernel versus the reduced additive bandpass

Date: 2026-09-05. Ordinary analytic audit; no new zero proportion.

This note fixes the normalization interface between the accepted zeta trace
and the additive bandpass model in `mobius_energy_20260905.md`. It also
records why the existing local arithmetic estimates do not yet imply the
terminal theorem.

## The inherited terminal form

For real coefficient sequences `c,d` supported on `n<=X`, define

\[
 \mathcal O_T(c,d)=\frac1{2\pi^2}
 \sum_{n\ne m\le X}\frac{c(n)d(m)}{\sqrt{nm}}
 A^-_\Phi(T;\log n,\log m),                              \tag{1}
\]

where

\[
 A^-_\Phi(T;y,y')=\int_{-T}^{T}\Phi(x)^2
 \int_{T+x_-}^{2T-x_+}\cos(xy+t(y-y'))\,dt\,dx .        \tag{2}
\]

This is exactly the accepted PDF/Lean `O1` kernel (`PPOffDiag` and
`PPKernel`), not a heuristic replacement. With
`r_R=Lambda-Lambda_R`, bilinearity gives

\[
 \mathcal O_T(\Lambda,\Lambda)
 =\mathcal O_T(\Lambda_R,\Lambda_R)
  +2\mathcal O_T(\Lambda_R,r_R)
  +\mathcal O_T(r_R,r_R).                               \tag{3}
\]

For `phi(y)^2=u(y/ell)` and `integral u=1`, the accepted normalization is

\[
 aL=\ell,\qquad g(y)=\ell A_u(y/\ell),\qquad
 Q_T=\ell^2N(T,2T)\sim\frac{T\ell^3}{2\pi}.             \tag{4}
\]

Thus the diagonal cost `D_diag` and the terminal allowance
`1.15-D_diag` in the arithmetic note are normalized correctly.

## The present reduced form is a different kernel

For one additive block, the current research controls variants of

\[
 E_{\rm off,Z}=\sum_{n\ne m}r_R(n)r_R(m)W(n/Z)W(m/Z)K_R(n-m), \tag{5}
\]

with

\[
 K_R(h)=\frac1R\int\chi(v)e(hv/R)\,dv.                  \tag{6}
\]

Equations (1) and (5) are not equal. The terminal kernel depends on
`log(n/m)`, `sqrt(nm)`, `g(log n)`, and moving height endpoints. The reduced
kernel depends only on `n-m`. In particular, the same additive shift at two
different basepoints has a different terminal phase.

After a genuinely narrow localization around `n,m~z`, the formal leading
scale is

\[
 R_z=\frac{2\pi z}{T},
\qquad
 \mathcal O_{T,z}(r_R,r_R)
 =2g(\log z)E_{\rm off,z}+o(\text{local scale})
 =2\ell A_u(\log z/\ell)E_{\rm off,z}+\cdots .          \tag{7}
\]

The exact variables are `z=T R_z/(2pi)` and, in exponent notation,
`R_z=(T/(2pi))^eta`; the simplified `z=TR`, `R=T^eta` convention omits
these constants.

Formula (7) shows that one local estimate `E_off=O(T ell)` contributes only
`O(T ell^2)=o(Q_T)`. It does **not** make the complete terminal residual
negligible: the full range contains logarithmically many scales and their
cross terms.

## Precise missing bridge theorem

A valid transfer must simultaneously:

1. localize the Mellin phase `log(n/m)` by a variable-bandwidth symbol or
   shrinking relative windows, with the endpoint and nonlinear phase errors
   controlled;
2. control neighboring-window cross terms and sum the logarithmic family of
   blocks over `T<z<X`;
3. work uniformly with the varying cutoff `R_z`, rather than only at
   `eta=.49`;
4. restore the model and mixed terms in (3), not just the residual square;
5. subtract the exact bandpass diagonal, because (1) excludes `n=m` while
   the positive bandpass norm includes it.

A fixed-width dyadic linearization is insufficient: replacing `log(n/m)` by
`(n-m)/z` over `n,m~z` leaves order-one phase error at height `T`. No
inherited file proves the required shrinking-window or semiclassical
Mellin-to-additive localization with its cross-block bounds.

Consequently the positive packet norm in Section 19 of the arithmetic note
has neither a terminal sign nor a percentage cost at present. Dividing its
`T log T` scale directly by `Q_T`, or multiplying it by an assumed two-log
factor, are both unjustified. The missing object is the explicit theorem
above, together with the two other terms in (3).

## Why the rational packet projection cannot simply tile the band

There is also a quantitative obstruction inside one additive block. At the
balanced scale put `Q=C=sqrt(Z)=T^.745`, `R=T^.49`. Farey cells of order
`Q` form an exact partition and the cell around `a/r`, `r~P`, has width at
most `1/(PQ)`. The arithmetic result in Section 21 of the Möbius note controls
only the natural packet width `1/Z=1/Q^2`. Tiling one cell therefore needs
`Q/P` natural translates.

Even grant, optimistically, the same Section 21 estimate on every translate.
For `D<=M`, its primitive-frequency bound and the prime large sieve give the
natural-packet shell estimate

\[
 B_{\rm nat}(P)\ll
 \left(\frac{PQ}{R}+\frac{P^3}{R}\right)T^{o(1)}.      \tag{8}
\]

Multiplying by the cell/packet ratio yields

\[
 B_{\rm cell}(P)\ll
 \left(\frac{Q^2}{R}+\frac{QP^2}{R}\right)T^{o(1)}.   \tag{9}
\]

At the first shell `P=R`, the second term is `QR=T^1.235`, whereas the
desired additive band scale `Q^2/R` has exponent one. Thus a nonnegative
Farey cover recreates exactly the old `T^.235` loss even under a translated
estimate stronger than the one proved.

The translated estimate is in fact unavailable. At
`alpha=a/r+beta`, Poisson completion in `q=dm` shifts the dual box by
`r beta d c`; across a Farey cell the prime variable `c` moves it through
`DC/Q` residue-scale aliases. This destroys the q-only congruence behind the
Section 21 estimate. A lift therefore needs a centered three-variable
`(d,m,c)` dispersion estimate, uniform across the Farey cell, with an extra
`P^2/Q` covariance saving. At `P=R` this is precisely `T^.235`. No packet
partition or nonnegative majorant can manufacture that saving from the
proved marginal estimate alone.

## Exact smooth-height surrogate and the sharp-endpoint obstruction

There is a rigorous partial bridge if the inherited sheared sharp height
interval is first replaced by a fixed `chi in C_c^infinity((1,2))`. Integrating
the `x` variable by Fourier inversion gives the exact smooth-height form

\[
 \mathcal O_T^\chi(c,c)=\frac{T}{\pi}\Re
 \sum_{n\ne m}\frac{c(n)c(m)g(\log n)}{\sqrt{nm}}
 \int\chi(v)e^{iTv\log(n/m)}\,dv .                    \tag{10}
\]

By symmetry, `g(log n)` may be replaced by
`[g(log n)+g(log m)]/2`. On a multiplicative block write
`m=zv_0`, `n=m+h`, `s=Th/z`, and `R_z=2pi z/T`. The exact local symbol is

\[
 K_T(v_0,s)=\int\chi(v)
 \exp\!\left(ivT\log\left(1+\frac{s}{Tv_0}\right)\right)dv . \tag{11}
\]

It is uniformly Schwartz in `s` and

\[
 K_T(v_0,s)=\widehat\chi(-s/v_0)
   +O_A\!\left(T^{-1}(1+|s|)^{-A}\right).             \tag{12}
\]

A rapidly convergent smooth expansion in `v_0` separates (11) into source
weights and ordinary additive kernels at scale `R_z`. These are exactly the
sort of smooth weights allowed in the Section 21 Poisson--Cochrane--Shi
argument. A smooth logarithmic partition has only neighboring block
interactions after Schwartz decay; polarization and a finite coloring handle
them. Although there are `O(log T)` blocks, their bounds grow geometrically:

\[
 \sum_z R_z^2\ll R_{\max}^2.
\]

Thus the transferred low-divisor packet component is
`O(ell R_max^2 T^o(1))=o(Q_T)` for every `eta_max<1/2`. More generally it
retains the thresholds `(1+eta)/4` for the pointwise divisor range and
`3(1-eta)/4` for the packet-projected range. This is a valid partial theorem
for (10), not for the exact inherited kernel (1).

The distinction is essential. Formula (1) has the sharp sheared interval
`t in [T+x_-,2T-x_+]`. Its Fourier transform has a `1/log(n/m)` tail for
`|n-m|>>z/T`; the smooth surrogate is Schwartz and sees only the natural
shift scale. Replacing the sharp interval by an interior smooth cutoff is not
known to be negligible for a polynomial longer than `T`: the generic
mean-value endpoint bound is of size

\[
 T^{1+\eta+o(1)},                                     \tag{13}
\]

against a terminal `T` power scale after suppressing logarithms. Hence no
fixed positive `eta` bridge to the exact `O_1` follows from the current
packet estimates. One must either resolve the `1/h` tail into signed forms at
all shifts `h>=z/T`, or redesign the zero-side/Gabor construction with a
smooth height weight and reprove its rank and trace normalization.

More explicitly, on `n~z` the inherited endpoint weight is bounded by

    (L/z)min(T,z/|h|)+(log L)/z,       h=n-m.          (14)

With `h_0=z/T`, the shell `|h|~2^j h_0` has coefficient
`LT/(2^j z)` but contains `~2^j z/T` shifts. The two factors cancel, so
there is no geometric tail saving without new signed arithmetic input.
The inherited mean-value bound gives `O(L^2z)`, whose ratio to `Q_T` is
`T^eta/ell` up to fixed logarithmic factors. It diverges for every fixed
`eta>0`.

## A tapered Gabor compression removes the sharp-endpoint tail

The last obstruction is not intrinsic to the zero-side matrix. It can be
removed by tapering the **finite Gabor coordinates**, while preserving the
same unconditional zero count. This is different from replacing the prime
kernel after the zero-side argument has already been fixed.

Use the notation of the accepted base proof: the grid spacing is
`h_0=2pi/L`, `tau_k=T+k h_0`, and

    G_(k,l)=W(f_k,f_l),       Ghat=G/(aL^2).

Let `delta=(log T)^(-A)` for a fixed sufficiently large `A`, and choose
`h_T in C_c^infinity((1,2))` with

    0<=h_T<=1,
    h_T=1 on [1+delta,2-delta],
    ||h_T^(j)||_infinity<<_j delta^(-j).               (15)

Put `h_k=h_T(tau_k/T)`, `D_h=diag(sqrt(h_k))`, and

    Ghat_h=D_h Ghat D_h.                               (16)

This normalization is essential: the sampling identity is

    sum_(k in Z)|phihat(gamma-tau_k)|^2=aL^2,

not `aL`. Hence every simple on-line atom in (16) has trace at most one:

    (aL^2)^(-1)sum_k h_k|phihat(gamma-tau_k)|^2<=1.    (17)

The zero decomposition is pulled back by `D_h`. Since this diagonal matrix
may be singular, inertia and rank need not be preserved as equalities, but
they can only decrease. The on-line rank bounds, the one-positive-direction
bound for every off-line pair, and the trace cap (17) therefore remain valid.
The tail trace norm also contracts. Consequently the accepted finite
zero-side argument gives the same form of inequality

    N_0^s(T,2T)
      >=4 tr(Ghat_h)-||Ghat_h||_F^2-2N(T,2T)-o(N).     (18)

The count in the penalty is still the full `N(T,2T)`, not a weighted count.

There is an equally explicit prime-side kernel. Extend `h_T` by zero and
write

    K_h(t,t')=sum_(k in Z)h_k phihat(t-tau_k)phihat(t'-tau_k).

The unweighted sampling formula gives

    K_infty(t,t')=L Phi(t-t').

Subtract `h_T(t/T)K_infty` from `K_h` term by term. The Lipschitz bound in
(15), Cauchy--Schwarz, and the first weighted sampling moment give, uniformly
on the main height range,

    K_h(t,t')=h_T(t/T)L Phi(t-t')
                 +O(L^2/(T delta)).                   (19)

The symmetric formula with `t'` also holds. Their product shows that the
main trace-square kernel is

    h_T(t/T)h_T(t'/T)L^2 Phi(t-t')^2,                  (20)

with a lower-order error under the same envelope estimates as the base
end-effect argument. Large `|t-t'|` is first removed using the decay of
`Phi^2`; no uniform approximation across that discarded range is assumed.

Let

    H_1=int_1^2 h_T(v)dv,       H_2=int_1^2 h_T(v)^2dv.

Then `H_1=1+O(delta)` and `H_2=1+O(delta)`. Direct weighted evaluation, not
a comparison of Frobenius boundary rows, gives

    tr(Ghat_h)=H_1 N(T,2T)+o(N),                       (21)

while the archimedean--archimedean main and the prime diagonal main are
respectively

    H_2[2pi bL int_T^(2T)mu(t)^2dt]+o(Q_T),
    H_2[(T/pi)sum_n Lambda(n)^2 g(log n)/n]+o(Q_T).    (22)

Thus both displayed pieces of `D_diag(u)` are multiplied by `H_2`; the
normalized zero-side expression is

    4H_1-H_2 D-2=2-D+O(delta)                         (23)

when `D` is the complete normalized second-trace cost. Since `delta=o(1)`,
the taper spends no asymptotic part of the strict profile margin. It would
be invalid instead to assert
`||Ghat||_F^2-||Ghat_h||_F^2=o(N)` from the global mean square: the deleted
boundary rows could contain all of the uncontrolled long-polynomial energy.

Finally, after the shear in the prime-prime term, the exact height factor is

    H_(x,T)(t)=h_T(t/T)h_T((t-x)/T).

For `|x|<<delta T`, integration by parts gives

    |int H_(x,T)(t)e^(it xi)dt|
       <<_J T(1+delta T|xi|)^(-J).                     (24)

On a local block `n,m~z`, its additive range is therefore only

    |n-m|<<R_z/delta=R_z(log T)^A.                    (25)

This is a polylogarithmic enlargement of the natural packet. Section 25 of
`mobius_energy_20260905.md` proves a fixed-power retained-beta collar, so
(25) lies wholly inside its valid range for the centered low-divisor
component. The infinite sharp `1/h` shell is gone.

This supplies a valid zero-side-compatible smoothing bridge and removes the
sharp endpoint as a blocker for that component. Section 26 of the arithmetic
note also recombines the twisted principal mode exactly on the first
denominator shell. It does **not** prove the complete tapered trace theorem.
The arithmetic note now also proves the grouped floor estimate and hence
evaluates the complete principal model through every fixed-power collar
`r<=R T^theta`, `theta<eta`. The denominator range beyond that collar, the
high-divisor Type-II energy, cross-block recombination and diagonal
subtraction, and the remaining secondary explicit-formula terms must still
be controlled before (23) can be used with `D<=1.15`.
