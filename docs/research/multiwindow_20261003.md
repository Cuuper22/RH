# Joint certificates over windows, scales and shifts of one zero set

Research note, 2026-10-03. Verifier:
[`verify/multiwindow_certificate.py`](../../verify/multiwindow_certificate.py),
output [`verify/multiwindow_certificate.out`](../../verify/multiwindow_certificate.out).
Status labels: PROVED (argument written here), CHECKED (exact rational
verification), NUMERICAL (floating diagnostics), DERIVED (a computation
obtained by the same method as an earlier note, not independently audited),
CONJECTURE, REFUTED.

## Summary

1. **Second-order joint certificates are closed.** Several windows, scales,
   translations, modulations and cross traces `tr(G_u G_v)` add no
   second-order information beyond the band form factor `F|(-1,1)`.
   Every rank-one, unit-norm feature construction built from them is a
   single mixture window. For real configurations with multiplicities at
   most 2, the loss of every window is fixed once one window's loss is
   known (§2, PROVED). The pair-measure LP converges to `D*` (§2.4,
   NUMERICAL). Off-band Bochner positivity is a real realizability
   constraint (the LP drops to about 1.321). The unconditional rank–trace
   framework cannot use it (§2.5, PROVED for the feature class).
2. **The cubic level gives a genuine joint gain.** If the zero-side slack
   is zero, then `p(G)=G^3-3G^2+2G` vanishes as an operator. So every
   localized trace `tr(p(G)M_phi)` must vanish, where `M_phi` is
   multiplication by a sub-window weight `phi` in the frequency variable.
   The arithmetic local defect density changes sign: it is +0.0516 at the
   centre and -0.0272 at the edges. Its absolute integral is 2.26 times
   the total defect `kappa`. The sharpened ordered-cubic comparison
   extends to diagonal multipliers (§3.2, PROVED). The new ingredient is
   `||W Phi W||_2^2 <= ||phi||_inf^2 ||W||_4^4 = ||phi||^2 tr(H^2K^2)/2
   <= ||phi||^2 tr H^3/3`. An SOCP selects `phi`. With the Taylor-8
   cosine profile and a rational degree-20 multiplier, the scalar step is
   CHECKED exactly:

   $$
   \liminf\frac{N_0^s(T,2T)}{N(T,2T)}\ \ge\ 2-D(u)+\frac1{64200}
   =0.6725162800034\ldots
   $$

   The previous frontier was 0.6725043820976 (increment `1/271803`). The
   new increment is about 4.2 times larger, and the new value lies
   `1.19e-5` above the old one.
   **Gap:** the analytic inputs are vertex-weighted versions of the
   cubic and ordered fourth statistics (§3.3). They are DERIVED by the
   same multilinear explicit-formula computation as
   [ordered_moment §§1–5, 8](ordered_moment_20260905.md), but have not been
   independently audited. The operator lemma has only been sanity-checked
   on random matrices; it is not machine-checked.
3. **Stated limits of this route.** Using different main windows `u` at
   the cubic level reduces to the best single `u` (§4). Test operators
   `X=G_v` need unavailable fourth-level norms (§4). The SOCP optimum
   saturates near `delta ~ 1/63300` for this proof template (§3.4).
   None of this is a step toward 85%.

## 0. Setting

Notation follows [the sharpened memo §1](sharpened_cubic_gain_20260905.md) and
[ordered_moment §1](ordered_moment_20260905.md). Write `z_rho=(rho-1/2)/i`
for the complex zeros, counted with multiplicity. Let `u>=0` be a smooth
density of integral one, supported in an interval of width `<1`. The window
operator on `L^2(R_x)` is

    G_u(x,y) = sqrt(u(x)u(y)) sum_rho m_rho h_T(z_rho/T) e^{iL z_rho (x-y)}.

It decomposes on the zero side as `G=P+B-C` with `P,B,C>=0` and `BC=0`.
Here `tr P<=S`, `rank P<=S`, `rank B<=b`, and `S+2b<=N`. `S` is the
number of simple on-line zeros and `N` the total count. The slack is
`Delta=tr G^2-2N+S`. `F` is the support projection of `B`, `J=I-F`, and
`E` is the positive spectral projection of `J(P-C)J`. Set `H=E+2F`,
`X=G-H`, `d=||X||_2`, and `p(t)=t^3-3t^2+2t`. Since `EF=0`, we have
`p(H)=0`. `V,W,Z` are the strictly lower (Volterra) parts of `G,H,X`,
so that `||Z||_2=d/sqrt2`.

Write `delta=Delta/N`. Then `S/N=2-D+delta` with `D=tr G^2/N -> D(u)`.

## 1. Formulation of the joint problem

*Zero-side model.* A finite multiset of on-line atoms carries
multiplicities `m_j`, with rank-one PSD blocks `m_j v_j v_j*` and
`||v_j||^2=int u=1`. Off-line conjugate pairs give Hermitian rank-two
blocks with one positive and one negative eigenvalue
(`ab*+ba*`, eigenvalues `1 +- sqrt(int u e^{-4pi eta x} int u e^{4pi eta x})`).
The same atoms appear in every `G_u`.

*Statistics vector.* It contains `tr G_u`, `tr G_u^2`, and the cross
traces `tr(G_u G_v)` for windows of any width `<=1`, any scale `u_lambda`,
any translate and any modulation. It also contains cubic traces with
vertex weights, `tr(G_u^2 M_phi)`, `tr(G_u^3 M_phi)` and
`tr(G_u G_v G_w)`, and ordered two-path norms with vertex weights.

*Arithmetic side.* For a cycle with frequency perimeter equal to twice
its range, which is less than 2, the smooth Rudnick–Sarnak computation
gives the limits. Second order: `int f^ (delta+|alpha|)` (Montgomery
band). Third order and ordered fourth order: the polarized functionals
`P,T,Q` of §3.3.

## 2. Second order: reduction and closure

**2.1 (PROVED) Translations and modulations are unitary.** The
translation `u(.-a)` is conjugation of `G_u` by the shift of `L^2(R_x)`.
The modulation `e(beta x)` is conjugation by the multiplication unitary
`M_{e(beta x)}`. All spectra and all single-window certificates are
unchanged. Only cross traces could carry new information.

**2.2 (PROVED) Cross traces and stacking are single windows.**
`tr(G_uG_v)=int int sqrt(u(x)v(x)) sqrt(u(y)v(y)) |K(x-y)|^2` is the
second trace of the (unnormalized) window `sqrt(uv)`. Its support lies in
`supp u ∩ supp v`, so the cross trace never leaves the band. More
generally, take any unit-norm feature map `rho -> w_rho` in a Hilbert
space whose Gram matrix depends only on ordinate differences. Examples are
stacked features `(c_i sqrt(u_i(x)) e(beta_i x) e^{iLz x})_i` with
`sum |c_i|^2=1`. Such a Gram is a continuous positive-definite function
`k` with `k(0)=1`. By Bochner, `k=mu^` for a probability measure `mu`; in
the stacked case `mu=sum |c_i|^2 u_i` and the modulations cancel. Its
second trace is computable from the band if and only if `supp mu` has
width `<=1`. Its atoms have `||w||=1` and `n_+<=1` per pair, so Lemma R
applies verbatim and gives `2-D(mu)<=2-D*`. **Every joint rank–trace
construction from windows, scales and shifts is one window.**

**2.3 (PROVED) One unknown for all windows.** For real configurations
with multiplicities in `{1,2}`, `N=s1+2s2` and `S=s1`. Hence
`S=2N-sum m_j^2` exactly. For every window,

    tr G_u^2 / N = A + E_u,   A = (1/N) sum_j m_j^2,
    E_u = (1/N) sum_{j != k sites} m_j m_k |u^(x_j-x_k)|^2 >= 0,

so `S/N = 2-D(u)+E_u` simultaneously for all `u`. Arithmetic fixes
`D(u)`, so `E_u-E_v=D(u)-D(v)` is forced. The joint linear constraints
`{E_u>=0 for all u}` are implied by `E_{u*}>=0`. Thus the joint
feasibility region of the second-order statistics vector with a given
simple fraction equals the single-window region.

This also answers the "double versus close pair" question. A window of
width `<=1` centred at 0 has `|u^(eps)|^2 >= 1-pi^2 eps^2/2+O(eps^4)`,
uniformly in the window, because `int x^2u<=1/4`. A close pair of simple
zeros at distance `eps` and a double zero therefore have the same
second-order footprint in every admissible window, up to `O(eps^2)`.
Finer scales cannot be reached: bandwidth one is the finest available
resolution. Lemma R equality for `u*` (`E_{u*}=0`) forces all site
differences into the zero set `{s_k}` of `u*^`, where
`s_k = k + sqrt2 tan(1/sqrt2)/(2 pi^2 k)+...`, about `k+0.0612/k`. Such
a configuration is automatically as extremal as possible for every
other window.

**2.4 (NUMERICAL) The pair-measure LP.** The LP has variables `A>=0` and
an even measure `nu>=0` on `R\{0}`. The constraint is
`A f(0)+int f dnu = int f^ (delta+|alpha|)` for hat tests `f^` supported
in `[-1,1]`; the objective is to maximize `A`. Weak duality,
`A<=D(u)` for every window (i.e. Lemma R / Montgomery–Taylor), is
PROVED. The discretized LP fixes the tail beyond `S` to Lebesgue density
1, which costs `~0.08/S`:

| truncation `S` | max `A`, band only | `D*-A` | max `A`, plus `F>=0` on `[1,4]` |
|---:|---:|---:|---:|
| 20 | 1.323184 | 0.00432 | 1.312785 |
| 40 | 1.325472 | 0.00203 | 1.318881 |
| 80 | 1.326457 | 0.00104 | 1.320687 |

The band-only value converges to `D*=1.3274993`. Below `s<11.5`, 98% of
the optimal `nu`'s mass lies within 0.03 of the zeros `s_k` of `u*^`, as
complementary slackness predicts. Large masses beyond `s~30` are
truncation artifacts. This is the dual obstruction for linear
second-order certificates: an atomic pair measure that agrees with all
band data at all scales and has diagonal mass `D*`. It is a pair measure,
**not** a realized point configuration.

**2.5 (PROVED, class obstruction) Off-band positivity is a real
constraint that the unconditional rank–trace class cannot use.** For any
conjugation-closed configuration, `F(alpha)=(1/N)|sum_rho e(alpha z_rho)|^2
>=0` for all real `alpha`. In the LP this cuts `max A` to about 1.321.
This is consistent with the RH-conditional constant 1.3208 discussed in
[certificate_limits](certificate_limits_20260905.md), which was not
re-derived here. The pair adversary of 2.4 is therefore not realizable
by real zeros. However:
(a) By 2.2, every unit-norm PSD-feature operator has
`tr G^2=N int (mu*mu)F` with `mu*mu>=0`. Off-band `F>=0` gives only
*lower* bounds on traces, which is the wrong direction for Lemma R.
(b) The RH-type use takes `f>=0` with `f^<=0` off band and drops
off-diagonal terms. This needs `f(z_j-z_k)>=0` at complex differences.
That fails for conjugate pairs; see the modulation obstruction in
certificate_limits §"Finite weighted pair bounds".
Whether complex configurations with GUE band data can push `S/N` down to
`2-D*` is OPEN.

## 3. Cubic level: localization multipliers

**3.1 Zero slack forces a pointwise identity.** If `Delta=0`, then
`G=H=E+2F` and `p(G)=0`. Hence `tr(p(G)M_phi)=0` for every bounded
multiplier `M_phi`. The 2026-09-05 certificate uses only `phi=1`. Write

    kappa_phi = -lim tr(p(G)M_phi)/N = -[T(u phi,u,u) - 3P(u phi,u) + 2 int u phi].

Then `kappa_phi = int phi c`, with the **local defect density** (DERIVED,
§3.3)

    c(x) = u(x) [u^2 - 2Du - K(u^2) + 3D - 2](x),   K f(x)=int |x-y| f(y) dy,

using the Euler identity `u*+Ku*=D*` for the cosine. This is the density
behind the first variation in the sharpened memo §5. NUMERICAL values
for `u*` (400-node Nyström): `c(0)=+0.05160`, `c(0.2)=+0.02424`, `c(0.3)=-0.00064`,
`c(0.4)=-0.02081`, `c(1/2)=-0.02716`. Also `int c=kappa=0.0117753`,
`int c_+=0.01917`, `int c_-=-0.00740`, and `int|c|=0.02657`.
A near-extremal configuration must therefore be wrong in both
directions locally. The total defect hides part of this through
cancellation.

**3.2 (PROVED) Localized ordered-cubic inequality.** Let `phi` be real
and bounded on the window, `Phi=M_phi`, `||phi||=sup|phi|`, and
`Y(A,B)=Phi AB+A Phi B+AB Phi`. Then

$$
 -\operatorname{tr}(p(G)\Phi)\le 6\|\phi\|\Delta
 +\sqrt\Delta\Big[\sqrt{\Sigma_\phi}
 +\sqrt2\Big(\|Y(V,V)\|_2+3\|\phi\|\sqrt{(4N-3S)/3}\Big)\Big],
$$

where `Sigma_phi = tr(E Phi^2)+4tr(F Phi^2)` satisfies
`Sigma_phi <= min{ ||phi||^2(2N-S), tr(G Phi^2)+sqrt(N Delta)||phi||^2+(N-S)||phi||^2 }`.

*Proof.*
(a) *Exact identity.* Multiplying a strictly lower kernel by a diagonal
multiplier keeps it strictly lower. Cyclic traces of three or more
such factors therefore vanish (Lidskii, or directly an empty
integration region). This includes `tr Z^2`, `tr(Phi Z^2)` and
`tr(Z Phi Z)`. Expanding `(V+V*)^3 Phi` gives
`tr(G^3 Phi)=2Re tr(V* Y(V,V))`, and similarly for `H`. Write
`V=W+Z`, and replace `W*` by `H-W` wherever it multiplies a lower
triangular product. This gives

    tr(p(G)Phi) = tr(R X) + 2Re tr(Z*(Y(V,V)-Y(W,W))) + 2Re tr(H Y(Z,Z)) - 3 tr(X^2 Phi),
    R = Phi H^2 + H Phi H + H^2 Phi - 3(Phi H + H Phi) + 2 Phi.            (3.2)

Section [A] of the verifier checks (3.2) on random strictly lower
matrices; the error is `3e-13`.
(b) *Linear term.* With spectral projections `E,F,Pi_0=I-E-F` of `H`, the
divided differences of `p` on `{0,1,2}` give
`R = 2Pi_0 Phi Pi_0 - E Phi E + 2F Phi F`. The off-diagonal blocks vanish.
As in the sharpened memo, `Pi_0 X Pi_0=-(J(P-C)J)_-`, which has trace
norm `nu`, and `EXE=(J(P-C)J)_+-E`. Hence

    -tr(RX) <= 2||phi|| nu + sqrt(||E Phi E||^2+4||F Phi F||^2) sqrt(||EXE||^2+||FXF||^2)
            <= (||phi||/2)(Delta-d^2) + sqrt(Sigma_phi) d.

Here we used `nu<=(Delta-d^2)/4` from identity (1) of the sharpened memo,
and `||E Phi E||_2^2<=tr(E Phi^2)`. For the bounds on `Sigma_phi`:
`tr(E Phi^2)+4tr(F Phi^2)=tr(H Phi^2)+2tr(F Phi^2)`;
`|tr(X Phi^2)|<=||X||_1||phi||^2<=sqrt N d||phi||^2`, since `X` lives on
the zero span; and `2f<=N-S` and `e+4f<=2N-S`.
(c) *Quadratic terms.* `tr(Y(Z,Z))=0`, so `H` may be replaced by `H-I`,
with `||H-I||<=1`. Each of the three terms is at most
`||phi|| ||Z||_2^2`, which gives `3||phi||d^2`. In addition,
`|3tr(X^2Phi)|<=3||phi||d^2`.
(d) *Main term.* `|2Re tr(Z*(Y_V-Y_W))|<=sqrt2 d(||Y_V||_2+||Y_W||_2)`.
(e) *New lemma.*
`||W Phi W||_2^2 = int int phi(y)phi(y') (W*W)(y,y') (WW*)(y',y) dy dy'
<= ||phi||^2 ||W*W||_2 ||WW*||_2 = ||phi||^2 ||W||_4^4`.
Write `W=(H+iK)/2` with `K=(W-W*)/i`; then
`W*W=(H^2+K^2+i[H,K])/4`. The real part of `tr W^4=0` gives
`tr K^4=4tr H^2K^2+2tr HKHK-tr H^4`. Also `tr((H^2+K^2)[H,K])=0` and
`tr((i[H,K])^2)=2tr H^2K^2-2tr HKHK`. Expanding
`16 tr(W*W)^2` therefore gives **`||W||_4^4 = tr(H^2K^2)/2`**. Then `H^2<=2H` and
`tr(HK^2)=tr H^3/3` (from `tr W^3=0`) give
`||W||_4^4<=tr H^3/3<=(4N-3S)/3`. The verifier checks the identity
numerically (relative error `3e-16`). Hence each of `Phi W^2`,
`W Phi W` and `W^2 Phi` has HS norm at most `||phi|| sqrt((4N-3S)/3)`.
For `Phi=I` this reproves (4) of the sharpened memo.
(f) Collecting terms with `d^2<=Delta`, `(||phi||/2)(Delta-d^2)+6||phi||d^2
<=6||phi||Delta`. ∎

Two remarks. Complex (modulated) `phi` gain nothing:
`Re tr(p(G)M_phi)=tr(p(G)M_{Re phi})`, and the bounds only get worse.
Diagonal multipliers are also the largest class for which this
technique works, because the Hermitian elements of the lower-triangular
nest algebra are exactly the multipliers. One may also split
`phi=c+psi`, using `d^2-Delta<=L<=1.5(Delta-d^2)` for the
`phi=1` part. A scan over `c` showed `c=0` to be optimal for the
multipliers used here.

Scalar form: divide by `N`, write `E_Y(phi)=lim||Y(V,V)||_2^2/N`, and
drop the favourable `-delta` terms:

    kappa_phi <= 6||phi|| delta + sqrt(delta) C_phi,
    C_phi = sqrt(sigma_phi) + sqrt2 ( sqrt(E_Y(phi)) + 3||phi|| sqrt(D-2/3) ),
    sigma_phi <= min{ ||phi||^2 D,  int u phi^2 + (D-1)||phi||^2 + sqrt(delta)||phi||^2 }.

If `kappa_phi > 6||phi||delta_0 + sqrt(delta_0) C_phi`, then
`delta>delta_0`, and the liminf of `S/N` is at least `2-D(u)+delta_0`.
The height-collar, `tr G=N+o(N)` and truncation reductions are those of
the sharpened memo §3. Only the linear term gains an `o(N)`.

**3.3 (DERIVED) Analytic inputs.** All quantities are limits of
vertex-weighted cycle statistics. The cubic statistic `tr(A_1A_2A_3)`
has vertex weights `w_a,w_b,w_c`, and its limit is

    T(w_a,w_b,w_c) = int w_a w_b w_c + K(w_a w_c, w_b) + K(w_a w_b, w_c) + K(w_b w_c, w_a),
    K(f,g) = int int |x-y| f(x) g(y),   P(w_x,w_y) = int w_x w_y + K(w_x,w_y).

The ordered two-path statistic with weights `(w_x,w_y,w_z,w_t)` on the
vertices `x>y>z`, `x>t>z` has limit `Q(w_x,w_y,w_z,w_t)`. It is the
polarization of (9) of ordered_moment:

    Q = (1/6) int w_x w_y w_z w_t
      + (1/3) int_{v>0} v int [ (w_x w_t)(z+v)(w_y w_z)(z) + w_x(z+v)(w_y w_z w_t)(z)
                               + (w_x w_y w_t)(z+v) w_z(z) + (w_x w_y)(z+v)(w_z w_t)(z) ] dz dv
      + int_{v,w>0} v w int [ w_x(z+v+w)(w_y w_t)(z+w) w_z(z)
                             + w_x(z+v+w) w_y(z+w) w_t(z+v) w_z(z) ] dz dv dw.

Each slot assignment was matched against the contractions listed in
ordered_moment §4: one prime pair on slots (1,3), (1,4), (2,3) or (2,4),
and the two perfect matchings. Then
`E_Y(phi)=sum_{a,b} Q(...)`, with `phi` inserted at vertex `x` for
`Phi V^2`, at `y` (respectively `t`) for `V Phi V`, and at `z` for
`V^2 Phi`. Finally `tr(G Phi^2)/N -> int u phi^2`, which is elementary.
The flat value `Q=73/180` and the cosine values `D`, `kappa` and `Q`
are reproduced (verifier [B]).
**Gap (flagged):** the derivation in ordered_moment §§1–5 is linear in
the symbol `Psi(xi)`, and it uses positivity only for the bound (11).
I have checked that the slot bookkeeping carries over to signed smooth
vertex weights with the same strict support gap. This multilinear
transfer has not been independently audited.

**3.4 (NUMERICAL, then CHECKED) Selecting `phi` and the exact
certificate.** For fixed `u` and `c=0`, maximizing `kappa_phi/C_phi` is
a second-order cone program. `kappa_phi` is linear in `phi`, `E_Y` and
`int u phi^2` are PSD quadratic forms, and `||phi||` is a sup-norm.
Results in an even Legendre basis (verifier [E]; the `K=0` row uses the
`c=0` bound, which is worse than the memo's one-sided treatment of
`phi=1`):

| degree of `phi` | 0 | 4 | 8 | 12 | 16 | 20 |
|---|---:|---:|---:|---:|---:|---:|
| `(kappa_phi/C_phi)^2` | 1/382317 | 1/81961 | 1/67188 | 1/64599 | 1/63930 | 1/63592 |

The optimal `phi` is close to 1 in the middle and close to -1 near the
edges: `phi(0)=0.99913` and `phi(1/2)=-0.954`.

CHECKED (verifier [C], exact rationals). Take
`u=p_8/int p_8` with `p_8=1-x^2+x^4/6-x^6/90+x^8/2520`; then
`p_8>=3/4` and `2-D(u)` agrees with `2-D*` to `4e-18`. Take `phi` to be
the rational degree-20 polynomial listed in the verifier. Then:

* `sup|phi| <= 1.00017970` (exact Bernstein subdivision),
* `kappa_phi = 0.025729366954...`, `E_Y = 1.942052790...`,
  `int u phi^2 = 0.814313237...`,
* `C_phi <= 6.4908014`, `q=6 sup|phi| <= 6.0010783`, and
  `(kappa_phi-q/64200)^2-(1/64200) C_phi^2 > 9.6e-7 > 0`.

Hence `delta>1/64200`, giving **`liminf N_0^s/N >= 2-D(u)+1/64200 =
0.6725162800...`** As a control, the same code with `phi=1` and the
memo's inequality (6) excludes `delta<=1/272000`, reproducing the
2026-09-05 constant.

## 4. What the multiwindow angle does not give

* *Different main windows at the cubic level (PROVED).* Window `v` has
  slack `delta_v = delta_u + D(v)-D(u)`. A joint cubic certificate over
  main windows is therefore the single-window objective optimized over
  `u`, which the sharpened memo §6 already did. Its gain there was
  `1/271908 -> 1/271803`. Re-optimizing `u` jointly with `phi` was not
  attempted; the expected effect is of the same tiny order.
* *Test operators `X=G_v`.* `tr(p(G_u)G_v)` is band-available, but the
  remainder needs `||G_v||_op` or alternating fourth-level norms such as
  `||V_u V_v^*||_2`. These are outside the RS range.
* *Saturation.* For this proof template the SOCP value converges to about
  `1/63300`. A larger gain needs a sharper inequality, for example a
  one-sided treatment of the `E`/`F` blocks for `phi!=1`, or new
  arithmetic.
* *Scale.* The increment `1.6e-5` over Montgomery–Taylor is about
  `10^-4` of the distance to 85%. None of this is evidence for 85%.

## 5. Adversarial self-check

* *Like with like.* The baseline, profile and analytic machinery are
  those of the 2026-09-05 frontier. The only new inputs are
  vertex-weighted versions of the same statistics. The `phi=1` control
  reproduces the old constant in the same code.
* *Cherry-picking.* Every SOCP degree is reported. The certified `phi`
  is the degree-20 optimum, rounded to rationals at `10^-7`, and the
  bound is re-verified for the rounded polynomial, including its exact
  sup-norm (which exceeds 1 and is used as such).
* *Assertion–evidence gaps.*
  (i) The multilinear analytic transfer (§3.3) is the main gap.
  (ii) The operator lemma (§3.2) is a written proof, with finite-matrix
  sanity checks only. It uses the continuous-kernel facts that the
  2026-09-05 audit accepted: vanishing triangular traces and the
  halving of HS norms.
  (iii) Smooth profiles of strict width `<1` approximate `u` and `phi`.
  `kappa_phi` and `E_Y` are bounded multilinear functionals in `L^4`, and
  the sup-norms do not increase under restriction, so the strict margin
  persists.
  (iv) The pair-level statements in §2.4–2.5 marked NUMERICAL are
  truncated LPs. They are not used in the certificate.
* *What would refute §3.* An error in the `R` block formula, in the
  `||W||_4^4` identity, or in the slot assignment of `Q`. The first two
  are checked to machine precision. For the third, the flat and cosine
  reproductions check only the diagonal (`phi=1`) case of the
  polarization; the weighted case relies on the bookkeeping in §3.3.
