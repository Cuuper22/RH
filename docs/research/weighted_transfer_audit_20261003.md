# Referee audit: vertex-weighted transfers behind the 1/64200 and 1/216600 increments

Audit, 2026-10-03. Audited notes:
[multiwindow](multiwindow_20261003.md) §3, which uses a diagonal multiplier
`phi` and claims `1/64200`, and
[triple correlation](triple_correlation_20261003.md) §5, which uses a mark
`a` in `[1-beta,1]` and claims `1/216600`. The inherited source is
[ordered_moment](ordered_moment_20260905.md) §§1–5 and §8, with the
operator step of [sharpened](sharpened_cubic_gain_20260905.md).

Independent verifier:
[`verify/weighted_transfer_audit.py`](../../verify/weighted_transfer_audit.py),
output [`.out`](../../verify/weighted_transfer_audit.out). It copies only the
polynomial coefficients from the audited scripts. Every functional is coded
from the derivation in §3 below, for a general (non-factorized) vertex
integrand.

Labels: PROVED (argument given or checked line by line here), CHECKED
(verified numerically with a margin far above the error), NUMERICAL,
CONJECTURE, REFUTED.

## 0. Verdicts

| claim | verdict |
|---|---|
| weighted cubic limit `tr(p(G)M_phi)/N`, mark `a` (both memos) | **PROVED**, with exactly the status of the inherited unweighted cubic transfer |
| weighted ordered fourth energy `E_Y(phi)`, `Q_A` | **PROVED**, with exactly the status of the inherited `Q` transfer (ordered_moment §§1–5) |
| Fourier support after weighting | no enlargement; **no band-limiting needed**; the polynomial `phi` and the mark are admissible as they stand |
| operator lemma `‖WΦW‖₂² ≤ ‖φ‖∞²‖W‖₄⁴`, `‖W‖₄⁴ = tr(H²K²)/2 ≤ tr H³/3` | **PROVED** (re-derived); identities CHECKED |
| multiwindow Thm 3.2 and triple Thm 5.1 (finite inequalities) | **PROVED** (each step re-derived; no sign or factor error found) |
| numerical inputs of both certificates | **CHECKED** independently, agreeing to ≤ 4e-13 |
| multiwindow: `liminf N_0^s/N ≥ 2-D(u_8)+1/64200 = 0.6725162800034…` | **PROVED** (same status as the 1/271803 frontier) |
| triple: `liminf ≥ 2-D(u_12)+1/216600 = 0.6725053197675…` | **PROVED** (same status); weaker than the multiwindow bound |

No corrected `delta` is needed. With the memos' data the largest certifiable
values are `1/64106.9` (multiwindow) and `1/216514.3` (triple). The stated
values `1/64200` and `1/216600` are therefore safe.

The new frontier is the multiwindow value
`0.6725162800034`. It is `1.19e-5` above `0.6725043820976`, and it carries
exactly the trust level of that older value. Both rest on the ordinary,
unformalized explicit-formula derivation of ordered_moment §§1–5.

## 1. What the inherited derivation proves, and what it relies on

The operator is built from the actual complex zeros. With
`z_ρ=(ρ-1/2)/i`, `|Im z_ρ| ≤ 1/2`, multiplicities `m_ρ`, and a real entire
height weight `h_T`:

```
A_T(x,y) = sqrt(u(x)u(y)) Σ_ρ m_ρ h_T(z_ρ/T) e^{iLz_ρ(x-y)},   L = log T.
```

`h_T` concentrates on `[1,2]`, has `ĥ_T ∈ C_c^∞` supported in `|y| ≤ O(log T)`,
and is power-small off a collar. It is built from a sinc-power B-spline,
§2 eq. (4).

Every cycle statistic is a zero-sum

```
Σ_{ρ_1..ρ_n} Π_j m h_T(z_j/T) ∫ Ψ(ξ) e^{iL Σ_j z_j ξ_j} dξ ,   Σ_j ξ_j = 0 .
```

Here `ξ_j` are the consecutive **differences of vertex positions** and `Ψ`
is the pushforward density of the vertex integrand. For the ordered
two-path statistic, `Ψ` also carries the orthant indicator `1_{++--}`.
Each single sum is then replaced by the zeta explicit formula, giving
archimedean, prime and polar factors (§3).

The following facts are used:

- the RS smooth-height machinery: RS Duke 1996, proof of Thm 3.1,
  Lemmas 3.2–3.10. It is unconditional for ζ and allows complex `z_ρ`,
  because the test `h_T(z/T)e^{iLzξ}` is entire. The sharp-height
  Thm 3.2, which needs RH, is not used;
- unique factorization for the diagonal `M_0=N_0`;
- the partial summation (6);
- `L^4` boundedness of the Hardy projections `P_±`;
- the exact half-line constants `C_0=∫|P_+1_[1,2]|⁴=1/6`,
  `C_1=∫_1^2|P_+1_[1,2]|²=1/3` and `C_2=1`. Re-evaluated numerically in [2]:
  `0.1666666666`, `0.3333333333`.

Support: the orthant identity `Σ|ξ_j| = 2(x-z) ≤ 2λ < 2` gives a fixed
gap. That gap is all that the error reductions §3.1–3.4 use.

**Key structural observation (PROVED by inspection of §§3–4).** After eq.
(3), `Ψ` is never used as a product. §3 needs only:

- `Ψ` is a fixed `C_c^∞` function, supported in `Σ|ξ| ≤ 2-δ`;
- finitely many seminorms of `Ψ` (Taylor step 3, uniform bounds);
- the orthant walls kept as literal half-lines on the archimedean slots.

§4 then evaluates the main terms **linearly** in `Ψ`. Positivity of `Ψ`
enters only in the bound (11), `Q ≤ 0.84`, which neither memo uses.
Therefore §§3–4 prove the following generic statement. Equation (9) is its
specialization to a product `Ψ`.

**Proposition A (generic ordered symbol).** Let `F(x,y,z,t)` be any real
smooth vertex integrand supported in `[-λ/2,λ/2]^4`, `λ<1`, possibly signed.
Write `S_F` for the corresponding statistic

```
S_F = ∫_{x>y>z, x>t>z} F(x,y,z,t) K(x,y)K(y,z)K(z,t)K(t,x),
K(x,y) = Σ m h_T e^{iLz(x-y)}.
```

Then `S_F/N` converges to

```
Q[F] = C_0 ∫F(s,s,s,s)ds
     + C_1 ∫_{v>0} v ∫ [F(X,Y,Y,X)+F(X,Y,Y,Y)+F(X,X,Y,X)+F(X,X,Y,Y)] dY dv ,   X=Y+v,
     + C_2 ∫_{v,w>0} vw ∫ [F(z+v+w,z+w,z,z+v)+F(z+v+w,z+w,z,z+w)] dz dv dw .
```

**Proposition B (generic cubic and pair symbols).** For `F_3(x,y,z)` on the
3-cycle `x→y→z→x`, and `F_2(x,y)` on a 2-cycle, both smooth with support
of width `<1`:

```
lim (1/N)·(3-cycle) = ∫F_3(s,s,s) + ∫∫|x-z| [F_3(x,x,z)+F_3(x,z,z)+F_3(x,z,x)] dx dz ,
lim (1/N)·(2-cycle) = ∫F_2(s,s) + ∫∫|x-y| F_2(x,y) dx dy .
```

This is the "smooth-symbol version" invoked in ordered_moment §8. Three
archimedean slots give `δδ`. One matched prime pair, two minus signs and
an archimedean slot with `ξ=0` give `|v| dv` with coefficient
`∫1_[1,2]^3=1`. Three prime slots cannot satisfy `M_0=N_0` with three
ordinary primes, and prime powers are lower order. There are no half-lines
here, because the 3-cycle is not truncated.

## 2. Fourier support, admissibility of `phi`, signed weights

**Support (PROVED; the concern in the brief does not arise).**
The RS test function on the zero side is
`f(z_1,…,z_n) = ∫Ψ(ξ)e^{iLΣz_jξ_j}dξ`. Its Fourier transform **is** `Ψ`,
a density in the position-difference variables `ξ`.

A vertex weight `φ(x)` multiplies the integrand in **position space**
before the pushforward. So it multiplies `Ψ` pointwise (fibrewise):

```
Ψ_w(ξ) = ∫ w(x,y,z,t) u(x)u(y)u(z)u(t) ds   (z=s, y=s+ξ_2, x=s+ξ_1+ξ_2, t=s-ξ_3).
```

Hence `supp Ψ_w ⊆ {ξ : ξ = vertex differences of points of supp u}`. That
set gives `Σ|ξ| = 2·range < 2` on the orthant, and `max|ξ| = range < 1` on
triangles and pairs. Verifier [1] samples this exactly.

A convolution in `ξ` would appear only if one weighted the **zeros** by a
function of their ordinates. Neither memo does that; the height weight
`h_T` is the inherited one. So no band-limiting of `φ` or of the mark is
required, and nothing is lost.

**Admissibility of a polynomial `φ` (PROVED).** All operators involved are
supported in `supp u × supp u`: `G`, `p(G)`, `H=E+2F`, which lives in the
span of the zero vectors, and `V`, `W`, `Z`, `X`. So only `φ|_{supp u}`
matters. One may replace `φ` by `φ·1_{[-1/2,1/2]}`, a bounded multiplier,
and `‖φ‖∞` means the sup over the window. For smooth `u` of width `<1`,
`φu ∈ C_c^∞` and `Ψ_w` is a fixed `C_c^∞` symbol, so Propositions A and B
apply verbatim.

The certificates use polynomial profiles with jumps at `±1/2`. These are
reached as in the inherited argument. Rescale to width `λ<1`, mollify, and
use `L^4` continuity. Every weighted functional is a bounded multilinear
form in `L^4` on a fixed interval, with constant `≤ C‖w‖∞`. For the
`C_2` term, apply Hölder in `(z,v,w)`, where each factor is an `L^4`
function composed with a measure-preserving shear. Restriction never
increases `sup|φ|`, and keeps the mark inside `[1-β,1]`. The strict scalar
margins therefore persist.

**Signed weights (PROVED).** The transfer is linear in `Ψ`, so sign plays
no role (see §1). The operator inequalities use positivity only in two
places. The multiwindow note uses `|φ| ≤ ‖φ‖`. The triple note uses
`b=1-a ≥ 0`, through `tr(B_m X_00) ≤ 0` and `‖B_m‖ ≤ β`. That holds
because `a ≤ 1`, which [4] confirms independently for the certified mark:
`-0.2000166 ≤ a ≤ 0.9999980`, with grid error below `2e-10`, inside
`(1-6001/5000, 1)`.

**Uniformity.** For fixed smooth `u` and fixed polynomial weight, `Ψ_w`
is one fixed symbol. All error terms are `O_{Ψ_w}(·)` with finitely many
seminorms, exactly as before. The order of limits is unchanged: `T → ∞`
first, then collar, then profile.

**No GUE input.** The main terms come from the explicit formula, not from
sine-kernel statistics. The triple note's phrase "granting the RS/GUE
identification" (Prop. 2.1) is unnecessary for the certificate.

**Collar and truncation.** The cubic difference satisfies
`|tr(p(G)Φ) - tr(p(G_in)Φ)| ≤ ‖φ‖∞ ‖p(G)-p(G_in)‖_1`, with
`‖E_T‖_1 ≪ N T^{λ/2-B}`. Likewise
`‖Y(V_T)-Y(V_in)‖_2 ≤ 3‖φ‖∞ (‖V_T‖_2+‖V_in‖_2)‖E_T‖_1`. Both are negligible.

When `M = tr G ≠ N`, I re-derived identity (1) of the sharpened note:
`Δ_M - d² = 2b_0+k+2h+4ν` with `Δ_M = tr G² - 4M + 2N + S` holds for every
`M`. The multiwindow linear-term bound uses only (1), so it is exact for
every `M`. The triple bound uses `-L ≤ Δ_M - d² + 2|M-N|`, which costs
`o(N)`.

## 3. The collapse (contraction) configurations and their coefficients

The ordered frequencies are `ξ=(x-y, y-z | z-t, t-x)`, with signs `++--`.
A matched prime pair must take one `+` slot and one `-` slot, since
`M_0=N_0`. Each pair leaves one `+` and one `-` archimedean half-line, so
the coefficient is `C_1` for **all four** choices. Both perfect matchings
have coefficient `C_2=1`.

| contraction | constraints | vertex configuration `(x,y,z,t)` |
|---|---|---|
| pair (1,3) | `y=z, t=x` | `(Y+v, Y, Y, Y+v)` |
| pair (1,4) | `y=z=t` | `(Y+v, Y, Y, Y)` |
| pair (2,3) | `x=y=t` | `(Y+v, Y+v, Y, Y+v)` |
| pair (2,4) | `x=y, z=t` | `(Y+v, Y+v, Y, Y)` |
| (1,3)(2,4) | `ξ=(v,w,-v,-w)` | `(z+v+w, z+w, z, z+v)` |
| (1,4)(2,3) | `ξ=(v,w,-w,-v)` | `(z+v+w, z+w, z, z+w)` |

These reproduce the four one-pair integrands and the two matching
integrands listed in ordered_moment §4.

The unweighted (9) merges the four one-pair terms into
`(x-z)u_xu_z(u_x+u_z)²`. That merge is valid only for product symbols.
Both memos correctly keep the six configurations separate. Against this
table I checked:

- multiwindow §3.3 `Q(w_x,w_y,w_z,w_t)`: the four `C_1` terms and the two
  `C_2` terms match exactly;
- the multiwindow slot sum for
  `Y = ΦV²+VΦV+V²Φ`. The kernel is
  `Y(x,z) = ∫_{x>y>z}(φ_x+φ_y+φ_z)V(x,y)V(y,z)dy`, so `‖Y‖₂²` is Proposition A
  with `w = (φ_x+φ_y+φ_z)(φ_x+φ_t+φ_z)`. The middle vertex of the
  conjugated path is `t`;
- the triple note's `Q_A`. Its `2u_x²u_y²(a_x+2a_y)(2a_x+a_y)` is the sum of
  pairs (1,3) and (2,4). Its `u_xu_y³(a_x+2a_y)²` is pair (1,4), and its
  `u_x³u_y(2a_x+a_y)²` is pair (2,3). The two `C_2` integrands also match.

Consistency checks, [2], with asymmetric signed weights. The formula
is invariant under:

- the path swap `y↔t`, i.e. complex conjugation;
- the reflection `x↦-x`, which reverses the order;
- reproducing the unweighted `Q(uφ)` when the same weight sits on all
  four vertices.

It also reproduces `73/180` (flat) and the inherited cosine values. For the
cubic, cyclic rotation and orientation reversal of the 3-cycle leave
Proposition B invariant. So placing the mark at the "start vertex" is
harmless. The weighted cubic densities agree:
`κ_φ = -[T(φu,u,u) - 3P(φu,u) + 2∫φu] = ∫ φ d`, with
`d = -[u³+2u²Ku+uK(u²)-3u²-3uKu+2u]`, where `Kf(x)=∫|x-y|f(y)dy`.

One minor point. The multiwindow memo displays `c(x)` in the Euler-reduced
form `u[u²-2Du-K(u²)+3D-2]`. That form is exact only for the exact cosine.
For the Taylor-8 profile it differs by `≤1e-8` ([3]), and the certificate
code correctly uses the general `T,P` form.

## 4. Operator lemmas (re-derived)

1. `‖WΦW‖₂² = tr(Φ(W*W)Φ(WW*)) = ∬φ(y)φ(y')(W*W)(y,y')(WW*)(y',y)`.
   Kernel Cauchy–Schwarz then gives `≤ ‖φ‖∞²‖W*W‖₂‖WW*‖₂ = ‖φ‖∞²‖W‖₄⁴`. **PROVED.**
2. With `W=(H+iK)/2`:
   `16‖W‖₄⁴ = tr(H²+K²)² + tr(C²)`, where `C=i[H,K]`. The cross term
   `tr((H²+K²)C)=0`, and `tr C² = 2tr H²K² - 2tr HKHK`. The real part of
   `tr W⁴=0` gives `tr K⁴ = 4trH²K² + 2trHKHK - trH⁴`. Hence
   `‖W‖₄⁴ = tr(H²K²)/2`. Since `H² ≤ 2H`,
   `tr(H²K²) = tr(KH²K) ≤ 2tr(HK²) = (2/3)tr H³`, using `Re tr W³=0`. Hence
   `‖W‖₄⁴ ≤ tr H³/3 = (e+8f)/3 ≤ (4N-3S)/3`. **PROVED.** The vanishing traces
   hold because `W` is a Hilbert–Schmidt Volterra operator, hence
   quasinilpotent, and `W³`, `W⁴` are trace class (Lidskii).
3. Multiwindow identity (3.2) and `tr(G³Φ) = 2Re tr(V*Y(V,V))`: CHECKED on
   random zero-diagonal matrices, residual `3e-13`. The block form
   `R = 2Π_0ΦΠ_0 - EΦE + 2FΦF` follows from the divided differences
   `p'(0)=2`, `p'(1)=-1`, `p'(2)=2`, and `p[λ_i,λ_j]=0` for `i≠j`.

   Step (b) uses `Π_0XΠ_0 = -(J(P-C)J)_-` (since `JBJ=0` and `Π_0=J-E`),
   `‖EΦE‖₂² ≤ tr(EΦ²)` (since `ΦEΦ ≤ Φ²`), and
   `ν ≤ (Δ-d²)/4`. The `Σ_φ` bounds use `e+4f ≤ 2N-S`, `2f ≤ N-S` and
   `‖X‖₁ ≤ √N d` on the zero span.

   Step (c): `tr Y(Z,Z)=0`, so `|2Re tr((H-I)Y(Z,Z))| ≤ 3‖φ‖d²`, and
   `|3tr(X²Φ)| ≤ 3‖φ‖d²`. Step (f):
   `(‖φ‖/2)(Δ-d²) + 6‖φ‖d² ≤ 6‖φ‖Δ`. The scalar reduction uses
   `(2N-S)/N ≤ D` and `(4N-3S)/(3N) ≤ D-2/3`. **PROVED.**
4. Triple Thm 5.1. Step (c) uses `tr(B_mX_00) ≤ 0`, the bound
   `-tr(B_mX_EE) ≤ β√e‖X_EE‖₂` and `2tr(B_mX_FF) ≤ 2β√f‖X_FF‖₂`. Step (d):
   `tr((WB_mW)²)=0` forces `‖WB_mW‖₂² = ‖HB_mK+KB_mH‖₂²/8 ≤ 2β²‖H‖₂²`, and
   `‖K‖₂ = ‖H‖₂`. Constant: `C = 3β√D + √2√Q_A + √2(2α+1)√(D-2/3)`.
   **PROVED.**
5. Full inequalities (NUMERICAL sanity, [6]). The test uses 60 discretized
   continuous zero-side configurations (`M=500`; simple and double zeros and
   off-line pairs; flat and cosine profiles). The multiplier is a random
   signed polynomial, and the mark is random in `[1-β,1]`. No violation
   occurred. The largest ratio lhs/rhs was `0.065` for the multiwindow
   inequality and `0.030` for the triple inequality.

## 5. Independent numerical verification of the certificate inputs (CHECKED)

All integrals use tensor Gauss–Legendre on collapsed simplices (160, 110
and 84 nodes). The integrands are polynomials, so the rule is exact up to
rounding.

| quantity | audit | memo |
|---|---|---|
| `D(u_8)` (Taylor-8 cosine) | 1.32749929632059 | 1.3274992963205883 |
| `κ_φ` | 0.02572936695467 | 0.02572936695466 |
| `E_Y(φ)` | 1.94205279052354 | 1.94205279052313 |
| `∫uφ²` | 0.81431323705458 | 0.81431323705434 |
| `sup|φ|` on the window | ≤ 1.0001761 (grid + `φ''` bound) | ≤ 1.0001797 (Bernstein) |
| `D(u_12)` | 1.32749929703765 | 1.3274992970376471 |
| `κ_a` | 0.02022781321611 | 0.0202278132161081 |
| `Q_A` | 1.62343800717028 | 1.6234380071702812 |
| `Q(u_12)` | 0.39896365069147 | 0.3989636506914728 |

Scalar margins recomputed from the audit values:

- multiwindow: `(κ_φ-6‖φ‖δ_0)² - δ_0C_φ² = 9.606e-7 > 0` at `δ_0=1/64200`;
  the largest certifiable value is `1/64106.9`;
- triple: the margin is `1.619e-7 > 0` at `1/216600`; the largest
  certifiable value is `1/216514.3`;
- control: the unmarked sharpened inequality gives `1/271802.3`.

The float error is about `1e-12`, far below either margin, which is about
`1e-3` relative.

## 6. Conclusions and what remains

- Both weighted transfers are special cases of what the inherited argument
  already proves, namely Propositions A and B for a generic smooth
  symbol. The vertex weight multiplies the symbol and never touches its
  support. Signed weights are harmless. The collapse configurations and
  coefficients (`C_0,C_1,C_2`, and 1 for the cubic) are as the memos
  state.
- The flagged gaps are resolved: multiwindow §3.3 "Gap (flagged)" and
  triple §5.3 (I1)–(I2). Their status becomes that of the inherited
  transfer.
- **Resulting frontier:**
  `liminf N_0^s(T,2T)/N(T,2T) ≥ 2-D(u_8)+1/64200 = 0.6725162800034…`
  This is the multiwindow certificate. The triple-correlation mark gives
  the weaker `0.6725053197675…`.
- **What remains:**
  1. The inherited unweighted transfer (ordered_moment §§1–5, §8) is
     still an ordinary written derivation. It has not been machine-checked,
     and I did not re-derive RS Lemmas 3.2–3.10 or the Hardy-projection
     constants beyond re-evaluating `C_0` and `C_1`.
  2. ordered_moment should state Proposition A explicitly, for a generic
     smooth symbol. Its (9) is written only for product symbols.
  3. The operator theorems are written proofs with numerical sanity
     checks; they are not formalized.
  4. None of this approaches 85%. The increment is `1.6e-5` above
     Montgomery–Taylor.
