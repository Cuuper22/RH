# The ξ′ → ξ bridge: threshold function, exact obstruction identity, tested mechanisms

Research memo, 2026-10-03. Ordinary mathematics; nothing here is Lean-checked.
Scripts: [`verify/xiprime_bridge_threshold.py`](../../verify/xiprime_bridge_threshold.py)
(exact rational, output `.out`) and
[`verify/xiprime_bridge_numerics.py`](../../verify/xiprime_bridge_numerics.py)
(mpmath diagnostics on actual zeros, output `.out`).

Labels used: **PROVED** (full argument written here or in the cited repo
theorem), **CHECKED** (exact rational verification by the script),
**NUMERICAL** (floating diagnostics only), **MODEL** (exact computation for an
explicit local model function, not for ξ), **CONJECTURE**, **REFUTED**.

## 0. Summary

* **Threshold function (CHECKED).** With Ω := W_s + C₂ + (W_d + M_{≥3})/2 (simple
  wrong extrema, double critical-line zeros of ξ, degenerate wrong extrema,
  critical-line zeros of multiplicity ≥ 3) and ω := limsup Ω(T,2T)/N(T,2T),
  the ξ′ theorem transfers to

      liminf N₀ˢ_ξ(T,2T)/N(T,2T) ≥ Θ_v(ω) := c′_v − 2ω,

  c′_quartic = 2 − κ₉ − ε₉ = 0.8686401735976…, c′_flat = 0.8583837135919….
  The proposed frontier F = 0.6725043820976… is beaten iff ω < W*, with

      W*_quartic = (c′_quartic − F)/2 = 0.0980678957500…,
      W*_flat    = (c′_flat − F)/2    = 0.0929396657471….

  This is 10.52 times the 0.00932 threshold of
  [critical_values_20260905.md](critical_values_20260905.md) §3.
* **Trivial bound (PROVED).** Unconditionally Ω ≤ (N′ − N₀ˢ_ξ + 1)/2, so
  ω ≤ (1 − F)/2 = 0.1637478…. Only 60 % (quartic) or 57 % (flat) of this
  trivial bound is needed.
* **Exact circularity (PROVED).** 2Ω = s − N₀ˢ_ξ + G_d + δ *exactly*, where s is
  the number of simple critical-line zeros of ξ′. Hence the hypothesis ω < W* is
  never weaker than the conclusion it is meant to imply: it is equivalent to it
  when the ξ′ certificate is tight (s = c′N′) and strictly stronger otherwise
  (when s = N′, which no known theorem excludes and which holds under RH, the
  hypothesis reads N₀ˢ_ξ ≥ (1 − 2W*)N = 0.804N). The ξ′ theorem itself
  contributes only the translation; the "bridge" is a reformulation of the
  target, not an intermediate step. This sharpens the negative verdicts of the
  September memo.
* **Mechanisms tested.** (a) Rolle/interlacing defect: exact identity
  R_d′ − R_d = 2W + E + C_m − δ; gives exactly the trivial bound and nothing
  more (REFUTED as a route: improving it means proving that ξ′ has a positive
  proportion of non-simple-or-off-line zeros, false under RH). (b) Joint
  two-trace certificate for ξ and ξ′: the bandwidth-one cross cost is exactly 1
  (flat) and 0.99560 (quartic) (CHECKED main-term computation), the union Gram
  has per-point cost 2.237 / 2.225 > 2, so the rank–trace certificate on the
  union is vacuous (CHECKED); the three doublet types (double real zero,
  near-double real pair, near-double nonreal pair) produce the same local
  ξ∪ξ′ zero geometry up to o(1/log T) (MODEL), so no zero-location statistic
  of bandwidth ≤ 1 can separate them. The LP with both certificates, the
  Morse identity and the counts has optimum exactly 2 − D_ξ (CHECKED feasible
  point). (c)/(d) Levinson pencils h_a = ξ + (a/L)ξ′: for fixed 0 < a < 1 all
  zeros of h_a over (T,2T] lie in |Re s − 1/2| < 1 and
  N₋(h_a) = (N − N₀*)/2 + O(log T) (PROVED modulo two flagged standard
  estimates). So W = N₋(h_a) − N₋(h_a′) + O(log T): mechanism (c)/(d) *is*
  Levinson's method for the pair (h_a, h_a′) and offers no shortcut.
* **Structure of wrong extrema (PROVED).** A wrong extremum at height c
  requires an off-line zero β + iγ with |γ − c| < |β − 1/2| and
  Σ_{such ρ}|β − 1/2|^{−2} > Σ_{on-line ρ}(c − γ)^{−2}. In particular W = 0 on
  any window where all zeros within height distance 1/2 are on the line
  (so W = 0 throughout the numerically verified range). In the local model a
  conjugate pair at depth δ with background log-derivative B creates a wrong
  extremum iff δ|B| < 1 and a nonreal ξ′ pair iff δ|B| > 1 (MODEL). Thus, in
  ξ-terms, the ξ′ certificate bounds *deep* off-line pairs (≤ 6.57 %), while
  the transfer loses exactly on *shallow* ones, which are the ones the ξ
  certificate cannot resolve at bandwidth one.
* **Numerics (NUMERICAL).** On actual zeros (ordinates 14–680 and ≈ 9880–9930)
  every gap has exactly one critical point of f(t) = ξ(1/2 + it), the Morse
  identity holds exactly, and the depth 1/|B_n| an off-line pair would need to
  create a wrong extremum has median 0.78 (height ≤ 680) and 1.46 (height
  ≈ 9900) mean spacings; exact bisection gives δ*/(1/|B_n|) between 0.38 and
  0.79 (median 0.64) on a sample of 13 gaps.
* **Verdict.** No improvement over 0.6725043820976 is obtained. The reframed
  target W* ≈ 9.8 % is a cleaner statement of what is missing, but any proof
  of ω < W* must carry sign-sensitive information at sub-mean-spacing
  resolution, exactly the input the ξ certificate lacks; the ξ′ zero count
  cannot supply it.

## 1. Setup and the simple-zero transfer identity

Put f(t) = ξ(1/2 + it), real for real t, with f′(t) = iξ′(1/2 + it). For a
window (a,b] with f(a)f′(a)f(b)f′(b) ≠ 0 write, counting distinct points unless
said otherwise:

* R_s, C₂, M_{≥3}: simple, double, and ≥-triple real zeros of f; R_d = R_s + C₂ + M_{≥3};
* s: simple real zeros of f′ (= simple critical-line zeros of ξ′: ord_η f′ = ord_{1/2+iη} ξ′);
* at a critical point c with f(c) ≠ 0 and k = ord_c f′ odd: *good* if
  f(c)f^{(k+1)}(c) < 0, *wrong* if > 0; G = G_s + G_d, W = W_s + W_d split by k = 1 / k ≥ 3;
* E: critical points with f(c) ≠ 0 and k even;
* N, N′: zeros of ξ, ξ′ in the window with multiplicity (all in the strip);
  N′ = N + O(log T) for (T,2T] (both satisfy Riemann–von Mangoldt with main
  term (T/2π)ℓ₁(T) and O(log T) error: `xiDerivZeros₀_rvm`,
  `Zeta23.RvM.riemannVonMangoldt`).

**Proposition 1 (PROVED).** With δ = [σ(b) − σ(a)]/2 ∈ {−1,0,1}, σ = sgn(ff′),

    R_s = s − 2W_s − 2C₂ − W_d + G_d − M_{≥3} + δ.                    (1.1)

*Proof.* (i) The Morse identity R_d = G − W + δ ([critical_values](critical_values_20260905.md) §1, eq. (1)):
at a zero of f of multiplicity m, ff′ has leading term mA²(x−c)^{2m−1}, so σ
jumps by +2; at a critical point with f(c) ≠ 0 and f′ ~ B(x−c)^k, σ jumps iff
k is odd, by +2 when f(c)B > 0, i.e. f(c)f^{(k+1)}(c) > 0 (wrong), by −2 when
good; even k gives no jump. Summing jumps: 2R_d + 2W − 2G = σ(b) − σ(a).
(ii) A simple zero c of f′ either has f(c) ≠ 0 (then k = 1 is odd, so c is a
good or wrong simple extremum) or f(c) = 0 (then ord_c f = 2). Hence
s = G_s + W_s + C₂. (iii) R_s = R_d − C₂ − M_{≥3} = G − W + δ − C₂ − M_{≥3}
= (s − W_s − C₂) + G_d − W_s − W_d + δ − C₂ − M_{≥3}, which is (1.1). ∎

Checks: f = x² (s = C₂ = 1, δ = 1, R_s = 0), x³ (M_{≥3} = 1, δ = 1), x⁴ + 1
(W_d = 1), x⁴ − 1 (G_d = 1, R_s = 2), x² + 1 (W_s = 1), C + sin x over K
periods (s = 2K, W_s = K, δ = 0) all satisfy (1.1).

Define the **obstruction**

    Ω := W_s + C₂ + (W_d + M_{≥3})/2.                                 (1.2)

**Corollary 2 (PROVED).** R_s ≥ s − 2Ω + G_d + δ ≥ s − 2Ω − 1. Applying the
repository theorem `xiDeriv_simple_on_line_quartic_std` (s ≥ 0.86864 N′
eventually), or its certified-constant form s ≥ c′_v N′ − o(N′) with
c′_v = 2 − κ₉(v) − ε₉ ([AtOne.lean](../../Zeta23/XiPrime/Certificate/AtOne.lean)),
and N′ = N + O(log T), with the O(log T) endpoint adjustments absorbed by
the local counts:

    liminf N₀ˢ_ξ(T,2T)/N(T,2T) ≥ c′_v − 2 limsup Ω(T,2T)/N(T,2T).      (1.3)

Remark. The September memo's (6) is the version of (1.3) for zeros counted
WITH multiplicity, where the degenerate terms are absorbed by the retained
surplus d of the ξ′ certificate. For the *simple* count the obstruction must
contain C₂ with coefficient 1 (a double critical-line zero of ξ is a simple
critical-line zero of ξ′ that transfers to nothing) and M₃ with coefficient 1/2
(a triple zero of ξ is a double zero of ξ′ that the surplus d does not cover).
Since the frontier being compared with is a *simple*-zero count, (1.2) is the
quantity to bound; W_s alone is not enough.

## 2. The threshold function

**Theorem 3 (CHECKED, exact rationals).** Θ_v(ω) = c′_v − 2ω, and

| window | c′_v (exact lower bound for 2 − κ₁(1,v)) | W*_v = (c′_v − F)/2 | ω_triv = (1−F)/2 | W*/ω_triv |
|---|---|---|---|---|
| quartic | 44914246778076124754447678/51706389070236368461368375 = 0.8686401735976 | 0.0980678957500 | 0.1637478089512 | 0.5989 |
| flat | 16008819950038/18649957701375 = 0.8583837135919 | 0.0929396657471 | 0.1637478089512 | 0.5676 |
| quartic, compiled 0.86864 | 0.86864 | 0.0980678089512 | | |
| flat, compiled 0.85838 | 0.85838 | 0.0929378089512 | | |

Here F = 2 − D(u) + 1/271803 is the exact rational of
[sharpened_cubic_gain_20260905.md](sharpened_cubic_gain_20260905.md) (8),
recomputed from the profile polynomial; the script checks
0.672504382 < F < 0.6725043821. The exact W* fractions are printed in the
`.out` file. For comparison, (c′_quartic − 0.85)/2 = 0.00932008679… is the
85 % threshold of the September memo; W*_quartic/0.00932… = 10.522.

So: a bound ω < 0.098 on the density of (1.2) would already improve the
frontier; ω < 0.00932 is what 85 % needs. The next section shows why the
reframing, while numerically ten times less demanding, is not logically weaker.

## 3. The trivial bound and the exact circularity

**Proposition 4 (PROVED).** 2Ω = s − R_s + G_d + δ, and unconditionally

    Ω ≤ (N′ − R_s + 1)/2,  hence  limsup Ω/N ≤ (1 − liminf N₀ˢ_ξ/N)/2 ≤ (1 − F)/2 = 0.16374….

*Proof.* From (1.1), 2W_s + 2C₂ = s − R_s − W_d + G_d − M_{≥3} + δ; adding
W_d + M_{≥3} gives the first identity. Each degenerate good extremum is a
distinct real zero of f′ of order ≥ 3, so s + 3G_d ≤ N′ and s + G_d ≤ N′. ∎

**Proposition 5 (PROVED; the circularity).** Substituting Prop. 4 into
Corollary 2 gives 0 ≥ (c′_v − 1)N′ − 2, a true and empty statement; the
transfer with the trivial bound returns Θ_v(ω_triv) = c′_v − 1 + F < F,
i.e. a loss of exactly 1 − c′_v (0.1314 quartic, 0.1416 flat) relative to the
frontier. More precisely, since 2Ω = s − R_s + G_d + δ exactly, for any
ω the hypothesis "Ω ≤ ωN" is equivalent to "R_s ≥ s + G_d + δ − 2ωN", and
with s ∈ [c′N′, N′]:

* if s = c′N′ (ξ′ certificate tight): hypothesis ⇔ R_s ≥ (c′ − 2ω)N, which IS the conclusion;
* if s = N′ (all ξ′ zeros simple and on the line — true under RH, excluded by no theorem):
  hypothesis ⇔ R_s ≥ (1 − 2ω)N, STRONGER than the conclusion; at ω = W* it reads R_s ≥ 0.804N.

Therefore the ξ′ theorem adds no information to the Ω-formulation beyond a
change of variables: the wrong-extremum density is not an intermediate target
that is easier than the zero count; bounding it *is* bounding the zero count,
in local-configuration language. The value of the language is only that Ω
counts explicit local configurations (Section 4e) that a sign-sensitive
method might attack directly. ∎

(The September memo's W_s/N ≤ 0.00932 hypothesis for 85 % is subject to the same
remark: in the s = N′ world it is equivalent to N₀ ≥ 0.981N.)

## 4. Mechanisms

### 4a. Rolle/interlacing defect (REFUTED as a route)

Let R_d′ count distinct real zeros of f′ and C_m = C₂ + M_{≥3}. Then
R_d′ = G + W + E + C_m and R_d = G − W + δ, so exactly

    R_d′ − R_d = 2W + E + C_m − δ.                                    (4.1)

Under RH with simple zeros R_d′ − R_d = ±1 (strict interlacing in the
Laguerre–Pólya class). Unconditionally R_d′ ≤ N′ − 2b′ where b′ counts
nonreal pairs and multiplicity surplus of ξ′, so

    2W + E + C_m ≤ N′ − 2b′ − R_d + 1 ≤ N − R_d + O(log T).            (4.2)

This is the trivial bound of Prop. 4 again (it is the local version of the
classical fact that a real polynomial with 2p nonreal zeros has at most p
wrong extrema). Any sharpening of (4.2) must either lower-bound b′ (a positive
proportion of ξ′ zeros off the line or multiple — false under RH, hence not
provable) or lower-bound R_d (the target). PROVED that the route gives
exactly the trivial bound; REFUTED as an improvement.

### 4b. Joint two-trace certificate for ξ and ξ′

*Cross cost.* In the layer calculus of the September "critical residues"
note, the ξ′ coefficient at a prime is Λ(p)(2u − 1), u = log p/ℓ, and the ξ
coefficient is Λ(p); only the prime layer is shared. The main-term cross
density is ρ_×(u) = u(2u − 1), and the bandwidth-one cross cost
κ_× = (∫v² + 2∫₀¹ρ_×(r)(v⋆v)(r)dr)/(∫v)² is (CHECKED)

    κ_×(flat) = 1 + 2∫₀¹(1−r)r(2r−1)dr = 1  exactly,
    κ_×(quartic) = 591190037/593803133 = 0.99559939….

(The script also re-derives v⋆v for vQuartic and confirms the Lean value
2∫₀¹convQ = (2777/3000)².) The full marked-trace theorem for this cross
statistic has not been assembled; the status is a main-term computation,
consistent with the memo's verified ρ_CC ↔ D₁ match. The value 1 means that
at bandwidth one the zeros of ξ and ξ′ are, in the second moment, exactly
uncorrelated: the interlacing repulsion at distance ≲ 1/(2L) and the
attraction at distance ≈ 1/L cancel against the test function.

*Union Gram (CHECKED).* The rank–trace lemma applied to the union of the two
zero sets has per-point second trace (D_ξ + D′ + 2κ_×)/2 = 2.2375 (flat) and
2.2250 (quartic, with D_ξ = D(u)), both > 2, so the certificate is vacuous:
interlaced points at spacing ~1/(2L) cannot be resolved by bandwidth one.

*LP (CHECKED).* With normalized unknowns r_s, c₂, p (nonreal ξ pairs), s, b′,
w_s and constraints r_s + 2c₂ + 2p = 1; 3r_s + 4(c₂+p) ≥ 4 − D_ξ;
s + 2b′ = 1; 3s + 4b′ ≥ 4 − D′; r_s = s − 2w_s − 2c₂ (Morse, simple case);
w_s ≤ p (Rolle), the point

    c₂ = 0, p = w_s = (D_ξ − 1)/2, r_s = 2 − D_ξ, s = 1, b′ = 0

is feasible for both windows, so the LP optimum is the ξ certificate alone:
2/3 (flat) and 0.6725007 (profile, before the cubic gain). Adding the cross
constraint changes nothing since the union certificate is vacuous.

*Why (MODEL).* Let g be real analytic near γ with g(γ) ≠ 0, B₀ = g′/g(γ),
B₁ = (g′/g)′(γ), and compare f₀ = g(t−γ)², f_δ = g((t−γ)² + δ²),
f_ε = g(t−γ−ε)(t−γ+ε). Writing u = t − γ and freezing g′/g = B₀ + B₁u,
the critical points solve B₀ + B₁u + 2u/(u²+δ²) = 0 (resp. with −ε² in place
of δ², resp. +2/u). For δ, ε → 0 the three equations have the roots
u = −2/B₀ + O(δ²), u = −B₀δ²/2 + O(δ⁴) [f_δ], u = ±ε + O(ε³)-adjacent root at
u = O(ε²) [f_ε], u = 0 [f₀] when B₀ ≠ 0, and u = ±√(−2/B₁) + O(δ²), u = O(δ²)
when B₀ = 0, B₁ < 0. In every case the three functions have the same
critical points up to O(δ² + ε²) and the same zero cluster up to O(δ + ε),
while W(f_δ) = 1, W(f₀) = W(f_ε) = 0 and R_s(f_ε) = 2, R_s(f₀) = R_s(f_δ) = 0.
Any statistic of the positions of ξ-zeros and ξ′-zeros that is continuous at
scale o(1/L) — every bandwidth-one trace — takes the same value on the three
configurations, which are respectively "bad, bad, good" for the simple count.
This is the P² ± ε² obstruction of the September memo seen in the joint
picture.

### 4c/4d. Levinson pencils and ξ + cξ′

Let L = ½log(T/2π), τ = a/L with fixed 0 < a < 1, and
h(t) := f(t) − iτf′(t). Since f′ = iξ′, this is exactly h(t) = ξ(s) + (a/L)ξ′(s)
at s = 1/2 + it: the s-plane pencil ξ + (a/L)ξ′ with the critical line as the
real t-axis, and Re s > 1/2 ⇔ Im t < 0.

**Proposition 6 (PROVED modulo (E1), (E2) below).** For T large and
a ∈ (0,1) fixed, every zero of h with Re t ∈ (T, 2T] satisfies
−1/2 < Im t < 1, and if f has no multiple real zero in the window,

    N₊(h) = (N + R_d)/2 + O(log T),  N₋(h) = (N − R_d)/2 + O(log T),   (4.3)

where N_± count zeros of h with ±Im t > 0 and R_d = N₀*(T,2T).

*Proof.* Zeros of h are the solutions of f′/f = −i/τ = −iL/a, and
f′/f(t) = iξ′/ξ(1/2 + it). (i) Lower half-plane, Im t = −y, y ≥ 1/2:
s = 1/2 + y + it has Re s ≥ 1, and f′/f = i(R + iI) = −I + iR with
R = Re ξ′/ξ(s) > 0 by the repository theorem Re ξ′/ξ > 0 on Re s ≥ 1; so
Im f′/f > 0 ≠ −L/a. (ii) Upper half-plane, Im t = y ≥ 1: s = 1/2 − y + it,
and by ξ′(s)/ξ(s) = −ξ′(w)/ξ(w) with w = 1 − s, Re w = 1/2 + y ≥ 3/2,
f′/f = −i(R + iI) = I − iR with R + iI = ξ′/ξ(w) = 1/w + 1/(w−1) − ½log π
+ ½ψ(w/2) + ζ′/ζ(w). For 1 ≤ y ≤ T one has |w| ∈ [T, 3T], so
R = ½log(|w|/2π) + O(1) = L + O(1) ≠ L/a for large T since a < 1 is fixed.
For y ≥ T: Im f′/f = −R = −L/a would force R = L/a, but then also
Re f′/f = I must vanish, while I = ½arg(w) + Im(1/w + 1/(w−1)) + ½(Im ψ(w/2) − arg(w/2))
+ Im ζ′/ζ(w), where ½|arg w| = ½arctan(t/(½+y)) ≥ T/(10y), the Stirling and
rational terms are O(1/y), and |Im ζ′/ζ(w)| ≤ Σ Λ(n)n^{−1/2−y} ≪ 2^{−y}; so
I ≠ 0 for T large. Hence all zeros lie in −1/2 < Im t < 1.
(iii) Count in the upper rectangle a ≤ Re t ≤ b, 0 ≤ Im t ≤ 1 (with
a ∈ (T−1, T], b ∈ (2T−1, 2T] chosen so that h ≠ 0 on the vertical sides and
f f′ ≠ 0 at a, b; the adjustment costs O(log T) zeros by the local counts).
Along the real segment, for P + iQ = f − iτf′, (1/π)Δ arg(P + iQ) = −Ind(Q/P)
and Q/P = −τf′/f jumps from +∞ to −∞ at each real zero of f (f′/f ~ m/(t−γ)),
so Δ_bottom arg h = πR_d. Along the top side Im t = 1, h = f(1 − τf′/f) with
1 − τf′/f = (1 − a) + O(1/L) by (ii), so Δ_top arg h = Δ_top arg f + O(1),
and Δ_top arg f, traversed from b to a on Re s = −1/2, equals by the
functional equation ξ(s) = ξ(1−s) = conj ξ(1 − s̄) the argument change of ξ up
the line Re s = 3/2, which is πN(a,b) + O(log T) (the two vertical sides of the
Riemann–von Mangoldt rectangle contribute equally). The vertical sides
contribute O(log T) each (E1). Thus 2πN₊ = πR_d + πN + O(log T).
(iv) The full rectangle |Im t| ≤ 1: on the bottom side Im t = −1,
1 − τf′/f = 1 + τI − iτR = 1 − ia + O(1/L), bounded away from 0, so the
argument change is Δ arg f + O(1) = πN + O(log T), and N₊ + N₋ = N + O(log T)
(E2). Subtracting gives (4.3). ∎

(E1) is the Backlund–Jensen bound for the argument of h on a vertical segment
of bounded length at height ≈ T; it applies verbatim since
h = ξ(1 + (a/L)ξ′/ξ) has the growth of ξ in a disc of radius 2, but it has not
been written out here. (E2) likewise for the full rectangle; the number of
zeros of h in a unit height interval is O(log T) by the same bound. Multiple
real zeros of f are zeros of h on the contour and require the usual
indentation; they are excluded above for simplicity (the transfer identity
handles them exactly and they are already in Ω).

*Consequences.* (1) Under RH (with simple zeros) every zero of ξ + (a/L)ξ′ with
0 < a < 1 lies strictly to the left of the critical line, since
Re ξ′/ξ(s) = Σ(σ − 1/2)/|s − ρ|² > 0 for σ > 1/2 and ξ′/ξ is purely imaginary on
the line; unconditionally the number to the
right is exactly half the number of off-line-or-multiple zeros of ξ, to
O(log T). Bounding N₋(h) is therefore Levinson's method for the pencil, and
(4.3) shows it is *equivalent* to bounding N − N₀*, not a step towards it.
(2) Applying (4.3) to f′ in place of f (h′ = f′ − iτf″, s-plane pencil
ξ′ + (a/L)ξ″, which is the s-derivative of the first pencil) and subtracting,
with (4.1): 2W + E + C_m − δ = R_d′ − R_d = 2N₋(h) − 2N₋(h′) + O(log T), the
memo's (11), now with an explicit proof of the boundary pieces: the wrong
count is the excess of right-half-plane zeros of the pencil over those of its
derivative. A Gauss–Lucas-type inequality N₋(h′) ≤ N₋(h) would be consistent
with W ≥ 0 but gives only the trivial bound; the useful direction (many
zeros of h′ to the right) is unavailable for the same reason as in 4a.
Mechanisms (c) and (d) are thus REFUTED as shortcuts; they are Levinson's
method for the function pair (h, h′) in disguise.

### 4e. Pointwise structure of wrong extrema

Write the zeros of f as z_n = γ_n + iδ_n with δ_n = 1/2 − β_n ∈ (−1/2, 1/2)
(ρ_n = β_n + iγ_n). Since ξ(s) = ξ(0)∏(1 − s/ρ) with symmetric pairing,
f′/f(t) = Σ_n (t − z_n)^{−1} (symmetric summation) and
(f′/f)′(t) = −Σ_n (t − z_n)^{−2}, absolutely convergent.

**Proposition 7 (PROVED).** Let c be a simple wrong extremum of f, u_n = c − γ_n. Then
(f′/f)′(c) = f″(c)/f(c) > 0 and

    Σ_{n: |u_n| < |δ_n|} (δ_n² − u_n²)/(u_n² + δ_n²)²  >  Σ_{on-line zeros} u_n^{−2} + Σ_{n: |u_n| > |δ_n|, δ_n ≠ 0} (u_n² − δ_n²)/(u_n² + δ_n²)².   (4.4)

In particular (i) some zero satisfies |γ_n − c| < |β_n − 1/2| (so it is off
the line and within height distance 1/2 of c); (ii) Σ_{|u_n|<|δ_n|} |β_n − 1/2|^{−2}
> Σ_{on-line} (c − γ_n)^{−2}; (iii) if every zero of ξ with |γ − c| < 1/2 is
on the line, c is not a wrong extremum. For a degenerate wrong extremum of
order k ≥ 3 (odd) the first nonvanishing derivative is
(f′/f)^{(k)}(c) = −k!Σ_n(c − z_n)^{−k−1}, with sign that of f(c)f^{(k+1)}(c) > 0;
on-line zeros again contribute negatively, and a zero can contribute positively
only if cos((k+1)arg(u_n + iδ_n)) < 0, i.e. |u_n| < |δ_n|·cot(π/(2(k+1))). So
(i)–(iii) hold with 1/2 replaced by ½cot(π/(2(k+1))) (= 1/2 for k = 1,
≈ 1.207 for k = 3).

*Proof.* At a critical point (f′/f)′ = f″/f − (f′/f)² = f″/f, positive at a
wrong extremum by definition. Expand −Re(c − z_n)^{−2} = (δ_n² − u_n²)/(u_n² + δ_n²)²
and separate the terms by sign; on-line zeros have δ_n = 0 and contribute
−u_n^{−2} < 0; each positive term is at most δ_n^{−2}. ∎

*Interpretation (MODEL).* Replace two consecutive real zeros γ₁ < γ₂ by the
pair m ± iδ, m = (γ₁+γ₂)/2, keeping the rest of f: f̃′/f̃ = B(t) + 2(t−m)/((t−m)² + δ²)
with B = f′/f − (t−γ₁)^{−1} − (t−γ₂)^{−1}; note B(m) = f′/f(m). With B frozen
at B₀ = B(m), the critical equation u² + (2/B₀)u + δ² = 0 has two real roots
(one wrong extremum, slope 2/δ² + B₁ > 0 at the wrong one as δ → 0) iff
δ|B₀| < 1, and a nonreal pair of critical points, i.e. a nonreal ξ′ pair, iff
δ|B₀| > 1. So an off-line pair is *shallow* (creates a wrong extremum,
invisible to the ξ′ count) or *deep* (creates a nonreal ξ′ pair, charged by
the ξ′ certificate at 2 per pair) according to δ|B₀| ≶ 1, with
|B₀| ≍ L typically, i.e. the dividing depth is a fraction of the mean
spacing 2π/log T. In ξ-terms the ξ′ certificate says (MODEL) that deep pairs
plus ξ′ multiplicity surplus are at most (2 − c′)/2 = 6.57 % of N; the
ξ certificate says shallow + deep + multiple ≤ (D_ξ − 1)/2 = 16.37 %. The
transfer loss is entirely on the shallow pairs, for which nothing beyond the
ξ certificate is known. No unconditional lower bound on Σ_{on-line}(c−γ)^{−2}
at an arbitrary c is available (zero gaps are not bounded), and the local
zero count in an interval of length 1/log T is only O(log T) unconditionally,
so (4.4) does not yield a density bound by itself; it is the right *local*
description of the obstruction.

### 4f. Side remark: triple zeros of ξ (PROVED from two repo theorems)

A zero of ξ of multiplicity m ≥ 3 is a zero of ξ′ of multiplicity m − 1 ≥ 2.
The distinct-zero theorem for ξ′ (N_d′ ≥ (3/2 − κ₉/2 − ε₉/2)N′ eventually, quartic)
gives Σ_{ξ zeros, m ≥ 3}(m − 2) ≤ 0.06568 N, slightly better than the
0.08187 for M₃ implied by Theorem D's distinct count (Σ(m−1) ≤ 0.16375N).
This does not affect the simple-on-line count (triple zeros already cost 1
each in Ω and are not the bottleneck).

## 5. Numerics (NUMERICAL)

All figures from [`verify/xiprime_bridge_numerics.out`](../../verify/xiprime_bridge_numerics.out)
(mpmath, 15 digits; f′/f(t) = −Im(ξ′/ξ)(1/2+it) from the logarithmic derivative
formula, checked against a numerical derivative of log|ξ| and against the residue
+1 at γ₁). These are diagnostics on the verified-RH range, where Ω = 0 is forced
by Prop. 7(iii); they test the identities and illustrate the local scale of the
obstruction, nothing more.

*Critical points per gap.* Blocks of zeros #1–#400 (ordinates 14.13–679.74,
399 gaps) and #10000–#10060 (9877.78–9929.44, 60 gaps), 32 interior sample
points per gap: every gap shows exactly one sign change of f′/f, f′/f is
strictly decreasing on every sampled grid, and the Morse identity
R_d = G − W + δ holds exactly (398 = 399 − 0 − 1 and 59 = 60 − 0 − 1, with
δ = −1 because σ = sgn(ff′) is +1 just right of the first zero and −1 just left
of the last). So W = C₂ = 0, R_d′ − R_d = 1, consistent with (1.1), (4.1).

*Susceptibility.* 1/|B_n| with B_n = f′/f at the gap midpoint, in units of the
local mean spacing 2π/log(t/2π):

| block | min | q1 | median | q3 | max | fraction > 1/2 | fraction > 1 |
|---|---|---|---|---|---|---|---|
| #1–#400 | 0.266 | 0.615 | 0.782 | 1.105 | 7.68 | 0.907 | 0.306 |
| #10000–#10060 | 0.623 | 0.955 | 1.464 | 2.965 | 392 | 1.000 | 0.717 |

Exact thresholds δ* (bisection on the modified log-derivative, 160 grid points
over the two neighbouring gaps) for 13 gaps of the first block lie between 0.36
and 0.60 mean spacings, and δ*/(1/|B_n|) ranges over 0.38–0.79 (median 0.64);
the frozen-background heuristic overestimates δ* by a bounded factor because
B varies across the gap. In the s-coordinate, a hypothetical off-line pair
collapsing a typical gap would need |β − 1/2| ≲ 0.4–0.6 mean spacings
to produce a wrong extremum; pairs deeper than that produce a
nonreal ξ′ pair instead (MODEL of §4e). The large values of 1/|B_n| (up to 392
spacings) occur where f′/f is nearly zero at the midpoint, i.e. where the two
neighbouring gaps nearly balance; there even a very shallow pair would be
"deep" in the sense of §4e.

The data say nothing about the unconditional density ω: in this range W = 0
identically, as it must be. What they quantify is the scale at which the
shallow/deep dichotomy operates — a fixed fraction of the mean spacing — which
is exactly the resolution a bandwidth-one certificate lacks.

## 6. Assessment

* **Proved:** the simple-zero transfer identity (1.1); the threshold function
  Θ_v(ω) = c′_v − 2ω with exact W*; the trivial bound ω ≤ 0.16375; the exact
  identity 2Ω = s − R_s + G_d + δ and the resulting circularity (Prop. 5); the
  Rolle identity (4.1); Proposition 7; Proposition 6 modulo the two flagged
  standard estimates.
* **Checked:** all rationals above; cross cost 1 and 0.99560; union cost > 2;
  the LP feasible point.
* **Refuted as routes:** (a) interlacing/Rolle counting, (c)/(d) pencils and
  derivative families (they are Levinson's method for (h, h′)), (b) joint
  bandwidth-one statistics.
* **Most promising open estimate.** Because of Prop. 5 the honest target is not
  "W small" but a sign-sensitive statement at sub-mean-spacing resolution. Two
  formulations, equivalent to ω < W*, are: (i) a Littlewood-lemma /
  mollifier estimate for the ratio (ξ″ + aLξ′)/(L²ξ + aLξ′) on the critical
  line (the common Γ-factor cancels; this is the memo's "critical-axis
  relative signature") strong enough to give N₋(h) − N₋(h′) < 0.098N; (ii) an
  anti-concentration statement for off-line zeros: fewer than 9.8 % of all
  zeros may be off-line pairs with |β − 1/2|·|B| < 1 where B is the local
  background log-derivative. Neither follows from pair correlation at
  bandwidth one, and (ii) is exactly what the ξ certificate pays 16.4 % for.
  The ξ′ zero count cannot help with either: in the only scenario where the
  bridge is not a tautology (s = N′) the ξ′ theorem is vacuous.
* **Feasibility.** Low along this axis. A plausible productive use of ξ′ is as
  a companion function inside a Levinson/Conrey-type mollified mean value
  (the pencil ξ + (a/L)ξ′ has all its zeros within 1/log T-scaled distance of
  the line and, under RH, all to the left), not through its zero count. That
  would be a new analytic programme, not a cheap bridge.
