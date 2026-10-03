# The Cheer–Goldston positivity class and actual complex zeros

Research note, 2026-10-03. Companion script
[`verify/positivity_class_certificate.py`](../../verify/positivity_class_certificate.py)
(output `verify/positivity_class_certificate.out`). Labels: PROVED (full
argument in this note), CHECKED (exact or high-precision computation in the
script), NUMERICAL (floating-point optimisation, no certificate), CONJECTURE,
REFUTED.

## 0. Summary

* The RH-side class of Cheer–Goldston (test r ≥ 0 on **R**, r̂ ≤ 0 off
  [−1,1], only F ≥ 0 off [−1,1] and Montgomery's asymptotic on [−1,1]) is
  **not** worth 0.672753 but 0.6792: Chirre–Gonçalves–de Laat (Adv. Math.
  2020, Thm. 1 / Cor. 2) optimise exactly this class by SDP and get
  N*(T) ≤ 1.3208 N(T), hence N_s ≥ 0.6792 N under RH. Cheer–Goldston's
  0.672753 used the Montgomery–Taylor kernel plus a combinatorial argument on
  consecutive gaps. The LP in Part A of the script reproduces 1.32092
  (0.67908) with a piecewise-linear r̂ (NUMERICAL).
* Unconditional transfer in the literal form "Σ_Z(r) ≥ r(0)(2N − s₁)" is
  **REFUTED** for every test with nonzero Fourier mass outside [−1,1]: a
  single conjugate pair {iy, −iy} gives Σ_Z(r) = 2r(0) + 2r(2iy) and
  r(2iy) → −∞ (Lemma 1, PROVED; CHECKED at y = 0.25, 0.5, 1, 2 for the LP
  test, where r(2iy)/r(0) = 0.19, −2.2·10³, −5.6·10⁹, −7.2·10²²).
* Positivity of F off [−1,1] is a tautology for every conjugation-invariant
  multiset (Lemma 0). Hence the only information is the bandwidth-one
  measure, and the correct transferred certificate is the bandwidth-one
  inequality

      (**)   Σ_Z(ρ) ≥ κ (2N − s₁),   ρ = r̂·1_{[−1,1]},   κ = r(0) < ∫ρ,

  for all finite conjugation-invariant multisets Z (Prop. 2: (**) implies
  liminf N₀ˢ/N ≥ 2 − P(ρ)/κ unconditionally, PROVED modulo the published
  unconditional pair-correlation formula). For real Z, (**) is exactly the
  Cheer–Goldston inequality (Prop. 3). For complex Z it is **open**.
* What is proved about (**) for complex Z: it holds for a lone pair, for
  all-pair configurations at a common height, and whenever ρ dominates an
  autocorrelation of mass κ — but the last route provably never beats
  Montgomery–Taylor (Prop. 4). The natural term-by-term complex completion
  needs Re r_in(x+it) ≥ s(x) for all t ≥ 0, which fails for every ρ ≠ 0
  (Prop. 6); any proof must balance self-terms against cross-terms
  quadratically.
* NUMERICAL: for the LP-optimal ρ (which has ρ ≥ 0 on [−1,1], min r_in =
  −0.0047, completion mass s(0) = 0.0126), adversarial search over complex
  configurations with up to ~17 points, including 60 random mixed patterns,
  never finds Σ_Z(ρ)/(2N − s₁) < 1 (minimum 1.00324 ≥ κ = 1); minimisers collapse onto the real line,
  and the second-order lifting coefficient at near-tight designs is positive
  (C_j ≈ +0.25). Lifting does lower the ratio at some non-tight
  configurations (e.g. {0⁴, x⁴} plus two pairs at height v ≈ 0.27: 1.6726
  versus 1.6768 collapsed), so κ_C(ρ) ≤ κ_real(ρ) can be strict in
  principle; for a control ρ = 1_{[1/2,1]} the complex infimum is 0.0071
  against a real infimum 0.1496 (CHECKED numerically). So (**) is
  ρ-specific; no general theorem "complex = real" exists.
* **Certified unconditional bound from this class: none above
  0.6725043820976.** If (**) were proved for the LP-optimal ρ the
  unconditional proportion would be 0.67908 (CONJECTURE), against the
  current 0.6725043820976, Cheer–Goldston's 0.672753 (RH) and CGdL's 0.6792
  (RH).

## 1. The RH-side argument as an abstract certificate

Montgomery units: L = log T/(2π) in Cheer–Goldston's normalisation, zeros
ρ = β + iγ with multiplicity m_ρ, z_ρ = (ρ − 1/2)/i = γ − i(β − 1/2). For
real even r̂ ∈ L¹ with compact support put r(u) = ∫ r̂(α) e^{2πiαu} dα and

    Σ_Z(r) = Σ_{z,z'∈Z} m_z m_{z'} r((z − z')L)        (ordered pairs, z = z' included).

Inputs of the certificate (CG 1993 §2; CGdL 2020 Lemma 8):

(I1) r ≥ 0 on **R**;
(I2) r̂ ≤ 0 on |α| > 1;
(I3) F(α) = r.h.s. of Montgomery's formula, F(α) = T^{−2|α|}log T + |α| + o(1) uniformly on |α| ≤ 1;
(I4) F(α) ≥ 0 for all α.

Chain: (a) Σ_Z(r) ≥ r(0) Σ_ρ m_ρ² by (I1) (drop off-diagonal terms);
(b) Σ_ρ m_ρ² ≥ 2N − N_s since m² ≥ 2m − [m = 1];
(c) Σ_Z(r) = N ∫ r̂ F ≤ N ∫_{−1}^{1} r̂ F by (I2),(I4);
(d) = N (r̂(0) + ∫_{−1}^{1}|α| r̂(α) dα + o(1)) =: N (P(r) + o(1)) by (I3).
Hence N_s/N ≥ 2 − P(r)/r(0). Montgomery–Taylor: r̂ supported in [−1,1],
optimum P/r(0) = 1/2 + 2^{−1/2}cot 2^{−1/2} = 1.3274993 (0.6725007; the
repo's c₁*). CGdL: (I2) instead of compact support, optimum 1.3208 by SDP
(0.6792 under RH; 1.3155/0.6845 under GRH using the Goldston–Gonek–Özlük–
Snyder *lower* bound F ≥ 3/2 − |α| on 1 ≤ |α| ≤ 3/2, which is a different
kind of input). The averaged *upper* bounds on F used by Carneiro–Milinovich–
Ramos and Carneiro–Chandee–Chirre–Milinovich (recorded as failing for finite
windows in `certificate_limits_20260905.md`) play no role in the simple-zero
problem.

Where RH is used: (a) needs the differences z − z' real; (c) needs nothing
beyond (I4), which Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh (BGSTB
2023, Thm. 1) prove for the complex-zero F unconditionally, and which is
in fact a tautology (Lemma 0); (d) is Montgomery's theorem, proved
unconditionally with complex z − z' by BGSTB (Thm. 1 and Lemma 5, with the
weight w(ρ − ρ') = 4/(4 − (ρ − ρ')²); Lamzouri 2026, Lemma 3.2, removes the
weight by a two-test combination). So RH enters only in step (a), the
zero-side inequality. This is exactly the step BGSTB could not remove: their
Theorem 2 assumes |β − 1/2| < 1/(2 log T) and uses a kernel with Re K > 0 in
a strip, losing to 61.7%; Lamzouri observes that no nonconstant entire kernel
has Re K ≥ 0 on **C**, and his Proposition 2.1 (like the repo's Lemma R)
handles only r = |FT(φ)|² with φ ≥ 0, i.e. r̂ an autocorrelation of a
nonnegative function — the class in which r̂ ≥ 0 automatically, so (I2) can
only be met with r̂ = 0 outside [−1,1].

## 2. Unconditional setting and what transfers

Let Z be a finite multiset of complex numbers, closed under conjugation with
equal multiplicities (for zeta: Z_T = {z_ρ L : T < γ ≤ 2T}; the functional
equation gives closure). Put S_Z(α) = Σ_z m_z e^{2πiαz}.

**Lemma 0 (PROVED).** For every real even r̂ with compact support,
Σ_Z(r) = ∫ r̂(α) |S_Z(α)|² dα. In particular Σ_Z(s) ≥ 0 whenever ŝ ≥ 0, for
every conjugation-invariant Z. *Proof.* |S_Z(α)|² = Σ_{z,z'} m_z m_{z'}
e^{2πiα(z − \bar z')}; re-index z' ↦ \bar z' using closure. □
This is the identity of `certificate_limits_20260905.md` §1 without the
weight w; every test whose Fourier transform is a nonnegative measure of
compact support inherits positivity, irrespective of the weight. So (I4)
carries no information about Z: the complete information is the family of
values Σ_Z(ρ) for ρ supported in [−1,1].

**Lemma 1 (PROVED; lone-pair obstruction).** Let r̂ be real, even, compactly
supported, Λ = sup supp r̂, and suppose r̂ ≤ 0 on [a, Λ] for some a < Λ with
∫_{a'}^{Λ} r̂ < 0 for a' = (a + Λ)/2. Then for Z = {iy, −iy}, Σ_Z(r) =
2r(0) + 2r(2iy) and r(2iy) = ∫ r̂(α) cosh(4παy) dα → −∞ as y → ∞. Hence the
inequality Σ_Z(r) ≥ r(0)(2|Z| − s₁(Z)) (here: Σ_Z(r) ≥ 4r(0)) fails for large
y. *Proof.* Split [0,Λ] at a and a'. On [0,a] the integral is at most
‖r̂‖₁ cosh(4πay); on [a,a'] it is ≤ 0; on [a',Λ], where r̂ ≤ 0 and cosh ≥
cosh(4πa'y), it is ≤ cosh(4πa'y)∫_{a'}^{Λ} r̂ = −c·cosh(4πa'y) with c > 0.
Since a' > a the total tends to −∞. □
Every Cheer–Goldston test with nonzero mass outside [−1,1] satisfies the
hypothesis (a = 1). The script checks the LP test: r(2iy)/r(0) =
+1.09, +0.19, −2.2·10³, −5.6·10⁹, −7.2·10²² at y = 0.1, 0.25, 0.5, 1, 2.
Since the repo's Lemma R certifies the analogous inequality for every
autocorrelation test, the lone pair also shows that Lemma R cannot extend to
any test whose r̂ is negative near the top of its support — including
Montgomery–Taylor-class tests r = |ĥ|² with signed h (REFUTED for that
extension as well).

**Definition.** For ρ ≥ 0 even on [−1,1] (the bandwidth-one part of a CG
test, ρ = r̂·1_{[−1,1]}) let P(ρ) = ρ(0) + ∫_{−1}^{1}|α|ρ, R = ∫ρ = r_in(0),
r_in(u) = ∫ρ e^{2πiαu}, and for a class 𝒵 of finite conjugation-invariant
multisets
    κ_𝒵(ρ) = inf_{Z∈𝒵} Σ_Z(ρ) / (2|Z| − s₁(Z)),
κ_real for real multisets, κ_C for all. Clearly κ_C ≤ κ_real.

**Proposition 2 (PROVED, modulo BGSTB Thm. 1/Lemma 5 and Lamzouri Lemma 3.2).**
If ρ is Lipschitz, even, supported in [−1,1] and Σ_Z(ρ) ≥ κ(2|Z| − s₁) for all
finite conjugation-invariant Z, then liminf N₀ˢ(T)/N(T) ≥ 2 − P(ρ)/κ. *Proof.*
Apply the inequality to Z_T. BGSTB Lemma 5 evaluates Σ_{Z_T}(ρ̃) with the
weight w for every Lipschitz ρ̃ supported in [−1,1] as N(P(ρ̃) + O(1/√log T));
the unweighted Σ_{Z_T}(ρ) equals the weighted sum for ρ plus (π²/L²) times the
weighted sum for the test with transform −ρ''/(4π²) (Lamzouri's combination;
mollify ρ so that ρ'' ∈ L¹, at cost o(1) in P). Hence Σ_{Z_T}(ρ) = N(P(ρ) +
o(1)) and 2N − s₁ ≤ Σ/κ gives the claim; only ordinates and the functional
equation are used, not β = 1/2. □

**Proposition 3 (PROVED; the real case is Cheer–Goldston).** If r = r_in − s
≥ 0 on **R** with ŝ ≥ 0, then κ_real(ρ) ≥ r(0) = R − s(0). Conversely the
two-point configurations {0}, {0,0}, {0,x} show κ_real(ρ) ≤ R and force
r_in(x) ≥ κ − R; and for any ρ, the condition "Σ_Z(ρ) ≥ κ(2N − s₁) for all
real Z" is the copositivity of the kernel r_in(x_j − x_k) − κδ_{jk} on
nonnegative integer vectors. *Proof.* Σ_Z(r_in) = Σ_Z(r) + Σ_Z(s) ≥ Σ_Z(r)
≥ r(0)Σm² ≥ r(0)(2N − s₁). □ For the LP test: κ = 1, R = 1.01261, min r_in =
−0.00474 (so s must dip to −0.00474 and s(0) = 0.01261 ≥ 0.00474).

**Proposition 4 (PROVED; dominated autocorrelations cannot help).** If
r̂_a ≤ ρ with r̂_a = φ⋆φ̃, φ ≥ 0 supported in [−1/2,1/2] (the repo's class),
then Σ_Z(ρ) ≥ Σ_Z(r_a) ≥ r_a(0)(2N − s₁) for every complex Z (Lemma 0 and
Lemma R), so κ_C(ρ) ≥ κ_auto(ρ) := sup r_a(0). But P(ρ) − P(r_a) = P(ρ − r̂_a)
≥ 0, hence 2 − P(ρ)/κ_auto(ρ) ≤ 2 − P(r_a)/r_a(0) ≤ 0.6725007. The CG gain is
therefore exactly the excess κ_CG(ρ) − κ_auto(ρ) > 0 obtained from r_in being
allowed to be negative on **R**, and any complex proof of (**) must use that
structure, not Lemma R alone.

**Proposition 5 (PROVED; two complex cases of (**)).** Let ρ ≥ 0 and κ ≤ R.
(i) For a lone pair, Σ_Z(ρ) = 4m²∫ρ cosh²(2παv) ≥ 4m²R ≥ κ·4m. (ii) If Z
consists only of pairs, all at the same height v, and Z₀ is the real multiset
obtained by collapsing each pair (x ± iv, m) to a real point x of multiplicity
2m, then S_Z(α) = cosh(2παv) S_{Z₀}(α), so Σ_Z(ρ) = ∫ρ cosh²(2παv)|S_{Z₀}|²
≥ Σ_{Z₀}(ρ), while 2|Z| − s₁(Z) = 2|Z₀| = 2|Z₀| − s₁(Z₀) because Z₀ has no
simple points. Hence (**) for real Z implies (**) for such Z. □
In general S_Z(α) = Σ_j w_j(α) e^{2πiαx_j} with w_j = m_j for a real cluster
and w_j(α) = 2m_j cosh(2παv_j) ≥ 2m_j = w_j(0) for a pair: a complex
configuration is a real configuration with α-dependent, nondecreasing weights.
Lifting can lower Σ: for a real cluster of multiplicity m₀ at 0 and a pair
(x ± iv, m), with t = m₀/(2m), Σ = 4m²∫ρ[(cosh(2παv) + t cos(2παx))² +
t² sin²(2παx)], which decreases in v while cosh < −t cos. This is the
mechanism behind every complex minimiser found below the collapsed real
value in the control experiment.

**Proposition 6 (PROVED; termwise completion is impossible).** Suppose one
tries to prove (**) for complex Z as in Prop. 3 by dominating every cross
kernel K_ρ(j,k) = ∫ρ w_j w_k cos(2παΔ_{jk}) by W_jW_k s(Δ_{jk}) with W_j =
w_j(0) and then using positive definiteness of s on the collapsed real
points. Since cosh(a)cosh(b) = [cosh(a+b) + cosh(a−b)]/2, this requires
Re r_in(x + it) := ∫ρ cos(2παx) cosh(2παt) dα ≥ s(x) for all real x and all
t ≥ 0. For ρ ≠ 0 and x with cos(2πΛ_ρ x) < 0 (Λ_ρ = sup supp ρ), the left side
tends to −∞ as t → ∞ while s is bounded. So no choice of s works; the
diagonal gain 4m²∫ρ cosh² − 4m²s(0) ≥ 4m²κ is available only if cross-terms
are controlled by the self-terms, i.e. by a genuinely quadratic argument. This
is the same obstruction Lamzouri records for kernels with Re K ≥ 0 on **C**.

## 3. Off-line zeros cannot be confined by density theorems

Zeros with |β − 1/2| = y contribute weights cosh(2πα yL/(2π)) ≤ e^{Ly} on
[−1,1]. A zero-density estimate N(σ,T) ≪ T^{1−c(σ−1/2)} (log T)^C bounds the
number of zeros with |β − 1/2| ≥ K/L by e^{−cK}N(log T)^C. Their total
weight is then ≤ e^{(Λ_ρ − c)K}N(log T)^C, negligible only if c > Λ_ρ, i.e.
c > 1 − δ when ρ is supported in [−(1−δ), 1−δ]. Selberg's c = 1/4 is far from
this; the density hypothesis is c = 2. Even granting such an estimate, the
control experiment finds violating complex configurations at heights v ∈
[0.05, 0.3], i.e. |β − 1/2| between 0.3/log T and 2/log T — inside any box
one could hope to isolate. So (**) must hold for all heights; nothing here
depends on, or is helped by, zero-density results.

## 4. Numerics (script Parts A–D)

Part A (NUMERICAL): LP over even piecewise-linear r̂ on [0, 2.5], step 0.01,
slope ≤ 20, r̂ ≤ 0 on [1, 2.5], r ≥ 0 on a grid to u = 60, r(0) = 1:
P = 1.3209166550, proportion 0.6790833 (CGdL: 1.3208). The optimum has
ρ ≥ 0 on [0,1] with ρ(1) = 0, min r̂ on (1, 2.5] = −0.0202, R = 1.0126111,
min r_in = −0.004744 at u = 2.10. Positivity is enforced only on a grid
(the far tail is not certified; the RH-side value is CGdL's theorem).

Part B (CHECKED): lone-pair values above; also r_in(2iy) ≥ R, so the lone
pair is harmless for (**).

Part C (NUMERICAL): adversarial minimisation of Σ_Z(ρ)/(2N − s₁) over 27
multiplicity patterns (real clusters with multiplicities up to 6, up to three
pairs, up to 12 points), Nelder–Mead from 12–20 random starts per pattern,
positions in [−3,3], heights v ∈ [0,1], pairs' weights 2m cosh(2παv).
LP-optimal ρ: minimum 1.004665 ≥ κ = 1; minimisers have v ≤ 10⁻⁸ in all but
one pattern ({0⁴, x⁴} + two pairs, v = 0.27, ratio 1.6726 < 1.6768 collapsed,
far above 1). A separate random search over 60 patterns with up to 8 real clusters
and 5 pairs (multiplicities up to 3, up to about 25 points; not in the
script) found minimum 1.003241 with all heights v ≤ 3·10⁻⁸ and no violation.
Control ρ = 1_{[1/2,1]}: real infimum 0.1496, complex infimum 0.0071
({0,x₁,x₂} + three pairs at v ≈ 0.25); 13 of 20 complex patterns lie below
their collapsed real pattern.

Part D (NUMERICAL): for near-tight real designs (n simple zeros + one double
zero, positions optimised; ratios 1.0045 → 1.003 as n grows), the
second-order lifting coefficient C_j = Σ_k m_k q(x_j − x_k), q(u) = ∫ρα²
cos(2παu), is ≈ +0.25 (q(0) = 0.1488, min q = −0.0865), and joint
re-optimisation returns to v = 0.

## 5. Self-check of every step against hidden RH use

| step | status | RH or real-zero use |
|---|---|---|
| prime side Σ_{Z_T}(ρ) = N(P(ρ)+o(1)), ρ on [−1,1] | published (BGSTB Thm 1, Lemma 5; Lamzouri Lemma 3.2) | none; complex z_ρ throughout |
| F ≥ 0 off [−1,1] | Lemma 0, PROVED | none; tautology, carries no information |
| Σ_Z(r) ≥ r(0)Σm² | REFUTED for complex Z (Lemma 1) when r̂ ≢ 0 off [−1,1] | this is the RH step |
| (**) for real Z with κ = r(0) | PROVED (Prop. 3) | real differences |
| (**) for complex Z | PROVED for lone pairs, common height, dominated autocorrelations (no gain, Prop. 4); otherwise CONJECTURE for the LP ρ; false for the control ρ | — |
| termwise complex completion | REFUTED (Prop. 6) | — |
| off-line control by density | insufficient (needs c > 1 − δ) | — |

Nothing above uses β = 1/2 or the multiset being real except the step marked
as the RH step. The repo's own mechanism (Lemma R) is tight for its class and
provably cannot be extended to signed r̂ near the top of the support.

## 6. What would be gained, and how it might be proved

If (**) holds for complex Z with the LP-optimal ρ and κ = 1, Proposition 2
gives liminf N₀ˢ/N ≥ 0.67908 unconditionally (and, by the same inequality
with the distinct-zero count, N_d/N ≥ (3 − 1.32092)/2 = 0.8395). This would
exceed the current 0.6725043820976 and Cheer–Goldston's RH value 0.672753,
and essentially reach CGdL's RH value 0.6792. It is CONJECTURE.

The clean statement to prove: for positive measures ν on **C** of finite
support, symmetric under conjugation, with integer masses,

    ∫∫ r_in(ζ − ζ̄') dν(ζ) dν(ζ') ≥ κ (2|ν| − #{simple real atoms}),

where the left side is ∫_{−1}^{1} ρ(α)|∫ e^{2πiαζ}dν(ζ)|² dα ≥ 0. Facts to
use: (i) the diagonal of each pair is 4m²∫ρcosh² ≥ 4m²R, strictly larger than
the collapsed value; (ii) the cross terms involve cosh(2παv_j)cosh(2παv_k)
cos(2παΔ) and are not termwise dominated (Prop. 6); (iii) the real case holds
with slack Σ_{j≠k}W_jW_k r(Δ_{jk}) + κΣ(W_j² − cost_j) + ∫_{|α|>1}ŝ|S_{Z₀}|².
A proof must show that the α-dependent weight increase cannot eat this slack,
using the quadratic structure (Cauchy–Schwarz between a pair's self-term and
its cross-terms with phases fixed by the real part of its position). The
control experiment shows this is false for some ρ, so a proof must use the
smallness of −min r_in relative to s(0) for the CG optimum (here
0.0047 against 0.0126), i.e. a perturbative argument around the autocorrelation
cone with an explicit error below the CG excess. I did not find one.

A weaker but still useful target: (**) for complex Z with κ' ∈ (κ_auto(ρ), 1).
Any κ' > κ_auto would give an unconditional proportion 2 − 1.32092/κ' above
the frontier as soon as κ' > 1.32092/1.3274956 = 0.99504 (the value at which
2 − P/κ' equals 0.6725043820976). So even a 0.5% loss in κ is affordable;
the lone pair, common-height and dominated-autocorrelation results give
κ' ≥ κ_auto only, which is below this threshold by Proposition 4.
