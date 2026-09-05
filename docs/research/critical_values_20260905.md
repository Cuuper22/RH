# Transferring the xi-prime two-trace bound through wrong extrema

Research derivation, 2026-09-05. This supplies a new exact counting transfer
and a signed critical-value moment. It does not bound the number of wrong
extrema, and therefore does not yet prove 85% for xi.

## 1. Exact interval identity, including every multiplicity

Let f be a nonconstant real analytic function on a neighborhood of [a,b],
with neither f nor f′ vanishing at the endpoints. Let Rd count its distinct
real zeros in (a,b). At a critical point c with f(c)≠0, put k=ord_c f′.
If k is odd, call the extremum good when f(c)f^(k+1)(c)<0 and wrong when
this product is positive. Let G,W count these distinct extrema, including
degenerate ones. Critical points of even k are neither.

Set σ(x)=sgn(f(x)f′(x)) off its zeros. At every real zero of f, of any
multiplicity m, f(x)f′(x) has leading term m A²(x−c)^(2m−1), so σ jumps
by +2. At a nonzero critical value of odd k, σ jumps by +2 at a wrong
extremum and −2 at a good one. At even k it does not jump. Summing gives

    Rd = G−W+δ,   δ=[σ(b)−σ(a)]/2 ∈ {−1,0,1}.             (1)

Let s count simple real zeros of f′. Split G=Gs+Gd and W=Ws+Wd by
simple/degenerate critical points. Let C2 count real f zeros of exact
multiplicity two and Ef=Σ_{f(c)=0}(ord_c f−1). Then
s=Gs+Ws+C2, and the real-zero count R0 WITH MULTIPLICITY satisfies exactly

    R0 = s−2Ws−Wd+Gd+(Ef−C2)+δ.                          (2)

Ef−C2≥0, hence

    R0 ≥ s−2Ws−Wd−1.                                    (3)

The degenerate wrong term cannot simply be omitted from this identity.
For example f=C−cos x+(cos²x)/2, C>1/2, is positive everywhere, with one
simple positive maximum and one positive minimum where f′ has order three
per period. On K full periods, s=Wd=K and Ws=R0=0. Equation (1) also
handles f=x² (a common simple f′ zero), x⁴+1 (a degenerate wrong extremum),
and x⁴−1 (a degenerate good extremum) without genericity assumptions.

## 2. The stronger two-trace budget absorbs degenerate wrong extrema

Consider the derivative-zero matrix G=P+Q in the inherited framework.
P is the sum of the simple real-root atoms, so P≥0, tr P≤s, rank P≤s.
Q is Hermitian, with n+(Q)≤b, where b counts the distinct nonsimple real
roots and distinct nonreal conjugate pairs of f′. Normalize atom norms as
in the existing repo theorem. Write Q=B−C for its positive/negative parts,
so BC=0, and put A=P−C. For q(X)=4tr X−tr X²,

    q(G)=q(A)+q(B)−2tr(PB) ≤ q(A)+q(B).

For λ≥0, 4λ−λ²≤2λ+1; negative eigenvalues contribute nonpositively.
Since A≤P, tr A+≤tr P≤s and n+(A)≤rank P≤s. Thus q(A)≤3s.
Also q(B)≤4rank B≤4b. Consequently

    4tr G−||G||HS² ≤ 3s+4b.                              (4)

This stronger expression already appears inside `ZeroSide/Mult.lean`,
`mult_two`, before its final multiplicity simplification.

Let N′ count all derivative zeros with multiplicity in the same window,
and set d=N′−s−2b. It is nonnegative: a nonsimple real zero of multiplicity
m contributes m−2, and a conjugate pair of multiplicity m per root
contributes 2m−2. Every degenerate wrong extremum has odd m≥3, so d≥Wd.
Equation (4) is equivalent to

    s ≥ 4tr G−||G||HS²−2N′+2d.

Combining with (2) proves

    R0 ≥ 4tr G−||G||HS²−2N′−2Ws−1.                      (5)

Indeed the discarded remainder is 2d−Wd+Gd+Ef−C2≥0. Thus no separate
bound on multiple derivative zeros is needed. Nonreal derivative roots
are included in b and N′ throughout, without assuming they lie on the line.
The standard repo collars/tail perturbations add o(N′), exactly as in the
existing seam; retaining d rather than discarding it changes no moment input.

If tr G=N′+o(N′), ||G||HS²≤(D′+o(1))N′, and N′=Nξ+o(Nξ), then

    liminf R0/Nξ ≥ 2−D′−2 limsup Ws/Nξ.                  (6)

The conclusion counts ordinary critical-line zeros WITH MULTIPLICITY.
It does not assert that they are simple.

## 3. Literal repo constants and the exact 85% threshold

`Zeta23/XiPrime/Certificate/AtOne.lean` defines

    K9=277244140547469154168336/245053976636191319722125,
    ε9=1024/2990212875,

and proves κXi(1,vQuartic)≤K9+ε9. Their numerical values are

    K9+ε9 = 1.131359826402381464671...,
    2−K9−ε9 = 0.868640173597618535...,
    (1.15−K9−ε9)/2 = 0.009320086798809267... .

The executable theorem `cert_quartic_one` safely states
2−κXi(1,vQuartic)≥0.86864017. `Certificate.lean` moves the strict
0.86864 bound to some fixed λ<1 by continuity. Thus the literal condition

    limsup Ws(T,2T)/Nξ(T,2T) ≤ 0.00932                   (7)

is sufficient to obtain strictly more than 85% via (6), using a fixed λ
close enough to one and the genuine strict margin. The threshold is not
rounded up from a weaker result. Some docstrings say the upper bound is
1.1313598, or the lower bound 0.8686402; those round in the wrong direction.
The compiled AtOne theorem uses the safe 0.86864017 instead.

## 4. The mixed observable and a computable signed first moment

At a simple real zero c of f′ with f(c)≠0,

    r_c = Res_{z=c} f(z)/f′(z) = f(c)/f″(c).

Wrong extrema are exactly the positive residues; good extrema have negative
residues. In the s-coordinate the corresponding residue ξ/ξ″ has the
OPPOSITE sign, because f″(t)=−ξ″(1/2+it). Common zeros of f and f′ give a removable quotient and no pole.
For any entire weight w and any finite contour avoiding poles, the exact
computable moment is

    Σ_inside Res[w(z)f(z)/f′(z)]
        = (2πi)^−1 ∮ w(z)f(z)/f′(z) dz.                 (8)

Multiple critical points contribute their actual higher-pole residues, not
an unsupported f/f″ substitution. Nonreal critical points remain in the sum
and occur in conjugate pairs for real-symmetric weights.

For f(z)=ξ(1/2+iz), take w(z)=exp(−((z−T)/H)²), H=T^a with fixed 0<a<1,
and a strip |Im z|<b with b>1/2. The repo's strip theorem puts all f′ zeros
inside. On the bottom side, s=1/2+b+it lies to the right of1 and

    f/f′ = −i ξ/ξ′ = −2i/log(T/(2π)) + O(log(T)^−2)

uniformly on |t−T|≤H log T; the top side is its conjugate. The right-half-plane
estimate follows directly from ξ′/ξ=h′/h+ζ′/ζ, Stirling, and the absolutely
convergent Dirichlet series for ζ′/ζ. Thus the two horizontal-side integrals
in the t-plane give

    Σ_contour Res[w f/f′]
       = −2H/[sqrt(π) log(T/(2π))] + O(H/log(T)²).        (9)

Here the sum is understood as the limit of finite strip contours closed
along admissible radii. Gaussian decay permits closing: ξ and ξ′ have
order one, and the usual minimum-modulus sequence bounds their quotient
by exp(O(R^(1+ε))) on a sequence of closing segments, with ε<1. No absolute
convergence of individual inverse-curvature residues is asserted.
The leading normalized mean residue is −4/log(T)² per derivative zero.

This gives a concrete mixed ξ/ξ′ observable, but it does not bound Ws:
positive residues can be arbitrarily small, negative ones arbitrarily large,
and off-line derivative poles contribute as well. Any conversion of (9)
to (7) needs new control of residue sizes or a signature-sensitive observable.
A signed first moment alone is insufficient.

## 5. Counterexample to a free derivative-to-function transfer

For C>1, f(x)=C+sin(ωx) has no real zeros and f′ has only simple real zeros;
exactly half are wrong extrema. Thus the coefficient two in (6) is sharp.
The local exponential-envelope version

    f(x)=exp(−a x)[C+sin(ωx)],   ω²>a²(C²−1),

still has no real zeros, while every zero of f′ is simple and real. The
critical equation is ω cos(ωx)−a sin(ωx)=aC, whose right side lies strictly
inside its real amplitude. The function's nonreal zeros lie in the fixed
strip |Im z|=acosh(C)/ω, which can be arbitrarily narrow. This example has
order one and exponential decay as x→+∞. It is not even and does not claim
to satisfy all xi axioms; it shows that a gamma-sized local decay envelope
and narrow-strip zeros alone do not rule out the wrong-extrema obstruction.


# Critical residues: exact coefficients and the mixed-moment obstruction

Research calculation, 2026-09-05. Ordinary mathematics, not Lean verified.
This note concerns the signed critical-value input to the separate Morse
transfer argument in the preceding sections. It establishes no new
zero percentage. That note also derives the first residue moment with an
explicit Gaussian contour; the coefficient calculation below complements it.

## 1. A contour moment that sees the sign of an extremum

Put F(s)=ξ(s)/ξ′(s), f(t)=ξ(1/2+it), and ℓ=log(T/(2π)). At a simple ξ′
zero ρ′=1/2+iη with ξ(ρ′)≠0,

    Res_{ρ′} F = ξ(ρ′)/ξ″(ρ′) = −f(η)/f″(η).

The residue is positive at a correct extremum and negative at a wrong
extremum f(η)f″(η)>0. Normalize it by ℓ²/4 and denote it by r.
For any admissible holomorphic contour test H, the residue theorem gives

    Σ_{poles in rectangle} Res(HF) = (1/(2πi)) ∮ H(s)F(s)ds.

This is an actual signed moment, unlike the unmarked ξ′ zero count. The
sum must retain higher-order poles: it is not automatically the sum of r
over simple critical points. Common zeros of ξ and ξ′ are removable for F.

The repo already defines E=ξ′/ξ=L−A with A(s)=ΣΛ(n)n^−s, and proves its
right-line estimates in `Zeta23/XiPrime/ExplicitFormula/Expansion.lean`.
For F=1/E, freezing L at L*=ℓ/2 gives

    F(s) ≈ Σ_{j≥0} L*^(−j−1) A(s)^j.

Thus the coefficient at n=1 is 2/ℓ. The resulting leading vertical-contour
term is 2T/(πℓ), or N after residue normalization ℓ²/4, where N~Tℓ/(2π).
The full contour/tail theorem for this new marked test has not been assembled.

For n>1 the normalized coefficients are

    R(n)=Σ_{k≥1} R_k(n),
    R_k(n)=2^(k−1) ℓ^(1−k) Λ^{*k}(n).

These are finite sums for each n and are nonnegative. In particular R(p)=Λ(p).
The existing unmarked ξ′ coefficient C satisfies exactly, after real freezing,

    C(n)=−Λ(n)+Σ_{k≥1}(2u/k)R_k(n), u=log n/ℓ.

This follows from (Λ log)*Λ^{*(k−1)}=(log n/k)Λ^{*k}(n).
At a prime, C(p)=Λ(p)(2u−1), so passing to R loses the prime-layer cancellation.

## 2. Diagonal densities and a closed scalar test

For squarefree n with k prime factors, only R_k(n) survives. The standard
prime-simplex integral yields the layer density

    r_k(u)=4^(k−1) k! u^(2k−1)/(2k−1)!.

The corresponding diagonal and cross main-term densities are

    ρ_RR(u)=Σ_{k≥1}r_k(u),
    ρ_CR(u)=u(2u−1)+Σ_{k≥2}(2u/k)r_k(u),
    ρ_CC(u)=u(2u−1)²+Σ_{k≥2}(4u²/k²)r_k(u).

The CC series agrees term by term with the repo's D1 density in
`Zeta23/XiPrime/Certificate/D1.lean`. This is a useful normalization check.
To obtain a complete marked-trace theorem, the nonsquarefree and uniform
layer-tail estimates must also be adapted; the displayed densities alone
are not that theorem.

For a flat frequency window of width one, its autocorrelation is 1−u on
0≤u≤1, and the candidate costs are D_ab=1+2∫₀¹(1−u)ρ_ab(u)du:

    D_CC = 1.141615945290782
    D_CR = 1.111912280055014
    D_RR = 1.515039234639352.

The squared difference cost is D_CC+D_RR−2D_CR=0.432830619820107.
The best trace-normalized scalar mixture (1−λ)C+λR has

    λ=0.0686265339733, D=1.139577485699348.

This small cost improvement does not bound the wrong-extremum count. At a
real simple critical point its atom has coefficient 1−λ+λr, still positive
for all sufficiently small negative r. The R-only positive-index estimate
also remains much too weak: even the prime layer alone has the zeta cost.

## 3. Retaining multiple poles exactly

Pass to the real coordinate via iF(1/2+iz)=−f(z)/f′(z); the simple residue
is unchanged. Suppose this real-reflection-symmetric function has a pole η of
order m with principal part Σ_{j=1}^m a_j/(z−η)^j, a_m≠0. Its divided-
difference kernel, with sign chosen positive for a positive simple residue,
has the block in features (z−η)^−1,...,(z−η)^−m

    H_ij = a_{i+j−1} if i+j−1≤m, and 0 otherwise.

This real symmetric Hankel block is nonsingular. Its inertia is (m/2,m/2)
for even m and ((m+sign(a_m))/2,(m−sign(a_m))/2) for odd m. One proof
deforms the lower coefficients to zero: the determinant never vanishes,
and the remaining anti-diagonal matrix has the stated inertia. A conjugate
nonreal pole pair of order m has inertia (m,m). Common ξ/ξ′ zeros supply
no pole. This prevents replacing multiple poles by simple weighted atoms.

Reciprocating a logarithmic derivative gives a kernel congruent to its
original kernel. Thus this sign geometry is another form of the Bezoutian
geometry, not a free new count of integer atoms.

## 4. Mixed second moments do not close the sign count

There is an explicit abstract unit-frame counterexample for the displayed
flat-window costs. It is not asserted to be a zeta-zero configuration.
Let q=(D_CC−1)/2=0.0708079726454 and d=D_CR−1=0.1119122800550.
Use qN orthogonal pairs of identical unit vectors and (1−2q)N singleton
unit vectors, orthogonal across blocks. The unmarked Gram C has eigenvalues
2 on pair blocks and 1 on singleton blocks, giving tr C=N, tr C²=D_CC N.

Give each pair a total residue d/q=1.58050394431535, split equally between
its two atoms. Then tr(CR)=D_CR N provided tr R=N. On the singleton blocks,
the remaining first and second residue sums must be

    sN=(1−d)N=0.8880877199450 N,
    bN=(D_RR−d²/q)N=1.3381614345951 N.

Take singleton residues −ε and a positive value, adjusting their proportions
to meet these two equations. As ε decreases to zero, the negative fraction
of all atoms approaches

    (1−2q)−s²/b = 0.2689934341704.

Consequently these three mixed second moments, even with unit atoms for C,
cannot force the needed wrong-extremum bound below 0.00932N. Integer block
counts can be approximated with arbitrarily large N; the gap is substantial.
Where the required inverses exist, a Schur complement C R^−1 C would preserve the sign of every nonzero r,
including tiny ones, but its traces require inverse/resolvent information
not supplied by the three displayed moments. That is a new input, not a
consequence of the calculation above.
