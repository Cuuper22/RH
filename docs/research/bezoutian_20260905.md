# Local Bezoutian certificate without atom norm caps

Research derivation, 2026-09-05. This establishes the operator/counting mechanism and an explicit arithmetic gate. It does not establish the required arithmetic moment inequality or an improved zeta proportion.

## 1. Finite polynomial identity and inertia

For a real polynomial f of degree n, define

    K_f(x,y)=[f(x)f'(y)-f'(x)f(y)]/(x-y),
    K_f(x,x)=f'(x)^2-f(x)f''(x).

The logarithmic derivative gives the exact identity

    K_f(x,y)=sum_r m_r [f(x)/(x-r)] [f(y)/(y-r)].             (1)

Each distinct real root gives a positive rank-one term, regardless of its multiplicity. Each conjugate pair of nonreal roots gives a Hermitian block with at most one positive and one negative direction. In the full polynomial coefficient space these blocks are independent. Thus, if d is the number of distinct complex roots and Rd the number of distinct real roots,

    rank K_f=d,
    signature K_f=Rd,
    n_positive(K_f)=(d+Rd)/2.

Multiplication by a real q that is nonzero on a set of positive measure preserves the finite-rank inertia. No bound on the individual atom norms is needed.

In particular the number S of simple real roots, and therefore also the real-root count with multiplicity, obeys

    S >= 2 n_positive(K_f)-n.                              (2)

The same upper bound on positive index follows directly without asserting independence: simple line atoms cost one zero per positive direction; nonsimple line atoms and nonreal pair blocks cost at least two.

## 2. Exact contraction via Hardy projections

Fix c>0, E=f+ic f', and, on the real axis,

    Theta=(f-ic f')/(f+ic f').

Cancel common factors at repeated roots, or define boundary values away from the isolated exceptional points. Then |Theta|=1 almost everywhere.

Let P+ be the orthogonal Hardy projection on L2(R). For **any measurable unimodular Theta**, the operator

    T=P+ - M_Theta P+ M_Theta*

is a difference of orthogonal projections, so ||T||op<=1. This does not require Theta to be inner or of bounded type. Its delta-kernel terms cancel, and its off-diagonal kernel is

    i[1-Theta(x)conj(Theta(y))]/[2 pi(x-y)]
      = (c/pi) K_f(x,y)/[E(x)conj(E(y))].

Conjugating by the measurable boundary phase E/|E| shows that

    C0(x,y)=(c/pi)K_f(x,y)/[|E(x)||E(y)|]                  (3)

is a self-adjoint contraction. Every interval compression is also a contraction. This proof applies to xi itself; no Cartwright or infinite-model-space assertion is needed.

For an arbitrary real q, write a=q|E|. Then the exact quadratic-form sandwich is

    -M_{a^2} <= (c/pi)M_q K_f M_q <= M_{a^2}.

Consequently |qE|<=1 pointwise supplies a genuine contraction. An averaged mollifier estimate alone does not supply that operator bound; the clipping below supplies it automatically.

## 3. Normalized local trace

Away from removable common zeros,

    (c/pi) K_f(x,x)/|E(x)|^2
      = -(1/pi) d[arg E(x)]/dx.                            (4)

At a distinct real zero of f, cancel the common factor in f and f'. The resulting E crosses the imaginary axis clockwise, since f'/f has positive residue equal to the multiplicity. Every such crossing counts one distinct real zero. Therefore the integral of (4) over a generic interval equals the number of distinct real zeros there plus an endpoint term of absolute value at most one.

For polynomials on the whole real line the endpoint term vanishes and the normalized trace equals Rd. For arbitrary clipped q the trace identity (4) is lost: clipping can suppress negative diagonal contributions. The local certificate below instead uses contraction, the finite local zero sum, and a trace-norm tail bound.

## 4. Clipping and the moment gate

Let mu>=0 be a chosen base weight on I. Put

    J=f'^2-f f'',
    L_kappa=f'^2+(kappa f^2+kappa^(-1) f''^2)/2,  kappa>0,
    A=integral_I mu J,
    B=integral_I mu^2 (f^2+c^2 f'^2) L_kappa.

Assume A>0 and 0<B<infinity. For a scale r>0 set

    q0^2=r mu,
    d=q0^2 |E|^2,
    qclip^2=q0^2/max(1,d).

Then |qclip E|<=1, so

    C=(c/pi) M_qclip K_f M_qclip

compressed to I is a contraction. The pointwise inequalities needed for its trace are exact:

    h/max(1,d) >= h-(d/4) h_plus,
    h=q0^2 J,
    h_plus<=q0^2 L_kappa.

For h>=0, the first inequality follows from 1/max(1,d)>=1-d/4; for d>1 the latter is equivalent to (d-2)^2>=0. For h<0, clipping increases h. The second inequality is Young's inequality for |f f''|.

It follows that

    tr C >= (c/pi)[rA-r^2 B/4].

Choosing r=2A/B gives

    tr C >= (c/pi) A^2/B.                                 (5)

This is a lower bound for the trace of a concretely clipped contraction, not an unsupported substitution of average normalization for pointwise normalization.

## 5. Entire xi: the local rank issue and how to control it

One must not use the global polynomial degree as the number of xi zeros in I. Even f=sin(pi x) has a positive infinite-rank Bezout kernel on a short interval containing no roots. Restricting x,y to I does not remove contributions from remote zeros.

For f(t)=xi(1/2+it), its genus-one canonical product gives, with normal convergence off the roots,

    K_f(x,y)=f(x)f(y) sum_rho m_rho/[(x-rho)(y-rho)].       (6)

The constant and genus-one compensation terms in f'/f cancel in the divided difference. Here rho is in the real t-coordinate: Re rho is the zero ordinate and |Im rho|<1/2.

Let I=[T,2T], and include in L the finite zero sum with Re rho in [T-H,2T+H], H>=1. Let E_tail=C-L. Since clipping ensures |qclip f|<=1, a real root's rank-one trace norm is bounded by

    (c/pi)m_rho integral_I |x-rho|^(-2) dx.

For a reflected nonreal pair, the nuclear norm is at most the sum of the same two bounds, by ||u v*||_1=||u|| ||v|| and conjugate equality of the two norms. Hence

    ||E_tail||_1
      <= (c/pi) sum_outside m_rho integral_I |x-rho|^(-2) dx.       (7)

For a zero at ordinate-distance u>=H beyond either endpoint, the integral is bounded by

    T/[u(u+T)].

The standard unit-interval zero-count bound O(log(2+|gamma|)), counted with multiplicity, therefore gives

    ||E_tail||_1
      = O(c log T [1+log(T/H)])                            (8)

for 1<=H<=T. A fixed H gives O(c log^2 T); in particular this is o(N(T,2T)) for bounded c, and even smaller for c of order 1/log T. The buffer itself contains O(H log T) additional zeros.

These are the precise analytic inputs for the xi passage: the canonical-product divided difference (6), the unit-interval zero-count bound, and the trace-class convergence justified by (7). No arithmetic value for A or B is being assumed.

## 6. Local count from the clipped trace

Let Nloc count all zeros in the buffered window and Sloc its simple line zeros. The finite local sum L satisfies

    rank(positive part of L) <= (Nloc+Sloc)/2.

Let Pi be its positive spectral projection, of rank rL. Since C<=I and the compression of L to the complement of Pi is nonpositive,

    tr C
      = tr(Pi C Pi)+tr((1-Pi)C(1-Pi))
      <= rL+||E_tail||_1.

Therefore

    Sloc >= 2 tr C-Nloc-2||E_tail||_1.                     (9)

If Nbuf=Nloc-N(T,2T), discarding the extra boundary zeros yields the precise unbuffered version

    S(T,2T) >= 2 tr C-N(T,2T)-2Nbuf-2||E_tail||_1.         (10)

Choose H=1 and bounded c (in particular c=v/log T with fixed v>0). Combining (5), (8), and (10) gives the asymptotic certificate

    S/N >= (2c/(pi N)) A^2/B - 1 - o(1).                  (11)

Thus an 85% result follows if the actual arithmetic moments satisfy

    (c/pi) A^2/B >= (37/40+o(1)) N,

with the appropriate strict margin or epsilon formulation. This would prove the stronger simple-on-line target and hence the requested ordinary-line proportion. Establishing this moment inequality is the remaining research problem; the clipping, contraction, and local counting steps do not require individual atom norm caps.


# Mollified Bezoutian: arithmetic gate and first closed test

Ordinary mathematics and numerical evaluation, 2026-09-05. No new zero
percentage is established. The zero-side contraction and localization are
derived in the preceding sections.

Let f(t)=ξ(1/2+it), ℓ=log(T/(2π)), and N~Tℓ/(2π). The real Bezoutian is

    K_f(x,y)=[f(x)f′(y)−f′(x)f(y)]/(x−y),
    K_f(x,x)=f′(x)²−f(x)f″(x).

Its canonical-product expansion consists of positive real-zero rank-one
atoms and Hermitian conjugate-pair atoms with positive index at most one.
The multiplicity budget is therefore n_+ ≤ (N+S)/2, with S the number of
simple real zeros. This does not assume RH.

Write f=±Aγ Z, with Z Hardy's real function and Aγ=|h(1/2+it)|,
h(s)=s(s−1)π^(−s/2)Γ(s/2)/2. Put aγ=(log Aγ)′.
For q0=M/Aγ the exact compensated diagonal is

    |q0|² K_f(t,t)=|M|²[Z′²−ZZ″−aγ′ Z²].

Here aγ=−π/4+O(1/T), aγ′=O(T^−2). These gamma corrections are lower order
in the moment calculations below; they are not deleted from the exact kernel.

The unnormalized Hilbert–Schmidt approach would require

    A=∫|q0|² K_f(t,t)dt ~ a Tℓ²,
    B_HS=∬|q0(x)q0(y)K_f(x,y)|²dxdy ~ b Tℓ³,
    b ≤ (80π/37)a²

to obtain 85%. The numerator is known; the denominator needs a two-height
shifted fourth moment with shifted mollifiers and controlled separation tails.
No such denominator evaluation is claimed in this note.

## Clipping replaces that denominator by local fourth moments

For c>0 and κ>0 put

    d=|q0|²(f²+c² f′²), h=|q0|²(f′²−ff″),
    Hκ=f′²+(κ f²+κ^−1 f″²)/2.

Since h_+≤|q0|²Hκ and (1−1/d)_+≤d/4,

    h/max(1,d) ≥ h−|q0|⁴ Hκ(f²+c²f′²)/4.

The clipped normalized kernel is a self-adjoint contraction. After optimizing
the scalar size of q0 and applying the local zero budget, the sufficient bound is

    S/N ≥ 2(c/π) A²/(B N)−1+o(1),
    B=∫|q0|⁴ Hκ(f²+c²f′²).

Take c=v/ℓ, κ=kℓ², Z_j=Z^(j)/ℓ^j, and
m_abcd=lim T^−1∫|M|⁴ Z_a Z_b Z_c Z_d. Then

    b(v,k)=m0011+v²m1111
           +(k/2)(m0000+v²m0011)
           +(1/(2k))(m0022+v²m1122).

The optimal k is the square root of the ratio of the last two parenthesized
quantities. Thus

    b(v)=m0011+v²m1111
         +sqrt[(m0000+v²m0011)(m0022+v²m1122)],
    S/N ≥ 4v a²/b(v)−1+o(1).

The exact 85% gate is b(v)≤(80/37)v a².

## Available input and numerical test

For M(s)=Σ_{n≤T^θ} μ(n)P(log(T^θ/n)/log T^θ)n^−s, P(0)=0,P(1)=1,
the polarized second moment gives

    a=1/2+(1/(6θ))∫P′²+θ∫P².

[Bui–Hall, Proposition 1 and equation (8)](https://arxiv.org/pdf/2304.05178)
provide this for θ<4/7. Their Proposition 2 supplies the shifted local fourth
moment for θ<1/8 and P(0)=P′(0)=0. Differentiation gives the five m's above.
This uses their proved moment result, not the repo's proposed AS interface.

For P(u)=u², θ→1/8, numerical evaluation gives

    a       = 2.30277777777778
    m0000   = 1878.63809523810
    m0011   = 46.8657319223987
    m1111   = 7.10327740763289
    m0022   = 10.4645340975897
    m1122   = 0.340966289495247.

The evaluator `../../verify/bezout_local_moments.py` extracts the eight auxiliary
derivatives as multiaffine coefficients and integrates the remaining
polynomials with Gauss quadrature. The published explicit expression for
m0022 agrees within 2e−14, providing a substantive normalization check.
The optimized coarse clipping certificate is negative, about −0.767524;
it provides no useful percentage. Four nearby smooth polynomials were worse.
This closes the first test, not the full class of mollifiers or clipping rules.

## Reciprocal of E: the actual next coefficient family

Because |Z+ivZ′/ℓ|=|Z−ivZ′/ℓ|, use the analytic orientation

    V_v=(1+v/2)ζ+(v/ℓ)ζ′ = α ζ(1−δ L/ℓ),
    α=1+v/2, δ=v/α∈(0,2), L=ΣΛ(n)n^−s.

Its formal reciprocal has coefficients

    b_v(n)=α^−1 Σ_{j≥0}(δ/ℓ)^j(μ*Λ^{*j})(n).

Each individual coefficient sum is finite. The first correction is
μ*Λ=−μ log, so j≤1 remains an ordinary μP mollifier. The first new term is
μ*Λ²=μ log²+μ*(Λ log), which includes prime-pair and prime-power terms.
For primes p,q, setting x=log p/ℓ,y=log q/ℓ gives

    α b_v(p)=−1+δx,
    α b_v(pq)=1−δ(x+y)+2δ²xy,
    α b_v(p^a)=δ²x²(1+δx)^(a−2), a≥2.

These identities are formal algebra, not a proved mollified moment advantage.
On n≤T^(1/8), δ log n/ℓ≤1/4; merely adding the first correction is modest.

There is also an exact second-moment flatness test for the entire μP family.
Normalize M's constant coefficient to 1/α, so its mean product with V_v is 1.
Minimizing its squared modulus over P(0)=0,P(1)=1 gives

    min ⟨|V_v M|²⟩ =
    [1+v²/4+v sqrt(1+v²/12)
       coth(vθ/sqrt(1+v²/12))]/(1+v/2)².

The minimizing profile is proportional to sinh(vθu/sqrt(1+v²/12)).
At θ=1/8, numerical minimization over v gives 2.6876554344 at v≈4.6991941.
Consequently ordinary μP cannot make V_v M close to 1 in mean square at
this length. This diagnoses the flatness proposal; it is not an obstruction
to 85% for a different coefficient family or a sharper nonlinear certificate.
