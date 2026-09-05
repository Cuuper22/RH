# Ordered Cayley resolvents: exact inertia identity and a closed certificate class

Research note, 2026-09-05. This note concerns a proposed certificate class, not a proof of 85%. It uses the finite ordered-moment functional developed in `ordered_moment_20260905.md` and its higher-order extension. The actual infinite-order asymptotic interchange for a rational resolvent is not established here; the obstructions below already apply to its proposed positive functional.

Let G be the actual finite-rank Hermitian zero operator and V its strictly lower Volterra part, so G=V+V*. For a complex alpha with a=Re(alpha)>0 set

    R=(I+alpha V)^(-1), S=VR,
    C=(I-conj(alpha)V)(I+alpha V)^(-1)=I-2a S.

Volterra quasinilpotence makes R well defined. Exact congruence gives

    F=I-C*C=2a R* G R.

Consequently F and G have the same positive index, and F<=I. Furthermore S-V is trace class and quasinilpotent, hence has trace zero. Therefore

    tr F = 2a tr G - 4a^2 ||S||_HS^2,
    n_+(G) >= tr F.

This is invariant under adding zero dimensions. Together with the zero-side relation simple >=2 n_+(G)-N, it gives the candidate proportion 4a-8a^2 J-1, where J=lim ||S||^2/N. Carleman determinant multiplication also gives the exact identity

    det(I-F)=exp(-2a tr G).

If r=n_+(G), concavity of log, including possible negative eigenvalues of F, yields

    tr F <= r(1-exp(-2a tr G/r)).

Thus this determinant improves the elementary trace cap.

## Flat ordered functional and numerical outcome

For flat u=1/lambda, let g=P_+ 1_[0,1]. The finite polynomial functional is

    lim ||f(V)||^2/N
      = lambda int_R |f(g/lambda)|^2
        + lambda sum_{r>=1} int_[0,1] |f^(r)(g/lambda)|^2/[r!(2r+1)!].

The sum is finite for a polynomial. Applying the resulting rational candidate to S=V/(1+alpha V), with D=|1+alpha g/lambda|^2, gives

    J = lambda^(-1) int_R |g|^2/D
        + lambda sum_{r>=1} |alpha|^(2r-2) r!/(2r+1)! int_[0,1] D^(-r-1).

This positive series converges. That fact alone does not justify exchanging the asymptotic limit with a rational functional: the original Taylor series has zero radius because of the Hardy-height moments.

Numerical one-dimensional integration, including complex alpha, gives at lambda=1:

- elementary trace-cap simple bound: maximum 0.5541401914 at real alpha=1.704524;
- determinant-enhanced rank bound: maximum 0.5915933311 at real alpha=1.14925955;
- proposed stronger atom-count inequality considered below, even if granted, gives only the flat baseline 2/3 in the limit alpha->0.

These are numerical research checks, not interval certificates. The exact class ceilings below do not depend on the numerical optimization.

## Exact all-profile obstruction for the elementary Cayley trace cap

This does not require optimizing the flat window. For every feasible u>=0 supported in an interval of width lambda<=1 and every Re(alpha)=a>0, put

    w_t(x)=2a u(x)/|1+alpha g(t)u(x)|^2,  t in [0,1].

Since Re(g(t))=1/2,

    w_t(x)=1-| (1-conj(alpha)g(t)u(x))/(1+alpha g(t)u(x)) |^2,

so 0<=w_t<=1. The Hardy contour identity converts the zero-prime part of tr F/N into int_[0,1] int w. The one-prime-pair term of the general divided-difference functional is exactly

    int_[0,1] int_{x>y} (x-y) w_t(x)w_t(y).

All further paired terms are nonnegative and are subtracted. Thus the formal rational functional satisfies

    tr F/N <= int_[0,1] [int w_t - int_{x>y}(x-y)w_t(x)w_t(y)].

On 0<=w<=1, the bracketed functional is increasing pointwise: its variational derivative is 1-int |x-y|w(y)dy >=1-lambda^2/2>0. Its maximum is at w=1 on the whole interval and equals lambda-lambda^3/6. Therefore

    tr F/N <= lambda-lambda^3/6 <=5/6.

The elementary trace-cap simple bound is consequently at most 2/3 for EVERY profile u and complex alpha in this class. This does not rule out the determinant refinement, extra zero-side information, or a different statistic.

## Why the obvious higher-degree inner-function amplification also fails

For a rational inner product C(z)=product_{j=1}^d (1-conj(alpha_j)z)/(1+alpha_j z), let f=1-C. Telescoping I-C(V)*C(V) expresses it as a sum of d congruences of G; this only guarantees n_+(I-C*C)<=d n_+(G). The corresponding rank certificate divides its trace by d.

The Hardy identity and the nonnegative derivative terms show that its formal trace per N is at most

    int_x int_[0,1] [1-|C(g(t)u(x))|^2] <=lambda<=1.

Hence this degree-counting method gives simple <=2lambda/d-1, already nonpositive for d>=2. Any useful extension must improve the index theorem itself, rather than merely raise the Cayley degree. Such an improvement is not true for arbitrary Volterra kernels: integrating many congruences can increase rank even when G has rank one.

## A separate ceiling for the adaptive spectral-clamp formula

A separate argument gives the valid adaptive bound

    simple/N >= [4 tr(BG)-tr((BG)^2)]/N-2,

with B=f(G), 0<=B<=I. Pointwise optimization makes f(lambda)lambda equal to min(lambda,2) on lambda>=0, and zero on negative eigenvalues. In a PSD configuration this yields

    2-D + int (lambda-2)_+^2 dmu(lambda).

There is a short exact upper bound on what this particular formula can ever certify from a PSD spectrum with the already-computed first three moments. For every lambda>=0,

    (lambda-2)_+^2 <= (9/64)lambda(lambda-4/3)^2.

For lambda>=2 the difference is exactly (lambda-4)^2(9lambda-16)/64; below2 it is nonnegative by inspection. Consequently the fully optimized clamp expression is at most

    9/4 - (11/8)D + (9/64)M3.

For the MT cosine moments D=1.3274992963205885 and M3=1.9707225761613916, this is 0.7018213298318865. A numerically optimized cubic majorant reduces the ceiling to 0.7009050236759083.

This is an obstruction to this scalar adaptive formula by itself, even with ideal full spectral knowledge in a PSD-compatible case. It does not obstruct a theorem that exploits additional negative-index or off-line-pair information, nor is it an assertion that RH is false or true. If G is known to be PSD for the actual zeros, its geometric meaning supplies information stronger than this formula.

An exploratory CUE Gram experiment supports the direction of the obstruction: six N=512 samples gave average tail gain only0.0009336, with cubic defect -0.01216 close to the analytic -0.0117753. This experiment is not a certified limit and is unnecessary for the polynomial inequality above.

## An exact adversary for every flat ordered polynomial moment

A stronger abstract obstruction matches the entire flat ordered Gram, not just its first few entries. This is a tracial model, not an actual zeta-zero configuration or an actual Volterra operator.

Set a_r=r!/(2r+1)! for r>=0 and

    w_n=a_(n-1)-2a_n+a_(n+1), n>=1.

These weights are strictly positive because a_(r+1)/a_r=1/(4r+6). Telescoping gives

    sum_n n w_n=1,
    sum_(n>r) (n-r)w_n=a_r.

Let J_n be the n-by-n Jordan block with unit superdiagonal. On t in I=[0,1], take the direct integral of blocks V_n(t)=g(t)I_n+J_n with trace weights w_n dt. On R outside I take the scalar block V(t)=g(t), with Lebesgue trace. The scalar part has G=V+V*=0; the nonzero support of G has trace dimension one. Although the ambient trace of the identity is infinite, every polynomial f(V) with f(0)=0 has finite Hilbert-Schmidt norm.

Orthogonality of different superdiagonals gives

    tr|f(g I_n+J_n)|^2
      = sum_(r=0)^(n-1) (n-r)|f^(r)(g)|^2/(r!)^2.

Summing the weights therefore gives EXACTLY

    tr|f(V)|^2
      = int_R |f(g)|^2
        + sum_(r>=1) int_I |f^(r)(g)|^2/[r!(2r+1)!],

for every polynomial. Polarization matches every ordered mixed moment. Also tr V^k=int_R g^k=0 for k>=2, so the pure-trace constraints are satisfied. The trace of G is one.

Inside I, G_n=I_n+J_n+J_n* has eigenvalues

    1+2cos(k*pi/(n+1)), 1<=k<=n.

Pair the spectrum about one. A pair 1+-c with c>=1 is a legal abstract bad pair: choose real orthogonal p,q with squared norms (1+c)/2 and (c-1)/2, and x=p+iq; then x^T x=1 and xx^T+conj(x x^T) has eigenvalues1+-c. A pair with 0<=c<1 is a sum of two unit-norm positive atoms. An unpaired middle eigenvalue1 is one simple atom. The boundary pair {0,2} is a double atom.

The resulting weighted simple population is

    sum_n w_n #{k: 0<1+2cos(k*pi/(n+1))<2}
      =0.6998737298919733...,

while the positive index is0.8499368649459866.... The tail beyond n=13 is below10^-17 at this precision. The first weights are 0.6833333333,0.1345238095,0.01435185185,0.001061207311.

Thus a certificate using only the full flat ordered Gram, pure zero traces, and the generic unit-norm/simple versus normalized bad-pair algebra cannot prove85%. It already admits this roughly70% model. This statement does not exclude use of quantitative frequency marks, genuine Volterra quasinilpotence, or other evaluation geometry. A later translation realization preserves bare commutation identities; the marked moments in ordered_hierarchy_20260905.md distinguish it. The model is not claimed to arise from zeta zeros. Finite-degree comparisons can be approximated by truncating the height integrals and the Jordan sizes; the margin to85% is large.


## 4. Exact literal exponential-atom counterexample

Work on the frequency interval [0,1]. Let

    m=(1,2,2),  v=(1,sqrt(2),sqrt(2)),
    Gamma=diag(0,-omega,omega),
    G(x,y)=sum_j m_j exp(i gamma_j(x-y)).

Each exponential has norm 1, so G is exactly one unit atom and two double atoms, with N=5 and rank r=3. The finite-rank state equation for the Cayley deficit reduces, up to a unitary factor, to

    U = exp(M),   M=-a vv* - i Gamma.

Its defect has the exact trace

    tr F_a = 3-||U||HS^2.                  (4)

For completeness, the state-space relation is exact: if u(x) collects the weighted exponential atoms and U'= -a u(x)u(x)* U, then the nonzero eigenvalues of F_a are those of I-U(1)U(1)*. Removing the rotating diagonal phase gives the constant generator M above.

The characteristic polynomial of M is

    lambda^3 + 5a lambda^2 + omega^2 lambda + a omega^2.

Choose

    a0 = 6 pi/(5 sqrt(2)),
    omega0 = 2 pi sqrt(5/2).

Then omega0^2=125 a0^2/9, and the three distinct eigenvalues of M are

    -5a0/3,   -5a0/3 + 2 pi i,   -5a0/3 - 2 pi i.

Consequently the matrix exponential is exactly scalar:

    exp(M)=exp(-5a0/3) I.

Thus

    tr F_a0 = 3[1-exp(-10a0/3)].           (5)

This attains the rank/determinant bound above exactly, with r=3 and N=5. In contrast, the proposed integer-atom bound would require

    tr F_a0 <= 3-exp(-2a0)-2exp(-4a0).

Strict convexity gives

    exp(-2a0)+2exp(-4a0) > 3exp(-10a0/3),

so the proposed inequality fails, with no numerical inference needed.

Numerical values, for orientation:

| quantity | value |
|---|---:|
| a0 | 2.66572976289501974821... |
| omega0 | 9.93458826579610123443... |
| actual tr F_a0 | 2.99958496744193766982... |
| proposed integer upper bound | 2.99511620163877443923... |
| violation | 0.00446876580316323060... |

The three frequencies can be translated without changing the deficit, so the centered notation does not impose a restriction on positive ordinates.

Split each of the two double atoms into a reflected complex pair with arbitrarily small nonzero displacement. The resulting literal exponential kernel converges to G in Hilbert-Schmidt norm; its finite-rank Volterra state equations and Cayley deficit vary continuously. Therefore the strict failure survives. The perturbed configuration has only one line zero out of five, and two off-line pairs. This does not claim compatibility with every zeta arithmetic statistic; it refutes the proposed universal zero-side inequality for this exact atom geometry.



# A rigorous ceiling for one-piece derivative mollification

Source functional: Conrey–Farmer–Kwan–Lin–Turnage-Butterbaugh,
*Short mollifiers of the Riemann zeta-function* (2025),
https://arxiv.org/pdf/2508.11108, equations (14)–(16), Section 7.
The one-piece asymptotic quoted there is unconditional for fixed θ<4/7.
The following ceiling is a new elementary deduction from that functional;
it is not a claim about every possible use of derivatives or mollifiers.

## Result

For every real C¹ pair P,Q with
P(0)=0, P(1)=1, Q(0)=1, Q(y)+Q(1−y)=β (β arbitrary),
and every R>0, 0<θ≤4/7, the paper's constant satisfies

    c(P,Q,R) > exp(R/4).

Consequently the standard Levinson certificate κ=1−log(c)/R is **strictly
less than 75% throughout this entire function class**. Increasing the
polynomial degrees or optimizing the derivative combination cannot make
this particular certificate reach 85%.

## Proof

Put B=∫₀¹P², C=∫₀¹P′², a=C/θ and w(y)=exp(Ry)Q(y).
Expanding the paper's square and integrating the mixed term gives

    c = (1+w(1)²)/2 + a∫w² + θB∫w′².

Cauchy–Schwarz gives C≥1 and BC≥1/4, so a≥7/4 and θB≥1/(4a).
Hence it suffices to lower-bound the energy
E=∫[a w²+(4a)⁻¹w′²].
For an interval of length 1/2 and prescribed endpoint values u,v, its exact
minimum is

    [(u²+v²)coth(a) − 2uv csch(a)]/2.

This follows by solving w″=4a²w and integrating by parts; the remainder
is the nonnegative energy of a function vanishing at both endpoints.
Let q=exp(R/2), M=w(1/2)=qβ/2 and D=w(1)=q²(β−1).
Applying this bound to the two half intervals yields

    c ≥ (1+D²)/2 + [(1+2M²+D²)coth(a)−2M(1+D)csch(a)]/2.

Since coth(a)≥1 and 0≤j=csch(a)≤3/8, the right side is at least

    H_j(β)=1+M²+D²−jM(1+D).

Indeed sinh(7/4)>8/3 follows already from the first three positive terms
of its Taylor series. Since H_j is affine in j for fixed β, it is enough
to treat j=0 and j=3/8. Write

    H_j(β)=A₂β²+A₁β+A₀,
    A₀=1+q⁴,
    A₁=−2q⁴−j q(1−q²)/2,
    A₂=q²/4+q⁴−j q³/2 > 0.

The minimum is A₀−A₁²/(4A₂). Set z=sqrt(q)=exp(R/4)>1.
To show that this minimum exceeds z, multiply by 4A₂. For j=0 the
resulting expression is

    z⁴ [z⁸−4z⁵+4z⁴−z+1].

The bracket expanded in v=z−1 has ascending coefficients
[1,3,12,32,54,52,28,8,1], all positive.
For j=3/8 the expression is z⁴/256 times

    247z⁸−192z⁶−1024z⁵+1042z⁴+192z³−192z²−256z+247.

Its expansion in v=z−1 is

    64−192v+432v²+4112v³+10332v⁴+11656v⁵
      +6724v⁶+1976v⁷+247v⁸.

The initial quadratic is 432(v−2/9)²+128/3>0; every remaining term is
nonnegative for v≥0. Thus both endpoint quadratics have minimum greater
than exp(R/4), proving the result.



# Fourier-normalized preconditioners: a concrete convex certificate

Research note, 2026-09-05. This is a useful certificate class and a precise description of its missing arithmetic input; no85% result is claimed.

## 1. Exact zero-side inequality

Let v_gamma(x)=sqrt(u(x)) exp(i L gamma x). A preconditioner B need only satisfy

    B>=0,   sup_(gamma real) <v_gamma,B v_gamma> <=1.

The stronger condition B<=I is unnecessary. Transform the actual zero operator by B^(1/2). Each simple on-line atom then remains positive with trace at most one. Bad pairs still have positive rank at most one. If N is the zero population and S the simple population, the same elementary decomposition argument gives

    S >= 4 tr(BG)-tr(BGBG)-2N.                 (1)

For completeness, write G'=P+Q_+-Q_-, A=P-Q_-, with tr P<=S and rank P<=S. Since Q_+Q_-=0,

    tr(G'^2)>=2 tr A-S+4 tr Q_+-4b
              >=4 tr G'-3S-4b
              >=4 tr G'-S-2N.

Here S+2b<=N. This proves (1).

In a finite Fourier frame, put D=diag(u). Exact equality <v_gamma,Bv_gamma>=1 for every gamma is equivalent to the diagonal sums of D^(1/2)(B-I)D^(1/2) being zero. Thus there are many nonzero feasible directions, including B with eigenvalues larger than one. Since G=D^(1/2) T D^(1/2), with T Toeplitz, this equality also forces tr(BG)=N. Then (1) becomes S/N>=2-tr(BGBG)/N.

## 2. Small convex optimization and its dual

For a PSD sample G, write H=G^(1/2)BG^(1/2), and a_j=G^(-1/2)v_(gamma_j). A finite set of Fourier constraints gives the concave quadratic problem

    maximize 4 tr H-tr H^2-2N,
    subject to H>=0, a_j* H a_j<=1.

Its dual, with y_j>=0, is

    minimize tr(2I-(1/2)sum_j y_j a_j a_j*)_+^2 + sum_j y_j-2N.

The gradient component is 1-a_j*H a_j, where H=(2I-(1/2)sum y_j a_j a_j*)_+. Strict feasibility gives strong duality. A finite grid relaxes the continuous Fourier constraint, so its dual remains an upper bound on the continuously constrained optimum for that sample. Fine-grid scaling of a primal matrix is only a numerical feasibility check until the trigonometric maximum is certified.

Four N=128 CUE samples had baseline values .6472-.7019 and optimized dual upper bounds .6993-.7522. The gain was approximately .05. These are sample diagnostics, not an asymptotic theorem. They show this class has more room than scalar spectral clamping, but give no numerical85% candidate.

## 3. Why the obvious safe directions fail at full flat bandwidth

For flat u, V is lower-triangular Toeplitz, hence V^2+(V*)^2 is also Toeplitz. Removing its Toeplitz projection gives zero. Furthermore every commutator [V^p,(V*)^q] is antisymmetric under reflection followed by transpose, while G^2 is symmetric. Consequently every Hermitian combination C of those commutators satisfies tr(CG^2)=0 and has no first-order benefit in (1).

The nontrivial gradient direction is

    A=G^2-Pi_Toeplitz(G^2),    B=I-epsilon A.

It has exact Fourier normalization and tr(A G^2)=||A||_HS^2. The useful part is the symmetric boundary correction in VV*+V*V. It requires an alternating fourth moment, unlike V^2+(V*)^2. A cosine-profile test with the latter safe seed showed only small, noisy gains; it supplied no confirmed nonzero limiting gain.

## 4. Exact Fourier region and a quantitative target

For flat support [0,lambda], write G(x,y)=F(x-y), d=x-y>=0, ell=lambda-d, and

    h_d(t)=F(d+t) conjugate(F(t)).

The non-Toeplitz part of G^2 along this diagonal is

    A(y+d,y)=int_0^ell k_ell(y,t) h_d(t) dt,
    k_ell(y,t)=1_(t<y)+1_(t<ell-y)-2(1-t/ell).

Its covariance kernel is

    W_ell(t,s)=2(ell-max(t,s))+2(ell-t-s)_+
               -4(ell-t)(ell-s)/ell.

Therefore

    ||A||_HS^2
      =2 int_(0<d<lambda) int_(0<t,s<lambda-d)
          W_(lambda-d)(t,s)
          F(d+t)conj(F(t))conj(F(d+s))F(s) dt ds dd.       (2)

The four signed Fourier frequencies are (d+t,-t,-d-s,s); their l1 sum is exactly2(d+t+s). The existing unconditional support covers d+t+s<1. The precise missing region is

    0<d<lambda, 0<t,s<lambda-d, d+t+s>=1.

This region disappears at lambda<=1/2. At full bandwidth it survives, and W changes sign. Thus positivity of the final norm does not supply the needed one-sided arithmetic estimate on the missing region.

To make the numerical size of a sufficient input explicit, suppose one could prove

    R=||A||_HS^2/N >=r,   ||A||_op<=L,   trG^2/N<=D.

Then B=I-epsilon A is feasible for0<=epsilon<=1/L, and (1) improves the baseline by at least2epsilon r-epsilon^2 L^2D. If r<=LD, choosing epsilon=r/(L^2D) gives gain r^2/(L^2D). At D=1.3274992963, reaching85% by this bound requires

    r/L >= sqrt(D(D-1.15)) approximately0.4854.

This states the required size, rather than merely naming an unknown fourth moment. The operator-norm condition is also unproved, and the finite CUE optimization suggests this particular certificate class is not an85% mechanism by itself.


## 10. Residue subtraction as one signed scalar estimate

This continues the trimmed route after the flat moment countermodels ruled out evaluating the clipped statistic from flat moments alone.

Select m actual off-line conjugate-pair operators `E_1,...,E_m`. Each E_j is Hermitian with at most one positive and one negative eigenvalue, including its positive multiplicity factor. Put

    A_ij = tr(E_i E_j),
    b_j  = tr(G E_j),
    t_j  = tr(E_j),
    d    = b-2t.

The real matrix A is positive semidefinite. Every relation `sum_j c_j E_j=0` implies `c.b=c.t=0`, so d lies in the range of A. Let `A^dagger` denote its Moore--Penrose inverse; no invertibility assumption is necessary.

For a real coefficient vector c, define `E(c)=sum c_j E_j`. Expanding exactly gives

    ||G-E(c)||^2+4trE(c)
      = ||G||^2 - 2 c.d + c^T A c.

The infimum is attained at `c=A^dagger d` and equals

    R_E(G) := ||G||^2 - d^T A^dagger d.

Crucially, `n_-(E(c))<=m` for every real c: each scalar multiple of a conjugate-pair atom still has at most one negative eigenvalue, and negative inertia is subadditive. The arbitrary-correction certificate S >= 4trG-2N-[||G-E||²+4trE+4n_-(E)] therefore gives the proved inequality

    S >= 4trG - 2N - R_E(G) - 4m.

If `trG=N+o(N)` and `m=o(N)`, the ONE sufficient signed scalar estimate is

    ||G||^2 - (b-2t)^T A^dagger (b-2t) <= 1.15N+o(N).

This does not bound the untrimmed HS norm, absorb the removed atom norm, or omit the trace change. The subtraction is retained as part of the quantity to estimate. Coefficients of the optimum correction can be large; the rank/inertia charge remains at most4m. All formulas are invariant under zero padding.



# Flat ordered moments: degree-eight slack diagnostic

Research checkpoint, 2026-09-05. Result: the degree-eight truncated tracial
positivity test remains feasible at zero two-trace slack. This calculation
produces no improved simple-zero bound. It retires this bounded test, not
all ordered-moment inequalities or the literal zero-atom geometry.

Let tau=tr/N, a=V, b=V*, H=a+b. At zero slack the zero-side argument gives
H=E+2F with mutually orthogonal projections E,F. Hence

    H^3-3H^2+2H=0,
    E=2H-H^2, F=(H^2-H)/2, I-E-F >= 0.

For the flat profile at bandwidth one, tau(H)=1, tau(H^2)=4/3, so

    tau(E)=2/3, tau(F)=1/6.

The known ordered moments tau(a^m b^n), m+n<=8, are the exact rational
entries generated by `verify/ordered_polynomial_functional.py`. Pure traces of powers
of a or b of degree at least two vanish. The regularized first-order
assignment tau(a)=tau(b)=1/2 occurs only in combinations giving tau(H).
All other words are treated as unknown tracial moments.

## Exact feasible witness

Average under a<->b and word reversal, and identify cyclic rotations.
Impose tau((H^3-3H^2+2H)q)=0 for every word q of length at most five,
including the empty word. Linear elimination leaves six free moments.
Choose these exact rational values, with denominator one million:

| Canonical word | Numerator |
|---|---:|
| aaabaaab | -5111 |
| aaabaabb | 24632 |
| aabaabab | 164982 |
| aababbab | 741260 |
| aabbaabb | 639692 |
| abababab | 1156934 |

Every remaining unknown moment is defined by the linear equations above.
This gives all four positive semidefinite matrices:

1. Ordinary Gram [tau(u* v)], over nonempty words of lengths at most four.
2. E-localized Gram [tau(u* E v)], over all words of lengths at most three,
   including the empty word.
3. F-localized Gram on the same words.
4. Complement-localized Gram [tau(u*(I-E-F)v)], over nonempty words of
   lengths at most three.

Their dimensions are 30,15,15,14 and their exact ranks are 26,8,8,7.
Rational symmetric elimination verifies PSD: every nonzero pivot is
positive and every zero pivot has its entire remaining column zero.
After removing their common algebraic nullspaces, their smallest
eigenvalues are approximately

    0.00134132256, 0.00319534233, 0.00326508927, 0.00324803529.

The rational verification is in `verify/slack_exact_witness.py`; run
`python verify/slack_exact_witness.py`. Its output is:

    EXACT_PSD 0 positive_pivots 26 zero_pivots 4
    EXACT_PSD 1 positive_pivots 8 zero_pivots 7
    EXACT_PSD 2 positive_pivots 8 zero_pivots 7
    EXACT_PSD 3 positive_pivots 7 zero_pivots 7

## Scope

Consequently no contradiction at flat two-trace equality follows from a
sum of these degree-eight Gram/localizer positivity constraints and the
listed trace identities. The calculation retains the simple/double
projection masses, including constant vectors in the E and F localizers.
It is stronger than merely testing the ordered Hankel/Gram matrix.

This witness is a truncated moment functional. It does not construct a
Volterra operator or prove realizability by zeta-zero exponential atoms.
Higher-degree identities, other noncommutative localizers, or genuinely
geometric information could still separate. None was pursued after this
bounded degree-eight diagnostic.


## Finite weighted pair bounds: source audit and an explicit obstruction

Research note, 2026-09-05. Sources: [Carneiro–Milinovich–Ramos, arXiv:2310.01913](https://arxiv.org/pdf/2310.01913), especially §2.1, (2.8)–(2.10); and [Carneiro–Chandee–Chirre–Milinovich, arXiv:2108.09258](https://arxiv.org/pdf/2108.09258), especially §2.1 and Theorem7. Both papers assume RH. Their constants1.3208 and1.3302 concern sufficiently long intervals. The former proof retains a boundary contribution depending on its chosen test function; dividing it by interval length makes it negligible only in the long-interval regime. The latter paper supplies a finite-interval optimization problem, not the same long-average constant for every interval.

### 1. Precisely what survives for actual complex ordinates

Let z_rho=(rho-1/2)/i, with |Im z_rho|<=1/2, and use a conjugation-compatible finite zero sum (or the existing entire height weight). Put w(z)=4/(4+z^2). The identity

    w(z-z')=2pi int_R exp(-4pi|u|)exp(2pi i u(z-z'))du

is valid on the relevant strip. Because the zero multiset is closed under conjugation, reindexing the second zero gives

    sum_(z,z') h(z)h(z') exp(i alpha L(z-z')) w(z-z')
      =2pi int_R exp(-4pi|u|)
          |sum_z h(z) exp(i(alpha L+2pi u)z)|^2 du >=0.

Thus the positivity of this analytically continued F is not the failed step.

The upper-bound proofs also use domination of a translated test by the untranslated one. On real zero differences, the modulation has modulus one and the test g is nonnegative. This domination fails off the real line. Take just a conjugate pair z=gamma+-iy, 0<y<1/2, and g(x)=(sin(pi x)/(pi x))^2. Its untranslated pair sum is

    2+2 w(2iy) g(iLy/pi),

whereas modulation by a real xi changes it to

    2+2 w(2iy) g(iLy/pi) cosh(2xi Ly).

The ratio is unbounded. On a conjugate pair this modulation is unitary for the indefinite exchange metric, but not for a positive Hilbert norm. It preserves inertia while allowing arbitrarily large amplification. Consequently inertia alone cannot replace the needed upper domination.

### 2. The finite weighted target already exceeds these proofs' information

There is an explicit positive model satisfying both positivity conditions used in the source proofs and the complete known band |alpha|<=1. Set eta=1/100 and

    dmu(alpha)=min(|alpha|,1)dalpha+delta_0
                +(1/5)(delta_(1+eta)+delta_(-1-eta)).       (1)

Its inverse Fourier measure is

    delta_0+[1-sinc(pi x)^2+(2/5)cos(2pi(1+eta)x)]dx.       (2)

Both measures are nonnegative. Here sinc(pi x)=sin(pi x)/(pi x).

An elementary verification of (2): write y=pi x. If y^2>=5/3, use sinc(y)^2<=1/y^2 and cos>=-1. If y^2<=5/3, the alternating cosine series gives

    sin(y)^2<=y^2-y^4/3+2y^6/45.

At eta=0 the density is consequently at least

    P(y^2),   P(q)=(90-105q+50q^2-8q^3)/225.

P is decreasing, since its derivative numerator -105+100q-24q^2 is strictly negative, and P(5/3)=91/1215. Changing eta from0 to1/100 changes the cosine term by at most (1/125)|y|<4/375. This is smaller than91/1215. Positivity follows.

For every real nonnegative test g, multiplying the nonnegative pair measure (2) by cos(2pi xi x)<=1 yields exactly the translated-test domination used by the two papers. If ghat<=0 outside[-1,1], positivity of (1) gives the other inequality in their framework. Thus (1) satisfies all those abstract constraints, not just a few triangular tests. Its average over long intervals tends to1. The isolated masses can also be replaced by narrow positive smooth bumps outside the known band, using the strict positivity margin above.

This is a countermodel to the sufficiency of those analytic inputs. It is not claimed to be the pair correlation of actual zeta zeros or of a realizable point process.

### 3. Numerical comparison with the exact chosen cosine target

For s=1.99, use the already-derived autocorrelation A_s from the cosine profile in the arithmetic target above. Its unknown-band mass is

    M_s=2 int_1^s A_s(t)dt=0.1412533266567336... .

The85% certificate requires its unknown-band cost to be at most

    0.21389703648923175... .

Model (1) instead gives the explicit value

    M_s+(2/5)A_s(1.01)=0.22694581961912824...,

or weighted mean1.6066582288050464.... Combined with the known-band cost, the two-trace simple-zero bound is only0.8369512168701034.... These decimals are ordinary quadrature of explicit trigonometric expressions; the gap exceeds0.013, so no fine numerical distinction is involved.

Therefore the published long-average estimate cannot establish the required finite weighted upper bound, even if its RH-dependent domination were granted. A successful route needs both a replacement for complex modulation and additional finite-band arithmetic information excluding a spike of the form (1).


## Half-interval Schur and additional matrix tests

For an actual finite zero kernel $G=UMU^*$, restriction of its distinct
exponential features to any nonempty interval preserves their linear
independence. For its two interval blocks $A,B,D$, this gives exactly
$D-B^*A^\dagger B=0$. Neither half supplies an independent half-sized rank
budget. On equal halves, the first inverse-Schur quadratic term needs
$3\sigma<2$; it is not a width-one fourth-level statistic.

A valid auxiliary correction is $E=cH^2\ge0$, where $H$ is a Hermitian
Schur cut of $G$ to edge length less than $1/2$. Its optimized gain is
$[(\operatorname{tr}GH^2-2\operatorname{tr}H^2)_+]^2/
\operatorname{tr}H^4$. All four-level moments are inside the support range.
For a flat profile and real symmetric filter $h$, its numerator per zero is
$-1+\iint|x-y|(2h-h^2)\,dx\,dy\le-2/3$.
Nonconstant profiles can produce a positive correction, but the bounded
joint profile/filter searches did not recover their increased baseline
cost. Those numerical searches are not a universal impossibility theorem.


## A legal confluent-pair four-level test and its cost

Research derivation, 2026-09-05. No new percentage is proved. The candidate
zero-side inequality below remains unproved; a valid arithmetic lower
bound already makes this positive-window version uncompetitive.

### Exterior support and the normalization problem

For four real frequency coordinates x1,...,x4, every permutation satisfies

    sum_i |xi-x_(pi(i))| <= 2(top two sum - bottom two sum).

Consequently multiplication on exterior frequency space by the indicator
of top-two sum minus bottom-two sum <1 is a positive compression that
keeps every determinant term inside Fourier l1 support <2, including
alternating cycles. This is not restricted to ordered two-path moments.

Ordinary exterior atoms lose the unit-norm multiplicity normalization:
their squared norm is the determinant of the individual feature Gram.
It tends to zero when distinct real zeros coalesce. For a closed tuple
containing b reflected off-line pairs, the exterior reflection sign is
(-1)^b. Nonclosed reflected tuple orbits give signed rank-two blocks.
Therefore positivity on real tuples cannot be applied unchanged to
unconditional complex zeros.

### A confluent pair feature

Write sinc(t)=sin(pi t)/(pi t). Use frequency coordinates

    x=m+d/2, y=m-d/2,
    m in an interval of width <1/2, 0<d<1/2.

For a nonnegative window measure W(dm,dd), let

    C=integral d^2 W(dm,dd),
    psi(z,w)(m,d)=d exp(2pi i(z+w)m) sinc(d(z-w))/sqrt(C).

This is the analytic divided exterior determinant. It is symmetric in
z,w, with its confluent value at z=w defined by continuity. For real z,
||psi(z,z)||=1. For a closed off-line pair z,bar z its norm is at least
one, since sinh(t)/t>=1. Its reflection is fixed, so that pair supplies
a positive rank-one atom; the two signs from the exterior numerator and
the divided difference cancel.

For two frequency pairs (m,d),(m',d'),

    top two sum - bottom two sum
      =2 max(|m-m'|,(d+d')/2)<1.

Convex interpolation inside the divided determinants preserves this
bound. Thus the second trace of the pair operator uses legal four-level
support while the coalescent feature exp(4pi i z m) has z-bandwidth one.

Enumerate the actual zeros with multiplicity and set

    B=sum_(j<k) psi(zj,zk) tensor psi(bar zj,bar zk)*.

B is Hermitian. The proposed inequality was

    ||B||_HS^2 >= b + sum_real binom(multiplicity,2),                 (1)

where b is the number of off-line pairs counted with multiplicity.
If true, it would imply S>=N-2||B||^2. It is immediate for all-real
configurations, because B is positive and coincident pair atoms have
unit norm. For mixed complex zeros, the nonclosed pair orbits are signed;
(1) has NOT been established. Their naive inertia budget is quadratic
in the total zero count and is not a usable substitute.

### A sufficient arithmetic closure of this window family

In the sine-process moment functional, all pair atoms are positive.
The Hilbert--Schmidt square is a sum of nonnegative terms. Keeping only
the terms in which the two unordered index pairs coincide gives

    lim tr(B^2)/N >= (1/2) integral K(t)^2(1-sinc(t)^2) dt,            (2)

where K(t)=integral sinc(d t)^2 nu(dd), and nu is the probability measure
obtained by normalizing the d^2-weighted gap marginal of W.

For 0<d<=e<=1/2, direct Fourier convolution gives

    J(d,e):=(1/2) integral sinc(dt)^2 sinc(et)^2(1-sinc(t)^2) dt
       =(1/2)[1/e-d/(3e^2)-1+e/3+d^2/(6e)-d^3/(30e^2)].

Indeed the integral of the first two squared sinc factors is
1/e-d/(3e^2). Their Fourier convolution is the law of the sum of two
independent triangular variables X_d,X_e. Since d+e<=1, multiplication
by sinc(t)^2 integrates to 1-E|X_d+X_e|, and

    E|X_d+X_e|=e/3+d^2/(6e)-d^3/(30e^2).

The displayed J decreases in both d and e on this triangle. For example,
twice its d-derivative is at most -1/(3e^2)+1/3<0; twice its e-derivative
is at most -1/(3e^2)+1/3+1/15<0. Therefore

    J(d,e)>=J(1/2,1/2)=17/60.

Integrating against nu(dd)nu(de) proves from (2) that tr(B^2)/N>=17/60.
Even granting (1), this candidate's lower-bound expression is at most

    1-2(17/60)=13/30=43.333... percent.

This uses neither an invented rank bound nor an RH assumption about the
actual zeros: it is a lower bound on the sine-side moment functional
that the proposed legal four-level arithmetic transfer would evaluate.
It retires this positive confluent-pair window family before a costly
attempt to prove (1). The signed compression considered next requires
a different argument.

### Signed compression in the gap variable also cannot improve the baseline

Now allow a single even entire gap profile P with Fourier support in
[-1/4,1/4], P(0)=1, including signed or complex Fourier coefficients:

    psi(z,w)(m)=exp(2pi i(z+w)m) P(z-w).

Normalize the center window so that its total mass is one. The hoped-for
off-pair atom bound would additionally require |P(2iy)|>=1 for all real y.
The following obstruction holds without imposing that extra condition.

Put Q(t)=|P(t)|^2 on the real line. Its entire continuation is P P#,
so Q has Fourier support in [-1/2,1/2], Q(0)=1, and Q(t)>=0. The
same-pair contribution to tr(B^2)/N is

    (1/2) J(Q),  J(Q)=integral |Q(t)|^2(1-sinc(t)^2) dt.

Write q for the Fourier transform of Q. On the interval [-1/2,1/2],

    J(Q)=||q||_2^2-double_integral (1-|x-y|)q(x)conj(q(y)) dx dy,
    integral q=1.

The unrestricted quadratic minimizer is exactly the Montgomery--Taylor
profile

    q*(x)=cos(sqrt(2)x)/(sqrt(2)sin(1/sqrt(2))),
    J(Q*)=D_MT-1,
    D_MT=1/2+cot(1/sqrt(2))/sqrt(2)=1.3274992963205885... .

The minimizing condition implies J(Q)=J(Q*)+J(Q-Q*) on this affine
constraint. The kernel 1-|x-y| is nonnegative and has maximum row integral
3/4, so Schur's bound gives J(R)>=||r||_2^2/4. Evaluation at any real t
has norm at most one from L2 of this width-one frequency interval.

At the explicit point t=3/2,

    Q*(3/2)=-6pi cot(1/sqrt(2))/(sqrt(2)(9pi^2-2))
            =-0.1796456739574475... .

Since Q(3/2)>=0,

    J(Q)>=D_MT-1+|Q*(3/2)|^2/4.

Consequently, for every such signed compression,

    tr(B^2)/N >= (D_MT-1)/2+|Q*(3/2)|^2/8
                =0.1677837191817474... .

Even granting the unproved zero-side inequality (1), the resulting
simple-line lower-bound expression is therefore at most

    2-D_MT-|Q*(3/2)|^2/4=0.6644325616365051... .

This is below the inherited cosine baseline. No finite-dimensional search
or unproved effective-rank estimate is used. The numeric values display
explicit analytic expressions, rather than being optimization certificates.
Non-product exterior compressions remain outside these two calculations.
