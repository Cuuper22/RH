> **Note**: This file is part of the 100% research program whose terminal result
> was [withdrawn](FINAL_100_RESULT.md). See [NARRATIVE_100.md](../NARRATIVE_100.md)
> for context.

# Zeta-100 arithmetic, cycle 4: exact zero-mode recombination and the reciprocity sign obstruction

## 0. Terminal output

This cycle takes the permitted **precise reciprocity-class kill plus first
third-stage completion** branch.  It does not claim support beyond two.

Set

\[
 \rho={1\over1001},\qquad L=H^\rho,\qquad
 P=H^{1/3},\qquad M=P^2.                                   \tag{1}
\]

The raw Type-III progression and its zero mode are kept together through
Poisson summation.  Their common main term cancels **exactly** before any
absolute value: the centered block is precisely the sum over nonzero dual
frequencies \(h\ne0\).  Thus no mixed raw/main terms remain in the dual
moment.

After the trace-safe reciprocity replacement from cycle 3, the surviving
self-dual \(j=j'=3\) coefficient tensor is invariant under exchanging the
two HB sides.  The reciprocal phases therefore pair as

\[
 e(z\bar a/b)+e(-z\bar a/b)=2\cos(2\pi z\bar a/b),          \tag{2}
\]

not with opposite signs.  The antisymmetric reciprocity projection is
identically zero.  Consequently, the precisely defined
recombination-plus-reciprocity class in Section 3 cannot improve the
remaining generic MD majorant

\[
 H^2L\,H^{o(1)}
 \quad\hbox{against}\quad
 {H^2\over L}H^{o(1)}.                                    \tag{3}
\]

Its exact sign obstruction remains

\[
                         \boxed{L^2=H^{2/1001}}.             \tag{4}
\]

The mandatory step outside that class keeps one two-factor HB convolution
unopened and performs a third multiplicative-Fourier difference.  For each
fixed shift, a product-residue large sieve gives

\[
 \boxed{|E_{\rm III}(\ell)|
        \ll P^{7/2}H^{o(1)}
        =H^{7/6+o(1)}}.                                    \tag{5}
\]

Equivalently, over the selected shift interval,

\[
 \boxed{\sum_{\ell\asymp L}|E_{\rm III}(\ell)|^2
        \ll P^7L\,H^{o(1)}
        =H^{7/3+\rho+o(1)}}.                               \tag{6}
\]

This first third-stage completion still misses the MD target
\(H^{2-\rho}\) by the explicit factor

\[
 \boxed{H^{1/3+2\rho}
        =H^{0.335331335\ldots}}.                            \tag{7}
\]

It is therefore not a support extension.  It is a completed calculation
which identifies the new loss: triangle summation over the variable
two-factor modulus \(b\asymp P^2\), not the already canceled zero mode and
not failure to exploit the individual product structure.

The unconditional endpoint and accepted capped-profile floor remain

\[
 \boxed{\sigma<2,\qquad
 \liminf_{T\to\infty}{N_{0,\mathrm{simple}}(T)\over N(T)}
 >0.96250068026-o(1).}                                     \tag{8}
\]

## 1. Recombine the raw progression and its zero mode first

Use the notation of cycles 2--3.  After fixing

\[
 a=x_1x_2\asymp P^2,\qquad b=y_1y_2\asymp P^2,             \tag{9}
\]

the third-factor equation is

\[
                         rax-kby=\ell.                      \tag{10}
\]

After the standard gcd split, the coprime core is

\[
 x\equiv \ell\,\overline{ra}\pmod{kb}.                     \tag{11}
\]

Poisson summation, with the \(y\)-weight inserted into the smooth
\(x\)-weight, is the exact identity

\[
 R_{a,b}(\ell)
 ={P\over kb}\sum_{h\in\mathbb Z}
 \widehat W_{a,b,\ell}\!\left({hP\over kb}\right)
 e\!\left({h\ell\overline{ra}\over kb}\right).             \tag{12}
\]

The shared main term is

\[
 \mathcal M_{a,b}(\ell)
 ={P\over kb}\widehat W_{a,b,\ell}(0).                     \tag{13}
\]

Keep (12) and (13) together.  Their difference is identically

\[
\begin{aligned}
 R_{a,b}(\ell)-\mathcal M_{a,b}(\ell)
 ={P\over kb}\sum_{h\ne0}
 \widehat W_{a,b,\ell}\!\left({hP\over kb}\right)
 e\!\left({h\ell\overline{ra}\over kb}\right).             \tag{14}
\end{aligned}
\]

Because \(kb/P\asymp P\), rapid decay restricts

\[
                              0<|h|\ll P H^{o(1)}.           \tag{15}
\]

Equation (14) is the requested main-term cancellation before absolute
values.  In particular, expanding the centered MD moment from (14) gives

\[
\begin{aligned}
 {1\over P^2}
 \sum_{\ell\asymp L}
 \sum_{\substack{0<|h_1|,|h_2|\ll P}}
 \sum_{a_1,b_1,a_2,b_2\asymp P^2}
 C_{\boldsymbol a,\boldsymbol b,\boldsymbol h,\ell}\,
 e\!\left(
 {h_1\ell\bar a_1\over b_1}
 -{h_2\ell\bar a_2\over b_2}\right),                       \tag{16}
\end{aligned}
\]

up to unit twists and \(H^{o(1)}\) gcd cases.  There is no \(h_\nu=0\)
term and hence no hidden raw--main or main--main contribution in (16).

The remaining task is cancellation in the fully nonzero dual sum (16).

## 2. Reciprocity acts with the wrong sign on the self-dual block

On the coprime core, cycle 3 proved

\[
 e(z\bar a/b)
 =e(-z\bar b/a)+O(|z|/(ab)),                               \tag{17}
\]

and the accumulated error is

\[
                         PL^2H^{o(1)}
                         =H^{1/3+2\rho+o(1)}=o(H).          \tag{18}
\]

Thus we may impose (17) at trace scale.

Let \(\mathcal R\) be the reciprocity involution

\[
 \mathcal R:(a,b,z)\longmapsto(b,a,-z).                    \tag{19}
\]

For the all-smooth \(j=j'=3\) block, after matching the two fixed smooth
windows, the coefficient tensor has the form

\[
                         \alpha_a\alpha_b\delta_z,          \tag{20}
\]

with real \(\alpha\) and

\[
                         \delta_{-z}=\overline{\delta_z}.   \tag{21}
\]

Hence (20) lies in the \(+1\) eigenspace of \(\mathcal R\).  Its
antisymmetric projection is exactly

\[
 {1\over2}\big(
 \alpha_a\alpha_b\delta_z
 -\alpha_b\alpha_a\delta_{-z}^{\,*}\big)=0.                \tag{22}
\]

Pairing a term with its reciprocal partner therefore gives (2).  There is
no algebraic minus sign to spend.  Removing the zero mode in (14) does not
alter (20)--(22), since \(h=0\) was itself in the symmetric eigenspace.

This is the exact sign obstruction: reciprocity changes the reading of the
phase, but on the self-dual Type-III coefficient it does not change the
sign of the observable.

## 3. Impossibility for recombination plus reciprocity alone

Define \(\mathscr C_{\rm rec}\) to consist of arguments which:

1. perform the exact raw/zero-mode recombination (12)--(14);
2. restrict to the large-determinant, low-gcd survivor of cycle 3;
3. pair all nonzero phases only through the reciprocity involution (19);
4. estimate the resulting symmetric and antisymmetric projections by
   triangle inequality, \(L^2\), divisor bounds, and the two completed
   dispersions of cycles 2--3, without a new completion in an HB factor or
   the variable modulus.

The antisymmetric projection vanishes by (22).  The symmetric projection
is the cosine kernel (2), whose coefficient majorant is the same as the
original nonzero-dual majorant.  Thus the class returns the generic
absolute two-dispersion scale from cycle 3,

\[
                         H^2L\,H^{o(1)}.                    \tag{23}
\]

The MD target is \(H^2/L\).  Therefore:

> **Reciprocity sign barrier.**  No argument in \(\mathscr C_{\rm rec}\)
> proves the Type-III MD estimate for any fixed \(\rho>0\).  Its exact loss
> is \(L^2=H^{2\rho}\).  The obstruction is the \(+1\), rather than \(-1\),
> reciprocity parity of the self-dual coefficient tensor.

This theorem does not rule out using the oscillation of the cosine kernel.
It rules out obtaining the needed gain from algebraic pairing alone.

## 4. Outside the class: a third multiplicative-Fourier difference

We now use that \(a=x_1x_2\) before treating its coefficient as arbitrary.
Fix \(\ell\) and \(b\asymp P^2\).  The nonzero part of (14), after smooth
separation, contains

\[
 \mathcal G_b(\ell)
 =
 \sum_{0<|h|\ll P}c_h
 \sum_{x_1,x_2\asymp P}
 \gamma_{x_1}\gamma'_{x_2}
 e\!\left({h\ell\,\overline{x_1x_2}\over b}\right).        \tag{24}
\]

Collapse only the **residue product**, not its coefficient:

\[
 \Gamma_r=
 \sum_{\substack{x_1,x_2\asymp P\\
 \ell\,\overline{x_1x_2}\equiv r\pmod b}}
 \gamma_{x_1}\gamma'_{x_2}.                                \tag{25}
\]

The divisor bound and the fact that the product interval has length
\(O(b)\) give

\[
                         \|\Gamma\|_2\ll P H^{o(1)}.        \tag{26}
\]

If \(d=(\ell,b)>1\), the residues in (25) live modulo \(b/d\) with
multiplicity \(O(dH^{o(1)})\).  The multiplicity factor \(d^{1/2}\) and the
modulus factor \((b/d)^{1/2}\) cancel, so (26) leads to the same final bound
uniformly in \(d\).

The additive large sieve on the interval \(0<|h|\ll P\) says

\[
 \sum_{0<|h|\ll P}
 \left|\sum_{r\bmod b}\Gamma_r e(hr/b)\right|^2
 \ll (b+P)\|\Gamma\|_2^2 H^{o(1)}
 \ll P^4H^{o(1)}.                                         \tag{27}
\]

Since \(\|c\|_2\ll P^{1/2}H^{o(1)}\), Cauchy in \(h\) and (27) yield

\[
                         |\mathcal G_b(\ell)|
 \ll P^{5/2}H^{o(1)}.                                     \tag{28}
\]

The \(b=y_1y_2\) convolution has

\[
 \sum_{b\asymp P^2}|\beta_b|\ll P^2H^{o(1)}.               \tag{29}
\]

Finally include the Poisson prefactor \(P^{-1}\):

\[
\begin{aligned}
 |E_{\rm III}(\ell)|
 &\ll {1\over P}
 \sum_{b\asymp P^2}|\beta_b|\,|\mathcal G_b(\ell)|\\
 &\ll P^{-1}\cdot P^2\cdot P^{5/2}H^{o(1)}
 =P^{7/2}H^{o(1)},                                        \tag{30}
\end{aligned}
\]

which proves (5).  Squaring and summing the \(L\) selected shifts proves
(6).

This is a genuine third difference: opening (27) produces

\[
 \sum_{r_1,r_2}\Gamma_{r_1}\overline{\Gamma_{r_2}}
 \sum_{0<|h|\ll P}e\!\left({h(r_1-r_2)\over b}\right),      \tag{31}
\]

so the new diagonal is equality of the **product residues**
\(\ell\overline{x_1x_2}\pmod b\), not equality of the original represented
integers or of the two-factor bases treated in cycles 1--3.

## 5. Exact remaining exponent after the third difference

From (6), the third-stage MD output is

\[
                         H^{7/3+\rho+o(1)}.                 \tag{32}
\]

The target is

\[
                         H^{2-\rho+o(1)}.                   \tag{33}
\]

Their ratio is

\[
                         H^{1/3+2\rho+o(1)},                \tag{34}
\]

which proves (7).  The loss in (30) is transparent:

* the product-residue large sieve uses both \(H^{1/3}\) factors on the
  \(a\)-side;
* the remaining \(b\asymp P^2\) values are still summed in \(L^1\);
* this last variable-modulus summation costs the uncanceled power which
  appears in (34).

Thus the third-stage calculation does not merely rename the old \(L^2\)
barrier.  It moves the obstruction from zero-mode/sign recombination to a
specific variable-modulus average and records its exact exponent.

## 6. Handoff

* Raw and zero mode recombine exactly: the centered dual sum has
  \(h_1,h_2\ne0\) only.
* Reciprocity parity of the self-dual Type-III block is \(+1\); paired
  phases form a cosine, so algebraic sign pairing supplies no saving.
* Exact \(\mathscr C_{\rm rec}\) loss: \(L^2=H^{2/1001}\).
* First third-stage product-residue completion:
  \(E_{\rm III}(\ell)\ll H^{7/6+o(1)}\).
* Induced MD output: \(H^{7/3+\rho+o(1)}\), missing the target by
  \(H^{1/3+2\rho}\).
* No support extension is claimed; the accepted floor remains
  \(0.96250068026-o(1)\).