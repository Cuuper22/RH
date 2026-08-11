# R1a audit: allocation-capacity no-go at the current interface

## Verdict

The current `PrincipalCyclicBlock` boundary is uninhabited for both frozen
families.  This is stronger than the earlier common-lattice rank kill and the
one-window normalization kill:

```text
F : Family14999 Z  ->  not PrincipalCyclicBlock F
F : Family19999 Z  ->  not PrincipalCyclicBlock F
```

The exact Lean theorems are
`R1aAllocationNoGo.no_principal14999` and
`R1aAllocationNoGo.no_principal19999`.  They do not assume a common lattice,
alias-free windows, critical coefficient count, or any particular number of
channels.  Consequently oversampling, noncommensurable periods, arbitrary
real signs, and complex phases cannot repair R1a while the consumed fields of
the current interface remain unchanged.

This result does not contradict the finite stability inequality.  It says
that the particular mean-one top-hat principal block required upstream of the
frozen quartic constants cannot coexist with the frozen full profiles and hat
normalization.

## Capacity calculation

Write

\[
 \ell=\log(T/2\pi),\quad L_T=\mu\ell,
 \quad E_T=\int |\varphi_{0,T}(u)|^2\,du,
 \quad W_T=\int \sum_j|\varphi_{j,T}(u)|^2\,du.
\]

Let `mass_T` be the integral of the normalized distinguished local profile on
the active top-hat cell `[-p/2,p/2]`.  The `k=1`, zero-shift instance of
`translated_products_locally_uniform`, with error `1/100`, gives

\[
 \operatorname{mass}_T\geq \frac{99}{100}.
\tag{1}
\]

The distinguished energy ratio tends to `mu`, and `2/5 < mu` for both
families, so eventually

\[
 E_T>\frac25 W_T.
\tag{2}
\]

The almost-everywhere reconstruction identity, together with nonnegativity of
every square summand in `windowEnergy`, gives
`|phi_0|^2 <= windowEnergy` almost everywhere.  Exact change of variables and
the proved full profile integral give

\[
 W_T=\sigma\ell A,
 \qquad
 A=\int_{-1/2}^{1/2}v(s)\,ds.
\tag{3}
\]

On the active physical interval, `|s| <= mu*p/(2*sigma)`.  The exact
polynomial monotonicity certificates give

\[
 v_{8686}(s)\leq \frac{1189}{1000},
 \qquad
 v_{9506}(s)\leq \frac{2509}{2000}.
\tag{4}
\]

Therefore

\[
 \operatorname{mass}_T E_T
 \leq L_T p v(0)=\mu\ell p v(0).
\tag{5}
\]

Combining (1)--(5) would require

\[
 \frac{99}{100}\frac25\sigma A
 < \mu p v(0).
\tag{6}
\]

Exact rational arithmetic proves the strict reverse inequality:

| family | `mu*p*v(0)` | `(99/100)*(2/5)*sigma*A` | right minus left |
|---|---:|---:|---:|
| `Family14999` | `528999179/1000000000` | `57223741884588397751/96314982400000000000` | `6273195269588948151/96314982400000000000` |
| `Family19999` | `1041026753/2000000000` | `50684669414097/64000000000000` | `17371813318097/64000000000000` |

This contradiction uses a deliberately loose energy floor `2/5` and L1
error `1/100`; it does not depend on taking a delicate limiting equality.

## Fields actually consumed

The proof uses exactly these `PrincipalCyclicBlock` fields:

- `support_pos`;
- `fill_pos`;
- `periods_pos`;
- `zero_alias_reconstruction`;
- `distinguished_period`;
- `distinguished_energy_ratio`;
- `distinguished_channel_energy_pos`;
- `local_profile_integrable`;
- `translated_products_locally_uniform`, only for `k=1` and zero shift;
- `windows_smooth` and `windows_compact`, only to justify integration of the
  distinguished window square.

The proof does **not** use:

- `bandwidth_pos`, `strict_fourier_support`, or `fill_le_one`;
- `critical_count`, `channel_grid_count`, or `column_address_bijective`;
- `real_aliases_summable` or `real_aliases_cancel`;
- `full_gram_summable`;
- `local_profile_nonneg`, `local_profile_support`, or
  `local_profile_mean_one`;
- `distinguished_columns`, `distinguished_exhaustive`, or `block_dimension`.

In particular, this is an allocation/normalization contradiction, not another
alias-rank argument.

## Exact replay

`verify/r1a_allocation_nogo.py` uses only Python integer arithmetic and
`fractions.Fraction`.  It reconstructs both even polynomial integrals from
their raw coefficients, reconstructs the two active edges, and independently
checks monotonicity by converting `-v'(s)/s` on the exact squared active
interval to the Bernstein basis.  Every Bernstein coefficient is strictly
positive.  It then reconstructs both sides and both strict gaps in the table.
The committed transcript is `verify/r1a_allocation_nogo.out`.

## Surviving scope

There is no surviving modulation or coefficient-count architecture inside
the current `PrincipalCyclicBlock` interface for either frozen family.  A new
route must change at least one consumed requirement: for example the
distinguished energy normalization, the sharp top-hat target, the frozen full
profile, or the energy/profile/translated-product semantics tying the block to
those data.  An aggregate-channel redesign is outside this no-go only if it
also changes those semantics; changing the principal-block definition alone
does not evade (1)--(6).  Any such change requires a fresh trace normalization,
zero-side principal-compression argument, and block-moment calculation.  Merely
changing lattice commensurability, phases, channel count, or oversampling
cannot evade (1)--(6).
