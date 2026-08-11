# Root 95% cycle 4: unconditional support-two plus quartic checkpoint

## Outcome

The signed-shift arithmetic theorem of `arithmetic95_cycle1.md` proves the
saturated pair-trace asymptotic for every fixed support

\[
\sigma<2.
\]

The nested-quartic stability certificate of `certificate95_cycle1.md` uses a
principal block of absolute bandwidth \(\mu<1/2\).  Its fourth trace has total
Fourier support \(4\mu<2\), so it lies wholly inside the same unconditional
range.  The two results can therefore be used simultaneously, with no
conditional prime-pair or higher-correlation input.

Let

\[
D_2=1.067717376064704\ldots
\]

be the limiting optimal saturated pair cost as \(\sigma\uparrow2\).  The
unrefined rank--trace certificate gives

\[
2-D_2=0.932282623935296\ldots .
\]

For the nested block, write the simple-zero proportion as

\[
s/N=2-D_2+\varepsilon.
\]

The stability tail and the exact four-moment trimmed problem give

\[
\varepsilon\geq
\mathcal L_\mu\!\left({D_2-1-\varepsilon\over2\mu}\right).
\]

On letting \(\mu\uparrow1/2\) through strict values, the unique fixed point is

\[
\varepsilon_2=0.006030703115653\ldots .
\]

Consequently

\[
\boxed{
\liminf_{T\to\infty}{N_0^s(T,2T)\over N(T,2T)}
\geq0.938313327050949\ldots .}
\]

This improves the unconditional support-two second-trace checkpoint by

\[
0.006030703115653\ldots,
\]

and improves the previous accepted support-\(3/2\) quartic checkpoint
\(0.86725400194550\ldots\) by more than seven percentage points.

## Strict-parameter formulation

No endpoint assertion is needed.  Choose any sequence of fixed parameters

\[
\sigma_j<2,\qquad \mu_j<1/2,
\qquad \sigma_j\uparrow2,\quad\mu_j\uparrow1/2.
\]

For each \(j\), the signed-shift theorem supplies the full pair trace at
support \(\sigma_j\), while the Rudnick--Sarnak diagonal expansion supplies
all four nested-block moments because \(4\mu_j<2\).  The finite-parameter
stability inequality then applies before either limit is taken.  Continuity of
the Euler solution and of the three-atom moment dual yields the displayed
limiting constant.

## Input inventory

1. The finite Weil-form compression and zero-side rank--trace decomposition
   accepted from the source PDFs.
2. The signed-shift-first all-block estimate from
   `arithmetic95_cycle1.md`, valid for every fixed \(\sigma<2\).
3. The exact principal-compression construction, four diagonal moments, and
   stability lemma from `certificate95_cycle1.md`.
4. The explicit three-atom primal/dual solution of the trimmed fourth-moment
   problem.

There is no RH assumption, no pair-correlation conjecture, no unproved
selector mean value, and no endpoint interchange.

## New floor and remaining gap

The operative unconditional floor for subsequent cycles is now

\[
\boxed{93.8313327050949\%}.
\]

The remaining distance to the target is

\[
\boxed{1.1686672949051\text{ percentage points}.}
\]

Every later certificate must improve this floor, or kill a precisely defined
method class and execute a concrete attack outside it.
