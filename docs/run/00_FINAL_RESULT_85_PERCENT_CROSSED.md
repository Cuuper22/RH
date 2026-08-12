# Final result: the 85% gate is crossed

## Fixed unconditional certificate

Within the two uploaded PDFs' accepted zero-side framework and the completed
prime-side transfer, take

\[
\sigma=\frac{143}{100},\qquad
v(s)=1-\frac{169}{100}s^2\quad (|s|\le 1/2).
\]

The exact saturated pair-kernel calculation gives

\[
c_{\rm pc}
=\frac{2227707598259143}{2561811364469143},
\qquad
D=c_{\rm pc}^{-1}=1.1499764899\ldots .
\]

Arithmetic cycle 5 evaluates the required signed prime-pair trace for every
fixed support \(\sigma<3/2\).  In particular, it applies at \(143/100\).
The accepted rank--trace inequality therefore gives

\[
\boxed{
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
2-D
=\frac{1893603832049143}{2227707598259143}
=0.8500235101\ldots .}
\]

This is a strict fixed-parameter result, not an endpoint limit.

## Stronger limiting checkpoint

Arithmetic cycle 5 proves the signed-shift-first remainder bound

\[
R_{\rm HB}\ll
\left(T^{1+\eta}+T^{1/2+2\eta}\right)(\log T)^C,
\qquad 0<\eta<\frac12.
\]

It follows by retaining the smooth signed \(h\)-sum through Poisson summation,
using

\[
\sum_{r\pmod q}^{*}|S_H(\ell r/q)|
\ll q+H(\ell,q),
\]

and only then applying the fixed-divisor progression majorants and the actual
Poisson-frequency decay.  This removes the earlier \(AB\)/Watt loss and
permits every fixed connected support \(\sigma<3/2\).

Optimizing the saturated kernel as \(\sigma\uparrow3/2\) gives

\[
D_{3/2}^{*}=1.134325745543364\ldots,
\qquad
2-D_{3/2}^{*}=0.865674254456636\ldots .
\]

Thus the strict proved gate is \(85.00235101\%\) at support \(1.43\), while
the limiting supported checkpoint is \(86.56742545\%\).

## Input inventory

1. The uploaded PDFs' finite Weil-form compression, zero-side block
   decomposition, and rank--trace transfer, taken as granted as requested.
2. The exact Poisson-stage identity underlying BBLR Proposition 3.1.
3. Poisson summation for the retained smooth signed shift.
4. Standard fixed-divisor progression majorants applied before collapsing the
   finite Heath--Brown factors.
5. The already completed Type-I, pole, tail, zero-mode, and normalization
   transfer from arithmetic cycles 1--4.

No RH assumption, Hardy--Littlewood conjecture, or pointwise prime-pair
asymptotic is invoked in the final construction.

## Principal proof artifacts

- `agents/arithmetic_cycle5.md`: signed-shift-first support-\(<3/2\) proof.
- `agents/certificate_cycle1.md`: exact support-\(1.43\) rational certificate.
- `agents/arithmetic_cycle4.md`: all-block transfer through support-\(5/4\),
  reused and extended by cycle 5.
- `agents/hybrid_cycle8.md`: exact phase/sawtooth cancellation, recording why
  the abandoned weighted-current branch contributes no spurious gain.
