/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the project LICENSE.
SPDX-License-Identifier: Apache-2.0

Formal statement of the audit boundary.  The archive's new analytic work is represented
as explicit hypotheses, never as an axiom and never as an unconditional theorem.
-/
import Zeta23.Extensions.RH95.Certificate85
import Zeta23.Extensions.RH95.QuarticCertificate

namespace Zeta23
namespace RH95Audit

/-- Data needed at one height to invoke the support-1.43 certificate. -/
structure Support143TraceInput where
  N : ℝ
  simpleOnLine : ℝ
  trace : ℝ
  secondMoment : ℝ
  nonnegN : 0 ≤ N
  rankTrace : 4 * trace - 2 * N - secondMoment ≤ simpleOnLine
  traceLower : N ≤ trace
  secondMomentUpper : secondMoment ≤ (((c85 : ℚ) : ℝ))⁻¹ * N

/-- Fully formal conditional conclusion from the exact support-1.43 trace input. -/
theorem support143_input_implies_85 (h : Support143TraceInput) :
    (17 / 20 : ℝ) * h.N ≤ h.simpleOnLine :=
  eighty_five_percent_of_rankTrace h.nonnegN h.rankTrace h.traceLower h.secondMomentUpper

/--
A sequence-level wrapper.  It does not prove that the trace inputs exist; it only states
what follows if the archive's analytic estimate supplies them eventually.
-/
theorem eventually_eighty_five
    (input : ℕ → Support143TraceInput) :
    ∀ n, (17 / 20 : ℝ) * (input n).N ≤ (input n).simpleOnLine := by
  intro n
  exact support143_input_implies_85 (input n)

end RH95Audit
end Zeta23
