/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the project LICENSE.
SPDX-License-Identifier: Apache-2.0

Exact arithmetic audit of the support-1.43 certificate in Rh/01_certificate_cycle1.md.
This file deliberately does not assert the missing analytic support-extension theorem.
It proves the polynomial/rational certificate and the conditional rank-trace assembly.
-/
import Mathlib

namespace Zeta23
namespace RH95Audit

abbrev sigma85 : ℚ := (143 : ℚ) / 100
abbrev profileCoeff85 : ℚ := (169 : ℚ) / 100
abbrev A85 : ℚ := (1031 : ℚ) / 1200
abbrev B85 : ℚ := (1809683 : ℚ) / 2400000
abbrev J85 : ℚ := (970487502160963 : ℚ) / 3017889594720000

/-- The exact pair-correlation ratio claimed by the archive. -/
abbrev c85 : ℚ := sigma85 * A85 ^ 2 / (B85 + sigma85 * J85)

/-- The simple-critical-line proportion produced by the accepted rank-trace transfer. -/
abbrev proportion85 : ℚ := 2 - 1 / c85

/-- The quadratic profile is strictly positive on its full support. -/
theorem profile85_pos {x : ℝ} (hx : |x| ≤ 1 / 2) :
    0 < 1 - (169 / 100 : ℝ) * x ^ 2 := by
  rcases abs_le.mp hx with ⟨hlo, hhi⟩
  have hp : (x + 1 / 2) * (x - 1 / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith

/-- Autocorrelation polynomial printed in equation (8) of the certificate. -/
def g85 (u : ℚ) : ℚ :=
  (1809683 : ℚ) / 2400000
    - (53361 : ℚ) / 160000 * u
    - (174239 : ℚ) / 120000 * u ^ 2
    + (169 : ℚ) / 150 * u ^ 3
    - (28561 : ℚ) / 300000 * u ^ 5

/-- A formal antiderivative of `g85`. -/
def G85 (u : ℚ) : ℚ :=
  (1809683 : ℚ) / 2400000 * u
    - (53361 : ℚ) / 320000 * u ^ 2
    - (174239 : ℚ) / 360000 * u ^ 3
    + (169 : ℚ) / 600 * u ^ 4
    - (28561 : ℚ) / 1800000 * u ^ 6

/-- A formal antiderivative of `u * g85 u`. -/
def UG85 (u : ℚ) : ℚ :=
  (1809683 : ℚ) / 4800000 * u ^ 2
    - (53361 : ℚ) / 480000 * u ^ 3
    - (174239 : ℚ) / 480000 * u ^ 4
    + (169 : ℚ) / 750 * u ^ 5
    - (28561 : ℚ) / 2100000 * u ^ 7

/-- Exact symbolic evaluation of equation (9), using the two antiderivatives above. -/
theorem J85_from_antiderivatives :
    2 * (sigma85 * (UG85 (1 / sigma85) - UG85 0)
      + (G85 1 - G85 (1 / sigma85))) = J85 := by
  norm_num [sigma85, J85, G85, UG85]

/-- Exact reduced fraction for the certificate ratio. -/
theorem c85_exact :
    c85 = (2227707598259143 : ℚ) / 2561811364469143 := by
  norm_num [c85, sigma85, A85, B85, J85]

/-- The exact ratio clears the threshold needed for an 85 percent conclusion. -/
theorem c85_gt_twenty_twenty_three : (20 : ℚ) / 23 < c85 := by
  norm_num [c85, sigma85, A85, B85, J85]

/-- Exact reduced fraction for the resulting proportion. -/
theorem proportion85_exact :
    proportion85 = (1893603832049143 : ℚ) / 2227707598259143 := by
  norm_num [proportion85, c85, sigma85, A85, B85, J85]

/-- The strict rational margin over 17/20. -/
theorem proportion85_margin_exact :
    proportion85 - (17 : ℚ) / 20
      = (1047470577429 : ℚ) / 44554151965182860 := by
  norm_num [proportion85, c85, sigma85, A85, B85, J85]

/-- The arithmetic certificate is strictly above 85 percent. -/
theorem proportion85_gt_seventeen_twentieths :
    (17 : ℚ) / 20 < proportion85 := by
  norm_num [proportion85, c85, sigma85, A85, B85, J85]

/--
Conditional assembly of the exact certificate.

This is the precise seam at which the uploaded extension needs a new analytic theorem:
`hsq` is the support-1.43 normalized second-moment estimate.  No theorem in this file
manufactures that estimate.
-/
theorem proportion85_of_rankTrace
    {N s tr sq : ℝ}
    (_hN : 0 ≤ N)
    (hRankTrace : 4 * tr - 2 * N - sq ≤ s)
    (hTrace : N ≤ tr)
    (hSq : sq ≤ (((c85 : ℚ) : ℝ))⁻¹ * N) :
    (((proportion85 : ℚ) : ℝ)) * N ≤ s := by
  have hc : (((proportion85 : ℚ) : ℝ)) = 2 - (((c85 : ℚ) : ℝ))⁻¹ := by
    norm_num [proportion85, c85, sigma85, A85, B85, J85]
  rw [hc]
  linarith

/-- The exact conditional seam implies the advertised 85 percent floor. -/
theorem eighty_five_percent_of_rankTrace
    {N s tr sq : ℝ}
    (hN : 0 ≤ N)
    (hRankTrace : 4 * tr - 2 * N - sq ≤ s)
    (hTrace : N ≤ tr)
    (hSq : sq ≤ (((c85 : ℚ) : ℝ))⁻¹ * N) :
    (17 / 20 : ℝ) * N ≤ s := by
  have hcert := proportion85_of_rankTrace hN hRankTrace hTrace hSq
  have hconst : (17 / 20 : ℝ) < ((proportion85 : ℚ) : ℝ) := by
    norm_num [proportion85, c85, sigma85, A85, B85, J85]
  nlinarith

end RH95Audit
end Zeta23
