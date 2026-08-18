/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Shiu/AllThetaUnconditional.lean — the Route 2 composition.

`AllTheta.lean` proves a short-interval bound for the fourth moment of the divisor function,
valid for every `θ > 1/4`, conditional on ONE named Landreau-type hypothesis with constants
`(A, B)`.  `Landreau.lean` proves exactly that hypothesis at `(A, B) = (4096, 28)`.  This file
discharges the hypothesis and records the resulting UNCONDITIONAL theorem:

    ∑_{x < n ≤ x+y} τ(n)^4 ≤ 4096 · 2^(2^28 + 1) · y · (1 + log x)^(2^28)

for every `θ > 1/4`, every `x ≥ allTheta_x₀ θ` and every `y` with `x^θ ≤ y ≤ x`.

The two units were developed independently and never import each other, so their statements meet
only here.  The single seam is a cast: `Landreau.lean` states its inequality in `ℕ`, while the
hypothesis of `AllTheta.lean` is phrased over `ℝ`; the divisor-filter `Finset`s are identical.

The log exponent `2^28` is enormous and nowhere near sharp — `MaxCoordinate.lean` gets the sharp
exponent by a different route, at the price of needing `y` close to `x`.  What this composition
buys is the RANGE: no wall anywhere above `θ = 1/4`, in particular across the whole classical
range `1/2 < θ < 1`, and (via `q ≤ P^{3/4−ε}` at full interval length) past the elementary `√P`
barrier that blocks purely elementary treatments of the progression form.
-/
import RH.Zeta85.Shiu.AllTheta
import RH.Zeta85.Shiu.Landreau

open scoped BigOperators ArithmeticFunction

noncomputable section

namespace RH
namespace Zeta85
namespace Shiu

/-- Lay's explicit Landreau inequality (`landreau_tau_pow_four_le`, stated over `ℕ`) transported
to the `ℝ`-valued shape that `allTheta_tau_pow_four_short_interval` takes as its hypothesis.
The constants are `(A, B) = (4096, 28) = (8^4, 4·7)`. -/
theorem allTheta_landreau_hypothesis (n : ℕ) (hn : 1 ≤ n) :
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 4
      ≤ ((4096 : ℕ) : ℝ) *
          ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ^ (4 : ℕ) ≤ (n : ℝ)),
            ((ArithmeticFunction.sigma 0 d : ℕ) : ℝ) ^ (28 : ℕ) := by
  exact_mod_cast landreau_tau_pow_four_le n hn

/-- **Route 2, unconditional.**  For every `θ > 1/4`, every `x ≥ allTheta_x₀ θ` and every
interval length `y` with `x^θ ≤ y ≤ x`,

    ∑_{x < n ≤ x+y} τ(n)^4 ≤ 4096 · 2^(2^28 + 1) · y · (1 + log x)^(2^28).

This is `allTheta_tau_pow_four_short_interval` with its Landreau hypothesis discharged by
`allTheta_landreau_hypothesis`; no hypotheses beyond `θ > 1/4` and the interval conditions
remain. -/
theorem allTheta_tau_pow_four_short_interval_unconditional
    (θ : ℝ) (hθ : 1 / 4 < θ) (x y : ℕ) (hx : allTheta_x₀ θ ≤ x)
    (hylo : (x : ℝ) ^ θ ≤ (y : ℝ)) (hyhi : y ≤ x) :
    ∑ n ∈ Finset.Ioc x (x + y), ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 4
      ≤ ((4096 : ℕ) : ℝ) * 2 ^ (2 ^ (28 : ℕ) + 1) * (y : ℝ) *
          (1 + Real.log x) ^ 2 ^ (28 : ℕ) :=
  allTheta_tau_pow_four_short_interval 4096 28 θ hθ allTheta_landreau_hypothesis x y hx hylo hyhi

/-- The classical-range specialization at `θ = 1/2`, where the threshold is `allTheta_x₀ (1/2) = 16`:
for `x ≥ 16` and `√x ≤ y ≤ x` the fourth divisor moment over `(x, x+y]` is `≤ C · y · (1+log x)^E`
with the same explicit `C, E`. -/
theorem allTheta_tau_pow_four_sqrt_interval
    (x y : ℕ) (hx : allTheta_x₀ (1 / 2) ≤ x)
    (hylo : (x : ℝ) ^ (1 / 2 : ℝ) ≤ (y : ℝ)) (hyhi : y ≤ x) :
    ∑ n ∈ Finset.Ioc x (x + y), ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 4
      ≤ ((4096 : ℕ) : ℝ) * 2 ^ (2 ^ (28 : ℕ) + 1) * (y : ℝ) *
          (1 + Real.log x) ^ 2 ^ (28 : ℕ) :=
  allTheta_tau_pow_four_short_interval_unconditional (1 / 2) (by norm_num) x y hx hylo hyhi

end Shiu
end Zeta85
end RH

end

/-!
Axiom audit: both results below must depend on the three standard axioms only.
-/
#print axioms RH.Zeta85.Shiu.allTheta_landreau_hypothesis
#print axioms RH.Zeta85.Shiu.allTheta_tau_pow_four_short_interval_unconditional
#print axioms RH.Zeta85.Shiu.allTheta_tau_pow_four_sqrt_interval
