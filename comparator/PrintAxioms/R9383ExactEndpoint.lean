/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.R9383ExactEndpoint

/-! Dependency audit for the exact rational endgame rejecting the frozen
R-9383 rounding in the flat three-atom certificate class. -/

#print axioms RH.Zeta85.R9383ExactEndpoint.weights_positive
#print axioms RH.Zeta85.R9383ExactEndpoint.moments_exact
#print axioms RH.Zeta85.R9383ExactEndpoint.high_atom_trim_legal
#print axioms RH.Zeta85.R9383ExactEndpoint.rational_tail_strict
#print axioms RH.Zeta85.R9383ExactEndpoint.rational_tail_strict_of_cost
#print axioms RH.Zeta85.R9383ExactEndpoint.endpoint_below_frozen_of_qLower
#print axioms RH.Zeta85.R9383ExactEndpoint.endpoint_box_separation
