/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.VirtualChannelMixer

open scoped BigOperators

/-!
# Exact aligned-channel scales

Use four virtual tiles at support 1.4999 and five at support 1.9999.
Each tile is strictly shorter than the frozen 0.4999 modulation period, while
the extra channel gives strict coherent-gain headroom over the ratios
14999/4999 and 19999/4999.
-/

noncomputable section

namespace RH
namespace Zeta85
namespace AlignedChannelScales

def frozenMu : ℝ := 4999 / 10000

def tileRatio4 : ℝ := (14999 / 10000) / 4

def tileRatio5 : ℝ := (19999 / 10000) / 5

theorem tileRatio4_eq : tileRatio4 = 14999 / 40000 := by
  norm_num [tileRatio4]

theorem tileRatio5_eq : tileRatio5 = 19999 / 50000 := by
  norm_num [tileRatio5]

/-- Exact four-tile support slack below the frozen period. -/
theorem frozenMu_sub_tileRatio4 :
    frozenMu - tileRatio4 = 4997 / 40000 := by
  norm_num [tileRatio4, frozenMu]

/-- Exact five-tile support slack below the frozen period. -/
theorem frozenMu_sub_tileRatio5 :
    frozenMu - tileRatio5 = 4996 / 50000 := by
  norm_num [tileRatio5, frozenMu]

theorem tileRatio4_lt_frozenMu :
    tileRatio4 < frozenMu := by
  norm_num [tileRatio4, frozenMu]

theorem tileRatio5_lt_frozenMu :
    tileRatio5 < frozenMu := by
  norm_num [tileRatio5, frozenMu]

/-- Four channels have strict coherent headroom over the lower support to
block-density ratio. -/
theorem support14999_over_mu_lt_four :
    (14999 / 10000 : ℝ) / frozenMu < 4 := by
  norm_num [frozenMu]

/-- Five channels have strict coherent headroom over the upper support to
block-density ratio. -/
theorem support19999_over_mu_lt_five :
    (19999 / 10000 : ℝ) / frozenMu < 5 := by
  norm_num [frozenMu]

/-- The exact four-channel Hadamard frame clears the lower frozen ratio. -/
theorem support14999_over_mu_lt_hadamard4_gain :
    (14999 / 10000 : ℝ) / frozenMu <
      (∑ j : Fin 4,
        VirtualChannelMixer.hadamardMixer4 j 0) ^ 2 := by
  rw [VirtualChannelMixer.hadamardMixer4_coherent_gain]
  exact support14999_over_mu_lt_four

/-- The exact rational five-channel frame clears the upper frozen ratio. -/
theorem support19999_over_mu_lt_rational5_gain :
    (19999 / 10000 : ℝ) / frozenMu <
      (∑ j : Fin 5,
        VirtualChannelMixer.rationalMixer5 j 0) ^ 2 := by
  rw [VirtualChannelMixer.rationalMixer5_firstColumn_sum]
  norm_num [frozenMu]

/-- The previous three-channel attempt cannot carry the lower support ratio. -/
theorem three_lt_support14999_over_mu :
    (3 : ℝ) < (14999 / 10000 : ℝ) / frozenMu := by
  norm_num [frozenMu]

/-- The previous four-channel attempt cannot carry the upper support ratio. -/
theorem four_lt_support19999_over_mu :
    (4 : ℝ) < (19999 / 10000 : ℝ) / frozenMu := by
  norm_num [frozenMu]

theorem tileLength4_lt_frozenPeriod {L : ℝ} (hL : 0 < L) :
    tileRatio4 * L < frozenMu * L :=
  mul_lt_mul_of_pos_right tileRatio4_lt_frozenMu hL

theorem tileLength5_lt_frozenPeriod {L : ℝ} (hL : 0 < L) :
    tileRatio5 * L < frozenMu * L :=
  mul_lt_mul_of_pos_right tileRatio5_lt_frozenMu hL

end AlignedChannelScales
end Zeta85
end RH

end
