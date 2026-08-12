/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RH.Zeta85.Discharge.VirtualChannelMixer

/-!
# Exact aligned-channel scales

The support-1.4999 family is split into three common-period channels and the
support-1.9999 family into four.  Both common periods lie strictly above the
frozen block density 0.4999 and strictly below one half.  These rational
slacks are the support gaps used by the aggregate-alias cancellation.
-/

noncomputable section

namespace RH
namespace Zeta85
namespace AlignedChannelScales

def frozenMu : ℝ := 4999 / 10000

def periodRatio3 : ℝ := (14999 / 10000) / 3

def periodRatio4 : ℝ := (19999 / 10000) / 4

theorem periodRatio3_eq : periodRatio3 = 14999 / 30000 := by
  norm_num [periodRatio3]

theorem periodRatio4_eq : periodRatio4 = 19999 / 40000 := by
  norm_num [periodRatio4]

/-- Exact three-channel support slack: 1/15000. -/
theorem periodRatio3_sub_mu :
    periodRatio3 - frozenMu = 1 / 15000 := by
  norm_num [periodRatio3, frozenMu]

/-- Exact four-channel support slack: 3/40000. -/
theorem periodRatio4_sub_mu :
    periodRatio4 - frozenMu = 3 / 40000 := by
  norm_num [periodRatio4, frozenMu]

theorem frozenMu_lt_periodRatio3 :
    frozenMu < periodRatio3 := by
  norm_num [periodRatio3, frozenMu]

theorem frozenMu_lt_periodRatio4 :
    frozenMu < periodRatio4 := by
  norm_num [periodRatio4, frozenMu]

theorem periodRatio3_lt_half :
    periodRatio3 < 1 / 2 := by
  norm_num [periodRatio3]

theorem periodRatio4_lt_half :
    periodRatio4 < 1 / 2 := by
  norm_num [periodRatio4]

/-- Scaling by a positive logarithmic length preserves the three-channel
strict support gap. -/
theorem frozenLength_lt_period3 {L : ℝ} (hL : 0 < L) :
    frozenMu * L < periodRatio3 * L :=
  mul_lt_mul_of_pos_right frozenMu_lt_periodRatio3 hL

/-- Scaling by a positive logarithmic length preserves the four-channel
strict support gap. -/
theorem frozenLength_lt_period4 {L : ℝ} (hL : 0 < L) :
    frozenMu * L < periodRatio4 * L :=
  mul_lt_mul_of_pos_right frozenMu_lt_periodRatio4 hL

end AlignedChannelScales
end Zeta85
end RH

end
