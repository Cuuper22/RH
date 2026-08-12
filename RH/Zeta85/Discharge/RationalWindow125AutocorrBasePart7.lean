/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Certificate

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace RH
namespace Zeta85
namespace RationalWindow125

def centeredCoeffBase125Part7 (u : ℝ) : List ℝ :=
[
    45843227478095079894576398371634947 / 625000000 + (18660979782340850366210091239972487 / 62500000) * u ^ 2 + (42779055901848861473459125316992143 / 125000000) * u ^ 4,
    0,
    -691147399345957420970744119998981 / 15625000 - (1475139858684443499084797424723867 / 15625000) * u ^ 2,
    0,
    491713286228147833028265808241289 / 39062500
  ]

end RationalWindow125
end Zeta85
end RH
