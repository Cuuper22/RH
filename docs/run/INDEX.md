# Research run-log index

This index organizes all research run logs by campaign and gives a one-line summary
of each file's content. For the full narrative of each campaign, see the NARRATIVE
documents linked below. For the hash-level inventory, see [MANIFEST.md](MANIFEST.md).

## The 85% campaign

**Narrative**: [NARRATIVE_85.md](NARRATIVE_85.md)
**Result**: Proved — 85.00% at support 143/100, limiting 86.57% as support approaches 3/2.

| File | Track | Summary | Status |
|---|---|---|---|
| [00_run_manifest.md](00_run_manifest.md) | meta | Original run contract and cycle-1 route plan | active |
| [00_FINAL_RESULT_85_PERCENT_CROSSED.md](00_FINAL_RESULT_85_PERCENT_CROSSED.md) | meta | Terminal result: 85% gate crossed at support 143/100 | active |
| [01_arithmetic_cycle1.md](01_arithmetic_cycle1.md) | arithmetic | Introduces prime-side aggregate criterion and local-energy routes | active |
| [01_certificate_cycle1.md](01_certificate_cycle1.md) | certificate | Constructs the exact rational 85% window certificate | active |
| [01_hybrid_cycle1.md](01_hybrid_cycle1.md) | hybrid | Derives the de-overlapped count LP for the certificate | active |
| [02_arithmetic_cycle2.md](02_arithmetic_cycle2.md) | arithmetic | Develops Fourier-first dispersion at the 85% scale | active |
| [02_certificate_cycle2.md](02_certificate_cycle2.md) | certificate | Reduces the certificate to the saturated prime-pair trace transfer | active |
| [02_hybrid_cycle2.md](02_hybrid_cycle2.md) | hybrid | Identifies the exact-selector and weighted-Levinson bottleneck | active |
| [03_arithmetic_cycle3.md](03_arithmetic_cycle3.md) | arithmetic | Explores quadratic-divisor route — **contains BBLR error** (corrected in cycle 4) | superseded |
| [03_certificate_cycle3.md](03_certificate_cycle3.md) | certificate | Develops signed-kernel/SDP ideas and states unverified power-complementary construction | superseded |
| [03_hybrid_cycle3.md](03_hybrid_cycle3.md) | hybrid | Tests a Routh-resultant certificate for xi and its derivative | active |
| [04_certificate_cycle4.md](04_certificate_cycle4.md) | certificate | Kills the one-sided sieve-majorant route by divergent cost | active |
| [04_hybrid_cycle4.md](04_hybrid_cycle4.md) | hybrid | Optimizes the linear mollifier after a Littlewood reduction | active |
| [05_hybrid_cycle5.md](05_hybrid_cycle5.md) | hybrid | Further mollifier optimization | active |
| [06_hybrid_cycle6.md](06_hybrid_cycle6.md) | hybrid | Additional hybrid analysis | active |
| [07_root_gain_support_1p01.md](07_root_gain_support_1p01.md) | root | Root-gain calculation at support 1.01 | active |
| [08_arithmetic_cycle4_unconditional_79p7214.md](08_arithmetic_cycle4_unconditional_79p7214.md) | arithmetic | **Corrects the BBLR error** from cycle 3; unconditional 79.72% result | active |
| [09_certificate_cycle5_adversary_constraints.md](09_certificate_cycle5_adversary_constraints.md) | certificate | Adversary constraint analysis for the certificate | active |
| [10_hybrid_cycle7_weighted_levinson_current.md](10_hybrid_cycle7_weighted_levinson_current.md) | hybrid | Weighted Levinson current analysis | active |
| [11_hybrid_cycle8_phase_cancellation.md](11_hybrid_cycle8_phase_cancellation.md) | hybrid | Exact phase/sawtooth cancellation — records why weighted-current branch contributes no gain | active |
| [12_arithmetic_cycle5_support_3over2_86p5674.md](12_arithmetic_cycle5_support_3over2_86p5674.md) | arithmetic | **Breakthrough**: signed-shift-first remainder bound enables support < 3/2, yielding 86.57% | active |

### Key supersession chain (85%)

- **BBLR error**: Cycle 3 (`03_arithmetic_cycle3.md`) has wrong exponent `(AB)^{1/2}` → Cycle 4 (`08_arithmetic_cycle4_unconditional_79p7214.md`) corrects to `AB`
- **Certificate cycle 3** (`03_certificate_cycle3.md`): Power-complementary construction was unverified; superseded by the direct route in cycle 5

---

## The 95% campaign

**Narrative**: [NARRATIVE_95.md](NARRATIVE_95.md)
**Result**: Proved — 95.064% via nonflat nested-block certificate at support near 2.

| File | Track | Summary | Status |
|---|---|---|---|
| [13_root95_cycle1_second_trace_threshold.md](13_root95_cycle1_second_trace_threshold.md) | root | Quantifies the barrier; kills the flat scalar class | active |
| [14_hybrid95_cycle1_three_translate_increment.md](14_hybrid95_cycle1_three_translate_increment.md) | hybrid | Three-translate incremental construction for the 95% extension | active |
| [15_root95_cycle2_nested_quartic_86p7170.md](15_root95_cycle2_nested_quartic_86p7170.md) | root | Nested quartic stability at 86.72% | active |
| [16_root95_cycle3_quartic_fixed_point_86p7233.md](16_root95_cycle3_quartic_fixed_point_86p7233.md) | root | Quartic fixed-point iteration at 86.72% | active |
| [17_certificate95_cycle1_quartic_86p7254_support_2p14234.md](17_certificate95_cycle1_quartic_86p7254_support_2p14234.md) | certificate | Mixed quartic certificate at support 2.14 yielding 86.73% | active |
| [18_arithmetic95_cycle1_support_2_93p2283.md](18_arithmetic95_cycle1_support_2_93p2283.md) | arithmetic | **Breakthrough**: pair trace at support < 2, yielding 93.23% | active |
| [19_root95_cycle4_unconditional_93p8313.md](19_root95_cycle4_unconditional_93p8313.md) | root | Merge with quartic stability block, yielding 93.83% | active |
| [20_arithmetic95_cycle2_depth9_md9.md](20_arithmetic95_cycle2_depth9_md9.md) | arithmetic | Depth-9 Heath-Brown expansion at support > 2 | superseded |
| [21_arithmetic95_cycle3_dependency_hypergraph.md](21_arithmetic95_cycle3_dependency_hypergraph.md) | arithmetic | Dependency hypergraph barrier for supercritical support | superseded |
| [22_hybrid95_cycle2_selector_quartic_handoff.md](22_hybrid95_cycle2_selector_quartic_handoff.md) | hybrid | Selector-quartic identity and weighted-translation boundary | superseded |
| [23_arithmetic95_cycle4_divisor_switch_checkpoint.md](23_arithmetic95_cycle4_divisor_switch_checkpoint.md) | arithmetic | Divisor-switch checkpoint for supercritical support | superseded |
| [24_TERMINAL_certificate95_cycle2_95p063832.md](24_TERMINAL_certificate95_cycle2_95p063832.md) | certificate | **Terminal**: nonflat nested-block certificate yields 95.064% | active |
| [00_FINAL_95_RESULT_95p063832.md](00_FINAL_95_RESULT_95p063832.md) | meta | Terminal result summary | active |

### Key supersession chain (95%)

- **Supercritical arithmetic** (files 20-23): Explored support > 2 strategies (depth-9 HB, hypergraph barrier, selector-quartic, divisor switch). All superseded by the terminal certificate which stays at support < 2.

---

## The withdrawn 100% campaign

**Narrative**: [NARRATIVE_100.md](NARRATIVE_100.md)
**Result**: **WITHDRAWN** — terminal claim contains a self-contradiction. See [FINAL_100_RESULT.md](100/FINAL_100_RESULT.md).

All files below are in the `100/` subdirectory.

| File | Track | Summary | Status |
|---|---|---|---|
| [100/00_RUN_100_MANIFEST.md](100/00_RUN_100_MANIFEST.md) | meta | Manifest for the 100% research fork | withdrawn |
| [100/FINAL_100_RESULT.md](100/FINAL_100_RESULT.md) | meta | **WITHDRAWN** terminal claim with detailed retraction | withdrawn |
| [100/arithmetic100_cycle1_BP_typeIII_class_kill.md](100/arithmetic100_cycle1_BP_typeIII_class_kill.md) | arithmetic | Type-III class kill via Blomer-Pascadi | withdrawn |
| [100/arithmetic100_cycle2_second_dispersion_subfamily.md](100/arithmetic100_cycle2_second_dispersion_subfamily.md) | arithmetic | Second dispersion subfamily analysis | withdrawn |
| [100/arithmetic100_cycle3_full_stratification_reciprocity.md](100/arithmetic100_cycle3_full_stratification_reciprocity.md) | arithmetic | Full stratification via reciprocity | withdrawn |
| [100/arithmetic100_cycle4_reciprocity_parity_third_difference.md](100/arithmetic100_cycle4_reciprocity_parity_third_difference.md) | arithmetic | Reciprocity parity and third difference | withdrawn |
| [100/arithmetic100_cycle5_bpoisson_kloosterman_survivor.md](100/arithmetic100_cycle5_bpoisson_kloosterman_survivor.md) | arithmetic | Poisson-Kloosterman survivor analysis | withdrawn |
| [100/arithmetic100_cycle6.md](100/arithmetic100_cycle6.md) | arithmetic | Further arithmetic exploration | withdrawn |
| [100/arithmetic100_cycle7.md](100/arithmetic100_cycle7.md) | arithmetic | Further arithmetic exploration | withdrawn |
| [100/arithmetic100_cycle8.md](100/arithmetic100_cycle8.md) | arithmetic | Final arithmetic exploration | withdrawn |
| [100/bangbang_opt_cycle1_profile_search.md](100/bangbang_opt_cycle1_profile_search.md) | optimization | Bang-bang profile search | withdrawn |
| [100/certificate100_cycle1_96p249017923.md](100/certificate100_cycle1_96p249017923.md) | certificate | Certificate at 96.25% | withdrawn |
| [100/certificate100_cycle2_higher_moment_class_kill.md](100/certificate100_cycle2_higher_moment_class_kill.md) | certificate | Higher-moment class kill | withdrawn |
| [100/certificate100_cycle3_cubic_96p512081.md](100/certificate100_cycle3_cubic_96p512081.md) | certificate | Cubic certificate at 96.51% | withdrawn |
| [100/certificate100_cycle4_cubic_96p518798.md](100/certificate100_cycle4_cubic_96p518798.md) | certificate | Refined cubic certificate at 96.52% | withdrawn |
| [100/certificate100_cycle5.md](100/certificate100_cycle5.md) | certificate | Final certificate exploration | withdrawn |
| [100/hybrid100_cycle1.md](100/hybrid100_cycle1.md) | hybrid | Hybrid construction cycle 1 | withdrawn |
| [100/hybrid100_cycle2.md](100/hybrid100_cycle2.md) | hybrid | Hybrid construction cycle 2 | withdrawn |
| [100/hybrid100_cycle3.md](100/hybrid100_cycle3.md) | hybrid | Hybrid construction cycle 3 | withdrawn |
| [100/hybrid100_cycle4.md](100/hybrid100_cycle4.md) | hybrid | Hybrid construction cycle 4 | withdrawn |
| [100/root100_cycle1_strict_increment.md](100/root100_cycle1_strict_increment.md) | root | Strict increment construction | withdrawn |
| [100/root100_cycle2_95p225662869565.md](100/root100_cycle2_95p225662869565.md) | root | Root analysis at 95.23% | withdrawn |
| [100/root100_cycle3_96p250068026.md](100/root100_cycle3_96p250068026.md) | root | Root analysis at 96.25% | withdrawn |
| [100/root100_cycle4_96p250173600.md](100/root100_cycle4_96p250173600.md) | root | Root analysis at 96.25% | withdrawn |
| [100/root100_cycle5_cubic_96p517625.md](100/root100_cycle5_cubic_96p517625.md) | root | Cubic root analysis at 96.52% | withdrawn |
| [100/sixth_block_cycle2_method_kill.md](100/sixth_block_cycle2_method_kill.md) | arithmetic | Sixth-moment block method kill | withdrawn |

**Independent disproof**: [verify/withdrawn_100_claim.py](../../verify/withdrawn_100_claim.py) and [verify/withdrawn_100_claim.out](../../verify/withdrawn_100_claim.out)

---

## Other documentation

| File | Purpose |
|---|---|
| [MANIFEST.md](MANIFEST.md) | SHA-256 hash inventory of all source files (Phase 0 intake record) |
| [NARRATIVE_85.md](NARRATIVE_85.md) | Human-readable narrative of the 85% campaign |
| [NARRATIVE_95.md](NARRATIVE_95.md) | Human-readable narrative of the 95% campaign |
| [NARRATIVE_100.md](NARRATIVE_100.md) | Human-readable narrative of the withdrawn 100% attempt |

## Accepted base papers

| File | Purpose |
|---|---|
| [00-accepted-base-zeta-two-thirds.pdf](00-accepted-base-zeta-two-thirds.pdf) | The accepted two-thirds paper |
| [00-accepted-base-zeta-transcript-explanation.pdf](00-accepted-base-zeta-transcript-explanation.pdf) | Transcript-style explanation of the paper |
