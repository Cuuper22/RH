# Research-run intake manifest

This manifest records the Phase 0 intake.  SHA-256 values and byte sizes are
for the committed files after the withdrawal banner was added to
`100/FINAL_100_RESULT.md`.  This manifest excludes itself to avoid a recursive
digest.

## Intake containers

Only three supplied objects are physical ZIP archives.  The fourth supplied
source is a Google Drive folder containing loose files; it is not described as
a ZIP here.  The terminal gate is evaluated over the union of these sources.

| source | bytes | SHA-256 | role |
|---|---:|---|---|
| `Rh.zip` | 1750438 | `241e1bc4d50f84f5e4cdb365d96a5aa5178c6ccfa3570a3d39b0110be404f33a` | Initial 85% analysis batch and the two accepted PDFs. |
| `95maybe.zip` | 33318 | `ea4e8c3b06165039dd33e165dbe677d7613ea20b6745962488ac640a60ec7a7e` | Partial 95% batch, including files 13–20. |
| supplied Drive folder, terminal-95 logical batch | — | constituent hashes below | Loose files 21–24 and `00_FINAL_95_RESULT_95p063832.md`. |
| supplied Drive folder, 100% logical batch | — | constituent hashes below | Loose 100% research fork files. |
| `DO.zip` | 81372 | `916c4d3e62f4606a6456f91b5105206ca92b78677e783ffe18d492807185cd59` | Sensitive infrastructure handoff; not copied into the repository and its credential-bearing contents are intentionally excluded from this public manifest. |

The Drive folder also contains loose copies of earlier files.  File 20 differs
between sources only by one trailing blank line; committed Markdown files are
normalized to one terminal newline.  Files
`14_hybrid95_cycle1_three_translate_increment.md` and `hybrid95_cycle1.md`
are byte-identical.  Likewise `100/hybrid100_cycle1.md` and
`100/hybrid100_cycle1_95p67290.md` are byte-identical.

## Terminal-batch gate

**PASS.**  The required terminal files are present:

- `20_arithmetic95_cycle2_depth9_md9.md`
- `21_arithmetic95_cycle3_dependency_hypergraph.md`
- `22_hybrid95_cycle2_selector_quartic_handoff.md`
- `23_arithmetic95_cycle4_divisor_switch_checkpoint.md`
- `24_TERMINAL_certificate95_cycle2_95p063832.md`
- `00_FINAL_95_RESULT_95p063832.md`

Presence is an inventory fact, not validation of the mathematical claims.

## Initial 85% batch

| file | bytes | SHA-256 | one-line role |
|---|---:|---|---|
| `00-accepted-base-zeta-transcript-explanation.pdf` | 1058230 | `271aba2d2083ffa778a53c2994f2061fad7fdda450bc296ec49c7cc41e91dd2d` | Transcript-style explanation of the accepted base paper. |
| `00-accepted-base-zeta-two-thirds.pdf` | 631785 | `6792988e6cd0e17690621ce898abd5d534f98407741bc7cb14bbe7d07c77d72f` | Accepted two-thirds paper used as base infrastructure. |
| `00_FINAL_RESULT_85_PERCENT_CROSSED.md` | 2740 | `2bc3801a0c031de01497ee3983e1398d0ad121d254762182754a4dbb8ed81964` | Source synthesis claiming the 85% checkpoint. |
| `00_run_manifest.md` | 1325 | `93f4136ad322372e83d1e17148a30b1cf814143a983210751638a80877f3fd5c` | Original 85% run contract and route manifest. |
| `01_arithmetic_cycle1.md` | 11703 | `dfd27a66dfc9a56e57ddf53055d0d079166f09406563230b168b756e58de687a` | Introduces the prime-side aggregate criterion and local-energy route. |
| `01_certificate_cycle1.md` | 6984 | `99ab7f159ae72582b4d6daee95c43e8e7a9b292f30081bd42678e1e120682d9c` | Constructs the rational 85% window and certificate arithmetic. |
| `01_hybrid_cycle1.md` | 10599 | `c6342d2a9c6d8947028786212301bfab3e1a8f5c47ba7e2728f37c61d74f5e82` | Derives the de-overlapped count LP used by the certificate. |
| `02_arithmetic_cycle2.md` | 17159 | `8c20864f73ca937c60c24d266e80d0e859e0421c1370cbe4e7da87ffd989643b` | Develops Fourier-first dispersion at the 85% scale. |
| `02_certificate_cycle2.md` | 11875 | `c9b371949bbf7ccc7d2d8307606fc10514027da695bd63a2527a9973cecdfe2a` | Reduces the certificate to the saturated prime-pair trace transfer. |
| `02_hybrid_cycle2.md` | 15031 | `c5f0f491b1490f363a394e6e7d59cd37b8792c3de62029d73cae60f2ca425bf1` | Identifies the exact-selector and weighted-Levinson bottleneck. |
| `03_arithmetic_cycle3.md` | 11605 | `5d96f58b26ec642cf1beee21df3ff65110638416a3d8a239ea3176fba77ead15` | Explores the quadratic-divisor route using a subsequently corrected BBLR factor. |
| `03_certificate_cycle3.md` | 13247 | `599b086cedd6eb266ccdd688956a78a8dfaf83974cc8af2c851b7a567411a740` | Develops signed-kernel/SDP ideas and states the unverified power-complementary construction. |
| `03_hybrid_cycle3.md` | 12185 | `d00008d64feed7e3abc057526b25b3f9756fb34c3678437bf27f4038c64a3066` | Tests a Routh-resultant certificate for xi and its derivative. |
| `04_certificate_cycle4.md` | 8500 | `236df836a29e869d01941aeff3aa25b4e630900df580bd642bfe803e901e5016` | Kills the one-sided sieve-majorant route by divergent cost. |
| `04_hybrid_cycle4.md` | 11441 | `42c1ba2dad581df41d06924d7ae7f89767f14ff80ad59a9f9a44bb852132241c` | Optimizes the linear mollifier after a Littlewood reduction. |
| `05_hybrid_cycle5.md` | 11887 | `03f645974837369fa32eef80405f5ec0d86beb085182335211c3b503c4774911` | Derives exact geometric cancellation and isolates its analytic tail. |
| `06_hybrid_cycle6.md` | 7110 | `0e4ada94a5a57580c630f024c21ba4dd51b9161cd0db0c5be819bbd72727ad75` | Completes the finite geometric moment at degree two. |
| `07_root_gain_support_1p01.md` | 3781 | `ce7b784d397dd52ab4d9674b8758a9fb7adbe67cdcb27cbffc4ecdb3a2df12b9` | Source claim for the 1.01-support R-679 numerical gain. |
| `08_arithmetic_cycle4_unconditional_79p7214.md` | 16978 | `dc337402f6ec5fdfa6bed822eea17a183795d23f4490c79b187f420e7053eedb` | Corrects the BBLR factor and claims the R-797 checkpoint. |
| `09_certificate_cycle5_adversary_constraints.md` | 9709 | `6c0b39fbb478d65a6c9384a136946a1515d0904532da451ce183dd0d2a66fc3b` | Builds an explicit adversary and warns that the coupling identity is absent. |
| `10_hybrid_cycle7_weighted_levinson_current.md` | 10679 | `18b7fb164791452d23951e265600757da67e4937158f71b15c5f802a26c5a008` | Evaluates the weighted Levinson intersection current. |
| `11_hybrid_cycle8_phase_cancellation.md` | 9055 | `9603bed88a52a0ce3cd624b54dcfce9131ce4c372b5b225bef24d95e85da9aa9` | Completes the sawtooth and indentation phase cancellations. |
| `12_arithmetic_cycle5_support_3over2_86p5674.md` | 10543 | `a9a2faf961501035c9e2a3f5cfd841001006fcfdec49ced8b9b415721d7abe12` | Sums signed shifts before Watt but leaves the fatal logarithmic budget gap. |

## 95% batches

| file | bytes | SHA-256 | one-line role |
|---|---:|---|---|
| `00_FINAL_95_RESULT_95p063832.md` | 3160 | `8e9111f7356d44c3efecbbac2a216646340d4d15f67c50cae7ec55b585aac4fb` | Terminal synthesis claiming R-9506; unconditional wording is not validated. |
| `13_root95_cycle1_second_trace_threshold.md` | 2604 | `0fa0a1cb740b58346c02ddcfe263514dfdd98344300f3f795b0cf239b1bc63bb` | Computes the two-trace ceiling below support 3/2 and support needed for 95%. |
| `14_hybrid95_cycle1_three_translate_increment.md` | 11855 | `a34e4c5e859c130a3841624b05f546da9ca27153d6a9a3c14d1b9384f22fd8c9` | Kills scalar hybrids and claims a three-translate geometry increment. |
| `15_root95_cycle2_nested_quartic_86p7170.md` | 5319 | `8d53c417eb29ff7ee57b1b381f5d4025de693aaf3a2ef08baeb4542e0e2ae700` | Claims the nested-quartic increment; first downstream dependency on the R1a alias gap. |
| `16_root95_cycle3_quartic_fixed_point_86p7233.md` | 2960 | `5c558b6147c78330fd0b2ef0078ae5846095cd4419129816326b7f85346eaeed` | Replaces iteration by a rational quartic fixed-point certificate, still R1a-dependent. |
| `17_certificate95_cycle1_quartic_86p7254_support_2p14234.md` | 11387 | `2a1ccc4e3c16535af04a69af359b8d8f02f267ab56e026bf89e49203d94569f0` | Derives pair/quartic thresholds including the claimed R-9383 value. |
| `18_arithmetic95_cycle1_support_2_93p2283.md` | 10502 | `a3e4f01fc6e02cb7d09c2955a45f6ca3479a41d22c8ea11417926d96c30a18f2` | Claims the support-below-two trace and isolates the first HB resonance. |
| `19_root95_cycle4_unconditional_93p8313.md` | 3025 | `d9c5b8c224519ed303e26d51b0f30a3b72bee799bcc16631be2247f6ab18d0c7` | Combines the claimed support-two trace and quartic fixed point for R-9383. |
| `20_arithmetic95_cycle2_depth9_md9.md` | 13175 | `d1a2bc7d6751dc012c1e2939ccddfe7ab8ba49e5e2c74fd6e40718481a0f9597` | Proves a one-shot Kloosterman method-class obstruction and leaves two-sided MD9. |
| `21_arithmetic95_cycle3_dependency_hypergraph.md` | 12372 | `476657b0011e01eacf538646398948ee3a6c7984aada2d8656eeb804e19be2bc` | Shows nominal Kloosterman gains do not tensor and identifies divisor switching. |
| `22_hybrid95_cycle2_selector_quartic_handoff.md` | 10620 | `776e0b518a31cc2d76ae76c6017198363e4bdad9efdb01c255ca558a602daf32` | Kills weighted all-k three-window methods and derives a selector-quartic sufficient identity. |
| `23_arithmetic95_cycle4_divisor_switch_checkpoint.md` | 7001 | `17a0a03a1777dcdaa1b4251e52a25051406bb5e1a4d7751ba866c596fbbd1a08` | Superseded checkpoint showing nonzero winding retains a long conductor. |
| `24_TERMINAL_certificate95_cycle2_95p063832.md` | 13126 | `37018e36b8a96b497bba9699bab5fb2179f9357da5dea054e68b4703de679af1` | Gives the claimed nonflat R-9506/R-8686 certificates, blocked by construction and arithmetic gaps. |
| `hybrid95_cycle1.md` | 11855 | `a34e4c5e859c130a3841624b05f546da9ca27153d6a9a3c14d1b9384f22fd8c9` | Byte-identical duplicate of file 14 retained for source fidelity. |

## 100% loose-file batch

| file | bytes | SHA-256 | one-line role |
|---|---:|---|---|
| `100/00_RUN_100_MANIFEST.md` | 2082 | `cefc4d76be9aa37d3a86f56ad1716ffc6854c8f40b5026a983adb039f66ce140` | Defines the density-one fork and its finish-or-kill research routes. |
| `100/FINAL_100_RESULT.md` | 5979 | `17aac5295ba8c5775c6a40ce98c8109ba060762427b3c7e853b1a1981dbdf371` | **WITHDRAWN** terminal claim; retained with its construction and endpoint defects marked. |
| `100/arithmetic100_cycle1_BP_typeIII_class_kill.md` | 10029 | `d2a6c388d833b28955b0e250240422e619aa5272e9cc97b835f66a9f331db494` | Kills one-shot BP grouping for the depth-three Type-III block. |
| `100/arithmetic100_cycle2_second_dispersion_subfamily.md` | 11304 | `cdf0ceb8e02acf55bd308cb2540707cc7beb94232d045c816adb9ad4bd1883e2` | Kills the single-Poisson/trilinear class and closes one diagonal stratum. |
| `100/arithmetic100_cycle3_full_stratification_reciprocity.md` | 12407 | `5f00fc46f931261ae4678030d17e3dfcce0654f57db7d5425f643fc7b2f27633` | Stratifies second dispersion and isolates the generic determinant survivor. |
| `100/arithmetic100_cycle4_reciprocity_parity_third_difference.md` | 11077 | `9b470a4258af352d2cb801423d26f90ef99cb1f89a155ee51e458ed050044a98` | Finds the wrong reciprocity sign and quantifies the third-difference deficit. |
| `100/arithmetic100_cycle5_bpoisson_kloosterman_survivor.md` | 9481 | `9969f09c4c3c0c86912e8ae21aac5210bfb37c5eada6640bc247f0f73c0750d0` | Evaluates the signed b-Poisson zero mode and leaves a nonzero-family deficit. |
| `100/arithmetic100_cycle6.md` | 11425 | `58ded34356635cc61b6b97de8c5a84028fab7d206ea70653d67f00285703cc0f` | Rejects direct Kuznetsov and transforms the survivor to a K3 family. |
| `100/arithmetic100_cycle7.md` | 9468 | `dadb86eb784133cc4823e5856f89980e5de2b75e2ddca68f34f8ddad2a27fb6e` | Computes K3 correlations and kills the moment-only method class. |
| `100/arithmetic100_cycle8.md` | 5138 | `820f06054537b38d4731a5c509b7add0614195b9a0f0c19ed9d5cc79f15a18d4` | Repeats the density-one claim with the same inconsistent wide-block premise. |
| `100/bangbang_opt_cycle1_profile_search.md` | 5119 | `272ba4afc1189849cfa292bcc528f90989e93c9adfb7c8c3e19266555c1d6d86` | Searches capped-symbol profiles and forecasts a quartic certificate. |
| `100/certificate100_cycle1_96p249017923.md` | 9524 | `3f91e02d94b9ccda73229425f3760cf31cdc14b3d7c5e5e281eecf1959a4530f` | Constructs a two-phase capped quartic profile and rational dual. |
| `100/certificate100_cycle2_higher_moment_class_kill.md` | 9283 | `c954df7b874f8711b7af96bbbd06455908f986d0c615cd5afb27c034a5f74941` | Shows a sixth-moment block loses and kills two sharing schemes. |
| `100/certificate100_cycle3_cubic_96p512081.md` | 7309 | `9e83fb02911ed3294a4c5ac4fe3df1d839af993c9fcff3d05b0ba16e4f24f42a` | Constructs the wide cubic block later implicated by the endpoint audit. |
| `100/certificate100_cycle4_cubic_96p518798.md` | 10294 | `f81dd5702c8b56adf4677758df729000350c88c588319c80f8ffb9634446cb6a` | Pushes the cubic block toward width 2/3 and states its pointwise cone. |
| `100/certificate100_cycle5.md` | 7268 | `10055f7bf50a6b24e32078ab85b150f8810fdccae311c3064781a50d681edbe6` | Claims density one from the same inconsistent moment/stability package. |
| `100/hybrid100_cycle1.md` | 9639 | `0cea8bcd22d3f4f8777b1e953a74bbb84c0703d4eca25af6e8955a40a9469901` | Uses a cap-following mixed fourth trace to claim a 95.67% checkpoint. |
| `100/hybrid100_cycle1_95p67290.md` | 9639 | `0cea8bcd22d3f4f8777b1e953a74bbb84c0703d4eca25af6e8955a40a9469901` | Byte-identical duplicate of `hybrid100_cycle1.md`. |
| `100/hybrid100_cycle2.md` | 17146 | `1827e1d32582dfa002fc8402d8b32474bd88f32c8911a63e3c2a2e7bc3d226af` | Derives a deletion-stable tail formula and kills scalar/random selectors. |
| `100/hybrid100_cycle3.md` | 13755 | `7478d2d6bdc408703a9e60ae691efcadc8486e4a4811f2e94ed4276123da754c` | Kills a one-block current class and evaluates a two-profile counterexample. |
| `100/hybrid100_cycle4.md` | 17816 | `870cfdd41439ec530ba9eb2d6e3d6af5fc1cf0ffe87706d2914685a671a12001` | Proves the stability algebra but supplies the inconsistent wide-block premise. |
| `100/root100_cycle1_strict_increment.md` | 3286 | `67c17b9a229067cce89d57bda7daebae0f28395e5c6bb49e2b2dd9924f859075` | Retunes the quartic dual for a tiny claimed increment above R-9506. |
| `100/root100_cycle2_95p225662869565.md` | 3935 | `38e8ef4d0f73a893a02db948c7fb67215204befa588b7960d8efbe724b78001e` | Tightens the top-hat width and quartic dual to a claimed 95.23%. |
| `100/root100_cycle3_96p250068026.md` | 3360 | `d4449e8d47c0b39c97d9ebef55538134a0e094da056b9813ac920e53213acbe3` | Reuses the capped quartic block at pair support 1.99999. |
| `100/root100_cycle4_96p250173600.md` | 3039 | `9bcdadd1a73f612f89d5f4dacdf833100f04a348cb430e429a53c8d5670305ea` | Tightens pair support to 1.999999 for a claimed 96.25%. |
| `100/root100_cycle5_cubic_96p517625.md` | 3017 | `25a3275a2b1d5a7dca5c4b9833b2e1978eac9601520edad049b5f9bc42c60c82` | Retunes the wide cubic dual without changing its analytic inputs. |
| `100/sixth_block_cycle2_method_kill.md` | 5946 | `43735ccaf02d08667063f62e1a4f8c8dfe4d0f47c903ab17a845cad47c30ff08` | Enumerates degree-six contractions and shows the block misses R-9506. |
| `100/sixth_block_search.py` | 4959 | `d72ec365d673c14e3357adf4055e5fb0a52ccd6893de62370d5292d44d2ccda0` | Deterministic quadrature/search program for the sixth-block moments. |
