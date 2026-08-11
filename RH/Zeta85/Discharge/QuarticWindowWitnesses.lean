/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RH/Zeta85/Discharge/QuarticWindowWitnesses.lean

Exact rational-polynomial saturated-window witnesses used by the source-only
R-8686 and R-9506 certificates.  The two profiles below have degrees 18 and
10, respectively (the degree-16 object associated with the first profile is
its derivative quotient).  All interval integrals are reduced to finite
rational sums by `Zeta23.XiPrime.integral_polyEval`.
-/
import RH.Zeta85.Certificate
import Zeta23.XiPrime.Certificate.Poly

open scoped BigOperators
open Set intervalIntegral MeasureTheory

noncomputable section

namespace RH
namespace Zeta85
namespace QuarticWindowWitnesses

/-! ## Finite polynomial and Bernstein infrastructure -/

/-- The Bernstein evaluation of a coefficient list at fixed degree `n`. -/
def bernsteinEval (n : ℕ) (c : List ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    c.getD k 0 * (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)

/-- A coefficientwise Bernstein lower bound is a pointwise lower bound on `[0,1]`. -/
lemma bernsteinEval_lower_bound (n : ℕ) (c : List ℝ) (m x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hc : ∀ k ∈ Finset.range (n + 1), m ≤ c.getD k 0) :
    m ≤ bernsteinEval n c x := by
  have hpart : ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k) = 1 := by
    calc
      _ = (x + (1 - x)) ^ n := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = 1 := by ring
  calc
    m = ∑ k ∈ Finset.range (n + 1),
        m * ((n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)) := by
          rw [← Finset.mul_sum, hpart, mul_one]
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        c.getD k 0 * ((n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)) := by
          apply Finset.sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_right (hc k hk)
          positivity
    _ = bernsteinEval n c x := by
          unfold bernsteinEval
          apply Finset.sum_congr rfl
          intro k hk
          ring

/-! ## The two explicit profiles -/

/-- The exact degree-18 rational profile for support `14999/10000`. -/
def v8686 (s : ℝ) : ℝ :=
  1189 / 1000 - (2611 / 1000) * s ^ 2 - (1293 / 200) * s ^ 4
    + (270061 / 1000) * s ^ 6 - (1766327 / 500) * s ^ 8
    + (12751103 / 500) * s ^ 10 - (106684243 / 1000) * s ^ 12
    + (123437043 / 500) * s ^ 14 - (26547161 / 100) * s ^ 16
    + (13324801 / 200) * s ^ 18

/-- The exact degree-10 rational profile for support `19999/10000`. -/
def v9506 (s : ℝ) : ℝ :=
  2509 / 2000 - (4689 / 1250) * s ^ 2 + (17669 / 2500) * s ^ 4
    - (238517 / 10000) * s ^ 6 + (362157 / 5000) * s ^ 8
    - (476329 / 5000) * s ^ 10

private def bern8686 : List ℝ :=
  [35776089 / 52428800,
   1817332619 / 2359296000,
   11292976807 / 13369344000,
   257588979 / 262144000,
   19068994241 / 22282240000,
   44025476597 / 31195136000,
   42048941353 / 57933824000,
   51616087867 / 40108032000,
   3423413762377 / 1911816192000,
   970392902337 / 3186360320000,
   3423413762377 / 1911816192000,
   51616087867 / 40108032000,
   42048941353 / 57933824000,
   44025476597 / 31195136000,
   19068994241 / 22282240000,
   257588979 / 262144000,
   11292976807 / 13369344000,
   1817332619 / 2359296000,
   35776089 / 52428800]

private def bern9506 : List ℝ :=
  [2947299 / 5120000,
   19916121 / 25600000,
   74317901 / 76800000,
   93070603 / 76800000,
   216076169 / 179200000,
   163640233 / 107520000,
   216076169 / 179200000,
   93070603 / 76800000,
   74317901 / 76800000,
   19916121 / 25600000,
   2947299 / 5120000]

set_option maxRecDepth 100000 in
private theorem v8686_eq_bernstein (s : ℝ) :
    v8686 s = bernsteinEval 18 bern8686 (s + 1 / 2) := by
  simp [v8686, bernsteinEval, bern8686, Finset.sum_range_succ]
  norm_num [Nat.choose]
  ring

set_option maxRecDepth 100000 in
private theorem v9506_eq_bernstein (s : ℝ) :
    v9506 s = bernsteinEval 10 bern9506 (s + 1 / 2) := by
  simp [v9506, bernsteinEval, bern9506, Finset.sum_range_succ]
  norm_num [Nat.choose]
  ring

private theorem bern8686_lower (k : ℕ) (hk : k ∈ Finset.range 19) :
    (970392902337 / 3186360320000 : ℝ) ≤ bern8686.getD k 0 := by
  simp only [Finset.mem_range] at hk
  interval_cases k <;> norm_num [bern8686]

private theorem bern9506_lower (k : ℕ) (hk : k ∈ Finset.range 11) :
    (2947299 / 5120000 : ℝ) ≤ bern9506.getD k 0 := by
  simp only [Finset.mem_range] at hk
  interval_cases k <;> norm_num [bern9506]

/-- The R-8686 rational profile is strictly positive on the full normalized window. -/
theorem v8686_pos {s : ℝ} (hs : |s| ≤ 1 / 2) : 0 < v8686 s := by
  rw [v8686_eq_bernstein]
  have hs' := abs_le.mp hs
  have hlower := bernsteinEval_lower_bound 18 bern8686
    (970392902337 / 3186360320000) (s + 1 / 2) (by linarith) (by linarith)
    bern8686_lower
  exact lt_of_lt_of_le (by norm_num) hlower

/-- The R-9506 rational profile is strictly positive on the full normalized window. -/
theorem v9506_pos {s : ℝ} (hs : |s| ≤ 1 / 2) : 0 < v9506 s := by
  rw [v9506_eq_bernstein]
  have hs' := abs_le.mp hs
  have hlower := bernsteinEval_lower_bound 10 bern9506
    (2947299 / 5120000) (s + 1 / 2) (by linarith) (by linarith)
    bern9506_lower
  exact lt_of_lt_of_le (by norm_num) hlower

/-! ## Exact one-variable integrals -/

private def coeff8686 : List ℝ :=
  [1189 / 1000, 0, -2611 / 1000, 0, -1293 / 200, 0, 270061 / 1000, 0,
   -1766327 / 500, 0, 12751103 / 500, 0, -106684243 / 1000, 0,
   123437043 / 500, 0, -26547161 / 100, 0, 13324801 / 200]

private def coeff9506 : List ℝ :=
  [2509 / 2000, 0, -4689 / 1250, 0, 17669 / 2500, 0, -238517 / 10000, 0,
   362157 / 5000, 0, -476329 / 5000]

private def squareCoeff8686 : List ℝ :=
  [1413721 / 1000000, 0, -3104479 / 500000, 0, -8556449 / 1000000, 0,
   84495661 / 125000, 0, -9769113529 / 1000000, 0, 37799938163 / 500000, 0,
   -53651497929 / 200000, 0, -546817986957 / 500000, 0,
   12856453044583 / 500000, 0, -59862701016941 / 250000, 0,
   770273154424981 / 500000, 0, -3664928522004837 / 500000, 0,
   25884819079684971 / 1000000, 0, -8335761556089457 / 125000, 0,
   30247052010031979 / 250000, 0, -2905831704670067 / 20000, 0,
   646066602475381 / 6250, 0, -353735637439961 / 10000, 0,
   177550321689601 / 40000]

private def squareCoeff9506 : List ℝ :=
  [6295081 / 4000000, 0, -11764701 / 1250000, 0, 397551373 / 12500000, 0,
   -5643393877 / 50000000, 0, 10265658661 / 25000000, 0,
   -5597898887 / 5000000, 0, 230745805609 / 100000000, 0,
   -120045629573 / 25000000, 0, 122385128371 / 12500000, 0,
   -172505881653 / 12500000, 0, 226889316241 / 25000000]

set_option maxRecDepth 100000 in
private theorem v8686_eq_polyEval :
    v8686 = Zeta23.XiPrime.polyEval coeff8686 := by
  funext s
  simp [v8686, Zeta23.XiPrime.polyEval, coeff8686, Finset.sum_range_succ]
  ring

set_option maxRecDepth 100000 in
private theorem v9506_eq_polyEval :
    v9506 = Zeta23.XiPrime.polyEval coeff9506 := by
  funext s
  simp [v9506, Zeta23.XiPrime.polyEval, coeff9506, Finset.sum_range_succ]
  ring

set_option maxRecDepth 100000 in
private theorem v8686_sq_eq_polyEval :
    (fun s => v8686 s ^ 2) = Zeta23.XiPrime.polyEval squareCoeff8686 := by
  funext s
  simp [v8686, Zeta23.XiPrime.polyEval, squareCoeff8686, Finset.sum_range_succ]
  ring

set_option maxRecDepth 100000 in
private theorem v9506_sq_eq_polyEval :
    (fun s => v9506 s ^ 2) = Zeta23.XiPrime.polyEval squareCoeff9506 := by
  funext s
  simp [v9506, Zeta23.XiPrime.polyEval, squareCoeff9506, Finset.sum_range_succ]
  ring

/-- Exact area of the R-8686 rational profile. -/
theorem integral_v8686 :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v8686 s) =
      3815170470337249 / 3814073303040000 := by
  rw [v8686_eq_polyEval, Zeta23.XiPrime.integral_polyEval]
  norm_num [Zeta23.XiPrime.polyInt, coeff8686, Finset.sum_range_succ]

/-- Exact square integral of the R-8686 rational profile. -/
theorem integral_v8686_sq :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v8686 s ^ 2) =
      691774481155307587947581018957 / 674932819789884476620800000000 := by
  rw [v8686_sq_eq_polyEval, Zeta23.XiPrime.integral_polyEval]
  norm_num [Zeta23.XiPrime.polyInt, squareCoeff8686, Finset.sum_range_succ]

/-- Exact area of the R-9506 rational profile. -/
theorem integral_v9506 :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v9506 s) =
      5913507107 / 5913600000 := by
  rw [v9506_eq_polyEval, Zeta23.XiPrime.integral_polyEval]
  norm_num [Zeta23.XiPrime.polyInt, coeff9506, Finset.sum_range_succ]

/-- Exact square integral of the R-9506 rational profile. -/
theorem integral_v9506_sq :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v9506 s ^ 2) =
      398236775005757803499 / 381407330304000000000 := by
  rw [v9506_sq_eq_polyEval, Zeta23.XiPrime.integral_polyEval]
  norm_num [Zeta23.XiPrime.polyInt, squareCoeff9506, Finset.sum_range_succ]

/-! ## Exact autocorrelations -/

private def centeredCoeff9506 (u : ℝ) : List ℝ :=
  [6295081 / 4000000 - (11764701 / 5000000) * u ^ 2
      + (397551373 / 200000000) * u ^ 4 - (5643393877 / 3200000000) * u ^ 6
      + (10265658661 / 6400000000) * u ^ 8 - (5597898887 / 5120000000) * u ^ 10
      + (230745805609 / 409600000000) * u ^ 12
      - (120045629573 / 409600000000) * u ^ 14
      + (122385128371 / 819200000000) * u ^ 16
      - (172505881653 / 3276800000000) * u ^ 18
      + (226889316241 / 26214400000000) * u ^ 20,
   0,
   -11764701 / 1250000 + (489079047 / 25000000) * u ^ 2
      - (42231738363 / 800000000) * u ^ 4 + (35027667563 / 400000000) * u ^ 6
      - (420221521479 / 6400000000) * u ^ 8
      + (860850933957 / 51200000000) * u ^ 10
      + (61587693401 / 102400000000) * u ^ 12
      - (131157692649 / 51200000000) * u ^ 14
      + (1207541171571 / 819200000000) * u ^ 16
      - (226889316241 / 655360000000) * u ^ 18,
   0,
   397551373 / 12500000 - (42231738363 / 200000000) * u ^ 2
      + (140392283247 / 200000000) * u ^ 4 - (540764547083 / 800000000) * u ^ 6
      + (184923643239 / 25600000000) * u ^ 8
      + (107102139447 / 5120000000) * u ^ 10
      + (175020514039 / 12800000000) * u ^ 12
      - (172505881653 / 10240000000) * u ^ 14
      + (2042003846169 / 327680000000) * u ^ 16,
   0,
   -5643393877 / 50000000 + (35027667563 / 25000000) * u ^ 2
      - (540764547083 / 200000000) * u ^ 4 - (1068685658381 / 1600000000) * u ^ 6
      - (477052761063 / 6400000000) * u ^ 8 - (9203335799 / 3200000000) * u ^ 10
      + (1207541171571 / 12800000000) * u ^ 12
      - (680667948723 / 10240000000) * u ^ 14,
   0,
   10265658661 / 25000000 - (420221521479 / 100000000) * u ^ 2
      + (184923643239 / 1600000000) * u ^ 4 - (477052761063 / 1600000000) * u ^ 6
      - (52204614147 / 320000000) * u ^ 8 - (1207541171571 / 6400000000) * u ^ 10
      + (4764675641061 / 10240000000) * u ^ 12,
   0,
   -5597898887 / 5000000 + (860850933957 / 200000000) * u ^ 2
      + (107102139447 / 80000000) * u ^ 4 - (9203335799 / 200000000) * u ^ 6
      - (1207541171571 / 1600000000) * u ^ 8
      - (14294026923183 / 6400000000) * u ^ 10,
   0,
   230745805609 / 100000000 + (61587693401 / 100000000) * u ^ 2
      + (175020514039 / 50000000) * u ^ 4 + (1207541171571 / 200000000) * u ^ 6
      + (4764675641061 / 640000000) * u ^ 8,
   0,
   -120045629573 / 25000000 - (131157692649 / 12500000) * u ^ 2
      - (172505881653 / 10000000) * u ^ 4 - (680667948723 / 40000000) * u ^ 6,
   0,
   122385128371 / 12500000 + (1207541171571 / 50000000) * u ^ 2
      + (2042003846169 / 80000000) * u ^ 4,
   0,
   -172505881653 / 12500000 - (226889316241 / 10000000) * u ^ 2,
   0,
   226889316241 / 25000000]

private def autocorrCoeff9506 : List ℝ :=
  [398236775005757803499 / 381407330304000000000,
   -8686571395401 / 26214400000000,
   -158765894552745967 / 69854822400000000,
   184371510093 / 204800000000,
   -110412865469376471 / 69701632000000000,
   321071269574277 / 16384000000000,
   -218896636762630759 / 3075072000000000,
   279774886495173 / 1792000000000,
   -111659843345620179 / 512512000000000,
   869908958511769 / 4608000000000,
   -402396418110029 / 4224000000000,
   331672850897 / 14437500000,
   0,
   -2081027866271 / 2002000000000,
   0,
   1601501593 / 9625000000,
   0,
   -139444139339 / 2431000000000,
   0,
   57501960551 / 3464175000000,
   0,
   -32412759463 / 13856700000000]

private def autocorr9506 (u : ℝ) : ℝ :=
  Zeta23.XiPrime.polyEval autocorrCoeff9506 u

set_option maxRecDepth 100000 in
private theorem centered_product9506 (u t : ℝ) :
    v9506 (t - u / 2) * v9506 (t + u / 2) =
      Zeta23.XiPrime.polyEval (centeredCoeff9506 u) t := by
  simp [v9506, Zeta23.XiPrime.polyEval, centeredCoeff9506, Finset.sum_range_succ]
  ring

set_option maxRecDepth 100000 in
private theorem centered_integral9506 (u : ℝ) :
    (∫ t in (-(1 - u) / 2)..((1 - u) / 2),
      v9506 (t - u / 2) * v9506 (t + u / 2)) = autocorr9506 u := by
  rw [intervalIntegral.integral_congr (fun t _ => centered_product9506 u t),
    Zeta23.XiPrime.integral_polyEval]
  simp [Zeta23.XiPrime.polyInt, centeredCoeff9506, autocorr9506,
    Zeta23.XiPrime.polyEval, autocorrCoeff9506, Finset.sum_range_succ]
  ring

/-- Exact polynomial autocorrelation identity for the R-9506 profile. -/
theorem integral_autocorr9506 (u : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u), v9506 s * v9506 (s + u)) =
      autocorr9506 u := by
  calc
    _ = ∫ t in (-(1 : ℝ) / 2 + u / 2)..(1 / 2 - u + u / 2),
        v9506 (t - u / 2) * v9506 (t + u / 2) := by
      rw [← intervalIntegral.integral_comp_add_right
        (f := fun t => v9506 (t - u / 2) * v9506 (t + u / 2)) (u / 2)]
      apply intervalIntegral.integral_congr
      intro s hs
      change v9506 s * v9506 (s + u) =
        v9506 (s + u / 2 - u / 2) * v9506 (s + u / 2 + u / 2)
      have hleft : s + u / 2 - u / 2 = s := by ring
      have hright : s + u / 2 + u / 2 = s + u := by ring
      rw [hleft, hright]
    _ = ∫ t in (-(1 - u) / 2)..((1 - u) / 2),
        v9506 (t - u / 2) * v9506 (t + u / 2) := by
      rw [show (-(1 : ℝ) / 2 + u / 2) = -(1 - u) / 2 by ring,
        show (1 / 2 - u + u / 2 : ℝ) = (1 - u) / 2 by ring]
    _ = autocorr9506 u := centered_integral9506 u

private def uAutocorrCoeff9506 : List ℝ := 0 :: autocorrCoeff9506

set_option maxRecDepth 100000 in
private theorem u_mul_autocorr9506 :
    (fun u => u * autocorr9506 u) =
      Zeta23.XiPrime.polyEval uAutocorrCoeff9506 := by
  funext u
  simp [autocorr9506, Zeta23.XiPrime.polyEval, autocorrCoeff9506,
    uAutocorrCoeff9506, Finset.sum_range_succ]
  ring

/-- Exact saturated autocorrelation term for the support-`19999/10000` profile. -/
theorem satJ_9506 : satJ (19999 / 10000) v9506 =
    12654362408818913918598078202299887130174174838134491358293857147392508151100367229026707432858920760142708528253 /
      23193321317200664038714548745801299874683032652874630502853562485113440372116044329742612601888648069120000000000 := by
  simp only [satJ]
  simp_rw [integral_autocorr9506]
  rw [u_mul_autocorr9506, Zeta23.XiPrime.integral_polyEval]
  change 2 * ((19999 / 10000) *
      Zeta23.XiPrime.polyInt uAutocorrCoeff9506 0 (1 / (19999 / 10000)) +
      (∫ u in (1 / (19999 / 10000))..1,
        Zeta23.XiPrime.polyEval autocorrCoeff9506 u)) = _
  rw [Zeta23.XiPrime.integral_polyEval]
  norm_num [Zeta23.XiPrime.polyInt, uAutocorrCoeff9506, autocorrCoeff9506,
    Finset.sum_range_succ]

/-- Exact normalized Frobenius cost of `v9506` in the repository's `satJ` model. -/
def D9506 : ℝ :=
  ((398236775005757803499 / 381407330304000000000 : ℝ) + (19999 / 10000) *
      (12654362408818913918598078202299887130174174838134491358293857147392508151100367229026707432858920760142708528253 /
        23193321317200664038714548745801299874683032652874630502853562485113440372116044329742612601888648069120000000000)) /
    ((19999 / 10000) * (5913507107 / 5913600000) ^ 2)

/-- Closed exact fraction for the support-`19999/10000` normalized cost. -/
theorem D9506_eq : D9506 =
    8989087516774182099401577279739227351968608799369099239262013003768256760796053096571117079678417054486469573405839 /
      8418911137217185639662759168702205719609122780493604383042937969747058940843782675490525565388271259278577073405839 := by
  norm_num [D9506]

/-- The exact rational cost is strictly below the certificate's directed decimal bound. -/
theorem D9506_lt : D9506 < 106772567 / 100000000 := by
  rw [D9506_eq]
  norm_num

/-- Full repository-model witness at support `19999/10000`, including strict pointwise positivity. -/
theorem windowCost_19999 : SaturatedWindowCost (19999 / 10000) D9506 := by
  refine ⟨v9506, fun s hs => v9506_pos hs, ?_, ?_⟩
  · rw [integral_v9506]
    norm_num
  · rw [integral_v9506, integral_v9506_sq, satJ_9506]
    norm_num [D9506]

set_option maxHeartbeats 1000000 in
private def centeredCoeff8686 (u : ℝ) : List ℝ :=
  [1413721 / 1000000 - (3104479 / 2000000) * u ^ 2 - (8556449 / 16000000) * u ^ 4
      + (84495661 / 8000000) * u ^ 6 - (9769113529 / 256000000) * u ^ 8
      + (37799938163 / 512000000) * u ^ 10 - (53651497929 / 819200000) * u ^ 12
      - (546817986957 / 8192000000) * u ^ 14 + (12856453044583 / 32768000000) * u ^ 16
      - (59862701016941 / 65536000000) * u ^ 18 + (770273154424981 / 524288000000) * u ^ 20
      - (3664928522004837 / 2097152000000) * u ^ 22
      + (25884819079684971 / 16777216000000) * u ^ 24
      - (8335761556089457 / 8388608000000) * u ^ 26
      + (30247052010031979 / 67108864000000) * u ^ 28
      - (2905831704670067 / 21474836480000) * u ^ 30
      + (646066602475381 / 26843545600000) * u ^ 32
      - (353735637439961 / 171798691840000) * u ^ 34
      + (177550321689601 / 2748779069440000) * u ^ 36,
   0,
   -3104479 / 500000 - (52938631 / 2000000) * u ^ 2 + (239982891 / 400000) * u ^ 4
      - (60256613251 / 16000000) * u ^ 6 + (1489642239847 / 128000000) * u ^ 8
      - (10276303656641 / 512000000) * u ^ 10
      + (41645860225233 / 2048000000) * u ^ 12
      - (14062073321591 / 1024000000) * u ^ 14
      + (189852198437923 / 16384000000) * u ^ 16
      - (1226461975633401 / 65536000000) * u ^ 18
      + (15547786170638349 / 524288000000) * u ^ 20
      - (36818280895958029 / 1048576000000) * u ^ 22
      + (61788615682386147 / 2097152000000) * u ^ 24
      - (141493615768101153 / 8388608000000) * u ^ 26
      + (166134319878584067 / 26843545600000) * u ^ 28
      - (8692291605602653 / 6710886400000) * u ^ 30
      + (1061206912319883 / 8589934592000) * u ^ 32
      - (1597952895206409 / 343597383680000) * u ^ 34,
   0,
   -8556449 / 1000000 + (239982891 / 100000) * u ^ 2
      - (57369222207 / 1600000) * u ^ 4 + (3117510646547 / 16000000) * u ^ 6
      - (25451839118727 / 51200000) * u ^ 8 + (325375391180251 / 512000000) * u ^ 10
      - (39848153463683 / 102400000) * u ^ 12 + (17004728356329 / 204800000) * u ^ 14
      + (2070500101265969 / 32768000000) * u ^ 16
      - (25121374832370767 / 131072000000) * u ^ 18
      + (171334653799828923 / 524288000000) * u ^ 20
      - (98025641407021519 / 262144000000) * u ^ 22
      + (1175563556065487209 / 4194304000000) * u ^ 24
      - (868553056123302627 / 6710886400000) * u ^ 26
      + (27250577910498759 / 838860800000) * u ^ 28
      - (4598563286719493 / 1342177280000) * u ^ 30
      + (27165199218508953 / 171798691840000) * u ^ 32,
   0,
   84495661 / 125000 - (60256613251 / 1000000) * u ^ 2
      + (3117510646547 / 4000000) * u ^ 4 - (55851876286967 / 16000000) * u ^ 6
      + (835837915269857 / 128000000) * u ^ 8
      - (312129784931713 / 64000000) * u ^ 10 + (248608408810933 / 256000000) * u ^ 12
      - (151666686932843 / 1024000000) * u ^ 14
      + (3779666716136939 / 6553600000) * u ^ 16
      - (20609870313543109 / 13107200000) * u ^ 18
      + (171240855651501769 / 65536000000) * u ^ 20
      - (706551494951665789 / 262144000000) * u ^ 22
      + (2738244266926245903 / 1677721600000) * u ^ 24
      - (212122860291900047 / 419430400000) * u ^ 26
      + (3891092011839571 / 67108864000) * u ^ 28
      - (9055066406169651 / 2684354560000) * u ^ 30,
   0,
   -9769113529 / 1000000 + (1489642239847 / 2000000) * u ^ 2
      - (25451839118727 / 3200000) * u ^ 4 + (835837915269857 / 32000000) * u ^ 6
      - (1777898392191851 / 64000000) * u ^ 8 + (565615142931233 / 128000000) * u ^ 10
      + (254310455781661 / 1024000000) * u ^ 12
      - (3235342812070209 / 4096000000) * u ^ 14
      + (53109692291340001 / 13107200000) * u ^ 16
      - (14029502170465011 / 1310720000) * u ^ 18
      + (4266860017266509379 / 262144000000) * u ^ 20
      - (5752383876928739043 / 419430400000) * u ^ 22
      + (72142933515992521 / 13107200000) * u ^ 24
      - (22285345158717543 / 33554432000) * u ^ 26
      + (27165199218508953 / 536870912000) * u ^ 28,
   0,
   37799938163 / 500000 - (10276303656641 / 2000000) * u ^ 2
      + (325375391180251 / 8000000) * u ^ 4 - (312129784931713 / 4000000) * u ^ 6
      + (565615142931233 / 32000000) * u ^ 8 + (158431639737637 / 128000000) * u ^ 10
      + (405434613596489 / 1024000000) * u ^ 12
      - (10643938532052749 / 2048000000) * u ^ 14
      + (206056980549371369 / 8192000000) * u ^ 16
      - (2034990596702589679 / 32768000000) * u ^ 18
      + (1657776785501371227 / 20971520000) * u ^ 20
      - (235120022315003553 / 5242880000) * u ^ 22
      + (225329601049255157 / 41943040000) * u ^ 24
      - (190156394529562671 / 335544320000) * u ^ 26,
   0,
   -53651497929 / 200000 + (41645860225233 / 2000000) * u ^ 2
      - (39848153463683 / 400000) * u ^ 4 + (248608408810933 / 4000000) * u ^ 6
      + (254310455781661 / 64000000) * u ^ 8 + (405434613596489 / 256000000) * u ^ 10
      + (5259724987536733 / 1024000000) * u ^ 12
      - (13800677225750821 / 512000000) * u ^ 14
      + (2413826180303279337 / 16384000000) * u ^ 16
      - (7788499627157509799 / 26214400000) * u ^ 18
      + (940431868273979081 / 3276800000) * u ^ 20
      - (32189943007036451 / 1048576000) * u ^ 22
      + (824011042961438241 / 167772160000) * u ^ 24,
   0,
   -546817986957 / 500000 - (14062073321591 / 250000) * u ^ 2
      + (17004728356329 / 200000) * u ^ 4 - (151666686932843 / 4000000) * u ^ 6
      - (3235342812070209 / 64000000) * u ^ 8
      - (10643938532052749 / 128000000) * u ^ 10
      - (13800677225750821 / 128000000) * u ^ 12
      - (176830600224315771 / 512000000) * u ^ 14
      + (3230703204421215699 / 6553600000) * u ^ 16
      - (2451745508206019311 / 1638400000) * u ^ 18
      + (151752588461743269 / 1310720000) * u ^ 20
      - (353147589840616389 / 10485760000) * u ^ 22,
   0,
   12856453044583 / 500000 + (189852198437923 / 1000000) * u ^ 2
      + (2070500101265969 / 8000000) * u ^ 4 + (3779666716136939 / 6400000) * u ^ 6
      + (53109692291340001 / 51200000) * u ^ 8
      + (206056980549371369 / 128000000) * u ^ 10
      + (2413826180303279337 / 1024000000) * u ^ 12
      + (3230703204421215699 / 1638400000) * u ^ 14
      + (1335006344579168547 / 204800000) * u ^ 16
      - (50584196153914423 / 262144000) * u ^ 18
      + (3884623488246780279 / 20971520000) * u ^ 20,
   0,
   -59862701016941 / 250000 - (1226461975633401 / 1000000) * u ^ 2
      - (25121374832370767 / 8000000) * u ^ 4
      - (20609870313543109 / 3200000) * u ^ 6
      - (14029502170465011 / 1280000) * u ^ 8
      - (2034990596702589679 / 128000000) * u ^ 10
      - (7788499627157509799 / 409600000) * u ^ 12
      - (2451745508206019311 / 102400000) * u ^ 14
      - (50584196153914423 / 65536000) * u ^ 16
      - (431624832027420031 / 524288000) * u ^ 18,
   0,
   770273154424981 / 500000 + (15547786170638349 / 2000000) * u ^ 2
      + (171334653799828923 / 8000000) * u ^ 4
      + (171240855651501769 / 4000000) * u ^ 6
      + (4266860017266509379 / 64000000) * u ^ 8
      + (1657776785501371227 / 20480000) * u ^ 10
      + (940431868273979081 / 12800000) * u ^ 12
      + (151752588461743269 / 20480000) * u ^ 14
      + (3884623488246780279 / 1310720000) * u ^ 16,
   0,
   -3664928522004837 / 500000 - (36818280895958029 / 1000000) * u ^ 2
      - (98025641407021519 / 1000000) * u ^ 4
      - (706551494951665789 / 4000000) * u ^ 6
      - (5752383876928739043 / 25600000) * u ^ 8
      - (235120022315003553 / 1280000) * u ^ 10
      - (32189943007036451 / 1024000) * u ^ 12
      - (353147589840616389 / 40960000) * u ^ 14,
   0,
   25884819079684971 / 1000000 + (61788615682386147 / 500000) * u ^ 2
      + (1175563556065487209 / 4000000) * u ^ 4
      + (2738244266926245903 / 6400000) * u ^ 6
      + (72142933515992521 / 200000) * u ^ 8
      + (225329601049255157 / 2560000) * u ^ 10
      + (824011042961438241 / 40960000) * u ^ 12,
   0,
   -8335761556089457 / 125000 - (141493615768101153 / 500000) * u ^ 2
      - (868553056123302627 / 1600000) * u ^ 4
      - (212122860291900047 / 400000) * u ^ 6
      - (22285345158717543 / 128000) * u ^ 8
      - (190156394529562671 / 5120000) * u ^ 10,
   0,
   30247052010031979 / 250000 + (166134319878584067 / 400000) * u ^ 2
      + (27250577910498759 / 50000) * u ^ 4 + (3891092011839571 / 16000) * u ^ 6
      + (27165199218508953 / 512000) * u ^ 8,
   0,
   -2905831704670067 / 20000 - (8692291605602653 / 25000) * u ^ 2
      - (4598563286719493 / 20000) * u ^ 4 - (9055066406169651 / 160000) * u ^ 6,
   0,
   646066602475381 / 6250 + (1061206912319883 / 8000) * u ^ 2
      + (27165199218508953 / 640000) * u ^ 4,
   0,
   -353735637439961 / 10000 - (1597952895206409 / 80000) * u ^ 2,
   0,
   177550321689601 / 40000]

private def autocorrCoeff8686 : List ℝ :=
  [691774481155307587947581018957 / 674932819789884476620800000000,
   -1279928544135921 / 2748779069440000,
   -4879992539075550259458341539 / 2871335819926935961600000000,
   273266797656233 / 201326592000000,
   -1651000252238632258543923329 / 76910780890900070400000000,
   44883071086578211559 / 128849018880000000,
   -6598177151380187360957893373 / 1938151678450681774080000,
   7433113004195703353 / 335544320000000,
   -18541674953489402329407887087 / 186074469897338880000000,
   4461244757919686215147 / 14092861440000000,
   -229589738899404386478537713 / 320818051547136000000,
   1504970541935947946897 / 1321205760000000,
   -1709206469722011320113138751 / 1403578975518720000000,
   92493362726088151076741 / 125954949120000000,
   155653079243797241240411 / 10633174056960000000,
   -5654083648394285461421 / 11808276480000000,
   6801318094994297380087 / 14599323648000000,
   -1590894788940825905311 / 6747586560000000,
   7262341042617177973207 / 108973522944000000,
   -48772429364756687 / 5819814000000,
   0,
   -16380424227238213 / 29099070000000,
   0,
   19288970210063297 / 27886608750000,
   0,
   -327258245288406539 / 608435100000000,
   0,
   20050909474025429 / 65189475000000,
   0,
   -12181260542269280183 / 97045398450000000,
   0,
   22385544392208577 / 651170422500000,
   0,
   -224833827166159793 / 39671305740000000,
   0,
   2659666446917 / 5799898500000,
   0,
   -25364331669943 / 1918742892000000]

private def autocorr8686 (u : ℝ) : ℝ :=
  Zeta23.XiPrime.polyEval autocorrCoeff8686 u

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem centered_product8686 (u t : ℝ) :
    v8686 (t - u / 2) * v8686 (t + u / 2) =
      Zeta23.XiPrime.polyEval (centeredCoeff8686 u) t := by
  simp [v8686, Zeta23.XiPrime.polyEval, centeredCoeff8686, Finset.sum_range_succ]
  ring

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem centered_integral8686 (u : ℝ) :
    (∫ t in (-(1 - u) / 2)..((1 - u) / 2),
      v8686 (t - u / 2) * v8686 (t + u / 2)) = autocorr8686 u := by
  rw [intervalIntegral.integral_congr (fun t _ => centered_product8686 u t),
    Zeta23.XiPrime.integral_polyEval]
  simp [Zeta23.XiPrime.polyInt, centeredCoeff8686, autocorr8686,
    Zeta23.XiPrime.polyEval, autocorrCoeff8686, Finset.sum_range_succ]
  ring

/-- Exact polynomial autocorrelation identity for the R-8686 profile. -/
theorem integral_autocorr8686 (u : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u), v8686 s * v8686 (s + u)) =
      autocorr8686 u := by
  calc
    _ = ∫ t in (-(1 : ℝ) / 2 + u / 2)..(1 / 2 - u + u / 2),
        v8686 (t - u / 2) * v8686 (t + u / 2) := by
      rw [← intervalIntegral.integral_comp_add_right
        (f := fun t => v8686 (t - u / 2) * v8686 (t + u / 2)) (u / 2)]
      apply intervalIntegral.integral_congr
      intro s hs
      change v8686 s * v8686 (s + u) =
        v8686 (s + u / 2 - u / 2) * v8686 (s + u / 2 + u / 2)
      have hleft : s + u / 2 - u / 2 = s := by ring
      have hright : s + u / 2 + u / 2 = s + u := by ring
      rw [hleft, hright]
    _ = ∫ t in (-(1 - u) / 2)..((1 - u) / 2),
        v8686 (t - u / 2) * v8686 (t + u / 2) := by
      rw [show (-(1 : ℝ) / 2 + u / 2) = -(1 - u) / 2 by ring,
        show (1 / 2 - u + u / 2 : ℝ) = (1 - u) / 2 by ring]
    _ = autocorr8686 u := centered_integral8686 u

private def uAutocorrCoeff8686 : List ℝ := 0 :: autocorrCoeff8686

set_option maxRecDepth 100000 in
private theorem u_mul_autocorr8686 :
    (fun u => u * autocorr8686 u) =
      Zeta23.XiPrime.polyEval uAutocorrCoeff8686 := by
  funext u
  simp [autocorr8686, Zeta23.XiPrime.polyEval, autocorrCoeff8686,
    uAutocorrCoeff8686, Finset.sum_range_succ]
  ring

/-- Exact saturated autocorrelation term for the support-`14999/10000` profile. -/
theorem satJ_8686 : satJ (14999 / 10000) v8686 =
    321389597218155351859513511053403031528549985414214171793319296777391789629406124641149419096717985290485444393223369490069226458031295472336874457173503091390178498440338156954942655539657211789 /
      711587542339804793185019828549339431606601345933092918444667874322951037014297530291571959968583829731913694094989788538089130677659276293749794939610531377025450731071770435031864338022400000000 := by
  simp only [satJ]
  simp_rw [integral_autocorr8686]
  rw [u_mul_autocorr8686, Zeta23.XiPrime.integral_polyEval]
  change 2 * ((14999 / 10000) *
      Zeta23.XiPrime.polyInt uAutocorrCoeff8686 0 (1 / (14999 / 10000)) +
      (∫ u in (1 / (14999 / 10000))..1,
        Zeta23.XiPrime.polyEval autocorrCoeff8686 u)) = _
  rw [Zeta23.XiPrime.integral_polyEval]
  norm_num [Zeta23.XiPrime.polyInt, uAutocorrCoeff8686, autocorrCoeff8686,
    Finset.sum_range_succ]

/-- Exact normalized Frobenius cost of `v8686` in the repository's `satJ` model. -/
def D8686 : ℝ :=
  ((691774481155307587947581018957 / 674932819789884476620800000000 : ℝ) +
      (14999 / 10000) *
        (321389597218155351859513511053403031528549985414214171793319296777391789629406124641149419096717985290485444393223369490069226458031295472336874457173503091390178498440338156954942655539657211789 /
          711587542339804793185019828549339431606601345933092918444667874322951037014297530291571959968583829731913694094989788538089130677659276293749794939610531377025450731071770435031864338022400000000)) /
    ((14999 / 10000) * (3815170470337249 / 3814073303040000) ^ 2)

/-- Closed exact fraction for the support-`14999/10000` normalized cost. -/
theorem D8686_eq : D8686 =
    18575978740728846110548832749235379157133006001351620138380201912370798933275791356361402367283424006788135483819442943259070702563126589970638100365501963179704964187537051961432044325149576041147 /
      16375930904829220985831344310017466744057923372288110116391552462936548152979474554736132991158704202327915022913346191201423946152858111347914252260647757495854597657389037833492037948087076041147 := by
  norm_num [D8686]

/-- The exact rational cost is strictly below the certificate's directed decimal bound. -/
theorem D8686_lt : D8686 < 113434643 / 100000000 := by
  rw [D8686_eq]
  norm_num

/-- Full repository-model witness at support `14999/10000`, including strict pointwise positivity. -/
theorem windowCost_14999 : SaturatedWindowCost (14999 / 10000) D8686 := by
  refine ⟨v8686, fun s hs => v8686_pos hs, ?_, ?_⟩
  · rw [integral_v8686]
    norm_num
  · rw [integral_v8686, integral_v8686_sq, satJ_8686]
    norm_num [D8686]

/-! ## Monotonicity on the allocation intervals and exact edge caps -/

/-- The normalized R-8686 allocation edge `μp/(2σ)`. -/
def edge8686 : ℝ := 444911 / 2999800

/-- The normalized R-9506 allocation edge `μp/(2σ)`. -/
def edge9506 : ℝ := 414917 / 3999800

private def derivQuot8686 (s : ℝ) : ℝ :=
  2611 / 500 + (1293 / 50) * s ^ 2 - (810183 / 500) * s ^ 4
    + (3532654 / 125) * s ^ 6 - (12751103 / 50) * s ^ 8
    + (320052729 / 250) * s ^ 10 - (864059301 / 250) * s ^ 12
    + (106188644 / 25) * s ^ 14 - (119923209 / 100) * s ^ 16

private def derivQuot9506 (s : ℝ) : ℝ :=
  4689 / 625 - (17669 / 625) * s ^ 2 + (715551 / 5000) * s ^ 4
    - (362157 / 625) * s ^ 6 + (476329 / 500) * s ^ 8

private def derivBern8686 : List ℝ :=
  [2611 / 500,
   19052637440263853 / 3599520016000000,
   6049647167136936033706643419897 / 1133697630238656022400000000000,
   13662109265676239372017613428016056533770247 /
     2550479570084880755979840224000000000000000,
   122996807817565142663684921918446451644950008456331094657 /
     22951255657299007750306616446924808960000000000000000000,
   631058466945763140770561033003441308178332757689693460288822029892447 /
     118019291615401449848811137197058073569280204800000000000000000000000,
   19789668585168912582203363048431104080115312554364218211245190896917848916251641179 /
     3717112021383061810304388793764660881111465774039068672000000000000000000000000000,
   1264447645816256095155932075944290596409334632335339496790515382751336028911827744769062879401 /
     238925341476474124813497187782178443482373524656295729479688192000000000000000000000000000000,
   22593095896929537938869940403168225612699009169471191458994288329874938306397747209896207389554449714069751 /
     4300082744871018026861326971908309776992641225944029993387294562714255360000000000000000000000000000000000]

private def derivBern9506 : List ℝ :=
  [4689 / 625,
   297024164720928259 / 39996000100000000,
   18820057312843829150929610089957 / 2559488038398720016000000000000,
   74548848902753716297270152996722562333503067 /
     10236928383974400959980800160000000000000000,
   4822355609428250240798173121846781697327296907375833561 /
     668467246806747721131154578281534720000000000000000000]

set_option maxRecDepth 100000 in
private theorem derivQuot8686_eq_bernstein (s : ℝ) :
    derivQuot8686 s = bernsteinEval 8 derivBern8686 (s ^ 2 / edge8686 ^ 2) := by
  simp [derivQuot8686, bernsteinEval, derivBern8686, edge8686, Finset.sum_range_succ]
  norm_num [Nat.choose]
  ring

set_option maxRecDepth 100000 in
private theorem derivQuot9506_eq_bernstein (s : ℝ) :
    derivQuot9506 s = bernsteinEval 4 derivBern9506 (s ^ 2 / edge9506 ^ 2) := by
  simp [derivQuot9506, bernsteinEval, derivBern9506, edge9506, Finset.sum_range_succ]
  norm_num [Nat.choose]
  ring

private theorem derivBern8686_lower (k : ℕ) (hk : k ∈ Finset.range 9) :
    (5 : ℝ) ≤ derivBern8686.getD k 0 := by
  simp only [Finset.mem_range] at hk
  interval_cases k <;> norm_num [derivBern8686]

private theorem derivBern9506_lower (k : ℕ) (hk : k ∈ Finset.range 5) :
    (7 : ℝ) ≤ derivBern9506.getD k 0 := by
  simp only [Finset.mem_range] at hk
  interval_cases k <;> norm_num [derivBern9506]

private theorem derivQuot8686_pos {s : ℝ} (hs0 : 0 ≤ s) (hse : s ≤ edge8686) :
    0 < derivQuot8686 s := by
  rw [derivQuot8686_eq_bernstein]
  have he : 0 < edge8686 := by norm_num [edge8686]
  have hs2 : s ^ 2 ≤ edge8686 ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hs0 hse
  have hlower := bernsteinEval_lower_bound 8 derivBern8686 5
    (s ^ 2 / edge8686 ^ 2) (by positivity) (by
      apply (div_le_one (by positivity)).2
      exact hs2) derivBern8686_lower
  linarith

private theorem derivQuot9506_pos {s : ℝ} (hs0 : 0 ≤ s) (hse : s ≤ edge9506) :
    0 < derivQuot9506 s := by
  rw [derivQuot9506_eq_bernstein]
  have he : 0 < edge9506 := by norm_num [edge9506]
  have hs2 : s ^ 2 ≤ edge9506 ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hs0 hse
  have hlower := bernsteinEval_lower_bound 4 derivBern9506 7
    (s ^ 2 / edge9506 ^ 2) (by positivity) (by
      apply (div_le_one (by positivity)).2
      exact hs2) derivBern9506_lower
  linarith

private theorem hasDerivAt_v8686 (s : ℝ) :
    HasDerivAt v8686 (-s * derivQuot8686 s) s := by
  have h := (((((((((hasDerivAt_const s (1189 / 1000 : ℝ)).sub
      ((hasDerivAt_pow 2 s).const_mul (2611 / 1000))).sub
      ((hasDerivAt_pow 4 s).const_mul (1293 / 200))).add
      ((hasDerivAt_pow 6 s).const_mul (270061 / 1000))).sub
      ((hasDerivAt_pow 8 s).const_mul (1766327 / 500))).add
      ((hasDerivAt_pow 10 s).const_mul (12751103 / 500))).sub
      ((hasDerivAt_pow 12 s).const_mul (106684243 / 1000))).add
      ((hasDerivAt_pow 14 s).const_mul (123437043 / 500))).sub
      ((hasDerivAt_pow 16 s).const_mul (26547161 / 100))).add
      ((hasDerivAt_pow 18 s).const_mul (13324801 / 200))
  convert h using 1 <;> try rfl
  norm_num [derivQuot8686]
  ring

private theorem hasDerivAt_v9506 (s : ℝ) :
    HasDerivAt v9506 (-s * derivQuot9506 s) s := by
  have h := (((((hasDerivAt_const s (2509 / 2000 : ℝ)).sub
      ((hasDerivAt_pow 2 s).const_mul (4689 / 1250))).add
      ((hasDerivAt_pow 4 s).const_mul (17669 / 2500))).sub
      ((hasDerivAt_pow 6 s).const_mul (238517 / 10000))).add
      ((hasDerivAt_pow 8 s).const_mul (362157 / 5000))).sub
      ((hasDerivAt_pow 10 s).const_mul (476329 / 5000))
  convert h using 1 <;> try rfl
  norm_num [derivQuot9506]
  ring

private theorem continuous_v8686 : Continuous v8686 := by
  unfold v8686
  fun_prop

private theorem differentiable_v8686 : Differentiable ℝ v8686 := by
  unfold v8686
  fun_prop

private theorem continuous_v9506 : Continuous v9506 := by
  unfold v9506
  fun_prop

private theorem differentiable_v9506 : Differentiable ℝ v9506 := by
  unfold v9506
  fun_prop

/-- The R-8686 profile is antitone on the exact normalized allocation interval. -/
theorem v8686_antitoneOn_edge : AntitoneOn v8686 (Icc 0 edge8686) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 edge8686)
  · exact continuous_v8686.continuousOn
  · exact differentiable_v8686.differentiableOn
  · intro s hs
    rw [(hasDerivAt_v8686 s).deriv]
    have hs' : s ∈ Icc 0 edge8686 := by
      have he : (0 : ℝ) < edge8686 := by norm_num [edge8686]
      have hsioo : s ∈ Ioo 0 edge8686 := by simpa [interior_Icc, he] using hs
      exact ⟨hsioo.1.le, hsioo.2.le⟩
    have hq := derivQuot8686_pos hs'.1 hs'.2
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hs'.1 hq.le)

/-- The R-9506 profile is antitone on the exact normalized allocation interval. -/
theorem v9506_antitoneOn_edge : AntitoneOn v9506 (Icc 0 edge9506) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 edge9506)
  · exact continuous_v9506.continuousOn
  · exact differentiable_v9506.differentiableOn
  · intro s hs
    rw [(hasDerivAt_v9506 s).deriv]
    have hs' : s ∈ Icc 0 edge9506 := by
      have he : (0 : ℝ) < edge9506 := by norm_num [edge9506]
      have hsioo : s ∈ Ioo 0 edge9506 := by simpa [interior_Icc, he] using hs
      exact ⟨hsioo.1.le, hsioo.2.le⟩
    have hq := derivQuot9506_pos hs'.1 hs'.2
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hs'.1 hq.le)

/-- The mean-one physical symbol associated with a normalized profile. -/
def fullSymbol (σ : ℝ) (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  v (x / σ) / (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s)

/-- Exact strict allocation cap for the R-8686 parameters `μ=4999/10000`, `p=89/100`. -/
theorem fullSymbol8686_edge_cap :
    (100 / 89 : ℝ) < fullSymbol (14999 / 10000) v8686
      ((4999 / 10000) * (89 / 100) / 2) := by
  rw [fullSymbol, integral_v8686]
  norm_num [v8686]

/-- Exact strict allocation cap for the R-9506 parameters `μ=4999/10000`, `p=83/100`. -/
theorem fullSymbol9506_edge_cap :
    (100 / 83 : ℝ) < fullSymbol (19999 / 10000) v9506
      ((4999 / 10000) * (83 / 100) / 2) := by
  rw [fullSymbol, integral_v9506]
  norm_num [v9506]

private theorem v8686_abs (s : ℝ) : v8686 |s| = v8686 s := by
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs]
  · rw [abs_of_nonpos (le_of_not_ge hs)]
    simp only [v8686]
    ring

private theorem v9506_abs (s : ℝ) : v9506 |s| = v9506 s := by
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs]
  · rw [abs_of_nonpos (le_of_not_ge hs)]
    simp only [v9506]
    ring

/-- Pointwise admissibility on the entire R-8686 allocation interval. -/
theorem fullSymbol8686_pointwise_cap {x : ℝ}
    (hx : |x| ≤ (4999 / 10000) * (89 / 100) / 2) :
    (100 / 89 : ℝ) < fullSymbol (14999 / 10000) v8686 x := by
  apply lt_of_lt_of_le fullSymbol8686_edge_cap
  unfold fullSymbol
  rw [integral_v8686]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [show ((4999 / 10000 : ℝ) * (89 / 100) / 2) / (14999 / 10000) = edge8686 by
    norm_num [edge8686]]
  let t : ℝ := |x| / (14999 / 10000)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hte : t ≤ edge8686 := by
    dsimp [t, edge8686]
    norm_num at hx ⊢
    linarith
  have htmem : t ∈ Icc 0 edge8686 := ⟨ht0, hte⟩
  have hemem : edge8686 ∈ Icc 0 edge8686 := ⟨by norm_num [edge8686], le_rfl⟩
  have hmono := v8686_antitoneOn_edge htmem hemem hte
  have ht_abs : t = |x / (14999 / 10000)| := by
    simp [t, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 14999 / 10000)]
  rw [ht_abs, v8686_abs] at hmono
  exact hmono

/-- Pointwise admissibility on the entire R-9506 allocation interval. -/
theorem fullSymbol9506_pointwise_cap {x : ℝ}
    (hx : |x| ≤ (4999 / 10000) * (83 / 100) / 2) :
    (100 / 83 : ℝ) < fullSymbol (19999 / 10000) v9506 x := by
  apply lt_of_lt_of_le fullSymbol9506_edge_cap
  unfold fullSymbol
  rw [integral_v9506]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [show ((4999 / 10000 : ℝ) * (83 / 100) / 2) / (19999 / 10000) = edge9506 by
    norm_num [edge9506]]
  let t : ℝ := |x| / (19999 / 10000)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hte : t ≤ edge9506 := by
    dsimp [t, edge9506]
    norm_num at hx ⊢
    linarith
  have htmem : t ∈ Icc 0 edge9506 := ⟨ht0, hte⟩
  have hemem : edge9506 ∈ Icc 0 edge9506 := ⟨by norm_num [edge9506], le_rfl⟩
  have hmono := v9506_antitoneOn_edge htmem hemem hte
  have ht_abs : t = |x / (19999 / 10000)| := by
    simp [t, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 19999 / 10000)]
  rw [ht_abs, v9506_abs] at hmono
  exact hmono

end QuarticWindowWitnesses
end Zeta85
end RH

end
