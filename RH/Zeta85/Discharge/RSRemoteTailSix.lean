import RH.Zeta85.Discharge.RSPoissonCyclicBridge

/-!
# Sixth-order remote Poisson tails

Six integrations by parts in each window factor give twelfth-power lattice
decay.  This is the decay order used to dominate the completed complex
kernel at off-critical-line zeros.
-/

open MeasureTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace RH.Zeta85.RSPoissonCyclicBridge

open Zeta23

def derivSix (f : ℝ → ℂ) : ℝ → ℂ :=
  deriv (deriv (derivFour f))

theorem paperFT_derivSix
    {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f)
    (hsupp : HasCompactSupport f) (z : ℂ) :
    paperFT (derivSix f) z = -(z ^ 6) * paperFT f z := by
  have hf2 : ContDiff ℝ 2 (derivFour f) := by
    unfold derivFour
    exact hf.deriv'.deriv'.deriv'.deriv'
  have hsupp4 : HasCompactSupport (derivFour f) := by
    unfold derivFour
    exact hsupp.deriv.deriv.deriv.deriv
  rw [derivSix, Zeta23.paperFT_deriv_deriv hf2 hsupp4,
    paperFT_derivFour (hf.of_le (by norm_num)) hsupp]
  ring

theorem norm_paperFT_mul_pow_six_le
    {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 6 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ^ 6 ≤
      Real.exp (|z.im| * Λ) * ∫ u, ‖derivSix f u‖ := by
  have hcs : HasCompactSupport f :=
    Zeta23.hasCompactSupport_of_support_subset_abs hsupp
  have hts := Zeta23.tsupport_subset_of_support_subset_abs hsupp
  have hsupp6 : ∀ u, derivSix f u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have hu5 : u ∈ tsupport (deriv (deriv (deriv (deriv (deriv f))))) :=
      support_deriv_subset (Function.mem_support.mpr hu)
    have hu4 : u ∈ tsupport (deriv (deriv (deriv (deriv f)))) :=
      tsupport_deriv_subset hu5
    have hu3 : u ∈ tsupport (deriv (deriv (deriv f))) :=
      tsupport_deriv_subset hu4
    have hu2 : u ∈ tsupport (deriv (deriv f)) :=
      tsupport_deriv_subset hu3
    have hu1 : u ∈ tsupport (deriv f) := tsupport_deriv_subset hu2
    have hu0 : u ∈ tsupport f := tsupport_deriv_subset hu1
    exact abs_le.mpr (hts hu0)
  have hf2 : ContDiff ℝ 2 (derivFour f) := by
    unfold derivFour
    exact hf.deriv'.deriv'.deriv'.deriv'
  have hint : Integrable (derivSix f) := by
    unfold derivSix
    exact (hf2.deriv'.continuous_deriv le_rfl).integrable_of_hasCompactSupport
      hcs.deriv.deriv.deriv.deriv.deriv.deriv
  have h := Zeta23.norm_paperFT_le hint hsupp6 z
  rw [paperFT_derivSix hf hcs z, norm_mul, norm_neg,
    norm_pow, mul_comm] at h
  exact h

theorem paperFT_horizontal_decay_six_uniform
    {f : ℝ → ℂ} {Λ B : ℝ}
    (hf : ContDiff ℝ 6 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) (_hB : 0 ≤ B)
    (z : ℂ) (hz : |z.im| ≤ B) (s : ℝ) :
    ‖paperFT f (z - s)‖ * (1 + (z.re - s) ^ 6) ≤
      Real.exp (B * Λ) *
        ((∫ u, ‖f u‖) + (∫ u, ‖derivSix f u‖)) := by
  have hcompact : HasCompactSupport f :=
    Zeta23.hasCompactSupport_of_support_subset_abs hsupp
  have hfi : Integrable f :=
    hf.continuous.integrable_of_hasCompactSupport hcompact
  let w : ℂ := z - s
  have h0 := Zeta23.norm_paperFT_le hfi hsupp w
  have h6 := norm_paperFT_mul_pow_six_le hf hsupp w
  have him : w.im = z.im := by simp [w]
  rw [him] at h0 h6
  have hreabs : |z.re - s| ≤ ‖w‖ := by
    have hwre : w.re = z.re - s := by simp [w]
    rw [← hwre]
    exact Complex.abs_re_le_norm w
  have hre : (z.re - s) ^ 6 ≤ ‖w‖ ^ 6 := by
    calc
      (z.re - s) ^ 6 = ((z.re - s) ^ 2) ^ 3 := by ring
      _ = (|z.re - s| ^ 2) ^ 3 := by rw [sq_abs]
      _ = |z.re - s| ^ 6 := by ring
      _ ≤ ‖w‖ ^ 6 := pow_le_pow_left₀ (abs_nonneg _) hreabs 6
  have h6re :
      ‖paperFT f w‖ * (z.re - s) ^ 6 ≤
        Real.exp (|z.im| * Λ) * ∫ u, ‖derivSix f u‖ :=
    (mul_le_mul_of_nonneg_left hre (norm_nonneg _)).trans h6
  have hexp : Real.exp (|z.im| * Λ) ≤ Real.exp (B * Λ) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz hΛ)
  have hfInt : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
  have hdInt : 0 ≤ ∫ u, ‖derivSix f u‖ :=
    integral_nonneg fun _ => norm_nonneg _
  change ‖paperFT f w‖ * (1 + (z.re - s) ^ 6) ≤ _
  calc
    ‖paperFT f w‖ * (1 + (z.re - s) ^ 6) =
        ‖paperFT f w‖ + ‖paperFT f w‖ * (z.re - s) ^ 6 := by ring
    _ ≤ Real.exp (|z.im| * Λ) * (∫ u, ‖f u‖) +
          Real.exp (|z.im| * Λ) * (∫ u, ‖derivSix f u‖) :=
      add_le_add h0 h6re
    _ ≤ Real.exp (B * Λ) * (∫ u, ‖f u‖) +
          Real.exp (B * Λ) * (∫ u, ‖derivSix f u‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hexp hfInt)
        (mul_le_mul_of_nonneg_right hexp hdInt)
    _ = Real.exp (B * Λ) *
          ((∫ u, ‖f u‖) + (∫ u, ‖derivSix f u‖)) := by ring

theorem paperFT_mul_horizontal_decay_six_uniform
    {f : ℝ → ℂ} {Λ B : ℝ}
    (hf : ContDiff ℝ 6 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B)
    (z z' : ℂ) (hz : |z.im| ≤ B) (hz' : |z'.im| ≤ B)
    (s : ℝ) :
    ‖paperFT f (z - s) * paperFT f (z' - s)‖ *
        ((1 + (z.re - s) ^ 6) * (1 + (z'.re - s) ^ 6)) ≤
      (Real.exp (B * Λ) *
        ((∫ u, ‖f u‖) + (∫ u, ‖derivSix f u‖))) ^ 2 := by
  let C : ℝ := Real.exp (B * Λ) *
    ((∫ u, ‖f u‖) + (∫ u, ‖derivSix f u‖))
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hzBound := paperFT_horizontal_decay_six_uniform
    hf hsupp hΛ hB z hz s
  have hz'Bound := paperFT_horizontal_decay_six_uniform
    hf hsupp hΛ hB z' hz' s
  rw [norm_mul]
  change
    (‖paperFT f (z - s)‖ * ‖paperFT f (z' - s)‖) *
        ((1 + (z.re - s) ^ 6) * (1 + (z'.re - s) ^ 6)) ≤ C ^ 2
  calc
    (‖paperFT f (z - s)‖ * ‖paperFT f (z' - s)‖) *
          ((1 + (z.re - s) ^ 6) * (1 + (z'.re - s) ^ 6)) =
        (‖paperFT f (z - s)‖ * (1 + (z.re - s) ^ 6)) *
          (‖paperFT f (z' - s)‖ * (1 + (z'.re - s) ^ 6)) := by ring
    _ ≤ C * C := mul_le_mul hzBound hz'Bound (by positivity) hC0
    _ = C ^ 2 := by ring

theorem summable_and_norm_tsum_le_inv_pow_twelve_grid
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {g : ℕ → E} {C D h : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hh : 0 < h)
    (hg : ∀ k : ℕ, ‖g k‖ ≤ C * ((D + k * h) ^ 12)⁻¹) :
    Summable g ∧
      ‖∑' k : ℕ, g k‖ ≤
        (C * (D ^ 8)⁻¹) *
          ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
  have hmajor : ∀ k : ℕ,
      ‖g k‖ ≤ (C * (D ^ 8)⁻¹) * ((D + k * h) ^ 4)⁻¹ := by
    intro k
    apply (hg k).trans
    have hx : D ≤ D + k * h := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [mul_nonneg hk hh.le]
    have hx0 : 0 < D + k * h := lt_of_lt_of_le hD hx
    have hinv : ((D + k * h) ^ 8)⁻¹ ≤ (D ^ 8)⁻¹ := by
      exact inv_anti₀ (pow_pos hD 8) (pow_le_pow_left₀ hD.le hx 8)
    have heq : ((D + k * h) ^ 12)⁻¹ =
        ((D + k * h) ^ 8)⁻¹ * ((D + k * h) ^ 4)⁻¹ := by
      field_simp [hx0.ne']
    rw [heq]
    calc
      C * (((D + k * h) ^ 8)⁻¹ * ((D + k * h) ^ 4)⁻¹) ≤
          C * ((D ^ 8)⁻¹ * ((D + k * h) ^ 4)⁻¹) := by gcongr
      _ = (C * (D ^ 8)⁻¹) * ((D + k * h) ^ 4)⁻¹ := by ring
  exact Zeta23.Tail.summable_and_norm_tsum_le_inv_pow_four_grid
    (mul_nonneg hC (inv_nonneg.mpr (pow_nonneg hD.le 8))) hD hh hmajor

def distinguishedWindowSobolevMassSix
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  (∫ u, ‖(F.window T (F.distinguished T) u : ℂ)‖) +
    ∫ u, ‖derivSix
      (fun x => (F.window T (F.distinguished T) x : ℂ)) u‖

def distinguishedWindowFourierMajorantTwelve
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  (Real.exp ((1 / 2 : ℝ) *
      (F.period T (F.distinguished T) / 2)) *
    distinguishedWindowSobolevMassSix F T) ^ 2

def distinguishedRemoteTailScaleTwelve
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  distinguishedWindowFourierMajorantTwelve F T *
    ((Zeta23.D0 T ^ 8)⁻¹ *
      ((Zeta23.D0 T ^ 4)⁻¹ +
        (Zeta23.D0 T ^ 3)⁻¹ /
          (3 * PoissonKernelBridge.distinguishedGridStep F T)))

theorem distinguishedLatticeTerm_le_twelveMajorant_on_ZI
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hL : 0 < F.period T (F.distinguished T))
    (hwindow : ContDiff ℝ 6
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupport : ∀ u,
      (F.window T (F.distinguished T) u : ℂ) ≠ 0 →
        |u| ≤ F.period T (F.distinguished T) / 2)
    (ρ ρ' : ↥(Zeta23.ZeroSide.ZI Z T)) (k : ℤ) :
    ‖PoissonKernelBridge.distinguishedLatticeTerm F T
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) k‖ *
        ((1 + ((gammaOf (ρ : ℂ)).re -
          (T + (k : ℝ) *
            PoissonKernelBridge.distinguishedGridStep F T)) ^ 6) *
         (1 + ((gammaOf (ρ' : ℂ)).re -
          (T + (k : ℝ) *
            PoissonKernelBridge.distinguishedGridStep F T)) ^ 6)) ≤
      distinguishedWindowFourierMajorantTwelve F T := by
  have hstrip : 0 ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ 1 :=
    Z.strip (ρ : ℂ)
      (Zeta23.ZeroSide.mem_carrier_of_mem_ZI Z T ρ.property)
  have hstrip' : 0 ≤ (ρ' : ℂ).re ∧ (ρ' : ℂ).re ≤ 1 :=
    Z.strip (ρ' : ℂ)
      (Zeta23.ZeroSide.mem_carrier_of_mem_ZI Z T ρ'.property)
  have him : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := by
    have hgamma : (gammaOf (ρ : ℂ)).im = 1 / 2 - (ρ : ℂ).re := by
      simp [gammaOf, Complex.div_I]
    rw [hgamma, abs_le]
    constructor <;> linarith
  have him' : |(gammaOf (ρ' : ℂ)).im| ≤ 1 / 2 := by
    have hgamma : (gammaOf (ρ' : ℂ)).im = 1 / 2 - (ρ' : ℂ).re := by
      simp [gammaOf, Complex.div_I]
    rw [hgamma, abs_le]
    constructor <;> linarith
  have hbound := paperFT_mul_horizontal_decay_six_uniform
    hwindow hsupport (by linarith) (by norm_num)
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) him him'
      (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)
  simpa only [PoissonKernelBridge.distinguishedLatticeTerm,
    PoissonKernelBridge.distinguishedGridStep,
    distinguishedWindowFourierMajorantTwelve,
    distinguishedWindowSobolevMassSix] using hbound

theorem norm_le_mul_inv_pow_twelve_of_weighted_decay
    {r a b x C : ℝ} (hr : 0 ≤ r) (hx : 0 < x)
    (hdecay : r * ((1 + a ^ 6) * (1 + b ^ 6)) ≤ C)
    (ha : x ≤ |a|) (hb : x ≤ |b|) :
    r ≤ C * (x ^ 12)⁻¹ := by
  have hxa : x ^ 6 ≤ a ^ 6 := by
    calc
      x ^ 6 ≤ |a| ^ 6 := pow_le_pow_left₀ hx.le ha 6
      _ = a ^ 6 := by
        calc
          |a| ^ 6 = (|a| ^ 2) ^ 3 := by ring
          _ = (a ^ 2) ^ 3 := by rw [sq_abs]
          _ = a ^ 6 := by ring
  have hxb : x ^ 6 ≤ b ^ 6 := by
    calc
      x ^ 6 ≤ |b| ^ 6 := pow_le_pow_left₀ hx.le hb 6
      _ = b ^ 6 := by
        calc
          |b| ^ 6 = (|b| ^ 2) ^ 3 := by ring
          _ = (b ^ 2) ^ 3 := by rw [sq_abs]
          _ = b ^ 6 := by ring
  have hweight : x ^ 12 ≤ (1 + a ^ 6) * (1 + b ^ 6) := by
    calc
      x ^ 12 = x ^ 6 * x ^ 6 := by ring
      _ ≤ x ^ 6 * (1 + b ^ 6) :=
        mul_le_mul_of_nonneg_left
          (hxb.trans (le_add_of_nonneg_left (by norm_num))) (pow_nonneg hx.le _)
      _ ≤ (1 + a ^ 6) * (1 + b ^ 6) :=
        mul_le_mul_of_nonneg_right
          (hxa.trans (le_add_of_nonneg_left (by norm_num))) (by positivity)
  have hrx : r * x ^ 12 ≤ C :=
    (mul_le_mul_of_nonneg_left hweight hr).trans hdecay
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hx 12)).2 hrx

theorem lowerLatticeTailFrom_bound_of_weightedDecayTwelve
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T D C : ℝ) (r : ℕ)
    (hL : 0 < F.period T (F.distinguished T))
    (hD : 0 < D) (hC0 : 0 ≤ C)
    (z z' : ℂ)
    (hdecay : ∀ k : ℤ,
      ‖PoissonKernelBridge.distinguishedLatticeTerm F T z z' k‖ *
          ((1 + (z.re -
            (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)) ^ 6) *
           (1 + (z'.re -
            (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)) ^ 6)) ≤ C)
    (hz : T - (r + 1) *
      (2 * Real.pi / F.period T (F.distinguished T)) + D ≤ z.re)
    (hz' : T - (r + 1) *
      (2 * Real.pi / F.period T (F.distinguished T)) + D ≤ z'.re) :
    Summable (fun m : ℕ =>
        PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          (-(((r + m : ℕ) : ℤ) + 1))) ∧
      ‖∑' m : ℕ,
        PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          (-(((r + m : ℕ) : ℤ) + 1))‖ ≤
        (C * (D ^ 8)⁻¹) *
          ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ /
            (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
  let h : ℝ := 2 * Real.pi / F.period T (F.distinguished T)
  have hh : 0 < h := by
    dsimp only [h]
    positivity
  have hz_h : T - (r + 1) * h + D ≤ z.re := by simpa only [h] using hz
  have hz'_h : T - (r + 1) * h + D ≤ z'.re := by simpa only [h] using hz'
  have hmajor : ∀ m : ℕ,
      ‖PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          (-(((r + m : ℕ) : ℤ) + 1))‖ ≤
        C * ((D + m * h) ^ 12)⁻¹ := by
    intro m
    have hx : 0 < D + m * h := by positivity
    have hfreq :
        T + ((-(((r + m : ℕ) : ℤ) + 1) : ℤ) : ℝ) * h =
          T - (r + 1) * h - m * h := by
      push_cast
      ring
    have ha : D + m * h ≤
        |z.re - (T + ((-(((r + m : ℕ) : ℤ) + 1) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonneg]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    have hb : D + m * h ≤
        |z'.re - (T + ((-(((r + m : ℕ) : ℤ) + 1) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonneg]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    apply norm_le_mul_inv_pow_twelve_of_weighted_decay
      (norm_nonneg _) hx _ ha hb
    simpa only [h, PoissonKernelBridge.distinguishedGridStep] using
      hdecay (-(((r + m : ℕ) : ℤ) + 1))
  obtain ⟨hsum, hnorm⟩ :=
    summable_and_norm_tsum_le_inv_pow_twelve_grid hC0 hD hh hmajor
  refine ⟨hsum, ?_⟩
  simpa only [h] using hnorm

theorem upperLatticeTail_bound_of_weightedDecayTwelve
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T D C : ℝ) (n : ℕ)
    (hL : 0 < F.period T (F.distinguished T))
    (hD : 0 < D) (hC0 : 0 ≤ C)
    (z z' : ℂ)
    (hdecay : ∀ k : ℤ,
      ‖PoissonKernelBridge.distinguishedLatticeTerm F T z z' k‖ *
          ((1 + (z.re -
            (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)) ^ 6) *
           (1 + (z'.re -
            (T + (k : ℝ) * PoissonKernelBridge.distinguishedGridStep F T)) ^ 6)) ≤ C)
    (hz : z.re + D ≤ T + n *
      (2 * Real.pi / F.period T (F.distinguished T)))
    (hz' : z'.re + D ≤ T + n *
      (2 * Real.pi / F.period T (F.distinguished T))) :
    Summable (fun m : ℕ =>
        PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          ((n + m : ℕ) : ℤ)) ∧
      ‖∑' m : ℕ,
        PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          ((n + m : ℕ) : ℤ)‖ ≤
        (C * (D ^ 8)⁻¹) *
          ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ /
            (3 * (2 * Real.pi / F.period T (F.distinguished T)))) := by
  let h : ℝ := 2 * Real.pi / F.period T (F.distinguished T)
  have hh : 0 < h := by
    dsimp only [h]
    positivity
  have hz_h : z.re + D ≤ T + n * h := by simpa only [h] using hz
  have hz'_h : z'.re + D ≤ T + n * h := by simpa only [h] using hz'
  have hmajor : ∀ m : ℕ,
      ‖PoissonKernelBridge.distinguishedLatticeTerm F T z z'
          ((n + m : ℕ) : ℤ)‖ ≤ C * ((D + m * h) ^ 12)⁻¹ := by
    intro m
    have hx : 0 < D + m * h := by positivity
    have hfreq :
        T + (((n + m : ℕ) : ℤ) : ℝ) * h = T + n * h + m * h := by
      push_cast
      ring
    have ha : D + m * h ≤
        |z.re - (T + (((n + m : ℕ) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonpos]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    have hb : D + m * h ≤
        |z'.re - (T + (((n + m : ℕ) : ℤ) : ℝ) * h)| := by
      rw [hfreq, abs_of_nonpos]
      · linarith
      · nlinarith [show 0 ≤ (m : ℝ) * h by positivity]
    apply norm_le_mul_inv_pow_twelve_of_weighted_decay
      (norm_nonneg _) hx _ ha hb
    simpa only [h, PoissonKernelBridge.distinguishedGridStep] using
      hdecay ((n + m : ℕ) : ℤ)
  obtain ⟨hsum, hnorm⟩ :=
    summable_and_norm_tsum_le_inv_pow_twelve_grid hC0 hD hh hmajor
  refine ⟨hsum, ?_⟩
  simpa only [h] using hnorm

def remoteLatticePairScaleTwelve
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ) : ℝ :=
  ‖PoissonKernelBridge.distinguishedLatticeScale F T‖ *
    (distinguishedRemoteTailScaleTwelve F T +
      distinguishedRemoteTailScaleTwelve F T)

theorem remoteLatticePairKernel_norm_le_twelve
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hT : 0 < T)
    (hL : 0 < F.period T (F.distinguished T))
    (hcount : F.channelDim T (F.distinguished T) =
      ⌊F.period T (F.distinguished T) * T / (2 * Real.pi)⌋₊)
    (hwindow : ContDiff ℝ 6
      (fun u => (F.window T (F.distinguished T) u : ℂ)))
    (hsupport : ∀ u,
      (F.window T (F.distinguished T) u : ℂ) ≠ 0 →
        |u| ≤ F.period T (F.distinguished T) / 2)
    (ρ ρ' : ↥(Zeta23.ZeroSide.ZI Z T)) :
    ‖remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ)‖ ≤
      remoteLatticePairScaleTwelve F T := by
  let n := F.channelDim T (F.distinguished T)
  let r := PoissonKernelBridge.distinguishedEndpointGuardWidth F T
  let C := distinguishedWindowFourierMajorantTwelve F T
  have hn : n = ⌊T / PoissonKernelBridge.distinguishedGridStep F T⌋₊ :=
    PoissonKernelBridge.distinguishedChannelDim_eq_floor_gridStep F T hL hcount
  have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT
  have hρ : (ρ : ℂ) ∈ Z.ZIprime T :=
    (Zeta23.ZeroSide.mem_ZI Z T).1 ρ.property
  have hρ' : (ρ' : ℂ) ∈ Z.ZIprime T :=
    (Zeta23.ZeroSide.mem_ZI Z T).1 ρ'.property
  have hdist := PoissonKernelBridge.mem_ZIprime_guarded_distances
    F T n hL hn hρ
  have hdist' := PoissonKernelBridge.mem_ZIprime_guarded_distances
    F T n hL hn hρ'
  have hdecay := distinguishedLatticeTerm_le_twelveMajorant_on_ZI
    F T hL hwindow hsupport ρ ρ'
  have hC0 : 0 ≤ C := by
    dsimp only [C, distinguishedWindowFourierMajorantTwelve]
    positivity
  have hlower := lowerLatticeTailFrom_bound_of_weightedDecayTwelve
    F T (Zeta23.D0 T) C r hL hD hC0
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) hdecay
      (by simpa only [PoissonKernelBridge.distinguishedGridStep] using hdist.1)
      (by simpa only [PoissonKernelBridge.distinguishedGridStep] using hdist'.1)
  have hupper := upperLatticeTail_bound_of_weightedDecayTwelve
    F T (Zeta23.D0 T) C (n + r) hL hD hC0
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ)) hdecay
      (by simpa only [n, r, Nat.cast_add,
        PoissonKernelBridge.distinguishedGridStep] using hdist.2)
      (by simpa only [n, r, Nat.cast_add,
        PoissonKernelBridge.distinguishedGridStep] using hdist'.2)
  have hcompact : HasCompactSupport
      (fun u => (F.window T (F.distinguished T) u : ℂ)) :=
    hasCompactSupport_of_support_subset_abs hsupport
  have hwindow2 : ContDiff ℝ 2
      (fun u => (F.window T (F.distinguished T) u : ℂ)) :=
    hwindow.of_le (by norm_num)
  have hsum : Summable (PoissonKernelBridge.distinguishedLatticeTerm F T
      (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))) :=
    (PoissonKernelBridge.hasSum_distinguishedLatticeTerm_alias_of_hasCompactSupport
      F T hL hwindow2 hcompact
        (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))).2.summable
  rw [remoteLatticePairKernel_eq_scaled_remoteTails F T ρ ρ' hsum,
    norm_mul]
  unfold remoteLatticePairScaleTwelve
  apply mul_le_mul_of_nonneg_left
  · calc
      ‖(∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
            (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))
            (-(((r + m : ℕ) : ℤ) + 1))) +
          ∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
            (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))
            ((n + r + m : ℕ) : ℤ)‖ ≤
          ‖∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
            (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))
            (-(((r + m : ℕ) : ℤ) + 1))‖ +
          ‖∑' m : ℕ, PoissonKernelBridge.distinguishedLatticeTerm F T
            (gammaOf (ρ : ℂ)) (gammaOf (ρ' : ℂ))
            ((n + r + m : ℕ) : ℤ)‖ := norm_add_le _ _
      _ ≤ distinguishedRemoteTailScaleTwelve F T +
          distinguishedRemoteTailScaleTwelve F T := by
        gcongr
        · simpa only [C, r, distinguishedRemoteTailScaleTwelve,
            PoissonKernelBridge.distinguishedGridStep, mul_assoc] using hlower.2
        · simpa only [C, n, r, distinguishedRemoteTailScaleTwelve,
            PoissonKernelBridge.distinguishedGridStep, Nat.add_assoc,
            mul_assoc] using hupper.2
  · exact norm_nonneg _

theorem remoteLatticePairScaleTwelve_nonneg
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    (F : QuarticGramFamily Z σ μ p v) (T : ℝ)
    (hT : 0 < T) (hL : 0 < F.period T (F.distinguished T)) :
    0 ≤ remoteLatticePairScaleTwelve F T := by
  unfold remoteLatticePairScaleTwelve distinguishedRemoteTailScaleTwelve
    PoissonKernelBridge.distinguishedGridStep
    distinguishedWindowFourierMajorantTwelve
  have hD : 0 < Zeta23.D0 T := Real.sqrt_pos.2 hT
  have hgrid : 0 < 2 * Real.pi / F.period T (F.distinguished T) := by positivity
  positivity

theorem eventually_remotePair_le_scale_twelve
    {Z : ZeroConfig} {σ μ p : ℝ} {v : ℝ → ℝ}
    {F : QuarticGramFamily Z σ μ p v}
    (htail : PoissonKernelBridge.DistinguishedPoissonTailControl F)
    (hguard : PoissonKernelBridge.DistinguishedGuardedPoissonKernelData F) :
    ∀ᶠ T in atTop, ∀ ρ ρ' : ↥(ZeroSide.ZI Z T),
      ‖remoteLatticePairKernel F T (ρ : ℂ) (ρ' : ℂ)‖ ≤
        remoteLatticePairScaleTwelve F T := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hguard.periods_pos,
    hguard.windows_smooth, hguard.distinguished_grid_count,
    htail.distinguished_support_half]
      with T hT hperiod hsmooth hcount hsupport
  intro ρ ρ'
  have hL := hperiod (F.distinguished T)
  have hwindow : ContDiff ℝ 6
      (fun u => (F.window T (F.distinguished T) u : ℂ)) := by
    change ContDiff ℝ 6 (Complex.ofRealCLM ∘ F.window T (F.distinguished T))
    exact (Complex.ofRealCLM.contDiff.comp
      (hsmooth (F.distinguished T))).of_le (by
        exact (WithTop.coe_le_coe).2 (show (6 : ℕ∞) ≤ ⊤ from le_top))
  have hsupp : ∀ u,
      (F.window T (F.distinguished T) u : ℂ) ≠ 0 →
        |u| ≤ F.period T (F.distinguished T) / 2 := by
    intro u hu
    apply hsupport u
    simpa only [Complex.ofReal_ne_zero] using hu
  exact remoteLatticePairKernel_norm_le_twelve
    F T hT hL hcount hwindow hsupp ρ ρ'

end RH.Zeta85.RSPoissonCyclicBridge
