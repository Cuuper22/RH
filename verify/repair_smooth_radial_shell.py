from pathlib import Path

PATH = Path("RH/Zeta85/Discharge/SmoothRadialShell.lean")
text = PATH.read_text()


def replace_once(old: str, new: str, label: str) -> None:
    global text
    if new in text:
        print(f"already patched: {label}")
        return
    count = text.count(old)
    if count == 1:
        text = text.replace(old, new, 1)
        print(f"patched: {label}")
    else:
        raise SystemExit(
            f"{label}: expected one old block or an existing new block, found old={count}"
        )


replace_once(
    "open MeasureTheory Filter Matrix Finset Set\n",
    "open MeasureTheory Filter Matrix Finset Set\nopen Zeta23\n",
    "open Zeta23 namespace",
)

replace_once(
'''theorem integral_supportedFullProfile
    (v : ℝ → ℝ) :
    (∫ x : ℝ, @QuarticGramFamily.supportedFullProfile v x) =
      ∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x := by
  rw [QuarticGramFamily.supportedFullProfile,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num :
      (-(1 : ℝ) / 2) ≤ 1 / 2)]
''',
'''theorem integral_supportedFullProfile
    (v : ℝ → ℝ) :
    (∫ x : ℝ, @QuarticGramFamily.supportedFullProfile v x) =
      ∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x := by
  change
    (∫ x : ℝ, (Icc (-(1 : ℝ) / 2) (1 / 2)).indicator v x) =
      ∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num :
      (-(1 : ℝ) / 2) ≤ 1 / 2)]
''',
    "unfold supported profile under the integral",
)

replace_once(
'''    · have habs : |u / L| ≤ (1 : ℝ) / 2 :=
        abs_le.mpr hmem
''',
'''    · have hmem' :
          -(1 : ℝ) / 2 ≤ u / L ∧ u / L ≤ 1 / 2 := by
        simpa only [Set.mem_Icc] using hmem
      have habs : |u / L| ≤ (1 : ℝ) / 2 :=
        abs_le.mpr hmem'
''',
    "convert Icc membership before abs_le",
)

replace_once(
'''      have hb1 :
          (shrinkingHalfPeriodBump L n hL) u ≤ 1 :=
        (shrinkingHalfPeriodBump L n hL).le_one
      nlinarith
''',
'''      have hb1 :
          (shrinkingHalfPeriodBump L n hL) u ≤ 1 :=
        (shrinkingHalfPeriodBump L n hL).le_one
      have hplus :
          0 ≤ 1 + (shrinkingHalfPeriodBump L n hL) u := by
        linarith
      have hfactor :
          0 ≤ (1 - (shrinkingHalfPeriodBump L n hL) u) *
            (1 + (shrinkingHalfPeriodBump L n hL) u) :=
        mul_nonneg (sub_nonneg.mpr hb1) hplus
      have hb_sq :
          (shrinkingHalfPeriodBump L n hL) u ^ 2 ≤ 1 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hb_sq hvnonneg
''',
    "prove bump square bounded by one",
)

replace_once(
'''    · have hscaled : (1 : ℝ) / 2 < |u / L| := by
        apply lt_of_not_ge
        intro habs
        exact hmem (abs_le.mp habs)
''',
'''    · have hscaled : (1 : ℝ) / 2 < |u / L| := by
        apply lt_of_not_ge
        intro habs
        apply hmem
        simpa only [Set.mem_Icc] using (abs_le.mp habs)
''',
    "turn absolute bound into Icc membership",
)

replace_once(
'''    have hshell :
        Continuous
          (fun u : ℝ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((shrinkingProfileShellWindow_contDiff
          v L n hL hv hposProfile).continuous.pow 2)
''',
'''    have hshell :
        Continuous
          (fun u : ℝ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ)) := by
      simpa only [Function.comp_apply, Complex.ofReal_pow] using
        Complex.continuous_ofReal.comp
          ((shrinkingProfileShellWindow_contDiff
            v L n hL hv hposProfile).continuous.pow 2)
''',
    "align complex coercion continuity",
)

replace_once(
'''    · have hscaled : |u / L| ≤ (1 : ℝ) / 2 := abs_le.mpr hmem
''',
'''    · have hmem' :
          -(1 : ℝ) / 2 ≤ u / L ∧ u / L ≤ 1 / 2 := by
        simpa only [Set.mem_Icc] using hmem
      have hscaled : |u / L| ≤ (1 : ℝ) / 2 := abs_le.mpr hmem'
''',
    "convert dominated-convergence Icc membership",
)

replace_once(
'''    · have hprofile :
          @QuarticGramFamily.supportedFullProfile v (u / L) = 0 := by
        simp [QuarticGramFamily.supportedFullProfile, hmem]
''',
'''    · have hprofile :
          @QuarticGramFamily.supportedFullProfile v (u / L) = 0 := by
        rw [QuarticGramFamily.supportedFullProfile,
          Set.indicator_of_notMem hmem]
''',
    "show supported profile vanishes outside support",
)

replace_once(
'''    have hcast :
        Tendsto
          (fun n : ℕ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ))
          Filter.atTop
          (nhds
            (@QuarticGramFamily.supportedFullProfile v (u / L) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.comp hu
''',
'''    have hcast :
        Tendsto
          (fun n : ℕ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ))
          Filter.atTop
          (nhds
            (@QuarticGramFamily.supportedFullProfile v (u / L) : ℂ)) :=
      by
        simpa only [Complex.ofReal_pow] using
          (Complex.continuous_ofReal.tendsto _).comp hu
''',
    "map pointwise convergence through ofReal",
)

replace_once(
'''  have hmassC :
      Tendsto
        (fun n : ℕ =>
          (∫ u : ℝ,
            shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ))
        Filter.atTop
        (nhds
          (∫ u : ℝ,
            @QuarticGramFamily.supportedFullProfile v (u / L) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.comp hmassR
''',
'''  have hmassC :
      Tendsto
        (fun n : ℕ =>
          (∫ u : ℝ,
            shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ))
        Filter.atTop
        (nhds
          (∫ u : ℝ,
            @QuarticGramFamily.supportedFullProfile v (u / L) : ℂ)) :=
    by
      simpa only [← Complex.ofReal_pow, Zeta23.integral_ofReal_C] using
        (Complex.continuous_ofReal.tendsto _).comp hmassR
''',
    "map mass convergence through ofReal",
)

replace_once(
'''        h.profile_smooth h.profile_pos).of_le
          (by exact le_top)).continuousLinearMap_comp
''',
'''        h.profile_smooth h.profile_pos).of_le
          (by exact_mod_cast le_top)).continuousLinearMap_comp
''',
    "cast finite differentiability order into infinity",
)

PATH.write_text(text)
