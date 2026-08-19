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
        return
    raise SystemExit(
        f"{label}: expected one old block or an existing new block, found old={count}"
    )


replace_once(
'''      have habs : |u / L| ≤ (1 : ℝ) / 2 :=
        abs_le.mpr hmem'
''',
'''      have habs : |u / L| ≤ (1 : ℝ) / 2 := by
        rw [abs_le]
        constructor <;> linarith [hmem'.1, hmem'.2]
''',
    "normalize the first half-period absolute bound",
)

replace_once(
'''      exact mul_le_mul_of_nonneg_left hb_sq hvnonneg
''',
'''      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hb_sq hvnonneg
''',
    "remove the harmless right factor one",
)

replace_once(
'''        simpa only [Set.mem_Icc] using (abs_le.mp habs)
''',
'''        rw [Set.mem_Icc]
        have habs' := abs_le.mp habs
        constructor
        · linarith [habs'.1]
        · exact habs'.2
''',
    "normalize the reverse half-period membership conversion",
)

replace_once(
'''    have hshell :
        Continuous
          (fun u : ℝ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ)) := by
      simpa only [Function.comp_apply, Complex.ofReal_pow] using
        Complex.continuous_ofReal.comp
          ((shrinkingProfileShellWindow_contDiff
            v L n hL hv hposProfile).continuous.pow 2)
''',
'''    have hshell :
        Continuous
          (fun u : ℝ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ)) := by
      simpa [Function.comp_apply] using
        Complex.continuous_ofReal.comp
          ((shrinkingProfileShellWindow_contDiff
            v L n hL hv hposProfile).continuous.pow 2)
''',
    "normalize complex continuity of the squared shell",
)

replace_once(
'''      have hscaled : |u / L| ≤ (1 : ℝ) / 2 := abs_le.mpr hmem'
''',
'''      have hscaled : |u / L| ≤ (1 : ℝ) / 2 := by
        rw [abs_le]
        constructor <;> linarith [hmem'.1, hmem'.2]
''',
    "normalize the dominated-convergence half-period bound",
)

replace_once(
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
'''    have hcast :
        Tendsto
          (fun n : ℕ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ))
          Filter.atTop
          (nhds
            (@QuarticGramFamily.supportedFullProfile v (u / L) : ℂ)) := by
      simpa [Function.comp_apply] using
        (Complex.continuous_ofReal.tendsto _).comp hu
''',
    "normalize pointwise complex convergence",
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
    by
      simpa only [← Complex.ofReal_pow, Zeta23.integral_ofReal_C] using
        (Complex.continuous_ofReal.tendsto _).comp hmassR
''',
'''  have hmassC :
      Tendsto
        (fun n : ℕ =>
          (∫ u : ℝ,
            shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ))
        Filter.atTop
        (nhds
          (∫ u : ℝ,
            @QuarticGramFamily.supportedFullProfile v (u / L) : ℂ)) := by
    simpa [Function.comp_apply] using
      (Complex.continuous_ofReal.tendsto _).comp hmassR
''',
    "normalize complex mass convergence",
)

replace_once(
'''        h.profile_smooth h.profile_pos).of_le
          (by exact_mod_cast le_top)).continuousLinearMap_comp
''',
'''        h.profile_smooth h.profile_pos).of_le
          (by simp)).continuousLinearMap_comp
''',
    "close the finite-to-infinite differentiability order",
)

replace_once(
'''theorem AnnularFamilyRealization.toRadialShellData
''',
'''def AnnularFamilyRealization.toRadialShellData
''',
    "make radial-shell data a definition",
)

replace_once(
'''theorem AnnularFamilyRealization.toCollectiveWindowRegularity
''',
'''def AnnularFamilyRealization.toCollectiveWindowRegularity
''',
    "make collective regularity a definition",
)

PATH.write_text(text)
