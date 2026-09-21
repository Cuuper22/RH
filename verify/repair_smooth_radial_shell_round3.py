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
'''    have hshell :
        Continuous
          (fun u : ℝ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ)) := by
      simpa [Function.comp_apply] using
        Complex.continuous_ofReal.comp
          ((shrinkingProfileShellWindow_contDiff
            v L n hL hv hposProfile).continuous.pow 2)
''',
'''    have hshell :
        Continuous
          (fun u : ℝ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ)) := by
      exact
        (Complex.continuous_ofReal.comp
          (shrinkingProfileShellWindow_contDiff
            v L n hL hv hposProfile).continuous).pow 2
''',
    "prove complex-shell continuity before squaring",
)

replace_once(
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
'''    have hcast :
        Tendsto
          (fun n : ℕ =>
            (shrinkingProfileShellWindow v L n hL u ^ 2 : ℂ))
          Filter.atTop
          (nhds
            (@QuarticGramFamily.supportedFullProfile v (u / L) : ℂ)) := by
      have hcomp := (Complex.continuous_ofReal.tendsto _).comp hu
      apply hcomp.congr'
      filter_upwards [] with n
      rw [Function.comp_apply, Complex.ofReal_pow]
''',
    "identify real-square and complex-square pointwise limits",
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
            @QuarticGramFamily.supportedFullProfile v (u / L) : ℂ)) := by
    simpa [Function.comp_apply] using
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
    have hcomp := (Complex.continuous_ofReal.tendsto _).comp hmassR
    have hlimit :
        (∫ u : ℝ,
          (@QuarticGramFamily.supportedFullProfile v (u / L) : ℂ)) =
        ((∫ u : ℝ,
          @QuarticGramFamily.supportedFullProfile v (u / L)) : ℂ) :=
      Zeta23.integral_ofReal_C _
    rw [hlimit]
    apply hcomp.congr'
    filter_upwards [] with n
    rw [Function.comp_apply]
    calc
      ((∫ u : ℝ,
          shrinkingProfileShellWindow v L n hL u ^ 2) : ℂ) =
          ∫ u : ℝ,
            ((shrinkingProfileShellWindow v L n hL u ^ 2 : ℝ) : ℂ) :=
        (Zeta23.integral_ofReal_C _).symm
      _ = ∫ u : ℝ,
            (shrinkingProfileShellWindow v L n hL u : ℂ) ^ 2 := by
        congr 1
        funext u
        exact Complex.ofReal_pow _ _
''',
    "identify real and complex annular mass integrals",
)

replace_once(
'''        h.profile_smooth h.profile_pos).of_le
          (by simp)).continuousLinearMap_comp
''',
'''        h.profile_smooth h.profile_pos).of_le
          (by exact le_top)).continuousLinearMap_comp
''',
    "supply the finite-to-infinite differentiability order",
)

PATH.write_text(text)
