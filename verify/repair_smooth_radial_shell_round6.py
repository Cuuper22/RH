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
'''      ((∫ u : ℝ,
          shrinkingProfileShellWindow v L n hL u ^ 2) : ℂ) =
          ∫ u : ℝ,
            ((shrinkingProfileShellWindow v L n hL u ^ 2 : ℝ) : ℂ) :=
        (Zeta23.integral_ofReal_C _).symm
''',
'''      ((show ℝ from
          ∫ u : ℝ,
            shrinkingProfileShellWindow v L n hL u ^ 2) : ℂ) =
          ∫ u : ℝ,
            ((shrinkingProfileShellWindow v L n hL u ^ 2 : ℝ) : ℂ) :=
        (Zeta23.integral_ofReal_C _).symm
''',
    "force the shell-square integral to be real before coercion",
)

replace_once(
'''          (show (2 : ℕ∞ω) ≤ (⊤ : ℕ∞ω) from le_top)).continuousLinearMap_comp
''',
'''          (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
            change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)).continuousLinearMap_comp
''',
    "prove order two lies below smooth infinity",
)

PATH.write_text(text)
