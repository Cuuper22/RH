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
'''        ((∫ u : ℝ,
          (@QuarticGramFamily.supportedFullProfile v (u / L) : ℝ)) : ℂ) :=
''',
'''        ((show ℝ from
          ∫ u : ℝ,
            @QuarticGramFamily.supportedFullProfile v (u / L)) : ℂ) :=
''',
    "force the limiting integral itself to be real",
)

replace_once(
'''          (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)).continuousLinearMap_comp
''',
'''          (show (2 : ℕ∞ω) ≤ (⊤ : ℕ∞ω) from le_top)).continuousLinearMap_comp
''',
    "use the actual smoothness-order type",
)

PATH.write_text(text)
