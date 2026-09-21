from pathlib import Path

PATH = Path("RH/Zeta85/Discharge/AnnularEnergyBridge.lean")
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
'''        rw [henergy u]
        push_cast
      _ = (c : ℂ) * ∫ u : ℝ, (W u : ℂ) :=
''',
'''        rw [henergy u]
        push_cast
        rfl
      _ = (c : ℂ) * ∫ u : ℝ, (W u : ℂ) :=
''',
    "close the pointwise cast identity",
)

replace_once(
'''  simpa only [shrinkingProfileShellNormalizedPairKernel] using
    normalizedPhysicalWindowEnergyPairKernel_eq_of_windowEnergy_eq_const_mul
      F T (F.channelCount T : ℝ)
        (fun u => shrinkingProfileShellWindow v L n hL u ^ 2)
        henergy hcount hmass ρ ρ'
''',
'''  have hmass' :
      (∫ u : ℝ,
        ((shrinkingProfileShellWindow v L n hL u ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    simpa only [Complex.ofReal_pow] using hmass
  simpa only [shrinkingProfileShellNormalizedPairKernel] using
    normalizedPhysicalWindowEnergyPairKernel_eq_of_windowEnergy_eq_const_mul
      F T (F.channelCount T : ℝ)
        (fun u => shrinkingProfileShellWindow v L n hL u ^ 2)
        henergy hcount hmass' ρ ρ'
''',
    "normalize the shell-square coercion",
)

PATH.write_text(text)
