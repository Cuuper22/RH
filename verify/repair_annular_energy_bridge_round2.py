from pathlib import Path

PATH = Path("RH/Zeta85/Discharge/AnnularEnergyBridge.lean")
text = PATH.read_text()

old = '''  simpa only [shrinkingProfileShellNormalizedPairKernel] using
    normalizedPhysicalWindowEnergyPairKernel_eq_of_windowEnergy_eq_const_mul
      F T (F.channelCount T : ℝ)
        (fun u => shrinkingProfileShellWindow v L n hL u ^ 2)
        henergy hcount hmass' ρ ρ'
'''
new = '''  simpa only [shrinkingProfileShellNormalizedPairKernel,
    Complex.ofReal_pow] using
    normalizedPhysicalWindowEnergyPairKernel_eq_of_windowEnergy_eq_const_mul
      F T (F.channelCount T : ℝ)
        (fun u => shrinkingProfileShellWindow v L n hL u ^ 2)
        henergy hcount hmass' ρ ρ'
'''

if new in text:
    print("already patched: normalize the final annular square coercion")
elif text.count(old) == 1:
    PATH.write_text(text.replace(old, new, 1))
    print("patched: normalize the final annular square coercion")
else:
    raise SystemExit(
        "normalize the final annular square coercion: expected one old block "
        f"or an existing new block, found old={text.count(old)}"
    )
