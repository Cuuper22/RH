/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RH.Zeta85.Discharge.RationalWindow125L2
import RH.Zeta85.Discharge.RationalWindow125Positivity
import RH.Zeta85.Discharge.RationalWindow125AutocorrBaseIntegral
import RH.Zeta85.Discharge.RationalWindow125AutocorrCross

open scoped BigOperators
open Set intervalIntegral MeasureTheory

noncomputable section

namespace RH
namespace Zeta85
namespace RationalWindow125

def satFunctional (σ : ℝ) (g : ℝ → ℝ) : ℝ :=
  2 * (σ * (∫ u in (0 : ℝ)..(1 / σ), u * g u) +
    ∫ u in (1 / σ)..(1 : ℝ), g u)

theorem continuous_polyEval (c : List ℝ) :
    Continuous (polyEval125 c) := by
  unfold polyEval125
  apply continuous_finset_sum
  intro k hk
  exact continuous_const.mul (continuous_id.pow k)

theorem satFunctional_linear3 (σ a b c : ℝ) (f g h : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    satFunctional σ (fun u => a * f u + b * g u + c * h u) =
      a * satFunctional σ f + b * satFunctional σ g + c * satFunctional σ h := by
  have hw : (fun u : ℝ => u * (a * f u + b * g u + c * h u)) =
      (fun u => a * (u * f u) + b * (u * g u) + c * (u * h u)) := by
    funext u
    ring
  have huf : Continuous (fun u : ℝ => u * f u) := continuous_id.mul hf
  have hug : Continuous (fun u : ℝ => u * g u) := continuous_id.mul hg
  have huh : Continuous (fun u : ℝ => u * h u) := continuous_id.mul hh
  have hweighted :
      (∫ u in (0 : ℝ)..(1 / σ),
        a * (u * f u) + b * (u * g u) + c * (u * h u)) =
        a * (∫ u in (0 : ℝ)..(1 / σ), u * f u) +
        b * (∫ u in (0 : ℝ)..(1 / σ), u * g u) +
        c * (∫ u in (0 : ℝ)..(1 / σ), u * h u) := by
    rw [intervalIntegral.integral_add
        (((huf.const_mul _).intervalIntegrable _ _).add
          ((hug.const_mul _).intervalIntegrable _ _))
        ((huh.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_add
        ((huf.const_mul _).intervalIntegrable _ _)
        ((hug.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hplain :
      (∫ u in (1 / σ)..(1 : ℝ), a * f u + b * g u + c * h u) =
        a * (∫ u in (1 / σ)..(1 : ℝ), f u) +
        b * (∫ u in (1 / σ)..(1 : ℝ), g u) +
        c * (∫ u in (1 / σ)..(1 : ℝ), h u) := by
    rw [intervalIntegral.integral_add
        (((hf.const_mul _).intervalIntegrable _ _).add
          ((hg.const_mul _).intervalIntegrable _ _))
        ((hh.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_add
        ((hf.const_mul _).intervalIntegrable _ _)
        ((hg.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  unfold satFunctional
  rw [hw, hweighted, hplain]
  ring

def uAutocorrCoeffBase125 : List ℝ := 0 :: autocorrCoeffBase125

set_option maxRecDepth 100000 in
theorem u_mul_autocorrBase125 :
    (fun u => u * autocorrBase125 u) =
      polyEval125 uAutocorrCoeffBase125 := by
  funext u
  simp [autocorrBase125, polyEval125, autocorrCoeffBase125,
    uAutocorrCoeffBase125, Finset.sum_range_succ]
  ring

def jBase : ℝ := 222796240117525756503359544189200400384114967965153037665112254748875436613738773324769317464897750596612891724342405518147649928752517613464204776191103804565916124960281057512050476350803735677617988708823631396954221037984244349575398413551148080232791927578630871394759764974505666355156650484812565790438683265695302567567709108862577216957005505464597235426940304136537542034100849501643137560373322402371004551850687456696226301191144711931814333738650721946774292266435216211857757450040484468114384829837329070904712119135393683781516822961787017608316133652203102776395162320058647284149516742778426607615453014344874978841751205061770394216046546847054868682531552264441400266150920709085661386600059203705682784173053435750424334534452341202131405830939397499 / 569451189650961445481878401739991414038782095964760724930400558868762936363990405737219438664238541164520095950956900230307852466522786074935839425287004611674929608474774630492079671436712305195284128698902775572691197139677389700507233086073745096541243160251098823205494851241297156903571630367546419465617576481182184817275013491133193002636894404543625167321418033055627632041698130131519509432501104388756317414943887458514988832587177774849552396396442297897531974852355994389180099210321823751616892326816971344380034762488135913705633163368628406272212272920408153471181616456198812486695036708662812190122104834128739148314486253162258461167294327058109490358518840095312110014193638348367272411490468727340213949435372731111478903464643924771605609211461766587

theorem satFunctional_base125 :
    satFunctional sigma125 autocorrBase125 = jBase := by
  unfold satFunctional
  rw [u_mul_autocorrBase125, integral_polyEval125]
  change 2 * (sigma125 *
      polyInt125 uAutocorrCoeffBase125 0 (1 / sigma125) +
      (∫ u in (1 / sigma125)..1,
        polyEval125 autocorrCoeffBase125 u)) = jBase
  rw [integral_polyEval125]
  norm_num [sigma125, jBase, polyInt125, uAutocorrCoeffBase125,
    autocorrCoeffBase125, Finset.sum_range_succ]

def uAutocorrCoeffCross125 : List ℝ := 0 :: autocorrCoeffCross125

set_option maxRecDepth 100000 in
theorem u_mul_autocorrCross125 :
    (fun u => u * autocorrCross125 u) =
      polyEval125 uAutocorrCoeffCross125 := by
  funext u
  simp [autocorrCross125, polyEval125, autocorrCoeffCross125,
    uAutocorrCoeffCross125, Finset.sum_range_succ]
  ring

def jCross : ℝ := 3050323298588636252548830501726633800443695636119649368053200157730158477864536863310316120661162504237663734125657713882189371655750764857292419681448021655395439298408320377360311179577162450461804836629321927299107855103494760898102444411854655072081258713765775240120520708438495948541689787009251553611723241665373551917550375979225121426295946177601070004418996279999766000000000006 / 3786532344963921437943941179535987198694868759202663401934714121422221074674121626147876922954670961086382944627377750243957907016877778630848046942308635032237241441577246727893417244168121313307958156196946252164407269428154526394801758266403335297090932728662497550248472791910171696870923042249214324951182245544433591906347656250263378906249970937500000002324999999999880000000000003

theorem satFunctional_cross125 :
    satFunctional sigma125 autocorrCross125 = jCross := by
  unfold satFunctional
  rw [u_mul_autocorrCross125, integral_polyEval125]
  change 2 * (sigma125 *
      polyInt125 uAutocorrCoeffCross125 0 (1 / sigma125) +
      (∫ u in (1 / sigma125)..1,
        polyEval125 autocorrCoeffCross125 u)) = jCross
  rw [integral_polyEval125]
  norm_num [sigma125, jCross, polyInt125, uAutocorrCoeffCross125,
    autocorrCoeffCross125, Finset.sum_range_succ]

def constCorr125 (u : ℝ) : ℝ := 1 - u

def jConst : ℝ := 1937499999995500000000003 / 4687499999992500000000003

theorem satFunctional_const125 :
    satFunctional sigma125 constCorr125 = jConst := by
  unfold satFunctional constCorr125
  have h1 : (∫ u in (0 : ℝ)..(1 / sigma125), u * (1 - u)) =
      (1 / sigma125) ^ 2 / 2 - (1 / sigma125) ^ 3 / 3 := by
    have hrw : (fun u : ℝ => u * (1 - u)) = (fun u => u ^ 1 - u ^ 2) := by
      funext u
      ring
    rw [hrw, intervalIntegral.integral_sub
      (intervalIntegral.intervalIntegrable_pow 1)
      (intervalIntegral.intervalIntegrable_pow 2), integral_pow, integral_pow]
    ring
  have h2 : (∫ u in (1 / sigma125)..(1 : ℝ), (1 - u)) =
      (1 - 1 / sigma125) -
        (1 ^ 2 - (1 / sigma125) ^ 2) / 2 := by
    have hrw : (fun u : ℝ => 1 - u) = (fun u => 1 - u ^ 1) := by
      funext u
      ring
    rw [hrw, intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_pow 1),
      intervalIntegral.integral_const, integral_pow]
    simp only [smul_eq_mul]
    ring
  rw [h1, h2]
  norm_num [sigma125, jConst]

theorem continuous_base125 : Continuous base125 := by
  rw [base125_eq_polyEval]
  exact continuous_polyEval coeff125

def profile125 (t s : ℝ) : ℝ := (1 - t) * base125 s + t

theorem integral_profile125 (t : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), profile125 t s) = 1 := by
  have hb : IntervalIntegrable base125 volume
      (-(1 : ℝ) / 2) (1 / 2) :=
    continuous_base125.intervalIntegrable _ _
  simp only [profile125]
  rw [intervalIntegral.integral_add (hb.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_base125,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem integral_profile125_sq (t : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), profile125 t s ^ 2) =
      (1 - t) ^ 2 * baseL2 + 2 * t * (1 - t) + t ^ 2 := by
  have hb : IntervalIntegrable base125 volume
      (-(1 : ℝ) / 2) (1 / 2) :=
    continuous_base125.intervalIntegrable _ _
  have hb2 : IntervalIntegrable (fun s : ℝ => base125 s ^ 2) volume
      (-(1 : ℝ) / 2) (1 / 2) :=
    (continuous_base125.pow 2).intervalIntegrable _ _
  have hpoint : (fun s : ℝ => profile125 t s ^ 2) =
      (fun s => (1 - t) ^ 2 * base125 s ^ 2 +
        (2 * t * (1 - t)) * base125 s + t ^ 2) := by
    funext s
    simp only [profile125]
    ring
  rw [hpoint,
    intervalIntegral.integral_add
      ((hb2.const_mul _).add (hb.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_add (hb2.const_mul _) (hb.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_base125_sq, integral_base125,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem integral_autocorr_profile125 (t u : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u),
      profile125 t s * profile125 t (s + u)) =
      (1 - t) ^ 2 * autocorrBase125 u +
        (t * (1 - t)) * autocorrCross125 u + t ^ 2 * constCorr125 u := by
  have hshift : Continuous (fun s : ℝ => base125 (s + u)) :=
    continuous_base125.comp (continuous_id.add continuous_const)
  have hprod : IntervalIntegrable
      (fun s : ℝ => base125 s * base125 (s + u)) volume
      (-(1 : ℝ) / 2) (1 / 2 - u) :=
    (continuous_base125.mul hshift).intervalIntegrable _ _
  have hcross : IntervalIntegrable
      (fun s : ℝ => base125 s + base125 (s + u)) volume
      (-(1 : ℝ) / 2) (1 / 2 - u) :=
    (continuous_base125.add hshift).intervalIntegrable _ _
  have hpoint :
      (fun s : ℝ => profile125 t s * profile125 t (s + u)) =
      (fun s => (1 - t) ^ 2 * (base125 s * base125 (s + u)) +
        (t * (1 - t)) * (base125 s + base125 (s + u)) + t ^ 2) := by
    funext s
    simp only [profile125]
    ring
  rw [hpoint,
    intervalIntegral.integral_add
      ((hprod.const_mul _).add (hcross.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_add (hprod.const_mul _) (hcross.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_autocorr_base125, integral_autocorr_cross125,
    intervalIntegral.integral_const]
  simp only [constCorr125, smul_eq_mul]
  ring

theorem satJ_profile125 (t : ℝ) :
    satJ sigma125 (profile125 t) =
      (1 - t) ^ 2 * jBase + (t * (1 - t)) * jCross + t ^ 2 * jConst := by
  change satFunctional sigma125
    (fun u => ∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u),
      profile125 t s * profile125 t (s + u)) = _
  rw [show (fun u => ∫ s in (-(1 : ℝ) / 2)..(1 / 2 - u),
      profile125 t s * profile125 t (s + u)) =
      (fun u => (1 - t) ^ 2 * autocorrBase125 u +
        (t * (1 - t)) * autocorrCross125 u + t ^ 2 * constCorr125 u) by
      funext u
      exact integral_autocorr_profile125 t u]
  rw [satFunctional_linear3 sigma125 ((1 - t) ^ 2) (t * (1 - t)) (t ^ 2)
      autocorrBase125 autocorrCross125 constCorr125
      (continuous_polyEval _) (continuous_polyEval _)
      (continuous_const.sub continuous_id),
    satFunctional_base125, satFunctional_cross125, satFunctional_const125]


end RationalWindow125
end Zeta85
end RH
