/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ThresholdLimit
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# `lem:threshold-asymptotic`: the limit of the critical values

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:threshold-asymptotic` (Q-0427).

With `m = (d+1)/2` and `S_m := Γ(m) m^{1/2-m} e^m` (`stirlingRatio`):

1. `tendsto_stirlingRatio`: `S_m → √(2π)` as `m → ∞` through the reals. **Stirling's formula for the
   real Gamma function**, which Mathlib at the pin has for factorials only
   (`Stirling.tendsto_stirlingSeq_sqrt_pi`). Proved as the proof of record does: the substitution
   `t = m + √m v` in `Γ(m+1) = ∫₀^∞ t^m e^{-t} dt` gives `S_m = ∫_ℝ f_m` with
   `f_m(v) = e^{m(log(1+v/√m) - v/√m)}` for `v > -√m` and `0` otherwise
   (`stirlingRatio_eq_integral`);
   `f_m → e^{-v²/2}` pointwise, from Mathlib's bound on the logarithm series
   (`tendsto_stirlingIntegrand`); `0 ≤ f_m ≤ e^{-v²/4} + e^{-|v|/4}` for `m ≥ 1`, from the three
   comparisons of `AffineHemigroup.ThresholdLimit` (`stirlingIntegrand_le`); dominated convergence
   along the filter `atTop` of the reals, which is countably generated, so no sequence is named.
2. `threshold_asymptotic_bounds`: `S_m/2 ≤ √m w_d` for every real `d ≥ 1`, and
   `√m w_d ≤ S_m/(2(1-ε_d))` when `ε_d < 1`.
3. `threshold_asymptotic`: `√m w_d → √(π/2)` and `√d w_d → √π` along the real parameter `d`.

Lean core only: no ledger entry is read.
-/

namespace AffineHemigroup

open MeasureTheory Set Real Filter
open scoped Topology

/-- **`S_m := Γ(m) m^{1/2-m} e^m`** (`lem:threshold-asymptotic`), for a real `m`. The blueprint
writes it for `m = (d+1)/2 ≥ 1`; the definition is total, with Mathlib's real power. -/
noncomputable def stirlingRatio (m : ℝ) : ℝ := Gamma m * m ^ (1 / 2 - m) * Real.exp m

/-- The integrand `f_m` of the proof of record: `e^{-mφ(v/√m)}`, `φ(u) = u - log(1+u)`, for
`v > -√m`, and `0` for `v ≤ -√m`. -/
noncomputable def stirlingIntegrand (m v : ℝ) : ℝ :=
  (Ioi (-Real.sqrt m)).indicator
    (fun v => Real.exp (m * (Real.log (1 + v / Real.sqrt m) - v / Real.sqrt m))) v

theorem stirlingIntegrand_nonneg (m v : ℝ) : 0 ≤ stirlingIntegrand m v :=
  indicator_nonneg (fun _ _ => (Real.exp_pos _).le) v

theorem measurable_stirlingIntegrand (m : ℝ) : Measurable (stirlingIntegrand m) := by
  unfold stirlingIntegrand
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact Real.measurable_exp.comp (measurable_const.mul
    ((Real.measurable_log.comp (measurable_const.add (measurable_id.div_const _))).sub
      (measurable_id.div_const _)))

/-- `S_m = √m Γ(m) / (m^m e^{-m})`. -/
theorem stirlingRatio_eq {m : ℝ} (hm : 0 < m) :
    stirlingRatio m = Real.sqrt m * Gamma m / (m ^ m * Real.exp (-m)) := by
  unfold stirlingRatio
  rw [rpow_sub hm, ← Real.sqrt_eq_rpow, Real.exp_neg]
  have h1 : (m ^ m) ≠ 0 := (rpow_pos_of_pos hm m).ne'
  have h2 : Real.exp m ≠ 0 := (Real.exp_pos m).ne'
  field_simp

theorem stirlingRatio_pos {m : ℝ} (hm : 0 < m) : 0 < stirlingRatio m := by
  unfold stirlingRatio
  have := Gamma_pos_of_pos hm
  positivity

/-! ### Clause (1): `S_m` as an integral over the line -/

/-- The substitution `t = m + √m v`: `e^{-t} t^m = m^m e^{-m} f_m(v)`, both sides `0` when
`t ≤ 0`. -/
theorem gamma_indicator_eq {m : ℝ} (hm : 0 < m) (v : ℝ) :
    (Ioi (0 : ℝ)).indicator (fun t => Real.exp (-t) * t ^ m) (Real.sqrt m * v + m) =
      m ^ m * Real.exp (-m) * stirlingIntegrand m v := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  unfold stirlingIntegrand
  by_cases hv : -Real.sqrt m < v
  · have ht : 0 < Real.sqrt m * v + m := by nlinarith
    rw [indicator_of_mem (mem_Ioi.2 ht), indicator_of_mem (mem_Ioi.2 hv), gamma_integrand_eq hm ht]
    have hu : (Real.sqrt m * v + m) / m - 1 = v / Real.sqrt m := by
      field_simp
      nlinarith
    rw [hu]
  · have ht : ¬ (0 < Real.sqrt m * v + m) := by
      rw [not_lt] at hv ⊢
      nlinarith
    rw [indicator_of_notMem (by simpa using ht), indicator_of_notMem (by simpa using hv), mul_zero]

/-- **`S_m = ∫_ℝ f_m(v) dv`** for `m > 0`. -/
theorem stirlingRatio_eq_integral {m : ℝ} (hm : 0 < m) :
    stirlingRatio m = ∫ v, stirlingIntegrand m v := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  set C := m ^ m * Real.exp (-m) with hC
  have hCpos : 0 < C := by positivity
  set G : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun t => Real.exp (-t) * t ^ m) with hG
  have hGint : ∫ t, G t = Gamma (m + 1) := by
    rw [hG, integral_indicator measurableSet_Ioi, Gamma_eq_integral (by linarith)]
    simp
  have hsub : ∫ v, G (Real.sqrt m * v + m) = |(Real.sqrt m)⁻¹| • ∫ t, G t := by
    rw [Measure.integral_comp_mul_left (fun y => G (y + m)) (Real.sqrt m),
      integral_add_right_eq_self G m]
  have hfm : ∫ v, G (Real.sqrt m * v + m) = C * ∫ v, stirlingIntegrand m v := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v => gamma_indicator_eq hm v)
  rw [hfm, hGint, Gamma_add_one hm.ne', abs_of_pos (inv_pos.2 hs), smul_eq_mul] at hsub
  rw [stirlingRatio_eq hm, ← hC, div_eq_iff hCpos.ne', mul_comm _ C, hsub]
  field_simp
  nlinarith [Gamma_pos_of_pos hm]

/-! ### Clause (1): the domination -/

/-- `0 ≤ f_m(v) ≤ e^{-v²/4} + e^{-|v|/4}` for `m ≥ 1` and every real `v`. -/
theorem stirlingIntegrand_le {m : ℝ} (hm : 1 ≤ m) (v : ℝ) :
    stirlingIntegrand m v ≤ Real.exp (-(1 / 4) * v ^ 2) + Real.exp (-(1 / 4) * |v|) := by
  have hm0 : 0 < m := by linarith
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hs1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.2 hm
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  have hg1 : 0 < Real.exp (-(1 / 4) * v ^ 2) := Real.exp_pos _
  have hg2 : 0 < Real.exp (-(1 / 4) * |v|) := Real.exp_pos _
  unfold stirlingIntegrand
  by_cases hv : -Real.sqrt m < v
  · rw [indicator_of_mem (mem_Ioi.2 hv)]
    set u := v / Real.sqrt m with hu
    have hvu : v = Real.sqrt m * u := by rw [hu]; field_simp
    have hmu2 : m * u ^ 2 = v ^ 2 := by rw [hvu, mul_pow, Real.sq_sqrt hm0.le]
    rcases le_total v 0 with hv0 | hv0
    · -- `-√m < v ≤ 0`: `mφ(u) ≥ v²/2`
      have hu1 : -1 < u := by rw [hu, lt_div_iff₀ hs]; linarith
      have hu0 : u ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv0 hs.le
      have h := log_one_add_le_neg hu1 hu0
      have : m * (Real.log (1 + u) - u) ≤ -(1 / 4) * v ^ 2 := by
        have h' : m * (Real.log (1 + u) - u) ≤ m * (-(u ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hm0.le
        nlinarith [sq_nonneg v]
      have := Real.exp_le_exp.2 this
      linarith
    · rcases le_total v (Real.sqrt m) with hvs | hvs
      · -- `0 ≤ v ≤ √m`: `mφ(u) ≥ v²/4`
        have hu0 : 0 ≤ u := div_nonneg hv0 hs.le
        have hu1 : u ≤ 1 := by rw [hu, div_le_one hs]; exact hvs
        have h := log_one_add_le_quarter hu0 hu1
        have : m * (Real.log (1 + u) - u) ≤ -(1 / 4) * v ^ 2 := by
          have h' : m * (Real.log (1 + u) - u) ≤ m * (-(u ^ 2 / 4)) :=
            mul_le_mul_of_nonneg_left (by linarith) hm0.le
          nlinarith
        have := Real.exp_le_exp.2 this
        linarith
      · -- `v ≥ √m`: `mφ(u) ≥ √m v/4 ≥ v/4`
        have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hs]; linarith
        have h := log_one_add_le_linear hu1
        have hmu : m * u = Real.sqrt m * v := by rw [hvu, ← mul_assoc, hss]
        have : m * (Real.log (1 + u) - u) ≤ -(1 / 4) * |v| := by
          have h' : m * (Real.log (1 + u) - u) ≤ m * (-(u / 4)) :=
            mul_le_mul_of_nonneg_left (by linarith) hm0.le
          rw [abs_of_nonneg hv0]
          nlinarith
        have := Real.exp_le_exp.2 this
        linarith
  · rw [indicator_of_notMem (by simpa using hv)]
    linarith

/-- The dominating function is integrable on the line. -/
theorem integrable_stirlingBound :
    Integrable (fun v : ℝ => Real.exp (-(1 / 4) * v ^ 2) + Real.exp (-(1 / 4) * |v|)) := by
  refine (integrable_exp_neg_mul_sq (by norm_num)).add ?_
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic (a := 1 / 4) (by norm_num) 0).congr_fun (fun v hv => ?_)
      measurableSet_Iic
    simp only [abs_of_nonpos (mem_Iic.1 hv)]
    ring_nf
  · refine (integrableOn_exp_mul_Ioi (a := -(1 / 4)) (by norm_num) 0).congr_fun (fun v hv => ?_)
      measurableSet_Ioi
    simp only [abs_of_pos (mem_Ioi.1 hv)]

/-! ### Clause (1): the pointwise limit -/

/-- `m(log(1+v/√m) - v/√m) → -v²/2` as `m → ∞`, for every real `v`. -/
theorem tendsto_stirlingExponent (v : ℝ) :
    Tendsto (fun m : ℝ => m * (Real.log (1 + v / Real.sqrt m) - v / Real.sqrt m)) atTop
      (𝓝 (-(v ^ 2 / 2))) := by
  have hu : Tendsto (fun m : ℝ => v / Real.sqrt m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hb : Tendsto (fun m : ℝ => v ^ 2 * (|v / Real.sqrt m| / (1 - |v / Real.sqrt m|))) atTop
      (𝓝 0) := by
    have := (hu.abs.div ((tendsto_const_nhds (x := (1 : ℝ))).sub hu.abs) (by simp)).const_mul
      (v ^ 2)
    simpa using this
  have hsmall : ∀ᶠ m : ℝ in atTop, |v / Real.sqrt m| < 1 :=
    (tendsto_order.1 hu.abs).2 1 (by simp)
  have key : ∀ᶠ m : ℝ in atTop,
      ‖m * (Real.log (1 + v / Real.sqrt m) - v / Real.sqrt m) - -(v ^ 2 / 2)‖ ≤
        v ^ 2 * (|v / Real.sqrt m| / (1 - |v / Real.sqrt m|)) := by
    filter_upwards [hsmall, eventually_gt_atTop 0] with m hm hm0
    set u := v / Real.sqrt m with hudef
    have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
    have hmu2 : m * u ^ 2 = v ^ 2 := by
      rw [hudef, div_pow, Real.sq_sqrt hm0.le]; field_simp
    have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rwa [abs_neg]) 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, abs_neg, sub_neg_eq_add]
      at h
    norm_num at h
    have h1u : 0 < 1 - |u| := by linarith
    have e : m * (Real.log (1 + u) - u) - -(v ^ 2 / 2) =
        m * (-u + u ^ 2 / 2 + Real.log (1 + u)) := by rw [← hmu2]; ring
    rw [Real.norm_eq_abs, e, abs_mul, abs_of_pos hm0]
    calc m * |-u + u ^ 2 / 2 + Real.log (1 + u)|
        ≤ m * (|u| ^ 3 / (1 - |u|)) := mul_le_mul_of_nonneg_left h hm0.le
      _ = v ^ 2 * (|u| / (1 - |u|)) := by
          rw [← hmu2, ← sq_abs u]; field_simp
  exact tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' key hb)

/-- `f_m(v) → e^{-v²/2}` as `m → ∞`, for every real `v`. -/
theorem tendsto_stirlingIntegrand (v : ℝ) :
    Tendsto (fun m : ℝ => stirlingIntegrand m v) atTop (𝓝 (Real.exp (-(1 / 2) * v ^ 2))) := by
  have h := (Real.continuous_exp.tendsto _).comp (tendsto_stirlingExponent v)
  rw [show -(v ^ 2 / 2) = -(1 / 2) * v ^ 2 by ring] at h
  refine h.congr' ?_
  have hlarge : ∀ᶠ m : ℝ in atTop, -Real.sqrt m < v := by
    have : Tendsto (fun m : ℝ => -Real.sqrt m) atTop atBot :=
      tendsto_neg_atTop_atBot.comp Real.tendsto_sqrt_atTop
    exact this.eventually (eventually_lt_atBot v)
  filter_upwards [hlarge] with m hm
  simp [stirlingIntegrand, indicator_of_mem (mem_Ioi.2 hm)]

/-- **`lem:threshold-asymptotic`(1), Stirling's formula for the real Gamma function**:
`Γ(m) m^{1/2-m} e^m → √(2π)` as `m → ∞` through the reals. -/
theorem tendsto_stirlingRatio : Tendsto stirlingRatio atTop (𝓝 (Real.sqrt (2 * π))) := by
  have hlim : Tendsto (fun m : ℝ => ∫ v, stirlingIntegrand m v) atTop
      (𝓝 (∫ v : ℝ, Real.exp (-(1 / 2) * v ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v : ℝ => Real.exp (-(1 / 4) * v ^ 2) + Real.exp (-(1 / 4) * |v|)) ?_ ?_
      integrable_stirlingBound ?_
    · exact Filter.Eventually.of_forall fun m =>
        (measurable_stirlingIntegrand m).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with m hm
      refine Filter.Eventually.of_forall fun v => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (stirlingIntegrand_nonneg m v)]
      exact stirlingIntegrand_le hm v
    · exact Filter.Eventually.of_forall tendsto_stirlingIntegrand
  rw [integral_gaussian, show π / (1 / 2) = 2 * π by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact (stirlingRatio_eq_integral hm).symm

/-! ### Clause (2): the critical value against the Gamma function -/

/-- **`lem:threshold-asymptotic`(2)**: for a real `d ≥ 1` and `m = (d+1)/2`, `S_m/2 ≤ √m w_d`, and
`√m w_d ≤ S_m/(2(1-ε_d))` when `ε_d < 1`. -/
theorem threshold_asymptotic_bounds (d : ℝ) (hd : 1 ≤ d) :
    stirlingRatio ((d + 1) / 2) / 2 ≤ Real.sqrt ((d + 1) / 2) * threshold d ∧
      (thresholdEps d < 1 →
        Real.sqrt ((d + 1) / 2) * threshold d ≤
          stirlingRatio ((d + 1) / 2) / (2 * (1 - thresholdEps d))) := by
  set m := (d + 1) / 2 with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  set C := m ^ m * Real.exp (-m) with hC
  have hCpos : 0 < C := by positivity
  have hM := (thresholdSup_spec d hd).2.1
  have hMle : thresholdSup d ≤ C := thresholdSup_le hd
  have hG := Gamma_pos_of_pos hm0
  have hnum : 0 < Real.sqrt m * Gamma m := mul_pos hs hG
  have hw : Real.sqrt m * threshold d = Real.sqrt m * Gamma m / (2 * thresholdSup d) := by
    unfold threshold; rw [← hmdef, mul_div_assoc]
  rw [hw, stirlingRatio_eq hm0, ← hC]
  refine ⟨?_, fun hε => ?_⟩
  · rw [div_div]
    exact div_le_div_of_nonneg_left hnum.le (by positivity) (by linarith)
  · have hMge := le_thresholdSup hd
    rw [← hmdef, ← hC] at hMge
    have h1ε : 0 < 1 - thresholdEps d := by linarith
    rw [div_div]
    refine div_le_div_of_nonneg_left hnum.le (by positivity) ?_
    nlinarith

/-! ### Clause (3): the limit -/

/-- **`lem:threshold-asymptotic`(3)**: as `d → ∞` through the reals, `√m w_d → √(π/2)` with
`m = (d+1)/2`, and `√d w_d → √π`. -/
theorem threshold_asymptotic :
    Tendsto (fun d : ℝ => Real.sqrt ((d + 1) / 2) * threshold d) atTop (𝓝 (Real.sqrt (π / 2))) ∧
      Tendsto (fun d : ℝ => Real.sqrt d * threshold d) atTop (𝓝 (Real.sqrt π)) := by
  have hm : Tendsto (fun d : ℝ => (d + 1) / 2) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_id).atTop_div_const (by norm_num)
  have hS : Tendsto (fun d : ℝ => stirlingRatio ((d + 1) / 2)) atTop (𝓝 (Real.sqrt (2 * π))) :=
    tendsto_stirlingRatio.comp hm
  have hε : Tendsto thresholdEps atTop (𝓝 0) := threshold_limit.2.1
  have hval : Real.sqrt (2 * π) / 2 = Real.sqrt (π / 2) := by
    rw [show π / 2 = 2 * π / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hlow : Tendsto (fun d : ℝ => stirlingRatio ((d + 1) / 2) / 2) atTop
      (𝓝 (Real.sqrt (π / 2))) := by
    rw [← hval]; exact hS.div_const 2
  have hupp : Tendsto (fun d : ℝ => stirlingRatio ((d + 1) / 2) / (2 * (1 - thresholdEps d)))
      atTop (𝓝 (Real.sqrt (π / 2))) := by
    have h2 : Tendsto (fun d : ℝ => 2 * (1 - thresholdEps d)) atTop (𝓝 2) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hε).const_mul (2 : ℝ)
    rw [← hval]
    exact hS.div h2 (by norm_num)
  have hfirst : Tendsto (fun d : ℝ => Real.sqrt ((d + 1) / 2) * threshold d) atTop
      (𝓝 (Real.sqrt (π / 2))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with d hd
      exact (threshold_asymptotic_bounds d hd).1
    · filter_upwards [eventually_ge_atTop 1, (tendsto_order.1 hε).2 1 one_pos] with d hd hε1
      exact (threshold_asymptotic_bounds d hd).2 hε1
  refine ⟨hfirst, ?_⟩
  -- `√d = √(2d/(d+1)) √m`, and `2d/(d+1) → 2`
  have hratio : Tendsto (fun d : ℝ => 2 * d / (d + 1)) atTop (𝓝 2) := by
    have h1 : Tendsto (fun d : ℝ => 2 - 2 / (d + 1)) atTop (𝓝 (2 - 0)) :=
      tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_id))
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with d hd
    have : d + 1 ≠ 0 := by linarith
    field_simp
    ring
  have hsqrt : Tendsto (fun d : ℝ => Real.sqrt (2 * d / (d + 1))) atTop (𝓝 (Real.sqrt 2)) :=
    (Real.continuous_sqrt.tendsto 2).comp hratio
  have hprod := hsqrt.mul hfirst
  rw [← Real.sqrt_mul (by norm_num), show 2 * (π / 2) = π by ring] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  rw [← mul_assoc, ← Real.sqrt_mul (by positivity)]
  congr 2
  field_simp

end AffineHemigroup
