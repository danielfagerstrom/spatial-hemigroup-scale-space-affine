/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Thresholds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `lem:threshold-criterion`: the witness profiles in closed form, and the monotonicity criterion

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:threshold-criterion` (wave 1, group D,
Q-0281): for an integer `d ≥ 1` and `w > 0`, with `s = d/2`, `m = (d+1)/2`,

* `witness_polar_closed_form`: [B, (A.1)],
  `k^{(w)}_d(r) = 2^{3/2}Γ(m)/(Γ(s) r) + 2w[P(s, r²/2) - P(s, r²/4)]` for `r > 0`, smooth on
  `(0,∞)`;
* `witness_threshold_criterion`: [B, (A.2)], `(k^{(w)}_d)'(r) ≤ 0` iff `w h_d(r²/2) ≤ Γ(m)/2`;
* `witness_antitone_iff`: `k^{(w)}_d` is nonincreasing on `(0,∞)` exactly when `w ≤ w_d`.

The incomplete gamma integral is handled through `lowerGammaInt s x = ∫₀ˣ v^{s-1} e^{-v} dv`, an
interval integral, whose derivative at `x > 0` is the integrand (the fundamental theorem of
calculus); Mathlib has no incomplete gamma function. Lean core only: no ledger entry is read.
-/

namespace AffineHemigroup

open MeasureTheory Set Real Filter
open scoped Topology

/-! ### The Gamma integrand and the lower incomplete gamma integral -/

/-- The Gamma integrand `v^{s-1} e^{-v}` is integrable on `(0,∞)` for `s > 0`. -/
theorem integrableOn_rpow_mul_exp_neg {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun v : ℝ => v ^ (s - 1) * exp (-v)) (Ioi 0) := by
  simpa only [mul_comm] using GammaIntegral_convergent hs

/-- `∫₀^∞ v^{s-1} e^{-v} dv = Γ(s)` for `s > 0`. -/
theorem integral_rpow_mul_exp_neg {s : ℝ} (hs : 0 < s) :
    ∫ v in Ioi (0 : ℝ), v ^ (s - 1) * exp (-v) = Gamma s := by
  rw [Gamma_eq_integral hs]
  simp only [mul_comm]

/-- **The lower incomplete gamma integral** `γ(s, x) = ∫₀ˣ v^{s-1} e^{-v} dv`, as an interval
integral (so that the fundamental theorem of calculus applies to it). -/
noncomputable def lowerGammaInt (s x : ℝ) : ℝ := ∫ v in (0 : ℝ)..x, v ^ (s - 1) * exp (-v)

/-- The Gamma integrand is interval integrable on `[0, x]` for `x ≥ 0` and `s > 0`. -/
theorem intervalIntegrable_rpow_mul_exp_neg {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    IntervalIntegrable (fun v : ℝ => v ^ (s - 1) * exp (-v)) volume 0 x :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2
    ((integrableOn_rpow_mul_exp_neg hs).mono_set Ioc_subset_Ioi_self)

/-- `P(s, x) = Γ(s)⁻¹ γ(s, x)` for `x ≥ 0`. -/
theorem regIncGamma_eq (s : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    regIncGamma s x = (Gamma s)⁻¹ * lowerGammaInt s x := by
  rw [regIncGamma, lowerGammaInt, intervalIntegral.integral_of_le hx]

/-- The Gamma integrand is continuous on `(0,∞)`. -/
theorem continuousOn_rpow_mul_exp_neg (s : ℝ) :
    ContinuousOn (fun v : ℝ => v ^ (s - 1) * exp (-v)) (Ioi 0) := fun v hv =>
  ((continuousAt_rpow_const v _ (Or.inl (ne_of_gt hv))).mul
    (continuous_exp.comp continuous_neg).continuousAt).continuousWithinAt

/-- **The derivative of `γ(s, ·)`** at `x > 0` is the integrand `x^{s-1} e^{-x}`. -/
theorem hasDerivAt_lowerGammaInt {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (lowerGammaInt s) (x ^ (s - 1) * exp (-x)) x :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_rpow_mul_exp_neg hs hx.le)
    ((continuousOn_rpow_mul_exp_neg s).stronglyMeasurableAtFilter isOpen_Ioi x hx)
    ((continuousOn_rpow_mul_exp_neg s).continuousAt (Ioi_mem_nhds hx))

/-- `γ(s, ·)` is smooth on `(0,∞)`. -/
theorem contDiffOn_lowerGammaInt {s : ℝ} (hs : 0 < s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lowerGammaInt s) (Ioi 0) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun x hx => (hasDerivAt_lowerGammaInt hs hx).differentiableAt.differentiableWithinAt,
    ?_⟩
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => v ^ (s - 1) * exp (-v)) (Ioi 0) :=
    fun v hv => ((contDiffAt_rpow_const_of_ne (ne_of_gt hv)).mul
      (contDiff_exp.comp contDiff_neg).contDiffAt).contDiffWithinAt
  exact hf.congr fun x hx => (hasDerivAt_lowerGammaInt hs hx).deriv

/-! ### The closed form [B, (A.1)] -/

/-- `(r²/2)^{-1/2} = √2 / r` for `r > 0`, with `√2` written `2^{1/2}`. -/
theorem rpow_sq_half_neg_half {r : ℝ} (hr : 0 < r) :
    (r ^ 2 / 2) ^ (-(1 : ℝ) / 2) = (2 : ℝ) ^ ((1 : ℝ) / 2) / r := by
  rw [neg_div, rpow_neg (by positivity), div_rpow (by positivity) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le, inv_div]

/-- The integrand of the polar profile of the witness, split at the two summands of the profile:
for `v > 0`, `v^{s-1} e^{-v} k^{(w)}_I(r²/2v) = (r²/2)^{-1/2} v^{(s+1/2)-1} e^{-v}
  + w 1_{[r²/4, r²/2]}(v) v^{s-1} e^{-v}`. -/
theorem witness_integrand_eq (s w : ℝ) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    v ^ (s - 1) * exp (-v) * witnessProfile w (r ^ 2 / (2 * v)) =
      (r ^ 2 / 2) ^ (-(1 : ℝ) / 2) * (v ^ (s + 1 / 2 - 1) * exp (-v)) +
        w * (Icc (r ^ 2 / 4) (r ^ 2 / 2)).indicator (fun v => v ^ (s - 1) * exp (-v)) v := by
  have hu : 0 < r ^ 2 / (2 * v) := by positivity
  have hmem : r ^ 2 / (2 * v) ∈ Icc (1 : ℝ) 2 ↔ v ∈ Icc (r ^ 2 / 4) (r ^ 2 / 2) := by
    simp only [mem_Icc]
    rw [le_div_iff₀ (by positivity), div_le_iff₀ (by positivity), div_le_iff₀ (by norm_num),
      le_div_iff₀ (by norm_num)]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hpow : v ^ (s - 1) * (r ^ 2 / (2 * v)) ^ (-(1 : ℝ) / 2) =
      (r ^ 2 / 2) ^ (-(1 : ℝ) / 2) * v ^ (s + 1 / 2 - 1) := by
    have e1 : r ^ 2 / (2 * v) = r ^ 2 / 2 * v⁻¹ := by field_simp
    rw [e1, mul_rpow (by positivity) (by positivity), inv_rpow hv.le,
      show s + 1 / 2 - 1 = (s - 1) - (-(1 : ℝ) / 2) by ring, rpow_sub hv (s - 1) (-(1 : ℝ) / 2),
      div_eq_mul_inv]
    ring
  unfold witnessProfile
  rw [if_pos hu]
  by_cases h : v ∈ Icc (r ^ 2 / 4) (r ^ 2 / 2)
  · rw [if_pos (hmem.2 h), indicator_of_mem h]
    have := hpow; linear_combination exp (-v) * this
  · rw [if_neg (fun h' => h (hmem.1 h')), indicator_of_notMem h]
    have := hpow; linear_combination exp (-v) * this

/-- `∫_{[a,b]} v^{s-1} e^{-v} dv = γ(s, b) - γ(s, a)` for `0 ≤ a ≤ b`. -/
theorem integral_Icc_rpow_mul_exp_neg {s a b : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ v in Icc a b, v ^ (s - 1) * exp (-v) = lowerGammaInt s b - lowerGammaInt s a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, lowerGammaInt,
    lowerGammaInt, intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_rpow_mul_exp_neg hs (ha.trans hab))
      (intervalIntegrable_rpow_mul_exp_neg hs ha)]

/-- **The closed form [B, (A.1)] through `γ`**: for an integer `d ≥ 1` and `r > 0`,
`k^{(w)}_d(r) = 2^{3/2}Γ(m)/(Γ(d/2) r) + (2w/Γ(d/2)) [γ(d/2, r²/2) - γ(d/2, r²/4)]`. -/
theorem polarProfileOf_witness_eq (d : ℕ) (hd : 1 ≤ d) (w : ℝ) {r : ℝ} (hr : 0 < r) :
    polarProfileOf (witnessProfile w) d r =
      2 ^ ((3 : ℝ) / 2) * Gamma (((d : ℝ) + 1) / 2) / Gamma ((d : ℝ) / 2) / r
        + 2 * w * ((Gamma ((d : ℝ) / 2))⁻¹ * lowerGammaInt ((d : ℝ) / 2) (r ^ 2 / 2)
          - (Gamma ((d : ℝ) / 2))⁻¹ * lowerGammaInt ((d : ℝ) / 2) (r ^ 2 / 4)) := by
  set s : ℝ := (d : ℝ) / 2 with hs_def
  have hs : 0 < s := by
    rw [hs_def]; have h1 : (1 : ℝ) ≤ d := (by exact_mod_cast hd); linarith
  have hG : 0 < Gamma s := Gamma_pos_of_pos hs
  have hint1 : IntegrableOn (fun v : ℝ => (r ^ 2 / 2) ^ (-(1 : ℝ) / 2) *
      (v ^ (s + 1 / 2 - 1) * exp (-v))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg (by linarith)).const_mul _
  have hint2 : IntegrableOn (fun v : ℝ => w * (Icc (r ^ 2 / 4) (r ^ 2 / 2)).indicator
      (fun v => v ^ (s - 1) * exp (-v)) v) (Ioi 0) :=
    ((integrableOn_rpow_mul_exp_neg hs).indicator measurableSet_Icc).const_mul _
  have hsplit : ∫ v in Ioi (0 : ℝ), v ^ (s - 1) * exp (-v) * witnessProfile w (r ^ 2 / (2 * v)) =
      (r ^ 2 / 2) ^ (-(1 : ℝ) / 2) * Gamma (s + 1 / 2) +
        w * (lowerGammaInt s (r ^ 2 / 2) - lowerGammaInt s (r ^ 2 / 4)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun v hv => witness_integrand_eq s w hr hv,
      integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_rpow_mul_exp_neg (by linarith), setIntegral_indicator measurableSet_Icc,
      inter_eq_right.2 (show Icc (r ^ 2 / 4) (r ^ 2 / 2) ⊆ Ioi 0 from
        fun v hv => lt_of_lt_of_le (by positivity) hv.1),
      integral_Icc_rpow_mul_exp_neg hs (by positivity) (by linarith [sq_nonneg r])]
  unfold polarProfileOf
  rw [← hs_def, hsplit, rpow_sq_half_neg_half hr,
    show s + 1 / 2 = ((d : ℝ) + 1) / 2 by rw [hs_def]; ring,
    show (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * 2 ^ ((1 : ℝ) / 2) by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, rpow_add two_pos, rpow_one]]
  field_simp

/-- **The closed form function**, `r ↦ 2^{3/2}Γ(m)/(Γ(d/2)) r⁻¹ + (2w/Γ(d/2))[γ(d/2, r²/2) -
γ(d/2, r²/4)]`, defined on all of `ℝ`; it is `k^{(w)}_d` on `(0,∞)`
(`polarProfileOf_witness_eq`). -/
noncomputable def witnessClosedForm (d : ℕ) (w r : ℝ) : ℝ :=
  2 ^ ((3 : ℝ) / 2) * Gamma (((d : ℝ) + 1) / 2) / Gamma ((d : ℝ) / 2) * r⁻¹
    + 2 * w * ((Gamma ((d : ℝ) / 2))⁻¹ * lowerGammaInt ((d : ℝ) / 2) (r ^ 2 / 2)
      - (Gamma ((d : ℝ) / 2))⁻¹ * lowerGammaInt ((d : ℝ) / 2) (r ^ 2 / 4))

theorem polarProfileOf_witness_eq_closedForm (d : ℕ) (hd : 1 ≤ d) (w : ℝ) {r : ℝ} (hr : 0 < r) :
    polarProfileOf (witnessProfile w) d r = witnessClosedForm d w r := by
  rw [polarProfileOf_witness_eq d hd w hr, witnessClosedForm, div_eq_mul_inv _ r]

/-- The witness profile agrees with its closed form near every `r > 0`. -/
theorem polarProfileOf_witness_eventuallyEq (d : ℕ) (hd : 1 ≤ d) (w : ℝ) {r : ℝ} (hr : 0 < r) :
    polarProfileOf (witnessProfile w) d =ᶠ[𝓝 r] witnessClosedForm d w :=
  Filter.eventually_of_mem (Ioi_mem_nhds hr) fun _ hx =>
    polarProfileOf_witness_eq_closedForm d hd w hx

/-- **The derivative of the closed form** at `r > 0`. -/
theorem hasDerivAt_witnessClosedForm (d : ℕ) (hd : 1 ≤ d) (w : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (witnessClosedForm d w)
      (2 ^ ((3 : ℝ) / 2) * Gamma (((d : ℝ) + 1) / 2) / Gamma ((d : ℝ) / 2) * (-(r ^ 2)⁻¹)
        + 2 * w * ((Gamma ((d : ℝ) / 2))⁻¹ *
            ((r ^ 2 / 2) ^ ((d : ℝ) / 2 - 1) * exp (-(r ^ 2 / 2)) * r)
          - (Gamma ((d : ℝ) / 2))⁻¹ *
            ((r ^ 2 / 4) ^ ((d : ℝ) / 2 - 1) * exp (-(r ^ 2 / 4)) * (r / 2)))) r := by
  have hs : 0 < (d : ℝ) / 2 := by
    have h1 : (1 : ℝ) ≤ d := (by exact_mod_cast hd); linarith
  have hq2 : HasDerivAt (fun r : ℝ => r ^ 2 / 2) r r := by
    have := (hasDerivAt_pow 2 r).div_const 2
    exact this.congr_deriv (by push_cast; ring)
  have hq4 : HasDerivAt (fun r : ℝ => r ^ 2 / 4) (r / 2) r := by
    have := (hasDerivAt_pow 2 r).div_const 4
    exact this.congr_deriv (by push_cast; ring)
  have hg2 := (hasDerivAt_lowerGammaInt hs (by positivity : 0 < r ^ 2 / 2)).comp r hq2
  have hg4 := (hasDerivAt_lowerGammaInt hs (by positivity : 0 < r ^ 2 / 4)).comp r hq4
  have hinv := hasDerivAt_inv hr.ne'
  have := (hinv.const_mul (2 ^ ((3 : ℝ) / 2) * Gamma (((d : ℝ) + 1) / 2) / Gamma ((d : ℝ) / 2))).add
    (((hg2.const_mul (Gamma ((d : ℝ) / 2))⁻¹).sub
      (hg4.const_mul (Gamma ((d : ℝ) / 2))⁻¹)).const_mul (2 * w))
  exact this

/-- **The closed form [B, (A.1)] is smooth** on `(0,∞)`. -/
theorem contDiffOn_witnessClosedForm (d : ℕ) (hd : 1 ≤ d) (w : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (witnessClosedForm d w) (Ioi 0) := by
  have hs : 0 < (d : ℝ) / 2 := by
    have h1 : (1 : ℝ) ≤ d := (by exact_mod_cast hd); linarith
  have hL := contDiffOn_lowerGammaInt hs
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ => lowerGammaInt ((d : ℝ) / 2) (r ^ 2 / 2)) (Ioi 0) :=
    hL.comp ((contDiff_id.pow 2).div_const 2).contDiffOn fun r (hr : 0 < r) =>
      (by positivity : 0 < r ^ 2 / 2)
  have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ => lowerGammaInt ((d : ℝ) / 2) (r ^ 2 / 4)) (Ioi 0) :=
    hL.comp ((contDiff_id.pow 2).div_const 4).contDiffOn fun r (hr : 0 < r) =>
      (by positivity : 0 < r ^ 2 / 4)
  have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ => r⁻¹) (Ioi 0) :=
    (contDiffOn_inv (𝕜 := ℝ)).mono fun r (hr : 0 < r) => hr.ne'
  unfold witnessClosedForm
  exact (contDiffOn_const.mul hinv).add
    (contDiffOn_const.mul ((contDiffOn_const.mul h2).sub (contDiffOn_const.mul h4)))

/-- **`lem:threshold-criterion`**, [B, (A.1)] restated: for an integer `d ≥ 1` and `w > 0`,
`k^{(w)}_d(r) = 2^{3/2}Γ(m)/(Γ(d/2) r) + 2w[P(d/2, r²/2) - P(d/2, r²/4)]` for `r > 0`, a smooth
function on `(0,∞)`. -/
theorem witness_polar_closed_form (d : ℕ) (hd : 1 ≤ d) {w : ℝ} (_hw : 0 < w) :
    (∀ r : ℝ, 0 < r → polarProfileOf (witnessProfile w) d r =
        2 ^ ((3 : ℝ) / 2) * Real.Gamma (((d : ℝ) + 1) / 2) / Real.Gamma ((d : ℝ) / 2) / r
          + 2 * w * (regIncGamma ((d : ℝ) / 2) (r ^ 2 / 2)
            - regIncGamma ((d : ℝ) / 2) (r ^ 2 / 4))) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polarProfileOf (witnessProfile w) d) (Ioi 0) := by
  refine ⟨fun r hr => ?_, (contDiffOn_witnessClosedForm d hd w).congr fun r hr =>
    polarProfileOf_witness_eq_closedForm d hd w hr⟩
  rw [polarProfileOf_witness_eq d hd w hr, regIncGamma_eq _ (by positivity),
    regIncGamma_eq _ (by positivity)]

/-- **The derivative of `k^{(w)}_d`, rescaled** (the computation behind [B, (A.2)]): for `r > 0`,
with `z = r²/2`, `r²Γ(d/2) (k^{(w)}_d)'(r) = 2^{3/2}(-Γ(m) + 2w h_d(z))`. -/
theorem witness_deriv_mul_eq (d : ℕ) (hd : 1 ≤ d) (w : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (polarProfileOf (witnessProfile w) d) r * (r ^ 2 * Gamma ((d : ℝ) / 2)) =
      2 ^ ((3 : ℝ) / 2) * (-Gamma (((d : ℝ) + 1) / 2) + 2 * w * thresholdFun d (r ^ 2 / 2)) := by
  rw [(polarProfileOf_witness_eventuallyEq d hd w hr).deriv_eq,
    (hasDerivAt_witnessClosedForm d hd w hr).deriv]
  set s : ℝ := (d : ℝ) / 2 with hs_def
  have hs : 0 < s := by
    rw [hs_def]; have h1 : (1 : ℝ) ≤ d := (by exact_mod_cast hd); linarith
  have hG : 0 < Gamma s := Gamma_pos_of_pos hs
  set T : ℝ := (2 : ℝ) ^ ((3 : ℝ) / 2) with hT_def
  set a : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 2) with ha_def
  have hT : T = 2 * a := by
    rw [hT_def, ha_def, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, rpow_add two_pos, rpow_one]
  have haa : a * a = 2 := by
    rw [ha_def, ← Real.sqrt_eq_rpow]; exact Real.mul_self_sqrt (by norm_num)
  set z : ℝ := r ^ 2 / 2 with hz_def
  have hz : 0 < z := by positivity
  set b : ℝ := z ^ ((1 : ℝ) / 2) with hb_def
  have hbb : b * b = z := by
    rw [hb_def, ← Real.sqrt_eq_rpow]; exact Real.mul_self_sqrt hz.le
  have hrab : r = a * b := by
    rw [ha_def, hb_def, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num),
      hz_def, show 2 * (r ^ 2 / 2) = r ^ 2 by ring, Real.sqrt_sq hr.le]
  set m : ℝ := ((d : ℝ) + 1) / 2 with hm_def
  have hzm : z ^ m = z * b * z ^ (s - 1) := by
    rw [show m = 1 + 1 / 2 + (s - 1) by rw [hm_def, hs_def]; ring, rpow_add hz, rpow_add hz,
      rpow_one]
  -- (a): `(r²/2)^{s-1} r³ = 2^{3/2} z^m`
  have hA : z ^ (s - 1) * r ^ 3 = T * z ^ m := by
    rw [hzm, hT]
    have hr3 : r ^ 3 = a * b * (a * a) * (b * b) := by rw [hrab]; ring
    rw [hr3, haa, hbb]; ring
  -- (b): `(r²/4)^{s-1} r³ / 2 = 2^{3/2} z^m 2^{-d/2}`
  have h2s : (2 : ℝ) ^ (-(d : ℝ) / 2) = ((2 : ℝ) ^ (s - 1) * 2)⁻¹ := by
    rw [show -(d : ℝ) / 2 = -s by rw [hs_def]; ring, rpow_neg (by norm_num),
      ← rpow_add_one (by norm_num : (2 : ℝ) ≠ 0), sub_add_cancel]
  have h2pos : 0 < (2 : ℝ) ^ (s - 1) := by positivity
  have hB : (r ^ 2 / 4) ^ (s - 1) * r ^ 3 / 2 = T * z ^ m * (2 : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [show r ^ 2 / 4 = z / 2 by rw [hz_def]; ring, div_rpow hz.le (by norm_num), h2s, ← hA]
    field_simp
  have hE : exp (-(r ^ 2 / 4)) = exp (-z / 2) := by rw [hz_def]; ring_nf
  have hC : T * Gamma m / Gamma s * (-(r ^ 2)⁻¹) * (r ^ 2 * Gamma s) = -(T * Gamma m) := by
    field_simp
  have hGinv : (Gamma s)⁻¹ * Gamma s = 1 := inv_mul_cancel₀ hG.ne'
  rw [hE]
  unfold thresholdFun
  rw [← hm_def]
  linear_combination hC + 2 * w * (z ^ (s - 1) * exp (-z) * r ^ 3
      - (r ^ 2 / 4) ^ (s - 1) * exp (-z / 2) * (r ^ 3 / 2)) * hGinv
    + 2 * w * exp (-z) * hA - 2 * w * exp (-z / 2) * hB

/-- **`lem:threshold-criterion`**, [B, (A.2)] restated: the derivative of `k^{(w)}_d` is nonpositive
at `r > 0` if and only if `w z^m (e^{-z} - 2^{-d/2} e^{-z/2}) ≤ Γ(m)/2`, `z = r²/2`. -/
theorem witness_threshold_criterion (d : ℕ) (hd : 1 ≤ d) {w : ℝ} (_hw : 0 < w) {r : ℝ}
    (hr : 0 < r) :
    deriv (polarProfileOf (witnessProfile w) d) r ≤ 0 ↔
      w * thresholdFun d (r ^ 2 / 2) ≤ Real.Gamma (((d : ℝ) + 1) / 2) / 2 := by
  have hs : 0 < (d : ℝ) / 2 := by
    have h1 : (1 : ℝ) ≤ d := (by exact_mod_cast hd); linarith
  have hc : 0 < r ^ 2 * Gamma ((d : ℝ) / 2) := mul_pos (by positivity) (Gamma_pos_of_pos hs)
  have hT : 0 < (2 : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have key := witness_deriv_mul_eq d hd w hr
  set D := deriv (polarProfileOf (witnessProfile w) d) r
  set c := r ^ 2 * Gamma ((d : ℝ) / 2)
  constructor
  · intro h
    have h1 : D * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hc.le
    rw [key] at h1
    have h2 : -Gamma (((d : ℝ) + 1) / 2) + 2 * w * thresholdFun d (r ^ 2 / 2) ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.2 (mul_pos hT (lt_of_not_ge h3)))
    linarith
  · intro h
    have h1 : -Gamma (((d : ℝ) + 1) / 2) + 2 * w * thresholdFun d (r ^ 2 / 2) ≤ 0 := by linarith
    have h2 : D * c ≤ 0 := by rw [key]; exact mul_nonpos_of_nonneg_of_nonpos hT.le h1
    by_contra h3
    exact absurd h2 (not_le.2 (mul_pos (lt_of_not_ge h3) hc))

/-- **`lem:threshold-criterion`** (`lem:threshold-monotone`'s clause): for an integer `d ≥ 1` and
`w > 0`, `k^{(w)}_d` is nonincreasing on `(0,∞)` exactly when `w ≤ w_d`. -/
theorem witness_antitone_iff (d : ℕ) (hd : 1 ≤ d) {w : ℝ} (hw : 0 < w) :
    AntitoneOn (polarProfileOf (witnessProfile w) d) (Ioi 0) ↔ w ≤ threshold d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨_, hM, z₀, hz₀, hz₀M⟩ := thresholdSup_spec d hd'
  have hGm : 0 < Gamma (((d : ℝ) + 1) / 2) := Gamma_pos_of_pos (by linarith)
  have hsmooth := (witness_polar_closed_form d hd hw).2
  have hdiff : DifferentiableOn ℝ (polarProfileOf (witnessProfile w) d) (Ioi 0) :=
    hsmooth.differentiableOn (by simp)
  unfold threshold
  rw [le_div_iff₀ (by positivity)]
  constructor
  · intro hanti
    -- the criterion at `r = √(2 z₀)`, where `r²/2 = z₀`
    set r := Real.sqrt (2 * z₀) with hr_def
    have hr : 0 < r := Real.sqrt_pos.2 (by linarith [hz₀.1])
    have hrz : r ^ 2 / 2 = z₀ := by
      rw [hr_def, Real.sq_sqrt (by linarith [hz₀.1])]; ring
    have hder : deriv (polarProfileOf (witnessProfile w) d) r ≤ 0 := by
      rw [← derivWithin_of_isOpen isOpen_Ioi hr]
      exact hanti.derivWithin_nonpos
    have := (witness_threshold_criterion d hd hw hr).1 hder
    rw [hrz, hz₀M] at this
    linarith
  · intro hwM
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hdiff.continuousOn
      (by rw [interior_Ioi]; exact hdiff) fun r hr => ?_
    rw [interior_Ioi] at hr
    have hr : 0 < r := hr
    refine (witness_threshold_criterion d hd hw hr).2 ?_
    have := thresholdFun_le_thresholdSup hd' (by positivity : (0 : ℝ) < r ^ 2 / 2)
    nlinarith

end AffineHemigroup
