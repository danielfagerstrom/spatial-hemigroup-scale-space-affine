/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Thresholds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `lem:threshold-limit`: the thresholds tend to `0` at the rate `d^{-1/2}`

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:threshold-limit` (wave 1, group D, Q-0281).

**Stirling's bounds** for real `m ≥ 1`, `e^{-1/2} m^m e^{-m} ≤ √m Γ(m) ≤ K m^m e^{-m}` with
`K = √(π/2) + √π + 4`, are proved from `Γ(m+1) = ∫₀^∞ t^m e^{-t} dt` in the blueprint's way, in the
variable `t = m(1+u)`: `t^m e^{-t} = m^m e^{-m} e^{m(log(1+u) - u)}`, and four elementary
inequalities for `log(1+u) - u` bound the integrand by Gaussians on `(0, m]` and `(m, 2m]`, by an
exponential on `(2m, ∞)`, and from below by `m^m e^{-m} e^{-1/2}` on `[m, m + √m]`. The half-line
Gaussian integrals are Mathlib's `integral_gaussian_Ioi`. Then `M_d` is squeezed between
`m^m e^{-m}(1 - ε_d)` and `m^m e^{-m}`. Lean core only: no ledger entry is read.
-/

namespace AffineHemigroup

open MeasureTheory Set Real Filter
open scoped Topology

/-! ### Four inequalities for `log(1 + u)` -/

/-- A function with nonnegative derivative inside `[a, b]` increases from `a` to `b`. -/
theorem le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hp : ∀ x ∈ Ioo a b, 0 ≤ f' x) : f a ≤ f b := by
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc a b) hf
    (by rw [interior_Icc]; exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (by rw [interior_Icc]; intro x hx; rw [(hd x hx).deriv]; exact hp x hx)
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- `F(u) = log(1+u) - u + u²/2` has derivative `u²/(1+u) ≥ 0` on `(-1, ∞)`. -/
theorem hasDerivAt_logOneAdd_aux {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun u => Real.log (1 + u) - u + u ^ 2 / 2) (x ^ 2 / (1 + x)) x := by
  have h1 : HasDerivAt (fun u => 1 + u) 1 x := (hasDerivAt_id x).const_add 1
  have h2 := h1.log (by linarith)
  have h3 := (h2.sub (hasDerivAt_id x)).add ((hasDerivAt_pow 2 x).div_const 2)
  refine h3.congr_deriv ?_
  have : (1 + x) ≠ 0 := by linarith
  field_simp
  ring

theorem continuousOn_logOneAdd_aux {a b : ℝ} (ha : -1 < a) :
    ContinuousOn (fun u => Real.log (1 + u) - u + u ^ 2 / 2) (Icc a b) := by
  refine ContinuousOn.add (ContinuousOn.sub ?_ continuousOn_id) (by fun_prop)
  exact ContinuousOn.log (by fun_prop) fun u hu => by linarith [hu.1]

/-- `log(1+u) ≥ u - u²/2` for `u ≥ 0`. -/
theorem log_one_add_ge {u : ℝ} (hu : 0 ≤ u) : u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  have := le_of_hasDerivAt_nonneg hu (continuousOn_logOneAdd_aux (by norm_num))
    (fun x hx => hasDerivAt_logOneAdd_aux (by linarith [hx.1]))
    (fun x hx => div_nonneg (sq_nonneg _) (by linarith [hx.1]))
  simp only [add_zero, Real.log_one, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at this
  linarith

/-- `log(1+u) ≤ u - u²/2` for `-1 < u ≤ 0`. -/
theorem log_one_add_le_neg {u : ℝ} (hu1 : -1 < u) (hu : u ≤ 0) :
    Real.log (1 + u) ≤ u - u ^ 2 / 2 := by
  have := le_of_hasDerivAt_nonneg hu (continuousOn_logOneAdd_aux hu1)
    (fun x hx => hasDerivAt_logOneAdd_aux (by linarith [hx.1]))
    (fun x hx => div_nonneg (sq_nonneg _) (by linarith [hx.1]))
  simp only [add_zero, Real.log_one, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at this
  linarith

/-- `log(1+u) ≤ u - u²/4` for `0 ≤ u ≤ 1`. -/
theorem log_one_add_le_quarter {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.log (1 + u) ≤ u - u ^ 2 / 4 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) u, HasDerivAt (fun v => v - v ^ 2 / 4 - Real.log (1 + v))
      (x * (1 - x) / (2 * (1 + x))) x := by
    intro x hx
    have h1 : HasDerivAt (fun v => 1 + v) 1 x := (hasDerivAt_id x).const_add 1
    have h2 := h1.log (by linarith [hx.1])
    have h3 := ((hasDerivAt_id x).sub ((hasDerivAt_pow 2 x).div_const 4)).sub h2
    refine h3.congr_deriv ?_
    have : (1 + x) ≠ 0 := by linarith [hx.1]
    field_simp
    ring
  have hc : ContinuousOn (fun v => v - v ^ 2 / 4 - Real.log (1 + v)) (Icc 0 u) := by
    refine ContinuousOn.sub (by fun_prop) ?_
    exact ContinuousOn.log (by fun_prop) fun v hv => by linarith [hv.1]
  have := le_of_hasDerivAt_nonneg hu hc hd (fun x hx => by
    have h0 := hx.1
    have h1 : x < 1 := lt_of_lt_of_le hx.2 hu1
    exact div_nonneg (mul_nonneg h0.le (by linarith)) (by linarith))
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, Real.log_one] at this
  linarith

/-- `log(1+u) ≤ 3u/4` for `u ≥ 1`: `log(1+u) ≤ log 2 + (u-1)/2` and `log 2 < 3/4`. -/
theorem log_one_add_le_linear {u : ℝ} (hu : 1 ≤ u) : Real.log (1 + u) ≤ 3 / 4 * u := by
  have h1 : Real.log ((1 + u) / 2) ≤ (1 + u) / 2 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at h1
  have h2 := Real.log_two_lt_d9
  norm_num at h2
  linarith

/-! ### The Gamma integrand in the variable `t = m(1+u)` -/

/-- `e^{-t} t^m = m^m e^{-m} e^{m(log(1+u) - u)}` with `u = t/m - 1`. -/
theorem gamma_integrand_eq {m t : ℝ} (hm : 0 < m) (ht : 0 < t) :
    Real.exp (-t) * t ^ m =
      m ^ m * Real.exp (-m) * Real.exp (m * (Real.log (1 + (t / m - 1)) - (t / m - 1))) := by
  rw [rpow_def_of_pos ht, rpow_def_of_pos hm, add_sub_cancel, Real.log_div ht.ne' hm.ne',
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- On `(0, m]`: `e^{-t}t^m ≤ m^m e^{-m} e^{-(t-m)²/(2m)}`. -/
theorem gamma_integrand_le_one {m t : ℝ} (hm : 0 < m) (ht : 0 < t) (htm : t ≤ m) :
    Real.exp (-t) * t ^ m ≤ m ^ m * Real.exp (-m) * Real.exp (-(1 / (2 * m)) * (t - m) ^ 2) := by
  rw [gamma_integrand_eq hm ht]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hu1 : -1 < t / m - 1 := by have := div_pos ht hm; linarith
  have hu0 : t / m - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hm]; exact htm
  have h := log_one_add_le_neg hu1 hu0
  have : -(1 / (2 * m)) * (t - m) ^ 2 = m * (-(t / m - 1) ^ 2 / 2) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) hm.le

/-- On `(m, 2m]`: `e^{-t}t^m ≤ m^m e^{-m} e^{-(t-m)²/(4m)}`. -/
theorem gamma_integrand_le_two {m t : ℝ} (hm : 0 < m) (htm : m ≤ t) (ht2 : t ≤ 2 * m) :
    Real.exp (-t) * t ^ m ≤ m ^ m * Real.exp (-m) * Real.exp (-(1 / (4 * m)) * (t - m) ^ 2) := by
  rw [gamma_integrand_eq hm (by linarith)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hu0 : 0 ≤ t / m - 1 := by rw [sub_nonneg, le_div_iff₀ hm]; linarith
  have hu1 : t / m - 1 ≤ 1 := by rw [sub_le_iff_le_add, div_le_iff₀ hm]; linarith
  have h := log_one_add_le_quarter hu0 hu1
  have : -(1 / (4 * m)) * (t - m) ^ 2 = m * (-(t / m - 1) ^ 2 / 4) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) hm.le

/-- On `(2m, ∞)`: `e^{-t}t^m ≤ m^m e^{-m} e^{m/4} e^{-t/4}`. -/
theorem gamma_integrand_le_three {m t : ℝ} (hm : 0 < m) (ht2 : 2 * m ≤ t) :
    Real.exp (-t) * t ^ m ≤ m ^ m * Real.exp (-m) * Real.exp (m / 4) * Real.exp (-(1 / 4) * t) := by
  rw [gamma_integrand_eq hm (by linarith), mul_assoc (m ^ m * Real.exp (-m)), ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hu : 1 ≤ t / m - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hm]; linarith
  have h := log_one_add_le_linear hu
  have : m / 4 + -(1 / 4) * t = m * (-(t / m - 1) / 4) := by field_simp; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) hm.le

/-- On `[m, m + √m]`: `m^m e^{-m} e^{-1/2} ≤ e^{-t}t^m`. -/
theorem gamma_integrand_ge {m t : ℝ} (hm : 0 < m) (htm : m ≤ t) (ht : t ≤ m + Real.sqrt m) :
    m ^ m * Real.exp (-m) * Real.exp (-(1 / 2)) ≤ Real.exp (-t) * t ^ m := by
  rw [gamma_integrand_eq hm (by linarith)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hu0 : 0 ≤ t / m - 1 := by rw [sub_nonneg, le_div_iff₀ hm]; linarith
  have h := log_one_add_ge hu0
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  -- `m u² ≤ 1`
  have hu : m * (t / m - 1) ^ 2 ≤ 1 := by
    have e : m * (t / m - 1) ^ 2 = (t - m) ^ 2 / m := by field_simp
    rw [e, div_le_one hm]
    have h0 : 0 ≤ t - m := by linarith
    nlinarith
  nlinarith

/-! ### Half-line Gaussian integrals -/

/-- `∫_{t > a} e^{-b(t-a)²} dt = √(π/b)/2`. -/
theorem integral_Ioi_gauss_shift (a : ℝ) {b : ℝ} (_hb : 0 < b) :
    ∫ t in Ioi a, Real.exp (-b * (t - a) ^ 2) = Real.sqrt (π / b) / 2 := by
  rw [← integral_gaussian_Ioi b, ← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi,
    ← integral_sub_right_eq_self (fun t => (Ioi (0 : ℝ)).indicator
      (fun x => Real.exp (-b * x ^ 2)) t) a]
  congr 1
  funext t
  simp only [indicator, mem_Ioi, sub_pos]

/-- `∫_{t ≤ a} e^{-b(t-a)²} dt = √(π/b)/2`. -/
theorem integral_Iic_gauss_shift (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ t in Iic a, Real.exp (-b * (t - a) ^ 2) = Real.sqrt (π / b) / 2 := by
  have h := integral_comp_neg_Ioi (-a) (fun t => Real.exp (-b * (t - a) ^ 2))
  rw [neg_neg] at h
  rw [← h, ← integral_Ioi_gauss_shift (-a) hb]
  congr 1
  funext t
  congr 2
  ring

theorem integrable_gauss_shift (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * (t - a) ^ 2)) :=
  (integrable_exp_neg_mul_sq hb).comp_sub_right a

/-! ### Stirling's bounds -/

/-- **Stirling's upper bound**: `√m Γ(m) ≤ K m^m e^{-m}` for `m ≥ 1`, `K = √(π/2) + √π + 4`. -/
theorem sqrt_mul_Gamma_le {m : ℝ} (hm : 1 ≤ m) :
    Real.sqrt m * Gamma m ≤ stirlingK * (m ^ m * Real.exp (-m)) := by
  have hm0 : 0 < m := by linarith
  set C := m ^ m * Real.exp (-m) with hC
  have hCpos : 0 < C := by positivity
  set F : ℝ → ℝ := fun t => Real.exp (-t) * t ^ m with hF
  have hFint : IntegrableOn F (Ioi 0) := by
    have := GammaIntegral_convergent (s := m + 1) (by linarith)
    simpa [hF] using this
  have hG : Gamma (m + 1) = ∫ t in Ioi 0, F t := by
    rw [Gamma_eq_integral (by linarith)]
    simp [hF]
  have hFnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ F t := fun t ht => by
    simp only [hF]; exact mul_nonneg (Real.exp_pos _).le (rpow_nonneg (le_of_lt ht) _)
  -- split `(0, ∞) = (0, m] ∪ (m, 2m] ∪ (2m, ∞)`
  have hsplit1 : ∫ t in Ioi 0, F t = (∫ t in Ioc 0 m, F t) + ∫ t in Ioi m, F t := by
    rw [← Ioc_union_Ioi_eq_Ioi hm0.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hFint.mono_set Ioc_subset_Ioi_self) (hFint.mono_set (Ioi_subset_Ioi hm0.le))]
  have hsplit2 : ∫ t in Ioi m, F t = (∫ t in Ioc m (2 * m), F t) + ∫ t in Ioi (2 * m), F t := by
    rw [← Ioc_union_Ioi_eq_Ioi (by linarith : m ≤ 2 * m),
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hFint.mono_set (fun t ht => lt_trans hm0 ht.1))
      (hFint.mono_set (Ioi_subset_Ioi (by linarith)))]
  -- the three pieces
  have hb1 : 0 < 1 / (2 * m) := by positivity
  have hb2 : 0 < 1 / (4 * m) := by positivity
  have h1 : ∫ t in Ioc 0 m, F t ≤ C * (Real.sqrt (π / (1 / (2 * m))) / 2) := by
    calc ∫ t in Ioc 0 m, F t
        ≤ ∫ t in Ioc 0 m, C * Real.exp (-(1 / (2 * m)) * (t - m) ^ 2) :=
          setIntegral_mono_on (hFint.mono_set Ioc_subset_Ioi_self)
            ((integrable_gauss_shift m hb1).const_mul C).integrableOn measurableSet_Ioc
            fun t ht => gamma_integrand_le_one hm0 ht.1 ht.2
      _ ≤ ∫ t in Iic m, C * Real.exp (-(1 / (2 * m)) * (t - m) ^ 2) :=
          setIntegral_mono_set ((integrable_gauss_shift m hb1).const_mul C).integrableOn
            (Filter.Eventually.of_forall fun t => by positivity)
            (Filter.Eventually.of_forall fun t ht => ht.2)
      _ = C * (Real.sqrt (π / (1 / (2 * m))) / 2) := by
          rw [integral_const_mul, integral_Iic_gauss_shift m hb1]
  have h2 : ∫ t in Ioc m (2 * m), F t ≤ C * (Real.sqrt (π / (1 / (4 * m))) / 2) := by
    calc ∫ t in Ioc m (2 * m), F t
        ≤ ∫ t in Ioc m (2 * m), C * Real.exp (-(1 / (4 * m)) * (t - m) ^ 2) :=
          setIntegral_mono_on (hFint.mono_set (fun t ht => lt_trans hm0 ht.1))
            ((integrable_gauss_shift m hb2).const_mul C).integrableOn measurableSet_Ioc
            fun t ht => gamma_integrand_le_two hm0 ht.1.le ht.2
      _ ≤ ∫ t in Ioi m, C * Real.exp (-(1 / (4 * m)) * (t - m) ^ 2) :=
          setIntegral_mono_set ((integrable_gauss_shift m hb2).const_mul C).integrableOn
            (Filter.Eventually.of_forall fun t => by positivity)
            (Filter.Eventually.of_forall fun t ht => ht.1)
      _ = C * (Real.sqrt (π / (1 / (4 * m))) / 2) := by
          rw [integral_const_mul, integral_Ioi_gauss_shift m hb2]
  have h3 : ∫ t in Ioi (2 * m), F t ≤ C * 4 := by
    have hint : IntegrableOn (fun t => C * Real.exp (m / 4) * Real.exp (-(1 / 4) * t))
        (Ioi (2 * m)) := (integrableOn_exp_mul_Ioi (by norm_num) _).const_mul _
    calc ∫ t in Ioi (2 * m), F t
        ≤ ∫ t in Ioi (2 * m), C * Real.exp (m / 4) * Real.exp (-(1 / 4) * t) :=
          setIntegral_mono_on (hFint.mono_set (Ioi_subset_Ioi (by linarith))) hint
            measurableSet_Ioi fun t ht => gamma_integrand_le_three hm0 (le_of_lt ht)
      _ = C * (4 * Real.exp (-(m / 4))) := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num), mul_assoc]
          congr 1
          rw [show -Real.exp (-(1 / 4) * (2 * m)) / -(1 / 4) = 4 * Real.exp (-(m / 2)) by
            field_simp; ring_nf, ← mul_assoc, mul_comm (Real.exp (m / 4)) 4, mul_assoc,
            ← Real.exp_add]
          ring_nf
      _ ≤ C * 4 := by
          refine mul_le_mul_of_nonneg_left ?_ hCpos.le
          have : Real.exp (-(m / 4)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
          linarith
  -- assemble: `Γ(m+1) ≤ C (√(πm/2) + √(πm) + 4) ≤ C K √m`
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hs1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.2 hm
  have e1 : Real.sqrt (π / (1 / (2 * m))) / 2 = Real.sqrt (π / 2) * Real.sqrt m := by
    rw [show π / (1 / (2 * m)) = (π / 2) * (4 * m) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
    ring
  have e2 : Real.sqrt (π / (1 / (4 * m))) / 2 = Real.sqrt π * Real.sqrt m := by
    rw [show π / (1 / (4 * m)) = π * (4 * m) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by norm_num),
      show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
    ring
  have hGm : Gamma (m + 1) ≤ C * (stirlingK * Real.sqrt m) := by
    rw [hG, hsplit1, hsplit2]
    rw [e1] at h1
    rw [e2] at h2
    unfold stirlingK
    nlinarith
  have hrec : Gamma (m + 1) = m * Gamma m := Gamma_add_one hm0.ne'
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  rw [hrec] at hGm
  -- divide by `√m`
  have : Real.sqrt m * (Real.sqrt m * Gamma m) ≤ Real.sqrt m * (stirlingK * C) := by
    rw [← mul_assoc, hss]; linarith
  exact le_of_mul_le_mul_left this hs

/-- **Stirling's lower bound**: `e^{-1/2} m^m e^{-m} ≤ √m Γ(m)` for `m ≥ 1`. -/
theorem le_sqrt_mul_Gamma {m : ℝ} (hm : 1 ≤ m) :
    Real.exp (-(1 / 2)) * (m ^ m * Real.exp (-m)) ≤ Real.sqrt m * Gamma m := by
  have hm0 : 0 < m := by linarith
  set C := m ^ m * Real.exp (-m) with hC
  have hCpos : 0 < C := by positivity
  set F : ℝ → ℝ := fun t => Real.exp (-t) * t ^ m with hF
  have hFint : IntegrableOn F (Ioi 0) := by
    have := GammaIntegral_convergent (s := m + 1) (by linarith)
    simpa [hF] using this
  have hG : Gamma (m + 1) = ∫ t in Ioi 0, F t := by
    rw [Gamma_eq_integral (by linarith)]
    simp [hF]
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  have hsub : Icc m (m + Real.sqrt m) ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hm0 ht.1
  have hlow : C * Real.exp (-(1 / 2)) * Real.sqrt m ≤ Gamma (m + 1) := by
    rw [hG]
    calc C * Real.exp (-(1 / 2)) * Real.sqrt m
        = ∫ t in Icc m (m + Real.sqrt m), C * Real.exp (-(1 / 2)) := by
          rw [setIntegral_const, Measure.real, Real.volume_Icc, add_sub_cancel_left,
            ENNReal.toReal_ofReal hs.le, smul_eq_mul, mul_comm]
      _ ≤ ∫ t in Icc m (m + Real.sqrt m), F t :=
          setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Icc]))
            (hFint.mono_set hsub) measurableSet_Icc fun t ht => gamma_integrand_ge hm0 ht.1 ht.2
      _ ≤ ∫ t in Ioi 0, F t :=
          setIntegral_mono_set hFint
            ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
              simp only [hF]; exact mul_nonneg (Real.exp_pos _).le (rpow_nonneg (le_of_lt ht) _)))
            (Filter.Eventually.of_forall hsub)
  rw [Gamma_add_one hm0.ne'] at hlow
  have : Real.sqrt m * (Real.exp (-(1 / 2)) * C) ≤ Real.sqrt m * (Real.sqrt m * Gamma m) := by
    rw [← mul_assoc (Real.sqrt m) (Real.sqrt m), hss]; linarith
  exact le_of_mul_le_mul_left this hs

/-! ### `M_d` between `m^m e^{-m}(1 - ε_d)` and `m^m e^{-m}` -/

/-- `z^m e^{-z} ≤ m^m e^{-m}` for `z, m > 0`. -/
theorem rpow_mul_exp_neg_le {m z : ℝ} (hm : 0 < m) (hz : 0 < z) :
    z ^ m * Real.exp (-z) ≤ m ^ m * Real.exp (-m) := by
  rw [rpow_def_of_pos hz, rpow_def_of_pos hm, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h := Real.log_le_sub_one_of_pos (div_pos hz hm)
  rw [Real.log_div hz.ne' hm.ne'] at h
  have h' : (Real.log z - Real.log m) * m ≤ (z / m - 1) * m := mul_le_mul_of_nonneg_right h hm.le
  have e : (z / m - 1) * m = z - m := by field_simp
  rw [e] at h'
  linarith

/-- **`M_d ≤ m^m e^{-m}`**, `m = (d+1)/2`. -/
theorem thresholdSup_le {d : ℝ} (hd : 1 ≤ d) :
    thresholdSup d ≤ ((d + 1) / 2) ^ ((d + 1) / 2) * Real.exp (-((d + 1) / 2)) := by
  obtain ⟨-, -, z, hz, hzM⟩ := thresholdSup_spec d hd
  rw [← hzM]
  have hz0 := hz.1
  calc thresholdFun d z ≤ z ^ ((d + 1) / 2) * Real.exp (-z) := by
        unfold thresholdFun
        have : 0 ≤ (2 : ℝ) ^ (-d / 2) * Real.exp (-z / 2) := by positivity
        have hp : 0 ≤ z ^ ((d + 1) / 2) := rpow_nonneg hz0.le _
        nlinarith
    _ ≤ _ := rpow_mul_exp_neg_le (by linarith) hz0

/-- `2^{-d/2} e^{-m/2} = e^{-m} ε_d`. -/
theorem two_rpow_mul_exp_eq (d : ℝ) :
    (2 : ℝ) ^ (-d / 2) * Real.exp (-((d + 1) / 2) / 2) =
      Real.exp (-((d + 1) / 2)) * thresholdEps d := by
  unfold thresholdEps
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- **`M_d ≥ m^m e^{-m}(1 - ε_d)`**: `M_d ≥ h_d(m)`. -/
theorem le_thresholdSup {d : ℝ} (hd : 1 ≤ d) :
    ((d + 1) / 2) ^ ((d + 1) / 2) * Real.exp (-((d + 1) / 2)) * (1 - thresholdEps d) ≤
      thresholdSup d := by
  have hm : 0 < (d + 1) / 2 := by linarith
  refine le_trans (le_of_eq ?_) (thresholdFun_le_thresholdSup hd hm)
  unfold thresholdFun
  rw [two_rpow_mul_exp_eq]
  ring

/-- `ε_d = e^{1/4 + d(1/4 - (log 2)/2)}`. -/
theorem thresholdEps_eq_exp (d : ℝ) :
    thresholdEps d = Real.exp (1 / 4 + d * (1 / 4 - Real.log 2 / 2)) := by
  unfold thresholdEps
  rw [rpow_def_of_pos two_pos, ← Real.exp_add]
  congr 1
  ring

/-- The slope of `log ε_d` is negative: `1/4 - (log 2)/2 < 0`. -/
theorem thresholdEps_slope_neg : 1 / 4 - Real.log 2 / 2 < 0 := by
  have := Real.log_two_gt_d9
  norm_num at this
  linarith

/-! ### The node -/

/-- **`lem:threshold-limit`**, the bounds: for a real `d ≥ 1`,
`ε_d = e^{1/4}(e/4)^{d/4}`, `w_d ≥ e^{-1/2}/(2√m)`, and `w_d ≤ K/(2(1-ε_d)√m)` when `ε_d < 1`. -/
theorem threshold_limit_bounds (d : ℝ) (hd : 1 ≤ d) :
    thresholdEps d = Real.exp (1 / 4) * (Real.exp 1 / 4) ^ (d / 4) ∧
      Real.exp (-(1 / 2)) / (2 * Real.sqrt ((d + 1) / 2)) ≤ threshold d ∧
      (thresholdEps d < 1 →
        threshold d ≤ stirlingK / (2 * (1 - thresholdEps d) * Real.sqrt ((d + 1) / 2))) := by
  set m := (d + 1) / 2 with hmdef
  have hm1 : 1 ≤ m := by rw [hmdef]; linarith
  have hm0 : 0 < m := by linarith
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  set C := m ^ m * Real.exp (-m) with hC
  have hCpos : 0 < C := by positivity
  have hM := (thresholdSup_spec d hd).2.1
  have hMle : thresholdSup d ≤ C := thresholdSup_le hd
  have hG := Gamma_pos_of_pos hm0
  refine ⟨?_, ?_, fun hε => ?_⟩
  · -- `ε_d = e^{1/4}(e/4)^{d/4}`
    rw [thresholdEps_eq_exp, rpow_def_of_pos (by positivity), Real.log_div (by positivity)
      (by norm_num), Real.log_exp, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, ← Real.exp_add]
    congr 1
    push_cast
    ring
  · -- the lower bound
    have hSl := le_sqrt_mul_Gamma hm1
    unfold threshold
    rw [← hmdef, div_le_div_iff₀ (by positivity) (by positivity)]
    calc Real.exp (-(1 / 2)) * (2 * thresholdSup d)
        ≤ Real.exp (-(1 / 2)) * (2 * C) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 2 * (Real.exp (-(1 / 2)) * C) := by ring
      _ ≤ 2 * (Real.sqrt m * Gamma m) := by linarith
      _ = Gamma m * (2 * Real.sqrt m) := by ring
  · -- the upper bound
    have hSu := sqrt_mul_Gamma_le hm1
    have hMge := le_thresholdSup hd
    rw [← hmdef, ← hC] at hMge
    have h1ε : 0 < 1 - thresholdEps d := by linarith
    have hK : 0 < stirlingK := by unfold stirlingK; positivity
    unfold threshold
    rw [← hmdef, div_le_div_iff₀ (by positivity) (by positivity)]
    calc Gamma m * (2 * (1 - thresholdEps d) * Real.sqrt m)
        = 2 * (1 - thresholdEps d) * (Real.sqrt m * Gamma m) := by ring
      _ ≤ 2 * (1 - thresholdEps d) * (stirlingK * C) :=
          mul_le_mul_of_nonneg_left hSu (by positivity)
      _ = stirlingK * (2 * (C * (1 - thresholdEps d))) := by ring
      _ ≤ stirlingK * (2 * thresholdSup d) :=
          mul_le_mul_of_nonneg_left (by linarith) hK.le

/-- **`lem:threshold-limit`**, the limit: `ε_d` decreases strictly to `0`; `w_d → 0`, of exact order
`d^{-1/2}`: `√m w_d ≥ e^{-1/2}/2` for every `d ≥ 1`, `√m w_d ≤ K` once `ε_d ≤ 1/2`, which is every
large `d`; and every fixed `w > 0` exceeds `w_d` from some `D` on. -/
theorem threshold_limit :
    StrictAntiOn thresholdEps (Ici 1) ∧ Tendsto thresholdEps atTop (𝓝 0) ∧
      Tendsto threshold atTop (𝓝 0) ∧
      (∀ d : ℝ, 1 ≤ d → Real.exp (-(1 / 2)) / 2 ≤ Real.sqrt ((d + 1) / 2) * threshold d) ∧
      (∀ d : ℝ, 1 ≤ d → thresholdEps d ≤ 1 / 2 →
        Real.sqrt ((d + 1) / 2) * threshold d ≤ stirlingK) ∧
      (∀ᶠ d in atTop, thresholdEps d ≤ 1 / 2) ∧
      ∀ w : ℝ, 0 < w → ∃ D : ℝ, ∀ d : ℝ, D ≤ d → threshold d < w := by
  have hslope := thresholdEps_slope_neg
  have hanti : StrictAnti thresholdEps := fun a b hab => by
    rw [thresholdEps_eq_exp, thresholdEps_eq_exp, Real.exp_lt_exp]
    nlinarith
  have htend : Tendsto thresholdEps atTop (𝓝 0) := by
    have h : Tendsto (fun d : ℝ => 1 / 4 + d * (1 / 4 - Real.log 2 / 2)) atTop atBot :=
      tendsto_atBot_add_const_left _ _ (tendsto_id.atTop_mul_const_of_neg hslope)
    have heq : thresholdEps = Real.exp ∘ fun d : ℝ => 1 / 4 + d * (1 / 4 - Real.log 2 / 2) := by
      funext d; exact thresholdEps_eq_exp d
    rw [heq]
    exact Real.tendsto_exp_atBot.comp h
  have hev : ∀ᶠ d in atTop, thresholdEps d ≤ 1 / 2 :=
    ((tendsto_order.1 htend).2 (1 / 2) (by norm_num)).mono fun _ h => h.le
  have hK : 0 < stirlingK := by unfold stirlingK; positivity
  -- `√m w_d ≥ e^{-1/2}/2`
  have hlow : ∀ d : ℝ, 1 ≤ d → Real.exp (-(1 / 2)) / 2 ≤ Real.sqrt ((d + 1) / 2) * threshold d := by
    intro d hd
    have h := (threshold_limit_bounds d hd).2.1
    have hs : 0 < Real.sqrt ((d + 1) / 2) := Real.sqrt_pos.2 (by linarith)
    rw [div_le_iff₀ (by positivity)] at h
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  -- `√m w_d ≤ K` once `ε_d ≤ 1/2`
  have hup : ∀ d : ℝ, 1 ≤ d → thresholdEps d ≤ 1 / 2 →
      Real.sqrt ((d + 1) / 2) * threshold d ≤ stirlingK := by
    intro d hd hε
    have h := (threshold_limit_bounds d hd).2.2 (by linarith)
    have hs : 0 < Real.sqrt ((d + 1) / 2) := Real.sqrt_pos.2 (by linarith)
    have h1ε : 1 ≤ 2 * (1 - thresholdEps d) := by linarith
    rw [le_div_iff₀ (by positivity)] at h
    have hw := threshold_pos d hd
    nlinarith
  -- `w_d → 0`
  have hwlim : Tendsto threshold atTop (𝓝 0) := by
    have hsq : Tendsto (fun d : ℝ => Real.sqrt ((d + 1) / 2)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp
        ((tendsto_atTop_add_const_right _ 1 tendsto_id).atTop_div_const (by norm_num))
    have hupper : Tendsto (fun d : ℝ => stirlingK / Real.sqrt ((d + 1) / 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsq
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with d hd
      exact (threshold_pos d hd).le
    · filter_upwards [eventually_ge_atTop 1, hev] with d hd hε
      have hs : 0 < Real.sqrt ((d + 1) / 2) := Real.sqrt_pos.2 (by linarith)
      rw [le_div_iff₀ hs, mul_comm]
      exact hup d hd hε
  refine ⟨hanti.strictAntiOn _, htend, hwlim, hlow, hup, hev, fun w hw => ?_⟩
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hwlim).2 w hw)
  exact ⟨D, hD⟩

end AffineHemigroup
