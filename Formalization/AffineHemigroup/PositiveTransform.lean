/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Polar
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# `lem:positive-transform-origin`: a nonnegative transform, bounded near the origin only if
integrable

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:positive-transform-origin`. Wave 2,
group A (Q-0281).

The blueprint's route. Clause (1): the heat kernel is a Gaussian Fourier integral
(`heatKernel_fourier`, Mathlib's `integral_cexp_neg_mul_sq_norm_add`), Fubini exchanges the two
integrals, and `μ̂(-ξ) = conj μ̂(ξ) = μ̂(ξ)` for a real transform; the monotone limit as `t ↓ 0` is
`lintegral_iSup` along `t = 1/(n+1)` and the antitone limit along `𝓝[>] 0`. Clause (2): the
hypothesis makes `μ|_U ≤ M · Lebesgue|_U`, `∫ g_t = 1`, and the tail of `g_t` off `U` tends to `0`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-- The Gaussian `v ↦ e^{-b|v|²}` is integrable on `ℝ^d` for `b > 0`. Mathlib types only. -/
theorem integrable_rexp_neg_mul_sq_norm_Rd (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : Rd d => Real.exp (-b * ‖v‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Rd d) (b := (b : ℂ))
    (by simpa using hb) 0 0
  refine h.norm.congr (ae_of_all _ fun v => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

/-- **The heat kernel as a Gaussian Fourier integral**:
`∫ e^{-t|ξ|²/2 - i⟨x,ξ⟩} dξ = (2π)^d g_t(x)` for `t > 0`. -/
theorem heatKernel_fourier {t : ℝ} (ht : 0 < t) (x : Rd d) :
    ∫ ξ : Rd d, cexp (-((t / 2 : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2 + (-I) * (⟪x, ξ⟫ : ℂ))
      = (((2 * Real.pi) ^ (d : ℝ) * heatKernel d t x : ℝ) : ℂ) := by
  have ht2 : 0 < ((t / 2 : ℝ) : ℂ).re := by simpa using half_pos ht
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add ht2 (-I) x, finrank_Rd]
  have h1 : ((Real.pi : ℂ) / ((t / 2 : ℝ) : ℂ)) ^ ((d : ℂ) / 2)
      = (((2 * Real.pi / t) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((Real.pi : ℂ) / ((t / 2 : ℝ) : ℂ)) = ((2 * Real.pi / t : ℝ) : ℂ) by
        push_cast; field_simp,
      Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have h2 : (-I) ^ 2 * ((‖x‖ : ℂ)) ^ 2 / (4 * ((t / 2 : ℝ) : ℂ))
      = ((-‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ) := by
    push_cast
    rw [neg_sq, I_sq]
    field_simp
    ring
  rw [h1, h2, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  congr 1
  rw [heatKernel]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [Real.mul_rpow hpi.le ht.le, Real.div_rpow hpi.le ht.le, ← mul_assoc, ← mul_assoc]
  congr 1
  have e1 : (2 * Real.pi) ^ (d : ℝ) * (2 * Real.pi) ^ (-(d : ℝ) / 2)
      = (2 * Real.pi) ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_add hpi]; ring_nf
  have e2 : t ^ (-(d : ℝ) / 2) = (t ^ ((d : ℝ) / 2))⁻¹ := by
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg ht.le]
  rw [e1, e2, div_eq_mul_inv]

/-- **`lem:positive-transform-origin`(1), the identity**: for a probability measure with real
transform and `t > 0`, `∫ g_t dμ = (2π)^{-d} ∫ μ̂(ξ) e^{-t|ξ|²/2} dξ`. -/
theorem integral_heatKernel_eq (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hreal : ∀ ξ : Rd d, (charFun μ ξ).im = 0) {t : ℝ} (ht : 0 < t) :
    ∫ x, heatKernel d t x ∂μ =
      (2 * Real.pi) ^ (-(d : ℝ)) * ∫ ξ, (charFun μ ξ).re * Real.exp (-(t * ‖ξ‖ ^ 2) / 2) := by
  set F : Rd d → Rd d → ℂ := fun x ξ =>
    cexp (-((t / 2 : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2 + (-I) * (⟪x, ξ⟫ : ℂ)) with hF
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpid : ((2 * Real.pi) ^ (-(d : ℝ))) * (2 * Real.pi) ^ (d : ℝ) = 1 := by
    rw [← Real.rpow_add hpi]; simp
  -- the heat kernel through the Fourier integral
  have hg : ∀ x : Rd d, ((heatKernel d t x : ℝ) : ℂ)
      = (((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) : ℂ) * ∫ ξ, F x ξ := by
    intro x
    rw [hF, heatKernel_fourier ht x, ← Complex.ofReal_mul, ← mul_assoc, hpid, one_mul]
  -- integrability on the product
  have hcont : Continuous (Function.uncurry F) := by
    simp only [hF]
    fun_prop
  have hgauss := integrable_rexp_neg_mul_sq_norm_Rd d (half_pos ht)
  have hint : Integrable (Function.uncurry F) (μ.prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hgauss)
      hcont.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, hF, Complex.norm_exp, one_mul]
    apply le_of_eq
    congr 1
    simp [← Complex.ofReal_pow]
  -- the inner integral in `x`
  have hinner : ∀ ξ : Rd d, ∫ x, F x ξ ∂μ
      = (((Real.exp (-(t * ‖ξ‖ ^ 2) / 2)) * (charFun μ ξ).re : ℝ) : ℂ) := by
    intro ξ
    have hsplit : ∀ x : Rd d, F x ξ
        = cexp (-((t / 2 : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2) * cexp ((⟪x, -ξ⟫ : ℂ) * I) := by
      intro x
      rw [hF, ← Complex.exp_add, inner_neg_right]
      push_cast
      ring_nf
    simp_rw [hsplit]
    rw [integral_const_mul, ← charFun_apply, charFun_neg]
    have hconj : (starRingEnd ℂ) (charFun μ ξ) = (((charFun μ ξ).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hreal ξ]
    rw [hconj, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hg]
  rw [integral_const_mul, integral_integral_swap hint]
  simp_rw [hinner]
  rw [integral_complex_ofReal, ← Complex.ofReal_mul]
  congr 2
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only
  ring

theorem heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : Rd d) : 0 ≤ heatKernel d t x := by
  unfold heatKernel
  have : 0 < 2 * Real.pi * t := by positivity
  positivity

theorem heatKernel_le {t : ℝ} (ht : 0 < t) (x : Rd d) :
    heatKernel d t x ≤ (2 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
  unfold heatKernel
  have : 0 < 2 * Real.pi * t := by positivity
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
  have : 0 ≤ ‖x‖ ^ 2 / (2 * t) := by positivity
  rw [neg_div]; linarith

theorem continuous_heatKernel {t : ℝ} : Continuous (heatKernel d t) := by
  unfold heatKernel
  fun_prop

/-- `g_t(x) = (2πt)^{-d/2} e^{-|x|²/2t}` written as a Gaussian `c e^{-b|x|²}`. -/
theorem heatKernel_eq_gauss {t : ℝ} (x : Rd d) :
    heatKernel d t x = (2 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (2 * t)) * ‖x‖ ^ 2) := by
  unfold heatKernel
  congr 2
  ring

theorem integrable_heatKernel {t : ℝ} (ht : 0 < t) : Integrable (heatKernel d t) := by
  have h := (integrable_rexp_neg_mul_sq_norm_Rd d (b := 1 / (2 * t)) (by positivity)).const_mul
    ((2 * Real.pi * t) ^ (-(d : ℝ) / 2))
  refine h.congr (ae_of_all _ fun x => ?_)
  rw [heatKernel_eq_gauss]

/-- `∫ g_t dx = 1`. -/
theorem integral_heatKernel_volume {t : ℝ} (ht : 0 < t) : ∫ x : Rd d, heatKernel d t x = 1 := by
  simp_rw [heatKernel_eq_gauss]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity),
    finrank_Rd, show Real.pi / (1 / (2 * t)) = 2 * Real.pi * t by field_simp,
    ← Real.rpow_add (by positivity), show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring, Real.rpow_zero]

/-- `∫⁻ g_t dx = 1`. -/
theorem lintegral_heatKernel_volume {t : ℝ} (ht : 0 < t) :
    ∫⁻ x : Rd d, ENNReal.ofReal (heatKernel d t x) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel ht)
    (ae_of_all _ (heatKernel_nonneg ht)), integral_heatKernel_volume ht, ENNReal.ofReal_one]

/-- **`lem:positive-transform-origin`(1)**: for a probability measure with real nonnegative
transform, `∫ g_t dμ = (2π)^{-d} ∫ μ̂(ξ) e^{-t|ξ|²/2} dξ` for `t > 0`, and as `t ↓ 0` this increases
to `(2π)^{-d} ∫ μ̂ ∈ (0,∞]`. -/
theorem positive_transform_heat (_hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hreal : ∀ ξ : Rd d, (charFun μ ξ).im = 0) (hpos : ∀ ξ : Rd d, 0 ≤ (charFun μ ξ).re) :
    (∀ t : ℝ, 0 < t → ∫ x, heatKernel d t x ∂μ =
        (2 * Real.pi) ^ (-(d : ℝ)) * ∫ ξ, (charFun μ ξ).re * Real.exp (-(t * ‖ξ‖ ^ 2) / 2)) ∧
      AntitoneOn (fun t => ∫ x, heatKernel d t x ∂μ) (Ioi 0) ∧
      Tendsto (fun t => ENNReal.ofReal (∫ x, heatKernel d t x ∂μ)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) * ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re)) ∧
      ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re ≠ 0 := by
  set re : Rd d → ℝ := fun ξ => (charFun μ ξ).re with hre
  have hre_cont : Continuous re := Complex.continuous_re.comp continuous_charFun
  have hre_le : ∀ ξ, re ξ ≤ 1 := fun ξ =>
    (Complex.re_le_norm _).trans (norm_charFun_le_one ξ)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hc : 0 < (2 * Real.pi) ^ (-(d : ℝ)) := Real.rpow_pos_of_pos hpi _
  have hexp : ∀ t : ℝ, ∀ ξ : Rd d, Real.exp (-(t * ‖ξ‖ ^ 2) / 2) = Real.exp (-(t / 2) * ‖ξ‖ ^ 2) :=
    fun t ξ => by ring_nf
  have hint : ∀ t : ℝ, 0 < t → Integrable (fun ξ => re ξ * Real.exp (-(t * ‖ξ‖ ^ 2) / 2)) := by
    intro t ht
    refine Integrable.mono' (integrable_rexp_neg_mul_sq_norm_Rd d (half_pos ht))
      ((hre_cont.mul (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos ξ) (Real.exp_pos _).le), hexp]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hre_le ξ)
  have hid := fun t (ht : 0 < t) => integral_heatKernel_eq μ hreal ht
  -- the `ℝ≥0∞` form
  set T : ℝ → ℝ≥0∞ := fun t => ∫⁻ ξ, ENNReal.ofReal (re ξ * Real.exp (-(t * ‖ξ‖ ^ 2) / 2))
    with hT
  have hlint : ∀ t : ℝ, 0 < t → ENNReal.ofReal (∫ x, heatKernel d t x ∂μ)
      = ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) * T t := by
    intro t ht
    rw [hid t ht, ENNReal.ofReal_mul hc.le, ofReal_integral_eq_lintegral_ofReal (hint t ht)
      (ae_of_all _ fun ξ => mul_nonneg (hpos ξ) (Real.exp_pos _).le)]
  have hTanti : AntitoneOn T (Ioi 0) := by
    intro s hs t ht hst
    refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hpos ξ)
    have : s * ‖ξ‖ ^ 2 ≤ t * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hst (by positivity)
    linarith
  have hTle : ∀ t : ℝ, 0 < t → T t ≤ ∫⁻ ξ, ENNReal.ofReal (re ξ) := by
    intro t _
    refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
    exact mul_le_of_le_one_right (hpos ξ) (Real.exp_le_one_iff.mpr (by
      have : 0 ≤ t * ‖ξ‖ ^ 2 := by positivity
      linarith))
  have hmono_n : ∀ ξ : Rd d, Monotone fun n : ℕ =>
      ENNReal.ofReal (re ξ * Real.exp (-(1 / ((n : ℝ) + 1) * ‖ξ‖ ^ 2) / 2)) := by
    intro ξ m n hmn
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr ?_) (hpos ξ))
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by gcongr
    have : 1 / ((n : ℝ) + 1) * ‖ξ‖ ^ 2 ≤ 1 / ((m : ℝ) + 1) * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith
  -- the monotone limit along `t = 1/(n+1)`
  have hseq : ∫⁻ ξ, ENNReal.ofReal (re ξ) = ⨆ n : ℕ, T (1 / ((n : ℝ) + 1)) := by
    simp only [hT]
    have hmeas : ∀ n : ℕ, Measurable fun ξ : Rd d =>
        ENNReal.ofReal (re ξ * Real.exp (-(1 / ((n : ℝ) + 1) * ‖ξ‖ ^ 2) / 2)) := fun n =>
      (hre_cont.measurable.mul (by fun_prop)).ennreal_ofReal
    rw [← lintegral_iSup hmeas (fun m n hmn ξ => hmono_n ξ hmn)]
    refine lintegral_congr fun ξ => ?_
    refine (iSup_eq_of_tendsto (hmono_n ξ) ?_).symm
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => re ξ * Real.exp (-(1 / ((n : ℝ) + 1) * ‖ξ‖ ^ 2) / 2))
        atTop (𝓝 (re ξ * Real.exp (-(0 * ‖ξ‖ ^ 2) / 2))) := by
      refine tendsto_const_nhds.mul ((Real.continuous_exp.tendsto _).comp ?_)
      exact ((h0.mul_const _).neg).div_const _
    simp only [zero_mul, neg_zero, zero_div, Real.exp_zero, mul_one] at h1
    exact (ENNReal.continuous_ofReal.tendsto _).comp h1
  have hTlim : Tendsto T (𝓝[>] 0) (𝓝 (∫⁻ ξ, ENNReal.ofReal (re ξ))) := by
    have h := hTanti.tendsto_nhdsGT (OrderTop.bddAbove _)
    have heq : sSup (T '' Ioi 0) = ∫⁻ ξ, ENNReal.ofReal (re ξ) := by
      refine le_antisymm (sSup_le ?_) ?_
      · rintro _ ⟨t, ht, rfl⟩; exact hTle t ht
      · rw [hseq]
        refine iSup_le fun n => le_sSup ⟨1 / ((n : ℝ) + 1), ?_, rfl⟩
        show (0 : ℝ) < 1 / ((n : ℝ) + 1)
        positivity
    rwa [heq] at h
  refine ⟨hid, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    simp only
    rw [hid s hs, hid t ht]
    refine mul_le_mul_of_nonneg_left (integral_mono (hint t ht) (hint s hs) fun ξ => ?_) hc.le
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hpos ξ)
    have : s * ‖ξ‖ ^ 2 ≤ t * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hst (by positivity)
    linarith
  · have h := ENNReal.Tendsto.const_mul hTlim (Or.inr (ENNReal.ofReal_ne_top
      (r := (2 * Real.pi) ^ (-(d : ℝ)))))
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hlint t ht).symm
  · -- positivity near `ξ = 0`
    set U := {ξ : Rd d | 1 / 2 < re ξ} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const hre_cont
    have h0 : (0 : Rd d) ∈ U := by
      show (1 : ℝ) / 2 < (charFun μ 0).re
      rw [charFun_zero]
      simp only [probReal_univ, Complex.ofReal_one, Complex.one_re]
      norm_num
    have hUpos : 0 < volume U := hUo.measure_pos volume ⟨0, h0⟩
    refine ne_of_gt (lt_of_lt_of_le ?_ (setLIntegral_le_lintegral U _))
    calc (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) * volume U :=
          ENNReal.mul_pos (by simp) hUpos.ne'
      _ = ∫⁻ _ξ in U, ENNReal.ofReal (1 / 2) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ ξ in U, ENNReal.ofReal (re ξ) :=
          setLIntegral_mono' hUo.measurableSet fun ξ hξ => ENNReal.ofReal_le_ofReal (le_of_lt hξ)

/-- The tail of the heat kernel off a ball: `(2πt)^{-d/2} e^{-δ²/2t} → 0` as `t ↓ 0`. -/
theorem tendsto_heatKernel_tail {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => (2 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-δ ^ 2 / (2 * t)))
      (𝓝[>] 0) (𝓝 0) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((d : ℝ) / 2) (δ ^ 2 / 2)
    (by positivity)).comp tendsto_inv_nhdsGT_zero
  have h2 := h.const_mul ((2 * Real.pi) ^ (-(d : ℝ) / 2))
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [Function.comp_apply]
  rw [Real.mul_rpow hpi.le ht.le, Real.inv_rpow ht.le, mul_assoc]
  congr 2
  · rw [← Real.rpow_neg ht.le]; ring_nf
  · congr 1; field_simp

/-- **`lem:positive-transform-origin`(2)**: if `μ(B) ≤ M|B|` for every Borel `B ⊆ {|x| < δ}`, then
`∫ μ̂ ≤ (2π)^d M`. -/
theorem positive_transform_bound (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hreal : ∀ ξ : Rd d, (charFun μ ξ).im = 0) (hpos : ∀ ξ : Rd d, 0 ≤ (charFun μ ξ).re)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ≥0)
    (hM : ∀ B : Set (Rd d), MeasurableSet B → B ⊆ Metric.ball 0 δ → μ B ≤ M * volume B) :
    ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re ≤ ENNReal.ofReal ((2 * Real.pi) ^ (d : ℝ)) * M := by
  set U := Metric.ball (0 : Rd d) δ with hU
  have hpi : 0 < 2 * Real.pi := by positivity
  -- `μ|_U ≤ M · Lebesgue|_U`
  have hle : μ.restrict U ≤ (M : ℝ≥0∞) • volume.restrict U := by
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    exact hM _ (hs.inter Metric.isOpen_ball.measurableSet) inter_subset_right
  -- the bound at every `t > 0`
  have hbound : ∀ t : ℝ, 0 < t → ENNReal.ofReal (∫ x, heatKernel d t x ∂μ) ≤
      (M : ℝ≥0∞) + ENNReal.ofReal ((2 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-δ ^ 2 / (2 * t))) := by
    intro t ht
    have hint : Integrable (heatKernel d t) μ :=
      Integrable.of_bound (continuous_heatKernel).aestronglyMeasurable _
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht x)]
          exact heatKernel_le ht x)
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (heatKernel_nonneg ht)),
      ← lintegral_add_compl _ Metric.isOpen_ball.measurableSet]
    refine add_le_add ?_ ?_
    · calc ∫⁻ x in U, ENNReal.ofReal (heatKernel d t x) ∂μ
          ≤ ∫⁻ x, ENNReal.ofReal (heatKernel d t x) ∂((M : ℝ≥0∞) • volume.restrict U) :=
            lintegral_mono' hle le_rfl
        _ = M * ∫⁻ x in U, ENNReal.ofReal (heatKernel d t x) := by
            rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ M * ∫⁻ x, ENNReal.ofReal (heatKernel d t x) := by
            gcongr; exact Measure.restrict_le_self
        _ = M := by rw [lintegral_heatKernel_volume ht, mul_one]
    · calc ∫⁻ x in Uᶜ, ENNReal.ofReal (heatKernel d t x) ∂μ
          ≤ ∫⁻ _x in Uᶜ, ENNReal.ofReal ((2 * Real.pi * t) ^ (-(d : ℝ) / 2) *
              Real.exp (-δ ^ 2 / (2 * t))) ∂μ := by
            refine setLIntegral_mono' Metric.isOpen_ball.measurableSet.compl fun x hx => ?_
            refine ENNReal.ofReal_le_ofReal ?_
            unfold heatKernel
            have h2t : 0 < 2 * Real.pi * t := by positivity
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            have hxδ : δ ≤ ‖x‖ := by
              simpa [hU, Metric.mem_ball, dist_zero_right, not_lt] using hx
            have : δ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hδ.le hxδ 2
            rw [neg_div, neg_div, neg_le_neg_iff]
            exact div_le_div_of_nonneg_right this (by positivity)
        _ ≤ ENNReal.ofReal ((2 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-δ ^ 2 / (2 * t))) := by
            rw [setLIntegral_const]
            exact mul_le_of_le_one_right' (prob_le_one)
  -- pass to the limit
  have hlim := (positive_transform_heat hd μ hreal hpos).2.2.1
  have hlimR : Tendsto (fun t : ℝ => (M : ℝ≥0∞) + ENNReal.ofReal ((2 * Real.pi * t) ^
      (-(d : ℝ) / 2) * Real.exp (-δ ^ 2 / (2 * t)))) (𝓝[>] 0) (𝓝 ((M : ℝ≥0∞) + 0)) := by
    refine tendsto_const_nhds.add ?_
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_heatKernel_tail hδ)
  rw [add_zero] at hlimR
  have hineq : ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) *
      ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re ≤ M :=
    le_of_tendsto_of_tendsto hlim hlimR
      (by filter_upwards [self_mem_nhdsWithin] with t ht using hbound t ht)
  have hone : ENNReal.ofReal ((2 * Real.pi) ^ (d : ℝ)) * ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ)))
      = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hpi, add_neg_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  calc ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re
      = ENNReal.ofReal ((2 * Real.pi) ^ (d : ℝ)) * (ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) *
          ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re) := by rw [← mul_assoc, hone, one_mul]
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ (d : ℝ)) * M := by gcongr

/-- **`lem:positive-transform-origin`(2)**, the last sentence: a density with a representative
bounded by `M` on `{0 < |x| < δ}` gives the hypothesis. -/
theorem density_bound_ball (hd : 1 ≤ d) (μ : Measure (Rd d)) {δ : ℝ} (_hδ : 0 < δ) (M : ℝ≥0)
    (q : Rd d → ℝ) (hq : μ = volume.withDensity (fun x => ENNReal.ofReal (q x)))
    (hqM : ∀ x : Rd d, 0 < ‖x‖ → ‖x‖ < δ → q x ≤ M) :
    ∀ B : Set (Rd d), MeasurableSet B → B ⊆ Metric.ball 0 δ → μ B ≤ M * volume B := by
  intro B hB hBδ
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  rw [hq, withDensity_apply _ hB, ← setLIntegral_const]
  refine setLIntegral_mono_ae' hB ?_
  have h0 : ∀ᵐ x ∂(volume : Measure (Rd d)), x ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with x hx0 hxB
  have hx : ‖x‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hBδ hxB
  rw [show ((M : ℝ≥0∞)) = ENNReal.ofReal (M : ℝ) by simp]
  exact ENNReal.ofReal_le_ofReal (hqM x (norm_pos_iff.mpr hx0) hx)

end AffineHemigroup
